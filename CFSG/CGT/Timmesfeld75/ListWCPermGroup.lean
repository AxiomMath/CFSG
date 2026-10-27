module

public import CFSG.CGT.Timmesfeld75.ListWCPermFacts
public import CFSG.CGT.Timmesfeld75.ListWCPermSpec

public section

namespace CFSG.CGT.Timmesfeld75.WCCheck

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

variable {D : Data} {M : Subgroup (Equiv.Perm (Fin D.n))} {genG : ℤ → M}

theorem mem_elts {t : Table} : t ∈ elts D ↔ ∃ m < 2 ^ D.pc.length, el D m = t := by
  simp only [elts, el, List.mem_map, List.mem_range]

theorem memS_iff {t : Table} : memS D t = true ↔ t ∈ elts D := by
  simp only [memS, memL, List.any_eq_true, beq_iff_eq, exists_eq_right]

theorem el_mem_elts {m : ℕ} (hm : m < 2 ^ D.pc.length) : el D m ∈ elts D :=
  mem_elts.2 ⟨m, hm, rfl⟩

theorem compT_eq_of_commT {x y : Table} (h : commT D.n x y = true) :
    compT D.n x y = compT D.n y x :=
  beq_iff_eq.1 h

variable (D genG) in
noncomputable abbrev S0 : Subgroup M := Subgroup.closure {g | g ∈ pcG D genG}

variable (D genG) in
noncomputable abbrev zG : M := eltG (pcG D genG) D.zIdx

section

variable (hn : D.n < 2 ^ 32) (hgen : ∀ l, Rep D.n (D.gens l) (genG l))
include hn hgen

theorem exists_eltG_of_memS {t : Table} {g : M} (ht : Rep D.n t g) (hmem : memS D t = true) :
    ∃ m < 2 ^ D.pc.length, eltG (pcG D genG) m = g := by
  obtain ⟨m, hm, hmt⟩ := mem_elts.1 (memS_iff.1 hmem)
  exact ⟨m, hm, eq_of_rep (hmt ▸ rep_el hn hgen m) ht⟩

theorem el_eq_of_eltG_eq {m m' : ℕ} (h : eltG (pcG D genG) m = eltG (pcG D genG) m') :
    el D m = el D m' :=
  beq_iff_eq.1 (beq_of_eq (rep_el hn hgen m) (h ▸ rep_el hn hgen m') (size_el m) (size_el m'))

theorem mem_S0_iff (hF : Facts D) (hinv : ∀ l, genG (-l) = (genG l)⁻¹) {g : M} :
    g ∈ S0 D genG ↔ ∃ m < 2 ^ D.pc.length, eltG (pcG D genG) m = g := by
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction_right with
    | one => exact ⟨0, Nat.two_pow_pos _, eltG_zero _⟩
    | mul_right x hx y hy ih =>
      obtain ⟨m, hm, rfl⟩ := ih
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hy
      exact exists_eltG_of_memS hn hgen (Rep.compT (rep_el hn hgen m) (rep_wT hn hgen w))
        (hF.closed _ (el_mem_elts hm) _ (List.mem_map.2 ⟨w, hw, rfl⟩))
    | mul_inv_cancel x hx y hy ih =>
      obtain ⟨m, hm, rfl⟩ := ih
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hy
      have hr := Rep.compT (rep_el hn hgen m) (rep_wT hn hgen (invWord w))
      rw [wG_invWord hinv] at hr
      exact exists_eltG_of_memS hn hgen hr (hF.closedInv _ (el_mem_elts hm) w hw)
  · rintro ⟨m, -, rfl⟩
    exact eltG_mem_closure _ _

theorem eltG_inj (hF : Facts D) {m m' : ℕ} (hm : m < 2 ^ D.pc.length)
    (hm' : m' < 2 ^ D.pc.length) (h : eltG (pcG D genG) m = eltG (pcG D genG) m') : m = m' :=
  List.inj_on_of_nodup_map hF.nodup (List.mem_range.2 hm) (List.mem_range.2 hm')
    (el_eq_of_eltG_eq hn hgen h)

theorem card_S0 (hF : Facts D) (hinv : ∀ l, genG (-l) = (genG l)⁻¹) :
    Nat.card (S0 D genG) = 2 ^ D.pc.length := by
  have h : Nat.card (Fin (2 ^ D.pc.length)) = Nat.card (S0 D genG) := by
    refine Nat.card_eq_of_bijective (fun i : Fin (2 ^ D.pc.length) =>
      (⟨eltG (pcG D genG) i, (mem_S0_iff hn hgen hF hinv).2 ⟨i, i.2, rfl⟩⟩ : S0 D genG))
      ⟨fun i j hij => Fin.ext (eltG_inj hn hgen hF i.2 j.2 (congrArg Subtype.val hij)), ?_⟩
    rintro ⟨g, hg⟩
    obtain ⟨m, hm, rfl⟩ := (mem_S0_iff hn hgen hF hinv).1 hg
    exact ⟨⟨m, hm⟩, rfl⟩
  rw [← h, Nat.card_fin]

theorem z_ne_one (hF : Facts D) : zG D genG ≠ 1 := fun h =>
  hF.zne (beq_iff_eq.1 (beq_of_eq (rep_el hn hgen D.zIdx)
    (by rw [show eltG (pcG D genG) D.zIdx = 1 from h]; exact Rep.idT (G := M) hn)
    (size_el _) size_idT'))

theorem cw_comm_z (hF : Facts D) {w : List ℤ} (hw : w ∈ D.cw) :
    wG D genG w * zG D genG = zG D genG * wG D genG w :=
  eq_of_rep ((compT_eq_of_commT (hF.cw w hw)) ▸
    Rep.compT (rep_wT hn hgen w) (rep_el hn hgen D.zIdx))
    (Rep.compT (rep_el hn hgen D.zIdx) (rep_wT hn hgen w))

theorem eq_one_or_eq_z_of_central (hF : Facts D) (hinv : ∀ l, genG (-l) = (genG l)⁻¹) {x : M}
    (hx : x ∈ S0 D genG) (hc : ∀ y ∈ S0 D genG, x * y = y * x) : x = 1 ∨ x = zG D genG := by
  obtain ⟨m, hm, rfl⟩ := (mem_S0_iff hn hgen hF hinv).1 hx
  have hcomm : ∀ s ∈ pcT D, commT D.n (el D m) s = true := by
    intro s hs
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hs
    have hmem : wG D genG w ∈ S0 D genG :=
      Subgroup.subset_closure (List.mem_map.2 ⟨w, hw, rfl⟩)
    have he := hc _ hmem
    exact beq_of_eq (he ▸ Rep.compT (rep_el hn hgen m) (rep_wT hn hgen w))
      (Rep.compT (rep_wT hn hgen w) (rep_el hn hgen m)) (size_compT' _ _) (size_compT' _ _)
  rcases hF.center _ (el_mem_elts hm) hcomm with h | h
  · exact Or.inl (eq_of_rep (h ▸ rep_el hn hgen m) (Rep.idT (G := M) hn))
  · exact Or.inr (eq_of_rep (h ▸ rep_el hn hgen m) (rep_el hn hgen D.zIdx))

end

end CFSG.CGT.Timmesfeld75.WCCheck
