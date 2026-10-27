module

public import CFSG.CGT.Timmesfeld75.ListWCPermGroup
public import CFSG.CGT.Timmesfeld75.ListWCBasic

public section

namespace CFSG.CGT.Timmesfeld75.WCCheck

open CFSG.Open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

variable {D : Data} {M : Subgroup (Equiv.Perm (Fin D.n))} {genG : ℤ → M}

theorem conj_mem {T : Subgroup M} {g x : M} (hg : g ∈ Subgroup.normalizer (T : Set M))
    (hx : x ∈ T) : g * x * g⁻¹ ∈ T :=
  (Subgroup.mem_normalizer_iff.1 hg x).1 hx

section

variable (hn : D.n < 2 ^ 32) (hgen : ∀ l, Rep D.n (D.gens l) (genG l))
  (hinv : ∀ l, genG (-l) = (genG l)⁻¹) (hF : Facts D)
include hn hgen hinv hF

theorem isPGroup_S0 : IsPGroup 2 (S0 D genG) :=
  IsPGroup.of_card (card_S0 hn hgen hF hinv)

theorem z_mem_of_le {T : Subgroup M} (hT : IsWC T) (hT1 : T ≠ ⊥) (hTS : T ≤ S0 D genG) :
    zG D genG ∈ T := by
  have hp := isPGroup_S0 hn hgen hinv hF
  have hSN : S0 D genG ≤ Subgroup.normalizer (T : Set M) := hT.le_normalizer_of_le_pGroup hp hTS
  have hnorm : (T.subgroupOf (S0 D genG)).Normal :=
    ⟨fun x hx g => (Subgroup.mem_normalizer_iff.1 (hSN g.2) x).1 hx⟩
  have hne : T.subgroupOf (S0 D genG) ≠ ⊥ := by
    intro h
    apply hT1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hTS hx⟩ : S0 D genG) ∈ T.subgroupOf (S0 D genG) := hx
    rw [h, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val this)
  have : Group.IsNilpotent (S0 D genG) := hp.isNilpotent
  obtain ⟨⟨u, huT, huZ⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hc : ∀ y ∈ S0 D genG, (u : M) * y = y * u := fun y hy =>
    (congrArg Subtype.val (Subgroup.mem_center_iff.1 huZ ⟨y, hy⟩)).symm
  rcases eq_one_or_eq_z_of_central hn hgen hF hinv u.2 hc with h | h
  · exact absurd (Subtype.ext (Subtype.ext h)) hu1
  · rw [← h]
    exact huT

omit hinv in
theorem mem_normalizer_of_comm_z {T : Subgroup M} (hT : IsWC T) (hz : zG D genG ∈ T) {g : M}
    (hg : g * zG D genG = zG D genG * g) : g ∈ Subgroup.normalizer (T : Set M) :=
  hT.centralizer_le_normalizer hz (z_ne_one hn hgen hF)
    (Subgroup.mem_centralizer_singleton_iff.2 hg)

theorem mem_allowed {T : Subgroup M} (hT : IsWC T) (hz : zG D genG ∈ T) (hTS : T ≤ S0 D genG)
    {x : M} (hx : x ∈ T) :
    x = 1 ∨ x = zG D genG ∨ ∃ c ∈ D.cls, ∃ p ∈ c, eltG (pcG D genG) p.1 = x := by
  obtain ⟨m, hm, rfl⟩ := (mem_S0_iff hn hgen hF hinv).1 (hTS hx)
  have hrm := rep_el hn hgen m
  have hp := isPGroup_S0 hn hgen hinv hF
  have hSN : S0 D genG ≤ Subgroup.normalizer (T : Set M) := hT.le_normalizer_of_le_pGroup hp hTS
  rcases hF.excl _ (el_mem_elts hm) with h | h | h | h
  · exact Or.inl (eq_of_rep (h ▸ hrm) (Rep.idT (G := M) hn))
  · exact Or.inr (Or.inl (eq_of_rep (h ▸ hrm) (rep_el hn hgen D.zIdx)))
  · obtain ⟨c, hc, p, hp', hpe⟩ := h
    exact Or.inr (Or.inr ⟨c, hc, p, hp', eq_of_rep (hpe ▸ rep_el hn hgen p.1) hrm⟩)
  · exfalso
    unfold excl at h
    simp only [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true] at h
    rcases h with (h | ⟨y, hy, hyc⟩) | ⟨g, hg, hwc⟩
    ·
      have hxx := elemAbelian_mul_self hT.1 hx
      have := beq_of_eq (hxx ▸ Rep.compT hrm hrm) (Rep.idT (G := M) hn) (size_compT' _ _)
        size_idT'
      rw [this] at h
      exact absurd h (by decide)
    ·
      obtain ⟨m', hm', rfl⟩ := mem_elts.1 hy
      have hry := rep_el hn hgen m'
      have hryi := Rep.inv_of_invOK hry (hF.invok _ (el_mem_elts hm'))
      have hymem : eltG (pcG D genG) m' ∈ S0 D genG :=
        (mem_S0_iff hn hgen hF hinv).2 ⟨m', hm', rfl⟩
      have hcT := conj_mem (hSN hymem) hx
      have hcomm := elemAbelian_mul_comm hT.1 hx hcT
      have hrc := Rep.compT (Rep.compT hry hrm) hryi
      have := beq_of_eq (hcomm ▸ Rep.compT hrm hrc) (Rep.compT hrc hrm) (size_compT' _ _)
        (size_compT' _ _)
      unfold commT conjT at hyc
      rw [this] at hyc
      exact absurd hyc (by decide)
    ·
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hg
      have hrw := rep_wT hn hgen w
      have hrwi := rep_wT hn hgen (invWord w)
      rw [wG_invWord hinv] at hrwi
      have hgN := mem_normalizer_of_comm_z hn hgen hF hT hz (cw_comm_z hn hgen hF hw)
      have hcT := conj_mem hgN hx
      have hrc := Rep.compT (Rep.compT hrw hrm) hrwi
      rcases hwc with hwc | hwc
      · obtain ⟨m'', hm'', he⟩ := (mem_S0_iff hn hgen hF hinv).1 (hTS hcT)
        have := beq_of_eq (he ▸ rep_el hn hgen m'') hrc (size_el _) (size_compT' _ _)
        have hmem : memL (elts D) (conjT D.n (wT D w) (wT D (invWord w)) (el D m)) = true :=
          memS_iff.2 (mem_elts.2 ⟨m'', hm'', beq_iff_eq.1 this⟩)
        rw [hmem] at hwc
        exact absurd hwc (by decide)
      · have hcomm := elemAbelian_mul_comm hT.1 hx hcT
        have := beq_of_eq (hcomm ▸ Rep.compT hrm hrc) (Rep.compT hrc hrm) (size_compT' _ _)
          (size_compT' _ _)
        unfold commT conjT at hwc
        rw [this] at hwc
        exact absurd hwc (by decide)

end

end CFSG.CGT.Timmesfeld75.WCCheck
