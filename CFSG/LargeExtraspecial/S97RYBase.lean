module

public import CFSG.LargeExtraspecial.S97RYCheck
public import CFSG.CGT.Timmesfeld75.ListWCPermMask
public import CFSG.CGT.Timmesfeld75.L2Pair

public section

namespace CFSG.LargeExtraspecial.S11.PairCheck

open CFSG.Open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.CGT.Timmesfeld75
  CFSG.CGT.Timmesfeld75.WCCheck

structure BaseFacts (D : Data) : Prop where
  nodup : (elts D).Nodup
  closed : ∀ x ∈ elts D, ∀ s ∈ pcT D, memS D (compT D.n x s) = true
  closedInv : ∀ x ∈ elts D, ∀ w ∈ D.pc, memS D (compT D.n x (wT D (invWord w))) = true
  invok : ∀ x ∈ elts D, invOK D.n x (invT D.n x) = true
  zlt : D.zIdx < 2 ^ D.pc.length
  zne : ¬ (el D D.zIdx = idT D.n)
  zsq : compT D.n (el D D.zIdx) (el D D.zIdx) = idT D.n
  zcomm : ∀ s ∈ pcT D, commT D.n (el D D.zIdx) s = true
  center : ∀ x ∈ elts D, (∀ s ∈ pcT D, commT D.n x s = true) →
    x = idT D.n ∨ x = el D D.zIdx
  cw : ∀ w ∈ D.cw, commT D.n (wT D w) (el D D.zIdx) = true
  exclOK : ∀ x ∈ elts D, x = idT D.n ∨ x = el D D.zIdx ∨
    (∃ c ∈ D.cls, ∃ p ∈ c, el D p.1 = x) ∨ excl D.n (elts D) (cwT D) x = true
  idxNodup : (0 :: D.zIdx :: (D.cls.flatMap fun c => c.map Prod.fst)).Nodup
  idxLt : ∀ i ∈ (D.cls.flatMap fun c => c.map Prod.fst), i < 2 ^ D.pc.length
  classes : ∀ c ∈ D.cls, (match c with
    | [] => false
    | (i₀, _) :: _ => c.all fun p => commT D.n (wT D p.2) (el D D.zIdx) &&
        conjT D.n (wT D p.2) (wT D (invWord p.2)) (el D i₀) == el D p.1) = true

theorem baseFacts_of_check {D : Data} (h : baseCheck D = true) : BaseFacts D := by
  unfold baseCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    beq_iff_eq, List.any_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩ := h
  refine ⟨h1, h2, h3, h4, h5, fun he => ?_, h7, h8, fun x hx hc => ?_, h10, fun x hx => ?_, h12,
    h13, h14⟩
  · rw [he] at h6
    simp at h6
  · rcases h9 x hx with (h | h) | h
    · rw [List.all_eq_true.2 hc] at h
      exact absurd h (by decide)
    · exact Or.inl h
    · exact Or.inr h
  · rcases h11 x hx with ((h | h) | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

variable {D : Data} {M : Subgroup (Equiv.Perm (Fin D.n))} {genG : ℤ → M}

section

variable (hn : D.n < 2 ^ 32) (hgen : ∀ l, Rep D.n (D.gens l) (genG l))
include hn hgen

theorem mem_S0_iff_base (hF : BaseFacts D) (hinv : ∀ l, genG (-l) = (genG l)⁻¹) {g : M} :
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

theorem eltG_inj_base (hF : BaseFacts D) {m m' : ℕ} (hm : m < 2 ^ D.pc.length)
    (hm' : m' < 2 ^ D.pc.length) (h : eltG (pcG D genG) m = eltG (pcG D genG) m') : m = m' :=
  List.inj_on_of_nodup_map hF.nodup (List.mem_range.2 hm) (List.mem_range.2 hm')
    (el_eq_of_eltG_eq hn hgen h)

theorem card_S0_base (hF : BaseFacts D) (hinv : ∀ l, genG (-l) = (genG l)⁻¹) :
    Nat.card (S0 D genG) = 2 ^ D.pc.length := by
  have h : Nat.card (Fin (2 ^ D.pc.length)) = Nat.card (S0 D genG) := by
    refine Nat.card_eq_of_bijective (fun i : Fin (2 ^ D.pc.length) =>
      (⟨eltG (pcG D genG) i, (mem_S0_iff_base hn hgen hF hinv).2 ⟨i, i.2, rfl⟩⟩ : S0 D genG))
      ⟨fun i j hij => Fin.ext (eltG_inj_base hn hgen hF i.2 j.2 (congrArg Subtype.val hij)), ?_⟩
    rintro ⟨g, hg⟩
    obtain ⟨m, hm, rfl⟩ := (mem_S0_iff_base hn hgen hF hinv).1 hg
    exact ⟨⟨m, hm⟩, rfl⟩
  rw [← h, Nat.card_fin]

theorem zG_ne_one (hF : BaseFacts D) : zG D genG ≠ 1 := fun h =>
  hF.zne (beq_iff_eq.1 (beq_of_eq (rep_el hn hgen D.zIdx)
    (by rw [show eltG (pcG D genG) D.zIdx = 1 from h]; exact Rep.idT (G := M) hn)
    (size_el _) size_idT'))

theorem cw_comm_zG (hF : BaseFacts D) {w : List ℤ} (hw : w ∈ D.cw) :
    wG D genG w * zG D genG = zG D genG * wG D genG w :=
  eq_of_rep ((compT_eq_of_commT (hF.cw w hw)) ▸
    Rep.compT (rep_wT hn hgen w) (rep_el hn hgen D.zIdx))
    (Rep.compT (rep_el hn hgen D.zIdx) (rep_wT hn hgen w))

theorem eq_one_or_eq_zG (hF : BaseFacts D) (hinv : ∀ l, genG (-l) = (genG l)⁻¹) {x : M}
    (hx : x ∈ S0 D genG) (hc : ∀ y ∈ S0 D genG, x * y = y * x) : x = 1 ∨ x = zG D genG := by
  obtain ⟨m, hm, rfl⟩ := (mem_S0_iff_base hn hgen hF hinv).1 hx
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

section

variable (hn : D.n < 2 ^ 32) (hgen : ∀ l, Rep D.n (D.gens l) (genG l))
  (hinv : ∀ l, genG (-l) = (genG l)⁻¹) (hF : BaseFacts D)
include hn hgen hinv hF

theorem isPGroup_S0_base : IsPGroup 2 (S0 D genG) :=
  IsPGroup.of_card (card_S0_base hn hgen hF hinv)

theorem zG_mem_of_le {T : Subgroup M} (hT : IsWC T) (hT1 : T ≠ ⊥) (hTS : T ≤ S0 D genG) :
    zG D genG ∈ T := by
  have hp := isPGroup_S0_base hn hgen hinv hF
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
  rcases eq_one_or_eq_zG hn hgen hF hinv u.2 hc with h | h
  · exact absurd (Subtype.ext (Subtype.ext h)) hu1
  · rw [← h]
    exact huT

omit hinv in
theorem mem_normalizer_of_comm_zG {T : Subgroup M} (hT : IsWC T) (hz : zG D genG ∈ T) {g : M}
    (hg : g * zG D genG = zG D genG * g) : g ∈ Subgroup.normalizer (T : Set M) :=
  hT.centralizer_le_normalizer hz (zG_ne_one hn hgen hF)
    (Subgroup.mem_centralizer_singleton_iff.2 hg)

theorem mem_allowed_base {T : Subgroup M} (hT : IsWC T) (hz : zG D genG ∈ T)
    (hTS : T ≤ S0 D genG) {x : M} (hx : x ∈ T) :
    x = 1 ∨ x = zG D genG ∨ ∃ c ∈ D.cls, ∃ p ∈ c, eltG (pcG D genG) p.1 = x := by
  obtain ⟨m, hm, rfl⟩ := (mem_S0_iff_base hn hgen hF hinv).1 (hTS hx)
  have hrm := rep_el hn hgen m
  have hp := isPGroup_S0_base hn hgen hinv hF
  have hSN : S0 D genG ≤ Subgroup.normalizer (T : Set M) := hT.le_normalizer_of_le_pGroup hp hTS
  rcases hF.exclOK _ (el_mem_elts hm) with h | h | h | h
  · exact Or.inl (eq_of_rep (h ▸ hrm) (Rep.idT (G := M) hn))
  · exact Or.inr (Or.inl (eq_of_rep (h ▸ hrm) (rep_el hn hgen D.zIdx)))
  · obtain ⟨c, hc, p, hp', hpe⟩ := h
    exact Or.inr (Or.inr ⟨c, hc, p, hp', eq_of_rep (hpe ▸ rep_el hn hgen p.1) hrm⟩)
  · exfalso
    unfold excl at h
    simp only [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true] at h
    rcases h with (h | ⟨y, hy, hyc⟩) | ⟨g, hg, hwc⟩
    · have hxx := elemAbelian_mul_self hT.1 hx
      have := beq_of_eq (hxx ▸ Rep.compT hrm hrm) (Rep.idT (G := M) hn) (size_compT' _ _)
        size_idT'
      rw [this] at h
      exact absurd h (by decide)
    · obtain ⟨m', hm', rfl⟩ := mem_elts.1 hy
      have hry := rep_el hn hgen m'
      have hryi := Rep.inv_of_invOK hry (hF.invok _ (el_mem_elts hm'))
      have hymem : eltG (pcG D genG) m' ∈ S0 D genG :=
        (mem_S0_iff_base hn hgen hF hinv).2 ⟨m', hm', rfl⟩
      have hcT := conj_mem (hSN hymem) hx
      have hcomm := elemAbelian_mul_comm hT.1 hx hcT
      have hrc := Rep.compT (Rep.compT hry hrm) hryi
      have := beq_of_eq (hcomm ▸ Rep.compT hrm hrc) (Rep.compT hrc hrm) (size_compT' _ _)
        (size_compT' _ _)
      unfold commT conjT at hyc
      rw [this] at hyc
      exact absurd hyc (by decide)
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hg
      have hrw := rep_wT hn hgen w
      have hrwi := rep_wT hn hgen (invWord w)
      rw [wG_invWord hinv] at hrwi
      have hgN := mem_normalizer_of_comm_zG hn hgen hF hT hz (cw_comm_zG hn hgen hF hw)
      have hcT := conj_mem hgN hx
      have hrc := Rep.compT (Rep.compT hrw hrm) hrwi
      rcases hwc with hwc | hwc
      · obtain ⟨m'', hm'', he⟩ := (mem_S0_iff_base hn hgen hF hinv).1 (hTS hcT)
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

theorem mem_of_mem_cls_base {T : Subgroup M} (hT : IsWC T) (hz : zG D genG ∈ T)
    {c : List (ℕ × List ℤ)} (hc : c ∈ D.cls) {p : ℕ × List ℤ} (hp : p ∈ c)
    (hpT : eltG (pcG D genG) p.1 ∈ T) {q : ℕ × List ℤ} (hq : q ∈ c) :
    eltG (pcG D genG) q.1 ∈ T := by
  have h := hF.classes c hc
  match c, hc, h, hp, hq with
  | [], _, h, _, _ => exact absurd h Bool.false_ne_true
  | (i₀, w₀) :: rest, _, h, hp, hq =>
    simp only [List.all_eq_true, Bool.and_eq_true] at h
    have hcl : ∀ r ∈ (i₀, w₀) :: rest, ∃ g : M, g * zG D genG = zG D genG * g ∧
        g * eltG (pcG D genG) i₀ * g⁻¹ = eltG (pcG D genG) r.1 := by
      intro r hr
      obtain ⟨h1, h2⟩ := h r hr
      have hrw := rep_wT hn hgen r.2
      have hrwi := rep_wT hn hgen (invWord r.2)
      rw [wG_invWord hinv] at hrwi
      refine ⟨wG D genG r.2, eq_of_rep ((compT_eq_of_commT h1) ▸
        Rep.compT hrw (rep_el hn hgen D.zIdx)) (Rep.compT (rep_el hn hgen D.zIdx) hrw), ?_⟩
      exact eq_of_beq (Rep.compT (Rep.compT hrw (rep_el hn hgen i₀)) hrwi) (rep_el hn hgen r.1)
        h2
    obtain ⟨gp, hgpz, hgp⟩ := hcl p hp
    obtain ⟨gq, hgqz, hgq⟩ := hcl q hq
    have hNp := mem_normalizer_of_comm_zG hn hgen hF hT hz hgpz
    have hNq := mem_normalizer_of_comm_zG hn hgen hF hT hz hgqz
    have h0 : eltG (pcG D genG) i₀ ∈ T := by
      have := conj_mem (Subgroup.inv_mem _ hNp) hpT
      rwa [← hgp, inv_inv, show gp⁻¹ * (gp * eltG (pcG D genG) i₀ * gp⁻¹) * gp =
        eltG (pcG D genG) i₀ by group] at this
    rw [← hgq]
    exact conj_mem hNq h0

end

end CFSG.LargeExtraspecial.S11.PairCheck
