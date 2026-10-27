module

public import CFSG.GH74.QTGen4.U42.PairMatch

public section

namespace CFSG.GH74.QTGen4.U42

theorem exists_quotient_equiv_of_ker_range {K K' A : Type*} [Group K] [Group K'] [Group A]
    (f : K →* A) (f' : K' →* A) (Z : Subgroup K) (Z' : Subgroup K') [Z.Normal] [Z'.Normal]
    (hZ : f.ker = Z) (hZ' : f'.ker = Z') (hr : f.range = f'.range) :
    ∃ q : K ⧸ Z ≃* K' ⧸ Z', ∀ x : K, ∀ y : K',
      q (QuotientGroup.mk x) = QuotientGroup.mk y ↔ f x = f' y := by
  classical
  let a : K ⧸ Z ≃* f.range := (QuotientGroup.quotientMulEquivOfEq hZ.symm).trans
    (QuotientGroup.quotientKerEquivRange f)
  let a' : K' ⧸ Z' ≃* f'.range := (QuotientGroup.quotientMulEquivOfEq hZ'.symm).trans
    (QuotientGroup.quotientKerEquivRange f')
  let r : f.range ≃* f'.range :=
    { toFun := fun x => ⟨x, hr ▸ x.2⟩
      invFun := fun y => ⟨y, hr.symm ▸ y.2⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun y => Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext rfl }
  refine ⟨a.trans (r.trans a'.symm), ?_⟩
  intro x y
  constructor
  · intro hq
    have he := congrArg a' hq
    simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at he
    exact congrArg Subtype.val he
  · intro hf
    apply a'.injective
    simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    apply Subtype.ext
    exact hf

variable {G G' : Type*} [Group G] [Group G']
    {H B T U : Subgroup G} {H' B' T' U' : Subgroup G'}

def pairTEquiv (h : PairCore H B T U) (h' : PairCore H' B' T' U')
    (lam : ↥B ≃* ↥B')
    (hT : ∀ b : ↥B, (b : G) ∈ T ↔ ((lam b : ↥B') : G') ∈ T') :
    ↥(T.subgroupOf H) ≃* ↥(T'.subgroupOf H') :=
  (Subgroup.subgroupOfEquivOfLe (h.T_le_B.trans h.B_le_H)).trans
    ((Subgroup.subgroupOfEquivOfLe h.T_le_B).symm.trans
      ((restrictEquiv (T.subgroupOf B) (T'.subgroupOf B') lam (fun b => hT b)).trans
        ((Subgroup.subgroupOfEquivOfLe h'.T_le_B).trans
          (Subgroup.subgroupOfEquivOfLe (h'.T_le_B.trans h'.B_le_H)).symm)))

theorem pairTEquiv_apply (h : PairCore H B T U) (h' : PairCore H' B' T' U')
    (lam : ↥B ≃* ↥B')
    (hT : ∀ b : ↥B, (b : G) ∈ T ↔ ((lam b : ↥B') : G') ∈ T') (t : ↥(T.subgroupOf H)) :
    (((pairTEquiv h h' lam hT t : ↥(T'.subgroupOf H')) : ↥H') : G') =
      ((lam ⟨((t : ↥H) : G), h.T_le_B t.2⟩ : ↥B') : G') := by
  simp only [pairTEquiv, MulEquiv.trans_apply, restrictEquiv_apply]
  rfl

theorem exists_pair_action_lift [Finite G] [Finite G']
    (h : PairCore H B T U) (h' : PairCore H' B' T' U') (e : ↥U ≃* U0) (lam : ↥B ≃* ↥B')
    (hT : ∀ b : ↥B, (b : G) ∈ T ↔ ((lam b : ↥B') : G') ∈ T')
    (hU : ∀ b : ↥B, (b : G) ∈ U ↔ ((lam b : ↥B') : G') ∈ U') :
    ∃ θ : ↥H ≃* ↥H', ∀ x : ↥H,
      nuHom h'.U_normal (pairUCoords h h' e lam hU) (θ x) = nuHom h.U_normal e x := by
  let e' := pairUCoords h h' e lam hU
  let z := zH h e
  let z' := zH h' e'
  let f := nuHom h.U_normal e
  let f' := nuHom h'.U_normal e'
  have hz : z ∈ Subgroup.center ↥H := zH_mem_center h e
  have hz' : z' ∈ Subgroup.center ↥H' := zH_mem_center h' e'
  letI : (Subgroup.zpowers z).Normal := normal_zpowers_of_mem_center z hz
  letI : (Subgroup.zpowers z').Normal := normal_zpowers_of_mem_center z' hz'
  have hk : f.ker = Subgroup.zpowers z := by
    ext x
    exact nu_eq_one_iff_mem_zpowers h h.U_normal e x
  have hk' : f'.ker = Subgroup.zpowers z' := by
    ext x
    exact nu_eq_one_iff_mem_zpowers h' h'.U_normal e' x
  obtain ⟨q, hq⟩ := exists_quotient_equiv_of_ker_range f f' (Subgroup.zpowers z)
    (Subgroup.zpowers z') hk hk' (pair_action_range_eq h h' e lam hT hU)
  let θT := pairTEquiv h h' lam hT
  have hcomp : ∀ t : ↥(T.subgroupOf H), q (QuotientGroup.mk (t : ↥H)) =
      QuotientGroup.mk (θT t : ↥H') := by
    intro t
    apply (hq _ _).mpr
    let b : ↥B := ⟨((t : ↥H) : G), h.T_le_B t.2⟩
    have hl : Subgroup.inclusion h.B_le_H b = (t : ↥H) := Subtype.ext rfl
    have hr : Subgroup.inclusion h'.B_le_H (lam b) = (θT t : ↥H') := by
      apply Subtype.ext
      exact (pairTEquiv_apply h h' lam hT t).symm
    rw [← hl, ← hr]
    exact nuHom_lam h h' e lam hU b
  have h2 : IsPGroup 2 (T.subgroupOf H) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h.T_two
    apply IsPGroup.of_card (n := n)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h.T_le_B.trans h.B_le_H)).toEquiv]
    exact hn
  have h2' : IsPGroup 2 (T'.subgroupOf H') := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h'.T_two
    apply IsPGroup.of_card (n := n)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h'.T_le_B.trans h'.B_le_H)).toEquiv]
    exact hn
  obtain ⟨θ, hθ⟩ := central_extension_rigidity z z' hz hz' (zH_orderOf h e) (zH_orderOf h' e')
    (T.subgroupOf H) (T'.subgroupOf H') h2 h2' h.T_odd_index h'.T_odd_index q θT hcomp
  refine ⟨θ, ?_⟩
  intro x
  exact ((hq x (θ x)).mp (hθ x).symm).symm

theorem pair_action_lift_kernel_iff
    (h : PairCore H B T U) (h' : PairCore H' B' T' U') (e : ↥U ≃* U0) (lam : ↥B ≃* ↥B')
    (hU : ∀ b : ↥B, (b : G) ∈ U ↔ ((lam b : ↥B') : G') ∈ U') (α : ↥H ≃* ↥H')
    (hα : ∀ x : ↥H, nuHom h'.U_normal (pairUCoords h h' e lam hU) (α x) =
      nuHom h.U_normal e x) (x : ↥H) :
    α x ∈ Subgroup.zpowers (zH h' (pairUCoords h h' e lam hU)) ↔
      x ∈ Subgroup.zpowers (zH h e) := by
  rw [← nu_eq_one_iff_mem_zpowers h' h'.U_normal (pairUCoords h h' e lam hU) (α x),
    ← nu_eq_one_iff_mem_zpowers h h.U_normal e x]
  change nuHom h'.U_normal (pairUCoords h h' e lam hU) (α x) = 1 ↔
    nuHom h.U_normal e x = 1
  rw [hα x]

end CFSG.GH74.QTGen4.U42
