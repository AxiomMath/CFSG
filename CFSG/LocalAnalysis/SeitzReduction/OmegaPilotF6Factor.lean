module

import CFSG.Quasithin.Background.A3ComponentsQuotient
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotRootCentralizerPerfect

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)

section Levi

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem apply_f_of_mem_rootLevi {P₁ P₂ : HypPair Q} (h₁₂ : P₁.Orth P₂) {g : V ≃ₗ[K] V}
    (hg : g ∈ rootLevi Q P₁ P₂) (h1 : g P₁.e = P₁.e) (h2 : g P₂.e = P₂.e) :
    g P₁.f = P₁.f ∧ g P₂.f = P₂.f := by
  obtain ⟨hf1, hf2⟩ := apply_e_of_commute (orth_flipPair_flipPair h₁₂)
    (mem_centralizer_singleton_iff.mp hg.2)
  simp only [flipPair_e, flipPair_f, h1, h2, P₁.polar_ef, P₂.polar_ef, one_smul] at hf1 hf2
  rw [polar_comm Q P₂.e P₁.f, h₁₂.fe, zero_smul, sub_zero] at hf1
  rw [h₁₂.ef, zero_smul, sub_zero] at hf2
  exact ⟨hf1, hf2⟩

end Levi

section Coord

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {a a' b b' : Fin d}

theorem rootLevi_apply_e_eq (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b')
    (hd : PairDisjoint a a' b b') {g : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hg : g ∈ rootLevi Q hi.hypPair hj.hypPair) :
    g (Pi.single a 1) = (g (Pi.single a 1)) a • Pi.single a 1 +
        (g (Pi.single a 1)) b • Pi.single b 1 ∧
      g (Pi.single b 1) = (g (Pi.single b 1)) a • Pi.single a 1 +
        (g (Pi.single b 1)) b • Pi.single b 1 := by
  obtain ⟨h1, h2⟩ := apply_e_of_commute (hi.orth hj hd) (mem_centralizer_singleton_iff.mp hg.1.2)
  simp only [IsHypCoord.hypPair_e, IsHypCoord.hypPair_f] at h1 h2
  have key : ∀ α β : K, (α • Pi.single a 1 - β • Pi.single b 1 : Fin d → K) =
      (α • Pi.single a 1 - β • Pi.single b 1 : Fin d → K) a • Pi.single a 1 +
        (α • Pi.single a 1 - β • Pi.single b 1 : Fin d → K) b • Pi.single b 1 := by
    intro α β
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne hd.left_ne_left, Pi.single_eq_of_ne hd.left_ne_left.symm, smul_eq_mul,
      mul_one, mul_zero, sub_zero, zero_sub]
    module
  constructor
  · rw [h1]
    exact key _ _
  · rw [h2, show ∀ α β : K, (α • Pi.single b 1 - β • Pi.single a 1 : Fin d → K) =
      (-β) • Pi.single a 1 - (-α) • Pi.single b 1 from fun α β => by module]
    exact key _ _

theorem stabPairsBar_subgroupOf_normal (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b')
    (hd : PairDisjoint a a' b b') :
    ((stabPairsBar Q a a' b b').subgroupOf (rootLeviBar Q hi.hypPair hj.hypPair)).Normal := by
  have h₁₂ := hi.orth hj hd
  refine ⟨fun x hx m => mem_subgroupOf.mpr ?_⟩
  obtain ⟨X, hX, hXx⟩ := mem_map.mp (mem_subgroupOf.mp hx)
  obtain ⟨Y, hY, hYm⟩ := mem_map.mp m.2
  have hX' := mem_subgroupOf.mp hX
  have hY' : (Y : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ rootLevi Q hi.hypPair hj.hypPair :=
    mem_subgroupOf.mp hY
  obtain ⟨⟨hXa, hXa'⟩, hXb, hXb'⟩ := hX'
  have hYi : (Y : (Fin d → K) ≃ₗ[K] (Fin d → K))⁻¹ ∈ rootLevi Q hi.hypPair hj.hypPair :=
    inv_mem hY'
  obtain ⟨hYa, hYb⟩ := rootLevi_apply_e_eq hi hj hd hYi
  set g : (Fin d → K) ≃ₗ[K] (Fin d → K) := (Y : (Fin d → K) ≃ₗ[K] (Fin d → K)) *
    (X : (Fin d → K) ≃ₗ[K] (Fin d → K)) * (Y : (Fin d → K) ≃ₗ[K] (Fin d → K))⁻¹ with hg
  have hXP : ∀ α β : K, (X : (Fin d → K) ≃ₗ[K] (Fin d → K))
      (α • Pi.single a 1 + β • Pi.single b 1) = α • Pi.single a 1 + β • Pi.single b 1 := by
    intro α β
    rw [map_add, map_smul, map_smul, hXa, hXb]
  have hga : g (Pi.single a 1) = Pi.single a 1 := by
    rw [hg, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hYa, hXP, ← hYa,
      LinearEquiv.apply_inv_apply']
  have hgb : g (Pi.single b 1) = Pi.single b 1 := by
    rw [hg, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hYb, hXP, ← hYb,
      LinearEquiv.apply_inv_apply']
  have hXL : (X : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ rootLevi Q hi.hypPair hj.hypPair :=
    mem_rootLevi_of_fix (Subgroup.commutator_le_self _ X.2) hXa hXa' hXb hXb'
  have hgL : g ∈ rootLevi Q hi.hypPair hj.hypPair := mul_mem (mul_mem hY' hXL) hYi
  obtain ⟨hga', hgb'⟩ := apply_f_of_mem_rootLevi h₁₂ hgL hga hgb
  have hgΩ : g ∈ orthDerived Q := mul_mem (mul_mem Y.2 X.2) (inv_mem Y.2)
  refine ⟨⟨g, hgΩ⟩, mem_subgroupOf.mpr ⟨⟨hga, hga'⟩, hgb, hgb'⟩, ?_⟩
  have : (⟨g, hgΩ⟩ : orthDerived Q) = Y * X * Y⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv, hXx, hYm]
  rfl

end Coord

section Factor

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {a a' b b' : Fin d}

@[expose] noncomputable def projLift (hQ : ∃ v, Q v ≠ 0) (x : matrixProjectiveDerived Q) :
    (Fin d → K) ≃ₗ[K] (Fin d → K) :=
  (((MulEquiv.ofBijective (projHom Q) ⟨projHom_injective hQ, projHom_surjective Q⟩).symm x :
    orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K))

omit [Finite K] in
theorem projHom_projLift (hQ : ∃ v, Q v ≠ 0) (x : matrixProjectiveDerived Q) :
    projHom Q ⟨projLift hQ x, ((MulEquiv.ofBijective (projHom Q)
      ⟨projHom_injective hQ, projHom_surjective Q⟩).symm x).2⟩ = x :=
  (MulEquiv.ofBijective (projHom Q) ⟨projHom_injective hQ, projHom_surjective Q⟩).apply_symm_apply x

omit [Finite K] in
theorem projLift_projHom (hQ : ∃ v, Q v ≠ 0) (X : orthDerived Q) :
    projLift hQ (projHom Q X) = X := by
  rw [projLift]
  exact congrArg Subtype.val
    ((MulEquiv.ofBijective (projHom Q)
      ⟨projHom_injective hQ, projHom_surjective Q⟩).symm_apply_apply X)

omit [Finite K] in
theorem projLift_mul (hQ : ∃ v, Q v ≠ 0) (x y : matrixProjectiveDerived Q) :
    projLift hQ (x * y) = projLift hQ x * projLift hQ y := by
  rw [projLift, map_mul]
  rfl

omit [Finite K] in
theorem projLift_inv (hQ : ∃ v, Q v ≠ 0) (x : matrixProjectiveDerived Q) :
    projLift hQ x⁻¹ = (projLift hQ x)⁻¹ := by
  rw [projLift, map_inv]
  rfl

omit [Finite K] in
theorem projLift_mem_of_mem_map (hQ : ∃ v, Q v ≠ 0) {H : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K))}
    {x : matrixProjectiveDerived Q} (hx : x ∈ (H.subgroupOf (orthDerived Q)).map (projHom Q)) :
    projLift hQ x ∈ H := by
  obtain ⟨X, hX, rfl⟩ := hx
  rw [projLift_projHom]
  exact mem_subgroupOf.mp hX

theorem map_eq_of_normal_of_isQuasisimple {M : Type*} [Group M] [Finite M] {B : Subgroup M}
    (hBn : B.Normal) (hBq : CFSG.IsQuasisimple B) (hBz : center B = ⊥) (ι : M ≃* M)
    (hsmall : ∀ N : Subgroup M, N ⊓ B = ⊥ → Nat.card N < Nat.card B) :
    B.map ι.toMonoidHom = B := by
  have eN : B ≃* B.map ι.toMonoidHom := B.equivMapOfInjective _ ι.injective
  have hNq : CFSG.IsQuasisimple (B.map ι.toMonoidHom) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eN hBq
  have hNz : center (B.map ι.toMonoidHom) = ⊥ := by
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv eN, hBz,
      Subgroup.map_bot]
  have hcardN : Nat.card (B.map ι.toMonoidHom) = Nat.card B := (Nat.card_congr eN.toEquiv).symm
  have hTn : (B.subgroupOf (B.map ι.toMonoidHom)).Normal := hBn.subgroupOf _
  rcases CFSG.Quasithin.A3.eq_top_or_le_center_of_subnormal hNq hTn.isSubnormal with htop | hcen
  · have hle : B.map ι.toMonoidHom ≤ B := fun x hx => by
      have h : (⟨x, hx⟩ : B.map ι.toMonoidHom) ∈ B.subgroupOf (B.map ι.toMonoidHom) :=
        htop ▸ mem_top _
      exact mem_subgroupOf.mp h
    exact eq_of_le_of_card_ge hle hcardN.ge
  · exfalso
    have hinf : B.map ι.toMonoidHom ⊓ B = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxN, hxB⟩
      have h : (⟨x, hxN⟩ : B.map ι.toMonoidHom) ∈ B.subgroupOf (B.map ι.toMonoidHom) :=
        mem_subgroupOf.mpr hxB
      have hT0 : B.subgroupOf (B.map ι.toMonoidHom) = ⊥ := by
        rw [eq_bot_iff]
        exact hcen.trans hNz.le
      rw [hT0, mem_bot] at h
      rw [mem_bot]
      exact congrArg Subtype.val h
    exact (hsmall _ hinf).ne hcardN

theorem card_lt_of_inf_stabPairsBar_eq_bot (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b')
    (hd : PairDisjoint a a' b b') {N : Subgroup (rootLeviBar Q hi.hypPair hj.hypPair)}
    (hN : N ⊓ (stabPairsBar Q a a' b b').subgroupOf (rootLeviBar Q hi.hypPair hj.hypPair) = ⊥) :
    Nat.card N < Nat.card K ^ 4 := by
  classical
  have h₁₂ := hi.orth hj hd
  have hQ' := hi.exists_ne_zero
  have hLevi : ∀ x : N, projLift hQ' (((x : rootLeviBar Q hi.hypPair hj.hypPair) :
      matrixProjectiveDerived Q)) ∈ rootLevi Q hi.hypPair hj.hypPair :=
    fun x => projLift_mem_of_mem_map hQ' (x : rootLeviBar Q hi.hypPair hj.hypPair).2
  let ℓ : N → (Fin d → K) ≃ₗ[K] (Fin d → K) := fun x =>
    projLift hQ' ((x : rootLeviBar Q hi.hypPair hj.hypPair) : matrixProjectiveDerived Q)
  let r : N → K × K × K × K := fun x =>
    (ℓ x (Pi.single a 1) a, ℓ x (Pi.single a 1) b, ℓ x (Pi.single b 1) a, ℓ x (Pi.single b 1) b)
  have hr : Function.Injective r := by
    intro x y hxy
    simp only [r, Prod.mk.injEq] at hxy
    obtain ⟨h1, h2, h3, h4⟩ := hxy
    obtain ⟨hxa, hxb⟩ := rootLevi_apply_e_eq hi hj hd (hLevi x)
    obtain ⟨hya, hyb⟩ := rootLevi_apply_e_eq hi hj hd (hLevi y)
    have ea : ℓ x (Pi.single a 1) = ℓ y (Pi.single a 1) := by
      change projLift _ _ _ = projLift _ _ _
      rw [hxa, hya]
      exact congrArg₂ (· + ·) (congrArg (· • _) h1) (congrArg (· • _) h2)
    have eb : ℓ x (Pi.single b 1) = ℓ y (Pi.single b 1) := by
      change projLift _ _ _ = projLift _ _ _
      rw [hxb, hyb]
      exact congrArg₂ (· + ·) (congrArg (· • _) h3) (congrArg (· • _) h4)
    have hzl : ℓ (x⁻¹ * y) = (ℓ x)⁻¹ * ℓ y := by
      change projLift _ _ = _
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv,
        projLift_mul, projLift_inv]
    have hfix : ∀ v, ℓ x v = ℓ y v → ℓ (x⁻¹ * y) v = v := fun v hv => by
      rw [hzl, LinearEquiv.mul_apply, ← hv, LinearEquiv.inv_apply_apply']
    have hza := hfix _ ea
    have hzb := hfix _ eb
    obtain ⟨hza', hzb'⟩ := apply_f_of_mem_rootLevi h₁₂ (hLevi (x⁻¹ * y)) hza hzb
    have hzB : (((x⁻¹ * y : N) : rootLeviBar Q hi.hypPair hj.hypPair) :
        matrixProjectiveDerived Q) ∈ stabPairsBar Q a a' b b' := by
      rw [← projHom_projLift hQ' (((x⁻¹ * y : N) : rootLeviBar Q hi.hypPair hj.hypPair) :
        matrixProjectiveDerived Q)]
      exact ⟨_, mem_subgroupOf.mpr ⟨⟨hza, hza'⟩, hzb, hzb'⟩, rfl⟩
    have hz : ((x⁻¹ * y : N) : rootLeviBar Q hi.hypPair hj.hypPair) ∈
        N ⊓ (stabPairsBar Q a a' b b').subgroupOf (rootLeviBar Q hi.hypPair hj.hypPair) :=
      ⟨(x⁻¹ * y).2, mem_subgroupOf.mpr hzB⟩
    rw [hN, mem_bot] at hz
    have hz' : x⁻¹ * y = 1 := Subtype.ext hz
    exact inv_mul_eq_one.mp hz'
  have hns : ¬ Function.Surjective r := by
    intro hsurj
    obtain ⟨x, hx⟩ := hsurj (0, 0, 0, 0)
    simp only [r, Prod.mk.injEq] at hx
    obtain ⟨hxa, -⟩ := rootLevi_apply_e_eq hi hj hd (hLevi x)
    change ℓ x (Pi.single a 1) = _ at hxa
    rw [hx.1, hx.2.1, zero_smul, zero_smul, add_zero] at hxa
    exact hi.hypPair.e_ne_zero ((ℓ x).injective (hxa.trans (map_zero _).symm))
  have := Fintype.ofFinite N
  have := Fintype.ofFinite K
  have hlt := Fintype.card_lt_of_injective_not_surjective r hr hns
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_prod, Nat.card_prod,
    Nat.card_prod] at hlt
  have h4 : Nat.card K * (Nat.card K * (Nat.card K * Nat.card K)) = Nat.card K ^ 4 := by ring
  omega

theorem map_stabPairsBar_subgroupOf_eq (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b')
    (hd : PairDisjoint a a' b b')
    (hS : CFSG.IsQuasisimple (stabPairsBar Q a a' b b') ∧ center (stabPairsBar Q a a' b b') = ⊥)
    (hcard : Nat.card K ^ 4 ≤ Nat.card (stabPairsBar Q a a' b b'))
    (ι : rootLeviBar Q hi.hypPair hj.hypPair ≃* rootLeviBar Q hi.hypPair hj.hypPair) :
    ((stabPairsBar Q a a' b b').subgroupOf (rootLeviBar Q hi.hypPair hj.hypPair)).map
        ι.toMonoidHom =
      (stabPairsBar Q a a' b b').subgroupOf (rootLeviBar Q hi.hypPair hj.hypPair) := by
  have hBM := stabPairsBar_le_rootLeviBar hi hj
  have eB : stabPairsBar Q a a' b b' ≃*
      (stabPairsBar Q a a' b b').subgroupOf (rootLeviBar Q hi.hypPair hj.hypPair) :=
    (subgroupOfEquivOfLe hBM).symm
  refine map_eq_of_normal_of_isQuasisimple (stabPairsBar_subgroupOf_normal hi hj hd)
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv eB hS.1) ?_ ι fun N hN => ?_
  · rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv eB, hS.2,
      Subgroup.map_bot]
  · rw [← Nat.card_congr eB.toEquiv]
    exact (card_lt_of_inf_stabPairsBar_eq_bot hi hj hd hN).trans_le hcard

end Factor

end CFSG.SeitzReduction.OmegaPilot
