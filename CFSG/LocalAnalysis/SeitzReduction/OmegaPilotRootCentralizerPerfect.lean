module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotRootCentralizer
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotTorusLayer
import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus regular_coordinateQuadPlus)
open CFSG.Quasithin (perfectCore)

section Coord

variable {K : Type*} [Field K] {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι']

theorem extend_single {j : ι' → ι} (hj : Function.Injective j) (x : ι') :
    Function.extend j (Pi.single x (1 : K)) 0 = Pi.single (j x) 1 := by
  funext i
  by_cases hi : ∃ y, j y = i
  · obtain ⟨y, rfl⟩ := hi
    rw [hj.extend_apply]
    by_cases hyx : y = x
    · subst hyx
      simp
    · rw [Pi.single_eq_of_ne hyx, Pi.single_eq_of_ne (fun h => hyx (hj h))]
  · rw [Function.extend_apply' _ _ _ hi, Pi.single_eq_of_ne (fun h => hi ⟨x, h.symm⟩)]
    rfl

theorem single_comp {j : ι' → ι} (hj : Function.Injective j) (x : ι') :
    (fun y => (Pi.single (j x) (1 : K) : ι → K) (j y)) = Pi.single x 1 := by
  funext y
  by_cases hyx : y = x
  · subst hyx
    simp
  · rw [Pi.single_eq_of_ne (fun h => hyx (hj h)), Pi.single_eq_of_ne hyx]

end Coord

section Formula

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

omit [Finite K] [CharP K 2] in
theorem orthDerivedCongr_apply {V V' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module K V'] {R : QuadraticForm K V} {R' : QuadraticForm K V'} (e : R.IsometryEquiv R')
    (g : orthDerived R) (w : V') :
    ((orthDerivedCongr e g : orthDerived R') : V' ≃ₗ[K] V') w =
      e.toLinearEquiv ((g : V ≃ₗ[K] V) (e.toLinearEquiv.symm w)) := by
  change LinearEquiv.autCongr e.toLinearEquiv (g : V ≃ₗ[K] V) w = _
  rw [LinearEquiv.autCongr_apply_apply]

theorem pairPerpEquiv_apply (hn : 4 ≤ n) (i : Fin n) (x : pairPerp (K := K) i)
    (G : orthDerived (coordinateQuadPlus n K))
    (hG : (G : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) ∈
      stabSub (plusIndexEquiv n (.inl i)) (plusIndexEquiv n (.inr i)))
    (hxG : (x : matrixProjectiveDerived (coordinateQuadPlus n K)) = projHom _ G)
    (w : Fin (2 * (n - 1)) → K) (y : Fin (2 * (n - 1))) :
    ((pairPerpEquiv hn i x : orthDerived (coordinateQuadPlus (n - 1) K)) :
        (Fin (2 * (n - 1)) → K) ≃ₗ[K] (Fin (2 * (n - 1)) → K)) w y =
      (G : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K))
        (Function.extend (plusPerpCoord (by omega) i) w 0) (plusPerpCoord (by omega) i y) := by
  have hsymm : ((stabDerived (coordinateQuadPlus n K) (plusIndexEquiv n (.inl i))
      (plusIndexEquiv n (.inr i))).equivMapOfInjective (projHom _)
      (projHom_injective (isHypCoord_coordinateQuadPlus (K := K) i).exists_ne_zero)).symm x =
      ⟨G, hG⟩ :=
    (MulEquiv.symm_apply_eq _).mpr (Subtype.ext hxG)
  have e1 : pairPerpEquiv hn i x = orthDerivedCongr (plusPerpIsometry (by omega) i)
      ((isHypCoord_coordinateQuadPlus (K := K) i).stabDerivedEquiv
        (regular_coordinateQuadPlus n K (by omega)).1 (regular_plusPerp hn i).1
        (regular_plusPerp hn i).2 ⟨G, hG⟩) := by
    unfold pairPerpEquiv IsHypCoord.pairPerpOfEquiv
    change orthDerivedCongr (plusPerpIsometry (by omega) i)
      ((isHypCoord_coordinateQuadPlus (K := K) i).stabDerivedEquiv
        (regular_coordinateQuadPlus n K (by omega)).1 (regular_plusPerp hn i).1
        (regular_plusPerp hn i).2
        (((stabDerived (coordinateQuadPlus n K) (plusIndexEquiv n (.inl i))
          (plusIndexEquiv n (.inr i))).equivMapOfInjective (projHom _)
          (projHom_injective (isHypCoord_coordinateQuadPlus (K := K) i).exists_ne_zero)).symm x)) = _
    rw [hsymm]
  rw [e1, orthDerivedCongr_apply]
  rfl

end Formula

section Factor

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {P₁ P₂ : HypPair Q}

theorem exists_factor_of_commute (h₁₂ : P₁.Orth P₂) (H : Subgroup (V ≃ₗ[K] V))
    (hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hE : ∀ u w, eichler Q u w ∈ H)
    {g : V ≃ₗ[K] V} (hgH : g ∈ H)
    (hgc : g * eichler Q P₁.e P₂.e = eichler Q P₁.e P₂.e * g) :
    ∃ m q g'' : V ≃ₗ[K] V, g = m * q * g'' ∧
      m ∈ rootPairSub Q P₁.e P₂.e ⊓ rootLevi Q P₁ P₂ ⊓ H ∧
      q ∈ rootRadical Q P₁ P₂ ⊓ rootPairSub Q P₁.e P₂.e ⊓ H ∧ g'' ∈ H ∧
      g'' P₁.e = P₁.e ∧ g'' P₁.f = P₁.f ∧ g'' P₂.e = P₂.e ∧ g'' P₂.f = P₂.f := by
  have hgO := hHO hgH
  obtain ⟨h1, h2⟩ := apply_e_of_commute h₁₂ hgc
  have hdet := det_eq_one_of_commute h₁₂ hgO hgc
  obtain ⟨m, hm, hm1, hm2⟩ := exists_word h₁₂ (rootPairSub Q P₁.e P₂.e ⊓ rootLevi Q P₁ P₂ ⊓ H)
    (fun t => ⟨⟨rootGroup_le_rootPairSub_left _ _ (eichler_mem_rootGroup (polar_e_smul_f h₁₂ t)),
      eichler_smul_f_mem_rootLevi h₁₂ t⟩, hE _ _⟩)
    (fun t => ⟨⟨rootGroup_le_rootPairSub_right _ _
      (eichler_mem_rootGroup (polar_e_smul_f h₁₂.symm t)), eichler_smul_f_mem_rootLevi' h₁₂ t⟩,
      hE _ _⟩)
    (a := polar Q (g P₂.f) P₂.e) (b := -polar Q (g P₁.f) P₂.e) (c := -polar Q (g P₂.f) P₁.e)
    (d := polar Q (g P₁.f) P₁.e) (by linear_combination hdet)
  have hmO := hHO hm.2
  have hg'1 : (m⁻¹ * g) P₁.e = P₁.e := by
    rw [LinearEquiv.mul_apply, h1]
    apply m.injective
    rw [LinearEquiv.apply_inv_apply', hm1]
    module
  have hg'2 : (m⁻¹ * g) P₂.e = P₂.e := by
    rw [LinearEquiv.mul_apply, h2]
    apply m.injective
    rw [LinearEquiv.apply_inv_apply', hm2]
    module
  have hg'O : m⁻¹ * g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := mul_mem (inv_mem hmO) hgO
  obtain ⟨y₁, y₂, hy11, hy21, hy12, hy22, hf1, hf2⟩ :=
    exists_eichler_mul_apply_f h₁₂ hg'O hg'1 hg'2
  set q := eichler Q P₁.e y₁ * eichler Q P₂.e y₂ with hqdef
  have hq : q ∈ rootRadical Q P₁ P₂ ⊓ rootPairSub Q P₁.e P₂.e ⊓ H :=
    ⟨⟨mul_mem (eichler_mem_rootRadical_left h₁₂ hy11 hy21)
      (eichler_mem_rootRadical_right h₁₂ hy12 hy22),
      mul_mem (rootGroup_le_rootPairSub_left _ _ (eichler_mem_rootGroup hy11))
        (rootGroup_le_rootPairSub_right _ _ (eichler_mem_rootGroup hy22))⟩,
      mul_mem (hE _ _) (hE _ _)⟩
  have hqi : ∀ v, q v = v → q⁻¹ v = v := fun v hv => by
    apply q.injective
    rw [LinearEquiv.apply_inv_apply', hv]
  have hqi' : ∀ v, q⁻¹ (q v) = v := fun v => by
    apply q.injective
    rw [LinearEquiv.apply_inv_apply']
  have hqe1 : q P₁.e = P₁.e := hq.1.1.2.1
  have hqe2 : q P₂.e = P₂.e := hq.1.1.2.2.1
  refine ⟨m, q, q⁻¹ * (m⁻¹ * g), by group, hm, hq,
    mul_mem (inv_mem hq.2) (mul_mem (inv_mem hm.2) hgH), ?_, ?_, ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, hg'1, hqi _ hqe1]
  · rw [LinearEquiv.mul_apply, ← hf1, hqi']
  · rw [LinearEquiv.mul_apply, hg'2, hqi _ hqe2]
  · rw [LinearEquiv.mul_apply, ← hf2, hqi']

theorem rootRadical_le_rootPairSub (h₁₂ : P₁.Orth P₂) :
    rootRadical Q P₁ P₂ ≤ rootPairSub Q P₁.e P₂.e := by
  intro g hg
  have hgR := hg
  obtain ⟨hgO, hg1, hg2, -⟩ := hg
  obtain ⟨y₁, y₂, hy11, hy21, hy12, hy22, hf1, hf2⟩ := exists_eichler_mul_apply_f h₁₂ hgO hg1 hg2
  set q := eichler Q P₁.e y₁ * eichler Q P₂.e y₂ with hqdef
  have hqR : q ∈ rootRadical Q P₁ P₂ := mul_mem (eichler_mem_rootRadical_left h₁₂ hy11 hy21)
    (eichler_mem_rootRadical_right h₁₂ hy12 hy22)
  have hqi : ∀ v, q v = v → q⁻¹ v = v := fun v hv => by
    apply q.injective
    rw [LinearEquiv.apply_inv_apply', hv]
  have hqi' : ∀ v, q⁻¹ (q v) = v := fun v => by
    apply q.injective
    rw [LinearEquiv.apply_inv_apply']
  have hM : q⁻¹ * g ∈ rootLevi Q P₁ P₂ := by
    refine mem_rootLevi_of_fix (mul_mem (inv_mem hqR.1) hgO) ?_ ?_ ?_ ?_
    · rw [LinearEquiv.mul_apply, hg1, hqi _ hqR.2.1]
    · rw [LinearEquiv.mul_apply, ← hf1, hqi']
    · rw [LinearEquiv.mul_apply, hg2, hqi _ hqR.2.2.1]
    · rw [LinearEquiv.mul_apply, ← hf2, hqi']
  have h1 : q⁻¹ * g ∈ rootRadical Q P₁ P₂ ⊓ rootLevi Q P₁ P₂ :=
    Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hqR) hgR, hM⟩
  rw [rootRadical_inf_rootLevi h₁₂, mem_bot] at h1
  have hgq : g = q := by
    rw [← mul_inv_cancel_left q g, h1, mul_one]
  rw [hgq]
  exact mul_mem (rootGroup_le_rootPairSub_left _ _ (eichler_mem_rootGroup hy11))
    (rootGroup_le_rootPairSub_right _ _ (eichler_mem_rootGroup hy22))

end Factor

section Center

theorem center_orthDerived_eq_bot' {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {R : QuadraticForm K V}
    (hR : (polarBilin R).Nondegenerate)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ x ∈ T, R x = 0)
    (hne : ∃ v, R v ≠ 0) : center (orthDerived R) = ⊥ := by
  obtain ⟨-, hc, -⟩ := CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts
    hR hT
  rw [hc, eq_bot_iff]
  intro g hg
  rw [mem_bot]
  obtain ⟨c, hcg⟩ := mem_scalars.mp (mem_subgroupOf.mp hg)
  obtain ⟨v, hv⟩ := hne
  have hgO : (g : V ≃ₗ[K] V) ∈ TauCeti.QuadraticMap.orthogonalGroup R :=
    Subgroup.commutator_le_self _ g.2
  have h1 := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO v
  rw [hcg, QuadraticMap.map_smul, smul_eq_mul] at h1
  have hcc : c * c = 1 := mul_right_cancel₀ hv (by rw [one_mul]; exact h1)
  have hc1 := eq_one_of_mul_self_eq_one hcc
  exact Subtype.ext (LinearEquiv.ext fun u => by rw [hcg, hc1, one_smul]; rfl)

end Center

theorem rootRadicalBar_le_rootPairBar {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
    {P₁ P₂ : HypPair Q} (h₁₂ : P₁.Orth P₂) :
    rootRadicalBar Q P₁ P₂ ≤ rootPairBar Q P₁.e P₂.e :=
  map_mono fun _ hx => mem_subgroupOf.mpr (rootRadical_le_rootPairSub h₁₂ (mem_subgroupOf.mp hx))


section Generic

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {a a' b b' : Fin d}

variable (Q) in
@[expose] noncomputable def stabPairsBar (a a' b b' : Fin d) :
    Subgroup (matrixProjectiveDerived Q) :=
  ((stabSub (K := K) a a' ⊓ stabSub b b').subgroupOf (orthDerived Q)).map (projHom Q)

theorem stabPairsBar_le_rootLeviBar (ha : IsHypCoord Q a a') (hb : IsHypCoord Q b b') :
    stabPairsBar Q a a' b b' ≤ rootLeviBar Q ha.hypPair hb.hypPair := by
  rintro _ ⟨X, hX, rfl⟩
  refine ⟨X, mem_subgroupOf.mpr ?_, rfl⟩
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := mem_subgroupOf.mp hX
  exact mem_rootLevi_of_fix (Subgroup.commutator_le_self _ X.2) h1 h2 h3 h4

theorem rootLeviBar_le_sup_of [Finite K] (ha : IsHypCoord Q a a') (hb : IsHypCoord Q b b')
    (hd : PairDisjoint a a' b b') (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    rootLeviBar Q ha.hypPair hb.hypPair ≤
      rootPairBar Q ha.hypPair.e hb.hypPair.e ⊔ stabPairsBar Q a a' b b' := by
  have h₁₂ := ha.orth hb hd
  have hΩO : orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.commutator_le_self _
  rintro _ ⟨Y, hY, rfl⟩
  have hYM := mem_subgroupOf.mp hY
  obtain ⟨m, q, g'', hYe, hm, hq, hg''H, h1, h2, h3, h4⟩ :=
    exists_factor_of_commute h₁₂ (orthDerived _) hΩO (eichler_mem_orthDerived hQ hT) Y.2
      (mem_centralizer_singleton_iff.mp hYM.1.2)
  have hg''M : g'' ∈ rootLevi _ ha.hypPair hb.hypPair :=
    mem_rootLevi_of_fix (hΩO hg''H) h1 h2 h3 h4
  have hqM : q ∈ rootLevi _ ha.hypPair hb.hypPair := by
    have e : q = m⁻¹ * (Y : (Fin d → K) ≃ₗ[K] (Fin d → K)) * g''⁻¹ := by
      rw [hYe]
      group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hm.1.2) hYM) (inv_mem hg''M)
  have hq1 : q = 1 := by
    have h := Subgroup.mem_inf.mpr ⟨hq.1.1, hqM⟩
    rwa [rootRadical_inf_rootLevi h₁₂, mem_bot] at h
  have hYe' : Y = ⟨m, hm.2⟩ * ⟨g'', hg''H⟩ := by
    apply Subtype.ext
    rw [hYe, hq1, mul_one]
    rfl
  rw [hYe', map_mul]
  exact mul_mem (mem_sup_left ⟨⟨m, hm.2⟩, mem_subgroupOf.mpr hm.1.1, rfl⟩)
    (mem_sup_right ⟨⟨g'', hg''H⟩, mem_subgroupOf.mpr ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩)

theorem centralizer_rootPairElt_eq_sup_of [Finite K] [CharP K 2] (ha : IsHypCoord Q a a')
    (hb : IsHypCoord Q b b') (hd : PairDisjoint a a' b b') (hQ : (polarBilin Q).Nondegenerate)
    {P₃ : HypPair Q} (h₁₃ : ha.hypPair.Orth P₃) (h₂₃ : hb.hypPair.Orth P₃) :
    centralizer {rootPairElt hQ (ha.orth hb hd) h₁₃ h₂₃} =
      rootPairBar Q ha.hypPair.e hb.hypPair.e ⊔ stabPairsBar Q a a' b b' := by
  have h₁₂ := ha.orth hb hd
  have hT := exists_totallySingular_of_hypPairs h₁₂ h₁₃ h₂₃
  have hC := centralizer_rootPairElt hQ h₁₂ h₁₃ h₂₃
  apply le_antisymm
  · rw [hC]
    exact sup_le ((rootRadicalBar_le_rootPairBar h₁₂).trans le_sup_left)
      (rootLeviBar_le_sup_of ha hb hd hQ hT)
  · refine sup_le (rootPairBar_le_centralizer hQ h₁₂ h₁₃ h₂₃) ?_
    rw [hC]
    exact (stabPairsBar_le_rootLeviBar ha hb).trans le_sup_right

theorem commutator_centralizer_rootPairElt_of [Finite K] [CharP K 2] (ha : IsHypCoord Q a a')
    (hb : IsHypCoord Q b b') (hd : PairDisjoint a a' b b') (hQ : (polarBilin Q).Nondegenerate)
    {P₃ : HypPair Q} (h₁₃ : ha.hypPair.Orth P₃) (h₂₃ : hb.hypPair.Orth P₃) {l : K} (hl0 : l ≠ 0)
    (hl1 : l * l ≠ 1)
    (hS : ⁅stabPairsBar Q a a' b b', stabPairsBar Q a a' b b'⁆ = stabPairsBar Q a a' b b') :
    ⁅centralizer {rootPairElt hQ (ha.orth hb hd) h₁₃ h₂₃},
      centralizer {rootPairElt hQ (ha.orth hb hd) h₁₃ h₂₃}⁆ =
      centralizer {rootPairElt hQ (ha.orth hb hd) h₁₃ h₂₃} := by
  have hA := commutator_rootPairBar hQ (ha.orth hb hd) h₁₃ h₂₃ hl0 hl1
  rw [centralizer_rootPairElt_eq_sup_of ha hb hd hQ h₁₃ h₂₃]
  refine le_antisymm (Subgroup.commutator_le_self _) (sup_le ?_ ?_)
  · calc _ = _ := hA.symm
      _ ≤ _ := Subgroup.commutator_mono le_sup_left le_sup_left
  · calc _ = _ := hS.symm
      _ ≤ _ := Subgroup.commutator_mono le_sup_right le_sup_right

end Generic

section StabTwo

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

variable (K) in
@[expose] noncomputable def stabTwo (i j : Fin n) : Subgroup ((Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) :=
  stabSub (plusIndexEquiv n (.inl i)) (plusIndexEquiv n (.inr i)) ⊓
    stabSub (plusIndexEquiv n (.inl j)) (plusIndexEquiv n (.inr j))

variable (K) in
@[expose] noncomputable def stabTwoBar (i j : Fin n) :
    Subgroup (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
  ((stabTwo K i j).subgroupOf (orthDerived _)).map (projHom _)

omit [Finite K] [CharP K 2] in
theorem stabTwoBar_le_pairPerp (i j : Fin n) : stabTwoBar K i j ≤ pairPerp i :=
  map_mono fun _ hx => (mem_subgroupOf.mp hx).1

omit [Finite K] [CharP K 2] in
theorem plusPerpCoord_inl {i j : Fin n} (hn1 : 1 ≤ n) {j' : Fin (n - 1)}
    (hj' : avoid (by omega) i j' = j) :
    plusPerpCoord hn1 i (plusIndexEquiv (n - 1) (.inl j')) = plusIndexEquiv n (.inl j) := by
  simp [plusPerpCoord, hj']

omit [Finite K] [CharP K 2] in
theorem plusPerpCoord_inr {i j : Fin n} (hn1 : 1 ≤ n) {j' : Fin (n - 1)}
    (hj' : avoid (by omega) i j' = j) :
    plusPerpCoord hn1 i (plusIndexEquiv (n - 1) (.inr j')) = plusIndexEquiv n (.inr j) := by
  simp [plusPerpCoord, hj']

theorem pairPerpEquiv_fix_iff (hn : 4 ≤ n) (i : Fin n) (x : pairPerp (K := K) i)
    (G : orthDerived (coordinateQuadPlus n K))
    (hG : (G : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) ∈
      stabSub (plusIndexEquiv n (.inl i)) (plusIndexEquiv n (.inr i)))
    (hxG : (x : matrixProjectiveDerived (coordinateQuadPlus n K)) = projHom _ G)
    (c' : Fin (2 * (n - 1))) :
    ((pairPerpEquiv hn i x : orthDerived (coordinateQuadPlus (n - 1) K)) :
        (Fin (2 * (n - 1)) → K) ≃ₗ[K] (Fin (2 * (n - 1)) → K)) (Pi.single c' 1) =
        Pi.single c' 1 ↔
      (G : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) (Pi.single (plusPerpCoord (by omega) i c') 1)
        = Pi.single (plusPerpCoord (by omega) i c') 1 := by
  have hn1 : 1 ≤ n := by omega
  have hinj := plusPerpCoord_injective hn1 i
  have hext := extend_single (K := K) hinj c'
  have hcomp := single_comp (K := K) hinj c'
  have hi := isHypCoord_coordinateQuadPlus (K := K) i
  have hGO : (G : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) ∈
      TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus n K) :=
    Subgroup.commutator_le_self _ G.2
  have hU : (G : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K))
      (Pi.single (plusPerpCoord hn1 i c') 1) ∈
      perpSub K (plusIndexEquiv n (.inl i)) (plusIndexEquiv n (.inr i)) :=
    hi.apply_mem_perpSub hGO hG (single_mem_perpSub (plusPerpCoord_ne_left hn1 i c')
      (plusPerpCoord_ne_right hn1 i c'))
  constructor
  · intro h
    funext v
    by_cases hva : v = plusIndexEquiv n (.inl i)
    · subst hva
      rw [hU.1, Pi.single_eq_of_ne (plusPerpCoord_ne_left hn1 i c').symm]
    by_cases hvb : v = plusIndexEquiv n (.inr i)
    · subst hvb
      rw [hU.2, Pi.single_eq_of_ne (plusPerpCoord_ne_right hn1 i c').symm]
    obtain ⟨y, rfl⟩ := exists_plusPerpCoord_eq hn1 i hva hvb
    have h1 := congrFun h y
    rw [pairPerpEquiv_apply hn i x G hG hxG, hext] at h1
    rw [h1, ← hcomp]
  · intro h
    funext y
    rw [pairPerpEquiv_apply hn i x G hG hxG, hext, h, ← hcomp]

theorem map_stabTwoBar (hn : 4 ≤ n) {i j : Fin n} {j' : Fin (n - 1)}
    (hj' : avoid (by omega) i j' = j) :
    ((stabTwoBar K i j).subgroupOf (pairPerp i)).map (pairPerpEquiv hn i).toMonoidHom =
      stabDerived (coordinateQuadPlus (n - 1) K) (plusIndexEquiv (n - 1) (.inl j'))
        (plusIndexEquiv (n - 1) (.inr j')) := by
  have hn1 : 1 ≤ n := by omega
  have hlift : ∀ x : pairPerp (K := K) i, ∃ G : orthDerived (coordinateQuadPlus n K),
      (G : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) ∈
        stabSub (plusIndexEquiv n (.inl i)) (plusIndexEquiv n (.inr i)) ∧
      (x : matrixProjectiveDerived (coordinateQuadPlus n K)) = projHom _ G := by
    rintro ⟨_, ⟨G, hG, rfl⟩⟩
    exact ⟨G, mem_subgroupOf.mp hG, rfl⟩
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨G, hG, hxG⟩ := mem_map.mp (mem_subgroupOf.mp hx)
    have hG' := mem_subgroupOf.mp hG
    refine mem_subgroupOf.mpr ⟨?_, ?_⟩
    · refine (pairPerpEquiv_fix_iff hn i x G hG'.1 hxG.symm _).mpr ?_
      rw [plusPerpCoord_inl hn1 hj']
      exact hG'.2.1
    · refine (pairPerpEquiv_fix_iff hn i x G hG'.1 hxG.symm _).mpr ?_
      rw [plusPerpCoord_inr hn1 hj']
      exact hG'.2.2
  · intro hz
    refine ⟨(pairPerpEquiv hn i).symm z, ?_, by simp⟩
    obtain ⟨G, hG, hxG⟩ := hlift ((pairPerpEquiv hn i).symm z)
    have hz' : ((pairPerpEquiv hn i ((pairPerpEquiv hn i).symm z) :
        orthDerived (coordinateQuadPlus (n - 1) K)) :
        (Fin (2 * (n - 1)) → K) ≃ₗ[K] (Fin (2 * (n - 1)) → K)) ∈
        stabSub (plusIndexEquiv (n - 1) (.inl j')) (plusIndexEquiv (n - 1) (.inr j')) := by
      rw [MulEquiv.apply_symm_apply]
      exact mem_subgroupOf.mp hz
    have h1 := (pairPerpEquiv_fix_iff hn i _ G hG hxG _).mp hz'.1
    have h2 := (pairPerpEquiv_fix_iff hn i _ G hG hxG _).mp hz'.2
    rw [plusPerpCoord_inl hn1 hj'] at h1
    rw [plusPerpCoord_inr hn1 hj'] at h2
    refine mem_subgroupOf.mpr ?_
    rw [hxG]
    exact mem_map_of_mem _ (mem_subgroupOf.mpr ⟨hG, h1, h2⟩)

@[expose] noncomputable def stabTwoBarEquiv (hn : 4 ≤ n) {i j : Fin n} {j' : Fin (n - 1)}
    (hj' : avoid (by omega) i j' = j) :
    stabTwoBar K i j ≃* stabDerived (coordinateQuadPlus (n - 1) K)
      (plusIndexEquiv (n - 1) (.inl j')) (plusIndexEquiv (n - 1) (.inr j')) :=
  ((Subgroup.subgroupOfEquivOfLe (stabTwoBar_le_pairPerp i j)).symm.trans
    (((stabTwoBar K i j).subgroupOf (pairPerp i)).equivMapOfInjective
      (pairPerpEquiv (K := K) hn i).toMonoidHom (pairPerpEquiv (K := K) hn i).injective)).trans
    (MulEquiv.subgroupCongr (map_stabTwoBar hn hj'))

theorem isQuasisimple_stabTwoBar (hn : 5 ≤ n) {i j : Fin n} (hij : i ≠ j) :
    CFSG.IsQuasisimple (stabTwoBar K i j) ∧ center (stabTwoBar K i j) = ⊥ := by
  obtain ⟨j', hj'⟩ := exists_avoid_eq (M := n - 1) (by omega : n - 1 + 1 = n) hij.symm
  have hk := isHypCoord_coordinateQuadPlus (K := K) (n := n - 1) j'
  obtain ⟨hR, hT⟩ := regular_plusPerp (K := K) (n := n - 1) (by omega) j'
  set φ := (stabTwoBarEquiv (K := K) (by omega) hj').trans
    (hk.stabDerivedEquiv (regular_coordinateQuadPlus (n - 1) K (by omega)).1 hR hT) with hφ
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv φ.symm
    (CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived hR hT), ?_⟩
  have hne : ∃ v, (coordinateQuadPlus (n - 1) K).comp (perpSub K (plusIndexEquiv (n - 1) (.inl j'))
      (plusIndexEquiv (n - 1) (.inr j'))).subtype v ≠ 0 := by
    obtain ⟨T, hT3, -⟩ := hT
    have : Nontrivial T := Module.nontrivial_of_finrank_eq_succ hT3
    obtain ⟨t, ht⟩ := exists_ne (0 : T)
    have : Nontrivial (perpSub K (plusIndexEquiv (n - 1) (.inl j'))
        (plusIndexEquiv (n - 1) (.inr j'))) :=
      nontrivial_of_ne (t : perpSub K (plusIndexEquiv (n - 1) (.inl j'))
        (plusIndexEquiv (n - 1) (.inr j'))) 0 (fun h => ht (Subtype.ext h))
    exact CFSG.RankThree.OrthogonalInvolutions.exists_map_ne_zero hR
  have hc := center_orthDerived_eq_bot' hR hT hne
  have hmap := CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv φ.symm
  rw [← hmap, hc, Subgroup.map_bot]

end StabTwo

section Perfect

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

variable (K) in
@[expose] noncomputable def plusRootElt (hn : 3 ≤ n) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : matrixProjectiveDerived (coordinateQuadPlus n K) :=
  rootPairElt (regular_coordinateQuadPlus n K hn).1
      ((isHypCoord_coordinateQuadPlus (K := K) i).orth (isHypCoord_coordinateQuadPlus j)
        (pairDisjoint_plus hij))
      ((isHypCoord_coordinateQuadPlus (K := K) i).orth (isHypCoord_coordinateQuadPlus k)
        (pairDisjoint_plus hik))
      ((isHypCoord_coordinateQuadPlus (K := K) j).orth (isHypCoord_coordinateQuadPlus k)
        (pairDisjoint_plus hjk))

omit [Finite K] [CharP K 2] in
theorem stabTwoBar_le_rootLeviBar {i j : Fin n} :
    stabTwoBar K i j ≤ rootLeviBar (coordinateQuadPlus n K)
      (isHypCoord_coordinateQuadPlus (K := K) i).hypPair
      (isHypCoord_coordinateQuadPlus (K := K) j).hypPair :=
  stabPairsBar_le_rootLeviBar _ _

omit [CharP K 2] in
theorem rootLeviBar_le_sup (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j) :
    rootLeviBar (coordinateQuadPlus n K) (isHypCoord_coordinateQuadPlus (K := K) i).hypPair
        (isHypCoord_coordinateQuadPlus (K := K) j).hypPair ≤
      rootPairBar (coordinateQuadPlus n K) (isHypCoord_coordinateQuadPlus (K := K) i).hypPair.e
        (isHypCoord_coordinateQuadPlus (K := K) j).hypPair.e ⊔ stabTwoBar K i j :=
  rootLeviBar_le_sup_of _ _ (pairDisjoint_plus hij) (regular_coordinateQuadPlus n K hn).1
    (regular_coordinateQuadPlus n K hn).2

theorem centralizer_rootPairElt_eq_sup (hn : 3 ≤ n) {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    centralizer {plusRootElt (K := K) hn hij hik hjk} =
      rootPairBar (coordinateQuadPlus n K) (isHypCoord_coordinateQuadPlus (K := K) i).hypPair.e
        (isHypCoord_coordinateQuadPlus (K := K) j).hypPair.e ⊔ stabTwoBar K i j :=
  centralizer_rootPairElt_eq_sup_of _ _ (pairDisjoint_plus hij) _ _ _

theorem commutator_centralizer_rootPairElt (hn : 5 ≤ n) (hq : 4 ≤ Nat.card K) {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅centralizer {plusRootElt (K := K) (by omega) hij hik hjk},
      centralizer {plusRootElt (K := K) (by omega) hij hik hjk}⁆ =
      centralizer {plusRootElt (K := K) (by omega) hij hik hjk} := by
  obtain ⟨l, hl0, hl1⟩ := exists_ne_zero_mul_self_ne_one hq
  exact commutator_centralizer_rootPairElt_of _ _ (pairDisjoint_plus hij) _ _ _ hl0 hl1
    (Subgroup.isPerfect_iff.mp (isQuasisimple_stabTwoBar (K := K) hn hij).1.1)

end Perfect

end CFSG.SeitzReduction.OmegaPilot
