module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNotLongRootBasic
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLongRoot
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFusionNotTransvection
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointSchreier

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv minusIndexEquiv coordinateQuadPlus coordinateQuadMinus regular_coordinateQuadPlus
    regular_coordinateQuadMinus)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Quasithin (perfectCore le_perfectCore_of_perfect)

section Bar

variable {K : Type*} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem rootPairSub_le_orthDerived [Finite K] (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (u u' : Fin d → K) : rootPairSub Q u u' ≤ orthDerived Q := by
  refine sup_le (fun g hg => ?_) (fun g hg => ?_)
  · obtain ⟨w, -, rfl⟩ := mem_rootGroup.mp hg
    exact eichler_mem_orthDerived hQ hT _ _
  · obtain ⟨w, -, rfl⟩ := mem_rootGroup.mp hg
    exact eichler_mem_orthDerived hQ hT _ _

@[expose] noncomputable def rootPairBar (Q : QuadraticForm K (Fin d → K)) (u u' : Fin d → K) :
    Subgroup (matrixProjectiveDerived Q) :=
  ((rootPairSub Q u u').subgroupOf (orthDerived Q)).map (projHom Q)

theorem commutator_subgroupOf_eq {G : Type*} [Group G] {A B : Subgroup G} (hAB : A ≤ B)
    (hA : ⁅A, A⁆ = A) : ⁅A.subgroupOf B, A.subgroupOf B⁆ = A.subgroupOf B := by
  apply Subgroup.map_injective B.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAB, hA]

theorem commutator_rootPairBar [Finite K] (hQ : (polarBilin Q).Nondegenerate)
    {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃) {l : K}
    (hl0 : l ≠ 0) (hl1 : l * l ≠ 1) :
    ⁅rootPairBar Q P₁.e P₂.e, rootPairBar Q P₁.e P₂.e⁆ = rootPairBar Q P₁.e P₂.e := by
  have hT := exists_totallySingular_of_hypPairs h₁₂ h₁₃ h₂₃
  rw [rootPairBar, ← Subgroup.map_commutator, commutator_subgroupOf_eq
    (rootPairSub_le_orthDerived hQ hT _ _) (commutator_rootPairSub h₁₂ h₁₃ h₂₃ hl0 hl1)]

@[expose] noncomputable def rootPairElt [Finite K] (hQ : (polarBilin Q).Nondegenerate)
    {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃) :
    matrixProjectiveDerived Q :=
  projHom Q ⟨eichler Q P₁.e P₂.e,
    eichler_mem_orthDerived hQ (exists_totallySingular_of_hypPairs h₁₂ h₁₃ h₂₃) _ _⟩

theorem linearIndependent_pair_e {P₁ P₂ : HypPair Q} (h₁₂ : P₁.Orth P₂) :
    LinearIndependent K ![P₁.e, P₂.e] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 := congrArg (fun v => polar Q v P₁.f) hst
  have h2 := congrArg (fun v => polar Q v P₂.f) hst
  have he₂f₁ : polar Q P₂.e P₁.f = 0 := by rw [polar_comm]; exact h₁₂.fe
  simp only [polar_add_left, polar_smul_left_eq, P₁.polar_ef, he₂f₁, h₁₂.ef, P₂.polar_ef,
    polar_zero_left] at h1 h2
  exact ⟨by linear_combination h1, by linear_combination h2⟩

theorem isLongRoot_rootPairElt [Finite K] (hQ : (polarBilin Q).Nondegenerate)
    {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃) :
    IsLongRoot Q (rootPairElt hQ h₁₂ h₁₃ h₂₃) :=
  ⟨P₁.e, P₂.e, P₁.Q_e, P₂.Q_e, h₁₂.ee, linearIndependent_pair_e h₁₂, _, rfl, rfl⟩

theorem rootPairElt_mem_rootPairBar [Finite K] (hQ : (polarBilin Q).Nondegenerate)
    {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃) :
    rootPairElt hQ h₁₂ h₁₃ h₂₃ ∈ rootPairBar Q P₁.e P₂.e :=
  ⟨_, eichler_mem_rootPairSub h₁₂.ee, rfl⟩

theorem rootPairBar_le_centralizer [Finite K] (hQ : (polarBilin Q).Nondegenerate)
    {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃) :
    rootPairBar Q P₁.e P₂.e ≤ centralizer {rootPairElt hQ h₁₂ h₁₃ h₂₃} := by
  rintro _ ⟨g, hg, rfl⟩
  rw [mem_centralizer_singleton_iff, rootPairElt, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact mem_centralizer_singleton_iff.mp
    (rootPairSub_le_centralizer P₁.Q_e P₂.Q_e h₁₂.ee (Subgroup.mem_subgroupOf.mp hg))

end Bar

section Conj

variable {K : Type*} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem exists_ne_zero_mul_self_ne_one (hq : 4 ≤ Nat.card K) : ∃ l : K, l ≠ 0 ∧ l * l ≠ 1 := by
  obtain ⟨c₀, hc₀⟩ := exists_units_ne_one (K := K) (by omega)
  exact ⟨c₀, c₀.ne_zero, fun h => units_val_ne_one hc₀ (eq_one_of_mul_self_eq_one h)⟩

theorem exists_perfect_le_centralizer_of_isLongRoot (hQ : (polarBilin Q).Nondegenerate)
    {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃)
    (hq : 4 ≤ Nat.card K) {z : matrixProjectiveDerived Q} (hz : IsLongRoot Q z) :
    ∃ H : Subgroup (matrixProjectiveDerived Q), ⁅H, H⁆ = H ∧ z ∈ H ∧ H ≤ centralizer {z} := by
  obtain ⟨l, hl0, hl1⟩ := exists_ne_zero_mul_self_ne_one hq
  obtain ⟨c, hc⟩ := isConj_iff.mp
    (isConj_of_isLongRoot hQ h₁₂ h₁₃ h₂₃ (isLongRoot_rootPairElt hQ h₁₂ h₁₃ h₂₃) hz)
  refine ⟨(rootPairBar Q P₁.e P₂.e).map (MulAut.conj c).toMonoidHom, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_commutator, commutator_rootPairBar hQ h₁₂ h₁₃ h₂₃ hl0 hl1]
  · rw [← hc]
    exact ⟨_, rootPairElt_mem_rootPairBar hQ h₁₂ h₁₃ h₂₃, rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    have h := mem_centralizer_singleton_iff.mp (rootPairBar_le_centralizer hQ h₁₂ h₁₃ h₂₃ hy)
    rw [mem_centralizer_singleton_iff, ← hc]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc c * y * c⁻¹ * (c * rootPairElt hQ h₁₂ h₁₃ h₂₃ * c⁻¹) =
        c * (y * rootPairElt hQ h₁₂ h₁₃ h₂₃) * c⁻¹ := by group
      _ = c * (rootPairElt hQ h₁₂ h₁₃ h₂₃ * y) * c⁻¹ := by rw [h]
      _ = c * rootPairElt hQ h₁₂ h₁₃ h₂₃ * c⁻¹ * (c * y * c⁻¹) := by group

theorem mem_perfectCore_centralizer_of_isLongRoot (hQ : (polarBilin Q).Nondegenerate)
    {P₁ P₂ P₃ : HypPair Q} (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃)
    (hq : 4 ≤ Nat.card K) {z : matrixProjectiveDerived Q} (hz : IsLongRoot Q z) :
    z ∈ perfectCore (centralizer {z}) := by
  obtain ⟨H, hH, hzH, hHC⟩ := exists_perfect_le_centralizer_of_isLongRoot hQ h₁₂ h₁₃ h₂₃ hq hz
  exact le_perfectCore_of_perfect hHC hH hzH

end Conj

section Setting

open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
  (statedProjectiveReindexEquiv)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointSchreier
  (orthogonal_geometry_classical_model_Schreier)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem isSolvable_outer_of_mulEquiv_plus {X : Type} [Group X] {n f : ℕ} (hn : 4 ≤ n)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f)
    (e : X ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) : Group.IsSolvable (Outer X) :=
  (orthogonal_geometry_classical_model_Schreier .POmegaPlus (Or.inr (Or.inl rfl))
    (n := n) (p := 2) (f := f)
    ⟨⟨Nat.prime_two, hf, hn⟩, K, inferInstance, inferInstance, hK,
      ⟨e.trans (statedProjectiveReindexEquiv (plusIndexEquiv n)
        (CFSG.LieType.Universal.Spin.quadPlus n K)
        (CFSG.LieType.Universal.Spin.coe_quadPlus n K)).symm⟩⟩).2.2

theorem isSolvable_outer_of_mulEquiv_minus {X : Type} [Group X] {n f : ℕ} (hn : 4 ≤ n)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : X ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) :
    Group.IsSolvable (Outer X) :=
  (orthogonal_geometry_classical_model_Schreier .POmegaMinus (Or.inr (Or.inr rfl))
    (n := n) (p := 2) (f := f)
    ⟨⟨Nat.prime_two, hf, hn⟩, K, inferInstance, inferInstance, hK, b, c, hirr,
      ⟨e.trans (statedProjectiveReindexEquiv (minusIndexEquiv n (by omega))
        (CFSG.LieType.Universal.Spin.quadMinus n K b c)
        (CFSG.LieType.Universal.Spin.coe_quadMinus n K b c)).symm⟩⟩).2.2

theorem not_isLongRoot_conj_of_perfect (hset : SeitzSetting G L) {K : Type*} [Field K] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} (e : L ≃* matrixProjectiveDerived Q)
    (hOut : Group.IsSolvable (Outer L))
    (hC0 : ∀ z : matrixProjectiveDerived Q, IsLongRoot Q z →
      ∃ H : Subgroup (matrixProjectiveDerived Q), ⁅H, H⁆ = H ∧ z ∈ H ∧ H ≤ centralizer {z})
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (g : G)
    (hgL : g⁻¹ * t * g ∈ L) : ¬ IsLongRoot Q (e ⟨g⁻¹ * t * g, hgL⟩) := by
  intro hz
  obtain ⟨H, hHp, hzH, hHC⟩ := hC0 _ hz
  set φ : matrixProjectiveDerived Q →* G := L.subtype.comp e.symm.toMonoidHom with hφ
  have hφw : φ (e ⟨g⁻¹ * t * g, hgL⟩) = g⁻¹ * t * g := by simp [hφ]
  refine LinearPilot.conj_not_mem_perfect hset.standardSetting hOut hset.center_eq_bot htC ht g
    (P := H.map φ) ?_ ?_ ?_ ⟨_, hzH, hφw⟩
  · rw [← Subgroup.map_commutator, hHp]
  · rintro _ ⟨x, -, rfl⟩
    exact (e.symm x).2
  · rintro _ ⟨x, hx, rfl⟩
    have h1 := mem_centralizer_singleton_iff.1 (hHC hx)
    rw [mem_centralizer_singleton_iff, ← hφw, ← map_mul, ← map_mul, h1]

theorem one_le_of_card_eq_two_pow {K : Type*} [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) : 1 ≤ f := by
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · rw [hK, pow_zero] at hq
    omega
  · exact hf

theorem not_isLongRoot_conj_plus (hset : SeitzSetting G L) {n f : ℕ} (hn : 4 ≤ n) {K : Type}
    [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (g : G) (hgL : g⁻¹ * t * g ∈ L) :
    ¬ IsLongRoot _ (e ⟨g⁻¹ * t * g, hgL⟩) := by
  obtain ⟨P₁, P₂, P₃, h₁₂, h₁₃, h₂₃⟩ := exists_three_pairs_plus (K := K) (by omega : 3 ≤ n)
  refine not_isLongRoot_conj_of_perfect hset e
    (isSolvable_outer_of_mulEquiv_plus hn (one_le_of_card_eq_two_pow hK hq) hK e)
    (fun z hz => exists_perfect_le_centralizer_of_isLongRoot
      (regular_coordinateQuadPlus n K (by omega)).1 h₁₂ h₁₃ h₂₃ hq hz) htC ht g hgL

theorem not_isLongRoot_conj_minus (hset : SeitzSetting G L) {n f : ℕ} (hn : 4 ≤ n) {K : Type}
    [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (g : G) (hgL : g⁻¹ * t * g ∈ L) :
    ¬ IsLongRoot _ (e ⟨g⁻¹ * t * g, hgL⟩) := by
  obtain ⟨P₁, P₂, P₃, h₁₂, h₁₃, h₂₃⟩ := exists_three_pairs_minus (K := K) hn b c
  refine not_isLongRoot_conj_of_perfect hset e
    (isSolvable_outer_of_mulEquiv_minus hn (one_le_of_card_eq_two_pow hK hq) hK hirr e)
    (fun z hz => exists_perfect_le_centralizer_of_isLongRoot
      (regular_coordinateQuadMinus n K b c hn hirr).1 h₁₂ h₁₃ h₂₃ hq hz) htC ht g hgL

omit [Finite G] in
theorem conj_ne_one_of_orderOf {t : G} (ht : orderOf t = 2) (g : G) (hgL : g⁻¹ * t * g ∈ L) :
    (⟨g⁻¹ * t * g, hgL⟩ : L) ≠ 1 := by
  intro h1
  have h2 : g⁻¹ * t * g = 1 := congrArg Subtype.val h1
  have ht1 : t = 1 := by
    calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
      _ = 1 := by rw [h2]; group
  rw [ht1, orderOf_one] at ht
  exact absurd ht (by decide)

theorem not_forall_commute_sylow_conj_plus (hset : SeitzSetting G L) {n f : ℕ} (hn : 4 ≤ n)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ L →
      ¬ ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u := by
  intro U g hgL hcomm
  exact not_isLongRoot_conj_plus hset hn hK hq e htC ht g hgL
    (isLongRoot_of_commute_sylow_plus_of_mulEquiv e (by omega) U
      (conj_ne_one_of_orderOf ht g hgL) fun u hu => Subtype.ext (hcomm u hu))

theorem not_forall_commute_sylow_conj_minus (hset : SeitzSetting G L) {n f : ℕ} (hn : 4 ≤ n)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    ∀ (U : Sylow 2 L) (g : G), g⁻¹ * t * g ∈ L →
      ¬ ∀ u ∈ (U : Subgroup L), (u : G) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * u := by
  intro U g hgL hcomm
  exact not_isLongRoot_conj_minus hset hn hK hq hirr e htC ht g hgL
    (isLongRoot_of_commute_sylow_minus_of_mulEquiv hn hirr e U
      (conj_ne_one_of_orderOf ht g hgL) fun u hu => Subtype.ext (hcomm u hu))

end Setting

end CFSG.SeitzReduction.OmegaPilot
