module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockOrthB
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockLinC
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.Layer
import CFSG.RankThree.PartOne.KC.OrthogonalRegularQuasisimple
import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaRegular
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticNormalForms

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T123CB

open Polynomial Module Matrix CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCLinPlane CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.Classical2
open CFSG.RankThree.PartOne.KCOrthogonal (OddOrderIsometry isometryCentralizer supportedBlock
  specialBlock supportedFixedDerived)

section Generic

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

private theorem not_smallFixedException_of_six_le
    (h6 : 6 ≤ finrank K (KCOrthogonal.fixedSpace x)) :
    ¬ KCOrthogonal.SmallFixedException (Q.comp (KCOrthogonal.fixedSpace x).subtype) := by
  rintro (⟨h3, -⟩ | ⟨⟨h4, -⟩, -⟩) <;> omega

private theorem isQuasisimple_supportedFixedDerived_of_six_le (hx : OddOrderIsometry Q p x)
    (h6 : 6 ≤ finrank K (KCOrthogonal.fixedSpace x)) :
    CFSG.IsQuasisimple ↥(supportedFixedDerived Q x) := by
  have hq := KCOrthogonal.orthogonal_regular_space_derived_quasisimple
    (Q.comp (KCOrthogonal.fixedSpace x).subtype) hx.polarBilin_fixed_nondegenerate (by omega)
    (not_smallFixedException_of_six_le h6) fun ⟨h4, _⟩ => by omega
  set O := TauCeti.QuadraticMap.orthogonalGroup (Q.comp (KCOrthogonal.fixedSpace x).subtype)
  let e : ↥(commutator ↥O) ≃* ↥(orthDerived (Q.comp (KCOrthogonal.fixedSpace x).subtype)) :=
    (Subgroup.equivMapOfInjective _ O.subtype O.subtype_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator O))
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (KCOrthogonal.supportedFixedDerivedEquiv hx).symm
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq)

private theorem apply_eq_of_commute_supportedFixedDerived (hx : OddOrderIsometry Q p x)
    (h6 : 6 ≤ finrank K (KCOrthogonal.fixedSpace x)) {g : V ≃ₗ[K] V}
    (hg : g ∈ isometryCentralizer Q x) (hgc : ∀ f ∈ supportedFixedDerived Q x, g * f = f * g)
    {w : V} (hw : w ∈ KCOrthogonal.fixedSpace x) : g w = w := by
  have hzc : ∀ y ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (KCOrthogonal.fixedSpace x).subtype), TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (KCOrthogonal.fixedSpace x).subtype)⁆,
      KCOrthogonal.isometryRestrictFixed Q x ⟨g, hg⟩ * y =
        y * KCOrthogonal.isometryRestrictFixed Q x ⟨g, hg⟩ := by
    intro y hy
    obtain ⟨f, hf⟩ := KCOrthogonal.restrictFixed_surjective hx y
      (Subgroup.commutator_le_self _ hy)
    have hfS : f.1 ∈ supportedFixedDerived Q x := KCOrthogonal.mem_supportedFixedDerived.mpr
      ⟨f.2, by
        have : KCOrthogonal.restrictFixed Q x ⟨f.1, f.2⟩ = y := hf
        rw [this]
        exact hy⟩
    rw [← hf, ← KCOrthogonal.isometryRestrictFixed_restrictFixed f, ← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (hgc f.1 hfS))
  have h1 := CFSG.StandardType.LayerCores.OrthRegular.eq_one_of_commute_orthDerived
    hx.polarBilin_fixed_nondegenerate (by omega) (not_smallFixedException_of_six_le h6)
    (KCOrthogonal.isometryRestrictFixed_mem_orthogonalGroup ⟨g, hg⟩) hzc
  have := congrArg (fun z : KCOrthogonal.fixedSpace x ≃ₗ[K] KCOrthogonal.fixedSpace x =>
    (z ⟨w, hw⟩ : V)) h1
  simpa [KCOrthogonal.coe_isometryRestrictFixed] using this

end Generic

section Plane

open scoped _root_.Classical

variable {n p : ℕ} {K : Type} [Field K] {Q : QuadraticForm K (Fin n → K)}
  {E0 : Subgroup (SpecialLinearGroup (Fin n) K)} [Fintype E0] [IsMulCommutative E0]

local notation "ρ₀" => planeRep E0

variable (hP : IsPlane p E0) (hpK : (p : K) ≠ 0)
include hP hpK

private theorem auxEquiv_eq_mul {M₁ : Subgroup ↥E0} (hM₁ : M₁ ∈ lines p E0) (â c₁ : ↥E0) :
    auxEquiv hP hpK hM₁ â c₁ = actEquiv c₁ * auxEquiv hP hpK hM₁ (â * c₁⁻¹) 1 := by
  refine LinearEquiv.ext fun v => ?_
  have hcomm : ∀ a b : ↥E0, a * b = b * a := fun a b =>
    (IsMulCommutative.is_comm (M := ↥E0)).comm a b
  have h1 : ∀ w, act ρ₀ c₁ (act ρ₀ (â * c₁⁻¹) w) = act ρ₀ â w := fun w => by
    rw [← Module.End.mul_apply, ← act_mul, hcomm â c₁⁻¹, mul_inv_cancel_left]
  have h2 : ∀ w, act ρ₀ c₁ (act ρ₀ 1 w) = act ρ₀ c₁ w := fun w => by
    rw [act_one, Module.End.one_apply]
  rw [LinearEquiv.mul_apply]
  show auxEnd E0 â c₁ M₁ v = act ρ₀ c₁ (auxEnd E0 (â * c₁⁻¹) 1 M₁ v)
  rw [auxEnd_apply, auxEnd_apply, map_add, h1, h2]

private theorem actEquiv_mul_auxEquiv_comm {M₁ : Subgroup ↥E0} (hM₁ : M₁ ∈ lines p E0)
    (c d c' : ↥E0) :
    actEquiv c' * auxEquiv hP hpK hM₁ c d = auxEquiv hP hpK hM₁ c d * actEquiv c' := by
  refine LinearEquiv.ext fun v => ?_
  show act ρ₀ c' (auxEnd E0 c d M₁ v) = auxEnd E0 c d M₁ (act ρ₀ c' v)
  exact congrArg (fun f : Module.End K (Fin n → K) => f v) (commute_act_auxEnd E0 c' c d M₁).eq

private theorem auxEquiv_apply_sub {M₁ : Subgroup ↥E0} (hM₁ : M₁ ∈ lines p E0) {c₁ : ↥E0}
    (hc₁M₁ : c₁ ∈ M₁) (d : ↥E0) (v : Fin n → K) :
    auxEquiv hP hpK hM₁ d 1 (actEquiv c₁ v - v) = actEquiv c₁ v - v := by
  have h0 : projLine ρ₀ M₁ (act ρ₀ c₁ v - v) = 0 := by
    rw [map_sub, projLine_act_apply, fix_range_projLine E0 hc₁M₁ _ (LinearMap.mem_range_self _ v),
      sub_self]
  show auxEnd E0 d 1 M₁ (act ρ₀ c₁ v - v) = act ρ₀ c₁ v - v
  rw [auxEnd_apply, h0, map_zero, zero_add, sub_zero, act_one, Module.End.one_apply]

private theorem fixedSpace_auxEquiv_le (hEQ : ∀ e : ↥E0, ∀ v, Q (act ρ₀ e v) = Q v)
    (hreg : ∀ v, (∀ w, QuadraticMap.polar Q v w = 0) → v = 0) {M₁ : Subgroup ↥E0}
    (hM₁ : M₁ ∈ lines p E0) (â : ↥E0) {c₁ : ↥E0} (hc₁M₁ : c₁ ∈ M₁) :
    KCOrthogonal.fixedSpace (auxEquiv hP hpK hM₁ â c₁) ≤
      KCOrthogonal.fixedSpace (actEquiv c₁) := by
  rw [auxEquiv_eq_mul hP hpK hM₁ â c₁]
  exact H81Orth.fixedSpace_mul_le (oddOrderIsometry_actEquiv hP hpK hEQ hreg c₁)
    (oddOrderIsometry_auxEquiv hP hpK hEQ hreg hM₁ (â * c₁⁻¹) 1)
    (actEquiv_mul_auxEquiv_comm hP hpK hM₁ _ _ _) (auxEquiv_apply_sub hP hpK hM₁ hc₁M₁ _)

private theorem supportedFixedDerived_auxEquiv_le (hEQ : ∀ e : ↥E0, ∀ v, Q (act ρ₀ e v) = Q v)
    (hreg : ∀ v, (∀ w, QuadraticMap.polar Q v w = 0) → v = 0) {M₁ : Subgroup ↥E0}
    (hM₁ : M₁ ∈ lines p E0) (â : ↥E0) {c₁ : ↥E0} (hc₁M₁ : c₁ ∈ M₁) :
    supportedFixedDerived Q (auxEquiv hP hpK hM₁ â c₁) ≤ supportedFixedDerived Q (actEquiv c₁) := by
  rw [auxEquiv_eq_mul hP hpK hM₁ â c₁]
  exact H81Orth.supportedFixedDerived_mul_le (oddOrderIsometry_actEquiv hP hpK hEQ hreg c₁)
    (oddOrderIsometry_auxEquiv hP hpK hEQ hreg hM₁ (â * c₁⁻¹) 1)
    (actEquiv_mul_auxEquiv_comm hP hpK hM₁ _ _ _) (auxEquiv_apply_sub hP hpK hM₁ hc₁M₁ _)

private theorem six_le_finrank_actEquiv [Finite K] [CharP K 2]
    (hEQ : ∀ e : ↥E0, ∀ v, Q (act ρ₀ e v) = Q v)
    (hreg : ∀ v, (∀ w, QuadraticMap.polar Q v w = 0) → v = 0) {M₁ : Subgroup ↥E0}
    (hM₁ : M₁ ∈ lines p E0) {â c₁ : ↥E0} (hâM₁ : â ∉ M₁) (hc₁M₁ : c₁ ∈ M₁)
    {y₁ : Fin n → K} (hy₁ : y₁ ∈ LinearMap.range (projLine ρ₀ M₁)) (hy₁0 : y₁ ≠ 0)
    (hns : ¬ Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (KCOrthogonal.fixedSpace (auxEquiv hP hpK hM₁ â c₁)).subtype))) :
    6 ≤ finrank K ↥(KCOrthogonal.fixedSpace (actEquiv c₁)) := by
  have hx₀ := oddOrderIsometry_auxEquiv hP hpK hEQ hreg hM₁ â c₁
  have hx := oddOrderIsometry_actEquiv hP hpK hEQ hreg c₁
  have h4 := four_le_finrank_of_not_isSolvable _ hx₀.polarBilin_fixed_nondegenerate hns
  obtain ⟨k, hk⟩ := CFSG.ComponentClassification.UnbalancedCatalog.even_finrank_of_charTwo _
    hx.polarBilin_fixed_nondegenerate
  have hle := fixedSpace_auxEquiv_le hP hpK hEQ hreg hM₁ â hc₁M₁
  have hy₁W : y₁ ∈ KCOrthogonal.fixedSpace (actEquiv c₁) := by
    rw [KCOrthogonal.mem_fixedSpace]
    exact fix_range_projLine E0 hc₁M₁ y₁ hy₁
  have hy₁V : y₁ ∉ KCOrthogonal.fixedSpace (auxEquiv hP hpK hM₁ â c₁) := by
    intro h
    rw [KCOrthogonal.mem_fixedSpace] at h
    have h' : act ρ₀ â y₁ = y₁ := (auxEnd_apply_of_mem_range hP hpK hM₁ â c₁ hy₁).symm.trans h
    exact hy₁0 (eq_zero_of_mem_range_projLine hP hpK hM₁ hâM₁ hy₁ h')
  have hlt := Submodule.finrank_lt_finrank_of_lt
    (lt_of_le_of_ne hle fun h => hy₁V (h ▸ hy₁W))
  omega

end Plane

section Fixed

open scoped _root_.Classical

variable {n p : ℕ} {K : Type} [Field K] {Q : QuadraticForm K (Fin n → K)}
  {E0 : Subgroup (SpecialLinearGroup (Fin n) K)} [Fintype E0] [IsMulCommutative E0]

local notation "ρ₀" => planeRep E0

theorem orthBlockConcl_of_fixed [Finite K] [CharP K 2] (hP : IsPlane p E0) (hpK : (p : K) ≠ 0)
    (hEQ : ∀ e : ↥E0, ∀ v, Q (act ρ₀ e v) = Q v)
    (hreg : ∀ v, (∀ w, QuadraticMap.polar Q v w = 0) → v = 0) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) {M₁ : Subgroup ↥E0} (hM₁ : M₁ ∈ lines p E0)
    (hM₁0 : projLine ρ₀ M₁ ≠ 0) {â c₁ : ↥E0} (hâM₁ : â ∉ M₁) (hc₁M₁ : c₁ ∈ M₁) (hc₁1 : c₁ ≠ 1)
    (hns : ¬ Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (KCOrthogonal.fixedSpace (auxEquiv hP hpK hM₁ â c₁)).subtype))) :
    OrthBlockConcl Q E0 p â := by
  have hp : p.Prime := hP.prime
  have hx₀ := oddOrderIsometry_auxEquiv hP hpK hEQ hreg hM₁ â c₁
  have hx := oddOrderIsometry_actEquiv hP hpK hEQ hreg c₁
  obtain ⟨y₁, hy₁, hy₁0⟩ : ∃ y ∈ LinearMap.range (projLine ρ₀ M₁), y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hM₁0 (LinearMap.ext fun v => hcon _ (LinearMap.mem_range_self _ v))
  have h6 := six_le_finrank_actEquiv hP hpK hEQ hreg hM₁ hâM₁ hc₁M₁ hy₁ hy₁0 hns
  have : Finite ((Fin n → K) ≃ₗ[K] (Fin n → K)) :=
    Finite.of_injective (fun g : (Fin n → K) ≃ₗ[K] (Fin n → K) => (g : (Fin n → K) → (Fin n → K)))
      DFunLike.coe_injective
  obtain ⟨F, hFq, hFS, hFn, hFp⟩ := exists_fixed_factor_dvd_card hx₀ hp hp2 hpq hns
  have hPM : F ≤ supportedFixedDerived Q (actEquiv c₁) :=
    hFS.trans (supportedFixedDerived_auxEquiv_le hP hpK hEQ hreg hM₁ â hc₁M₁)
  have hPd : p ∣ Nat.card (↥F ⧸ Subgroup.center ↥F) :=
    CFSG.dvd_card_quotient_center_of_quasisimple hFq hp hFp
  refine ⟨c₁, not_mem_zpowers_of_mem hP hM₁ hc₁M₁ hc₁1 hâM₁, F,
    supportedFixedDerived Q (auxEquiv hP hpK hM₁ â c₁), supportedFixedDerived Q (actEquiv c₁),
    hFS, fun g hg y hy => (Subgroup.normal_subgroupOf_iff hFS).mp hFn y g hy hg,
    hx₀.supportedFixedDerived_le_orthDerived,
    fun g hg e => commute_act_of_mem_supportedBlock_fixed hP hpK hM₁ hâM₁ hc₁M₁ hc₁1
      (KCOrthogonal.supportedFixedDerived_le_supportedBlock hg) e,
    fun g hgO hgc y hy => hx₀.conj_mem_supportedFixedDerived
      (mem_isometryCentralizer_auxEquiv hP hpK hgO hgc hM₁ â c₁) hy,
    hFq, hPd, hx.supportedFixedDerived_le_orthDerived,
    KCOrthogonal.supportedFixedDerived_le_isometryCentralizer,
    fun g hg y hy => hx.conj_mem_supportedFixedDerived hg hy,
    isQuasisimple_supportedFixedDerived_of_six_le hx h6, hPM, dvd_card_quot_center_of_le hPM hPd,
    fun hcen => ?_⟩
  have hâc : actEquiv â ∈ isometryCentralizer Q (actEquiv c₁) :=
    mem_isometryCentralizer_actEquiv (oddOrderIsometry_actEquiv hP hpK hEQ hreg â).mem
      (fun e => commute_act E0 â e) c₁
  have hy₁W : y₁ ∈ KCOrthogonal.fixedSpace (actEquiv c₁) := by
    rw [KCOrthogonal.mem_fixedSpace]
    exact fix_range_projLine E0 hc₁M₁ y₁ hy₁
  have h1 := apply_eq_of_commute_supportedFixedDerived hx h6 hâc
    (fun f hf => (Subgroup.mem_centralizer_iff.mp hcen f hf).symm) hy₁W
  exact hy₁0 (eq_zero_of_mem_range_projLine hP hpK hM₁ hâM₁ hy₁ h1)

end Fixed

end CFSG.LocalAnalysis.GLTheoremA.T123CB

end
