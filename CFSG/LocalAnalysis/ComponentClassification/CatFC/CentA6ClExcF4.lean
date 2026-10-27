module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClExcField
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClExcOrbit
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Transport
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4FrameB4
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4SignOrbit
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4ToralB4
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4ToralC3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ClassicalInvolution.RouteD (hiF4)


theorem f4_toral_C3_hasBigLieSub {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    HasBigLieSub p ↥(toralCentralizer .F4 K (bitsTuple f4BitsC3)) := by
  classical
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  have hadm : StatedLieAdmissible .PSp 3 p f := ⟨hp, hf, by norm_num, by simp⟩
  have : Finite (ModGL .F4 K) := finite_modGL
  obtain ⟨hSX, -, -, -, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction .F4 K hK2 _ (bitsTuple_mem _)
  set H := subsystemGroup .F4 K f4LeviC3 with hH_def
  have hS : rootSpan .F4 K (rootCharKernel (bitsTuple (K := K) f4BitsC3)) =
      H ⊔ (rootSubgroup .F4 K hiF4 ⊔ rootSubgroup .F4 K (-hiF4)) := by
    rw [rootCharKernel_f4BitsC3 hK2, rootSpan_union_pair, ← subsystemGroup_eq_rootSpan]
  have hHX : H ≤ toralCentralizer .F4 K (bitsTuple f4BitsC3) :=
    le_sup_left.trans (hS ▸ hSX)
  obtain ⟨-, -, -, hqH, hlieH⟩ := f4_levi_C3_recognition_frame hp hp2 hK h2
  exact ⟨↥H, inferInstance, Subgroup.inclusion hHX, Subgroup.inclusion_injective hHX, hqH, .PSp,
    3, f, hadm, by decide, hlieH⟩

theorem f4_toral_B4_hasBigLieSub {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    HasBigLieSub p ↥(toralCentralizer .F4 K (bitsTuple f4BitsB4)) := by
  classical
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  have hadm : StatedLieAdmissible .POmegaOdd 4 p f := ⟨hp, hf, by norm_num, hp2⟩
  obtain ⟨hSX, -, -, -, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction .F4 K hK2 _
      (bitsTuple_mem (K := K) f4BitsB4)
  have hker : rootCharKernel (bitsTuple (K := K) f4BitsB4) =
      kernelRoots (maskChar (τ := .F4) f4BitsB4) := by
    rw [rootCharKernel_eq_kernelRoots hK2 (bitsTuple_mem _), signTupleBits_bitsTuple hK2]
  obtain ⟨-, -, -, hqs, hlie⟩ := exists_psi_B4_F4_frame hp hp2 hK h2
  have hSim : (⨆ k, b4Chain K k).map (adjointGroup .F4 K).subtype =
      rootSpan .F4 K (rootCharKernel (bitsTuple (K := K) f4BitsB4)) := by
    rw [map_subtype_iSup_b4Chain, hker]
  let e₁ : ↥(⨆ k, b4Chain K k) ≃* rootSpan .F4 K (rootCharKernel (bitsTuple (K := K) f4BitsB4)) :=
    ((⨆ k, b4Chain K k).equivMapOfInjective _ (adjointGroup .F4 K).subtype_injective).trans
      (MulEquiv.subgroupCongr hSim)
  let e₂ := Subgroup.subgroupOfEquivOfLe hSX
  let e := e₂.trans e₁.symm
  exact HasBigLieSub.of_subgroup _ (LocalCores.isQuasisimple_of_mulEquiv e.symm hqs) hadm
    (by decide) (lieModel_of_mulEquiv
      (QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)) hlie)

theorem f4_toral_hasBigLieSub {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) {b : Fin Tag.F4.rank → Kˣ}
    (hb : ∀ i, b i = 1 ∨ b i = -1) (hb1 : b ≠ 1) : HasBigLieSub p ↥(toralCentralizer .F4 K b) := by
  have hf : 1 ≤ f := (one_le_and_three_le_of_card hp hp2 hK).1
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  refine hasBigLieSub_toralCentralizer_of_orbitCheck hK2 f4SignOrbitB4_check
    (fun ρ hρ hne => ?_) hb hb1
  have hlen : f4SignRepsB4.length = 3 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · exact absurd (by funext i; revert i; decide) hne
  · exact f4_toral_C3_hasBigLieSub hp hp2 hK
  · exact f4_toral_B4_hasBigLieSub hp hp2 hK

theorem a6_F4_inner_false (hO : LieOrderFormulasInput) {K : Type} [Field K] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    {α : MulAut (adjointGroup .F4 K)} {g : adjointGroup .F4 K} {a : Fin Tag.F4.rank → Kˣ}
    (hαg : ∀ h : adjointGroup .F4 K, (α h : ModGL .F4 K) = (g : ModGL .F4 K) *
      rootDiagUnit .F4 a * (h : ModGL .F4 K) * (rootDiagUnit .F4 a)⁻¹ * (g : ModGL .F4 K)⁻¹)
    (hαo : orderOf α = 2) {D : Subgroup ↥(fixedSubgroup α)} (hD : A6Hyp α D) : False := by
  have : Finite (ModGL .F4 K) := finite_modGL
  have hKodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hα : α ^ 2 = 1 := hαo ▸ pow_orderOf_eq_one α
  have hα1 : α ≠ 1 := fun h => by
    rw [h, orderOf_one] at hαo
    exact absurd hαo (by norm_num)
  obtain ⟨b, hb, hb1, ⟨Θ⟩⟩ :=
    exists_toralCentralizer_equiv_of_innerDiag (Or.inr (Or.inl rfl)) hKodd hαg hα
  exact hD.false_of_hasBigLieSub hO hp2 ((f4_toral_hasBigLieSub hp hp2 hK hb (hb1 hα1)).of_mulEquiv
    Θ.symm)

theorem a6_F4_false (hO : LieOrderFormulasInput) {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (σ : MulAut (adjointGroup .F4 K))
    (hσ : orderOf σ = 2) {D : Subgroup ↥(fixedSubgroup σ)} (hD : A6Hyp σ D) : False := by
  have hf : 1 ≤ f := (one_le_and_three_le_of_card hp hp2 hK).1
  have : Finite (ModGL .F4 K) := finite_modGL
  have hKodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hσ2 : σ ^ 2 = 1 := hσ ▸ pow_orderOf_eq_one σ
  rcases odd_F4_E8_G2_involution_inner_or_quadratic (Or.inl rfl) hKodd hσ2 with ⟨g, a, hσg⟩ |
    ⟨q, e, hq, he, hKe, δ, hδ, g, a, hσg⟩
  · exact a6_F4_inner_false hO hp hp2 hK hσg hσ hD
  · have hqp : q = p := by
      have h : q ∣ p ^ f := by
        rw [← hK, hKe]
        exact dvd_pow (dvd_pow_self q (by omega)) two_ne_zero
      exact (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h)
    subst hqp
    exact a6_exc_field_false hO (t := .F4) (Or.inr (Or.inl ⟨rfl, rfl⟩)) hq hp2 he hKe δ hδ hσg
      hσ2 hD

theorem oddA6Shape_F4 (hO : LieOrderFormulasInput) (_hgls : GLS3OddFamilyInput .F4) :
    OddA6Shape .F4 := by
  refine oddA6Shape_of_concrete fun S _ _ n p f hp hp2 hadm hm => ?_
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4
    ((GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2 :
      UntwistedChevalleyModel S .F4 (p ^ f))
  have : Finite ↥(adjointGroup .F4 F) := Finite.of_equiv S e.toEquiv
  exact ⟨↥(adjointGroup .F4 F), inferInstance, inferInstance, e, fun σ D hσ hD =>
    (a6_F4_false hO hp hp2 hF σ hσ hD).elim⟩

end CFSG.ComponentClassification.CatFC
