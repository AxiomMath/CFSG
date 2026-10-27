module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClExcField
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClExcOrbit
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Transport
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE8Inner

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)


theorem e8_toral_D8_hasBigLieSub {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    HasBigLieSub p ↥(toralCentralizer .E8 K (bitsTuple e8BitsD8)) := by
  classical
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hadm : StatedLieAdmissible .POmegaPlus 8 p f := ⟨hp, hf, by norm_num⟩
  obtain ⟨hSX, -, -, -, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction .E8 K hK2 _
      (bitsTuple_mem (K := K) e8BitsD8)
  obtain ⟨-, -, -, hqs, hlie⟩ := exists_psi_D8_E8 hp hp2 hK
  let e₁ : ↥(⨆ k, e8D8Chain K k) ≃*
      rootSpan .E8 K (rootCharKernel (bitsTuple (K := K) e8BitsD8)) :=
    ((⨆ k, e8D8Chain K k).equivMapOfInjective _ (adjointGroup .E8 K).subtype_injective).trans
      (MulEquiv.subgroupCongr (map_subtype_iSup_e8D8Chain hK2))
  let e₂ := Subgroup.subgroupOfEquivOfLe hSX
  let e := e₂.trans e₁.symm
  exact HasBigLieSub.of_subgroup _ (LocalCores.isQuasisimple_of_mulEquiv e.symm hqs) hadm
    (by decide) (lieModel_of_mulEquiv
      (QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)) hlie)

theorem e8_toral_E7_hasBigLieSub {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    HasBigLieSub p ↥(toralCentralizer .E8 K (bitsTuple e8BitsE7)) := by
  classical
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hadm : StatedLieAdmissible .E7 0 p f := ⟨hp, hf, rfl⟩
  have : Finite (ModGL .E8 K) := finite_modGL
  obtain ⟨hSX, -, -, -, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction .E8 K hK2 _ (bitsTuple_mem _)
  set H := subsystemGroup .E8 K e8LeviE7 with hH_def
  have hS : rootSpan .E8 K (rootCharKernel (bitsTuple (K := K) e8BitsE7)) =
      H ⊔ (rootSubgroup .E8 K hiE8 ⊔ rootSubgroup .E8 K (-hiE8)) := by
    rw [rootCharKernel_e8BitsE7 hK2, rootSpan_union_pair, ← subsystemGroup_eq_rootSpan]
  have hHX : H ≤ toralCentralizer .E8 K (bitsTuple e8BitsE7) :=
    le_sup_left.trans (hS ▸ hSX)
  obtain ⟨hqH, hlieH⟩ := e8_levi_E7_recognition hp hp2 hK
  exact ⟨↥H, inferInstance, Subgroup.inclusion hHX, Subgroup.inclusion_injective hHX, hqH, .E7,
    0, f, hadm, by decide, hlieH⟩

theorem e8_toral_hasBigLieSub {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) {b : Fin Tag.E8.rank → Kˣ}
    (hb : ∀ i, b i = 1 ∨ b i = -1) (hb1 : b ≠ 1) : HasBigLieSub p ↥(toralCentralizer .E8 K b) := by
  have hf : 1 ≤ f := (one_le_and_three_le_of_card hp hp2 hK).1
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  refine hasBigLieSub_toralCentralizer_of_orbitCheck hK2 e8SignOrbit_check
    (fun ρ hρ hne => ?_) hb hb1
  have hlen : e8SignReps.length = 3 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · exact absurd (by funext i; revert i; decide) hne
  · exact e8_toral_D8_hasBigLieSub hp hp2 hK
  ·
    have hmap := map_conj_toralCentralizer_of_maskAct (K := K) hK2 e8MaskWord e8BitsE7
    rw [maskAct_e8MaskWord] at hmap
    let e : toralCentralizer .E8 K (bitsTuple e8BitsE7) ≃*
        toralCentralizer .E8 K (bitsTuple (listMask (e8SignReps.getD 2 []))) :=
      ((toralCentralizer .E8 K _).equivMapOfInjective _ (MulAut.conj _).injective).trans
        (MulEquiv.subgroupCongr hmap)
    exact (e8_toral_E7_hasBigLieSub hp hp2 hK).of_mulEquiv e

theorem a6_E8_inner_false (hO : LieOrderFormulasInput) {K : Type} [Field K] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    {α : MulAut (adjointGroup .E8 K)} {g : adjointGroup .E8 K} {a : Fin Tag.E8.rank → Kˣ}
    (hαg : ∀ h : adjointGroup .E8 K, (α h : ModGL .E8 K) = (g : ModGL .E8 K) *
      rootDiagUnit .E8 a * (h : ModGL .E8 K) * (rootDiagUnit .E8 a)⁻¹ * (g : ModGL .E8 K)⁻¹)
    (hαo : orderOf α = 2) {D : Subgroup ↥(fixedSubgroup α)} (hD : A6Hyp α D) : False := by
  have : Finite (ModGL .E8 K) := finite_modGL
  have hKodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hα : α ^ 2 = 1 := hαo ▸ pow_orderOf_eq_one α
  have hα1 : α ≠ 1 := fun h => by
    rw [h, orderOf_one] at hαo
    exact absurd hαo (by norm_num)
  obtain ⟨b, hb, hb1, ⟨Θ⟩⟩ :=
    exists_toralCentralizer_equiv_of_innerDiag (Or.inr (Or.inr (Or.inr rfl))) hKodd hαg hα
  exact hD.false_of_hasBigLieSub hO hp2 ((e8_toral_hasBigLieSub hp hp2 hK hb (hb1 hα1)).of_mulEquiv
    Θ.symm)

theorem a6_E8_false (hO : LieOrderFormulasInput) {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (σ : MulAut (adjointGroup .E8 K))
    (hσ : orderOf σ = 2) {D : Subgroup ↥(fixedSubgroup σ)} (hD : A6Hyp σ D) : False := by
  have hf : 1 ≤ f := (one_le_and_three_le_of_card hp hp2 hK).1
  have : Finite (ModGL .E8 K) := finite_modGL
  have hKodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hσ2 : σ ^ 2 = 1 := hσ ▸ pow_orderOf_eq_one σ
  rcases odd_F4_E8_G2_involution_inner_or_quadratic (Or.inr (Or.inl rfl)) hKodd hσ2 with
    ⟨g, a, hσg⟩ | ⟨q, e, hq, he, hKe, δ, hδ, g, a, hσg⟩
  · exact a6_E8_inner_false hO hp hp2 hK hσg hσ hD
  · have hqp : q = p := by
      have h : q ∣ p ^ f := by
        rw [← hK, hKe]
        exact dvd_pow (dvd_pow_self q (by omega)) two_ne_zero
      exact (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h)
    subst hqp
    exact a6_exc_field_false hO (t := .E8) (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))) hq hp2
      he hKe δ hδ hσg hσ2 hD

theorem oddA6Shape_E8 (hO : LieOrderFormulasInput) (_hgls : GLS3OddFamilyInput .E8) :
    OddA6Shape .E8 := by
  refine oddA6Shape_of_concrete fun S _ _ n p f hp hp2 hadm hm => ?_
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E8
    ((GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2 :
      UntwistedChevalleyModel S .E8 (p ^ f))
  have : Finite ↥(adjointGroup .E8 F) := Finite.of_equiv S e.toEquiv
  exact ⟨↥(adjointGroup .E8 F), inferInstance, inferInstance, e, fun σ D hσ hD =>
    (a6_E8_false hO hp hp2 hF σ hσ hD).elim⟩

end CFSG.ComponentClassification.CatFC
