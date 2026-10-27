module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClExcField
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Transport
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddG2Inner

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Ree (ReeTag)

theorem card_specialLinear_two_eq (F : Type*) [Field F] [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  let : Fintype F := Fintype.ofFinite F
  let q := Nat.card F
  have hq : 2 ≤ q := Finite.one_lt_card
  have hsq : q ^ 2 - q = q * (q - 1) := by
    rw [pow_two, Nat.mul_sub_left_distrib, mul_one]
  rw [Matrix.card_SL_field 2, Fin.prod_univ_two]
  rw [← Nat.card_eq_fintype_card]
  change ((q ^ 2 - q ^ 0) * (q ^ 2 - q ^ 1)) / (q - 1) = q * (q ^ 2 - 1)
  rw [pow_zero, pow_one, hsq, ← mul_assoc, Nat.mul_div_cancel]
  · exact Nat.mul_comm _ _
  · omega

theorem three_pow_odd_mod_five (a : ℕ) :
    3 ^ (2 * a + 1) % 5 = 2 ∨ 3 ^ (2 * a + 1) % 5 = 3 := by
  induction a with
  | zero => norm_num
  | succ n ih =>
    have h : 3 ^ (2 * (n + 1) + 1) = 3 ^ (2 * n + 1) * 9 := by ring
    omega

theorem not_five_dvd_ree_card {q : ℕ} (hq : q % 5 = 2 ∨ q % 5 = 3) :
    ¬ 5 ∣ q ^ 3 * (q ^ 3 + 1) * (q - 1) := by
  have h5 : Nat.Prime 5 := by norm_num
  have h3 : q ^ 3 % 5 = 3 ∨ q ^ 3 % 5 = 2 := by
    rw [Nat.pow_mod]
    rcases hq with h | h <;> rw [h] <;> norm_num
  rw [Nat.Prime.dvd_mul h5, Nat.Prime.dvd_mul h5]
  omega


theorem a6_G2_inner_false (hO : LieOrderFormulasInput) {K : Type} [Field K] [Finite K]
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f) {α : MulAut (adjointGroup .G2 K)}
    {g : adjointGroup .G2 K} {a : Fin Tag.G2.rank → Kˣ}
    (hαg : ∀ h : adjointGroup .G2 K, (α h : ModGL .G2 K) = (g : ModGL .G2 K) *
      rootDiagUnit .G2 a * (h : ModGL .G2 K) * (rootDiagUnit .G2 a)⁻¹ * (g : ModGL .G2 K)⁻¹)
    (hαo : orderOf α = 2) {D : Subgroup ↥(fixedSubgroup α)} (hD : A6Hyp α D) : False := by
  have : Finite (ModGL .G2 K) := finite_modGL
  have hKodd : Odd (Nat.card K) := by
    rw [hK]; exact (Nat.prime_three.eq_two_or_odd'.resolve_left (by decide)).pow
  have hα : α ^ 2 = 1 := hαo ▸ pow_orderOf_eq_one α
  have hα1 : α ≠ 1 := fun h => by
    rw [h, orderOf_one] at hαo
    exact absurd hαo (by norm_num)
  obtain ⟨b, hb, hb1, ⟨Θ⟩⟩ := exists_toralCentralizer_equiv_of_innerDiag (Or.inl rfl) hKodd hαg hα
  have hb1' := hb1 hα1
  have hK2 : Nat.card K ≠ 2 := fun h => absurd (h ▸ hKodd) (by decide)
  obtain ⟨-, -, hcases, hstruct, hq3⟩ := odd_G2_toral_involution_fixed_p_components K hKodd b hb
  by_cases hK3 : Nat.card K = 3
  ·
    have hsolv : Group.IsSolvable ↥(toralCentralizer .G2 K b) := (hq3 hK3 hb1').1
    exact hD.not_solvable
      (Group.isSolvable_of_isSolvable_injective (f := Θ.toMonoidHom) Θ.injective)
  ·
    obtain ⟨α₀, β₀, hc⟩ : ∃ α₀ β₀ : Fin Tag.G2.rank → ℤ,
        (b = ![-1, 1] ∧ α₀ = ![0, 1] ∧ β₀ = ![2, 3]) ∨
          (b = ![1, -1] ∧ α₀ = ![1, 0] ∧ β₀ = ![1, 2]) ∨
            (b = ![-1, -1] ∧ α₀ = ![1, 1] ∧ β₀ = ![1, 3]) := by
      rcases hcases with h | h | h | h
      · exact absurd h hb1'
      · exact ⟨_, _, Or.inl ⟨h, rfl, rfl⟩⟩
      · exact ⟨_, _, Or.inr (Or.inl ⟨h, rfl, rfl⟩)⟩
      · exact ⟨_, _, Or.inr (Or.inr ⟨h, rfl, rfl⟩)⟩
    obtain ⟨-, -, hS, -, -, ⟨eα⟩, -, hSX, -, -, -⟩ := hstruct α₀ β₀ hc
    have hQαX : rootSubgroup .G2 K α₀ ⊔ rootSubgroup .G2 K (-α₀) ≤ toralCentralizer .G2 K b :=
      (hS ▸ (le_sup_left : rootSubgroup .G2 K α₀ ⊔ rootSubgroup .G2 K (-α₀) ≤
        (rootSubgroup .G2 K α₀ ⊔ rootSubgroup .G2 K (-α₀)) ⊔
          (rootSubgroup .G2 K β₀ ⊔ rootSubgroup .G2 K (-β₀)))).trans hSX
    let φ : SL2 K →* ↥(fixedSubgroup α) :=
      Θ.symm.toMonoidHom.comp ((Subgroup.inclusion hQαX).comp eα.toMonoidHom)
    have hφ : Function.Injective φ :=
      Θ.symm.injective.comp ((Subgroup.inclusion_injective hQαX).comp eα.injective)
    have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl (Or.inr hK2)
      (Or.inr hK3)
    have hq9 : 9 ≤ Nat.card K := by
      rcases Nat.lt_or_ge f 2 with h | h
      · have : f = 1 := by omega
        subst this
        exact absurd (by simpa using hK) hK3
      · rw [hK]
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) h
    have hcard := card_specialLinear_two_eq K
    have hker : Nat.card φ.ker ≤ 1 := by
      rw [(MonoidHom.ker_eq_bot_iff φ).2 hφ, Subgroup.card_bot]
    refine hD.perfect_witness φ (Group.isPerfect_def.mp hSL.1) hker ?_
    rw [hcard]
    have h1 : 9 * 80 ≤ Nat.card K * (Nat.card K ^ 2 - 1) :=
      Nat.mul_le_mul hq9 (by have : 81 ≤ Nat.card K ^ 2 := by nlinarith
                             omega)
    omega

theorem a6_G2_ree_false {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime] {b : ℕ}
    (hK : Nat.card K = 3 ^ (2 * b + 1)) {g : adjointGroup ReeTag.G2.tag K}
    (hg : (MulAut.conj g * ReeTag.G2.finiteReeAut K b) ^ 2 = 1)
    {D : Subgroup ↥(fixedSubgroup (MulAut.conj g * ReeTag.G2.finiteReeAut K b))}
    (hD : A6Hyp (MulAut.conj g * ReeTag.G2.finiteReeAut K b) D) : False := by
  obtain ⟨⟨ψ, hψ⟩, -, -⟩ :=
    LieType.Ree.G2_exceptional_coset_involution_fixed_p_components b K hK g hg
  have hc : MulAut.congr ψ (MulAut.conj g * ReeTag.G2.finiteReeAut K b) =
      ReeTag.G2.finiteReeAut K b :=
    (MulEquiv.ext fun _ => rfl : MulAut.congr ψ (MulAut.conj g * ReeTag.G2.finiteReeAut K b) =
      ψ * (MulAut.conj g * ReeTag.G2.finiteReeAut K b) * ψ⁻¹).trans hψ
  have hmap : (fixedSubgroup (ReeTag.G2.finiteReeAut K b)).map
      (adjointGroup ReeTag.G2.tag K).subtype = ReeTag.G2.reeGamma K b := rfl
  have hFc : fixedSubgroup (MulAut.congr ψ (MulAut.conj g * ReeTag.G2.finiteReeAut K b)) =
      fixedSubgroup (ReeTag.G2.finiteReeAut K b) := by rw [hc]
  let Ψ' : ↥(fixedSubgroup (MulAut.conj g * ReeTag.G2.finiteReeAut K b)) ≃*
      ReeTag.G2.reeGamma K b :=
    (fixedSubgroupCongrEquiv ψ _).trans ((MulEquiv.subgroupCongr hFc).trans
      (((fixedSubgroup (ReeTag.G2.finiteReeAut K b)).equivMapOfInjective _
        Subtype.val_injective).trans (MulEquiv.subgroupCongr hmap)))
  have hcard := (Nat.card_congr Ψ'.toEquiv).trans (LiteratureLocal.G2_card_reeGamma b hK)
  have h1 := hD.dvd
  rw [hcard] at h1
  exact not_five_dvd_ree_card (three_pow_odd_mod_five b) ((by norm_num : 5 ∣ 360).trans h1)

theorem a6_G2_false (hO : LieOrderFormulasInput) {K : Type} [Field K] [Finite K] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f) (σ : MulAut (adjointGroup .G2 K))
    (hσ : orderOf σ = 2) {D : Subgroup ↥(fixedSubgroup σ)} (hD : A6Hyp σ D) : False := by
  have : Finite (ModGL .G2 K) := finite_modGL
  have : CharP K ReeTag.G2.prime :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three hf hK
  have hσ2 : σ ^ 2 = 1 := hσ ▸ pow_orderOf_eq_one σ
  rcases G2_three_involution_inner_quadratic_or_exceptional hf hK hσ2 with ⟨g, a, hσg⟩ |
    ⟨e, he, hKe, δ, hδ, g, a, hσg⟩ | ⟨b, g, hfb, rfl⟩
  · exact a6_G2_inner_false hO hf hK hσg hσ hD
  · exact a6_exc_field_false hO (t := .G2) (Or.inl ⟨rfl, rfl⟩) Nat.prime_three (by decide) he hKe
      δ hδ hσg hσ2 hD
  · exact a6_G2_ree_false (hfb ▸ hK) hσ2 hD

theorem oddA6Shape_G2 (hO : LieOrderFormulasInput) (hgls : GLS3OddFamilyInput .G2) :
    OddA6Shape .G2 := by
  refine oddA6Shape_of_concrete fun S _ _ n p f hp hp2 hadm hm => ?_
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2
    ((GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2 :
      UntwistedChevalleyModel S .G2 (p ^ f))
  have : Finite ↥(adjointGroup .G2 F) := Finite.of_equiv S e.toEquiv
  refine ⟨↥(adjointGroup .G2 F), inferInstance, inferInstance, e, fun σ D hσ hD => ?_⟩
  exfalso
  have hp3 : p = 3 := hD.char_three hO hgls hp hp2 hadm (lieModel_of_mulEquiv e hm) hσ
  subst hp3
  exact a6_G2_false hO hadm.2.1 hF σ hσ hD

end CFSG.ComponentClassification.CatFC
