module

public import CFSG.ClassicalInvolution.Asc77.AscIH8Bridge
public import CFSG.ClassicalInvolution.Asc77.WP2Defs
public import CFSG.ClassicalInvolution.Generic.Frame
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Asc77.WP1Section6
public import CFSG.ClassicalInvolution.Asc77.WP2Interface
public import CFSG.ClassicalInvolution.Balance.LayerGenerationInner
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.ClassicalInvolution.ModelFacts.TG3

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1

theorem natCard_galoisField_three : Nat.card 𝔽₃ = 3 := by
  rw [GaloisField.card 3 1 (by norm_num)]
  norm_num

theorem odd_natCard_galoisField_three : Odd (Nat.card 𝔽₃) := by
  rw [natCard_galoisField_three]
  decide

theorem two_ne_zero_three : (2 : 𝔽₃) ≠ 0 := two_ne_zero_galoisField 1 (by norm_num)

theorem natCard_sl2_three : Nat.card SL(2, 𝔽₃) = 24 := by
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, natCard_galoisField_three]
  norm_num

theorem injOn_of_natCard_map3 {M X : Type} [Group M] [Group X] [Finite M] (ψ : M →* X)
    {R : Subgroup M} (h : Nat.card R = Nat.card (R.map ψ)) :
    ∀ r ∈ R, ∀ s ∈ R, ψ r = ψ s → r = s := by
  have hbij : Function.Bijective (ψ.subgroupMap R) :=
    (ψ.subgroupMap_surjective R).bijective_of_nat_card_le h.le
  intro r hr s hs hrs
  have := hbij.1 (a₁ := ⟨r, hr⟩) (a₂ := ⟨s, hs⟩) (Subtype.ext hrs)
  exact congrArg Subtype.val this

section Four

variable {M X : Type} [Group M] [Group X]

theorem uniqueInvolution_map3 [Finite M] (ψ : M →* X) {R : Subgroup M} (e : R ≃* SL(2, 𝔽₃))
    (hcard : Nat.card (R.map ψ) = 24) :
    IsUniqueInvolution (R.map ψ) (ψ (sl2Inv e)) ∧ ∀ r ∈ R, ∀ s ∈ R, ψ r = ψ s → r = s := by
  have hodd := odd_natCard_galoisField_three
  have hRcard : Nat.card R = Nat.card (R.map ψ) := by
    rw [hcard, Nat.card_congr e.toEquiv]
    exact natCard_sl2_three
  have hinj := injOn_of_natCard_map3 ψ hRcard
  refine ⟨⟨Subgroup.mem_map_of_mem ψ (sl2Inv_mem e), ?_, ?_, ?_⟩, hinj⟩
  · intro h
    apply sl2Inv_ne_one hodd e
    exact hinj _ (sl2Inv_mem e) 1 R.one_mem (h.trans (map_one ψ).symm)
  · rw [← map_mul, sl2Inv_mul_self hodd e, map_one]
  · rintro _ ⟨r, hr, rfl⟩ hy
    have hrr : r * r = 1 :=
      hinj _ (R.mul_mem hr hr) 1 R.one_mem (by rw [map_mul, hy, map_one])
    by_cases hr1 : r = 1
    · left
      rw [hr1, map_one]
    · right
      have h2 : orderOf r = 2 := orderOf_eq_prime (by rwa [pow_two]) hr1
      rw [eq_sl2Inv_of_orderOf_eq_two hodd e hr h2]

theorem twin_ratio_mem_ker [Finite M] (ψ : M →* X) {R₁ R₂ : Subgroup M} (e₁ : R₁ ≃* SL(2, 𝔽₃))
    (e₂ : R₂ ≃* SL(2, 𝔽₃)) (h24₁ : Nat.card (R₁.map ψ) = 24) (h24₂ : Nat.card (R₂.map ψ) = 24)
    {z : X} (hz₁ : IsUniqueInvolution (R₁.map ψ) z) (hz₂ : IsUniqueInvolution (R₂.map ψ) z) :
    sl2Inv e₂ * (sl2Inv e₁)⁻¹ ∈ ψ.ker := by
  obtain ⟨u₁, -⟩ := uniqueInvolution_map3 ψ e₁ h24₁
  obtain ⟨u₂, -⟩ := uniqueInvolution_map3 ψ e₂ h24₂
  rw [MonoidHom.mem_ker, map_mul, map_inv, u₁.eq hz₁, u₂.eq hz₂, mul_inv_cancel]

theorem mem_sup_of_commutes {K L : Subgroup X} (h : Commutes K L) {x : X} (hx : x ∈ K ⊔ L) :
    ∃ a ∈ K, ∃ b ∈ L, a * b = x := by
  let P : Subgroup X :=
    { carrier := {x | ∃ a ∈ K, ∃ b ∈ L, a * b = x}
      one_mem' := ⟨1, K.one_mem, 1, L.one_mem, mul_one 1⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', K.mul_mem ha ha', b * b', L.mul_mem hb hb', ?_⟩
        calc a * a' * (b * b') = a * (a' * b) * b' := by group
          _ = a * (b * a') * b' := by rw [h a' ha' b hb]
          _ = a * b * (a' * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, K.inv_mem ha, b⁻¹, L.inv_mem hb, ?_⟩
        calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := by group
          _ = (a * b)⁻¹ := by rw [h a ha b hb] }
  have hle : K ⊔ L ≤ P := sup_le (fun a ha => ⟨a, ha, 1, L.one_mem, mul_one a⟩)
    (fun b hb => ⟨1, K.one_mem, b, hb, one_mul b⟩)
  exact hle hx

theorem exists_mem_ne_of_card_four {A : Subgroup X} (hA : IsElemAbelian2 A 2) {z : X} :
    ∃ w ∈ A, w ≠ 1 ∧ w ≠ z := by
  by_contra hcon
  push Not at hcon
  have hsub : (A : Set X) ⊆ {1, z} := fun w hw => by
    by_cases h1 : w = 1
    · exact Or.inl h1
    · exact Or.inr (hcon w hw h1)
  have h1 : Nat.card A ≤ 2 := by
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [← Nat.card_coe_set_eq] at this
    exact this.trans ((Set.ncard_insert_le _ _).trans (by simp))
  have h2 := hA.1
  omega

end Four

end CFSG.ClassicalInvolution.ModelFacts.TG3
