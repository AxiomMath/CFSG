module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CompatModel.WitSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.SylowCover
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableISpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.InvClasses

public section

namespace CFSG.EvenSporadicStandard.HNRecog.CompatModel

open Subgroup CFSG.EvenSporadicStandard.HNRecog

private theorem factorization_80640 : (80640 : ℕ).factorization 2 = 8 := by
  rw [show (80640 : ℕ) = 2 ^ 8 * 315 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

section Cert


theorem exists_modelVertex (hP : Nat.card ↥P1408 = 177408000) {τ : ↥P1408} (hτ : orderOf τ = 2)
    (hc : pB * τ = τ * pB) (h1 : τ ≠ pA) (h2 : τ ≠ pB) (h3 : τ ≠ pA * pB) :
    ∃ w : ↥P1408, ModelVertex w ∧ w * τ = τ * w := by
  obtain ⟨hcard, hle, hcov⟩ := witSylow_spec
  have hbcard : Nat.card ↥(P1408 ⊓ centralizer ({elemB} : Set (Equiv.Perm (Fin 1408)))) = 80640 :=
    (invClasses_classSpec hP).2.2.1.cent_card
  have hSord : Nat.card ↥(closure (elemW '' {w | w ∈ witSylow})) =
      2 ^ (Nat.card ↥(P1408 ⊓ centralizer ({elemB} : Set (Equiv.Perm (Fin 1408))))).factorization
        2 := by
    rw [hcard, hbcard, factorization_80640]
    norm_num
  have hτR : (τ : Equiv.Perm (Fin 1408)) ∈
      P1408 ⊓ centralizer ({elemB} : Set (Equiv.Perm (Fin 1408))) :=
    Subgroup.mem_inf.2 ⟨τ.2, Subgroup.mem_centralizer_singleton_iff.2
      (congrArg Subtype.val hc.symm)⟩
  have hτo : orderOf (τ : Equiv.Perm (Fin 1408)) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hτ
  obtain ⟨x, hxR, hxS⟩ :=
    TwoHSData.exists_conj_mem_of_orderOf_eq_prime (p := 2) hle hSord hτR hτo
  obtain ⟨hxP, hxB⟩ := Subgroup.mem_inf.1 hxR
  have hxB' : x * elemB = elemB * x := Subgroup.mem_centralizer_singleton_iff.1 hxB
  let x' : ↥P1408 := ⟨x, hxP⟩
  let s' : ↥P1408 := x'⁻¹ * τ * x'
  have hτ_eq : τ = x' * s' * x'⁻¹ := by
    simp only [s']
    group
  have hxpB : x' * pB * x'⁻¹ = pB :=
    Subtype.ext (by
      show x * elemB * x⁻¹ = elemB
      rw [hxB', mul_assoc, mul_inv_cancel, mul_one])
  have hxpA : x' * pA * x'⁻¹ = pA :=
    Subtype.ext (by
      show x * elemA * x⁻¹ = elemA
      rw [← elemA_comm hxP, mul_assoc, mul_inv_cancel, mul_one])
  have hso : orderOf (x⁻¹ * (τ : Equiv.Perm (Fin 1408)) * x) = 2 := by
    have hs'o : orderOf s' = 2 := by
      rw [show s' = MulAut.conj x'⁻¹ τ by simp [s', MulAut.conj_apply], MulEquiv.orderOf_eq]
      exact hτ
    exact (Subgroup.orderOf_coe s').trans hs'o
  rcases hcov _ hxS hso with h | h | h | ⟨w, hw, hws⟩
  · exact absurd (by rw [hτ_eq, show s' = pA from Subtype.ext h, hxpA]) h1
  · exact absurd (by rw [hτ_eq, show s' = pB from Subtype.ext h, hxpB]) h2
  · refine absurd ?_ h3
    rw [hτ_eq, show s' = pA * pB from Subtype.ext h,
      show x' * (pA * pB) * x'⁻¹ = (x' * pA * x'⁻¹) * (x' * pB * x'⁻¹) by group, hxpA, hxpB]
  · have hws' : w * s' = s' * w := Subtype.ext hws
    refine ⟨x' * w * x'⁻¹, hw.map_conj hxpB, ?_⟩
    have key : x' * w * x'⁻¹ * (x' * s' * x'⁻¹) = x' * s' * x'⁻¹ * (x' * w * x'⁻¹) :=
      calc x' * w * x'⁻¹ * (x' * s' * x'⁻¹) = x' * (w * s') * x'⁻¹ := by group
        _ = x' * (s' * w) * x'⁻¹ := by rw [hws']
        _ = x' * s' * x'⁻¹ * (x' * w * x'⁻¹) := by group
    rw [← hτ_eq] at key
    exact key

end Cert

end CFSG.EvenSporadicStandard.HNRecog.CompatModel
