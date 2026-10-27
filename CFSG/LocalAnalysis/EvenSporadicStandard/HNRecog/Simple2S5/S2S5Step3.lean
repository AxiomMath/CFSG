module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.InvClasses

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

open CFSG.EvenSporadicStandard.TwoHS

section Cert


private lemma exists_conj_coe {x₀ a : ↥P1408} (h : IsConj a x₀) :
    ∃ c ∈ P1408, c * (x₀ : Equiv.Perm (Fin 1408)) * c⁻¹ =
      (a : Equiv.Perm (Fin 1408)) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  refine ⟨(c : Equiv.Perm (Fin 1408))⁻¹, P1408.inv_mem c.2, ?_⟩
  have hval : (c : Equiv.Perm (Fin 1408)) * (a : Equiv.Perm (Fin 1408)) *
      (c : Equiv.Perm (Fin 1408))⁻¹ = (x₀ : Equiv.Perm (Fin 1408)) := by
    simpa using congrArg Subtype.val hc
  rw [← hval]
  group

theorem exists_conj_t₀ (hΛ : HSCtx) {S : Subgroup (Equiv.Perm (Fin 1408))} (hSP : S ≤ P1408)
    (hSQ : S ≤ blocks1408) (haS : S ⊓ Subgroup.zpowers elemA = ⊥)
    {t : Equiv.Perm (Fin 1408)} (htS : t ∈ S) (ht2 : orderOf t = 2) :
    ∃ c ∈ P1408, c * t * c⁻¹ = elemZ ∨ c * t * c⁻¹ = elemA * elemZ := by
  let x : ↥P1408 := ⟨t, hSP htS⟩
  have hxt : (x : Equiv.Perm (Fin 1408)) = t := rfl
  have hx2 : orderOf x = 2 := by
    change orderOf (⟨t, hSP htS⟩ : ↥P1408) = 2
    rw [Subgroup.orderOf_mk]
    exact ht2
  obtain ⟨i, hi⟩ := involution_cover_inv (card_P1408 hΛ) x hx2
  obtain ⟨-, -, -, -, hAcomm, -, -, -, hBnb, hZ1nb⟩ := twoHSBasic_spec
  fin_cases i
  ·
    change IsConj pA x at hi
    obtain ⟨c', hc', hcj⟩ := exists_conj_coe hi
    have hconjA : c' * t * c'⁻¹ = elemA := by simpa [coe_pA, hxt] using hcj
    have htA : t = elemA := by
      have hcomm : elemA * c'⁻¹ = c'⁻¹ * elemA := hAcomm c'⁻¹ (P1408.inv_mem hc')
      calc t = c'⁻¹ * (c' * t * c'⁻¹) * c' := by group
           _ = c'⁻¹ * elemA * c' := by rw [hconjA]
           _ = elemA := by rw [← hcomm]; group
    have hbot : t ∈ (⊥ : Subgroup (Equiv.Perm (Fin 1408))) := by
      have hmem : t ∈ S ⊓ Subgroup.zpowers elemA :=
        ⟨htS, by rw [htA]; exact Subgroup.mem_zpowers elemA⟩
      rwa [haS] at hmem
    have ht1 : t = 1 := Subgroup.mem_bot.mp hbot
    rw [ht1, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  ·
    change IsConj pZ x at hi
    obtain ⟨c', hc', hcj⟩ := exists_conj_coe hi
    exact ⟨c', hc', Or.inl (by simpa [coe_pZ, hxt] using hcj)⟩
  ·
    change IsConj (pA * pZ) x at hi
    obtain ⟨c', hc', hcj⟩ := exists_conj_coe hi
    exact ⟨c', hc', Or.inr (by simpa [Subgroup.coe_mul, coe_pA, coe_pZ, hxt] using hcj)⟩
  ·
    change IsConj pB x at hi
    obtain ⟨c', hc', hcj⟩ := exists_conj_coe hi
    have hconjB : c' * t * c'⁻¹ = elemB := by simpa [coe_pB, hxt] using hcj
    have hxS : t ∈ pPrime := Subgroup.mem_inf.mpr ⟨hSP htS, hSQ htS⟩
    have hmem : c' * t * c'⁻¹ ∈ pPrime := conj_mem_pPrime hΛ hc' hxS
    rw [hconjB] at hmem
    exact absurd (Subgroup.mem_inf.mp hmem).2 hBnb
  ·
    change IsConj pZ₁ x at hi
    obtain ⟨c', hc', hcj⟩ := exists_conj_coe hi
    have hconjZ₁ : c' * t * c'⁻¹ = elemZ₁ := by simpa [coe_pZ₁, hxt] using hcj
    have hxS : t ∈ pPrime := Subgroup.mem_inf.mpr ⟨hSP htS, hSQ htS⟩
    have hmem : c' * t * c'⁻¹ ∈ pPrime := conj_mem_pPrime hΛ hc' hxS
    rw [hconjZ₁] at hmem
    exact absurd (Subgroup.mem_inf.mp hmem).2 hZ1nb

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5
