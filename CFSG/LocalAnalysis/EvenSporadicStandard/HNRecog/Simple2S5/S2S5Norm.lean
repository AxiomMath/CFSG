module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5Step1
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5Step3
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5Step45

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

open CFSG.EvenSporadicStandard.TwoHS

theorem map_inf_centralizer_conj (S : Subgroup (Equiv.Perm (Fin 1408)))
    (c t : Equiv.Perm (Fin 1408)) :
    (S.map (MulAut.conj c).toMonoidHom) ⊓
        Subgroup.centralizer ({c * t * c⁻¹} : Set (Equiv.Perm (Fin 1408))) =
      (S ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 1408)))).map
        (MulAut.conj c).toMonoidHom := by
  have hφ : ∀ x : Equiv.Perm (Fin 1408), MulAut.conj c x = c * x * c⁻¹ :=
    fun x => MulAut.conj_apply c x
  ext x
  constructor
  · rintro ⟨hxS, hxC⟩
    rcases Subgroup.mem_map.mp hxS with ⟨s, hs, rfl⟩
    have hcomm : MulAut.conj c s * (c * t * c⁻¹) = (c * t * c⁻¹) * MulAut.conj c s :=
      Subgroup.mem_centralizer_singleton_iff.mp hxC
    have hst : s * t = t * s := by
      apply (MulAut.conj c).injective
      rw [map_mul, map_mul]
      rw [← hφ t] at hcomm
      exact hcomm
    exact Subgroup.mem_map.mpr
      ⟨s, ⟨hs, Subgroup.mem_centralizer_singleton_iff.mpr hst⟩, rfl⟩
  · rintro hx
    rcases Subgroup.mem_map.mp hx with ⟨s, ⟨hs, hsc⟩, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom hs, ?_⟩
    change MulAut.conj c s ∈
      Subgroup.centralizer ({c * t * c⁻¹} : Set (Equiv.Perm (Fin 1408)))
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hst : s * t = t * s := Subgroup.mem_centralizer_singleton_iff.mp hsc
    calc MulAut.conj c s * (c * t * c⁻¹) = MulAut.conj c s * MulAut.conj c t := by rw [← hφ t]
      _ = MulAut.conj c (s * t) := by rw [map_mul]
      _ = MulAut.conj c (t * s) := by rw [hst]
      _ = MulAut.conj c t * MulAut.conj c s := by rw [map_mul]
      _ = (c * t * c⁻¹) * MulAut.conj c s := by rw [← hφ t]

section Cert


theorem good_basic (hΛ : HSCtx) {S : Subgroup (Equiv.Perm (Fin 1408))}
    {t : Equiv.Perm (Fin 1408)} (h : Good S t) :
    S ≤ pPrime ∧ S ⊓ Subgroup.zpowers elemA = ⊥ ∧ Nat.card ↥S ∣ 44352000 := by
  haveI := h.simple
  have hYcard : Nat.card ↥(S ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 1408)))) =
      240 :=
    (step2 (Y := S ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 1408)))) h.cover
      ⟨h.mem, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
      (fun y hy => (Subgroup.mem_centralizer_singleton_iff.mp hy.2).symm) h.ne).1
  have h2S : 2 < Nat.card ↥S := by
    have hle : Nat.card ↥(S ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 1408)))) ≤
        Nat.card ↥S := Subgroup.card_le_of_le inf_le_left
    omega
  obtain ⟨hSQ, hdisj, hdvd⟩ :=
    step1 (P := P1408) (Q := pPrime) pPrime_le (relIndex_pPrime hΛ) (a := elemA)
      (Subgroup.mem_inf.mpr ⟨elemA_mem, twoHSBasic_spec.2.2.2.2.2.1⟩)
      twoHSBasic_spec.1 twoHSBasic_spec.2.2.2.2.1 h.le h2S
  refine ⟨hSQ, hdisj, ?_⟩
  rw [card_pPrime hΛ] at hdvd
  rw [show (88704000 : ℕ) = 2 * 44352000 by norm_num] at hdvd
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < (2 : ℕ)) hdvd

theorem exists_normalized (hΛ : HSCtx) (hF : YFacts) {S₁ : Subgroup (Equiv.Perm (Fin 1408))}
    {t₁ : Equiv.Perm (Fin 1408)} (h : Good S₁ t₁) :
    ∃ (S₃ : Subgroup (Equiv.Perm (Fin 1408))) (k : ℕ), k < 2 ∧ Good S₃ (elemA * elemZ) ∧
      S₃ ≤ pPrime ∧ S₃ ⊓ Subgroup.zpowers elemA = ⊥ ∧ Nat.card ↥S₃ ∣ 44352000 ∧
      S₃ ⊓ Subgroup.centralizer ({elemA * elemZ} : Set (Equiv.Perm (Fin 1408))) = yK k ∧
      Nonempty (↥S₁ ≃* ↥S₃) := by
  obtain ⟨hSP₁, haS₁, -⟩ := good_basic hΛ h
  have hSQ₁ : S₁ ≤ blocks1408 := fun x hx => (Subgroup.mem_inf.mp (hSP₁ hx)).2
  have ht2 : orderOf t₁ = 2 := by
    haveI : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
    exact orderOf_eq_prime (by rw [pow_two]; exact h.sq) h.ne
  obtain ⟨c, hc, hct⟩ := exists_conj_t₀ hΛ h.le hSQ₁ haS₁ h.mem ht2
  let S₂ : Subgroup (Equiv.Perm (Fin 1408)) := S₁.map (MulAut.conj c).toMonoidHom
  let t₂ : Equiv.Perm (Fin 1408) := c * t₁ * c⁻¹
  have h₂ : Good S₂ t₂ := h.conj hc
  obtain ⟨hSP₂, -, -⟩ := good_basic hΛ h₂
  obtain ⟨ht₂eq, k, hk2, c₂, hc₂, hmap⟩ := exists_conj_Yk hF h₂ hSP₂ hct
  let S₃ : Subgroup (Equiv.Perm (Fin 1408)) := S₂.map (MulAut.conj c₂).toMonoidHom
  have hcent : c₂ * (elemA * elemZ) * c₂⁻¹ = elemA * elemZ := by
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hc₂.2
    rw [hcomm]
    group
  have h₃ : Good S₃ (elemA * elemZ) := by
    have hc3 := h₂.conj hc₂.1
    rw [ht₂eq, hcent] at hc3
    exact hc3
  obtain ⟨hSP₃, haS₃, hdvd₃⟩ := good_basic hΛ h₃
  refine ⟨S₃, k, hk2, h₃, hSP₃, haS₃, hdvd₃, ?_, ?_⟩
  · have hmap' := map_inf_centralizer_conj S₂ c₂ (elemA * elemZ)
    rw [hcent] at hmap'
    rw [show S₃ = S₂.map (MulAut.conj c₂).toMonoidHom from rfl, hmap', hmap]
  · exact ⟨(Subgroup.equivMapOfInjective S₁ (MulAut.conj c).toMonoidHom
        (MulAut.conj c).injective).trans
      (Subgroup.equivMapOfInjective S₂ (MulAut.conj c₂).toMonoidHom
        (MulAut.conj c₂).injective)⟩

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5
