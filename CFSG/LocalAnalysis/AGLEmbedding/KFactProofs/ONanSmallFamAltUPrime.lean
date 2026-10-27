module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltMaxThree
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamNoTwoAlt
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltAut
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltAutThree

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.Open

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem kFactUPrime_of_autFixInner (hp : p.Prime) (hp2 : p ≠ 2) (hK : IsAltTwoP p K)
    (hmax : ∀ (T : Sylow p K) (Y : Subgroup K), GLBCore p 1 (T : Subgroup K) ≤ Y →
      Y = GLBCore p 1 (T : Subgroup K) ∨ Y = ⊤)
    (hA : ∀ T : Sylow p K, AutFixInner p K T) : KFactUPrime p K := by
  intro T _
  have hT0 : (T : Subgroup K) ≠ ⊥ := by
    obtain ⟨e⟩ := hK
    intro h
    have := sylowSq_of_isAltTwoP hp hp2 ⟨e⟩ T
    rw [h, Subgroup.card_bot] at this
    have hp1 := hp.one_lt
    nlinarith
  have hTΓ : (T : Subgroup K) ≤ GLBCore p 1 (T : Subgroup K) :=
    CFSG.AGLEmbedding.le_glbCore_one_of_ne_bot hp T hT0
  refine ⟨fun Y hY => hmax T Y hY, fun N hNΓ hNn hcop => ?_, fun f hf => ?_⟩
  · have hconj : ∀ t ∈ (T : Subgroup K), ∀ x ∈ N, t * x * t⁻¹ ∈ N := by
      intro t ht x hx
      have h1 := hNn.conj_mem (⟨x, hNΓ hx⟩ : GLBCore p 1 (T : Subgroup K))
        (Subgroup.mem_subgroupOf.2 hx) ⟨t, hTΓ ht⟩
      exact Subgroup.mem_subgroupOf.1 h1
    have hTN : (T : Subgroup K) ≤ Subgroup.normalizer (N : Set K) := by
      intro t ht
      apply Subgroup.mem_normalizer_fintype
      intro x hx
      exact hconj t ht x hx
    refine eq_bot_of_normalizes_of_isAltTwoP hp hp2 hK T N (fun h => ?_) hTN
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop h)
  · obtain ⟨g, hg⟩ := hA T f fun t ht => hf t (hTΓ ht)
    obtain ⟨k, -, hkT⟩ := exists_inverting_of_isAltTwoP hp hp2 hK T
    have hkN : k ∈ Subgroup.normalizer ((T : Subgroup K) : Set K) := by
      apply Subgroup.mem_normalizer_fintype
      intro t ht
      rw [hkT t ht]
      exact Subgroup.inv_mem _ ht
    have hkΓ : k ∈ GLBCore p 1 (T : Subgroup K) := normalizer_le_glbCore_one hp T hT0 hkN
    have hgc : ∀ t ∈ (T : Subgroup K), g * t = t * g := by
      intro t ht
      have h1 := hf t (hTΓ ht)
      rw [← hg, MulAut.conj_apply] at h1
      calc g * t = (g * t * g⁻¹) * g := by group
        _ = t * g := by rw [h1]
    have hgT : g ∈ (T : Subgroup K) := centralizer_le_of_isAltTwoP hp hp2 hK T hgc
    have hk1 := hf k hkΓ
    rw [← hg, MulAut.conj_apply] at hk1
    have hkg : k * g = g * k := (mul_inv_eq_iff_eq_mul.1 hk1).symm
    have hg1 : g = 1 := eq_one_of_inverted hp hp2 hK T hgT (hkT g hgT) hkg
    rw [← hg, hg1, map_one]

theorem kFactUPrime_of_isAltTwoP_of_five_le (hp : p.Prime) (hp5 : 5 ≤ p) (hK : IsAltTwoP p K) :
    KFactUPrime p K :=
  kFactUPrime_of_autFixInner hp (by omega) hK
    (fun T _ hY => eq_or_eq_top_of_glbCore_le_of_five_le hp hp5 hK T hY)
    (fun T => autFixInner_of_isAltTwoP_of_five_le hp hp5 hK T)

theorem kFactUPrime_of_isAltTwoP (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : IsAltTwoP p K) : KFactUPrime p K := by
  by_cases h3 : p = 3
  · subst h3
    exact kFactUPrime_of_autFixInner hp hp2 hK
      (fun T _ hY => eq_or_eq_top_of_glbCore_le_three hK T hY)
      (fun T => autFixInner_of_isAltTwoP_three hK T)
  · have h4 : p ≠ 4 := by
      rintro rfl
      norm_num at hp
    have := hp.two_le
    exact kFactUPrime_of_isAltTwoP_of_five_le hp (by omega) hK

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
