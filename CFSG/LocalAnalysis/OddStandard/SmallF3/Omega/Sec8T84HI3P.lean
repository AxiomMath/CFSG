module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84HMono
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84HUnits
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84HDet

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma swap45_mem_hMonoC :
    (Equiv.swap 4 5 : Equiv.Perm (Fin 6)) ∈ hMonoC := by
  rw [hMonoC, Subgroup.mem_centralizer_iff]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx]
  decide

private lemma hH2_comm_ffK0_ffF0 {κ : Equiv.Perm (Fin 6)} (hκ : κ ∈ ffK0)
    {K : Finset (Fin 6)} (hK : K ∈ ffF0) :
    Equiv.swap 4 5 * κ = κ * Equiv.swap 4 5 ∧
      symmDiff (({1, 3} : Finset (Fin 6)).map κ⁻¹.toEmbedding) K =
        symmDiff (K.map (Equiv.swap 4 5)⁻¹.toEmbedding) ({1, 3} : Finset (Fin 6)) := by
  simp only [ffK0, Finset.mem_insert, Finset.mem_singleton] at hκ
  simp only [ffF0, Finset.mem_insert, Finset.mem_singleton] at hK
  rcases hκ with rfl | rfl | rfl | rfl <;>
    rcases hK with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private lemma po_translate_A (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1)
    {t : OGroup Q} {σ : Equiv.Perm (Fin 6)} {J : Finset (Fin 6)}
    (ht : t = fr.permOrth σ * fr.signChange J) (hσC : σ ∈ hMonoC)
    (hσA : σ ∈ alternatingGroup (Fin 6)) (hJ : Odd J.card) (h2 : t * t = 1) :
    ∃ U : Subgroup (OGroup Q), U ≤ ffP0 hQ fr ∧ piOrth Q ∈ U ∧
      (∀ a ∈ U, ∀ b ∈ U, a * b = b * a) ∧ (∀ a ∈ U, a * a = 1) ∧ Nat.card U = 2 ^ 5 ∧
      ∃ p ∈ ffP0 hQ fr, (p * t) * (p * t) = 1 ∧
        (∀ u ∈ U, (p * t) * u = u * (p * t)) ∧ invDim (p * t) = 3 ∧
        p * t ≠ 1 ∧ p * t ≠ piOrth Q := by
  have hσD : σ ∈ monoD := by
    rw [monoD_eq_inf]
    exact Subgroup.mem_inf.mpr ⟨hσA, hσC⟩
  have hH1p : hH1 fr = fr.permOrth 1 * fr.signChange {3, 4, 5} := by
    rw [hH1, fr.permOrth_one, one_mul]
  have hpP0 : hH1 fr * t ∈ ffP0 hQ fr := by
    have h := ffMono_mul fr 1 σ {3, 4, 5} J
    rw [ht, hH1p, h, one_mul]
    refine (mem_ffP0_iff hQ fr).mpr
      ⟨σ, hσD, symmDiff (({3, 4, 5} : Finset (Fin 6)).map σ⁻¹.toEmbedding) J, ?_, rfl⟩
    rw [Finset.even_card_symmDiff_iff, Finset.card_map]
    exact iff_of_false (by decide) (Nat.not_even_iff_odd.mpr hJ)
  have hpt : (hH1 fr * t) * t = hH1 fr := by rw [mul_assoc, h2, mul_one]
  refine ⟨ffB0 fr, ffB0_le_ffP0 hQ fr, piOrth_mem_ffB0 fr, ?_, ?_, ?_,
    hH1 fr * t, hpP0, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun a ha b hb => ffB0_comm fr ha hb
  · exact fun a ha => ffB0_mul_self fr ha
  · rw [ffB0_card fr]; norm_num
  · rw [hpt, hH1_mul_self fr]
  · intro u hu
    rw [hpt]
    obtain ⟨K, -, rfl⟩ := (mem_ffB0_iff fr).mp hu
    rw [hH1]
    exact fr.signChange_comm {3, 4, 5} K
  · rw [hpt]; exact hH1_invDim fr
  · rw [hpt]; exact hH1_ne_one fr
  · rw [hpt]; exact hH1_ne_piOrth fr

private lemma po_translate_B (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1)
    {t : OGroup Q} {σ : Equiv.Perm (Fin 6)} {J : Finset (Fin 6)}
    (ht : t = fr.permOrth σ * fr.signChange J) (hσC : σ ∈ hMonoC)
    (hσnA : σ ∉ alternatingGroup (Fin 6)) (hJ : Even J.card) (h2 : t * t = 1) :
    ∃ U : Subgroup (OGroup Q), U ≤ ffP0 hQ fr ∧ piOrth Q ∈ U ∧
      (∀ a ∈ U, ∀ b ∈ U, a * b = b * a) ∧ (∀ a ∈ U, a * a = 1) ∧ Nat.card U = 2 ^ 5 ∧
      ∃ p ∈ ffP0 hQ fr, (p * t) * (p * t) = 1 ∧
        (∀ u ∈ U, (p * t) * u = u * (p * t)) ∧ invDim (p * t) = 3 ∧
        p * t ≠ 1 ∧ p * t ≠ piOrth Q := by
  have h45C : (Equiv.swap 4 5 : Equiv.Perm (Fin 6)) ∈ hMonoC := swap45_mem_hMonoC
  have hκC : Equiv.swap 4 5 * σ ∈ hMonoC := hMonoC.mul_mem h45C hσC
  have hsignσ : Equiv.Perm.sign σ = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · exact absurd (Equiv.Perm.mem_alternatingGroup.mpr h) hσnA
    · exact h
  have hsignκ : Equiv.Perm.sign (Equiv.swap 4 5 * σ) = 1 := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide : (4 : Fin 6) ≠ 5), hsignσ]
    decide
  have hκD : Equiv.swap 4 5 * σ ∈ monoD := by
    rw [monoD_eq_inf]
    exact Subgroup.mem_inf.mpr ⟨Equiv.Perm.mem_alternatingGroup.mpr hsignκ, hκC⟩
  have hpP0 : hH2 fr * t ∈ ffP0 hQ fr := by
    rw [ht, hH2, ffMono_mul fr (Equiv.swap 4 5) σ {1, 3} J]
    refine (mem_ffP0_iff hQ fr).mpr
      ⟨Equiv.swap 4 5 * σ, hκD, symmDiff (({1, 3} : Finset (Fin 6)).map σ⁻¹.toEmbedding) J, ?_,
        rfl⟩
    rw [Finset.even_card_symmDiff_iff, Finset.card_map]
    exact iff_of_true (by decide) hJ
  have hpt : (hH2 fr * t) * t = hH2 fr := by rw [mul_assoc, h2, mul_one]
  refine ⟨hU2 fr, hU2_le_ffP0 hQ fr, piOrth_mem_hU2 fr, ?_, ?_, ?_,
    hH2 fr * t, hpP0, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun a ha b hb => hU2_comm fr ha hb
  · exact fun a ha => hU2_mul_self fr ha
  · rw [hU2_card fr]; norm_num
  · rw [hpt, hH2_mul_self fr]
  · intro u hu
    rw [hpt]
    obtain ⟨κ, hκ, K, hK, rfl⟩ := (mem_hU2_iff fr).mp hu
    have h := hH2_comm_ffK0_ffF0 hκ hK
    rw [hH2, ffMono_mul fr (Equiv.swap 4 5) κ {1, 3} K,
      ffMono_mul fr κ (Equiv.swap 4 5) K {1, 3}, h.1, h.2]
  · rw [hpt]; exact hH2_invDim fr
  · rw [hpt]; exact hH2_ne_one fr
  · rw [hpt]; exact hH2_ne_piOrth fr

theorem po_translate (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1) {t : OGroup Q}
    (ht : t ∈ hPO fr) (h2 : t * t = 1) (hodd : Odd (invDim t)) :
    ∃ U : Subgroup (OGroup Q), U ≤ ffP0 hQ fr ∧ piOrth Q ∈ U ∧
      (∀ a ∈ U, ∀ b ∈ U, a * b = b * a) ∧ (∀ a ∈ U, a * a = 1) ∧ Nat.card U = 2 ^ 5 ∧
      ∃ p ∈ ffP0 hQ fr, (p * t) * (p * t) = 1 ∧ (∀ u ∈ U, (p * t) * u = u * (p * t)) ∧
        invDim (p * t) = 3 ∧ p * t ≠ 1 ∧ p * t ≠ piOrth Q := by
  obtain ⟨σ, hσC, J, rfl⟩ := (mem_hPO_iff fr).mp ht
  rcases mono_parity hQ fr h2 hodd with hA | hB
  · exact po_translate_A hQ fr rfl hσC hA.1 hA.2 h2
  · exact po_translate_B hQ fr rfl hσC hB.1 hB.2 h2

end CFSG.OddStandard.SmallF3.Omega
