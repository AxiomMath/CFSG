module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.DatumSup
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.AGLEmbeddingD2

section Generic

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem isCyclic_sylow_of_not_sq_dvd (hp : p.Prime) (T : Sylow p K) (h : ¬ p ^ 2 ∣ Nat.card K) :
    IsCyclic (T : Subgroup K) := by
  have : Fact p.Prime := ⟨hp⟩
  have hf : (Nat.card K).factorization p ≤ 1 := by
    by_contra hlt
    push Not at hlt
    exact h ((hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').2 hlt)
  refine isCyclic_of_card_dvd_prime (p := p) ?_
  have hT : Nat.card (T : Subgroup K) = p ^ (Nat.card K).factorization p :=
    Sylow.card_eq_multiplicity T
  rw [hT]
  exact (pow_dvd_pow p hf).trans (dvd_of_eq (pow_one p))

theorem exists_plane_of_not_isCyclic (hp : p.Prime) (hp2 : p ≠ 2) (T : Sylow p K)
    (hT : ¬ IsCyclic (T : Subgroup K)) :
    ∃ A : Subgroup K, A ≤ (T : Subgroup K) ∧ IsElemAbelian p A ∧ Nat.card A = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (IsPGroup p (T : Subgroup K)) := ⟨T.isPGroup'⟩
  obtain ⟨S, -, hcard, hel⟩ := CFSG.lemma_4_5_a hp2 hT
  refine ⟨S.map (T : Subgroup K).subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · have : IsElementaryAbelian p S := hel
    exact (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mp
      IsElementaryAbelian.map_subtype
  · rw [Subgroup.card_map_of_injective (T : Subgroup K).subtype_injective, hcard]

theorem false_of_d2DatumPlus (hp : p.Prime) (hp2 : p ≠ 2) (h : D2IndexDatumPlus K p)
    (T : Sylow p K) (hT : ¬ IsCyclic (T : Subgroup K))
    (hΓ : GLBCore p 1 (T : Subgroup K) ≠ ⊤) (hr : Open.pRank p (⊤ : Subgroup K) ≤ 2) : False := by
  rcases h with ⟨-, hd⟩ | ⟨-, hsup⟩
  · rcases hd with h2 | h3 | ⟨-, hfus⟩ | hcore
    · exact hT (isCyclic_sylow_of_not_sq_dvd hp T h2)
    · omega
    · exact hΓ (glbCore_one_eq_top_of_fusionGenerationOf hp hfus T)
    · have h := glbCore_anti p (k := 1) (l := 2) (by norm_num) (T : Subgroup K)
      rw [hcore T] at h
      exact hΓ (top_le_iff.mp h)
  · obtain ⟨A, hAT, hel, hcard⟩ := exists_plane_of_not_isCyclic hp hp2 T hT
    have h := hsup T A hAT hel hcard
    have h2 : GLBCore p 2 (T : Subgroup K) ⊔ GLBCore p 1 A ≤ GLBCore p 1 (T : Subgroup K) :=
      sup_le (glbCore_anti p (k := 1) (l := 2) (by norm_num) _) (glbCore_mono p 1 hAT)
    rw [h] at h2
    exact hΓ (top_le_iff.mp h2)

end Generic

end CFSG.AGLEmbedding
