module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFOutSimTab

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem ffOut_sq_aux {H : Type} [Group H] {P : Subgroup H} {x c g : H} (hx : x * x = 1)
    (hxN : x ∈ normalizer (P : Set H)) (hcN : c ∈ normalizer (P : Set H)) (hg : g ∈ P)
    (hsq : (x * (c * g)) * (x * (c * g)) ∈ P) : (x * c * x) * c ∈ P := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hxgx : x * g * x ∈ P := by
    have h := (Subgroup.mem_normalizer_iff (H := P)).mp hxN g
    rw [hxinv] at h
    exact h.mp hg
  have hcx : c⁻¹ * (x * g * x) * c ∈ P := by
    have hcN' : c⁻¹ ∈ normalizer (P : Set H) := (normalizer (P : Set H)).inv_mem hcN
    have h := (Subgroup.mem_normalizer_iff (H := P)).mp hcN' (x * g * x)
    rw [inv_inv] at h
    exact h.mp hxgx
  have h2 : c⁻¹ * (x * g * x) * c * g ∈ P := P.mul_mem hcx hg
  have h3 : ((x * (c * g)) * (x * (c * g))) * (c⁻¹ * (x * g * x) * c * g)⁻¹ =
      x * c * x⁻¹ * c := by group
  have hid : (x * c * x) * c =
      ((x * (c * g)) * (x * (c * g))) * (c⁻¹ * (x * g * x) * c * g)⁻¹ := by
    rw [h3, hxinv]
  rw [hid]
  exact P.mul_mem hsq (P.inv_mem h2)

lemma ffOutClass_map_perm_mul (J : Finset (Fin 6)) (σ τ : Equiv.Perm (Fin 6)) :
    J.map (σ * τ).toEmbedding = (J.map τ.toEmbedding).map σ.toEmbedding := by
  ext i
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨j, hj, hji⟩
    exact ⟨τ j, ⟨j, hj, rfl⟩, hji⟩
  · rintro ⟨k, hk, hki⟩
    obtain ⟨j, hj, hjk⟩ := hk
    have hjk' : τ j = k := hjk
    exact ⟨j, hj, by
      show (σ * τ) j = i
      rw [Equiv.Perm.mul_apply, hjk']; exact hki⟩

lemma ffOutClass_map_one (J : Finset (Fin 6)) :
    J.map (1 : Equiv.Perm (Fin 6)).toEmbedding = J := by
  have h : (1 : Equiv.Perm (Fin 6)) = Equiv.refl (Fin 6) := rfl
  rw [h, Equiv.refl_toEmbedding, Finset.map_refl]

lemma ffOutClass_map_compl (σ : Equiv.Perm (Fin 6)) (J : Finset (Fin 6)) :
    (J.map σ.toEmbedding)ᶜ = Jᶜ.map σ.toEmbedding := by
  ext i
  simp only [Finset.mem_compl, Finset.mem_map]
  constructor
  · intro hi
    exact ⟨σ.symm i, fun hmem => hi ⟨σ.symm i, hmem, by simp⟩, by simp⟩
  · rintro ⟨j, hj, hji⟩ ⟨k, hk, hki⟩
    exact hj ((σ.injective (hki.trans hji.symm)) ▸ hk)

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma ffOutClass_beta_inv : ffBeta⁻¹ = ffBeta := by
  have h : ffBeta * ffBeta = 1 := by
    unfold ffBeta
    simpa using Equiv.Perm.swap_mul_self_mul 0 2 (1 : Equiv.Perm (Fin 6))
  exact inv_eq_of_mul_eq_one_right h

lemma ffOutClass_ffM_inv_mul (fr : NFrame Q (Fin 6) 1) (σ : Equiv.Perm (Fin 6))
    (K : Finset (Fin 6)) : (ffM fr σ ∅)⁻¹ * ffM fr σ K = ffM fr 1 K := by
  rw [ffM_inv, ffM_mul, inv_mul_cancel σ]
  simp only [Finset.map_empty]
  exact (ffM_eq_iff fr).mpr ⟨rfl,
    Or.inl (by ext i; simp [Finset.mem_symmDiff])⟩

private lemma ffOutClass_a_inv (fr : NFrame Q (Fin 6) 1) :
    (ffM fr 1 {0})⁻¹ = ffM fr 1 {0} := by
  rw [ffM_inv, inv_one, ffOutClass_map_one]

private lemma ffOutClass_b_inv (fr : NFrame Q (Fin 6) 1) :
    (ffM fr ffBeta ∅)⁻¹ = ffM fr ffBeta ∅ := by
  rw [ffM_inv, ffOutClass_beta_inv, Finset.map_empty]

private lemma ffOutClass_even_symmDiff {A K : Finset (Fin 6)} (hA : ¬ Even A.card)
    (hK : ¬ Even K.card) : Even (symmDiff A K).card := by
  rw [ffOut_even_symmDiff_iff]
  exact ⟨fun h => absurd h hA, fun h => absurd h hK⟩

lemma ffOutClass_conj_a (fr : NFrame Q (Fin 6) 1) :
    ffX0 fr * ffM fr 1 {0} * ffX0 fr = ffM fr ffBeta {0, 2} := by
  calc ffX0 fr * ffM fr 1 {0} * ffX0 fr
      = (ffX0 fr * ffM fr 1 {0}) * ffX0 fr := by group
    _ = (ffM fr ffBeta {0, 2} * ffX0 fr) * ffX0 fr := by rw [ffX0_conj_a fr]
    _ = ffM fr ffBeta {0, 2} * (ffX0 fr * ffX0 fr) := by group
    _ = ffM fr ffBeta {0, 2} := by rw [ffX0_mul_self fr, mul_one]

lemma ffOutClass_conj_b (fr : NFrame Q (Fin 6) 1) :
    ffX0 fr * ffM fr ffBeta ∅ * ffX0 fr = ffM fr 1 {2} := by
  calc ffX0 fr * ffM fr ffBeta ∅ * ffX0 fr
      = (ffX0 fr * ffM fr ffBeta ∅) * ffX0 fr := by group
    _ = (ffM fr 1 {2} * ffX0 fr) * ffX0 fr := by rw [ffX0_conj_b fr]
    _ = ffM fr 1 {2} * (ffX0 fr * ffX0 fr) := by group
    _ = ffM fr 1 {2} := by rw [ffX0_mul_self fr, mul_one]

lemma ffOutClass_a_mul (fr : NFrame Q (Fin 6) 1) :
    ffM fr ffBeta {0, 2} * ffM fr 1 {0} = ffM fr ffBeta {2} := by
  rw [ffM_mul, mul_one, inv_one, ffOutClass_map_one]
  exact (ffM_eq_iff fr).mpr ⟨rfl,
    Or.inl (show symmDiff ({0, 2} : Finset (Fin 6)) {0} = {2} from by decide)⟩

lemma ffOutClass_b_mul (fr : NFrame Q (Fin 6) 1) :
    ffM fr 1 {2} * ffM fr ffBeta ∅ = ffM fr ffBeta {0} := by
  rw [ffM_mul, one_mul]
  exact (ffM_eq_iff fr).mpr ⟨rfl,
    Or.inl (by rw [ffOutClass_beta_inv]; decide)⟩

theorem ff_N0_class (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1) {σ : Equiv.Perm (Fin 6)}
    (hσ : ∀ τ ∈ monoD, σ * τ * σ⁻¹ ∈ monoD) (K : Finset (Fin 6)) :
    ffM fr σ K ∈ ffPS hQ fr ∨ (ffM fr 1 {0})⁻¹ * ffM fr σ K ∈ ffPS hQ fr ∨
      (ffM fr ffBeta ∅)⁻¹ * ffM fr σ K ∈ ffPS hQ fr ∨
        (ffM fr ffRhoPerm ffRhoSet)⁻¹ * ffM fr σ K ∈ ffPS hQ fr := by
  rcases ff_normalizer_cases hσ with hD | hb
  · by_cases hK : Even K.card
    · exact Or.inl ((ffM_mem_ffPS_iff hQ fr σ K).mpr ⟨hD, hK⟩)
    · refine Or.inr (Or.inl ?_)
      rw [ffOutClass_a_inv, ffM_mul, one_mul]
      refine (ffM_mem_ffPS_iff hQ fr σ _).mpr ⟨hD, ?_⟩
      exact ffOutClass_even_symmDiff
        (by rw [Finset.card_map, Finset.card_singleton]; decide) hK
  · by_cases hK : Even K.card
    · refine Or.inr (Or.inr (Or.inl ?_))
      rw [ffOutClass_b_inv, ffM_mul, Finset.map_empty]
      refine (ffM_mem_ffPS_iff hQ fr (ffBeta * σ) _).mpr ⟨hb, ?_⟩
      rw [show symmDiff (∅ : Finset (Fin 6)) K = K from by ext i; simp [Finset.mem_symmDiff]]
      exact hK
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [ffM_inv, ffM_mul]
      refine (ffM_mem_ffPS_iff hQ fr (ffRhoPerm⁻¹ * σ) _).mpr
        ⟨ff_beta_coset ff_rho_coset hb, ?_⟩
      exact ffOutClass_even_symmDiff
        (by rw [Finset.card_map, Finset.card_map]; exact ff_rho_card) hK

end CFSG.OddStandard.SmallF3.Omega
