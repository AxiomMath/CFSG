module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Cocode24Weight
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Cocode24Act

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance.Cocode24

open Equiv

@[expose] def ind (S : Finset (Fin 24)) : Word := fun i => if i ∈ S then 1 else 0

theorem ind_apply (S : Finset (Fin 24)) (i : Fin 24) : ind S i = if i ∈ S then 1 else 0 := rfl

theorem synd_ind (S : Finset (Fin 24)) : synd (ind S) = ∑ i ∈ S, col i := by
  rw [synd_apply]
  simp [ind, Finset.sum_ite_mem]

@[expose] def IsOctad (S : Finset (Fin 24)) : Prop := S.card = 8 ∧ ∑ i ∈ S, col i = 0

instance (S : Finset (Fin 24)) : Decidable (IsOctad S) := by
  unfold IsOctad
  infer_instance

theorem ind_mem_golay_iff (S : Finset (Fin 24)) : ind S ∈ golay ↔ ∑ i ∈ S, col i = 0 := by
  rw [golay, LinearMap.mem_ker, synd_ind]

theorem wt_ind_add_le (S T : Finset (Fin 24)) :
    wt (ind S + ind T) ≤ (S \ T).card + (T \ S).card := by
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le (S \ T) (T \ S))
  intro i hi
  rw [Finset.mem_filter] at hi
  obtain ⟨-, hi⟩ := hi
  simp only [Pi.add_apply, ind_apply] at hi
  rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff]
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T
  · exfalso
    apply hi
    simp only [hS, hT, ↓reduceIte]
    decide
  · exact Or.inl ⟨hS, hT⟩
  · exact Or.inr ⟨hT, hS⟩
  · exfalso
    apply hi
    simp only [hS, hT, ↓reduceIte]
    decide

theorem octad_inter_le {S T : Finset (Fin 24)} (hS : IsOctad S) (hT : IsOctad T) (hne : S ≠ T) :
    (S ∩ T).card ≤ 4 := by
  have hmem : ind S + ind T ∈ golay :=
    add_mem ((ind_mem_golay_iff S).2 hS.2) ((ind_mem_golay_iff T).2 hT.2)
  have h0 : ind S + ind T ≠ 0 := by
    intro h
    apply hne
    ext i
    have h1 := congrFun h i
    simp only [Pi.add_apply, Pi.zero_apply, ind_apply] at h1
    by_cases hS' : i ∈ S <;> by_cases hT' : i ∈ T
    · exact ⟨fun _ => hT', fun _ => hS'⟩
    · simp only [hS', hT', ↓reduceIte] at h1
      exact absurd h1 (by decide)
    · simp only [hS', hT', ↓reduceIte] at h1
      exact absurd h1 (by decide)
    · exact ⟨fun h => absurd h hS', fun h => absurd h hT'⟩
  have h8 := minDist hmem h0
  have h9 := wt_ind_add_le S T
  have hSc : S.card = 8 := hS.1
  have hTc : T.card = 8 := hT.1
  have h1 := Finset.card_sdiff_add_card_inter S T
  have h2 := Finset.card_sdiff_add_card_inter T S
  rw [Finset.inter_comm] at h2
  omega

theorem eq_of_five {S T F : Finset (Fin 24)} (hS : IsOctad S) (hT : IsOctad T) (hFS : F ⊆ S)
    (hFT : F ⊆ T) (hF : 5 ≤ F.card) : S = T := by
  by_contra hne
  have := octad_inter_le hS hT hne
  have h2 : F.card ≤ (S ∩ T).card := Finset.card_le_card (Finset.subset_inter hFS hFT)
  omega

theorem permW_ind (σ : Perm (Fin 24)) (S : Finset (Fin 24)) :
    permW σ (ind S) = ind (S.image σ) := by
  ext i
  simp only [permW_apply, ind_apply, Finset.mem_image]
  have : σ⁻¹ i ∈ S ↔ ∃ a ∈ S, σ a = i := by
    constructor
    · exact fun h => ⟨_, h, Equiv.apply_symm_apply _ _⟩
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
  simp only [this]

theorem image_isOctad {σ : Perm (Fin 24)} (hσ : σ ∈ aut) {S : Finset (Fin 24)} (hS : IsOctad S) :
    IsOctad (S.image σ) := by
  refine ⟨by rw [Finset.card_image_of_injective _ σ.injective, hS.1], ?_⟩
  have h1 : ind S ∈ golay := (ind_mem_golay_iff S).2 hS.2
  have h2 := (hσ (ind S)).2 h1
  rw [permW_ind, ind_mem_golay_iff] at h2
  exact h2

theorem image_eq_of_five {σ : Perm (Fin 24)} (hσ : σ ∈ aut) {S F : Finset (Fin 24)}
    (hS : IsOctad S) (hFS : F ⊆ S) (hF : 5 ≤ F.card) (hfix : ∀ x ∈ F, σ x = x) :
    S.image σ = S := by
  refine eq_of_five (image_isOctad hσ hS) hS (F := F) ?_ hFS hF
  intro x hx
  rw [Finset.mem_image]
  exact ⟨x, hFS hx, hfix x hx⟩

end CFSG.EvenSporadicStandard.Induction.Balance.Cocode24
