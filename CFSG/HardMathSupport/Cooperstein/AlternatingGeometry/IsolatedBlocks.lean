module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.Background.B2Factorization

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.Quasithin

variable {G : Type} [Group G] {S L : Subgroup G}

theorem exists_decomp_of_isolated_blocks {d : ℕ} (θ : ↥(L ⊔ S) →* Perm (Fin d)) {ι : Type*}
    [DecidableEq ι] (a a' : ι → Fin d)
    (hne : ∀ i, a i ≠ a' i)
    (hdisj : ∀ i j, i ≠ j → a i ≠ a j ∧ a i ≠ a' j ∧ a' i ≠ a j ∧ a' i ≠ a' j)
    (hJ : ∀ i, ∃ j : ↥(L ⊔ S), (j : G) ∈ thompsonJ S ∧ θ j = swap (a i) (a' i))
    (hS : ∀ s : ↥(L ⊔ S), (s : G) ∈ S → ∀ i,
      (θ s (a i) = a i ∨ θ s (a i) = a' i) ∧ (θ s (a' i) = a i ∨ θ s (a' i) = a' i))
    (B : Finset ι) (s : ↥(L ⊔ S)) (hs : (s : G) ∈ S) :
    ∃ j : ↥(L ⊔ S), (j : G) ∈ thompsonJ S ∧ ∃ δ : ↥(L ⊔ S), (δ : G) ∈ S ∧
      (∀ i ∈ B, θ δ (a i) = a i ∧ θ δ (a' i) = a' i) ∧ s = δ * j := by
  classical
  have hJS : thompsonJ S ≤ S := thompsonJ_le_self S
  induction B using Finset.induction_on generalizing s with
  | empty => exact ⟨1, (thompsonJ S).one_mem, s, hs, by simp, by simp⟩
  | insert b B hb ih =>
    obtain ⟨j₀, hj₀, δ₀, hδ₀, hfix, rfl⟩ := ih s hs
    obtain ⟨jb, hjb, hθjb⟩ := hJ b
    by_cases hflip : θ δ₀ (a b) = a b
    · refine ⟨j₀, hj₀, δ₀, hδ₀, ?_, rfl⟩
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hiB
      · refine ⟨hflip, ?_⟩
        rcases (hS δ₀ hδ₀ i).2 with h | h
        · exact absurd ((θ δ₀).injective (h.trans hflip.symm)).symm (hne i)
        · exact h
      · exact hfix i hiB
    · have hflip' : θ δ₀ (a b) = a' b := by
        rcases (hS δ₀ hδ₀ b).1 with h | h
        · exact absurd h hflip
        · exact h
      have hflip'' : θ δ₀ (a' b) = a b := by
        rcases (hS δ₀ hδ₀ b).2 with h | h
        · exact h
        · exact absurd ((θ δ₀).injective (h.trans hflip'.symm)) (hne b).symm
      refine ⟨jb * j₀, (thompsonJ S).mul_mem hjb hj₀, δ₀ * jb⁻¹,
        S.mul_mem hδ₀ (S.inv_mem (hJS hjb)), ?_, by simp [mul_assoc]⟩
      intro i hi
      have hθ : θ (δ₀ * jb⁻¹) = θ δ₀ * swap (a b) (a' b) := by
        rw [map_mul, map_inv, hθjb, swap_inv]
      rcases Finset.mem_insert.1 hi with rfl | hiB
      · rw [hθ, Perm.mul_apply, Perm.mul_apply, swap_apply_left, swap_apply_right, hflip', hflip'']
        exact ⟨rfl, rfl⟩
      · have hib : i ≠ b := fun h => hb (h ▸ hiB)
        obtain ⟨h1, h2, h3, h4⟩ := hdisj i b hib
        rw [hθ, Perm.mul_apply, Perm.mul_apply, swap_apply_of_ne_of_ne h1 h2,
          swap_apply_of_ne_of_ne h3 h4]
        exact hfix i hiB

theorem not_mem_normalizer_of_cycle {d : ℕ} (W : Subgroup (Perm (Fin d))) (hW : IsPGroup 2 W)
    {a₁ a₁' a₂ a₂' x : Fin d} (h12 : a₁ ≠ a₁') (h1 : a₂ ≠ a₂') (hd1 : a₁ ≠ a₂) (hd2 : a₁ ≠ a₂')
    (hd3 : a₁' ≠ a₂) (hd4 : a₁' ≠ a₂') (hx1 : x ≠ a₁) (hx2 : x ≠ a₂) (hx3 : x ≠ a₁')
    (hW1 : swap a₁ a₁' ∈ W) (hW2 : swap a₂ a₂' ∈ W) :
    swap a₁ a₂ * swap a₂ x ∉ Subgroup.normalizer (W : Set (Perm (Fin d))) := by
  intro hN
  have hc1 : (swap a₁ a₂ * swap a₂ x) a₁ = a₂ := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hd1 hx1.symm, swap_apply_left]
  have hc2 : (swap a₁ a₂ * swap a₂ x) a₁' = a₁' := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hd3 hx3.symm,
      swap_apply_of_ne_of_ne h12.symm hd3]
  have hconj : (swap a₁ a₂ * swap a₂ x) * swap a₁ a₁' * (swap a₁ a₂ * swap a₂ x)⁻¹ =
      swap a₂ a₁' := by
    rw [← Equiv.swap_apply_apply, hc1, hc2]
  have hmem : swap a₂ a₁' ∈ W := by
    have := (Subgroup.mem_normalizer_iff.1 hN _).1 hW1
    rwa [hconj] at this
  have hp : swap a₂ a₂' * swap a₂ a₁' ∈ W := W.mul_mem hW2 hmem
  have h3 : (swap a₂ a₂' * swap a₂ a₁').IsThreeCycle :=
    isThreeCycle_swap_mul_swap_same h1 (Ne.symm hd3) (Ne.symm hd4)
  obtain ⟨k, hk⟩ := hW ⟨_, hp⟩
  have hk' : (swap a₂ a₂' * swap a₂ a₁') ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hdvd : 3 ∣ 2 ^ k := by
    rw [← h3.orderOf]; exact orderOf_dvd_of_pow_eq_one hk'
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  omega

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
