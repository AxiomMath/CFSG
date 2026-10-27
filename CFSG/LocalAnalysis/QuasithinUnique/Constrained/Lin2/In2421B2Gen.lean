module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InTorus

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

section Gen2

variable {G : Type*} [Group G]

theorem conjR_commutator (X Y : Subgroup G) (h : G) :
    conjR ⁅X, Y⁆ h = ⁅conjR X h, conjR Y h⁆ := by
  simp only [conjR_def]
  exact (Subgroup.map_commutator _ _ _)

theorem commutator_le_of_relIndex_dvd_four [Finite G] {T N : Subgroup G}
    (hN : T ≤ Subgroup.normalizer (N : Set G)) (h : N.relIndex T ∣ 4) :
    ⁅T, T⁆ ≤ N := by
  have hnorm : (N.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (↥T ⧸ N.subgroupOf T) = N.relIndex T := by
    rw [← Subgroup.index_eq_card]
    rfl
  have hcomm : ∀ a b : ↥T ⧸ N.subgroupOf T, a * b = b * a := by
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (by simpa using h : N.relIndex T ∣ 2 ^ 2)
    interval_cases k
    · have h1 : Nat.card (↥T ⧸ N.subgroupOf T) = 1 := by rw [hcard, hk']; rfl
      intro a b
      have : Subsingleton (↥T ⧸ N.subgroupOf T) := (Nat.card_eq_one_iff_unique.1 h1).1
      exact Subsingleton.elim _ _
    · have h2 : Nat.card (↥T ⧸ N.subgroupOf T) = 2 := by rw [hcard, hk']; rfl
      have : IsCyclic (↥T ⧸ N.subgroupOf T) := isCyclic_of_prime_card (p := 2) h2
      let _ : CommGroup (↥T ⧸ N.subgroupOf T) := IsCyclic.commGroup
      exact fun a b => mul_comm a b
    · have h4 : Nat.card (↥T ⧸ N.subgroupOf T) = 2 ^ 2 := by rw [hcard, hk']
      exact fun a b => (IsPGroup.isMulCommutative_of_card_eq_prime_sq h4).is_comm.comm a b
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have h1 := hcomm (QuotientGroup.mk' (N.subgroupOf T) (⟨x, hx⟩ : T))
    (QuotientGroup.mk' (N.subgroupOf T) (⟨y, hy⟩ : T))
  have h2 : (⁅(⟨x, hx⟩ : T), (⟨y, hy⟩ : T)⁆ : T) ∈ N.subgroupOf T := by
    rw [← QuotientGroup.eq_one_iff]
    have : (QuotientGroup.mk ⁅(⟨x, hx⟩ : T), (⟨y, hy⟩ : T)⁆ : ↥T ⧸ N.subgroupOf T) = 1 := by
      have := map_commutatorElement (QuotientGroup.mk' (N.subgroupOf T)) (⟨x, hx⟩ : T)
        (⟨y, hy⟩ : T)
      rw [commutatorElement_eq_one_iff_mul_comm.2 h1] at this
      exact this
    exact this
  rw [Subgroup.mem_subgroupOf] at h2
  simpa [commutatorElement_def] using h2

theorem one_lt_card_inf_of_relIndex_two [Finite G] {E S₁ T₁ : Subgroup G} (hET : E ≤ T₁)
    (h2 : S₁.relIndex T₁ = 2) (hcard : 2 < Nat.card E) :
    1 < Nat.card (E ⊓ S₁ : Subgroup G) := by
  have h1 : S₁.relIndex E ≤ 2 := by
    have := Subgroup.relIndex_le_of_le_right (H := S₁) hET (by rw [h2]; norm_num)
    omega
  have h3 : (E ⊓ S₁ : Subgroup G).relIndex E = S₁.relIndex E := by
    have := Subgroup.inf_relIndex_right S₁ E
    rwa [inf_comm] at this
  have h4 : Nat.card E = Nat.card (E ⊓ S₁ : Subgroup G) * S₁.relIndex E := by
    rw [← h3]
    exact card_eq_mul_of_relIndex (inf_le_left : E ⊓ S₁ ≤ E)
  have h5 : Nat.card E ≤ Nat.card (E ⊓ S₁ : Subgroup G) * 2 := by
    rw [h4]; exact Nat.mul_le_mul_left _ h1
  omega

end Gen2

section Field4

theorem ringEquiv_apply_apply_of_card_four {K : Type} [Field K] [Fintype K]
    (hcard : Fintype.card K = 4) (σ : K ≃+* K) (v : K) : σ (σ v) = v := by
  classical
  have h2 : (2 : K) = 0 := two_eq_zero_of_card (F := K) (n := 2) (by norm_num) (by rw [hcard]; norm_num)
  have h11 : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two]; exact h2
  obtain ⟨ω, hω0, hω1⟩ : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hs : Function.Surjective (fun b : Bool => if b then (1 : K) else 0) := by
      intro y
      by_cases hy : y = 0
      · exact ⟨false, by simp [hy]⟩
      · exact ⟨true, by simp [hcon y hy]⟩
    have := Fintype.card_le_of_surjective _ hs
    rw [hcard] at this
    simp at this
  have hs0 : ω + 1 ≠ 0 := by
    intro h
    apply hω1
    have : ω = -1 := eq_neg_of_add_eq_zero_left h
    rw [this]; exact neg_eq_of_add_eq_zero_left h11
  have hs1 : ω + 1 ≠ 1 := fun h => hω0 (by simp at h; exact h)
  have hsω : ω + 1 ≠ ω := fun h => by simp at h
  let f : Fin 4 → K := ![0, 1, ω, ω + 1]
  have hinj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢ <;>
      first | exact absurd hij.symm (by assumption) | exact absurd hij (by assumption)
  have hsurj : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj, by simp [hcard]⟩).2
  have hσω : σ ω = ω ∨ σ ω = ω + 1 := by
    obtain ⟨i, hi⟩ := hsurj (σ ω)
    fin_cases i <;> simp [f] at hi
    · exact absurd (σ.injective (by rw [← hi, map_zero])) hω0
    · exact absurd (σ.injective (by rw [← hi, map_one])) hω1
    · exact Or.inl hi.symm
    · exact Or.inr hi.symm
  have key : σ (σ ω) = ω := by
    rcases hσω with h | h
    · rw [h, h]
    · rw [h, map_add, map_one, h, add_assoc, h11, add_zero]
  obtain ⟨i, rfl⟩ := hsurj v
  fin_cases i <;> simp [f, map_add, key]

end Field4

end CFSG.QuasithinUnique.Lin2
