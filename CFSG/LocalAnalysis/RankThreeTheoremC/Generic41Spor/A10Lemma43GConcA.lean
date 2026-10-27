module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GConcDefs
import all CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GConcDefs
import all CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Perm

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

namespace A10Perm

open Equiv Equiv.Perm Subgroup

theorem a10t1_ca_mem_L1 (σ : A10) :
    σ ∈ L1 ↔ ∀ i : Fin 10, 5 ≤ (i : ℕ) → (σ : Perm (Fin 10)) i = i := Iff.rfl

theorem a10t1_ca_mem_L2 (σ : A10) :
    σ ∈ L2 ↔ ∀ i : Fin 10, (i : ℕ) < 5 → (σ : Perm (Fin 10)) i = i := Iff.rfl

theorem a10t1_ca_iso_of_support (L : Subgroup A10) (s : Finset (Fin 10)) (hs : s.card = 5)
    (hL : ∀ σ : A10, σ ∈ L ↔ (σ : Perm (Fin 10)).support ⊆ s) :
    Nonempty (↥L ≃* alternatingGroup (Fin 5)) := by
  have hrange : L = (alternatingGroup.ofSubtype s).range := by
    ext σ
    rw [hL, alternatingGroup.mem_range_ofSubtype_iff]
  subst hrange
  exact ⟨(MonoidHom.ofInjective (alternatingGroup.ofSubtype_injective (s := s))).symm.trans
    (Equiv.altCongrHom (Finset.equivFinOfCardEq hs))⟩

theorem L1_iso : Nonempty (↥L1 ≃* alternatingGroup (Fin 5)) := by
  refine a10t1_ca_iso_of_support L1 (Finset.univ.filter fun i : Fin 10 => (i : ℕ) < 5)
    (by decide) ?_
  intro σ
  rw [a10t1_ca_mem_L1]
  constructor
  · intro h i hi
    rw [Equiv.Perm.mem_support] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hlt
    exact hi (h i (not_lt.1 hlt))
  · intro h i hi
    by_contra hne
    have := h ((Equiv.Perm.mem_support).2 hne)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    omega

theorem L2_iso : Nonempty (↥L2 ≃* alternatingGroup (Fin 5)) := by
  refine a10t1_ca_iso_of_support L2 (Finset.univ.filter fun i : Fin 10 => 5 ≤ (i : ℕ))
    (by decide) ?_
  intro σ
  rw [a10t1_ca_mem_L2]
  constructor
  · intro h i hi
    rw [Equiv.Perm.mem_support] at hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hlt
    exact hi (h i (not_le.1 hlt))
  · intro h i hi
    by_contra hne
    have := h ((Equiv.Perm.mem_support).2 hne)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    omega

theorem L1_comm_L2 : ∀ a ∈ L1, ∀ b ∈ L2, a * b = b * a := by
  intro a ha b hb
  have hdisj : Equiv.Perm.Disjoint (a : Perm (Fin 10)) (b : Perm (Fin 10)) := by
    intro i
    by_cases hi : 5 ≤ (i : ℕ)
    · exact Or.inl ((a10t1_ca_mem_L1 a).1 ha i hi)
    · exact Or.inr ((a10t1_ca_mem_L2 b).1 hb i (not_le.1 hi))
  exact Subtype.ext hdisj.commute.eq

theorem L1_inf_L2 : L1 ⊓ L2 = ⊥ := by
  rw [eq_bot_iff]
  rintro σ ⟨h1, h2⟩
  rw [Subgroup.mem_bot]
  refine Subtype.ext (Equiv.ext fun i => ?_)
  by_cases hi : 5 ≤ (i : ℕ)
  · exact (a10t1_ca_mem_L1 σ).1 h1 i hi
  · exact (a10t1_ca_mem_L2 σ).1 h2 i (not_le.1 hi)

theorem a10t1_ca_a₁_mem_L1 : a₁ ∈ L1 := by
  rw [a10t1_ca_mem_L1]; decide +kernel

theorem a10t1_ca_a₂_mem_L2 : a₂ ∈ L2 := by
  rw [a10t1_ca_mem_L2]; decide +kernel

theorem S₀_inf_L1 : S₀ ⊓ L1 = line₁ := by
  apply le_antisymm
  · rintro x ⟨hxS, hxL⟩
    obtain ⟨i, j, rfl⟩ := mem_S₀.1 hxS
    have hi := pow_eq_pow_mod i a₁_pow
    have hj := pow_eq_pow_mod j a₂_pow
    have key : ∀ u v : Fin 5,
        ((a₁ ^ (u : ℕ) * a₂ ^ (v : ℕ) : A10) : Perm (Fin 10)) 5 = 5 → v = 0 := by
      decide +kernel
    have h5 := (a10t1_ca_mem_L1 _).1 hxL 5 (by decide)
    rw [hi, hj] at h5
    have hv := key ⟨i % 5, Nat.mod_lt _ (by norm_num)⟩ ⟨j % 5, Nat.mod_lt _ (by norm_num)⟩ h5
    have hj0 : j % 5 = 0 := by simpa [Fin.ext_iff] using hv
    have h1 : a₂ ^ j = 1 := by rw [hj, hj0, pow_zero]
    rw [h1, mul_one]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers a₁) i
  · exact le_inf line₁_le (Subgroup.zpowers_le.2 a10t1_ca_a₁_mem_L1)

theorem S₀_inf_L2 : S₀ ⊓ L2 = line₂ := by
  apply le_antisymm
  · rintro x ⟨hxS, hxL⟩
    obtain ⟨i, j, rfl⟩ := mem_S₀.1 hxS
    have hi := pow_eq_pow_mod i a₁_pow
    have hj := pow_eq_pow_mod j a₂_pow
    have key : ∀ u v : Fin 5,
        ((a₁ ^ (u : ℕ) * a₂ ^ (v : ℕ) : A10) : Perm (Fin 10)) 0 = 0 → u = 0 := by
      decide +kernel
    have h0 := (a10t1_ca_mem_L2 _).1 hxL 0 (by decide)
    rw [hi, hj] at h0
    have hu := key ⟨i % 5, Nat.mod_lt _ (by norm_num)⟩ ⟨j % 5, Nat.mod_lt _ (by norm_num)⟩ h0
    have hi0 : i % 5 = 0 := by simpa [Fin.ext_iff] using hu
    have h1 : a₁ ^ i = 1 := by rw [hi, hi0, pow_zero]
    rw [h1, one_mul]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers a₂) j
  · exact le_inf line₂_le (Subgroup.zpowers_le.2 a10t1_ca_a₂_mem_L2)

end A10Perm

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
