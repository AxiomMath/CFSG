module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.ElementaryPerm

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T2A7Loc

open Equiv Subgroup CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

theorem card_support_of_odd_involution {σ : Perm (Fin 9)} (h2 : σ * σ = 1)
    (hs : Perm.sign σ = -1) : σ.support.card = 2 ∨ σ.support.card = 6 := by
  have h1 : σ ≠ 1 := by
    rintro rfl
    simp at hs
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact h2) h1
  obtain ⟨n, hn⟩ := Perm.cycleType_prime_order (σ := σ) (by rw [hord]; exact Nat.prime_two)
  rw [hord] at hn
  have hsupp : σ.support.card = 2 * (n + 1) := by
    rw [← Perm.sum_cycleType, hn, Multiset.sum_replicate, smul_eq_mul, mul_comm]
  have hsign := Perm.sign_of_cycleType σ
  rw [hn, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul, hs] at hsign
  have hle : σ.support.card ≤ 9 := (Finset.card_le_univ _).trans (by simp)
  have hn4 : n ≤ 3 := by omega
  interval_cases n
  · exact Or.inl hsupp
  · exact absurd hsign (by decide)
  · exact Or.inr hsupp
  · exact absurd hsign (by decide)

theorem false_of_odd_involution_commute {F : Subgroup (alternatingGroup (Fin 9))}
    (hF : IsPGroup 2 F) (hcyc : ∀ g ∈ F, g ≠ 1 → (g : Perm (Fin 9)).cycleType = {2, 2, 2, 2})
    (h3 : 2 < Nat.card F) {σ : Perm (Fin 9)} (h2 : σ * σ = 1) (hs : Perm.sign σ = -1)
    (hcomm : ∀ g ∈ F, (g : Perm (Fin 9)) * σ = σ * g) : False := by
  classical
  obtain ⟨p, hp⟩ := exists_forall_apply_eq_of_isPGroup hF
  have huniq : ∀ g ∈ F, g ≠ 1 → ∀ i, (g : Perm (Fin 9)) i = i → i = p := fun g hg hg1 i hi =>
    eq_of_apply_eq_of_cycleType_two_two_two_two (hcyc g hg hg1) hi (hp g hg)
  have happ : ∀ g ∈ F, ∀ i, (g : Perm (Fin 9)) (σ i) = σ ((g : Perm (Fin 9)) i) := fun g hg i => by
    have := congrArg (fun τ : Perm (Fin 9) => τ i) (hcomm g hg)
    simpa only [Perm.mul_apply] using this
  obtain ⟨g₀, hg₀, hg₀1⟩ : ∃ g ∈ F, g ≠ 1 := by
    by_contra h
    have hbot : F = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      by_contra hg1
      exact h ⟨g, hg, hg1⟩
    rw [hbot, card_bot] at h3
    omega
  have hσp : σ p = p := huniq g₀ hg₀ hg₀1 (σ p) (by rw [happ g₀ hg₀, hp g₀ hg₀])
  have hne : ∀ g ∈ F, ∀ i, i ≠ p → (g : Perm (Fin 9)) i ≠ p := fun g hg i hi h =>
    hi ((g : Perm (Fin 9)).injective (h.trans (hp g hg).symm))
  obtain ⟨T, hT2, hTp, hTF⟩ : ∃ T : Finset (Fin 9), T.card = 2 ∧ p ∉ T ∧
      ∀ g ∈ F, ∀ i ∈ T, (g : Perm (Fin 9)) i ∈ T := by
    rcases card_support_of_odd_involution h2 hs with hc | hc
    · refine ⟨σ.support, hc, by rw [Perm.mem_support, not_not]; exact hσp, ?_⟩
      intro g hg i hi
      rw [Perm.mem_support] at hi ⊢
      intro h
      apply hi
      apply (g : Perm (Fin 9)).injective
      rw [happ g hg, h]
    · have hpc : p ∈ σ.supportᶜ := by
        rw [Finset.mem_compl, Perm.mem_support, not_not]
        exact hσp
      refine ⟨σ.supportᶜ.erase p, ?_, Finset.notMem_erase p _, ?_⟩
      · rw [Finset.card_erase_of_mem hpc, Finset.card_compl, hc]
        simp
      · intro g hg i hi
        obtain ⟨hip, hi⟩ := Finset.mem_erase.mp hi
        rw [Finset.mem_compl, Perm.mem_support, not_not] at hi
        refine Finset.mem_erase.mpr ⟨hne g hg i hip, ?_⟩
        rw [Finset.mem_compl, Perm.mem_support, not_not, ← happ g hg, hi]
  obtain ⟨i, hi⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
  have hip : i ≠ p := fun h => hTp (h ▸ hi)
  let φ : ↥F → ↥T := fun g => ⟨(g : Perm (Fin 9)) i, hTF g g.2 i hi⟩
  have hinj : Function.Injective φ := by
    intro g h hgh
    have hgh' : ((g : alternatingGroup (Fin 9)) : Perm (Fin 9)) i =
        ((h : alternatingGroup (Fin 9)) : Perm (Fin 9)) i := congrArg Subtype.val hgh
    by_contra hne'
    have hk : (h : alternatingGroup (Fin 9))⁻¹ * g ∈ F := F.mul_mem (F.inv_mem h.2) g.2
    have hk1 : (h : alternatingGroup (Fin 9))⁻¹ * g ≠ 1 := fun h1 =>
      hne' (Subtype.ext (inv_mul_eq_one.mp h1).symm)
    apply hip
    apply huniq _ hk hk1 i
    simp only [coe_mul, coe_inv, Perm.mul_apply, hgh']
    simp
  have hcard := Nat.card_le_card_of_injective φ hinj
  rw [Nat.card_eq_fintype_card (α := ↥T), Fintype.card_coe, hT2] at hcard
  omega

end CFSG.GH74.Generic.BProg.B3.S3T2A7Loc
