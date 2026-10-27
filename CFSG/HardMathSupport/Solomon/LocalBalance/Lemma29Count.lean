module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Components

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type*} [Group G]

private theorem card_le_card_iInf_mul_pow_aux [Finite G] {B : Subgroup G}
    (hB : IsMulCommutative B) (K : Subgroup G → Subgroup G) :
    ∀ (n : ℕ) (T : Finset (Subgroup G)), T.card = n →
    (∀ J ∈ T, ∀ g ∈ B, GLBConj g J ∈ T) →
    (∀ J ∈ T, (Subgroup.normalizer (J : Set G)).relIndex B = 3) →
    (∀ J ∈ T, ∀ g ∈ B, K (GLBConj g J) = K J) →
    (∀ J ∈ T, (K J).relIndex B ≤ 27) →
    Nat.card B ≤ Nat.card ↥(B ⊓ ⨅ J ∈ T, K J) * 3 ^ n := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T hn hcl hidx hKconj hK27
  rcases T.eq_empty_or_nonempty with rfl | ⟨J, hJ⟩
  · simp at hn
    subst hn
    simp
  · obtain ⟨L₂, L₃, ⟨g₂, hg₂, hL₂⟩, ⟨g₃, hg₃, hL₃⟩, h12, h13, h23, hall⟩ :=
      exists_three_conjugates hB (hidx J hJ)
    set O : Finset (Subgroup G) := {J, L₂, L₃} with hO
    have hL₂T : L₂ ∈ T := hL₂ ▸ hcl J hJ g₂ hg₂
    have hL₃T : L₃ ∈ T := hL₃ ▸ hcl J hJ g₃ hg₃
    have hOT : O ⊆ T := by
      intro I hI
      simp only [hO, Finset.mem_insert, Finset.mem_singleton] at hI
      rcases hI with rfl | rfl | rfl <;> assumption
    have hOcard : O.card = 3 := Finset.card_eq_three.mpr ⟨J, L₂, L₃, h12, h13, h23, rfl⟩
    have horb : ∀ I, (∃ g ∈ B, I = GLBConj g J) → I ∈ O := by
      intro I hI
      simp only [hO, Finset.mem_insert, Finset.mem_singleton]
      exact hall I hI
    have hOorb : ∀ I ∈ O, ∃ g ∈ B, I = GLBConj g J := by
      intro I hI
      simp only [hO, Finset.mem_insert, Finset.mem_singleton] at hI
      rcases hI with rfl | rfl | rfl
      · exact ⟨1, B.one_mem, (gLBConj_one _).symm⟩
      · exact ⟨g₂, hg₂, hL₂⟩
      · exact ⟨g₃, hg₃, hL₃⟩
    set T' : Finset (Subgroup G) := T \ O with hT'
    have hT'sub : T' ⊆ T := Finset.sdiff_subset
    have hT'card : T'.card + 3 = n := by
      rw [hT', Finset.card_sdiff_of_subset hOT, hOcard, hn]
      have : 3 ≤ T.card := hOcard ▸ Finset.card_le_card hOT
      omega
    have hlt : T'.card < n := by omega
    have hcl' : ∀ I ∈ T', ∀ g ∈ B, GLBConj g I ∈ T' := by
      intro I hI g hg
      rw [hT', Finset.mem_sdiff] at hI ⊢
      refine ⟨hcl I hI.1 g hg, fun hmem => hI.2 ?_⟩
      obtain ⟨h, hh, hIh⟩ := hOorb _ hmem
      apply horb
      refine ⟨h * g⁻¹, B.mul_mem hh (B.inv_mem hg), ?_⟩
      rw [← gLBConj_gLBConj, ← hIh, gLBConj_inv_gLBConj]
    have hIH := ih T'.card hlt T' rfl hcl' (fun I hI => hidx I (hT'sub hI))
      (fun I hI => hKconj I (hT'sub hI)) (fun I hI => hK27 I (hT'sub hI))
    set B' : Subgroup G := B ⊓ ⨅ I ∈ T', K I with hB'
    have hKO : ∀ I ∈ O, K I = K J := by
      intro I hI
      obtain ⟨g, hg, rfl⟩ := hOorb I hI
      exact hKconj J hJ g hg
    have hle : B' ⊓ K J ≤ B ⊓ ⨅ I ∈ T, K I := by
      intro x hx
      refine ⟨hx.1.1, ?_⟩
      show x ∈ ⨅ I ∈ T, K I
      rw [Subgroup.mem_iInf]
      intro I
      rw [Subgroup.mem_iInf]
      intro hI
      by_cases hIO : I ∈ O
      · rw [hKO I hIO]; exact hx.2
      · have : I ∈ T' := by rw [hT', Finset.mem_sdiff]; exact ⟨hI, hIO⟩
        have h2 : x ∈ ⨅ I ∈ T', K I := hx.1.2
        rw [Subgroup.mem_iInf] at h2
        have h3 := h2 I
        rw [Subgroup.mem_iInf] at h3
        exact h3 this
    have hB'B : B' ≤ B := inf_le_left
    have hidx' : (K J).relIndex B' ≤ 27 := by
      have : (K J).FiniteIndex := Subgroup.finiteIndex_of_finite
      have : (K J).IsFiniteRelIndex B := Subgroup.isFiniteRelIndex_of_finiteIndex
      exact (Subgroup.relIndex_le_of_le_right hB'B Subgroup.relIndex_ne_zero).trans (hK27 J hJ)
    have h1 : Nat.card B' ≤ Nat.card ↥(B' ⊓ K J) * 27 := by
      rw [← Subgroup.relIndex_mul_card (H := K J) (K := B'), inf_comm, mul_comm]
      exact Nat.mul_le_mul_left _ hidx'
    have h2 : Nat.card ↥(B' ⊓ K J) ≤ Nat.card ↥(B ⊓ ⨅ I ∈ T, K I) :=
      Subgroup.card_le_of_le hle
    calc Nat.card B ≤ Nat.card B' * 3 ^ T'.card := hIH
      _ ≤ (Nat.card ↥(B ⊓ ⨅ I ∈ T, K I) * 27) * 3 ^ T'.card :=
          Nat.mul_le_mul_right _ (h1.trans (Nat.mul_le_mul_right _ h2))
      _ = Nat.card ↥(B ⊓ ⨅ I ∈ T, K I) * 3 ^ n := by
          rw [← hT'card, pow_add]; ring

theorem card_le_card_iInf_mul_pow [Finite G] {B : Subgroup G} (hB : IsMulCommutative B)
    (S : Set (Subgroup G)) (hS : S.Finite)
    (hcl : ∀ J ∈ S, ∀ g ∈ B, GLBConj g J ∈ S)
    (hidx : ∀ J ∈ S, (Subgroup.normalizer (J : Set G)).relIndex B = 3)
    (K : Subgroup G → Subgroup G) (hKB : ∀ J ∈ S, K J ≤ B)
    (hKconj : ∀ J ∈ S, ∀ g ∈ B, K (GLBConj g J) = K J)
    (hK27 : ∀ J ∈ S, (K J).relIndex B ≤ 27) :
    Nat.card B ≤ Nat.card ↥(B ⊓ ⨅ J ∈ S, K J) * 3 ^ hS.toFinset.card := by
  classical
  have h := card_le_card_iInf_mul_pow_aux hB K _ hS.toFinset rfl
    (fun J hJ g hg => by
      rw [Set.Finite.mem_toFinset] at hJ ⊢; exact hcl J hJ g hg)
    (fun J hJ => hidx J (by simpa using hJ))
    (fun J hJ => hKconj J (by simpa using hJ))
    (fun J hJ => hK27 J (by simpa using hJ))
  simpa using h

end CFSG.HardMathSupport.Solomon.LocalBalance
