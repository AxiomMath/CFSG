module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameStmt

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.ClassicalInvolution.Balance (oddCoreIn odd_card_oddCoreIn)

section Generation

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {A : Subgroup G}

theorem mem_normalizer_oddCoreIn_exactLayer (hΩ : ConjInvariant Ω) {a n : G}
    (hn : n ∈ Subgroup.centralizer ({a} : Set G)) :
    n ∈ Subgroup.normalizer (oddCoreIn (exactLayer Ω a) : Set G) :=
  CFSG.ClassicalInvolution.Balance.mem_normalizer_oddCoreIn_of_mem_normalizer
    (mem_normalizer_iff_conjSub_eq.mpr (conjSub_exactLayer hΩ hn))

theorem oddCoreIn_exactLayer_le_rankTwoSpan (hΩ : ConjInvariant Ω) (hA : IsElemAbelian 2 A)
    (h8 : 8 ≤ Nat.card A) {a : G} (ha : a ∈ A) :
    oddCoreIn (exactLayer Ω a) ≤ rankTwoSpan A := by
  have hnorm : A ≤ Subgroup.normalizer (oddCoreIn (exactLayer Ω a) : Set G) := fun g hg =>
    mem_normalizer_oddCoreIn_exactLayer hΩ
      (Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_mem_elemAbelian hA hg ha))
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two A (oddCoreIn (exactLayer Ω a)) hA (by simpa using h8) hnorm
    (Nat.coprime_two_left.mpr (odd_card_oddCoreIn _))
  conv_lhs => rw [← hgen]
  exact iSup₂_le fun F hF => le_rankTwoSpan_of_le_centralizer hF inf_le_right

theorem exactLayer_le_rankTwoSpan (hΩ : ConjInvariant Ω) (hA : IsElemAbelian 2 A)
    (h8 : 8 ≤ Nat.card A) {a : G} (ha : a ∈ A) (hgen : CentralizerGenerationStar Ω A a) :
    exactLayer Ω a ≤ rankTwoSpan A :=
  hgen.trans (sup_le (oddCoreIn_exactLayer_le_rankTwoSpan hΩ hA h8 ha)
    (iSup₂_le fun _ hF => le_rankTwoSpan_of_le_centralizer hF inf_le_left))

end Generation

section Closure

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {A : Subgroup G} {S : Set (Subgroup G)}

theorem mem_omegaStarTwo_of_dAdj_star (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hF : FrameSideTwoStar p f Ω A S) {L L' : Subgroup G} (hLs : L ∈ omegaStarTwo p f Ω A S)
    (hL' : L' ∈ Ω) (hadj : dAdj Ω L L') : L' ∈ omegaStarTwo p f Ω A S := by
  obtain ⟨hLΩ, h₀, hh₀, K, hKS, a, haA, hKa, hLa⟩ := hLs
  have hconj := hΩ.conjInvariant
  have hf : 0 < f := pos_of_five_le hq
  have hLa' := isClassicalMember_conj_inv hLa
  have hL₁Ω : conjSub h₀⁻¹ L ∈ Ω := hconj _ _ hLΩ
  have hMΩ : conjSub h₀⁻¹ L' ∈ Ω := hconj _ _ hL'
  have hadj' : dAdj Ω (conjSub h₀⁻¹ L) (conjSub h₀⁻¹ L') := by
    rcases hadj with h | h
    · exact Or.inl (Asc77.omegaNbr_conj hconj h h₀⁻¹)
    · exact Or.inr (Asc77.omegaNbr_conj hconj h h₀⁻¹)
  have hframe : IsFrameInvolution p f S a := ⟨K, hKS, hKa⟩
  have hYH := exactLayer_le_rankTwoSpan hconj hF.elem hF.card haA
    (hF.generation a haA hframe)
  obtain ⟨z₀, hz₀, hcond⟩ : ∃ z₀, IsClassicalMember p f (conjSub h₀⁻¹ L') z₀ ∧
      (ActsTrivOnQuot (conjSub h₀⁻¹ L') a ∨ ∃ L₂ ∈ Ω, IsClassicalMember p f L₂ a ∧
        ActsTrivOnQuot L₂ z₀) := by
    rcases hadj' with h | h
    · obtain ⟨a', ha', hMa'⟩ := tq_of_mem_omegaNbr hp2 hq hΩ.classical hL₁Ω h
      have e : a = a' := ha'.eq_of_isCentralInvolution hp2 hf hLa'.isCentralInvolution
      rw [← e] at hMa'
      obtain ⟨z₀, hz₀⟩ := hΩ.classical _ hMΩ
      exact ⟨z₀, hz₀, Or.inl hMa'⟩
    · obtain ⟨a'', ha'', hL₁a''⟩ := tq_of_mem_omegaNbr hp2 hq hΩ.classical hMΩ h
      exact ⟨a'', ha'', Or.inr ⟨conjSub h₀⁻¹ L, hL₁Ω, hLa', hL₁a''⟩⟩
  obtain ⟨K', hK'S, z', hz'A, hK'z', h₁, hh₁Y, hz₀h₁⟩ :=
    hF.link a haA hframe _ hMΩ z₀ hz₀ hcond
  have hz₀' : IsClassicalMember p f (conjSub h₀⁻¹ L') (h₁ * z' * h₁⁻¹) := by rwa [← hz₀h₁]
  have hL'z : IsClassicalMember p f L' (h₀ * (h₁ * z' * h₁⁻¹) * h₀⁻¹) := by
    have := hz₀'.conj h₀
    rwa [conjSub_conjSub_inv] at this
  refine ⟨hL', h₀ * h₁, mul_mem hh₀ (hYH hh₁Y), K', hK'S, z', hz'A, hK'z', ?_⟩
  have e : h₀ * h₁ * z' * (h₀ * h₁)⁻¹ = h₀ * (h₁ * z' * h₁⁻¹) * h₀⁻¹ := by group
  rwa [e]

theorem le_rankTwoSpan_of_mem_omegaStarTwo_star (hΩ : InClass p f Ω)
    (hF : FrameSideTwoStar p f Ω A S) {L : Subgroup G} (hLs : L ∈ omegaStarTwo p f Ω A S) :
    L ≤ rankTwoSpan A := by
  obtain ⟨hLΩ, h, hh, K, hK, a, haA, hKa, hLa⟩ := hLs
  have hconj := hΩ.conjInvariant
  have hLa' := isClassicalMember_conj_inv hLa
  have hmem : conjSub h⁻¹ L ∈ centralizingMembers Ω {a} :=
    ⟨hconj _ _ hLΩ, le_centralizer hLa'⟩
  have hY : conjSub h⁻¹ L ≤ exactLayer Ω a :=
    (le_centralizingLayer hmem).trans (centLayer_le_exactLayer (fun M hM => hΩ.classical M hM))
  have hY' : conjSub h⁻¹ L ≤ rankTwoSpan A :=
    hY.trans (exactLayer_le_rankTwoSpan hconj hF.elem hF.card haA
      (hF.generation a haA ⟨K, hK, hKa⟩))
  intro x hx
  have h1 : h⁻¹ * x * h ∈ conjSub h⁻¹ L := by
    rw [mem_conjSub_iff]
    simpa [mul_assoc] using hx
  have h2 := hY' h1
  have h3 : x = h * (h⁻¹ * x * h) * h⁻¹ := by group
  rw [h3]
  exact mul_mem (mul_mem hh h2) (inv_mem hh)

theorem mem_omegaStarTwo_of_dConnected_star (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hF : FrameSideTwoStar p f Ω A S) (hconn : DConnected Ω) {L : Subgroup G} (hLΩ : L ∈ Ω) :
    L ∈ omegaStarTwo p f Ω A S := by
  obtain ⟨K₀, hK₀⟩ := hF.nonempty
  obtain ⟨z, hzA, hz⟩ := hF.involution K₀ hK₀
  have hK₀s : K₀ ∈ omegaStarTwo p f Ω A S :=
    ⟨hF.subset hK₀, 1, one_mem _, K₀, hK₀, z, hzA, hz, by simpa using hz⟩
  have key : ∀ L', Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ dAdj Ω M N) K₀ L' →
      L' ∈ omegaStarTwo p f Ω A S := by
    intro L' hpath
    induction hpath with
    | refl => exact hK₀s
    | tail _ hbc ih => exact mem_omegaStarTwo_of_dAdj_star hp2 hq hΩ hF ih hbc.1 hbc.2
  exact key L (hconn K₀ (hF.subset hK₀) L hLΩ)

theorem rankTwoSpan_eq_top_of_dConnected_star (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hF : FrameSideTwoStar p f Ω A S) (hconn : DConnected Ω) :
    rankTwoSpan A = ⊤ := by
  refine top_unique ?_
  rw [← hΩ.generated]
  exact iSup₂_le fun _ hLΩ => le_rankTwoSpan_of_mem_omegaStarTwo_star hΩ hF
    (mem_omegaStarTwo_of_dConnected_star hp2 hq hΩ hF hconn hLΩ)

end Closure

end CFSG.ClassicalInvolution.Asc77
