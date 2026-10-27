module

public import CFSG.ClassicalInvolution.Balance.Theorem5Core
public import CFSG.ClassicalInvolution.Balance.BootstrapInvolutory
public import CFSG.ClassicalInvolution.Balance.LayerGenerationTriple
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Balance.Theorem5

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance.Bootstrap

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)}

section Frames

omit [Group G] in
@[expose] def triangleFrames (p f : ℕ) [Fact p.Prime] {G : Type} [Group G]
    (Ω : Set (Subgroup G)) : Set (Subgroup G) :=
  {A | IndepTripleOn p f Ω A}

theorem memberFamily_of_indepTripleOn [Finite G] (hp2 : p ≠ 2) (hf : 0 < f) {A : Subgroup G}
    (h : IndepTripleOn p f Ω A) : MemberFamily p f Ω A (frameFamily p f Ω A) := by
  obtain ⟨K, z, hK, hcomm, hAdef, hel, hcard⟩ := h
  have hc : ∀ i, IsCentralInvolution (K i) (z i) := fun i => (hK i).2.isCentralInvolution
  have hKA : ∀ i, K i ≤ Subgroup.centralizer (A : Set G) := by
    intro i k hk
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hsub : Set.range z ⊆ ((Subgroup.centralizer ({k} : Set G) : Subgroup G) : Set G) := by
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      by_cases hij : i = j
      · subst hij
        exact (hc i).central k hk
      · exact (hcomm i j hij k hk (z j) (hc j).mem).symm
    rw [hAdef] at hx
    exact (Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.closure_le _).mpr hsub hx))
  have hmem : ∀ i, K i ∈ frameFamily p f Ω A := fun i =>
    ⟨(hK i).1, hKA i, z i, hAdef ▸ Subgroup.subset_closure ⟨i, rfl⟩, (hK i).2⟩
  exact
    { elem := hel
      card := hcard
      subset := fun L hL => hL.1
      nonempty := ⟨K 0, hmem 0⟩
      involution := fun L hL => by
        obtain ⟨-, hLA, z', hz'A, hz'⟩ := hL
        exact ⟨z', hz'A, hz', hLA⟩
      generate := by
        apply le_antisymm
        · calc A = Subgroup.closure (Set.range z) := hAdef
            _ ≤ _ := by
              refine Subgroup.closure_mono ?_
              rintro _ ⟨i, rfl⟩
              exact ⟨K i, hmem i, (hK i).2⟩
        · rw [Subgroup.closure_le]
          rintro w ⟨L, ⟨-, -, z', hz'A, hz'⟩, hw⟩
          have : w = z' := hz'.eq_of_isCentralInvolution hp2 hf hw.isCentralInvolution
          rw [this]
          exact hz'A }

theorem indepTripleOn_map (hΩ : ConjInvariant Ω) {A : Subgroup G} (h : IndepTripleOn p f Ω A)
    (g : G) : IndepTripleOn p f Ω (A.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨K, z, hK, hcomm, hAdef, hel, hcard⟩ := h
  refine ⟨fun i => conjSub g (K i), fun i => g * z i * g⁻¹, fun i => ⟨hΩ g _ (hK i).1,
    (hK i).2.conj g⟩, ?_, ?_, ?_, ?_⟩
  · intro i j hij x hx y hy
    have hx' := mem_conjSub_iff.mp hx
    have hy' := mem_conjSub_iff.mp hy
    have h1 := hcomm i j hij _ hx' _ hy'
    have h2 : g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ =
        g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
    simpa [mul_assoc] using h2
  · rw [hAdef, MonoidHom.map_closure]
    congr 1
    ext w
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨z i, ⟨i, rfl⟩, rfl⟩
  · exact isElemAbelian_two_map hel g
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hcard

end Frames

section Balance

variable [Finite G]

theorem rankThreeBalance_of_indepTripleOn_of_layers [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hf : 0 < f) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω) {A : Subgroup G}
    (hA : IndepTripleOn p f Ω A) (hloc : ∀ a ∈ A, a ≠ 1 → ComponentLayersAt Ω A a) :
    RankThreeBalance A := by
  have hM := memberFamily_of_indepTripleOn hp2 hf hA
  exact ⟨hM.elem, hM.card, weakBalanced_of_memberFamily hnab hp2 hq ModelFacts.modelClauseZero
    fundamentalWholeA1 hΩ hIH hM, twoBalancedWrt_of_memberFamily_of_layers hM hloc⟩

theorem rankThreeBalance_of_indepTripleOn [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hf : 0 < f) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω) (hmodel : LayerGenerationInvolutoryModel)
    {A : Subgroup G} (hA : IndepTripleOn p f Ω A)
    (hF3 : ∀ a ∈ A, a ≠ 1 → NoComponentOverF3 p f Ω a) : RankThreeBalance A :=
  rankThreeBalance_of_indepTripleOn_of_layers hnab hp2 hf hq hΩ hIH hA
    (componentLayersAt_of_involutoryModel_of_noF3 hnab hp2 hq ModelFacts.modelClauseZero hΩ hIH
      (memberFamily_of_indepTripleOn hp2 hf hA) hmodel hF3)

omit [Finite G] in
@[expose] def TriangleConnected (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) : Prop :=
  ∀ A ∈ triangleFrames p f Ω, ∀ A' ∈ triangleFrames p f Ω,
    Relation.ReflTransGen
      (fun X Y => X ∈ triangleFrames p f Ω ∧ Y ∈ triangleFrames p f Ω ∧ ShareFour X Y) A A'

theorem deltaCore_eq_bot_of_connected_triangleFamily [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hf : 0 < f) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω) (hmodel : LayerGenerationInvolutoryModel)
    (hF3 : ∀ A, IndepTripleOn p f Ω A → ∀ a ∈ A, a ≠ 1 → NoComponentOverF3 p f Ω a)
    {𝒯 : Set (Subgroup G)} (hsub : 𝒯 ⊆ triangleFrames p f Ω)
    (hinv : ∀ A ∈ 𝒯, ∀ g : G, A.map (MulAut.conj g).toMonoidHom ∈ 𝒯)
    (hconn : ∀ A ∈ 𝒯, ∀ A' ∈ 𝒯,
      Relation.ReflTransGen (fun X Y => X ∈ 𝒯 ∧ Y ∈ 𝒯 ∧ ShareFour X Y) A A') :
    ∀ A ∈ 𝒯, ∀ F ∈ signalizerFunctorEk 2 2 A, deltaCore F = ⊥ :=
  deltaCore_eq_bot_of_connected_frames (𝒯 := 𝒯)
    (componentClassificationOddCore_eq_bot_of_simple hnab) hinv
    (fun A hA => rankThreeBalance_of_indepTripleOn hnab hp2 hf hq hΩ hIH hmodel (hsub hA)
      (hF3 A (hsub hA))) hconn

theorem deltaCore_eq_bot_of_triangleConnected [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hf : 0 < f) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω) (hmodel : LayerGenerationInvolutoryModel)
    (hF3 : ∀ A, IndepTripleOn p f Ω A → ∀ a ∈ A, a ≠ 1 → NoComponentOverF3 p f Ω a)
    (htri : TriangleConnected p f Ω) :
    ∀ A, IndepTripleOn p f Ω A → ∀ F ∈ signalizerFunctorEk 2 2 A, deltaCore F = ⊥ :=
  fun A hA => deltaCore_eq_bot_of_connected_triangleFamily hnab hp2 hf hq hΩ hIH hmodel hF3
    (𝒯 := triangleFrames p f Ω) (fun _ h => h)
    (fun _ hA g => indepTripleOn_map hΩ.conjInvariant hA g) htri A hA

end Balance

end CFSG.ClassicalInvolution.Balance.Theorem5
