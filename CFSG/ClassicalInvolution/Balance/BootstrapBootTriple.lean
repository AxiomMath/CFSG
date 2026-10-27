module

public import CFSG.ClassicalInvolution.Balance.BootstrapAuditFamily
public import CFSG.ClassicalInvolution.Balance.BootstrapDischarge
public import CFSG.ClassicalInvolution.Balance.BootstrapGeneration
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

section Family

@[expose] def frameFamily (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (A : Subgroup G) :
    Set (Subgroup G) :=
  {L | L ∈ Ω ∧ L ≤ Subgroup.centralizer (A : Set G) ∧ ∃ z ∈ A, IsClassicalMember p f L z}

@[expose] def FamilyMeetsAt (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (A : Subgroup G)
    (a : G) : Prop :=
  ∀ K ∈ centMembers Ω a, ∃ L ∈ frameFamily p f Ω A, InCommonComponent a K L

theorem exists_memberFamily_of_indepTriple (hp2 : p ≠ 2) (hf : 0 < f)
    (h : CoreAssembly.IndepTriple p f Ω) :
    ∃ A : Subgroup G, MemberFamily p f Ω A (frameFamily p f Ω A) := by
  obtain ⟨K, z, hK, hcomm, hel, hcard⟩ := h
  set A : Subgroup G := Subgroup.closure (Set.range z) with hA
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
    exact (Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.closure_le _).mpr hsub hx))
  have hmem : ∀ i, K i ∈ frameFamily p f Ω A := fun i =>
    ⟨(hK i).1, hKA i, z i, Subgroup.subset_closure ⟨i, rfl⟩, (hK i).2⟩
  refine ⟨A, ?_⟩
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
        · refine Subgroup.closure_mono ?_
          rintro _ ⟨i, rfl⟩
          exact ⟨K i, hmem i, (hK i).2⟩
        · rw [Subgroup.closure_le]
          rintro w ⟨L, ⟨-, -, z', hz'A, hz'⟩, hw⟩
          have : w = z' := hz'.eq_of_isCentralInvolution hp2 hf hw.isCentralInvolution
          rw [this]
          exact hz'A }

end Family

section Generation

theorem centralizerGenerationModOTwo_of_memberFamily (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (h27 : p ^ f ≠ 27) (h0 : ModelClauseZero) (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hmodel : LayerGenerationModel) {A : Subgroup G}
    {𝒦 : Set (Subgroup G)} (hM : MemberFamily p f Ω A 𝒦) {a : G} (ha : a ∈ A)
    (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G) : CentralizerGenerationModOTwo Ω A a := by
  have hcen : ∀ {K : Subgroup G}, K ≤ Subgroup.centralizer (A : Set G) →
      K ≤ Subgroup.centralizer ({a} : Set G) := fun hK =>
    hK.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
  have hAY : A ≤ centLayer Ω a := by
    rw [hM.generate, Subgroup.closure_le]
    rintro z ⟨K, hK, hz⟩
    obtain ⟨-, -, -, hKA⟩ := hM.involution K hK
    exact le_centLayer ⟨hM.subset hK, hcen hKA⟩ hz.mem
  exact centralizerGenerationModOTwo_of_model hp2 hq h27 h0 hA1 hΩ hIH hmodel hM.elem hM.card ha
    hnc hAY fun L hL g hg hgC y hy =>
      oddQuotMk_centralizes_of_memberFamily hM ha (Or.inr hL) hg hgC y hy

end Generation

section Stage2

theorem exactMembers_and_localOddCentral_of_frameFamily [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h9 : p ^ f ≠ 9)
    (h27 : p ^ f ≠ 27) (hΩ : InClass p f Ω)
    (hsingle : ∃ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hIH : LocalLieSystems p f Ω)
    (hmodel : LayerGenerationModel) (hconn : OmegaConnected Ω) {A : Subgroup G}
    (hM : MemberFamily p f Ω A (frameFamily p f Ω A))
    (hMF1 : ∀ a ∈ A, a ≠ 1 → ∀ D : LieSystemData p f (LocalQuot Ω a) (localFamily Ω a),
      SingleClassComponents p f D)
    (hcover : ∀ a ∈ A, IsFrameInvolution p f (frameFamily p f Ω A) a → FamilyMeetsAt p f Ω A a) :
    ExactMembers Ω ∧ ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z} := by
  obtain ⟨K₀, hK₀⟩ := hM.nonempty
  obtain ⟨z₀, -, hz₀, -⟩ := hM.involution K₀ hK₀
  exact exactMembers_and_localOddCentral_of_memberFamily_meets hnab hp2 hq h9 hΩ hsingle hIH hM
    hMF1
    (componentLayersAt_of_model hnab hp2 hq h27 ModelFacts.modelClauseZero hΩ hIH
      (fun x hx => by
        rw [← pow_two]
        exact hM.elem.2 x hx) hmodel)
    hconn
    (fun a ha hfa => centralizerGenerationModOTwo_of_memberFamily hp2 hq h27
      ModelFacts.modelClauseZero fundamentalWholeA1 hΩ hIH hmodel hM ha
      (by
        obtain ⟨K, -, hK⟩ := hfa
        exact not_subset_center_of_ne_one hnab hK.ne_one))
    hK₀ hz₀ hcover

end Stage2

section BootTriple

@[expose] def FrameMF1 (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z → CITBelowU p f (Nat.card G) →
      RouteD.DeltaConnected (CoreAssembly.conjClass K) → ∀ A : Subgroup G,
        MemberFamily p f (CoreAssembly.conjClass K) A
          (frameFamily p f (CoreAssembly.conjClass K) A) →
        ∀ a ∈ A, a ≠ 1 → ∀ D : LieSystemData p f (LocalQuot (CoreAssembly.conjClass K) a)
          (localFamily (CoreAssembly.conjClass K) a), SingleClassComponents p f D

@[expose] def FrameCoverage (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z → CITBelowU p f (Nat.card G) →
      RouteD.DeltaConnected (CoreAssembly.conjClass K) → ∀ A : Subgroup G,
        MemberFamily p f (CoreAssembly.conjClass K) A
          (frameFamily p f (CoreAssembly.conjClass K) A) →
        ∀ a ∈ A, IsFrameInvolution p f (frameFamily p f (CoreAssembly.conjClass K) A) a →
          FamilyMeetsAt p f (CoreAssembly.conjClass K) A a

theorem bootTriple_of_model (h9 : p ^ f ≠ 9) (h27 : p ^ f ≠ 27) (hmodel : LayerGenerationModel)
    (hMF1 : FrameMF1 p f) (hcover : FrameCoverage p f) : CoreAssembly.BootTriple p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hind
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  obtain ⟨A, hM⟩ := exists_memberFamily_of_indepTriple hp2 hf hind
  have hΩ : InClass p f (CoreAssembly.conjClass K) := inClass_conjugates hz
  obtain ⟨hex, hP1⟩ := exactMembers_and_localOddCentral_of_frameFamily hnab hp2 hq h9 h27 hΩ
    (CoreAssembly.exists_single_class K) (localLieSystems_of_citBelowU hΩ hBelow) hmodel
    (omegaConnected_of_deltaConnected hconn) hM
    (hMF1 G hnab K z hz hBelow hconn A hM)
    (hcover G hnab K z hz hBelow hconn A hM)
  exact ⟨hex, hP1 K (CoreAssembly.mem_conjClass_self K) z hz⟩

end BootTriple

end CFSG.ClassicalInvolution.Balance.Bootstrap
