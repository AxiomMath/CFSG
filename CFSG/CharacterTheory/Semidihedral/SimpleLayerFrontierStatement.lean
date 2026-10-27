module

public import CFSG.CharacterTheory.Semidihedral.CentralizerStructure
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.FourPointBranchClassification
public import CFSG.CharacterTheory.Semidihedral.PerfectLayerNormalization

public section

namespace CFSG.Semidihedral.SimpleLayerFrontier

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage

@[expose] def FrontierConclusion (G : Type) [Group G] : Prop :=
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 3 ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 3 p f) ∨
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ p ^ f % 4 = 1 ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSU 3 p f) ∨
  Nonempty (G ≃* CFSG.Assembly.LowTwoRank.StatedM11)

@[expose] def FrontierAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (n : ℕ), 4 ≤ n → ∀ (S0 : Sylow 2 G), (SemidihedralGroup n ≃* S0) →
    ∀ (t : G), orderOf t = 2 →
    ∀ [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))],
    (∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a) →
    Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥ →
    ∀ (m : ℕ), 2 ≤ m → m ≤ n - 2 →
    ∀ (U : Sylow 2 (CFSG.generalizedFitting (Gamma t))),
      Nonempty (U ≃* DihedralGroup (2 ^ (m - 1))) → FrontierConclusion G

@[expose] def FrontierStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G], FrontierAt G

theorem odd_normal_eq_bot_of_simple {A : Type} [Group A] [Finite A] [IsSimpleGroup A]
    (k : ℕ) (hk : 4 ≤ k) (S : Sylow 2 A) (f : SemidihedralGroup k ≃* S) :
    ∀ K : Subgroup A, K.Normal → Odd (Nat.card K) → K = ⊥ := by
  intro K hK hKodd
  rcases hK.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hz : orderOf (f (z k)) = 2 := by
      rw [MulEquiv.orderOf_eq]
      exact CFSG.Semidihedral.orderOf_z k (by omega)
    have h2 : 2 ∣ Nat.card A := by
      rw [← hz, ← Subgroup.orderOf_coe]
      exact orderOf_dvd_natCard _
    rw [h, Subgroup.card_top] at hKodd
    exact (Nat.not_even_iff_odd.mpr hKodd) (even_iff_two_dvd.mpr h2)

theorem smaller_simple_model_of_frontierAt
    {A : Type} [Group A] [Finite A] [IsSimpleGroup A]
    (hnonab : ∃ a b : A, a * b ≠ b * a) (k : ℕ) (hk : 4 ≤ k) (S : Sylow 2 A)
    (hS : Nonempty (SemidihedralGroup k ≃* S)) (hfront : FrontierAt A) :
    ProperSubgroupRegularity.SmallerSimpleModel A := by
  obtain ⟨f⟩ := hS
  have hA : ∀ V : Subgroup A, V.index ≠ 2 :=
    CFSG.Semidihedral.Principal.index_ne_two_of_isSimpleGroup hnonab
  have hodd := odd_normal_eq_bot_of_simple k hk S f
  have ht : orderOf (CentralizerResidual.centeredInvolution k S f) = 2 := by
    rw [← CentralizerResidual.centralInvolution_order k hk S f, Subgroup.orderOf_mk]
    rfl
  rcases CentralizerStructure.centered_structural_alternatives k hk S f hA with hfour | hlayer
  · obtain ⟨-, φ, -⟩ := hfour
    obtain ⟨-, -, -, -, hxor⟩ :=
      GL2Recognition.four_point_reduced_centralizer_branch_classification hA hodd k hk S f
        (CentralizerResidual.centeredInvolution k S f) ht φ
    rcases hxor with ⟨⟨-, hpsl⟩, -⟩ | ⟨⟨-, -, hm11⟩, -⟩
    · exact Or.inl ⟨3, 1, Nat.prime_three, by decide, le_rfl, by norm_num, hpsl⟩
    · exact Or.inr (Or.inr hm11)
  · obtain ⟨hsimple, hLnonab, -, hcentral, hSylow, -, -⟩ := hlayer
    let : IsSimpleGroup (CFSG.generalizedFitting
        (Gamma (CentralizerResidual.centeredInvolution k S f))) := hsimple
    let U : Sylow 2 (CFSG.generalizedFitting
        (Gamma (CentralizerResidual.centeredInvolution k S f))) := Classical.choice Sylow.nonempty
    obtain ⟨m, hm, hmk, hU⟩ := hSylow U
    rcases hfront hnonab k hk S f (CentralizerResidual.centeredInvolution k S f) ht hLnonab
        hcentral m hm hmk U hU with
      ⟨p, f', hp, hp2, hf', hmod, hmodel⟩ | ⟨p, f', hp, hp2, hf', hmod, hmodel⟩ | hm11
    · exact Or.inl ⟨p, f', hp, hp.odd_of_ne_two hp2, hf', hmod, hmodel⟩
    · exact Or.inr (Or.inl ⟨p, f', hp, hp.odd_of_ne_two hp2, hf', hmod, hmodel⟩)
    · exact Or.inr (Or.inr hm11)

theorem smaller_simple_recognition_of_frontier_below
    (G : Type) [Group G] [Finite G]
    (hbelow : ∀ (A : Type) [Group A] [Finite A], Nat.card A < Nat.card G → FrontierAt A) :
    ProperSubgroupRegularity.SmallerSimpleRecognition G := by
  intro A _ _ _ hnonab hcard k hk S hS
  exact smaller_simple_model_of_frontierAt hnonab k hk S hS (hbelow A hcard)

theorem original_smaller_simple_recognition_of_frontier_below
    (G : Type) [Group G] [Finite G]
    (hbelow : ∀ (A : Type) [Group A] [Finite A], Nat.card A < Nat.card G → FrontierAt A) :
    PerfectLayerNormalization.OriginalSmallerSimpleRecognition G := by
  intro A _ _ _ hnonab hcard k hk S hS
  exact smaller_simple_model_of_frontierAt hnonab k hk S hS (hbelow A hcard)

theorem frontier_of_inductive_step
    (hstep : ∀ (G : Type) [Group G] [Finite G],
      ProperSubgroupRegularity.SmallerSimpleRecognition G → FrontierAt G) :
    FrontierStatement := by
  suffices h : ∀ (k : ℕ) (G : Type) [Group G] [Finite G], Nat.card G = k → FrontierAt G by
    intro G _ _
    exact h _ G rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro G _ _ hk
    apply hstep G
    apply smaller_simple_recognition_of_frontier_below G
    intro A _ _ hA
    exact ih (Nat.card A) (hk ▸ hA) A rfl

theorem semidihedral_simple_model_of_frontier
    (hfront : FrontierStatement)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G) (hS : Nonempty (SemidihedralGroup n ≃* S)) :
    ProperSubgroupRegularity.SmallerSimpleModel G :=
  smaller_simple_model_of_frontierAt hnonab n hn S hS (hfront G)

end CFSG.Semidihedral.SimpleLayerFrontier
