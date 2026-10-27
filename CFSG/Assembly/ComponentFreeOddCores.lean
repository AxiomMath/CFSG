module

public import CFSG.Assembly.CompletedOddCoreElimination
public import CFSG.Assembly.BalancedOddCoreCompletion

public section

namespace CFSG.Assembly.Dichotomy

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem orderOf_eq_two_of_isElemAbelian {A : Subgroup G} (hA : IsElemAbelian 2 A) {a : G}
    (ha : a ∈ A) (hne : a ≠ 1) : orderOf a = 2 :=
  orderOf_eq_prime (hA.2 a ha) hne

theorem involutionOddCore_balance (hcomp : ¬ IsComponentType G) {A : Subgroup G}
    (hA : IsElemAbelian 2 A) {a b : G} (ha : a ∈ A) (ha1 : a ≠ 1) (hb : b ∈ A) (hb1 : b ≠ 1) :
    involutionOddCore a ⊓ Subgroup.centralizer ({b} : Set G) ≤ involutionOddCore b := by
  have hab : Commute a b :=
    congrArg Subtype.val (hA.1.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩)
  have h := component_free_oddCore_balance G hcomp a b (orderOf_eq_two_of_isElemAbelian hA ha ha1)
    (orderOf_eq_two_of_isElemAbelian hA hb hb1) hab
  change involutionOddCore a ⊓ _ = involutionOddCore b ⊓ _ at h
  rw [h]
  exact inf_le_left

theorem oddCoreSpanCompleted_of_componentFree (hcomp : ¬ IsComponentType G) (A : Subgroup G)
    (hA : IsElemAbelian 2 A) (hcard : 8 ≤ Nat.card A) : OddCoreSpanCompleted A :=
  (balanced_oddCoreSpan_completed A hA hcard fun _ ha ha1 _ hb hb1 =>
    involutionOddCore_balance hcomp hA ha ha1 hb hb1).1

omit [Finite G] in
theorem commutator_eq_top_of_isSimpleGroup [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) :
    commutator G = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · obtain ⟨a, b, hab⟩ := hnonab
    exact absurd (by
      have hmem : a * b * a⁻¹ * b⁻¹ ∈ commutator G := by
        rw [commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot] at hmem
      have := mul_inv_eq_one.mp hmem
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this) hab
  · exact h

theorem oddCore_eq_bot_of_isSimpleGroup [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) :
    oddCore G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (oddCore G) with h | h
  · exact h
  · exfalso
    have hodd : Odd (Nat.card G) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hc := (CFSG.pPrimeCore_coprime_card (p := 2) (G := G))
      rw [← oddCore_eq_pPrimeCore, h, Subgroup.card_top] at hc
      exact Nat.coprime_two_left.mp hc
    have hsolv := CFSG.Milestones.odd_order_solvable hodd
    have hperf := commutator_eq_top_of_isSimpleGroup hnonab
    obtain ⟨n, hn⟩ := hsolv.solvable
    have hder : ∀ m, derivedSeries G m = ⊤ := by
      intro m
      induction m with
      | zero => exact derivedSeries_zero G
      | succ m ih => rw [derivedSeries_succ, ih, ← commutator_def, hperf]
    rw [hder] at hn
    obtain ⟨a, b, hab⟩ := hnonab
    have ha : a = 1 := by
      have : a ∈ (⊤ : Subgroup G) := Subgroup.mem_top a
      rw [hn, Subgroup.mem_bot] at this
      exact this
    exact hab (by rw [ha, one_mul, mul_one])

theorem component_free_oddCore_eq_bot_of_steps (hcov : PerfectInvolutionCoverageStatement)
    (hprep : CompletedSpanPreparationStatement) (hcent : CentralInvolutionCentralizerStatement)
    (hfus : FusionControlStatement) (heq : FourSpanEqualizationStatement)
    (hemb : CommonSpanStrongEmbeddingStatement) [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hrank : 3 ≤ twoRank G)
    (hcomp : ¬ IsComponentType G) (hse : ∀ M : Subgroup G, ¬ dichotomyStronglyEmbedded M)
    (t : G) (ht : orderOf t = 2) :
    oddCore (Subgroup.centralizer ({t} : Set G)) = ⊥ :=
  oddCore_centralizer_eq_bot_of_steps hcov hprep hcent hfus heq hemb
    (commutator_eq_top_of_isSimpleGroup hnonab) (oddCore_eq_bot_of_isSimpleGroup hnonab) hrank
    hcomp hse (fun D hD hD8 => oddCoreSpanCompleted_of_componentFree hcomp D hD hD8.ge) t ht

end CFSG.Assembly.Dichotomy
