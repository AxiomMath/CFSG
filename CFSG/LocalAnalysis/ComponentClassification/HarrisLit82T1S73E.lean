module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RO
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S73Sq

public section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup QuadraticMap CliffordAlgebra CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K]

theorem mul_self_eq_one_of_mem_ker_spinAction (h2 : (2 : K) ≠ 0) {x : spinGroup (quadOdd 3 K)}
    (hx : x ∈ (spinAction (quadOdd 3 K)).ker) : x * x = 1 := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  rcases (mem_ker_spinAction_iff _ (nondegenerate_quadOdd 3 K) x).mp hx with rfl | rfl
  · exact mul_one 1
  · exact spinGroup.negOne_mul_self _ _

theorem commute_spinJ₂_spinJ₃_odd [Finite K] (hodd : Odd (Nat.card K))
    {a b : spinGroup (quadOdd 3 K)} (ha : a ∈ spinJ₂ K) (hb : b ∈ spinJ₃ K) : a * b = b * a := by
  have hle : spinJ₂ K ≤ centralizer {b} := by
    refine le_centralizer_of_mul_self (range_le_closure_mul_self_sl2 hodd _) fun a' ha' => ?_
    have hk : ⁅a', b⁆ ∈ (spinAction (quadOdd 3 K)).ker := by
      obtain ⟨A, rfl⟩ := ha'
      obtain ⟨B, rfl⟩ := hb
      rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv,
        spinAction_longSL2, spinAction_longSL2,
        show (oddFrame 3 K).toHypFrame.toFrame fin3_zero_ne_one true false = (frame01 K).swap from
          toFrame_not _ fin3_zero_ne_one true true, Frame.La_comm_La_swap]
      group
    exact ⟨ker_spinAction_le_center _ hk, mul_self_eq_one_of_mem_ker_spinAction
      (CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd) hk⟩
  exact mem_centralizer_singleton_iff.mp (hle ha)

theorem commute_spinMul₁₂_spinJ₃_odd [Finite K] (hodd : Odd (Nat.card K))
    (x : spinJ₁ K × spinJ₂ K) (c : spinJ₃ K) :
    Commute (spinMul₁₂ K x) ((spinJ₃ K).subtype c) := by
  change (x.1 : spinGroup (quadOdd 3 K)) * x.2 * c = c * (x.1 * x.2)
  rw [mul_assoc, commute_spinJ₂_spinJ₃_odd hodd x.2.2 c.2, ← mul_assoc,
    commute_spinJ₁_spinJ₃ x.1.2 c.2, mul_assoc]

@[expose] noncomputable def spinMulOdd [Finite K] (hodd : Odd (Nat.card K)) :
    (spinJ₁ K × spinJ₂ K) × spinJ₃ K →* spinGroup (quadOdd 3 K) :=
  MonoidHom.noncommCoprod (spinMul₁₂ K) (spinJ₃ K).subtype (commute_spinMul₁₂_spinJ₃_odd hodd)

theorem spinMulOdd_apply [Finite K] (hodd : Odd (Nat.card K))
    (x : (spinJ₁ K × spinJ₂ K) × spinJ₃ K) :
    spinMulOdd hodd x = (x.1.1 : spinGroup (quadOdd 3 K)) * x.1.2 * x.2 :=
  rfl

theorem range_spinMulOdd [Finite K] (hodd : Odd (Nat.card K)) :
    (spinMulOdd hodd).range = spinE K := by
  refine le_antisymm ?_ (sup_le (sup_le ?_ ?_) ?_)
  · rintro _ ⟨x, rfl⟩
    rw [spinMulOdd_apply]
    exact mul_mem (mul_mem (mem_sup_left (mem_sup_left x.1.1.2))
      (mem_sup_left (mem_sup_right x.1.2.2))) (mem_sup_right x.2.2)
  · intro a ha
    exact ⟨((⟨a, ha⟩, 1), 1), by rw [spinMulOdd_apply]; simp⟩
  · intro b hb
    exact ⟨((1, ⟨b, hb⟩), 1), by rw [spinMulOdd_apply]; simp⟩
  · intro c hc
    exact ⟨((1, 1), ⟨c, hc⟩), by rw [spinMulOdd_apply]; simp⟩

section Centres

variable [Finite K] (hodd : Odd (Nat.card K))
include hodd

theorem mem_zpowers_of_commute_spinJ₁_odd {a : spinGroup (quadOdd 3 K)} (ha : a ∈ spinJ₁ K)
    (hc : ∀ a' ∈ spinJ₁ K, a * a' = a' * a) :
    a ∈ zpowers (spinGroup.negOne (quadOdd 3 K) (nondegenerate_quadOdd 3 K).ne_zero) := by
  rw [← shortSeven_neg_one, ← map_center_range_sl2_odd hodd _ injective_shortSeven]
  refine ⟨⟨a, ha⟩, mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
  exact (hc y y.2).symm

theorem mem_zpowers_of_commute_spinJ₂_odd {b : spinGroup (quadOdd 3 K)} (hb : b ∈ spinJ₂ K)
    (hc : ∀ b' ∈ spinJ₂ K, b * b' = b' * b) : b ∈ zpowers (tSeven K) := by
  rw [← map_center_range_sl2_odd hodd _ (longSL2_injective _ fin3_zero_ne_one true true)]
  refine ⟨⟨b, hb⟩, mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
  exact (hc y y.2).symm

theorem mem_zpowers_of_commute_spinJ₃_odd {c : spinGroup (quadOdd 3 K)} (hc3 : c ∈ spinJ₃ K)
    (hc : ∀ c' ∈ spinJ₃ K, c * c' = c' * c) :
    c ∈ zpowers ((oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false (-1)) := by
  rw [← map_center_range_sl2_odd hodd _ (longSL2_injective _ fin3_zero_ne_one true false)]
  refine ⟨⟨c, hc3⟩, mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
  exact (hc y y.2).symm

end Centres

section Card

variable [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
include hp hp2 hK

omit [Field K] [Finite K] in
theorem odd_card_spin : Odd (Nat.card K) :=
  hK ▸ (hp.odd_of_ne_two hp2).pow

theorem mem_ker_spinMulOdd_iff (x : (spinJ₁ K × spinJ₂ K) × spinJ₃ K) :
    x ∈ (spinMulOdd (odd_card_spin hp hp2 hK)).ker ↔
      x = 1 ∨ x = ((⟨spinZ K, (spinZ_facts hp hp2 hK).2.2.2.2.2.2.1⟩,
        ⟨tSeven K, (spinZ_facts hp hp2 hK).2.2.2.2.2.2.2.1⟩),
        ⟨spinZ K * tSeven K, (spinZ_facts hp hp2 hK).2.2.2.2.2.2.2.2.1⟩) := by
  have hodd := odd_card_spin hp hp2 hK
  obtain ⟨hzz, hz1, hzc, htt, ht1, htc, -, -, -, h3eq⟩ := spinZ_facts hp hp2 hK
  have hzcomm : ∀ g : spinGroup (quadOdd 3 K), spinZ K * g = g * spinZ K := fun g =>
    (mem_center_iff.mp hzc g).symm
  have htz : tSeven K ≠ spinZ K := fun h => htc (h ▸ hzc)
  rw [MonoidHom.mem_ker, spinMulOdd_apply]
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, ⟨c, hc⟩⟩ := x
  constructor
  · intro habc
    change a * b * c = 1 at habc
    have hac : ∀ a' ∈ spinJ₁ K, a * a' = a' * a := by
      intro a' ha'
      have hbc : a = (b * c)⁻¹ := by rw [eq_inv_iff_mul_eq_one, ← mul_assoc, habc]
      rw [hbc, mul_inv_rev]
      calc c⁻¹ * b⁻¹ * a' = c⁻¹ * (b⁻¹ * a') := mul_assoc _ _ _
        _ = c⁻¹ * (a' * b⁻¹) := by
          rw [commute_spinJ₁_spinJ₂ ha' (inv_mem hb)]
        _ = a' * (c⁻¹ * b⁻¹) := by
          rw [← mul_assoc, ← commute_spinJ₁_spinJ₃ ha' (inv_mem hc), mul_assoc]
    have hbb : ∀ b' ∈ spinJ₂ K, b * b' = b' * b := by
      intro b' hb'
      have hbeq : b = a⁻¹ * c⁻¹ := by
        rw [← mul_inv_rev, eq_inv_iff_mul_eq_one, ← mul_assoc]
        rw [show b * c * a = a⁻¹ * (a * b * c) * a by group, habc]
        group
      rw [hbeq]
      calc a⁻¹ * c⁻¹ * b' = a⁻¹ * (c⁻¹ * b') := mul_assoc _ _ _
        _ = a⁻¹ * (b' * c⁻¹) := by
          rw [← commute_spinJ₂_spinJ₃_odd hodd hb' (inv_mem hc)]
        _ = b' * (a⁻¹ * c⁻¹) := by
          rw [← mul_assoc, commute_spinJ₁_spinJ₂ (inv_mem ha) hb', mul_assoc]
    have hcc : ∀ c' ∈ spinJ₃ K, c * c' = c' * c := by
      intro c' hc'
      have hceq : c = (a * b)⁻¹ := eq_inv_of_mul_eq_one_right habc
      rw [hceq, mul_inv_rev]
      calc b⁻¹ * a⁻¹ * c' = b⁻¹ * (a⁻¹ * c') := mul_assoc _ _ _
        _ = b⁻¹ * (c' * a⁻¹) := by
          rw [commute_spinJ₁_spinJ₃ (inv_mem ha) hc']
        _ = c' * (b⁻¹ * a⁻¹) := by
          rw [← mul_assoc, commute_spinJ₂_spinJ₃_odd hodd (inv_mem hb) hc', mul_assoc]
    have hztzt : spinZ K * tSeven K * (spinZ K * tSeven K) = 1 := by
      rw [mul_assoc, ← mul_assoc (tSeven K), ← hzcomm, mul_assoc, htt, mul_one, hzz]
    have h1 := eq_one_or_eq_of_mem_zpowers_of_mul_self hzz
      (mem_zpowers_of_commute_spinJ₁_odd hodd ha hac)
    have h2 := eq_one_or_eq_of_mem_zpowers_of_mul_self htt
      (mem_zpowers_of_commute_spinJ₂_odd hodd hb hbb)
    have h3 := eq_one_or_eq_of_mem_zpowers_of_mul_self hztzt
      (h3eq ▸ mem_zpowers_of_commute_spinJ₃_odd hodd hc hcc)
    rcases eq_of_mul_mul_eq_one hzz hz1 hzcomm htt ht1 htz h1 h2 h3 habc with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · left; rfl
    · right; rfl
  · rintro (h | h)
    · rw [h]
      simp
    · rw [h]
      change spinZ K * tSeven K * (spinZ K * tSeven K) = 1
      rw [mul_assoc, ← mul_assoc (tSeven K), ← hzcomm, mul_assoc, htt, mul_one, hzz]

end Card

end CFSG.ComponentClassification.HarrisLit.T1
