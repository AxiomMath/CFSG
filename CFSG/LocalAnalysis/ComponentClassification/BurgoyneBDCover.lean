module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBCover
public import CFSG.LieType.Steinberg.CentralExt.SpinMinusCenter
public import CFSG.LieType.Steinberg.CentralExt.OrthogonalPerfect

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.B

open CFSG Subgroup CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
open CFSG.LieType.Steinberg.CentralExt

theorem center_hyps_of_isCyclic {G : Type*} [Group G] [Finite G] (hcyc : IsCyclic (center G))
    (hcard : Nat.card (center G) ∣ 4) {g : G} (hg : g ∈ center G) (hg2 : orderOf g = 2) :
    (∀ z ∈ center G, z ^ 2 = 1 ∨ z ^ 2 = g) ∧ (∀ z ∈ center G, z ^ 2 = 1 → z = 1 ∨ z = g) := by
  classical
  have : Fintype (center G) := Fintype.ofFinite _
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hg2
    exact absurd hg2 (by norm_num)
  have hgg : (⟨g, hg⟩ : center G) ^ 2 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hg2, pow_orderOf_eq_one])
  have hroots : ∀ x : center G, x ^ 2 = 1 → x = 1 ∨ x = ⟨g, hg⟩ := by
    intro x hx
    by_contra hne
    push Not at hne
    have hsub : ({1, ⟨g, hg⟩, x} : Finset (center G)) ⊆
        Finset.univ.filter (fun a : center G => a ^ 2 = 1) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases ha with rfl | rfl | rfl
      · exact one_pow 2
      · exact hgg
      · exact hx
    have h1g : (1 : center G) ≠ ⟨g, hg⟩ := fun h => hg1 (congrArg Subtype.val h).symm
    have h3 : ({1, ⟨g, hg⟩, x} : Finset (center G)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair hne.2.symm]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h1g, hne.1.symm⟩
    have := (Finset.card_le_card hsub).trans
      (IsCyclic.card_pow_eq_one_le (α := center G) (n := 2) (by norm_num))
    omega
  refine ⟨fun z hz => ?_, fun z hz hz1 => ?_⟩
  · have hz4 : (⟨z, hz⟩ : center G) ^ 4 = 1 := by
      obtain ⟨k, hk⟩ := hcard
      rw [hk, pow_mul, pow_card_eq_one', one_pow]
    rcases hroots (⟨z, hz⟩ ^ 2) (by rw [← pow_mul]; exact hz4) with h | h
    · left
      have := congrArg Subtype.val h
      simpa using this
    · right
      have := congrArg Subtype.val h
      simpa using this
  · rcases hroots ⟨z, hz⟩ (Subtype.ext (by simpa using hz1)) with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)

theorem spinPlus_odd_cover {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2) {n : ℕ}
    (hn : 3 ≤ n) (ho : Odd n) {L : Type} [Group L] [Finite L] (α : spinGroup (quadPlus n F) →* L)
    (hα : Function.Surjective α) {c : L} (hc : PropBHypII L c) :
    c = α (SpinPlusClosed.negOneS F hn) := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n))
  have hZ : center (spinGroup (quadPlus n F)) = SpinPlusClosed.scalarSpin n F :=
    (spinToStatedProj_quadPlus hn).2.2.symm.trans (spinToStatedProj_quadPlus hn).2.1
  have hcyc : IsCyclic (center (spinGroup (quadPlus n F))) ∧
      Nat.card (center (spinGroup (quadPlus n F))) ∣ 4 := by
    rw [hZ]
    by_cases hsq : IsSquare (-1 : F)
    · obtain ⟨r, hr⟩ := hsq
      have hr0 : r ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hr
        exact one_ne_zero (neg_eq_zero.1 hr)
      have hι : Units.mk0 r hr0 ^ 2 = -1 := Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.val_mk0, pow_two, ← hr, Units.val_neg, Units.val_one])
      obtain ⟨hc4, hcy⟩ := SpinPlusClosed.card_scalarSpin_of_isSquare hn h2 ho hι
      exact ⟨hcy, by rw [hc4]⟩
    · have hc2 := SpinPlusClosed.card_scalarSpin_of_not_isSquare hn h2 ho hsq
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact ⟨isCyclic_of_prime_card hc2, by rw [hc2]; norm_num⟩
  have hg : SpinPlusClosed.negOneS F hn ∈ center (spinGroup (quadPlus n F)) :=
    mem_center_iff.2 fun x => (SpinPlusClosed.commute_negOneS hn x).eq.symm
  have hg2 : orderOf (SpinPlusClosed.negOneS F hn) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact SpinPlusClosed.negOneS_mul_self hn)
      (SpinPlusClosed.negOneS_ne_one hn h2)
  obtain ⟨hZ1, hZ2⟩ := center_hyps_of_isCyclic hcyc.1 hcyc.2 hg hg2
  exact eq_of_propBHypII (isQuasisimple_spinGroup_quadPlus hn) hg hg2 hZ1 hZ2 α hα hc

theorem spinMinus_cover {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2) {p f : ℕ}
    (hK : Nat.card F = p ^ f) {n : ℕ} (hn : 4 ≤ n) {b c₀ : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c₀ ≠ 0) {L : Type} [Group L] [Finite L]
    (α : spinGroup (quadMinus n F b c₀) →* L) (hα : Function.Surjective α) {c : L}
    (hc : PropBHypII L c) : c = α (SpinMinusClosed.negOneM n F b c₀) := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have : Finite (spinGroup (quadMinus n F b c₀)) :=
    CFSG.LieType.Steinberg.finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus (n := n) hirr)
  have hZ : center (spinGroup (quadMinus n F b c₀)) = SpinMinusClosed.scalarSpinM n F b c₀ :=
    (spinToStatedProj_quadMinus hn hirr).2.2.symm.trans (spinToStatedProj_quadMinus hn hirr).2.1
  have hcyc : IsCyclic (center (spinGroup (quadMinus n F b c₀))) ∧
      Nat.card (center (spinGroup (quadMinus n F b c₀))) ∣ 4 := by
    rw [hZ]
    obtain ⟨hcard, hcy⟩ := SpinMinusClosed.card_scalarSpinM hirr hn hK
    exact ⟨hcy, by rw [hcard]; exact Nat.gcd_dvd_left _ _⟩
  have hg : SpinMinusClosed.negOneM n F b c₀ ∈ center (spinGroup (quadMinus n F b c₀)) :=
    mem_center_iff.2 fun x => (SpinMinusClosed.commute_negOneM x).eq.symm
  have hg2 : orderOf (SpinMinusClosed.negOneM n F b c₀) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact SpinMinusClosed.negOneM_mul_self)
      (SpinMinusClosed.negOneM_ne_one h2)
  obtain ⟨hZ1, hZ2⟩ := center_hyps_of_isCyclic hcyc.1 hcyc.2 hg hg2
  exact eq_of_propBHypII (isQuasisimple_spinGroup_quadMinus hn hirr) hg hg2 hZ1 hZ2 α hα hc

end CFSG.ComponentClassification.Burgoyne.B
