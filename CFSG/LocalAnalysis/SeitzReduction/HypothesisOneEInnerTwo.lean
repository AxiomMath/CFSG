module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneEInner
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneF4InnerTwo

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open scoped commutatorElement

@[expose] def eGenRoot (τ : Tag) (v : Fin τ.rank → ℤ) : Bool :=
  decide (0 < height v) || (decide (height v < 0) && decide (v (highNode τ) = 0))

@[expose] def eDerivTable : Tag → List (ℕ × ℕ)
  | .E6 =>
    [(7, 10), (9, 12), (6, 7), (10, 11), (12, 13), (14, 15), (2, 17), (0, 2), (0, 0), (1, 3),
      (0, 17), (2, 3), (2, 22), (3, 4), (3, 24), (4, 5), (4, 26), (3, 27), (0, 11), (0, 0),
      (1, 11), (1, 13), (0, 27), (2, 13), (2, 34), (3, 15), (3, 36), (4, 38), (0, 20), (0, 23),
      (0, 0), (0, 0), (1, 23), (1, 25), (0, 38), (2, 25), (2, 45), (0, 0), (5, 47), (0, 32),
      (0, 35), (0, 0), (0, 0), (3, 32), (1, 35), (0, 47), (0, 0), (6, 45), (0, 43), (0, 44),
      (0, 0), (0, 0), (3, 44), (0, 0), (0, 0), (2, 48), (0, 52), (0, 0), (4, 52), (0, 0), (0, 0),
      (2, 56), (0, 58), (0, 0), (0, 0), (0, 0), (2, 62), (0, 0), (3, 66), (0, 0), (1, 68), (0, 0)]
  | .E7 =>
    [(8, 11), (10, 13), (12, 13), (9, 10), (13, 14), (15, 16), (17, 18), (0, 0), (0, 2), (3, 22),
      (1, 3), (3, 25), (2, 3), (1, 22), (3, 4), (3, 27), (4, 5), (4, 29), (5, 6), (5, 31),
      (0, 0), (0, 12), (2, 35), (1, 12), (1, 14), (1, 35), (2, 14), (1, 36), (3, 16), (3, 41),
      (4, 18), (4, 43), (0, 0), (0, 23), (0, 26), (4, 48), (2, 48), (1, 26), (1, 28), (1, 48),
      (2, 28), (1, 49), (3, 30), (3, 55), (0, 0), (0, 0), (0, 37), (0, 40), (3, 61), (2, 62),
      (3, 37), (1, 40), (1, 42), (1, 62), (2, 42), (1, 63), (0, 0), (0, 0), (0, 50), (0, 51),
      (0, 54), (5, 73), (3, 73), (2, 74), (3, 51), (1, 54), (1, 74), (0, 0), (0, 0), (0, 0),
      (2, 58), (0, 64), (0, 65), (4, 83), (3, 84), (4, 64), (3, 65), (0, 0), (0, 0), (0, 0),
      (2, 71), (0, 75), (0, 76), (6, 92), (4, 92), (4, 76), (0, 0), (0, 0), (0, 0), (2, 81),
      (2, 82), (0, 85), (5, 100), (5, 85), (0, 0), (0, 0), (0, 0), (3, 89), (2, 91), (0, 93),
      (17, 92), (0, 0), (0, 0), (0, 0), (1, 97), (3, 98), (2, 99), (0, 0), (0, 0), (0, 0),
      (1, 105), (3, 106), (0, 0), (0, 0), (1, 111), (4, 111), (0, 0), (0, 0), (1, 115), (0, 0),
      (3, 118), (0, 0), (2, 120), (0, 0), (0, 122), (0, 0)]
  | .E8 =>
    [(9, 12), (11, 14), (8, 9), (10, 11), (14, 15), (16, 17), (18, 19), (20, 21), (2, 23),
      (0, 2), (3, 25), (1, 3), (0, 23), (2, 3), (1, 25), (3, 4), (3, 30), (4, 5), (4, 32),
      (5, 6), (5, 34), (6, 7), (0, 0), (3, 37), (0, 13), (2, 40), (1, 13), (1, 15), (0, 37),
      (2, 15), (1, 41), (3, 17), (3, 46), (4, 19), (4, 48), (5, 21), (0, 0), (1, 51), (0, 26),
      (0, 29), (0, 51), (2, 55), (1, 29), (1, 31), (0, 52), (2, 31), (1, 56), (3, 33), (3, 62),
      (4, 35), (0, 0), (4, 65), (1, 65), (0, 42), (0, 45), (0, 65), (2, 71), (3, 42), (1, 45),
      (1, 47), (0, 66), (2, 47), (1, 72), (3, 49), (0, 0), (3, 79), (1, 80), (0, 57), (0, 58),
      (0, 61), (0, 79), (0, 80), (2, 87), (3, 58), (1, 61), (1, 63), (0, 81), (2, 63), (0, 0),
      (2, 93), (3, 94), (1, 95), (2, 67), (0, 73), (0, 74), (0, 77), (0, 94), (0, 95), (0, 0),
      (4, 73), (3, 74), (1, 77), (0, 0), (5, 106), (2, 106), (3, 108), (0, 0), (2, 83), (0, 89),
      (0, 90), (0, 91), (0, 107), (0, 108), (0, 0), (4, 90), (3, 91), (4, 118), (2, 118),
      (2, 119), (0, 0), (2, 98), (2, 99), (0, 104), (0, 105), (0, 120), (0, 0), (5, 104),
      (4, 105), (3, 130), (4, 131), (2, 131), (0, 0), (3, 110), (2, 112), (2, 113), (0, 116),
      (0, 117), (0, 133), (0, 0), (5, 117), (1, 142), (3, 143), (0, 0), (2, 144), (0, 0),
      (1, 122), (3, 123), (2, 125), (2, 126), (0, 129), (0, 0), (6, 129), (6, 153), (1, 153),
      (3, 154), (0, 0), (0, 0), (1, 136), (3, 137), (3, 138), (2, 139), (0, 141), (0, 0),
      (5, 163), (1, 163), (0, 0), (0, 0), (0, 0), (1, 148), (1, 149), (4, 148), (3, 150),
      (2, 151), (4, 172), (0, 0), (1, 172), (0, 0), (0, 0), (1, 160), (1, 161), (4, 161),
      (3, 162), (3, 180), (0, 0), (0, 0), (0, 0), (3, 168), (1, 170), (1, 171), (4, 171),
      (2, 188), (0, 0), (0, 0), (0, 0), (2, 176), (3, 177), (1, 179), (5, 179), (0, 196), (0, 0),
      (0, 0), (0, 0), (0, 184), (2, 185), (3, 186), (1, 187), (8, 188), (0, 0), (0, 0), (0, 0),
      (0, 193), (2, 194), (3, 195), (0, 0), (0, 0), (0, 0), (0, 201), (2, 202), (4, 202), (0, 0),
      (0, 0), (0, 0), (0, 207), (2, 208), (0, 0), (0, 0), (0, 213), (3, 213), (0, 0), (0, 0),
      (0, 217), (1, 217), (0, 0), (0, 0), (0, 221), (2, 220), (0, 0), (0, 0), (1, 225), (0, 0),
      (3, 228), (0, 0), (4, 230), (0, 0), (5, 232), (0, 0), (6, 234), (0, 0), (7, 236), (0, 0)]
  | .G2 => []
  | .F4 => []
  | .D4 => []

@[expose] def eTwoStep (τ : Tag) (k : ℕ) (p : ℕ × ℕ) : Bool :=
  decide (p.1 < τ.rootCertificate.roots.length) && decide (p.2 < τ.rootCertificate.roots.length) &&
    eGenRoot τ (τ.rootCertificate.root p.1) && eGenRoot τ (τ.rootCertificate.root p.2) &&
    (List.ofFn (τ.rootCertificate.root p.1 + τ.rootCertificate.root p.2) ==
      List.ofFn (τ.rootCertificate.root k)) &&
    (List.ofFn (τ.rootCertificate.root p.1) != List.ofFn (τ.rootCertificate.root p.2)) &&
    (List.ofFn (τ.rootCertificate.root p.1) != List.ofFn (-τ.rootCertificate.root p.2))

@[expose] def eCommCheck (τ : Tag) (k : ℕ) : Bool :=
  decide (0 < height (τ.rootCertificate.root k)) ||
    ((List.ofFn (τ.rootCertificate.root k) != List.ofFn (-highRoot τ)) &&
      (List.range τ.rootCertificate.roots.length).all fun n =>
        List.ofFn (τ.rootCertificate.root n) !=
          List.ofFn (τ.rootCertificate.root k + highRoot τ))

@[expose] def eTwoCheck (τ : Tag) : Bool :=
  (List.range τ.rootCertificate.roots.length).all fun k =>
    !eGenRoot τ (τ.rootCertificate.root k) ||
      (eTwoStep τ k ((eDerivTable τ).getD k (0, 0)) && eCommCheck τ k)

theorem eTwoCheck_E6 : eTwoCheck .E6 = true := by decide +kernel

theorem eTwoCheck_E7 : eTwoCheck .E7 = true := by decide +kernel

theorem eTwoCheck_E8 : eTwoCheck .E8 = true := by decide +kernel

theorem eTwoCheck_eq_true {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) : eTwoCheck τ = true := by
  rcases hτ with rfl | rfl | rfl
  exacts [eTwoCheck_E6, eTwoCheck_E7, eTwoCheck_E8]

theorem eTwoCheck_sound {τ : Tag} (h : eTwoCheck τ = true)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hg : eGenRoot τ γ = true) :
    (∃ a b : Fin τ.rank → ℤ, IsRoot τ a ∧ IsRoot τ b ∧ eGenRoot τ a = true ∧
      eGenRoot τ b = true ∧ a + b = γ ∧ a ≠ b ∧ a ≠ -b) ∧
    (height γ < 0 → γ ≠ -highRoot τ ∧ ¬IsRoot τ (γ + highRoot τ)) := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hγ
  simp only [eTwoCheck, List.all_eq_true, List.mem_range] at h
  have h' := h k hk
  rw [hg, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h'
  obtain ⟨hs, hc⟩ := h'
  simp only [eTwoStep, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hs
  obtain ⟨⟨⟨⟨⟨⟨hp1, hp2⟩, hg1⟩, hg2⟩, hsum⟩, hne1⟩, hne2⟩ := hs
  refine ⟨⟨_, _, RootCertificate.isRoot_root τ.rootCertificate_check _ hp1,
    RootCertificate.isRoot_root τ.rootCertificate_check _ hp2, hg1, hg2,
    RootCertificate.eq_of_ofFn_beq hsum, fun e => hne1 (congrArg List.ofFn e),
    fun e => hne2 (congrArg List.ofFn e)⟩, fun hneg => ?_⟩
  simp only [eCommCheck, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, bne_iff_ne,
    ne_eq, List.all_eq_true, List.mem_range] at hc
  rcases hc with hpos | ⟨hr, hn⟩
  · exact absurd hpos (not_lt.2 hneg.le)
  · refine ⟨fun e => hr (congrArg List.ofFn e), fun hroot => ?_⟩
    obtain ⟨n, hn', hne⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hroot
    exact hn n hn' (congrArg List.ofFn hne)


variable {τ : Tag} {K : Type} [Field K]

theorem posUnipotent_le_closure_odd_E_two (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) [Finite K]
    [CharP K 2] (hK : Nat.card K = 2) {t : adjointGroup τ K}
    (ht : (t : ModGL τ K) = pinnedX τ K (highRoot τ) 1) {u : adjointGroup τ K}
    (hu : (u : ModGL τ K) ∈ posUnipotent τ K) :
    u ∈ closure {c : adjointGroup τ K | c * t = t * c ∧ Odd (orderOf c)} := by
  have : Finite (ModGL τ K) := finite_modGL
  have hchk := eTwoCheck_eq_true hτ
  set P : Subgroup (adjointGroup τ K) := closure
    ((fun γ => (⟨pinnedX τ K γ 1, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup τ K)) ''
      {γ | IsRoot τ γ ∧ eGenRoot τ γ = true}) with hP
  have hgen : ∀ γ, IsRoot τ γ → eGenRoot τ γ = true →
      (⟨pinnedX τ K γ 1, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup τ K) ∈ P :=
    fun γ hγ hg => subset_closure ⟨γ, ⟨hγ, hg⟩, rfl⟩
  have hcomm : ∀ γ, IsRoot τ γ → eGenRoot τ γ = true →
      (⟨pinnedX τ K γ 1, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup τ K) * t =
        t * ⟨pinnedX τ K γ 1, pinnedX_mem_adjointGroup _ _⟩ := by
    intro γ hγ hg
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, ht]
    by_cases hpos : 0 < height γ
    · exact (commute_pinnedX_highRoot K hγ hpos 1 1).eq
    · have hneg : height γ < 0 := by
        have hg' := hg
        simp only [eGenRoot, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at hg'
        rcases hg' with h | ⟨h, -⟩
        · exact absurd h hpos
        · exact h
      obtain ⟨hr, hnr⟩ := (eTwoCheck_sound hchk hγ hg).2 hneg
      have hne : γ ≠ highRoot τ := fun e => by
        rw [e] at hneg
        exact absurd (height_highRoot_pos τ) (not_lt.2 hneg.le)
      exact ((simply_laced_root_commutator_unit.{0} τ (Or.inr hτ) hγ (isRoot_highRoot τ) hne
        hr).2 hnr K _ (mem_rootSubgroup.2 ⟨1, rfl⟩) _ (mem_rootSubgroup.2 ⟨1, rfl⟩)).eq
  have hPt : ∀ x ∈ P, x * t = t * x := by
    intro x hx
    induction hx using closure_induction with
    | mem x hx =>
      obtain ⟨γ, ⟨hγ, hg⟩, rfl⟩ := hx
      exact hcomm γ hγ hg
    | one => rw [one_mul, mul_one]
    | mul x y _ _ hx hy => exact (Commute.mul_left (hx : Commute x _) hy).eq
    | inv x _ hx => exact (Commute.inv_left (hx : Commute x _)).eq
  have hperf : P ≤ ⁅P, P⁆ := by
    refine (closure_le _).2 ?_
    rintro _ ⟨γ, ⟨hγ, hg⟩, rfl⟩
    obtain ⟨⟨a, b, ha, hb, hga, hgb, hab, hne, hne'⟩, -⟩ := eTwoCheck_sound hchk hγ hg
    obtain ⟨hε, hc⟩ := (simply_laced_root_commutator_unit.{0} τ (Or.inr hτ) ha hb hne hne').1
      (hab ▸ hγ)
    have e : (⟨pinnedX τ K γ 1, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup τ K) =
        ⁅(⟨pinnedX τ K a 1, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup τ K),
          ⟨pinnedX τ K b 1, pinnedX_mem_adjointGroup _ _⟩⁆ := by
      refine Subtype.ext ?_
      change pinnedX τ K γ 1 = _
      rw [commutatorElement_def]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← commutatorElement_def, hc K 1 1, hab, mul_one, mul_one]
      rcases hε with h | h <;> rw [h] <;> simp [CharTwo.neg_eq]
    show (⟨pinnedX τ K γ 1, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup τ K) ∈ ⁅P, P⁆
    rw [e]
    exact commutator_mem_commutator (hgen a ha hga) (hgen b hb hgb)
  have hU : u ∈ P := mem_of_mem_posUnipotent_of_forall_pinnedX (fun γ hγ hγp c => by
    rcases eq_zero_or_eq_one_of_card_eq_two hK c with rfl | rfl
    · convert one_mem P
      rw [OneMemClass.coe_one]
      exact pinnedX_zero τ K γ
    · exact hgen γ hγ (by simp [eGenRoot, hγp])) hu
  exact le_closure_odd_of_le_commutator le_rfl hPt hperf hU

theorem innerCentralizerCriterion_E_longRoot_two (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) [Finite K]
    [CharP K 2] (hK : Nat.card K = 2) :
    InnerCentralizerCriterion
      (⟨pinnedX τ K (highRoot τ) 1, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup τ K) :=
  innerCentralizerCriterion_E_of_posUnipotent_le hτ le_rfl (by rw [pow_one]; exact hK)
    fun _ hu => posUnipotent_le_closure_odd_E_two hτ hK rfl hu

theorem innerCentralizerCriterion_E_longRoot' (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ}
    (hf : 1 ≤ f) [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) :
    InnerCentralizerCriterion
      (⟨pinnedX τ K (highRoot τ) 1, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup τ K) := by
  rcases Nat.lt_or_ge f 2 with h | h
  · obtain rfl : f = 1 := by omega
    exact innerCentralizerCriterion_E_longRoot_two hτ (by simpa using hK)
  · exact innerCentralizerCriterion_E_longRoot hτ h hK

theorem innerCentralizerCriterion_E6_longRoot {f : ℕ} (hf : 1 ≤ f) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) :
    InnerCentralizerCriterion
      (⟨pinnedX .E6 K (highRoot .E6) 1, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .E6 K) :=
  innerCentralizerCriterion_E_longRoot' (Or.inl rfl) hf hK

theorem innerCentralizerCriterion_E7_longRoot {f : ℕ} (hf : 1 ≤ f) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) :
    InnerCentralizerCriterion
      (⟨pinnedX .E7 K (highRoot .E7) 1, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .E7 K) :=
  innerCentralizerCriterion_E_longRoot' (Or.inr (Or.inl rfl)) hf hK

theorem innerCentralizerCriterion_E8_longRoot {f : ℕ} (hf : 1 ≤ f) [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ f) :
    InnerCentralizerCriterion
      (⟨pinnedX .E8 K (highRoot .E8) 1, pinnedX_mem_adjointGroup _ _⟩ : adjointGroup .E8 K) :=
  innerCentralizerCriterion_E_longRoot' (Or.inr (Or.inr rfl)) hf hK

end CFSG.SeitzReduction
