module

public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultBound
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Blueprint.Multiplier CFSG.Assembly.LowTwoRank

theorem i61_gcd_two_sub_one {n : ℕ} (hn : 1 ≤ n) : Nat.gcd 2 (2 ^ n - 1) = 1 := by
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hodd : (2 ^ n - 1) % 2 = 1 := by omega
  rw [Nat.gcd_rec, hodd, Nat.gcd_one_left]

theorem i61_gcd_four_sub_one {n : ℕ} (hn : 1 ≤ n) : Nat.gcd 4 (2 ^ n - 1) = 1 := by
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  rw [Nat.gcd_rec]
  have h4 : (2 ^ n - 1) % 4 = 1 ∨ (2 ^ n - 1) % 4 = 3 := by omega
  rcases h4 with h | h <;> rw [h] <;> norm_num

theorem i61_not_two_dvd_two_pow_add_one {n : ℕ} (hn : 1 ≤ n) : ¬ 2 ∣ 2 ^ n + 1 := by
  have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  omega

theorem i61_dvd_three_of_dvd_six {n d : ℕ} (hn : 1 ≤ n) (h6 : d ∣ 6) (hq : d ∣ 2 ^ n + 1) :
    d ∣ 3 := by
  have hc : Nat.Coprime d 2 :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
      fun h2 => i61_not_two_dvd_two_pow_add_one hn (h2.trans hq))
  exact Nat.Coprime.dvd_of_dvd_mul_left hc (show d ∣ 2 * 3 from h6)

theorem i61_odd_of_three_dvd_two_pow_add_one {n : ℕ} (h : 3 ∣ 2 ^ n + 1) : Odd n := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | h'
  · exfalso
    have h4 : (2 : ℕ) ^ (k + k) = 4 ^ k := by
      rw [← two_mul, pow_mul]; norm_num
    have hm : 4 ^ k % 3 = 1 := by
      rw [Nat.pow_mod]; norm_num
    rw [h4] at h
    omega
  · exact h'

theorem i61_gen_PSU (n : ℕ) : genericOrders .PSU 6 2 n = (Nat.gcd 6 (2 ^ n + 1), 1) := rfl

theorem i61_gen_twE6 (n : ℕ) : genericOrders .twistedE6 0 2 n = (Nat.gcd 3 (2 ^ n + 1), 1) := rfl

theorem i61_gen_PSp {ℓ n : ℕ} (hn : 1 ≤ n) : genericOrders .PSp ℓ 2 n = (1, 1) := by
  show (Nat.gcd 2 (2 ^ n - 1), 1) = (1, 1)
  rw [i61_gcd_two_sub_one hn]

theorem i61_gen_PSL_four {n : ℕ} (hn : 1 ≤ n) : genericOrders .PSL 4 2 n = (1, 1) := by
  show (Nat.gcd 4 (2 ^ n - 1), 1) = (1, 1)
  rw [i61_gcd_four_sub_one hn]

theorem i61_gen_E7 {n : ℕ} (hn : 1 ≤ n) : genericOrders .E7 0 2 n = (1, 1) := by
  show (Nat.gcd 2 (2 ^ n - 1), 1) = (1, 1)
  rw [i61_gcd_two_sub_one hn]

theorem i61_gen_POmegaPlus {ℓ n : ℕ} (hn : 1 ≤ n) :
    genericOrders .POmegaPlus ℓ 2 n = (1, 1) := by
  have he : Even (2 ^ n) := (Nat.even_pow).2 ⟨even_two, by omega⟩
  simp [genericOrders, he]

theorem i61_gen_F4 {n : ℕ} : genericOrders .F4 0 2 n = (1, 1) := rfl

theorem i61_gen_E8 {n : ℕ} : genericOrders .E8 0 2 n = (1, 1) := rfl

theorem i61_gen_E6 {n : ℕ} (hn : n = 1) : genericOrders .E6 0 2 n = (1, 1) := by
  subst hn; rfl

theorem i61_gen_PSL_nine {n : ℕ} (hn : n = 1) : genericOrders .PSL 9 2 n = (1, 1) := by
  subst hn; rfl

theorem i61_exc_PSU {f : ℕ} (hf : f ≠ 1) : exceptionalOrders .PSU 6 2 f = (1, 1) := by
  unfold exceptionalOrders
  split <;> simp_all

theorem i61_exc_twE6 {f : ℕ} (hf : f ≠ 1) : exceptionalOrders .twistedE6 0 2 f = (1, 1) := by
  unfold exceptionalOrders
  split <;> simp_all

theorem i61_exc_PSp {ℓ f : ℕ} (hf : f ≠ 1) : exceptionalOrders .PSp ℓ 2 f = (1, 1) := by
  unfold exceptionalOrders
  split <;> simp_all

theorem i61_exc_PSL_four {f : ℕ} (hf : f ≠ 1) : exceptionalOrders .PSL 4 2 f = (1, 1) := by
  unfold exceptionalOrders
  split <;> simp_all

theorem i61_exc_POmegaPlus {ℓ f : ℕ} (hf : f ≠ 1) :
    exceptionalOrders .POmegaPlus ℓ 2 f = (1, 1) := by
  unfold exceptionalOrders
  split <;> simp_all

theorem i61_exc_F4 {f : ℕ} (hf : f ≠ 1) : exceptionalOrders .F4 0 2 f = (1, 1) := by
  unfold exceptionalOrders
  split <;> simp_all

theorem i61_exc_E7 {f : ℕ} : exceptionalOrders .E7 0 2 f = (1, 1) := by
  unfold exceptionalOrders
  split <;> simp_all

theorem i61_exc_E8 {f : ℕ} : exceptionalOrders .E8 0 2 f = (1, 1) := by
  unfold exceptionalOrders
  split <;> simp_all

theorem i61_exc_E6 {f : ℕ} : exceptionalOrders .E6 0 2 f = (1, 1) := by
  unfold exceptionalOrders
  split <;> simp_all

theorem i61_exc_PSL_nine {n : ℕ} (hn : n = 1) : exceptionalOrders .PSL 9 2 n = (1, 1) := by
  subst hn
  unfold exceptionalOrders
  split <;> simp_all

section Models

variable {X : Type} [Group X]

theorem i61_model_psu {lab : GLALabel} (h : CFSG.StandardType.MarkedModel lab X)
    (ht : lab.tag = .twA) (hr : lab.rank = 5) : CFSG.Blueprint.LieModel X .PSU 6 2 lab.n := by
  obtain ⟨tg, rk, nn⟩ := lab
  dsimp only at ht hr
  subst ht; subst hr
  exact h

theorem i61_model_twE6 {lab : GLALabel} (h : CFSG.StandardType.MarkedModel lab X)
    (ht : lab.tag = .twE6) : CFSG.Blueprint.LieModel X .twistedE6 0 2 lab.n := by
  obtain ⟨tg, rk, nn⟩ := lab
  dsimp only at ht
  subst ht
  exact h

theorem i61_model_B {lab : GLALabel} (h : CFSG.StandardType.MarkedModel lab X)
    (ht : lab.tag = .B) : CFSG.Blueprint.LieModel X .PSp lab.rank 2 lab.n := by
  obtain ⟨tg, rk, nn⟩ := lab
  dsimp only at ht
  subst ht
  exact h

theorem i61_model_D3 {lab : GLALabel} (h : CFSG.StandardType.MarkedModel lab X)
    (ht : lab.tag = .D) (hr : lab.rank = 3) : CFSG.Blueprint.LieModel X .PSL 4 2 lab.n := by
  obtain ⟨tg, rk, nn⟩ := lab
  dsimp only at ht hr
  subst ht; subst hr
  exact h

theorem i61_model_D {lab : GLALabel} (h : CFSG.StandardType.MarkedModel lab X)
    (ht : lab.tag = .D) (hr : lab.rank ≠ 3) :
    CFSG.Blueprint.LieModel X .POmegaPlus lab.rank 2 lab.n := by
  obtain ⟨tg, rk, nn⟩ := lab
  dsimp only at ht hr
  subst ht
  have h' := h
  unfold CFSG.StandardType.MarkedModel at h'
  simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank, CFSG.StandardType.markChar,
    CFSG.StandardType.markDeg, if_neg hr] at h'
  exact h'

theorem i61_model_F4 {lab : GLALabel} (h : CFSG.StandardType.MarkedModel lab X)
    (ht : lab.tag = .F4) : CFSG.Blueprint.LieModel X .F4 0 2 lab.n := by
  obtain ⟨tg, rk, nn⟩ := lab
  dsimp only at ht
  subst ht
  exact h

theorem i61_model_E7 {lab : GLALabel} (h : CFSG.StandardType.MarkedModel lab X)
    (ht : lab.tag = .E7) : CFSG.Blueprint.LieModel X .E7 0 2 lab.n := by
  obtain ⟨tg, rk, nn⟩ := lab
  dsimp only at ht
  subst ht
  exact h

theorem i61_model_E8 {lab : GLALabel} (h : CFSG.StandardType.MarkedModel lab X)
    (ht : lab.tag = .E8) : CFSG.Blueprint.LieModel X .E8 0 2 lab.n := by
  obtain ⟨tg, rk, nn⟩ := lab
  dsimp only at ht
  subst ht
  exact h

theorem i61_model_E6 {lab : GLALabel} (h : CFSG.StandardType.MarkedModel lab X)
    (ht : lab.tag = .E6) : CFSG.Blueprint.LieModel X .E6 0 2 lab.n := by
  obtain ⟨tg, rk, nn⟩ := lab
  dsimp only at ht
  subst ht
  exact h

theorem i61_model_A8 {lab : GLALabel} (h : CFSG.StandardType.MarkedModel lab X)
    (ht : lab.tag = .A) (hr : lab.rank = 8) : CFSG.Blueprint.LieModel X .PSL 9 2 lab.n := by
  obtain ⟨tg, rk, nn⟩ := lab
  dsimp only at ht hr
  subst ht; subst hr
  exact h

end Models

theorem i61_two_le_of_half_twA_twE6 {p : ℕ} {lab : GLALabel} {c : Prop}
    (hT : (lab.tag = .twA ∧ lab.rank = 5) ∨ lab.tag = .twE6)
    (hH : CFSG.Assembly.LargeEvenHalfSplit16 p lab c) (hN : ¬ CFSG.Assembly.LargeEvenSplit16 p lab)
    (hn : 1 ≤ lab.n) : 2 ≤ lab.n := by
  by_contra hlt
  have h1 : lab.n = 1 := by omega
  unfold CFSG.Assembly.LargeEvenHalfSplit16 at hH
  rcases hH with hS | ⟨hfam, -⟩ | ⟨-, hp⟩ | ⟨hfam, hn2, -⟩ | ⟨htg, -⟩ | ⟨htg, -⟩
  · exact hN hS
  · rcases hT with ⟨ht, -⟩ | ht <;> rcases hfam with h | h | h | h | h <;>
      exact absurd (ht.symm.trans h) (by decide)
  · rw [h1] at hp
    norm_num at hp
    subst hp
    apply hN
    unfold CFSG.Assembly.LargeEvenSplit16
    right; left
    refine ⟨?_, ?_, ?_, one_dvd _⟩
    · rcases hT with ⟨ht, -⟩ | ht <;> simp [ht, CFSG.Assembly.LargeEvenUntwisted]
    · rcases hT with ⟨ht, -⟩ | ht <;> simp [ht]
    · rcases hT with ⟨ht, -⟩ | ht <;> simp [ht]
  · omega
  · rcases hT with ⟨ht, -⟩ | ht <;> exact absurd (ht.symm.trans htg) (by decide)
  · rcases hT with ⟨ht, -⟩ | ht <;> exact absurd (ht.symm.trans htg) (by decide)

theorem i61_two_le_of_family {p : ℕ} {lab : GLALabel}
    (hfam : lab.tag = .B ∨ lab.tag = .D ∨ lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8)
    (hp : p ∣ 2 ^ lab.n + 1) (hN : ¬ CFSG.Assembly.LargeEvenSplit16 p lab) (hn : 1 ≤ lab.n) :
    2 ≤ lab.n := by
  by_contra hlt
  have h1 : lab.n = 1 := by omega
  rw [h1] at hp
  norm_num at hp
  rcases (Nat.dvd_prime Nat.prime_three).1 hp with rfl | rfl
  · apply hN
    unfold CFSG.Assembly.LargeEvenSplit16
    left
    refine ⟨?_, one_dvd _⟩
    rcases hfam with h | h | h | h | h <;> simp [h, CFSG.Assembly.LargeEvenUntwisted]
  · apply hN
    unfold CFSG.Assembly.LargeEvenSplit16
    right; right; right
    exact ⟨h1, rfl⟩

section Marking


theorem i61_labelOf_model {G : Type} [Group G] [Finite G] {K : Subgroup G} {lab : GLALabel}
    (h : LabelOf K lab) :
    1 ≤ lab.n ∧ CFSG.Open.IsQuasisimple ↥K ∧
      CFSG.StandardType.MarkedModel lab (↥K ⧸ Subgroup.center ↥K) := by
  obtain ⟨hcomm, lab', hlam, R, _, I, F, θ, hs, -, ⟨rfl, hm⟩⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_exists
      (CFSG.StandardType.Canonical.largeEvenMarking_markedModel h)
  haveI := hs
  exact ⟨hlam.1, ⟨hcomm, θ.isSimpleGroup⟩,
    CFSG.StandardType.MarkedModel.of_mulEquiv θ.symm hm⟩

end Marking

section Griess


theorem i61_card_mult_zmod (n : ℕ) : Nat.card (Multiplicative (ZMod n)) = n := by
  rw [Nat.card_congr Multiplicative.toAdd]
  exact Nat.card_zmod n

theorem i61_card_center_dvd_native {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.Open.IsQuasisimple Q) {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f a b c d : ℕ}
    (hm : CFSG.Blueprint.LieModel (Q ⧸ Subgroup.center Q) t n p f)
    (hg : genericOrders t n p f = (a, b)) (he : exceptionalOrders t n p f = (c, d)) :
    Nat.card (Subgroup.center Q) ∣ a * b * (c * d) := by
  obtain ⟨-, ⟨e⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models
    (Q ⧸ Subgroup.center Q) t n p f hm
  have h := card_center_dvd_hopfMultiplier_of_cover hQ
    (QuotientGroup.mk' (Subgroup.center Q)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _)
  rw [← Nat.card_congr
      (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess (Q ⧸ Subgroup.center Q)).toEquiv,
    Nat.card_congr e.toEquiv] at h
  simp only [Nat.card_prod, i61_card_mult_zmod, hg, he] at h
  exact h

theorem i61_center_eq_bot_of_model {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.Open.IsQuasisimple Q) {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}
    (hm : CFSG.Blueprint.LieModel (Q ⧸ Subgroup.center Q) t n p f)
    (hg : genericOrders t n p f = (1, 1)) (he : exceptionalOrders t n p f = (1, 1)) :
    Subgroup.center Q = ⊥ := by
  have h := i61_card_center_dvd_native hQ hm hg he
  simp only [mul_one] at h
  exact Subgroup.card_eq_one.1 (Nat.dvd_one.1 h)

theorem i61_card_center_dvd_psu {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.Open.IsQuasisimple Q) {n : ℕ} (hn : 2 ≤ n)
    (hm : CFSG.Blueprint.LieModel (Q ⧸ Subgroup.center Q) .PSU 6 2 n) :
    Nat.card (Subgroup.center Q) ∣ 3 ∧ Nat.card (Subgroup.center Q) ∣ 2 ^ n + 1 := by
  have h := i61_card_center_dvd_native hQ hm (i61_gen_PSU n) (i61_exc_PSU (f := n) (by omega))
  simp only [mul_one] at h
  have hq : Nat.card (Subgroup.center Q) ∣ 2 ^ n + 1 := h.trans (Nat.gcd_dvd_right _ _)
  exact ⟨i61_dvd_three_of_dvd_six (by omega) (h.trans (Nat.gcd_dvd_left _ _)) hq, hq⟩

theorem i61_card_center_dvd_twE6 {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.Open.IsQuasisimple Q) {n : ℕ} (hn : 2 ≤ n)
    (hm : CFSG.Blueprint.LieModel (Q ⧸ Subgroup.center Q) .twistedE6 0 2 n) :
    Nat.card (Subgroup.center Q) ∣ 3 ∧ Nat.card (Subgroup.center Q) ∣ 2 ^ n + 1 := by
  have h := i61_card_center_dvd_native hQ hm (i61_gen_twE6 n) (i61_exc_twE6 (f := n) (by omega))
  simp only [mul_one] at h
  exact ⟨h.trans (Nat.gcd_dvd_left _ _), h.trans (Nat.gcd_dvd_right _ _)⟩

theorem i61At_holds (G : Type) [Group G] [Finite G] : I61At G := by
  intro K lab hK hlab
  obtain ⟨hn1, hQ, hM⟩ := i61_labelOf_model hlab
  refine ⟨fun hT h3 => ?_, fun hL hZ => ?_⟩
  · have hdiv : 2 ≤ lab.n → Nat.card (Subgroup.center ↥K) ∣ 3 ∧
        Nat.card (Subgroup.center ↥K) ∣ 2 ^ lab.n + 1 := by
      intro hn2
      rcases hT with ⟨ht, hr⟩ | ht
      · exact i61_card_center_dvd_psu hQ hn2 (i61_model_psu hM ht hr)
      · exact i61_card_center_dvd_twE6 hQ hn2 (i61_model_twE6 hM ht)
    refine ⟨fun hn2 => Nat.dvd_antisymm (hdiv hn2).1 h3, ?_⟩
    rcases Nat.lt_or_ge lab.n 2 with h | h
    · have h1 : lab.n = 1 := by omega
      rw [h1]
      exact odd_one
    · exact i61_odd_of_three_dvd_two_pow_add_one (h3.trans (hdiv h).2)
  · obtain ⟨p, hl⟩ := hL
    have hHS : CFSG.Assembly.LargeEvenHalfSplit16 p lab (Subgroup.center ↥K = ⊥) := hl.1
    have hNS : ¬ CFSG.Assembly.LargeEvenSplit16 p lab := hl.2
    have hHS0 := hHS
    unfold CFSG.Assembly.LargeEvenHalfSplit16 at hHS
    rcases hHS with hS | hfam1 | hfam2 | hfam3 | hfam4 | hfam5
    · exact absurd hS hNS
    · obtain ⟨hfam, hp⟩ := hfam1
      have hn2 : 2 ≤ lab.n := i61_two_le_of_family hfam hp hNS hn1
      exfalso
      apply hZ
      rcases hfam with ht | ht | ht | ht | ht
      · exact i61_center_eq_bot_of_model hQ (i61_model_B hM ht) (i61_gen_PSp hn1)
          (i61_exc_PSp (by omega))
      · by_cases hr : lab.rank = 3
        · exact i61_center_eq_bot_of_model hQ (i61_model_D3 hM ht hr) (i61_gen_PSL_four hn1)
            (i61_exc_PSL_four (by omega))
        · exact i61_center_eq_bot_of_model hQ (i61_model_D hM ht hr) (i61_gen_POmegaPlus hn1)
            (i61_exc_POmegaPlus (by omega))
      · exact i61_center_eq_bot_of_model hQ (i61_model_F4 hM ht) i61_gen_F4
          (i61_exc_F4 (by omega))
      · exact i61_center_eq_bot_of_model hQ (i61_model_E7 hM ht) (i61_gen_E7 hn1) i61_exc_E7
      · exact i61_center_eq_bot_of_model hQ (i61_model_E8 hM ht) i61_gen_E8 i61_exc_E8
    · obtain ⟨hT, hp⟩ := hfam2
      have hn2 : 2 ≤ lab.n := i61_two_le_of_half_twA_twE6 hT hHS0 hNS hn1
      have h3 : Nat.card (Subgroup.center ↥K) ∣ 3 := by
        rcases hT with ⟨ht, hr⟩ | ht
        · exact (i61_card_center_dvd_psu hQ hn2 (i61_model_psu hM ht hr)).1
        · exact (i61_card_center_dvd_twE6 hQ hn2 (i61_model_twE6 hM ht)).1
      have h3eq : Nat.card (Subgroup.center ↥K) = 3 := by
        rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
        · exact absurd (Subgroup.card_eq_one.1 h) hZ
        · exact h
      exact ⟨hT, by simp [h3eq]⟩
    · exact (hZ hfam3.2.2.1).elim
    · obtain ⟨ht, hr, hn, -⟩ := hfam4
      exfalso
      apply hZ
      exact i61_center_eq_bot_of_model hQ (i61_model_A8 hM ht hr) (i61_gen_PSL_nine hn)
        (i61_exc_PSL_nine hn)
    · obtain ⟨ht, hn, -⟩ := hfam5
      exfalso
      apply hZ
      exact i61_center_eq_bot_of_model hQ (i61_model_E6 hM ht) (i61_gen_E6 hn) i61_exc_E6

theorem i161bAt_holds (G : Type) [Group G] [Finite G] : I161bAt G := by
  intro p hp hp2 K hK hH hN
  by_cases hZ : Subgroup.center ↥K = ⊥
  · rw [hZ]
    simp
  · obtain ⟨lab, hlab, hHS⟩ := hH
    have hl : List110 p lab (Subgroup.center ↥K = ⊥) := ⟨hHS, hN lab hlab⟩
    obtain ⟨hC1, hC2⟩ := i61At_holds G K lab hK hlab
    obtain ⟨hT, h3⟩ := hC2 ⟨p, hl⟩ hZ
    have hn1 : 1 ≤ lab.n := (i61_labelOf_model hlab).1
    have hn2 : 2 ≤ lab.n := i61_two_le_of_half_twA_twE6 hT hHS (hN lab hlab) hn1
    rw [(hC1 hT h3).1 hn2]
    exact ⟨1, rfl⟩

end Griess

end CFSG.LocalAnalysis.GLTheoremA
