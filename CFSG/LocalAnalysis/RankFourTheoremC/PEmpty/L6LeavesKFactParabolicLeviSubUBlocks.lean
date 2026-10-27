module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubOUCore
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubUArith
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniData
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniBlocks

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPLeviSub

open Matrix CFSG.Open Subgroup CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem det_pow_succ_eq_one_of_gram {K : Type} [Field K] {p f r ε : ℕ}
    (h : UnitaryFieldData p f K) {x : Matrix (HypIndex r ε) (HypIndex r ε) K}
    (hx : (x.map h.bar)ᵀ * hypGram r ε K * x = hypGram r ε K) :
    x.det ^ (p ^ f + 1) = 1 := by
  have hJ : (hypGram r ε K).det ≠ 0 := det_hypGram_ne_zero
  have h1 := congrArg Matrix.det hx
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h1
  have h2 : (x.map h.bar).det = h.bar x.det := (RingHom.map_det h.bar x).symm
  rw [h2] at h1
  have h3 : h.bar x.det * x.det = 1 := by
    apply mul_left_cancel₀ hJ
    linear_combination h1
  rw [h.bar_apply] at h3
  calc x.det ^ (p ^ f + 1) = x.det ^ (p ^ f) * x.det := pow_succ _ _
    _ = 1 := h3

theorem mem_hypSU_of_pow_eq_one {K : Type} [Field K] {p f s ε : ℕ} (h : UnitaryFieldData p f K)
    {x : GL (HypIndex s ε) K}
    (hx : ((x : Matrix (HypIndex s ε) (HypIndex s ε) K).map h.bar)ᵀ * hypGram s ε K *
      (x : Matrix (HypIndex s ε) (HypIndex s ε) K) = hypGram s ε K) {n : ℕ}
    (hp : n.Prime) (hnq : ¬ n ∣ p ^ f + 1) (hxn : x ^ n = 1) : x ∈ hypSU h s ε := by
  refine mem_hypSU.mpr ⟨hx, ?_⟩
  have hd1 : (Matrix.GeneralLinearGroup.det x) ^ n = 1 := by
    rw [← map_pow, hxn, map_one]
  have hd2 : (Matrix.GeneralLinearGroup.det x) ^ (p ^ f + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    exact det_pow_succ_eq_one_of_gram h hx
  have h1 : orderOf (Matrix.GeneralLinearGroup.det x) ∣ n := orderOf_dvd_of_pow_eq_one hd1
  have h2 : orderOf (Matrix.GeneralLinearGroup.det x) ∣ p ^ f + 1 := orderOf_dvd_of_pow_eq_one hd2
  rcases (Nat.dvd_prime hp).1 h1 with h3 | h3
  · have := orderOf_eq_one_iff.1 h3
    have := congrArg Units.val this
    rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at this
  · exact absurd (h3 ▸ h2) hnq

variable {K : Type} [Field K] {f s ε : ℕ}

theorem card_hypPSU_eq_ordTwistedA (h : UnitaryFieldData 2 f K) (hs : 1 ≤ s) :
    Nat.card (hypPSU h s ε) = ordTwistedA (2 * s + ε - 1) (2 ^ f) := by
  have : Finite K := h.finite
  have hF : Nat.card K = (2 ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  obtain ⟨R, hR⟩ := exists_isHypTransport h (r := s) (ε := ε)
  rw [Nat.card_congr (hypPSUEquivStatedProj h hR (by omega)).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU h.prime h.one_le hF (by omega),
    ordTwistedA, Nat.sub_add_cancel (by omega : 1 ≤ 2 * s + ε),
    mul_comm (2 * s + ε - 1) (2 * s + ε)]

theorem card_center_hypSU_eq (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1) (hs : 1 ≤ s)
    (hq : CFSG.Open.IsQuasisimple (hypSU h s ε)) :
    Nat.card (Subgroup.center (hypSU h s ε)) = Nat.gcd (2 * s + ε) (2 ^ f + 1) := by
  have : Finite K := h.finite
  have hN : Nat.card (hypSU h s ε ⧸ Subgroup.center (hypSU h s ε)) =
      Nat.card (hypPSU h s ε) := by
    rw [(hypSU_facts h hε s).2 hq, card_hypPSU_eq_ordTwistedA h hs]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (hypSU h s ε))
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (hypScalars h s ε)
  have hq' : Nat.card (hypSU h s ε ⧸ hypScalars h s ε) =
      Nat.card (hypSU h s ε ⧸ Subgroup.center (hypSU h s ε)) := hN.symm
  have hpos : 0 < Nat.card (hypSU h s ε ⧸ Subgroup.center (hypSU h s ε)) := Nat.card_pos
  have h3 : Nat.card (Subgroup.center (hypSU h s ε)) = Nat.card (hypScalars h s ε) := by
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    calc Nat.card (hypSU h s ε ⧸ Subgroup.center (hypSU h s ε)) *
          Nat.card (Subgroup.center (hypSU h s ε)) = Nat.card (hypSU h s ε) := h1.symm
      _ = Nat.card (hypSU h s ε ⧸ hypScalars h s ε) * Nat.card (hypScalars h s ε) := h2
      _ = Nat.card (hypSU h s ε ⧸ Subgroup.center (hypSU h s ε)) *
          Nat.card (hypScalars h s ε) := by rw [hq']
  rw [h3, card_hypScalars h (by omega)]

theorem eq_one_of_pow_eq_one_hypSU_small (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1)
    (hsmall : s = 0 ∨ (s = 1 ∧ f = 1)) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    {x : hypSU h s ε} (hx : x ^ p = 1) : x = 1 := by
  rcases hsmall with rfl | ⟨rfl, rfl⟩
  · have := subsingleton_hypSU_zero h hε
    exact Subsingleton.elim _ _
  · have : Finite K := h.finite
    haveI : Fact p.Prime := ⟨hp⟩
    by_contra hx1
    have hord : orderOf x = p := orderOf_eq_prime hx hx1
    have hdvd : p ∣ Nat.card (hypSU h 1 ε) := hord ▸ orderOf_dvd_natCard x
    have hcard := (unitary_order_and_Sylow h le_rfl hε).2.2.2.2.2.1
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
    · have h6 : Nat.card (hypSU h 1 0) = 2 ^ 1 * 3 ^ 1 := by
        have : ((Nat.card (hypSU h 1 0) : ℕ) : ℤ) = ((2 ^ 1 * 3 ^ 1 : ℕ) : ℤ) := by
          rw [hcard]
          decide
        exact_mod_cast this
      rw [h6] at hdvd
      have := Nat.le_of_dvd (by norm_num) hdvd
      have h5' : p = 5 ∨ p = 6 := by omega
      rcases h5' with rfl | rfl
      · omega
      · exact absurd hp (by norm_num)
    · have h216 : Nat.card (hypSU h 1 1) = 2 ^ 3 * 3 ^ 3 := by
        have : ((Nat.card (hypSU h 1 1) : ℕ) : ℤ) = ((2 ^ 3 * 3 ^ 3 : ℕ) : ℤ) := by
          rw [hcard]
          decide
        exact_mod_cast this
      rw [h216] at hdvd
      rcases (Nat.Prime.dvd_mul hp).1 hdvd with h2 | h3
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2)
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)
        omega

theorem isQuasisimple_hypSU_or_small (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1) :
    CFSG.Open.IsQuasisimple (hypSU h s ε) ∨ s = 0 ∨ (s = 1 ∧ f = 1) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · exact Or.inr (Or.inl rfl)
  by_cases hm3 : 3 ≤ 2 * s + ε
  · by_cases hmq : (2 * s + ε, 2 ^ f) = (3, 2)
    · rw [Prod.mk.injEq] at hmq
      obtain ⟨rfl, rfl⟩ : s = 1 ∧ ε = 1 := by omega
      obtain rfl : f = 1 := Nat.pow_right_injective le_rfl (hmq.2.trans (pow_one 2).symm)
      exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inl (hypSU_facts_of_three_le h hm3 hmq).1
  · obtain ⟨rfl, rfl⟩ : s = 1 ∧ ε = 0 := by omega
    rcases Nat.lt_or_ge f 2 with hf2 | hf2
    · obtain rfl : f = 1 := by have := h.one_le; omega
      exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inl (hypSU_facts_two h hf2).1

theorem uni_res_block_data (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1) {p : ℕ} (hp : p.Prime)
    (h5 : 5 ≤ p) (hnd : ¬ p ∣ Nat.card K - 1) {x : hypSU h s ε} (hx : x ^ p = 1)
    (hx1 : x ≠ 1) :
    CFSG.Open.IsQuasisimple (hypSU h s ε) ∧
      ¬ p ∣ Nat.card (Subgroup.center (hypSU h s ε)) ∧
      p ∣ Nat.card (hypSU h s ε ⧸ Subgroup.center (hypSU h s ε)) ∧
      3 ∣ Nat.card (hypSU h s ε ⧸ Subgroup.center (hypSU h s ε)) := by
  have : Finite K := h.finite
  have hF : Nat.card K = (2 ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  rcases isQuasisimple_hypSU_or_small h hε with hq | hsmall
  swap
  · exact absurd (eq_one_of_pow_eq_one_hypSU_small h hε hsmall hp h5 hx) hx1
  have hs : 1 ≤ s := by
    by_contra hs0
    have hs0' : s = 0 := by omega
    subst hs0'
    have := subsingleton_hypSU_zero h hε
    exact hx1 (Subsingleton.elim _ _)
  have hq1 : ¬ p ∣ 2 ^ f + 1 := by
    intro hdvd
    apply hnd
    rw [hF]
    have h1 : 2 ^ f + 1 ∣ (2 ^ f) ^ 2 - 1 := by
      have := Nat.sq_sub_sq (2 ^ f) 1
      rw [one_pow] at this
      exact ⟨2 ^ f - 1, by rw [this]⟩
    exact hdvd.trans h1
  have hZ := card_center_hypSU_eq h hε hs hq
  have hpZ : ¬ p ∣ Nat.card (Subgroup.center (hypSU h s ε)) := by
    rw [hZ]
    exact fun hd => hq1 (hd.trans (Nat.gcd_dvd_right _ _))
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf x = p := orderOf_eq_prime hx hx1
  have hdvd : p ∣ Nat.card (hypSU h s ε) := hord ▸ orderOf_dvd_natCard x
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (hypSU h s ε))
  refine ⟨hq, hpZ, ?_, ?_⟩
  · rw [hmul] at hdvd
    exact ((Nat.Prime.dvd_mul hp).1 hdvd).resolve_right hpZ
  · rw [(hypSU_facts h hε s).2 hq]
    exact three_dvd_ordTwistedA h.one_le (by omega)

section Levi

variable {t : ℕ}

theorem eq_one_of_det_eq_one_of_eq_one {k : ℕ} (hk : k = 1) (x : GL (Fin k) K)
    (hd : Matrix.GeneralLinearGroup.det x = 1) : x = 1 := by
  subst hk
  apply Units.ext
  ext a b
  rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
  have h1 := congrArg Units.val hd
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, Matrix.det_unique] at h1
  simpa using h1

theorem exists_uniLeviHom_ne_one (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1) {I : Finset ℕ}
    (hI : IsTopCut I t) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    {g : ↥(flagStabilizer h (t + s) ε ↑I)} (hgp : g ^ p = 1) (hg1 : g ≠ 1) :
    ∃ j, uniLeviHom h hε hI g j ≠ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hβ : uniLeviHom h hε hI g ≠ 1 := by
    intro h1
    obtain ⟨k, hk⟩ := isPGroup_ker_uniLeviHom h hε hI ⟨g, h1⟩
    have hk' : g ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hord : orderOf g = p := orderOf_eq_prime hgp hg1
    have h2k : p ∣ 2 ^ k := hord ▸ orderOf_dvd_of_pow_eq_one hk'
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2k)
    omega
  by_contra hcon
  push Not at hcon
  exact hβ (funext hcon)

theorem uni_hblk (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1) {I : Finset ℕ} (hI : IsTopCut I t)
    {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hnd : ¬ p ∣ Nat.card K - 1)
    (g : ↥(flagStabilizer h (t + s) ε ↑I)) (hgp : g ^ p = 1) (hg1 : g ≠ 1) :
    ∃ j, CFSG.Open.IsQuasisimple ↥(uniBlockSub (s := s) (ε := ε) h I j) ∧
      ¬ p ∣ Nat.card (Subgroup.center ↥(uniBlockSub (s := s) (ε := ε) h I j)) ∧
      p ∣ Nat.card (↥(uniBlockSub (s := s) (ε := ε) h I j) ⧸
        Subgroup.center ↥(uniBlockSub (s := s) (ε := ε) h I j)) ∧
      3 ∣ Nat.card (↥(uniBlockSub (s := s) (ε := ε) h I j) ⧸
        Subgroup.center ↥(uniBlockSub (s := s) (ε := ε) h I j)) := by
  have : Finite K := h.finite
  have : CharP K 2 := h.charP
  obtain ⟨j, hj⟩ := exists_uniLeviHom_ne_one h hε hI hp h5 hgp hg1
  have hx : (uniLeviHom h hε hI g j) ^ p = 1 := by
    rw [← Pi.pow_apply, ← map_pow, hgp, map_one]
    rfl
  refine ⟨j, ?_⟩
  rcases j with _ | b
  ·
    have hF : Nat.card K = (2 ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
    have hq1 : ¬ p ∣ 2 ^ f + 1 := by
      intro hdvd
      apply hnd
      rw [hF]
      have h1 : 2 ^ f + 1 ∣ (2 ^ f) ^ 2 - 1 := by
        have := Nat.sq_sub_sq (2 ^ f) 1
        rw [one_pow] at this
        exact ⟨2 ^ f - 1, by rw [this]⟩
      exact hdvd.trans h1
    have hgram := resBlock_gram h hε (Finset.mem_coe.mpr hI.mem) g
    have hxS : uniLeviHom h hε hI g none ∈ hypSU h s ε :=
      mem_hypSU_of_pow_eq_one h hgram hp hq1 hx
    have := uni_res_block_data h hε hp h5 hnd (x := ⟨_, hxS⟩)
      (Subtype.ext hx) (fun h' => hj (congrArg Subtype.val h'))
    exact this
  ·
    have hk1 : 1 ≤ b.1 - predCut I b.1 :=
      Nat.sub_pos_of_lt (predCut_lt (I := I) (hI.le b.1 b.2).1)
    have hxb : (uniLeviHom h hε hI g (some b) : GL (Fin (b.1 - predCut I b.1)) K) ^ p = 1 := hx
    have hxb1 : (uniLeviHom h hε hI g (some b) : GL (Fin (b.1 - predCut I b.1)) K) ≠ 1 := hj
    by_cases hk2 : 2 ≤ b.1 - predCut I b.1
    · have hK4 := four_le_card_of_unitaryFieldData_two h
      obtain ⟨-, hQS, hpZ, hpQ, h3Q⟩ := slBlock_data hk2 (Or.inr hK4) hp hnd hxb hxb1
      exact ⟨hQS, hpZ, hpQ, h3Q⟩
    · exfalso
      exact hxb1 (eq_one_of_det_eq_one_of_eq_one (by omega) _
        (det_eq_one_of_pow_eq_one hp hnd hxb))

end Levi

end KPLeviSub

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
