module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54Odd

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

private theorem isCyclic_prod_of_subsingleton {A B : Type*} [Group A] [Group B] [IsCyclic A]
    [Subsingleton B] : IsCyclic (A × B) := by
  haveI : Unique B := ⟨⟨1⟩, fun b => Subsingleton.elim _ _⟩
  exact isCyclic_of_surjective (MulEquiv.prodUnique (M := A) (N := B)).symm.toMonoidHom
    (MulEquiv.prodUnique (M := A) (N := B)).symm.surjective

private theorem gcd_four_pow_sub_one {q n : ℕ} (hq1 : 1 ≤ q) (hq : 4 ∣ q - 1) :
    Nat.gcd 4 (q ^ n - 1) = 4 := by
  apply Nat.gcd_eq_left
  have hmod : (1 : ℕ) ≡ q [MOD 4] := (Nat.modEq_iff_dvd' hq1).mpr hq
  have hpow : (1 : ℕ) ≡ q ^ n [MOD 4] := by simpa using hmod.pow n
  exact (Nat.modEq_iff_dvd' (one_le_pow₀ hq1)).mp hpow

private theorem modEq_three_pow_odd {n : ℕ} (hn : Odd n) : 3 ^ n ≡ 3 [MOD 4] := by
  obtain ⟨k, rfl⟩ := hn
  have h9 : 3 ^ 2 ≡ 1 [MOD 4] := by decide
  calc 3 ^ (2 * k + 1) = 3 * (3 ^ 2) ^ k := by rw [pow_succ, pow_mul, mul_comm]
    _ ≡ 3 * 1 ^ k [MOD 4] := (Nat.ModEq.refl 3).mul (h9.pow k)
    _ = 3 := by simp

private theorem gcd_four_pow_add_one {q n : ℕ} (hq : 4 ∣ q + 1) (hn : Odd n) :
    Nat.gcd 4 (q ^ n + 1) = 4 := by
  apply Nat.gcd_eq_left
  have hq0 : q + 1 ≡ 0 [MOD 4] := (Nat.modEq_zero_iff_dvd).mpr hq
  have h4zero : (3 : ℕ) + 1 ≡ 0 [MOD 4] := by
    have : (4 : ℕ) ≡ 0 [MOD 4] := (Nat.modEq_zero_iff_dvd).mpr (dvd_refl 4)
    simpa using this
  have hq3 : q ≡ 3 [MOD 4] := Nat.ModEq.add_right_cancel' 1 (hq0.trans h4zero.symm)
  have hqn : q ^ n ≡ 3 [MOD 4] := (hq3.pow n).trans (modEq_three_pow_odd hn)
  have hzero : q ^ n + 1 ≡ 0 [MOD 4] := by
    have h : q ^ n + 1 ≡ 3 + 1 [MOD 4] :=
      hqn.add (Nat.ModEq.refl 1 : (1 : ℕ) ≡ 1 [MOD 4])
    exact h.trans h4zero
  exact (Nat.modEq_zero_iff_dvd).mp hzero

private theorem exists_generator_four {G : Type*} [Group G] (M : Subgroup G) [Finite M]
    (hc : IsCyclic M) (h4 : Nat.card M = 4) :
    ∃ ζ : G, ζ ∈ M ∧ orderOf ζ = 4 ∧ ∀ u ∈ M, ∃ k : ℕ, u = ζ ^ k := by
  classical
  obtain ⟨ζ', hζ'⟩ := IsCyclic.exists_monoid_generator (α := M)
  refine ⟨(ζ' : G), ζ'.2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_powers hζ', h4]
  · intro u hu
    have hmem : (⟨u, hu⟩ : M) ∈ Submonoid.powers ζ' := hζ' ⟨u, hu⟩
    rw [Submonoid.mem_powers_iff] at hmem
    obtain ⟨k, hk⟩ := hmem
    exact ⟨k, by
      have := congrArg (Subtype.val) hk.symm
      simpa using this⟩

private theorem finish_cyclic_four
    (hG : CFSG.ComponentClassification.HarrisLit.T1.P54.GriessNativeTable)
    {S : Type} [Group S] [Finite S] {t : CFSG.Open.StatedLieTag} {n p f : ℕ}
    (hLie : CFSG.Blueprint.LieModel S t n p f)
    (hg : CFSG.Blueprint.Multiplier.genericOrders t n p f = (4, 1))
    (he : CFSG.Blueprint.Multiplier.exceptionalOrders t n p f = (1, 1)) :
    Group.IsPerfect S ∧ ∃ ζ : CFSG.RankThree.PerfectCover.HopfCover S,
      ζ ∈ CFSG.RankThree.PerfectCover.hopfMultiplier S ∧ orderOf ζ = 4 ∧
      ∀ u ∈ CFSG.RankThree.PerfectCover.hopfMultiplier S, ∃ k : ℕ, u = ζ ^ k := by
  classical
  obtain ⟨hcomm, ⟨eM⟩⟩ := hG S t n p f hLie
  have hperf : Group.IsPerfect S := ⟨hcomm⟩
  let e : CFSG.RankThree.PerfectCover.hopfMultiplier S ≃*
      CFSG.Blueprint.Multiplier.generic t n p f ×
        CFSG.Blueprint.Multiplier.exceptional t n p f :=
    (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess S).symm.trans eM
  have hcard : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier S) = 4 := by
    rw [Nat.card_congr e.toEquiv]
    unfold CFSG.Blueprint.Multiplier.generic CFSG.Blueprint.Multiplier.exceptional
    rw [hg, he]
    simp [Nat.card_prod, Nat.card_congr Multiplicative.toAdd]
  have hcyc : IsCyclic (CFSG.RankThree.PerfectCover.hopfMultiplier S) := by
    haveI : Subsingleton (CFSG.Blueprint.Multiplier.exceptional t n p f) := by
      unfold CFSG.Blueprint.Multiplier.exceptional
      rw [he]
      infer_instance
    haveI : IsCyclic (CFSG.Blueprint.Multiplier.generic t n p f) := by
      unfold CFSG.Blueprint.Multiplier.generic
      rw [hg]
      exact isCyclic_prod_of_subsingleton
    haveI : IsCyclic (CFSG.Blueprint.Multiplier.generic t n p f ×
        CFSG.Blueprint.Multiplier.exceptional t n p f) := isCyclic_prod_of_subsingleton
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  haveI : Finite (CFSG.RankThree.PerfectCover.hopfMultiplier S) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨ζ, hζmem, hζord, hζgen⟩ :=
    exists_generator_four (CFSG.RankThree.PerfectCover.hopfMultiplier S) hcyc hcard
  exact ⟨hperf, ζ, hζmem, hζord, hζgen⟩

theorem l2_hopf_cyclic_four (hG : CFSG.ComponentClassification.HarrisLit.T1.P54.GriessNativeTable)
    {S : Type} [Group S] [Finite S] {n p f : ℕ} (hn : Odd n)
    (hX : (4 ∣ p ^ f - 1 ∧ CFSG.Blueprint.LieModel S .POmegaPlus n p f) ∨
      (4 ∣ p ^ f + 1 ∧ CFSG.Blueprint.LieModel S .POmegaMinus n p f)) :
    Group.IsPerfect S ∧ ∃ ζ : CFSG.RankThree.PerfectCover.HopfCover S,
      ζ ∈ CFSG.RankThree.PerfectCover.hopfMultiplier S ∧ orderOf ζ = 4 ∧
      ∀ u ∈ CFSG.RankThree.PerfectCover.hopfMultiplier S, ∃ k : ℕ, u = ζ ^ k := by
  classical
  have hn0 : n ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hn
  rcases hX with ⟨h4, hLi⟩ | ⟨h4, hLi⟩
  ·
    obtain ⟨hadm, -⟩ := hLi.statedClassicalModel_of_ne_zero hn0
    have hp : p.Prime := hadm.1
    have hq1 : 1 ≤ p ^ f := by
      have : 0 < p ^ f := pow_pos hp.pos f
      omega
    have hqmod4 : p ^ f % 4 = 1 := by
      have h : 1 % 4 = p ^ f % 4 := (Nat.modEq_iff_dvd' hq1).mpr h4
      norm_num at h
      exact h.symm
    have hqEven : ¬ Even (p ^ f) := by
      rw [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
      have := Nat.odd_of_mod_four_eq_one hqmod4
      omega
    have hnEven : ¬ Even n := by
      rintro ⟨l, hl⟩
      obtain ⟨k, hk⟩ := hn
      omega
    have hgen : CFSG.Blueprint.Multiplier.genericOrders .POmegaPlus n p f = (4, 1) := by
      have hg : CFSG.Blueprint.Multiplier.genericOrders .POmegaPlus n p f =
          (if Even (p ^ f) then (1, 1) else if Even n then (2, 2) else
            (Nat.gcd 4 ((p ^ f) ^ n - 1), 1)) := by
        simp [CFSG.Blueprint.Multiplier.genericOrders]
      rw [hg, if_neg hqEven, if_neg hnEven, gcd_four_pow_sub_one hq1 h4]
    have hn4 : n ≠ 4 := by
      rintro rfl
      obtain ⟨k, hk⟩ := hn
      omega
    have hex : CFSG.Blueprint.Multiplier.exceptionalOrders .POmegaPlus n p f = (1, 1) := by
      have he : CFSG.Blueprint.Multiplier.exceptionalOrders .POmegaPlus n p f =
          (if n = 4 ∧ p = 2 ∧ f = 1 then (2, 2) else (1, 1)) := by
        unfold CFSG.Blueprint.Multiplier.exceptionalOrders
        split_ifs <;> simp_all
      rw [he]
      simp [hn4]
    exact finish_cyclic_four hG hLi hgen hex
  ·
    have hgen : CFSG.Blueprint.Multiplier.genericOrders .POmegaMinus n p f = (4, 1) := by
      have hg : CFSG.Blueprint.Multiplier.genericOrders .POmegaMinus n p f =
          (Nat.gcd 4 ((p ^ f) ^ n + 1), 1) := by
        simp [CFSG.Blueprint.Multiplier.genericOrders]
      rw [hg, gcd_four_pow_add_one h4 hn]
    have hex : CFSG.Blueprint.Multiplier.exceptionalOrders .POmegaMinus n p f = (1, 1) := by
      unfold CFSG.Blueprint.Multiplier.exceptionalOrders
      split <;> simp_all
    exact finish_cyclic_four hG hLi hgen hex

end CFSG.OddStandard.HigherRank.YamadaG23
