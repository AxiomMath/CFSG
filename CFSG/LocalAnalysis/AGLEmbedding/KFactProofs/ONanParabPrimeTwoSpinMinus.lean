module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwo
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSpinMinus

public section

namespace CFSG.AGLEmbedding.ParabPrime

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabHub CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.OddCT CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.CentralExt CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem
open scoped commutatorElement

private theorem not_dvd_of_dvd_two_mul_three {m a b p : ℕ} (hm : m ∣ 2 ^ a * 3 ^ b)
    (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ p ∣ m := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 (h.trans hm) with h2 | h3
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2)
    omega
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h3)
    omega

section Rels

variable {K : Type*} [Group K]

theorem rankOne_perfect_of_rankOneRels {D : UniversalRootDatum K} {i : Fin D.rank}
    {k : Type} [Field k] [Finite k] (R : RankOneRels K k)
    (hX : ∀ g, g ∈ D.rootGroup (Pi.single i 1) ↔ ∃ t, R.x t = g)
    (hY : ∀ g, g ∈ D.rootGroup (-Pi.single i 1) ↔ ∃ t, R.y t = g) (hk4 : 4 ≤ Nat.card k) :
    ⁅rankOne D.rootGroup i, rankOne D.rootGroup i⁆ = rankOne D.rootGroup i := by
  have hL : rankOne D.rootGroup i = R.sub := by
    refine le_antisymm (sup_le (fun g hg => ?_) (fun g hg => ?_)) ?_
    · obtain ⟨t, rfl⟩ := (hX g).1 hg
      exact R.x_mem_sub t
    · obtain ⟨t, rfl⟩ := (hY g).1 hg
      exact Subgroup.subset_closure (Or.inr ⟨t, rfl⟩)
    · rw [RankOneRels.sub, Subgroup.closure_le]
      rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩)
      · exact le_sup_left (a := D.rootGroup (Pi.single i 1)) ((hX _).2 ⟨t, rfl⟩)
      · exact le_sup_right (b := D.rootGroup (-Pi.single i 1)) ((hY _).2 ⟨t, rfl⟩)
  obtain ⟨t, ht0, ht2⟩ := CFSG.ClassicalModels.exists_ne_zero_sq_ne_one_of_four_le_card k hk4
  have hh : R.h t ∈ rankOne D.rootGroup i := hL ▸ R.h_mem_sub t
  have hne : t ^ 2 - 1 ≠ 0 := fun h => ht2 (sub_eq_zero.1 h)
  have hne' : (t ^ 2)⁻¹ - 1 ≠ 0 := by
    intro h
    apply ht2
    have := sub_eq_zero.1 h
    exact inv_eq_one.1 this
  have key : R.sub ≤ ⁅rankOne D.rootGroup i, rankOne D.rootGroup i⁆ := by
    rw [RankOneRels.sub, Subgroup.closure_le]
    rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · have hxa : R.x a = ⁅R.h t, R.x (a / (t ^ 2 - 1))⁆ := by
        rw [commutatorElement_def, R.h_conj_x ht0, ← R.x_neg, ← R.x_add]
        congr 1
        field_simp
        ring
      rw [SetLike.mem_coe, hxa]
      exact Subgroup.commutator_mem_commutator hh (hL ▸ R.x_mem_sub _)
    · have hya : R.y a = ⁅R.h t, R.y (a / ((t ^ 2)⁻¹ - 1))⁆ := by
        rw [commutatorElement_def, R.h_conj_y ht0, ← R.y_neg, ← R.y_add]
        congr 1
        field_simp
        ring
      rw [SetLike.mem_coe, hya]
      exact Subgroup.commutator_mem_commutator hh
        (hL ▸ Subgroup.subset_closure (Or.inr ⟨_, rfl⟩))
  exact le_antisymm (commutator_self_le _) (hL.le.trans key)

end Rels

section Minus

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

include hirr in
omit [CharP F 2] in
theorem spinMinus_long_card (hF : Nat.card F = 2) {k : Fin (n - 1)} (hk : k.val + 1 < n - 1) :
    Nat.card ↥(rankOne (minusDatum n hirr).rootGroup k) = 6 := by
  let e : ↥(rankOne (minusDatum n hirr).rootGroup k) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (MulEquiv.subgroupCongr (rankOne_minusRootGroup_of_lt n hirr hk)).trans
      (MonoidHom.ofInjective (SpinFrame.longSL2_injective _ (succ_ne_of_lt n hk) true false)).symm
  rw [Nat.card_congr e.toEquiv, card_sl2, hF]
  norm_num

include hirr in
omit [CharP F 2] in
theorem spinMinus_short_perfect (hF : Nat.card F = 2) {k : Fin (n - 1)}
    (hk : ¬k.val + 1 < n - 1) :
    ⁅rankOne (minusDatum n hirr).rootGroup k, rankOne (minusDatum n hirr).rootGroup k⁆ =
      rankOne (minusDatum n hirr).rootGroup k := by
  have := fact_shortField hirr
  have := finite_shortField (b := b) (c := c)
  have hk4 : 4 ≤ Nat.card (ShortField b c) := by
    rw [SpinMinusClosed.card_shortField, hF]
    norm_num
  exact rankOne_perfect_of_rankOneRels (shortRels n hirr k) (mem_minusRootGroup_single_iff hirr hk)
    (mem_minusRootGroup_neg_single_iff hirr hk) hk4

omit [Finite F] [CharP F 2] in
theorem spinMinus_card_range_longRoot (hF : Nat.card F = 2) {i j : Fin (n - 1)} (hij : i ≠ j)
    (s t : Bool) :
    Nat.card ↥((minusFrame n b c).longRoot hij s t).range = 2 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective
    ((minusFrame n b c).longRoot_injective hij s t)).toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative F ≃ F), hF]

include hirr in
omit [Finite F] [CharP F 2] in
theorem spinMinus_pair_perfect {w : Fin (n - 1) → spinGroup (quadMinus n F b c)}
    {T : Fin (n - 1) → Subgroup (spinGroup (quadMinus n F b c))}
    (hct : IsCTGroupDatum (coxeterMatrix (minusDatum n hirr).isFiniteType).toCoxeterSystem
      (weylAction (minusDatum n hirr).isFiniteType) (minusDatum n hirr).roots
      (minusDatum n hirr).rootGroup w T)
    (hext : SteinbergExtras (minusDatum n hirr) w T) (hF : Nat.card F = 2)
    {i j : Fin (n - 1)} (hij : i.val + 1 = j.val) (hj2 : j.val + 1 < n - 1) :
    ⁅rankOne (minusDatum n hirr).rootGroup i ⊔ rankOne (minusDatum n hirr).rootGroup j,
        rankOne (minusDatum n hirr).rootGroup i ⊔ rankOne (minusDatum n hirr).rootGroup j⁆ =
      rankOne (minusDatum n hirr).rootGroup i ⊔ rankOne (minusDatum n hirr).rootGroup j := by
  have hi1 : i.val + 1 < n - 1 := by omega
  obtain rfl : j = ⟨i.val + 1, hi1⟩ := Fin.ext hij.symm
  have hne : i ≠ ⟨i.val + 1, hi1⟩ := succ_ne_of_lt n hi1
  have hik : i ≠ ⟨i.val + 1 + 1, hj2⟩ := Fin.ne_of_val_ne (by show i.val ≠ i.val + 1 + 1; omega)
  have hAij : (minusDatum n hirr).cartan i ⟨i.val + 1, hi1⟩ = -1 := cartanB_of_succ rfl
  have hAji : (minusDatum n hirr).cartan ⟨i.val + 1, hi1⟩ i = -1 := by
    change cartanB (n - 1) ⟨i.val + 1, hi1⟩ i = -1
    rw [cartanB_of_pred (by rfl)]
    split_ifs with h
    · exfalso
      change i.val + 1 + 1 = n - 1 at h
      omega
    · rfl
  have hX : ∀ {k : Fin (n - 1)} (hk : k.val + 1 < n - 1),
      Nat.card ↥((minusDatum n hirr).rootGroup (Pi.single k 1)) = 2 ∧
        Nat.card ↥((minusDatum n hirr).rootGroup (-Pi.single k 1)) = 2 := by
    intro k hk
    exact ⟨by
      change Nat.card ↥(minusRootGroup n hirr (Pi.single k 1)) = 2
      rw [minusRootGroup_single_of_lt n hirr hk]
      exact spinMinus_card_range_longRoot hF _ true false, by
      change Nat.card ↥(minusRootGroup n hirr (-Pi.single k 1)) = 2
      rw [minusRootGroup_neg_single_of_lt n hirr hk]
      exact spinMinus_card_range_longRoot hF _ true false⟩
  have hnc : ∃ x ∈ (minusDatum n hirr).rootGroup (Pi.single i 1),
      ∃ y ∈ (minusDatum n hirr).rootGroup (Pi.single (⟨i.val + 1, hi1⟩ : Fin (n - 1)) 1),
        ⁅x, y⁆ ≠ 1 := by
    refine ⟨(minusFrame n b c).longRoot hne true false (.ofAdd (1 : F)), ?_,
      (minusFrame n b c).longRoot (succ_ne_of_lt n hj2) true false (.ofAdd (1 : F)), ?_, ?_⟩
    · change _ ∈ minusRootGroup n hirr (Pi.single i 1)
      rw [minusRootGroup_single_of_lt n hirr hi1]
      exact ⟨_, rfl⟩
    · change _ ∈ minusRootGroup n hirr (Pi.single (⟨i.val + 1, hi1⟩ : Fin (n - 1)) 1)
      rw [minusRootGroup_single_of_lt n hirr hj2]
      exact ⟨_, rfl⟩
    · have hcomm : ⁅(minusFrame n b c).longRoot hne true false (.ofAdd (1 : F)),
          (minusFrame n b c).longRoot (succ_ne_of_lt n hj2) true false (.ofAdd (1 : F))⁆ =
          (minusFrame n b c).longRoot hik true false (.ofAdd ((1 : F) * 1)) :=
        (minusFrame n b c).commutator_longRoot_longRoot hne (succ_ne_of_lt n hj2) hik true false
          false 1 1
      rw [hcomm]
      intro h
      have h1 := (minusFrame n b c).longRoot_injective hik true false
        (h.trans (map_one ((minusFrame n b c).longRoot hik true false)).symm)
      exact absurd (by simpa using congrArg Multiplicative.toAdd h1 : (1 : F) = 0) one_ne_zero
  exact commutator_rankOne_sup_eq hct hext hne hAij hAji (hX hi1).1 (hX hi1).2 (hX hj2).1
    (hX hj2).2 hnc

include hirr in
omit [CharP F 2] in
theorem twoLevi_spinMinus {w : Fin (n - 1) → spinGroup (quadMinus n F b c)}
    {T : Fin (n - 1) → Subgroup (spinGroup (quadMinus n F b c))}
    (hct : IsCTGroupDatum (coxeterMatrix (minusDatum n hirr).isFiniteType).toCoxeterSystem
      (weylAction (minusDatum n hirr).isFiniteType) (minusDatum n hirr).roots
      (minusDatum n hirr).rootGroup w T)
    (hext : SteinbergExtras (minusDatum n hirr) w T) (hF : Nat.card F = 2) :
    TwoLevi (minusDatum n hirr) (fun _ _ => False) := by
  refine TwoLevi.of_pair (fun i => ?_) (fun i j hij hcart hi hj => ?_)
  · by_cases hk : i.val + 1 < n - 1
    · exact Or.inr (fun p hp hp5 => not_dvd_of_dvd_two_mul_three (a := 1) (b := 1)
        ((dvd_of_eq (spinMinus_long_card hirr hF hk)).trans (by norm_num)) hp hp5)
    · exact Or.inl (spinMinus_short_perfect hirr hF hk)
  · have hi' : i.val + 1 < n - 1 := by
      by_contra hk
      exact hi (spinMinus_short_perfect hirr hF hk)
    have hj' : j.val + 1 < n - 1 := by
      by_contra hk
      exact hj (spinMinus_short_perfect hirr hF hk)
    have hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val := by
      by_contra hno
      exact hcart (cartanB_of_far hij (fun h => hno (Or.inl h)) (fun h => hno (Or.inr h)))
    rcases hadj with h | h
    · exact spinMinus_pair_perfect hirr hct hext hF h hj'
    · rw [sup_comm]
      exact spinMinus_pair_perfect hirr hct hext hF h hi'

include hirr in
theorem parabCore_spinMinus_two (hF : Nat.card F = 2) (hn : 4 ≤ n) {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* StatedProj (StatedOmega (StatedQuadMinus n F b c))) : ParabCore Y 2 := by
  have : Finite (spinGroup (quadMinus n F b c)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadMinus hirr)
  have h := borelQuotient_spinMinus hirr hn e
  exact h.parabCore_two (by rw [hF]; norm_num) (twoLevi_spinMinus hirr h.ct h.extras hF)

end Minus

theorem parabCore_of_model_pomegaMinus_two {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (h : StatedClassicalModel Y .POmegaMinus n 2 1) : ParabCore Y 2 := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, b, c, hirr, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
  exact parabCore_spinMinus_two hirr (by simpa using hcard) (by omega) e

end CFSG.AGLEmbedding.ParabPrime
