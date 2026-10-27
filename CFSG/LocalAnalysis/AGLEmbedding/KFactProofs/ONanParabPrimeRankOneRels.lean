module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeAbstract
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeRankOne

public section

namespace CFSG.AGLEmbedding.ParabPrime

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
open scoped commutatorElement

variable {K : Type*} [Group K]

theorem rankOneNode_of_rankOneRels {D : UniversalRootDatum K} {i : Fin D.rank} {q : ℕ}
    {k : Type} [Field k] [Finite k] [CharP k 2] (R : RankOneRels K k)
    (hX : ∀ g, g ∈ D.rootGroup (Pi.single i 1) ↔ ∃ t, R.x t = g)
    (hY : ∀ g, g ∈ D.rootGroup (-Pi.single i 1) ↔ ∃ t, R.y t = g)
    (hinj : Function.Injective R.x) (hk : Nat.card k = q ^ 2) : RankOneNode D i q := by
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
  refine ⟨fun h4 => ?_, fun p hp hp5 hpq => ?_⟩
  ·
    have hk4 : 4 ≤ Nat.card k := by
      rw [hk]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left (by omega) 2
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
  ·
    have : Fact p.Prime := ⟨hp⟩
    have hcard : p ∣ Nat.card kˣ := by
      rw [Nat.card_units, hk]
      exact hpq
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' p hcard
    have ht0 : (t : k) ≠ 0 := t.ne_zero
    have htp : t ^ p = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
    have htpk : (t : k) ^ p = 1 := by
      have := congrArg Units.val htp
      simpa using this
    have hpow : ∀ m : ℕ, R.h ((t : k) ^ (m + 1)) = R.h t ^ (m + 1) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ _ (m + 1), R.h_mul (pow_ne_zero _ ht0) ht0, ih, pow_succ _ (m + 1)]
    have hxp : R.h t ^ p = 1 := by
      obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.pos; omega⟩
      rw [hm, ← hpow m, ← hm, htpk, R.h_one]
    have hnc : R.h t ∉ Subgroup.center K := by
      intro hc
      have hcomm := Subgroup.mem_center_iff.1 hc (R.x 1)
      have h1 := R.h_mul_x ht0 1
      rw [← hcomm] at h1
      have h2 : R.x 1 = R.x ((t : k) ^ 2 * 1) := mul_right_cancel h1
      have h3 : (t : k) ^ 2 = 1 := by simpa using (hinj h2).symm
      have h4 : ((t : k) - 1) ^ 2 = 0 := by
        have h2' : (2 : k) = 0 := CharTwo.two_eq_zero
        linear_combination h3 + (1 - (t : k)) * h2'
      have h5 : (t : k) = 1 := sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h4)
      have h6 : t = 1 := Units.ext h5
      rw [h6, orderOf_one] at ht
      exact hp.one_lt.ne ht
    have hx1 : R.h t ≠ 1 := fun h => hnc (h ▸ Subgroup.one_mem _)
    exact ⟨R.h t, hL ▸ R.h_mem_sub t, orderOf_eq_prime hxp hx1, hnc⟩

end CFSG.AGLEmbedding.ParabPrime
