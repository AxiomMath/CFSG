module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.HeartFix

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open Equiv Equiv.Perm CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

variable {n : ℕ}

theorem mk_pairEW_self (k : Fin n) : (pairEW k k : altHeart n) = 0 := by
  have h : pairEW k k = 0 := Subtype.ext <| funext fun p => by
    rw [pairEW_apply, zmod2_add_self]
    rfl
  rw [h, QuotientAddGroup.mk_zero]

theorem altHeart_add_self (y : altHeart n) : y + y = 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [← QuotientAddGroup.mk_add]
  have : x + x = 0 := Subtype.ext (funext fun i => zmod2_add_self _)
  rw [this, QuotientAddGroup.mk_zero]

theorem exists_altHeartCoord_eq (k : Fin n) (w : Fin n → ZMod 2) (hk : w k = 0)
    (hw : Odd n ∨ ∑ i, w i = 0) : ∃ z : altHeart n, altHeartCoord k z = w := by
  by_cases hs : ∑ i, w i = 0
  · have hmem : w ∈ evenWeight n := by
      rw [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply]
      exact hs
    refine ⟨((⟨w, hmem⟩ : evenWeight n) : altHeart n), funext fun i => ?_⟩
    rw [altHeartCoord_mk]
    simp [hk]
  · have hodd : Odd n := hw.resolve_right hs
    have hs1 : ∑ i, w i = 1 := (zmod_two_cases _).resolve_left hs
    have hn1 : ((n : ℕ) : ZMod 2) = 1 := (ZMod.natCast_eq_one_iff_odd).2 hodd
    have hmem : w + allOnes n ∈ evenWeight n := by
      rw [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply]
      simp only [Pi.add_apply, Finset.sum_add_distrib, hs1, allOnes, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, hn1]
      decide
    refine ⟨((⟨w + allOnes n, hmem⟩ : evenWeight n) : altHeart n), funext fun i => ?_⟩
    rw [altHeartCoord_mk]
    simp [hk, allOnes]

private theorem zmod2_add_eq_sub_add (p q r : ZMod 2) : p + q = (p + r) - (q + r) := by
  revert p q r; decide

theorem altCocycle_cases (hn : 7 ≤ n) (k : Fin n) (c : Perm (Fin n) → altHeart n)
    (hc : ∀ σ ∈ alternatingGroup (Fin n), ∀ τ ∈ alternatingGroup (Fin n),
      c (σ * τ) = c σ + altAct σ (c τ)) :
    ∃ z : altHeart n, (∀ g ∈ alternatingGroup (Fin n), c g = altAct g z - z) ∨
      ∀ g ∈ alternatingGroup (Fin n), c g = altAct g z - z + (pairEW k (g k) : altHeart n) := by
  classical
  obtain ⟨x, hx⟩ := exists_cobound_of_cocycle_stab hn k (fun σ => altHeartCoord k (c σ))
    fun σ hσ hσk τ hτ _ i => by
      simp only [hc σ hσ τ hτ, map_add, Pi.add_apply, altHeartCoord_altAct hσk]
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : altHeart n, ∀ g ∈ alternatingGroup (Fin n), g k = k →
      c g = altAct g z₀ - z₀ := by
    set b : ZMod 2 := if Even n then ∑ i ∈ Finset.univ.erase k, x i else 0 with hb
    have hpar : Odd n ∨ ∑ i, (fun i => if i = k then 0 else x i + b) i = 0 := by
      rcases Nat.even_or_odd n with he | ho
      · right
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), ite_eq_left rfl, zero_add,
          Finset.sum_congr rfl (fun i hi => ite_eq_right (Finset.ne_of_mem_erase hi)),
          Finset.sum_add_distrib, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ k),
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have h1 : ((n - 1 : ℕ) : ZMod 2) = 1 := by
          rw [ZMod.natCast_eq_one_iff_odd]
          obtain ⟨m, hm⟩ := he
          exact ⟨m - 1, by omega⟩
        rw [h1, one_mul, hb, ite_eq_left he, zmod2_add_self]
      · exact Or.inl ho
    obtain ⟨z₀, hz₀⟩ := exists_altHeartCoord_eq k (fun i => if i = k then 0 else x i + b)
      (ite_eq_left rfl) hpar
    refine ⟨z₀, fun g hg hgk => altHeartCoord_injective k (funext fun i => ?_)⟩
    rw [map_sub, Pi.sub_apply, altHeartCoord_altAct hgk, hz₀]
    have hxi : altHeartCoord k (c g) i = x (g⁻¹ i) + x i := hx g hg hgk i
    rw [hxi]
    by_cases hik : i = k
    · have hgi : g⁻¹ i = k := by rw [hik, Perm.inv_eq_iff_eq, hgk]
      rw [hgi, hik, sub_self, zmod2_add_self]
    · have hgi : g⁻¹ i ≠ k := fun h => hik (by rw [← perm_apply_inv_apply g i, h, hgk])
      simp only [ite_eq_right hgi, ite_eq_right hik]
      exact zmod2_add_eq_sub_add _ _ _
  set c' : Perm (Fin n) → altHeart n := fun g => c g - (altAct g z₀ - z₀) with hc'
  have hc'c : ∀ σ ∈ alternatingGroup (Fin n), ∀ τ ∈ alternatingGroup (Fin n),
      c' (σ * τ) = c' σ + altAct σ (c' τ) := by
    intro σ hσ τ hτ
    simp only [hc', hc σ hσ τ hτ, map_sub, altAct_mul]
    abel
  have hc'k : ∀ g ∈ alternatingGroup (Fin n), g k = k → c' g = 0 := fun g hg hgk => by
    simp only [hc', hz₀ g hg hgk, sub_self]
  have hc'1 : c' 1 = 0 := by
    have h := hc'c 1 (one_mem _) 1 (one_mem _)
    rw [mul_one, altAct_one] at h
    exact left_eq_add.1 h
  have hdep : ∀ g ∈ alternatingGroup (Fin n), ∀ g' ∈ alternatingGroup (Fin n), g k = g' k →
      c' g = c' g' := by
    intro g hg g' hg' hgg'
    have hs : g⁻¹ * g' ∈ alternatingGroup (Fin n) := mul_mem (inv_mem hg) hg'
    have hsk : (g⁻¹ * g') k = k := by rw [Perm.mul_apply, ← hgg', perm_inv_apply_apply]
    have h := hc'c g hg (g⁻¹ * g') hs
    rw [mul_inv_cancel_left, hc'k _ hs hsk, map_zero, add_zero] at h
    exact h.symm
  obtain ⟨x₀, hx₀k, -, -, -⟩ := exists_ne_four (by omega : 5 ≤ n) k k k k
  obtain ⟨p, hpk, hpx, -, -⟩ := exists_ne_four (by omega : 5 ≤ n) k x₀ x₀ x₀
  obtain ⟨q, hqk, hqx, hqp, -⟩ := exists_ne_four (by omega : 5 ≤ n) k x₀ p p
  set τ : Perm (Fin n) := swap k x₀ * swap p q with hτ
  have hτA : τ ∈ alternatingGroup (Fin n) := by
    rw [mem_alternatingGroup, hτ, map_mul, sign_swap (Ne.symm hx₀k), sign_swap (Ne.symm hqp)]
    decide
  have hτk : τ k = x₀ := by
    rw [hτ, Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hpk) (Ne.symm hqk), swap_apply_left]
  have hττ : τ * τ = 1 := by
    have hnd : [k, x₀, p, q].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, and_true, not_false_eq_true]
      exact ⟨⟨Ne.symm hx₀k, Ne.symm hpk, Ne.symm hqk⟩, ⟨Ne.symm hpx, Ne.symm hqx⟩, Ne.symm hqp⟩
    have hcomm : Commute (swap p q) (swap k x₀) :=
      (Perm.disjoint_swap_swap hnd).commute.symm
    rw [hτ, hcomm.mul_mul_mul_comm, swap_mul_self, swap_mul_self, one_mul]
  set y₀ := c' τ with hy₀def
  have hy₀τ : altAct τ y₀ = y₀ := by
    have h := hc'c τ hτA τ hτA
    rw [hττ, hc'1] at h
    have h2 := altHeart_add_self y₀
    exact add_left_cancel (h.symm.trans h2.symm)
  have hy₀fix : ∀ σ : alternatingGroup (Fin n), (σ : Perm (Fin n)) k = k →
      (σ : Perm (Fin n)) x₀ = x₀ → altAct (σ : Perm (Fin n)) y₀ = y₀ := by
    intro σ hσk hσx
    have h := hc'c σ σ.2 τ hτA
    rw [hc'k σ σ.2 hσk, zero_add] at h
    rw [← h]
    exact hdep _ (mul_mem σ.2 hτA) _ hτA (by rw [Perm.mul_apply, hτk, hσx])
  have hy₀ : y₀ = 0 ∨ y₀ = (pairEW k x₀ : altHeart n) := by
    by_cases h0 : y₀ = 0
    · exact Or.inl h0
    right
    rcases Nat.even_or_odd n with he | ho
    · exact heart_eq_pair_of_fix_two he (by omega) (Ne.symm hx₀k) h0 hy₀fix
    · exact heart_eq_pair_of_fix_two_swap ho (by omega) (Ne.symm hx₀k) hpk hpx hqk hqx h0
        hy₀fix hy₀τ
  have hprop : ∀ g ∈ alternatingGroup (Fin n), g k ≠ k → ∃ s ∈ alternatingGroup (Fin n),
      s k = k ∧ s x₀ = g k ∧ c' g = altAct s y₀ := by
    intro g hg hgk
    obtain ⟨s, hs, hsk, hsx⟩ := exists_alt_fix_apply_eq (by omega) hx₀k hgk
    refine ⟨s, hs, hsk, hsx, ?_⟩
    have h := hc'c s hs τ hτA
    rw [hc'k s hs hsk, zero_add] at h
    rw [← h]
    exact hdep g hg _ (mul_mem hs hτA) (by rw [Perm.mul_apply, hτk, hsx])
  have hc_eq : ∀ g, c g = c' g + (altAct g z₀ - z₀) := fun g => (sub_add_cancel _ _).symm
  refine ⟨z₀, ?_⟩
  rcases hy₀ with h0 | h1
  · left
    intro g hg
    rw [hc_eq g]
    by_cases hgk : g k = k
    · rw [hc'k g hg hgk, zero_add]
    · obtain ⟨s, -, -, -, hs⟩ := hprop g hg hgk
      rw [hs, h0, map_zero, zero_add]
  · right
    intro g hg
    have hc'g : c' g = (pairEW k (g k) : altHeart n) := by
      by_cases hgk : g k = k
      · rw [hc'k g hg hgk, hgk, mk_pairEW_self]
      · obtain ⟨s, -, hsk, hsx, hs⟩ := hprop g hg hgk
        rw [hs, h1, altAct_mk, evenWeightPerm_pairEW, hsk, hsx]
    rw [hc_eq g, hc'g]
    exact add_comm _ _

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
