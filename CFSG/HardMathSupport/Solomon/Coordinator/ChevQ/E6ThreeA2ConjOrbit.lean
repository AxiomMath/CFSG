module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInnerLine
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsWeyl
public import CFSG.LieType.Chevalley.CLSOddE7RationalEightGroup

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

set_option linter.unusedSectionVars false

local instance e6ConjOrbitNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

@[expose] def e6Sact (k : Fin Tag.E6.rank) (x : Fin Tag.E6.rank → ZMod 3) :
    Fin Tag.E6.rank → ZMod 3 :=
  fun j => x j - ((Tag.E6.cartan k j : ℤ) : ZMod 3) * x k

@[expose] def e6Wact (l : List (Fin Tag.E6.rank)) (x : Fin Tag.E6.rank → ZMod 3) :
    Fin Tag.E6.rank → ZMod 3 :=
  l.foldr e6Sact x

@[expose] def e6KacVec : Fin Tag.E6.rank → ZMod 3 := ![0, 0, 0, 1, 0, 0]

@[expose] def e6KerCount (x : Fin Tag.E6.rank → ZMod 3) : ℕ :=
  ((rootFinset .E6).filter fun α => ∑ i, x i * ((α i : ℤ) : ZMod 3) = 0).card

@[expose] def e6ConjVec (a b c d e f : ZMod 3) : Fin Tag.E6.rank → ZMod 3 := ![a, b, c, d, e, f]

@[expose] def e6OrbitTable : List ((Fin Tag.E6.rank → ZMod 3) × List (Fin 6)) :=
  [
    (e6ConjVec 0 0 0 1 0 0, []), (e6ConjVec 0 1 1 2 1 0, [3]), (e6ConjVec 0 2 1 0 1 0, [3, 1]),
    (e6ConjVec 1 1 2 0 1 0, [3, 2]), (e6ConjVec 0 1 1 0 2 1, [3, 4]),
    (e6ConjVec 1 2 2 1 1 0, [3, 1, 2]), (e6ConjVec 0 2 1 1 2 1, [3, 1, 4]),
    (e6ConjVec 2 1 0 0 1 0, [3, 2, 0]), (e6ConjVec 1 1 2 1 2 1, [3, 2, 4]),
    (e6ConjVec 0 1 1 0 0 2, [3, 4, 5]), (e6ConjVec 2 2 0 1 1 0, [3, 1, 2, 0]),
    (e6ConjVec 1 0 0 2 2 0, [3, 1, 2, 3]), (e6ConjVec 1 2 2 2 2 1, [3, 1, 2, 4]),
    (e6ConjVec 0 0 2 2 0 1, [3, 1, 4, 3]), (e6ConjVec 0 2 1 1 0 2, [3, 1, 4, 5]),
    (e6ConjVec 2 1 0 1 2 1, [3, 2, 0, 4]), (e6ConjVec 1 2 0 2 0 1, [3, 2, 4, 3]),
    (e6ConjVec 1 1 2 1 0 2, [3, 2, 4, 5]), (e6ConjVec 2 0 1 2 2 0, [3, 1, 2, 0, 3]),
    (e6ConjVec 2 2 0 2 2 1, [3, 1, 2, 0, 4]), (e6ConjVec 1 0 0 1 1 2, [3, 1, 2, 3, 4]),
    (e6ConjVec 1 1 1 1 1 1, [3, 1, 2, 4, 3]), (e6ConjVec 1 2 2 2 0 2, [3, 1, 2, 4, 5]),
    (e6ConjVec 2 0 1 1 0 1, [3, 1, 4, 3, 2]), (e6ConjVec 0 0 2 2 1 2, [3, 1, 4, 3, 5]),
    (e6ConjVec 2 2 1 2 0 1, [3, 2, 0, 4, 3]), (e6ConjVec 2 1 0 1 0 2, [3, 2, 0, 4, 5]),
    (e6ConjVec 1 1 0 1 0 1, [3, 2, 4, 3, 1]), (e6ConjVec 1 2 0 2 1 2, [3, 2, 4, 3, 5]),
    (e6ConjVec 0 0 2 0 2 0, [3, 1, 2, 0, 3, 2]), (e6ConjVec 2 0 1 1 1 2, [3, 1, 2, 0, 3, 4]),
    (e6ConjVec 2 1 2 1 1 1, [3, 1, 2, 0, 4, 3]), (e6ConjVec 2 2 0 2 0 2, [3, 1, 2, 0, 4, 5]),
    (e6ConjVec 1 1 1 2 2 2, [3, 1, 2, 3, 4, 3]), (e6ConjVec 1 0 0 1 0 1, [3, 1, 2, 3, 4, 5]),
    (e6ConjVec 1 2 1 2 1 1, [3, 1, 2, 4, 3, 1]), (e6ConjVec 2 1 2 2 1 1, [3, 1, 2, 4, 3, 2]),
    (e6ConjVec 1 1 1 1 2 2, [3, 1, 2, 4, 3, 5]), (e6ConjVec 2 1 1 1 0 1, [3, 2, 0, 4, 3, 1]),
    (e6ConjVec 0 2 2 0 0 1, [3, 2, 0, 4, 3, 2]), (e6ConjVec 2 2 1 2 1 2, [3, 2, 0, 4, 3, 5]),
    (e6ConjVec 1 1 0 1 1 2, [3, 2, 4, 3, 1, 5]), (e6ConjVec 1 2 0 0 2 0, [3, 2, 4, 3, 5, 4]),
    (e6ConjVec 2 1 2 2 2 2, [3, 1, 2, 0, 3, 4, 3]),
    (e6ConjVec 2 2 2 2 1 1, [3, 1, 2, 0, 4, 3, 1]),
    (e6ConjVec 1 1 1 0 1 1, [3, 1, 2, 0, 4, 3, 2]),
    (e6ConjVec 2 1 2 1 2 2, [3, 1, 2, 0, 4, 3, 5]),
    (e6ConjVec 1 2 1 0 2 2, [3, 1, 2, 3, 4, 3, 1]),
    (e6ConjVec 2 1 2 0 2 2, [3, 1, 2, 3, 4, 3, 2]),
    (e6ConjVec 1 1 1 2 1 1, [3, 1, 2, 3, 4, 3, 5]),
    (e6ConjVec 2 2 2 0 1 1, [3, 1, 2, 4, 3, 1, 2]),
    (e6ConjVec 1 2 1 2 2 2, [3, 1, 2, 4, 3, 1, 5]),
    (e6ConjVec 0 1 2 2 0 1, [3, 2, 0, 4, 3, 1, 2]),
    (e6ConjVec 2 1 1 1 1 2, [3, 2, 0, 4, 3, 1, 5]),
    (e6ConjVec 0 2 2 0 1 2, [3, 2, 0, 4, 3, 2, 5]),
    (e6ConjVec 2 2 1 0 2 0, [3, 2, 0, 4, 3, 5, 4]),
    (e6ConjVec 1 1 0 2 2 0, [3, 2, 4, 3, 1, 5, 4]),
    (e6ConjVec 2 2 2 0 2 2, [3, 1, 2, 0, 3, 4, 3, 1]),
    (e6ConjVec 1 2 1 1 1 1, [3, 1, 2, 0, 4, 3, 1, 2]),
    (e6ConjVec 2 2 2 2 2 2, [3, 1, 2, 0, 4, 3, 1, 5]),
    (e6ConjVec 2 1 2 0 1 1, [3, 1, 2, 0, 4, 3, 2, 0]),
    (e6ConjVec 1 1 1 0 2 2, [3, 1, 2, 0, 4, 3, 2, 5]),
    (e6ConjVec 2 2 2 1 2 2, [3, 1, 2, 3, 4, 3, 1, 2]),
    (e6ConjVec 1 2 1 0 1 1, [3, 1, 2, 3, 4, 3, 1, 5]),
    (e6ConjVec 0 0 1 1 2 1, [3, 2, 0, 4, 3, 1, 2, 3]),
    (e6ConjVec 0 1 2 2 1 2, [3, 2, 0, 4, 3, 1, 2, 5]),
    (e6ConjVec 2 1 1 2 2 0, [3, 2, 0, 4, 3, 1, 5, 4]),
    (e6ConjVec 0 2 2 1 2 0, [3, 2, 0, 4, 3, 2, 5, 4]),
    (e6ConjVec 1 0 2 1 1 0, [3, 2, 4, 3, 1, 5, 4, 3]),
    (e6ConjVec 2 2 2 1 1 1, [3, 1, 2, 0, 4, 3, 1, 2, 0]),
    (e6ConjVec 1 0 2 2 2 1, [3, 1, 2, 0, 4, 3, 1, 2, 3]),
    (e6ConjVec 1 2 1 1 2 2, [3, 1, 2, 0, 4, 3, 1, 2, 5]),
    (e6ConjVec 2 0 0 2 0 2, [3, 1, 2, 3, 4, 3, 1, 2, 3]),
    (e6ConjVec 0 0 1 0 1 0, [3, 2, 0, 4, 3, 1, 2, 3, 4]),
    (e6ConjVec 0 0 1 1 0 2, [3, 2, 0, 4, 3, 1, 2, 3, 5]),
    (e6ConjVec 0 1 2 0 2 0, [3, 2, 0, 4, 3, 1, 2, 5, 4]),
    (e6ConjVec 2 0 0 1 1 0, [3, 2, 0, 4, 3, 1, 5, 4, 3]),
    (e6ConjVec 0 0 0 2 0 0, [3, 2, 0, 4, 3, 2, 5, 4, 3]),
    (e6ConjVec 2 0 0 2 2 1, [3, 1, 2, 0, 4, 3, 1, 2, 0, 3]),
    (e6ConjVec 1 0 2 2 0 2, [3, 1, 2, 0, 4, 3, 1, 2, 3, 5])
  ]

theorem e6_orbit_words : ∀ p ∈ e6OrbitTable, e6Wact p.2 p.1 = e6KacVec := by
  decide +kernel

theorem e6_orbit_complete : ∀ a b c d e f : ZMod 3,
    e6KerCount (e6ConjVec a b c d e f) = 18 → ∃ p ∈ e6OrbitTable, p.1 = e6ConjVec a b c d e f := by
  decide +kernel

theorem exists_word_of_kerCount (x : Fin Tag.E6.rank → ZMod 3) (hx : e6KerCount x = 18) :
    ∃ l : List (Fin Tag.E6.rank), e6Wact l x = e6KacVec := by
  have hx' : x = e6ConjVec (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) := by
    funext i
    fin_cases i <;> rfl
  obtain ⟨p, hp, hpx⟩ := e6_orbit_complete (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)
    (by rw [← hx']; exact hx)
  refine ⟨p.2, ?_⟩
  have h := e6_orbit_words p hp
  rw [hpx, ← hx'] at h
  exact h

section Bridge

variable {K : Type} [Field K] {ω : Kˣ}

theorem e6Conj_zpow_val_intCast (h3 : ω ^ 3 = 1) (n : ℤ) : ω ^ ((n : ZMod 3).val) = ω ^ n := by
  have h : (((n : ZMod 3).val : ℕ) : ℤ) = n % 3 := ZMod.val_intCast n
  rw [← zpow_natCast, h]
  conv_rhs => rw [← Int.emod_add_mul_ediv n 3]
  rw [zpow_add, zpow_mul, zpow_ofNat, h3, one_zpow, mul_one]

theorem e6Conj_simple_inv (k : Fin Tag.E6.rank) : (simple .E6 k)⁻¹ = simple .E6 k := by
  unfold simple
  exact (coxeterSystem .E6).inv_simple k

theorem weylTuple_simple_torV (h3 : ω ^ 3 = 1) (k : Fin Tag.E6.rank)
    (x : Fin Tag.E6.rank → ZMod 3) :
    weylTuple (simple .E6 k) (torV ω x) = torV ω (e6Sact k x) := by
  funext i
  rw [weylTuple, e6Conj_simple_inv, simple_smul, rootChar_torV, torV, e6Sact]
  have hsum : ∑ j, ((x j).val : ℤ) * (reflect .E6 k (Pi.single i 1)) j =
      ((x i).val : ℤ) - Tag.E6.cartan k i * ((x k).val : ℤ) := by
    simp only [reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
    simp [Pi.single_apply, mul_comm, mul_left_comm]
  have hn : ((((x i).val : ℤ) - Tag.E6.cartan k i * ((x k).val : ℤ) : ℤ) : ZMod 3) =
      x i - ((Tag.E6.cartan k i : ℤ) : ZMod 3) * x k := by
    push_cast
    simp [ZMod.natCast_val, ZMod.cast_id]
  rw [hsum, ← e6Conj_zpow_val_intCast h3, hn]

theorem weylTuple_prod_torV (h3 : ω ^ 3 = 1) (l : List (Fin Tag.E6.rank))
    (x : Fin Tag.E6.rank → ZMod 3) :
    weylTuple ((l.map (simple .E6)).prod) (torV ω x) = torV ω (e6Wact l x) := by
  induction l with
  | nil => simp [e6Wact, weylTuple_one]
  | cons k l ih =>
    rw [List.map_cons, List.prod_cons, ← weylTuple_weylTuple, ih, weylTuple_simple_torV h3]
    rfl

theorem torV_e6KacVec : torV ω e6KacVec = e6LineChar ω := by
  funext i
  have key : ∀ j : Fin Tag.E6.rank, (e6KacVec j = 0 ∧ e6LineChar ω j = 1) ∨
      (e6KacVec j = 1 ∧ e6LineChar ω j = ω) := by
    intro j
    fin_cases j
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
  rcases key i with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rw [torV, h0, h1]
    simp
  · rw [torV, h0, h1]
    have h : (1 : ZMod 3).val = 1 := rfl
    rw [h, pow_one]

theorem rootChar_torV_eq_one_iff (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) (x : Fin Tag.E6.rank → ZMod 3)
    (v : Fin Tag.E6.rank → ℤ) :
    rootChar (torV ω x) v = 1 ↔ ∑ i, x i * ((v i : ℤ) : ZMod 3) = 0 := by
  rw [rootChar_torV, e6Line_zpow_eq_one_iff_three_dvd h3 h1]
  have h := ZMod.intCast_zmod_eq_zero_iff_dvd (∑ i, ((x i).val : ℤ) * v i) 3
  have e : ((∑ i, ((x i).val : ℤ) * v i : ℤ) : ZMod 3) = ∑ i, x i * ((v i : ℤ) : ZMod 3) := by
    push_cast
    simp [ZMod.natCast_val, ZMod.cast_id]
  rw [e] at h
  rw [h]
  norm_num

open scoped Classical in
theorem card_filter_rootChar_torV (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) (x : Fin Tag.E6.rank → ZMod 3) :
    ((rootFinset .E6).filter fun α => rootChar (torV ω x) α = 1).card = e6KerCount x := by
  unfold e6KerCount
  refine congrArg Finset.card (Finset.ext fun α => ?_)
  simp only [Finset.mem_filter]
  exact and_congr_right fun _ => rootChar_torV_eq_one_iff h3 h1 x α

open scoped Classical in
theorem exists_weylTuple_eq_e6LineChar (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1)
    (x : Fin Tag.E6.rank → ZMod 3)
    (hx : ((rootFinset .E6).filter fun α => rootChar (torV ω x) α = 1).card = 18) :
    ∃ w : WeylGroup .E6, weylTuple w (torV ω x) = e6LineChar ω := by
  rw [card_filter_rootChar_torV h3 h1] at hx
  obtain ⟨l, hl⟩ := exists_word_of_kerCount x hx
  exact ⟨(l.map (simple .E6)).prod, by rw [weylTuple_prod_torV h3, hl, torV_e6KacVec]⟩

end Bridge

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
