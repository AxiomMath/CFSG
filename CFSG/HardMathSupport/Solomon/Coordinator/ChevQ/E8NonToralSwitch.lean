module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToralTrace
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCoreDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore

section Counts

variable {τ : Tag}

theorem charRes_neg_add (k : Fin τ.rank → ZMod 3) (v : Fin τ.rank → ℤ) :
    charRes k (-v) + charRes k v = 0 := by
  have h : ∑ i, (k i * (((-v) i : ℤ) : ZMod 3) + k i * ((v i : ℤ) : ZMod 3)) = 0 :=
    Finset.sum_eq_zero fun i _ => by
      rw [Pi.neg_apply, Int.cast_neg, mul_neg, neg_add_cancel]
  rw [Finset.sum_add_distrib] at h
  exact h

theorem charRes_neg_of_eq_one {k : Fin τ.rank → ZMod 3} {v : Fin τ.rank → ℤ}
    (h1 : charRes k v = 1) : charRes k (-v) = 2 := by
  have h := charRes_neg_add k v
  rw [h1] at h
  revert h
  generalize charRes k (-v) = x
  revert x
  decide

theorem charRes_neg_of_eq_two {k : Fin τ.rank → ZMod 3} {v : Fin τ.rank → ℤ}
    (h2 : charRes k v = 2) : charRes k (-v) = 1 := by
  have h := charRes_neg_add k v
  rw [h2] at h
  revert h
  generalize charRes k (-v) = x
  revert x
  decide

theorem resCount_one_eq_two (k : Fin τ.rank → ZMod 3) : resCount k 1 = resCount k 2 := by
  classical
  unfold resCount
  refine Finset.card_bij (fun α _ => ⟨-α.1, IsRoot.neg α.2⟩) ?_ ?_ ?_
  · intro α hα
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hα ⊢
    exact charRes_neg_of_eq_one hα
  · intro α _ β _ h
    apply Subtype.ext
    have := congrArg Subtype.val h
    simpa using this
  · intro β hβ
    refine ⟨⟨-β.1, IsRoot.neg β.2⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hβ ⊢
      exact charRes_neg_of_eq_two hβ
    · apply Subtype.ext
      simp

theorem resCount_add (k : Fin τ.rank → ZMod 3) :
    resCount k 0 + resCount k 1 + resCount k 2 =
      Fintype.card {v : Fin τ.rank → ℤ // IsRoot τ v} := by
  classical
  unfold resCount
  have h := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ)
    (f := fun α : {v : Fin τ.rank → ℤ // IsRoot τ v} => charRes k α.1)
    (fun _ _ => Finset.mem_univ _)
  have huniv : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.card_univ] at h
  rw [h, add_assoc]

theorem ncard_setOf_isRoot (P : (Fin τ.rank → ℤ) → Prop) [DecidablePred P] :
    {α : Fin τ.rank → ℤ | IsRoot τ α ∧ P α}.ncard =
      (Finset.univ.filter fun α : {v : Fin τ.rank → ℤ // IsRoot τ v} => P α.1).card := by
  rw [← Nat.card_coe_set_eq, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun v => IsRoot τ v) P).symm

end Counts

section Trace

variable {K : Type} [Field K]

theorem trace_rootDiagUnit_E8_of_kills (b : Fin Tag.E8.rank → Kˣ) (hb3 : ∀ i, b i ^ 3 = 1)
    (h78 : {α : Fin Tag.E8.rank → ℤ | IsRoot Tag.E8 α ∧ rootChar b α = 1}.ncard = 78) :
    LinearMap.trace K (RootModule Tag.E8 K)
        ((rootDiagUnit Tag.E8 b : ModGL Tag.E8 K) : Module.End K (RootModule Tag.E8 K)) = 5 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Fintype.card {v : Fin Tag.E8.rank → ℤ // IsRoot Tag.E8 v} = 240 := by
    rw [card_isRoot]
    rfl
  obtain ⟨i₀, hi₀⟩ : ∃ i, b i ≠ 1 := by
    by_contra h
    push Not at h
    have hall : ∀ α : Fin Tag.E8.rank → ℤ, rootChar b α = 1 := fun α => by
      simp [rootChar, h]
    have e : {α : Fin Tag.E8.rank → ℤ | IsRoot Tag.E8 α ∧ rootChar b α = 1}.ncard = 240 := by
      rw [ncard_setOf_isRoot]
      simp only [hall]
      rw [Finset.filter_true_of_mem (fun _ _ => trivial), Finset.card_univ, hcard]
    omega
  set ω := b i₀ with hωdef
  have hprim : IsPrimitiveRoot ω 3 := by
    have hord : orderOf ω = 3 := orderOf_eq_prime (hb3 i₀) hi₀
    exact hord ▸ IsPrimitiveRoot.orderOf ω
  have hex : ∀ i, ∃ n < 3, ω ^ n = b i := fun i =>
    hprim.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity 3 (b i)).2 (hb3 i))
  choose n hn hωn using hex
  set k : Fin Tag.E8.rank → ZMod 3 := fun i => (n i : ZMod 3) with hkdef
  have hkv : ∀ i, (k i).val = n i := fun i => ZMod.val_natCast_of_lt (hn i)
  have hb : ∀ i, b i = ω ^ (k i).val := fun i => by rw [hkv, hωn]
  have hiff : ∀ v : Fin Tag.E8.rank → ℤ, rootChar b v = 1 ↔ charRes k v = 0 := by
    intro v
    rw [rootChar_eq_pow_charRes (hprim.pow_eq_one) b k hb, hprim.pow_eq_one_iff_dvd,
      ← ZMod.val_eq_zero]
    constructor
    · intro h
      have hlt := ZMod.val_lt (charRes k v)
      omega
    · intro h
      rw [h]
      exact dvd_zero 3
  have h0 : resCount k 0 = 78 := by
    rw [← h78, ncard_setOf_isRoot]
    unfold resCount
    exact congrArg Finset.card (Finset.filter_congr fun α _ => (hiff α.1).symm)
  have hsum := resCount_add k
  rw [hcard, h0, resCount_one_eq_two k] at hsum
  have h2 : resCount k 2 = 81 := by omega
  have h1 : resCount k 1 = 81 := by rw [resCount_one_eq_two k, h2]
  exact trace_rootDiagUnit_E8_of_counts hprim b k hb h0 h1 h2

theorem five_ne_neg_four (hK : ringChar K ≠ 3) : (5 : K) ≠ ((-4 : ℤ) : K) := by
  intro h
  have h3 : (3 : K) = 0 := by
    have h9 : (3 : K) * 3 = 0 := by
      push_cast at h
      linear_combination h
    exact mul_self_eq_zero.1 h9
  have hd : ringChar K ∣ 3 := by
    have := (ringChar.spec K 3).1
    exact this (by exact_mod_cast h3)
  rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · exact hK h1

end Trace

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral
