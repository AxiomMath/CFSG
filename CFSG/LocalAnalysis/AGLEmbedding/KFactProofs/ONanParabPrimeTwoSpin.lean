module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwo
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSpin

public section

namespace CFSG.AGLEmbedding.ParabPrime

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabHub CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg CFSG.LieType.Steinberg.SpinFrame
  CFSG.LieType.RootSystem
open scoped commutatorElement

section Plus

variable {n : ℕ} {F : Type} [Field F]

theorem spinPlus_commutator_ne_one (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j)
    (hA : cartanD n j i = -1) :
    ⁅SpinPlus.x n F hn (Pi.single i 1) 1, SpinPlus.x n F hn (Pi.single j 1) 1⁆ ≠ 1 := by
  have hn2 : 2 ≤ n := by omega
  have hαi : (Pi.single i 1 : Fin n → ℤ) ∈ roots (isFiniteType_cartanD n) ∅ :=
    (RootSystem.ofCartan (plusDatum n F hn).isFiniteType (plusDatum n F hn).divisible).single_mem i
  have hαj : (Pi.single j 1 : Fin n → ℤ) ∈ roots (isFiniteType_cartanD n) ∅ :=
    (RootSystem.ofCartan (plusDatum n F hn).isFiniteType (plusDatum n F hn).divisible).single_mem j
  have hsum : (Pi.single i 1 + Pi.single j 1 : Fin n → ℤ) ∈ roots (isFiniteType_cartanD n) ∅ := by
    have h := pair_one_one_mem_roots (D := plusDatum n F hn) (i := i) (j := j) hA
    have e : pair (I := Fin (plusDatum n F hn).rank) i j ((1 : ℤ), (1 : ℤ)) =
        Pi.single i 1 + Pi.single j 1 := by
      exact (pair_apply i j ((1 : ℤ), (1 : ℤ))).trans (by simp; rfl)
    exact e ▸ h
  have ha : IsLong (toStdD n (Pi.single i 1)) := (SpinPlus.isLong_toStdD_iff hn2).2 hαi
  have hb : IsLong (toStdD n (Pi.single j 1)) := (SpinPlus.isLong_toStdD_iff hn2).2 hαj
  have hl : IsLong (toStdD n (Pi.single i 1) + toStdD n (Pi.single j 1)) := by
    rw [← toStdD_add]
    exact (SpinPlus.isLong_toStdD_iff hn2).2 hsum
  have hab : toStdD n (Pi.single i 1) + toStdD n (Pi.single j 1) ≠ 0 := by
    apply SpinPlus.toStdD_add_ne_zero
    intro h
    have := congrFun h i
    simp [hij] at this
  rw [SpinPlus.x, SpinPlus.x, commutator_rootElt (plusFrame n F hn) ha hb hab hl 1 1]
  intro h
  have h1 := rootElt_injective (plusFrame n F hn) hl (h.trans (rootElt_zero _ _).symm)
  rcases chainSign_eq_one_or_eq_neg_one (toStdD n (Pi.single i 1)) (toStdD n (Pi.single j 1))
    with h2 | h2 <;> simp [h2] at h1

theorem cartanD_eq_neg_one {i j : Fin n} (hij : i ≠ j) (hA : cartanD n i j ≠ 0) :
    cartanD n i j = -1 ∧ cartanD n j i = -1 := by
  have hv : i.val ≠ j.val := fun e => hij (Fin.ext e)
  simp only [cartanD, Matrix.of_apply, hij, hij.symm, ↓reduceIte] at hA ⊢
  split_ifs at hA ⊢ <;> omega

section TwoLevi

variable [Finite F]

theorem twoLevi_spinPlus (hF : Nat.card F = 2) (hn : 3 ≤ n)
    {w : Fin n → spinGroup (quadPlus n F)} {T : Fin n → Subgroup (spinGroup (quadPlus n F))}
    (hct : CFSG.LieType.CurtisTits.IsCTGroupDatum
      (coxeterMatrix (plusDatum n F hn).isFiniteType).toCoxeterSystem
      (weylAction (plusDatum n F hn).isFiniteType) (plusDatum n F hn).roots
      (plusDatum n F hn).rootGroup w T)
    (hext : SteinbergExtras (plusDatum n F hn) w T) :
    TwoLevi (plusDatum n F hn) (fun _ _ => False) := by
  refine TwoLevi.of_param hF (SpinPlus.isParametrization hn) hct hext (fun i => ?_)
    (fun _ _ h => h) (fun _ _ _ h => h.elim) (fun _ _ h => h.elim)
    (fun i j hij hA _ => ?_)
  · obtain ⟨φ, -, hx, hy⟩ := SpinPlus.rankOne (K := F) hn i
    exact ⟨φ, hx, hy⟩
  · obtain ⟨h1, h2⟩ := cartanD_eq_neg_one hij hA
    refine ⟨h1, h2, 1, 1, spinPlus_commutator_ne_one hn hij h2⟩

end TwoLevi

section Main

variable [Finite F] [CharP F 2]

theorem parabCore_spinPlus_two (hF : Nat.card F = 2) (hn : 3 ≤ n) {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* StatedProj (StatedOmega (StatedQuadPlus n F))) : ParabCore Y 2 := by
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  have h := borelQuotient_spinPlus hn e
  exact h.parabCore_two (by rw [hF]; norm_num) (twoLevi_spinPlus hF hn h.ct h.extras)

end Main

end Plus

theorem parabCore_of_model_pomegaPlus_two {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (h : StatedClassicalModel Y .POmegaPlus n 2 1) : ParabCore Y 2 := by
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
  exact parabCore_spinPlus_two (by simpa using hcard) (by omega) e

end CFSG.AGLEmbedding.ParabPrime
