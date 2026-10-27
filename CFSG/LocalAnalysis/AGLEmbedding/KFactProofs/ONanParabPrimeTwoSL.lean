module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwo
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSL

public section

namespace CFSG.AGLEmbedding.ParabPrime

open CFSG.AGLEmbedding.ParabHub CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear
  CFSG.LieType.Steinberg
open scoped commutatorElement

variable {m : ℕ} {F : Type} [Field F]

theorem transvection_ne_one {i j : Fin (m + 1)} (hij : i ≠ j) {c : F} (hc : c ≠ 0) :
    Matrix.SpecialLinearGroup.transvection hij c ≠ 1 := by
  intro h
  apply hc
  apply Matrix.SpecialLinearGroup.transvection_injective hij
  rw [h]
  simp

theorem sl_commutator_ne_one {i j : Fin m} (hij : i.val + 1 = j.val) :
    ⁅SL.x m F (Pi.single i 1) 1, SL.x m F (Pi.single j 1) 1⁆ ≠ 1 := by
  have h1 : i.castSucc ≠ i.succ := Fin.castSucc_lt_succ.ne
  have hs : j.castSucc = i.succ := Fin.ext (by simp [hij])
  have h2 : i.succ ≠ j.succ := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have h3 : i.castSucc ≠ j.succ := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have e1 : SL.x m F (Pi.single i 1) 1 = Matrix.SpecialLinearGroup.transvection h1 1 :=
    SL.x_eq h1 (toStd_single m i) 1
  have e2 : SL.x m F (Pi.single j 1) 1 = Matrix.SpecialLinearGroup.transvection h2 1 :=
    SL.x_eq h2 (by rw [toStd_single, hs]) 1
  rw [e1, e2, Matrix.SpecialLinearGroup.commutatorElement_transvection h1 h2 h3]
  exact transvection_ne_one h3 (by simp)

theorem twoLevi_sl [Finite F] (hF : Nat.card F = 2) :
    TwoLevi (rootDatum m F) (fun _ _ => False) := by
  refine TwoLevi.of_param hF SL.isParametrization (isCTGroupDatum m F) (steinbergExtras m F)
    (fun i => ?_) (fun _ _ h => h) (fun _ _ _ h => h.elim) (fun _ _ h => h.elim)
    (fun (i j : Fin m) hij hA _ => ?_)
  · obtain ⟨φ, -, hx, hy⟩ := SL.rankOne (F := F) i
    exact ⟨φ, hx, hy⟩
  · have hv : i.val ≠ j.val := fun e => hij (Fin.ext e)
    have hA' : CartanMatrix.A m i j ≠ 0 := hA
    have hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val := by
      by_contra hn
      apply hA'
      simp [CartanMatrix.A, Fin.ext_iff, hv]
      omega
    refine ⟨?_, ?_, 1, 1, ?_⟩
    · show CartanMatrix.A m i j = -1
      simp [CartanMatrix.A, Fin.ext_iff, hv]
      omega
    · show CartanMatrix.A m j i = -1
      simp [CartanMatrix.A, Fin.ext_iff, Ne.symm hv]
      omega
    · rcases hadj with h | h
      · exact sl_commutator_ne_one h
      · intro hc
        apply sl_commutator_ne_one (F := F) h
        rw [← commutatorElement_inv]
        exact inv_eq_one.2 hc

theorem parabCore_of_model_psl_two {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel Y .PSL n 2 1) : ParabCore Y 2 := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have hF2 : Nat.card F = 2 := by simpa using hcard
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (borelQuotient_sl ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj
    (m + 1) F).trans e.symm)).parabCore_two (by rw [hF2]; norm_num) (twoLevi_sl hF2)

end CFSG.AGLEmbedding.ParabPrime
