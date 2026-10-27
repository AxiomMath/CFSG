module

public import CFSG.ClassicalInvolution.WeakCT.TwistedSpinNodes
public import CFSG.ClassicalInvolution.WeakCT.SpinOdd

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CliffordAlgebra QuadraticMap CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras
  CFSG.ClassicalInvolution.Models.TwistedPairs
open scoped MatrixGroups

section SL3

variable {F : Type} [Field F] [Finite F]

theorem exists_sl3_minus (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : 4 ≤ n) (b c : F) {i j : Fin (n - 1)}
    (hij : i.val + 1 = j.val) (hi : i.val + 1 < n - 1) (hj : j.val + 1 < n - 1) :
    ∃ emb : SL(3, F) →* spinGroup (quadMinus n F b c), Function.Injective emb ∧
      emb.comp (blk F 0) = rLong n b c hi ∧ emb.comp (blk F 1) = rLong n b c hj := by
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan (Spin.oddDatum (n - 1) F).isFiniteType
    (Dv := (Spin.oddDatum (n - 1) F).divisible) rfl
  have hE := Steinberg.SpinOdd.chevalleyExtras (by omega : 2 ≤ n - 1) O Steinberg.SpinOdd.commC
    (Steinberg.SpinOdd.commutatorFormula O)
  obtain ⟨a, ha⟩ : ∃ a : Fin (n - 1), a.val + 2 = n - 1 :=
    ⟨⟨n - 3, by omega⟩, by simp only; omega⟩
  obtain ⟨b', hb'⟩ : ∃ b' : Fin (n - 1), b'.val + 1 = n - 1 :=
    ⟨⟨n - 2, by omega⟩, by simp only; omega⟩
  have hdiag := doubleBondDiagram_cartanB ha hb'
  have hadj : edgeUp (n - 1) i j := hij
  have hne : ¬ (i = a ∧ j = b') := fun h => by
    have := congrArg Fin.val h.2
    omega
  obtain ⟨hc1, hc2⟩ := hdiag.cartan_adj i j hadj hne
  obtain ⟨k', hk'⟩ := hdiag.neighbour i j hadj hne
  obtain ⟨emb, hinj, -, hv⟩ := exists_sl3Levi hE rfl (Fin.ne_of_val_ne (by omega)) hc1 hc2 hk'
  have hv1 : ∀ x : F, emb (tv 0 1 x) = rootB F i (.ofAdd x) := fun x =>
    (hv x).1.trans (Steinberg.SpinOdd.x_single i x)
  have hv2 : ∀ x : F, emb (tv 1 0 x) = negRootB F i (.ofAdd x) := fun x =>
    (hv x).2.1.trans (Steinberg.SpinOdd.x_neg_single i x)
  have hv3 : ∀ x : F, emb (tv 1 2 x) = rootB F j (.ofAdd x) := fun x =>
    (hv x).2.2.1.trans (Steinberg.SpinOdd.x_single j x)
  have hv4 : ∀ x : F, emb (tv 2 1 x) = negRootB F j (.ofAdd x) := fun x =>
    (hv x).2.2.2.trans (Steinberg.SpinOdd.x_neg_single j x)
  refine ⟨(oddToMinus n b c).spinGroupMap.comp emb,
    (spinGroupMap_oddToMinus_injective h2 n b c).comp hinj, ?_, ?_⟩
  · refine hom_ext_sl2 (fun x => ?_) (fun x => ?_)
    · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, blk_zero_tv01, hv1, rLong_tv01 hi, rootB,
        dite_eq_left hi, spinGroupMap_oddToMinus_longRoot]
    · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, blk_zero_tv10, hv2, rLong_tv10 hi, negRootB,
        dite_eq_left hi, spinGroupMap_oddToMinus_longRoot]
  · refine hom_ext_sl2 (fun x => ?_) (fun x => ?_)
    · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, blk_one_tv01, hv3, rLong_tv01 hj, rootB,
        dite_eq_left hj, spinGroupMap_oddToMinus_longRoot]
    · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, blk_one_tv10, hv4, rLong_tv10 hj, negRootB,
        dite_eq_left hj, spinGroupMap_oddToMinus_longRoot]

end SL3

section DoubleBond

variable {F : Type} [Field F] {b c : F}

theorem longSL2_congr {V : Type*} [AddCommGroup V] [Module F V] {Q : QuadraticForm F V} {m : ℕ}
    (H : HypFrame Q m) {i j i' j' : Fin m} (hij : i ≠ j) (hij' : i' ≠ j') (hi : i = i')
    (hj : j = j') (s t : Bool) : H.longSL2 hij s t = H.longSL2 hij' s t := by
  subst hi hj
  rfl

theorem minusShift_comp_longBlock {n : ℕ} (hn : 3 ≤ n) {k : Fin (n - 1)}
    (hk3 : k.val + 3 = n) (hk : k.val + 1 < n - 1) :
    (minusShift n hn b c).spinGroupMap.comp (minusLongBlock b c) = rLong n b c hk := by
  have e0 : pairShift n hn ⟨0, by decide⟩ = k := Fin.ext (by simp only [pairShift]; omega)
  have e1 : pairShift n hn ⟨1, by decide⟩ = ⟨k.val + 1, hk⟩ :=
    Fin.ext (by simp only [pairShift]; omega)
  rw [minusLongBlock, spinGroupMap_minusShift_longSL2, rLong]
  exact longSL2_congr _ _ _ e0 e1 _ _

variable [Finite F] [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)]

theorem minusShift_comp_shortBlock {n : ℕ} (hn : 3 ≤ n)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {k : Fin (n - 1)} (hk2 : k.val + 2 = n) :
    (minusShift n hn b c).spinGroupMap.comp (shortBlock hirr 3 finOne) = shortBlock hirr n k := by
  have e : pairShift n hn finOne = k := Fin.ext (by simp only [pairShift, finOne]; omega)
  refine hom_ext_sl2 (fun x => ?_) (fun x => ?_)
  · rw [MonoidHom.comp_apply, shortBlock_tv01, shortBlock_tv01]
    have := spinGroupMap_minusShift_twShortRoot n hn hirr finOne true (fieldCoord x)
    simp only [twShortRoot_true] at this
    rw [this, e]
  · rw [MonoidHom.comp_apply, shortBlock_tv10, shortBlock_tv10]
    have := spinGroupMap_minusShift_twShortRoot n hn hirr finOne false (starCoord x)
    simp only [twShortRoot_false] at this
    rw [this, e]

end DoubleBond

end CFSG.ClassicalInvolution.WeakCT
