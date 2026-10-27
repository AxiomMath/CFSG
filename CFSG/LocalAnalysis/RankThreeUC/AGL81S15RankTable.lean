module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbedding

@[expose] noncomputable def eP (Q r : ℕ) : ℕ := orderOf (Q : ZMod r)

@[expose] noncomputable def eM (Q r : ℕ) : ℕ := orderOf (-(Q : ZMod r))

@[expose] noncomputable def eS (Q r : ℕ) : ℕ := orderOf ((Q : ZMod r) ^ 2)

@[expose] noncomputable def rkLin (m : ℕ) (eps : Bool) (Q r z : ℕ) : ℕ :=
  if (if eps then eP Q r else eM Q r) = 1 then
    m - 1 - (if ¬ r ∣ z ∧ r ∣ m ∧ 4 ≤ m ∧
        padicValNat r (if eps then Q - 1 else Q + 1) ≤ padicValNat r m then 1 else 0)
  else m / (if eps then eP Q r else eM Q r)

@[expose] noncomputable def rkSp (l Q r : ℕ) : ℕ := l / eS Q r

@[expose] noncomputable def rkOmMinus (l Q r : ℕ) : ℕ :=
  l / eS Q r - (if eP Q r ∣ l then 1 else 0)

@[expose] noncomputable def rkOmPlus (l Q r : ℕ) : ℕ :=
  if eP Q r ∣ 2 * l ∧ ¬ eP Q r ∣ l then 2 * l / eP Q r - 1 else l / eS Q r

@[expose] noncomputable def rkG2 (Q r : ℕ) : ℕ :=
  if eS Q r = 1 then 2 else if eS Q r = 3 then 1 else 0

@[expose] noncomputable def mRankChev : TauCeti.LieTypeIndex → ℕ → ℕ → ℕ
  | .A l Q, r, z => rkLin (l + 1) true Q.card r z
  | .twistedA l Q, r, z => rkLin (l + 1) false Q.card r z
  | .B l Q, r, _ => rkSp l Q.card r
  | .D l Q, r, _ => rkOmPlus l Q.card r
  | .twistedD l Q, r, _ => rkOmMinus l Q.card r
  | .G2 Q, r, _ => rkG2 Q.card r
  | _, _, _ => 0

@[expose] def LieOddRankChev : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    ∀ d : TauCeti.ValidLieTypeIndex, IsClassicalOrG2Index d.1 →
      Nonempty ((K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ r : ℕ, r.Prime → r ≠ 2 →
        CFSG.Open.pRank r (⊤ : Subgroup K) = mRankChev d.1 r (Nat.card (Subgroup.center K))

@[expose] def LieOddRankAlt : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → ∀ n : ℕ, 5 ≤ n →
    Nonempty ((K ⧸ Subgroup.center K) ≃* alternatingGroup (Fin n)) →
    ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r (⊤ : Subgroup K) = n / r

@[expose] def LieOddRankSmall : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    ∀ r : ℕ, r.Prime → r ≠ 2 →
      ((∃ q : TauCeti.PrimePower, ∃ d : TauCeti.ValidLieTypeIndex, q.card = 7 ∧ d.1 = .A 1 q ∧
          Nonempty ((K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie d).Group)) →
        CFSG.Open.pRank r (⊤ : Subgroup K) = if r = 3 ∨ r = 7 then 1 else 0) ∧
      ((∃ q : TauCeti.PrimePower, ∃ d : TauCeti.ValidLieTypeIndex, q.card = 3 ∧
          d.1 = .twistedA 2 q ∧
          Nonempty ((K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie d).Group)) →
        CFSG.Open.pRank r (⊤ : Subgroup K) = if r = 3 then 2 else if r = 7 then 1 else 0)

structure LieOddRankTable : Prop where
  chev : LieOddRankChev
  alt : LieOddRankAlt
  small : LieOddRankSmall

end CFSG.LocalAnalysis.RankThreeUC.S15
