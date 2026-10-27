module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOutBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

variable {T : TauCeti.CFSGIndex → Prop}

structure LieSOutOrd (N : ℕ) : Prop where
  three_dvd : 3 ∣ N
  not_dvd_216 : ¬ N ∣ 216
  not_dvd_360 : ¬ N ∣ 360
  not_dvd_12096 : ¬ N ∣ 12096
  not_dvd_17971200 : ¬ N ∣ 17971200
  ne_triD4 : ∀ Q : ℕ, 2 ≤ Q → N ≠ Q ^ 12 * (Q ^ 2 - 1) * (Q ^ 6 - 1) * (Q ^ 8 + Q ^ 4 + 1)
  ne_g2 : ∀ Q : ℕ, 4 ≤ Q → N ≠ Q ^ 6 * (Q ^ 6 - 1) * (Q ^ 2 - 1)
  ne_sl3 : ∀ q : ℕ, 2 ≤ q → q ^ 3 ∣ N →
    N * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))
  ne_su3 : ∀ q : ℕ, 2 ≤ q → q ^ 3 ∣ N →
    N * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))

structure LieSOutType (T : TauCeti.CFSGIndex → Prop) (m f N : ℕ) : Prop where
  card_eq : TypeOrd T N
  det : ∀ {X : Type} [Group X], catalogIs X T → ∀ {t : StatedLieTag} {n g : ℕ},
    Blueprint.LieModel X t n 2 g → t = .PSp ∧ n = m ∧ g = f
  ord : LieSOutOrd N

@[expose] def isBIdx (m Q : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun
    | .B r q => r = m ∧ q.card = Q
    | _ => False

@[expose] def TypeOuterAt (T P : TauCeti.CFSGIndex → Prop) (F : TauCeti.LieTypeIndex → Prop) :
    Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, F d.1 →
      CFSG.HardMathSupport.Solomon.Coordinator.IsCharTwoLieIndex d.1 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ α : MulAut S, α ∉ innAutDerived S → TypePumpup T S α → P (.lie d)

variable {P : TauCeti.CFSGIndex → Prop}

theorem TypeOuterAt.union {F G : TauCeti.LieTypeIndex → Prop} (hF : TypeOuterAt T P F)
    (hG : TypeOuterAt T P G) : TypeOuterAt T P (fun d => F d ∨ G d) :=
  fun S _ _ hs hnab d hd hc he α hα hp => by
    rcases hd with h | h
    · exact hF S hs hnab d h hc he α hα hp
    · exact hG S hs hnab d h hc he α hα hp

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
