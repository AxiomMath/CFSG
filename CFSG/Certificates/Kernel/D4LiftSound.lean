module

public import Certificates.Data.Kernel.D4LiftK
public import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import CFSG.Certificates.Kernel.Spor.BaseSep
public import CFSG.RankThree.PartOne.KS.PKit

public section

namespace CFSG.KC.D4Lift

open CFSG.KC.Enum (pg allN permOK)
open CFSG.KS (mask)
open CFSG.KC.D4K (siftOK)
open CFSG.KC.B3S3K (cm)

theorem bAnd_true {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem anyN_iff {n : Nat} {f : Nat → Bool} : anyN n f = true ↔ ∃ i < n, f i = true := by
  have key : allN n (fun i => bIf(f i, false, true)) = true ↔ ∀ i < n, f i = false := by
    rw [CFSG.KS.Raw.Orb.allN_iff]
    refine forall₂_congr fun i _ => ?_
    cases f i <;> simp
  unfold anyN
  cases h : allN n (fun i => bIf(f i, false, true))
  · refine iff_of_true rfl ?_
    by_contra hn
    push Not at hn
    exact absurd (key.2 fun i hi => by simpa using hn i hi) (by rw [h]; exact Bool.false_ne_true)
  · refine iff_of_false Bool.false_ne_true ?_
    rintro ⟨i, hi, hf⟩
    rw [key.1 h i hi] at hf
    exact Bool.false_ne_true hf

theorem baseAll_iff {w BP nb : Nat} {f : Nat → Bool} :
    baseAll w BP nb f = true ↔ ∀ t < nb, f (pg w (mask w) BP t) = true :=
  CFSG.KS.Raw.Orb.allN_iff

theorem baseAny_iff {w BP nb : Nat} {f : Nat → Bool} :
    baseAny w BP nb f = true ↔ ∃ t < nb, f (pg w (mask w) BP t) = true :=
  anyN_iff

theorem bIf_ne {a b : Nat} (h : bIf(Nat.beq a b, false, true) = true) : a ≠ b := by
  intro e
  rw [e, Nat.beq_refl] at h
  exact Bool.false_ne_true h

theorem liftK_sound {n w nb BP F0 PH NQ NI N : Nat} {LR TRI QT IT T : Nat → Nat}
    (h : liftK n w LR TRI BP nb F0 PH NQ QT NI IT N T = true) :
    permOK n w (mask w) (n * w) F0 (cm n w F0 F0) = true ∧
      siftOK n w LR TRI BP nb (cm n w F0 (cm n w PH PH)) = true ∧
      (∀ j < NI, permOK n w (mask w) (n * w) (IT j) (IT j) = true ∧
        siftOK n w LR TRI BP nb (IT j) = true ∧
        (∀ t < nb, pg w (mask w) (IT j) (pg w (mask w) (IT j) (pg w (mask w) BP t)) =
          pg w (mask w) BP t) ∧
        ∃ t < nb, pg w (mask w) (IT j) (pg w (mask w) BP t) ≠ pg w (mask w) BP t) ∧
      ∀ i < N, (∃ j < NQ, T i = QT j) ∨
        (∃ t < nb, pg w (mask w) (T i) (pg w (mask w) (T i) (pg w (mask w) (T i)
          (pg w (mask w) BP t))) ≠ pg w (mask w) BP t) ∨
        ∃ j < NI, ∀ t < nb, pg w (mask w) (T i) (pg w (mask w) (IT j) (pg w (mask w) BP t)) =
          pg w (mask w) (IT j) (pg w (mask w) (T i) (pg w (mask w) BP t)) := by
  unfold liftK at h
  obtain ⟨h1, h⟩ := bAnd_true h
  obtain ⟨h2, h⟩ := bAnd_true h
  obtain ⟨h3, h4⟩ := bAnd_true h
  refine ⟨h1, h2, fun j hj => ?_, fun i hi => ?_⟩
  · obtain ⟨p1, p⟩ := bAnd_true (CFSG.KS.Raw.Orb.allN_iff.1 h3 j hj)
    obtain ⟨p2, p3⟩ := bAnd_true p
    unfold invAt at p3
    obtain ⟨q1, q2⟩ := bAnd_true p3
    refine ⟨p1, p2, fun t ht => Nat.eq_of_beq_eq_true (baseAll_iff.1 q1 t ht), ?_⟩
    obtain ⟨t, ht, e⟩ := baseAny_iff.1 q2
    exact ⟨t, ht, bIf_ne e⟩
  · have p := CFSG.KS.Raw.Orb.allN_iff.1 h4 i hi
    unfold pointK at p
    cases hq : anyN NQ (fun j => Nat.beq (T i) (QT j))
    · rw [hq] at p
      cases hc : cubeMoves w BP nb (T i)
      · rw [hc] at p
        obtain ⟨j, hj, e⟩ := anyN_iff.1 p
        unfold commAt at e
        exact Or.inr (Or.inr ⟨j, hj, fun t ht => Nat.eq_of_beq_eq_true (baseAll_iff.1 e t ht)⟩)
      · unfold cubeMoves at hc
        obtain ⟨t, ht, e⟩ := baseAny_iff.1 hc
        exact Or.inr (Or.inl ⟨t, ht, bIf_ne e⟩)
    · obtain ⟨j, hj, e⟩ := anyN_iff.1 hq
      exact Or.inl ⟨j, hj, Nat.eq_of_beq_eq_true e⟩

end CFSG.KC.D4Lift

namespace CFSG.RankThree.PartOne

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem eq_one_of_fix_two {n : ℕ} (hn : 1 ≤ n) {S : Array (Array ℕ)} (hk : 2 ≤ S.size)
    {bs : List (Fin n)} (hb : bs.Nodup) {W : Array (List ℤ)} {a b : Array ℕ}
    {A B : Equiv.Perm (Fin n)} (ha : Rep n a A) (hb' : Rep n b B)
    (hchain : caseChainOK2P n S (bs.map Fin.val).toArray W a b = true)
    {G : Equiv.Perm (Fin n)} (hG : G ∈ Subgroup.closure {A, B}) (hfix : ∀ x ∈ bs, G x = x) :
    G = 1 := by
  obtain ⟨hc, e0, e1⟩ := caseChainOK2P_parts hchain
  have hA : ChainArrays (RawSchreierDatum.ofArrays n hn S 2 hk bs hb W) (S.extract 0 2) S
      (bs.map Fin.val).toArray W := chainArrays_ofArrays (chainCheckFacts hc).strong_inv
  have hv := validSchreier_of_chainOK hA (by norm_num) hc
  rw [← originalSubgroup_ofArrays_twoP (hn := hn) (hk := hk) (hb := hb) hc ha hb' e0 e1] at hG
  refine RawSchreierDatum.eq_one_of_fixes_base _ hv.1 hG fun i => hfix _ ?_
  have hbase := RawSchreierDatum.ofArrays_base_toList (hn := hn) (S := S) (k := 2) (hk := hk)
    (base := bs) (hb := hb) (W := W)
  have hm : (RawSchreierDatum.ofArrays n hn S 2 hk bs hb W).base.get i ∈
      (RawSchreierDatum.ofArrays n hn S 2 hk bs hb W).base.toList := by
    simp [Vector.get, Vector.toList]
  rwa [hbase] at hm

end CFSG.RankThree.PartOne

end
