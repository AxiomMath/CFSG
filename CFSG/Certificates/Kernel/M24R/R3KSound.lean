module

public import Certificates.Data.Kernel.M24R.R3K
public import CFSG.Certificates.Kernel.KGC31PBSound
public import CFSG.CGT.M24R.R3Model
public import Certificates.Data.Kernel.J2ModelK

public section

namespace CFSG.KC.M24R3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.KGC31P CFSG.KC.Misc.ArrEnum CFSG.KC.BfsPin
  CFSG.KC.TabWord CFSG.KC.J2ModelK CFSG.CGT.M24R CFSG.CGT.M24R.R3 CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native
open CFSG.KC.Child3 (tabP)

theorem strictB_eqR3 (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem strictN_eqR3 (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem withL_eq (L : Int → Nat) (k : (Int → Nat) → Bool) : withL L k = k L := by
  have ite_L : ∀ {c z : Int} {X : Nat}, X = L z → (if z = c then L c else X) = L z :=
    fun {c z X} h => by
      by_cases e : z = c
      · rw [if_pos e, e]
      · rw [if_neg e, h]
  unfold withL
  repeat (rw [strictB_eqR3]; beta_reduce)
  exact congrArg k (funext fun z => by
    repeat (refine ite_L ?_)
    rfl)

theorem hsz24 : szOK 24 5 = true := by decide +kernel

theorem gen_eq : ∀ k : Fin 10, genTab k = tabP 24 5 (pmk 24 5 fun i => ap (genTab k) i) := by
  decide +kernel

theorem genInv_eq :
    ∀ k : Fin 10, genTabInv k = tabP 24 5 (pmk 24 5 fun i => ap (genTabInv k) i) := by
  decide +kernel

theorem id_eq : idT 24 = tabP 24 5 (pmk 24 5 fun i => ap (idT 24) i) := by decide +kernel

theorem gen_perm : ∀ k : Fin 10, permOK 24 5 (mask 5) (24 * 5) (pmk 24 5 fun i => ap (genTab k) i)
    (pinvS 24 5 (mask 5) (pmk 24 5 fun i => ap (genTab k) i)) = true := by decide +kernel

theorem genInv_perm : ∀ k : Fin 10,
    permOK 24 5 (mask 5) (24 * 5) (pmk 24 5 fun i => ap (genTabInv k) i)
      (pinvS 24 5 (mask 5) (pmk 24 5 fun i => ap (genTabInv k) i)) = true := by decide +kernel

theorem id_perm : permOK 24 5 (mask 5) (24 * 5) (pmk 24 5 fun i => ap (idT 24) i)
    (pinvS 24 5 (mask 5) (pmk 24 5 fun i => ap (idT 24) i)) = true := by decide +kernel

theorem letTab_eq (z : Int) : letTab z = tabP 24 5 (gP z) ∧ PP 24 5 (gP z) := by
  have key : ∀ T : Table, (T = idT 24 ∨ ∃ k : Fin 10, T = genTab k ∨ T = genTabInv k) →
      T = tabP 24 5 (pmk 24 5 fun i => ap T i) ∧ PP 24 5 (pmk 24 5 fun i => ap T i) := by
    rintro T (rfl | ⟨k, rfl | rfl⟩)
    · exact ⟨id_eq, PP_of_permOK hsz24 id_perm⟩
    · exact ⟨gen_eq k, PP_of_permOK hsz24 (gen_perm k)⟩
    · exact ⟨genInv_eq k, PP_of_permOK hsz24 (genInv_perm k)⟩
  apply key
  unfold letTab
  split_ifs
  · rcases Nat.lt_or_ge (z.toNat - 1) 10 with h | h
    · exact Or.inr ⟨⟨_, h⟩, Or.inl rfl⟩
    · exact Or.inl (genTab_of_ge h)
  · rcases Nat.lt_or_ge ((-z).toNat - 1) 10 with h | h
    · exact Or.inr ⟨⟨_, h⟩, Or.inr rfl⟩
    · exact Or.inl (genTabInv_of_ge h)

theorem tabEq_tabP {a b : Nat} (ha : PP 24 5 a) (hb : PP 24 5 b) :
    tabEq (tabP 24 5 a) (tabP 24 5 b) = Nat.beq a b := by
  cases h : Nat.beq a b
  · cases e : tabEq (tabP 24 5 a) (tabP 24 5 b)
    · rfl
    · have hall := allIn_eq_true.1 e
      obtain ⟨-, hw, sa, -⟩ := PF.canon_facts ha.1
      obtain ⟨-, -, sb, -⟩ := PF.canon_facts hb.1
      have hab : a = b := PF.eq_of_fields (PF.w_pos hw) sa sb fun i hi => by
        rw [← ap_tabP' ha hi, ← ap_tabP' hb hi]
        exact eq_of_beq (hall i (Nat.zero_le _) hi)
      rw [hab, Nat.beq_refl] at h
      exact absurd h (by decide)
  · rw [Nat.eq_of_beq_eq_true h]
    exact allIn_eq_true.2 fun i _ _ => beq_self_eq_true _

theorem wordK_pword (L : Int → Nat) :
    ∀ u, wordK 24 5 (pidn 24 5) L u = pword 24 5 L u
  | [] => rfl
  | z :: u => by
    change strictN (wordK 24 5 (pidn 24 5) L u) (fun T => pcomp 24 5 (mask 5) (L z) T) = _
    rw [strictN_eqR3, wordK_pword L u]
    rfl

theorem nEq_eq (w w' : N0Word) : nEq w w' = eqWd gP w w' := by
  have hG : ∀ z, letTab z = tabP 24 5 (gP z) := fun z => (letTab_eq z).1
  have hP : ∀ z, PP 24 5 (gP z) := fun z => (letTab_eq z).2
  unfold nEq wTab eqWd
  rw [wordT_tabP hsz24 hG hP, wordT_tabP hsz24 hG hP,
    tabEq_tabP (PP_pword hsz24 hP _) (PP_pword hsz24 hP _), wordK_pword, wordK_pword]

theorem relCheck_of (h : relK gP = true) : relCheck = true := by
  rw [relK, withL_eq] at h
  unfold relCheck
  simpa only [nEq_eq] using h

theorem identCheck_of (h : idK gP = true) : identCheck = true := by
  rw [idK, withL_eq] at h
  unfold identCheck
  simpa only [nEq_eq] using h

theorem distinctCheck_of (h : distK gP = true) : distinctCheck = true := by
  rw [distK, withL_eq] at h
  unfold distinctCheck
  simpa only [nEq_eq] using h

end CFSG.KC.M24R3

end
