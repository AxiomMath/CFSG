module

public import CFSG.GH74.M12.HypCoreInputs
public meta import CFSG.GH74.M12.HypCoreInputs
public import Certificates.Certificate5135

public section

namespace CFSG.GH74.M12.Hyp

@[expose] def tA : List Nat := [3, 1, 9, 0, 10, 11, 6, 7, 8, 2, 4, 5]

@[expose] def tB : List Nat := [7, 2, 3, 1, 11, 9, 5, 8, 0, 6, 4, 10]

@[expose] def letterT (l : Int) : List Nat :=
  if l = 1 then tA else if l = -1 then tinv tA else if l = 2 then tB else tinv tB

@[expose] def wordT : List Int → List Nat
  | [] => tid
  | l :: w => tmul (letterT l) (wordT w)

theorem XT_eq : XT = [3, 2, 1, 0, 4, 10, 9, 7, 8, 6, 5, 11] := by decide +kernel

theorem JT_eq : JT = tpow FT 4 := by decide +kernel

@[expose] def wordG1 : List Int := [1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1]

@[expose] def wordG2 : List Int := [2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2]

@[expose] def wordG3 : List Int := [1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2]

@[expose] def wordH : List Int := [1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2]

theorem wordG1_eq : wordT wordG1 = g1T := by decide +kernel

theorem wordG2_eq : wordT wordG2 = g2T := by decide +kernel

theorem wordG3_eq : wordT wordG3 = g3T := by decide +kernel

theorem wordH_conj : tmul (tmul (wordT wordH) JT) (tinv (wordT wordH)) = XT := by decide +kernel

theorem mem_QT_iff {t : List Nat} : t ∈ QT ↔ t ∈ HT ∧ t.take 4 ∈ V4pre := by
  simp [QT, List.mem_filter]

@[expose] def x1T : List Nat := [0, 1, 2, 3, 10, 4, 7, 9, 5, 11, 8, 6]

@[expose] def y1T : List Nat := [0, 1, 2, 3, 11, 6, 10, 4, 7, 5, 9, 8]

theorem mem_BT_iff {t : List Nat} :
    t ∈ BT ↔ ∃ n < 64, t = bfT (n / 32) ((n / 16) % 2) ((n / 8) % 2) (n % 8) := by
  simp only [BT, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨n, hn, rfl⟩; exact ⟨n, hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩; exact ⟨n, hn, rfl⟩

theorem hyp_core_checks_1 :
    (∀ g ∈ gensT, tmul JT g = tmul g JT) ∧
    (HT.length = 192) ∧
    (HT.Nodup) ∧
    (JT ∈ HT) :=
  Certificates.certificate5135.1

theorem hyp_core_checks_2 :
    (∀ a0 ∈ List.range 4, ∀ a1 ∈ List.range 4, ∀ a2 ∈ List.range 4,
         ∀ a3 ∈ List.range 4, ∀ a4 ∈ List.range 12, a0 ≠ a1 → a0 ≠ a2 → a0 ≠ a3 → a1 ≠ a2 →
           a1 ≠ a3 → a2 ≠ a3 → 4 ≤ a4 → ∃ t ∈ HT, t.take 5 = [a0, a1, a2, a3, a4]) :=
  Certificates.certificate5135.2.1

theorem hyp_core_checks_3 :
    (∀ t ∈ HT, (∀ s ∈ HT, tmul t s = tmul s t) → t = tid ∨ t = JT) ∧
    (∃ c ∈ HT, ∃ d ∈ HT, tcomm c d ≠ tid) ∧
    (QT.length = 32) ∧
    (tid ∈ QT) ∧
    (JT ∈ QT) ∧
    (∀ s ∈ QT, ∀ t ∈ QT, tmul s t ∈ QT) :=
  Certificates.certificate5135.2.2.1

theorem hyp_core_checks_4 :
    (∀ s ∈ QT, tinv s ∈ QT) ∧
    (∀ c ∈ HT, ∀ q ∈ QT, tmul (tmul c q) (tinv c) ∈ QT) ∧
    (∀ s ∈ QT, ((∀ t ∈ QT, tmul s t = tmul t s) ↔ (s = tid ∨ s = JT))) ∧
    (∀ s ∈ QT, ∀ t ∈ QT, tcomm s t = tid ∨ tcomm s t = JT) ∧
    (∀ s ∈ QT, tmul s s = tid ∨ tmul s s = JT) ∧
    (∃ s ∈ QT, s ≠ tid ∧ s ≠ JT) :=
  Certificates.certificate5135.2.2.2.1

theorem hyp_core_checks_5 :
    (∃ c ∈ HT, ∃ d ∈ HT, tcomm c d ∉ QT) ∧
    (∀ x ∈ HT, tmul x (tmul x x) = tid → x ≠ tid →
         ∀ q ∈ QT, tmul q x = tmul x q → q = tid ∨ q = JT) ∧
    (XT ∈ QT) ∧
    (XT ≠ JT) ∧
    (Q1T.length = 8) ∧
    (Q2T.length = 8) :=
  Certificates.certificate5135.2.2.2.2.1

theorem hyp_core_checks_6 :
    (Q1T.Nodup) ∧
    (Q2T.Nodup) ∧
    (∀ t ∈ Q1T, t ∈ QT) ∧
    (∀ t ∈ Q2T, t ∈ QT) ∧
    (tid ∈ Q1T) ∧
    (tid ∈ Q2T) :=
  Certificates.certificate5135.2.2.2.2.2.1

theorem hyp_core_checks_7 :
    (∀ s ∈ Q1T, ∀ t ∈ Q1T, tmul s t ∈ Q1T) ∧
    (∀ s ∈ Q2T, ∀ t ∈ Q2T, tmul s t ∈ Q2T) ∧
    (∀ s ∈ Q1T, tinv s ∈ Q1T) ∧
    (∀ s ∈ Q2T, tinv s ∈ Q2T) ∧
    (∀ c ∈ HT, ∀ q ∈ Q1T, tmul (tmul c q) (tinv c) ∈ Q1T) ∧
    (∀ c ∈ HT, ∀ q ∈ Q2T, tmul (tmul c q) (tinv c) ∈ Q2T) :=
  Certificates.certificate5135.2.2.2.2.2.2.1

theorem hyp_core_checks_8 :
    (∀ x ∈ QT, ∀ y ∈ QT, tpow x 4 = tid → tpow x 2 ≠ tid →
         tmul y y = tpow x 2 → tmul y x = tmul (tpow x 3) y →
           (x ∈ Q1T ∧ y ∈ Q1T) ∨ (x ∈ Q2T ∧ y ∈ Q2T)) :=
  Certificates.certificate5135.2.2.2.2.2.2.2.1

theorem hyp_core_checks_9 :
    (BT.length = 64) ∧
    (BT.Nodup) ∧
    (tid ∈ BT) ∧
    (∀ s ∈ BT, ∀ t ∈ BT, tmul s t ∈ BT) ∧
    (∀ s ∈ BT, tinv s ∈ BT) ∧
    (∀ t ∈ BT, t ∈ HT) :=
  Certificates.certificate5135.2.2.2.2.2.2.2.2.1

theorem hyp_core_checks_10 :
    (ET ∈ BT) ∧
    (NT ∈ BT) ∧
    (FT ∈ BT) ∧
    (JT ∈ BT) ∧
    (XT ∈ BT) ∧
    (∀ s ∈ BT, (∀ t ∈ BT, tmul s t = tmul t s) →
         tmul s s = tid → s ≠ tid → s = JT) :=
  Certificates.certificate5135.2.2.2.2.2.2.2.2.2

theorem gensT_commute : ∀ g ∈ gensT, tmul JT g = tmul g JT :=
  hyp_core_checks_1.1

theorem HT_length : HT.length = 192 :=
  hyp_core_checks_1.2.1

theorem HT_nodup : HT.Nodup :=
  hyp_core_checks_1.2.2.1

theorem JT_mem_HT : JT ∈ HT :=
  hyp_core_checks_1.2.2.2

theorem HT_cover :
    ∀ a0 ∈ List.range 4, ∀ a1 ∈ List.range 4, ∀ a2 ∈ List.range 4,
    ∀ a3 ∈ List.range 4, ∀ a4 ∈ List.range 12, a0 ≠ a1 → a0 ≠ a2 → a0 ≠ a3 → a1 ≠ a2 →
      a1 ≠ a3 → a2 ≠ a3 → 4 ≤ a4 → ∃ t ∈ HT, t.take 5 = [a0, a1, a2, a3, a4] :=
  hyp_core_checks_2

theorem HT_center :
    ∀ t ∈ HT, (∀ s ∈ HT, tmul t s = tmul s t) → t = tid ∨ t = JT :=
  hyp_core_checks_3.1

theorem HT_noncomm : ∃ c ∈ HT, ∃ d ∈ HT, tcomm c d ≠ tid :=
  hyp_core_checks_3.2.1

theorem QT_length : QT.length = 32 :=
  hyp_core_checks_3.2.2.1

theorem tid_mem_QT : tid ∈ QT :=
  hyp_core_checks_3.2.2.2.1

theorem JT_mem_QT : JT ∈ QT :=
  hyp_core_checks_3.2.2.2.2.1

theorem QT_mul : ∀ s ∈ QT, ∀ t ∈ QT, tmul s t ∈ QT :=
  hyp_core_checks_3.2.2.2.2.2

theorem QT_inv : ∀ s ∈ QT, tinv s ∈ QT :=
  hyp_core_checks_4.1

theorem QT_normal :
    ∀ c ∈ HT, ∀ q ∈ QT, tmul (tmul c q) (tinv c) ∈ QT :=
  hyp_core_checks_4.2.1

theorem QT_center :
    ∀ s ∈ QT, ((∀ t ∈ QT, tmul s t = tmul t s) ↔ (s = tid ∨ s = JT)) :=
  hyp_core_checks_4.2.2.1

theorem QT_comm :
    ∀ s ∈ QT, ∀ t ∈ QT, tcomm s t = tid ∨ tcomm s t = JT :=
  hyp_core_checks_4.2.2.2.1

theorem QT_sq : ∀ s ∈ QT, tmul s s = tid ∨ tmul s s = JT :=
  hyp_core_checks_4.2.2.2.2.1

theorem QT_noncentral : ∃ s ∈ QT, s ≠ tid ∧ s ≠ JT :=
  hyp_core_checks_4.2.2.2.2.2

theorem HQ_noncomm : ∃ c ∈ HT, ∃ d ∈ HT, tcomm c d ∉ QT :=
  hyp_core_checks_5.1

theorem QT_order3 : ∀ x ∈ HT, tmul x (tmul x x) = tid → x ≠ tid →
    ∀ q ∈ QT, tmul q x = tmul x q → q = tid ∨ q = JT :=
  hyp_core_checks_5.2.1

theorem XT_mem_QT : XT ∈ QT :=
  hyp_core_checks_5.2.2.1

theorem XT_ne_JT : XT ≠ JT :=
  hyp_core_checks_5.2.2.2.1

theorem Q1T_length : Q1T.length = 8 :=
  hyp_core_checks_5.2.2.2.2.1

theorem Q2T_length : Q2T.length = 8 :=
  hyp_core_checks_5.2.2.2.2.2

theorem Q1T_nodup : Q1T.Nodup :=
  hyp_core_checks_6.1

theorem Q2T_nodup : Q2T.Nodup :=
  hyp_core_checks_6.2.1

theorem Q1T_sub : ∀ t ∈ Q1T, t ∈ QT :=
  hyp_core_checks_6.2.2.1

theorem Q2T_sub : ∀ t ∈ Q2T, t ∈ QT :=
  hyp_core_checks_6.2.2.2.1

theorem tid_mem_Q1T : tid ∈ Q1T :=
  hyp_core_checks_6.2.2.2.2.1

theorem tid_mem_Q2T : tid ∈ Q2T :=
  hyp_core_checks_6.2.2.2.2.2

theorem Q1T_mul : ∀ s ∈ Q1T, ∀ t ∈ Q1T, tmul s t ∈ Q1T :=
  hyp_core_checks_7.1

theorem Q2T_mul : ∀ s ∈ Q2T, ∀ t ∈ Q2T, tmul s t ∈ Q2T :=
  hyp_core_checks_7.2.1

theorem Q1T_inv : ∀ s ∈ Q1T, tinv s ∈ Q1T :=
  hyp_core_checks_7.2.2.1

theorem Q2T_inv : ∀ s ∈ Q2T, tinv s ∈ Q2T :=
  hyp_core_checks_7.2.2.2.1

theorem Q1T_normal :
    ∀ c ∈ HT, ∀ q ∈ Q1T, tmul (tmul c q) (tinv c) ∈ Q1T :=
  hyp_core_checks_7.2.2.2.2.1

theorem Q2T_normal :
    ∀ c ∈ HT, ∀ q ∈ Q2T, tmul (tmul c q) (tinv c) ∈ Q2T :=
  hyp_core_checks_7.2.2.2.2.2

theorem Q8_classification :
    ∀ x ∈ QT, ∀ y ∈ QT, tpow x 4 = tid → tpow x 2 ≠ tid →
    tmul y y = tpow x 2 → tmul y x = tmul (tpow x 3) y →
      (x ∈ Q1T ∧ y ∈ Q1T) ∨ (x ∈ Q2T ∧ y ∈ Q2T) :=
  hyp_core_checks_8

theorem BT_length : BT.length = 64 :=
  hyp_core_checks_9.1

theorem BT_nodup : BT.Nodup :=
  hyp_core_checks_9.2.1

theorem tid_mem_BT : tid ∈ BT :=
  hyp_core_checks_9.2.2.1

theorem BT_mul : ∀ s ∈ BT, ∀ t ∈ BT, tmul s t ∈ BT :=
  hyp_core_checks_9.2.2.2.1

theorem BT_inv : ∀ s ∈ BT, tinv s ∈ BT :=
  hyp_core_checks_9.2.2.2.2.1

theorem BT_sub_HT : ∀ t ∈ BT, t ∈ HT :=
  hyp_core_checks_9.2.2.2.2.2

theorem ET_mem_BT : ET ∈ BT :=
  hyp_core_checks_10.1

theorem NT_mem_BT : NT ∈ BT :=
  hyp_core_checks_10.2.1

theorem FT_mem_BT : FT ∈ BT :=
  hyp_core_checks_10.2.2.1

theorem JT_mem_BT : JT ∈ BT :=
  hyp_core_checks_10.2.2.2.1

theorem XT_mem_BT : XT ∈ BT :=
  hyp_core_checks_10.2.2.2.2.1

theorem BT_central_involution :
    ∀ s ∈ BT, (∀ t ∈ BT, tmul s t = tmul t s) →
    tmul s s = tid → s ≠ tid → s = JT :=
  hyp_core_checks_10.2.2.2.2.2

theorem QT_nodup : QT.Nodup := HT_nodup.filter _

end CFSG.GH74.M12.Hyp
