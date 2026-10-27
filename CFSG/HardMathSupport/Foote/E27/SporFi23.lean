module

public import CFSG.HardMathSupport.Foote.E27.SporCommData
public import CFSG.HardMathSupport.Foote.E27.SporFi23Action
public import CFSG.RankThree.Asc83Table.MatCert
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TcGenDefs
public import Certificates.Certificate9507
public import CFSG.Sporadic.Fi23.Simple
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.HardMathSupport.Foote.E27.Fi23

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table
  CFSG.RankThree.Asc83Table.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.Fi23Three
  CFSG.Monster.B.Pinned Subgroup

abbrev Ct : MCert := ⟨tcNregs, tcProg, tcSpec.facts⟩

@[expose] def creg : Fin 8 → ℕ := ![22, 24, 26, 27, 28, 29, 30, 31]

@[expose] def cbase : Fin 8 → ℕ := ![6, 16, 25, 33, 40, 46, 51, 55]

@[expose] def MRows : List (List ℕ) :=
  [[0, 1, 2, 0, 0, 1, 1, 1], [2, 0, 0, 0, 0, 2, 0, 2], [1, 0, 0, 1, 1, 1, 0, 2],
    [0, 0, 2, 0, 0, 0, 2, 2], [0, 0, 2, 0, 0, 0, 0, 0], [2, 1, 2, 0, 0, 0, 0, 0],
    [2, 0, 0, 1, 0, 0, 0, 0], [2, 1, 1, 1, 0, 0, 0, 0]]

@[expose] def MiRows : List (List ℕ) :=
  [[0, 0, 0, 0, 2, 2, 2, 1], [0, 0, 0, 0, 1, 0, 2, 1], [0, 0, 0, 0, 2, 0, 0, 0],
    [0, 0, 0, 0, 2, 2, 0, 1], [1, 2, 1, 1, 0, 0, 0, 2], [1, 0, 0, 1, 0, 0, 1, 2],
    [1, 1, 0, 0, 0, 2, 0, 0], [2, 2, 0, 2, 1, 1, 0, 0]]

@[expose] def MFi : Matrix (Fin 8) (Fin 8) (ZMod 3) := rowsMat 3 8 MRows

theorem M_mul_inv : MFi * rowsMat 3 8 MiRows = 1 := by decide +kernel

theorem M_antisymm (i j : Fin 8) : MFi i j = - MFi j i := by
  fin_cases i <;> fin_cases j <;> rfl

@[expose] def cX : Fin 8 → ℕ := ![1, 0, 2, 2, 0, 0, 0, 0]

@[expose] def cY : Fin 8 → ℕ := ![2, 0, 2, 2, 0, 2, 1, 0]

@[expose] def fullWord (A : Matrix (Fin 8) (Fin 8) (ZMod 3)) (c : Fin 8 → ℕ) (i : Fin 8) : Word :=
  List.ofFn (fun j : Fin 8 => (33 + (j : ℕ), (A i j).val)) ++ [(41, c i)]

@[expose] def chainWord (i j : Fin 8) : Word :=
  [(creg j, 1), (32, (MFi i j).val)].filter fun a => a.2 ≠ 0

theorem fact_ord_q (j : Fin 8) : Ct.facts[58 + 2 * (j : ℕ)]? = some (MFact.ord (33 + j) 3) := by
  fin_cases j <;> rfl

theorem fact_eq_q (j : Fin 8) :
    Ct.facts[59 + 2 * (j : ℕ)]? = some (MFact.eq [(33 + (j : ℕ), 1)] [(creg j, 1)]) := by
  fin_cases j <;> rfl

theorem fact_ord_chain (j : Fin 8) :
    Ct.facts[cbase j - 2]? = some (MFact.ord (creg j) 3) := by
  fin_cases j <;> rfl

theorem fact_chain (i j : Fin 8) (hij : i < j) :
    Ct.facts[cbase i + ((j : ℕ) - i - 1)]? =
      some (MFact.conj (creg i) [(creg j, 1)] (chainWord i j)) := by
  fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | rfl

theorem fact_zc (i : Fin 8) :
    Ct.facts[cbase i + (7 - (i : ℕ))]? = some (MFact.conj (creg i) [(32, 1)] [(32, 1)]) := by
  fin_cases i <;> rfl

theorem fact_act_x (i : Fin 8) :
    Ct.facts[121 + (i : ℕ)]? = some (MFact.conj 45 [(33 + (i : ℕ), 1)]
      ((fullWord (rowsMat 3 8 XRows) cX i).filter fun a => a.2 ≠ 0)) := by
  fin_cases i <;> rfl

theorem fact_act_h (i : Fin 8) :
    Ct.facts[131 + (i : ℕ)]? = some (MFact.conj 46 [(33 + (i : ℕ), 1)]
      ((fullWord (rowsMat 3 8 YRows) cY i).filter fun a => a.2 ≠ 0)) := by
  fin_cases i <;> rfl

theorem hasOrd_regs {w : Word} (hw : ∀ a ∈ w, a.1 ∈ ([22, 24, 26, 27, 28, 29, 30, 31, 32, 33, 34,
    35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46] : List ℕ)) : HasOrd Ct w := by
  have hord : ∀ r ∈ ([22, 24, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42,
      43, 44, 45, 46] : List ℕ), ∃ e, MFact.ord r e ∈ Ct.facts := by
    intro r hr
    have h1 : HasOrd Ct [(r, 0)] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hasOrd_of_bool (by decide +kernel)
    exact h1 (r, 0) (by simp)
  intro a ha
  exact hord a.1 (hw a ha)

section Certificate


theorem hCt : mcertCheck (ops3 253) NativeSporadic.Fi23Seed1 NativeSporadic.Fi23Seed2 Ct = true := by
  have h := Certificates.certificate9507.1
  unfold tcCheck at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1

local notation "Rg" r => regUnit (spec3 253) hCt r

local notation "Wd" w => wordUnit (spec3 253) hCt w

theorem Wd_single (r : ℕ) : (Wd [(r, 1)]) = Rg r := by
  rw [wordUnit_cons, wordUnit_nil, pow_one, mul_one]

theorem Wd_filter : ∀ w : Word, (Wd (w.filter fun a => a.2 ≠ 0)) = Wd w
  | [] => rfl
  | a :: w => by
    by_cases h : a.2 = 0
    · rw [List.filter_cons_of_neg (by simpa using h), Wd_filter w, wordUnit_cons, h, pow_zero,
        one_mul]
    · rw [List.filter_cons_of_pos (by simpa using h), wordUnit_cons, wordUnit_cons, Wd_filter w]

@[expose] noncomputable def q (i : Fin 8) : NativeSporadic.Fi23 := Rg (33 + (i : ℕ))

@[expose] noncomputable def zq : NativeSporadic.Fi23 := Rg 41

theorem q_def (i : Fin 8) : q i = Rg (33 + (i : ℕ)) := rfl

theorem zq_def : zq = Rg 41 := rfl

theorem Rg_creg (j : Fin 8) : (Rg (creg j)) = q j := by
  have h := regUnit_eq (spec3 253) hCt (mem_facts _ (fact_eq_q j))
    (hasOrd_regs (by fin_cases j <;> decide)) (hasOrd_regs (by fin_cases j <;> decide))
  rw [Wd_single, Wd_single] at h
  rw [q_def, h]

theorem Rg_32 : (Rg 32) = zq := by
  have h := regUnit_eq (spec3 253) hCt (mem_facts 75 rfl : MFact.eq [(41, 1)] [(32, 1)] ∈ Ct.facts)
    (hasOrd_regs (by decide)) (hasOrd_regs (by decide))
  rw [Wd_single, Wd_single] at h
  rw [zq_def, h]

theorem q_pow (i : Fin 8) : q i ^ 3 = 1 :=
  regUnit_pow (spec3 253) hCt (mem_facts _ (fact_ord_q i))

theorem zq_pow : zq ^ 3 = 1 := regUnit_pow (spec3 253) hCt (mem_facts 74 rfl)

theorem zq_ne_one : zq ≠ 1 := by
  have h := regUnit_ne (spec3 253) hCt
    (mem_facts 94 rfl : MFact.ne [(42, 0), (43, 0), (44, 1)] [] 0 ∈ Ct.facts)
    (hasOrd_regs (by decide)) (hasOrd_regs (by decide))
  have h44 := regUnit_eq (spec3 253) hCt
    (mem_facts 81 rfl : MFact.eq [(44, 1)] [(32, 1)] ∈ Ct.facts) (hasOrd_regs (by decide))
    (hasOrd_regs (by decide))
  rw [Wd_single, Wd_single] at h44
  simp only [wordUnit_cons, wordUnit_nil, pow_zero, pow_one, one_mul, mul_one] at h
  rw [h44, Rg_32] at h
  exact h

theorem conj_zq (i : Fin 8) : q i * zq * (q i)⁻¹ = zq := by
  have h := regUnit_conj (spec3 253) hCt (mem_facts _ (fact_zc i))
    (mem_facts _ (fact_ord_chain i)) (hasOrd_regs (by decide)) (hasOrd_regs (by decide))
  rw [Wd_single, Rg_creg, Rg_32] at h
  exact h

theorem comm_zq (i : Fin 8) : q i * zq = zq * q i := by
  have h := conj_zq i
  rw [mul_inv_eq_iff_eq_mul] at h
  exact h

theorem conj_chain (i j : Fin 8) (hij : i < j) :
    q i * q j * (q i)⁻¹ = q j * zq ^ (MFi i j).val := by
  have h := regUnit_conj (spec3 253) hCt (mem_facts _ (fact_chain i j hij))
    (mem_facts _ (fact_ord_chain i)) (hasOrd_regs (by fin_cases j <;> decide))
    (hasOrd_regs (by
      intro a ha
      have ha' := List.mem_of_mem_filter ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
      rcases ha' with rfl | rfl
      · fin_cases j <;> decide
      · show 32 ∈ _
        decide))
  rw [chainWord, Wd_filter] at h
  simp only [wordUnit_cons, wordUnit_nil, pow_one, mul_one] at h
  rw [Rg_creg, Rg_creg, Rg_32] at h
  exact h

theorem commData : CommData 3 q zq MFi :=
  commData_of_rel M_antisymm (fun i => by fin_cases i <;> rfl)
    (Matrix.isUnit_det_of_right_inverse M_mul_inv) (i₀ := 0) (j₀ := 1) (by decide +kernel) q_pow
    zq_pow zq_ne_one conj_zq conj_chain

theorem Wd_fullWord (A : Matrix (Fin 8) (Fin 8) (ZMod 3)) (c : Fin 8 → ℕ) (i : Fin 8) :
    (Wd (fullWord A c i)) = (List.ofFn fun j => q j ^ (A i j).val).prod * zq ^ c i := by
  rw [fullWord, wordUnit_append, wordUnit_cons, wordUnit_nil, mul_one, zq_def]
  congr 1

theorem hasOrd_fullWord (A : Matrix (Fin 8) (Fin 8) (ZMod 3)) (c : Fin 8 → ℕ) (i : Fin 8) :
    HasOrd Ct ((fullWord A c i).filter fun a => a.2 ≠ 0) := by
  apply hasOrd_regs
  intro a ha
  have ha' := List.mem_of_mem_filter ha
  simp only [fullWord, List.mem_append, List.mem_ofFn, List.mem_cons, List.not_mem_nil,
    or_false] at ha'
  have hj : ∀ j : Fin 8, 33 + (j : ℕ) ∈ ([22, 24, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37,
      38, 39, 40, 41, 42, 43, 44, 45, 46] : List ℕ) := by decide
  rcases ha' with ⟨j, rfl⟩ | rfl
  · exact hj j
  · show 41 ∈ _
    decide

@[expose] noncomputable def b₁ : NativeSporadic.Fi23 := (Rg 45)⁻¹

@[expose] noncomputable def b₂ : NativeSporadic.Fi23 := (Rg 46)⁻¹

theorem conj_b₁ (i : Fin 8) :
    b₁⁻¹ * q i * b₁ = (List.ofFn fun j => q j ^ (rowsMat 3 8 XRows i j).val).prod * zq ^ cX i := by
  have h := regUnit_conj (spec3 253) hCt (mem_facts _ (fact_act_x i))
    (mem_facts 120 rfl : MFact.ord 45 3 ∈ Ct.facts) (hasOrd_regs (by fin_cases i <;> decide))
    (hasOrd_fullWord _ _ i)
  rw [Wd_filter, Wd_fullWord, Wd_single, ← q_def] at h
  rw [b₁, inv_inv]
  exact h

theorem conj_b₂ (i : Fin 8) :
    b₂⁻¹ * q i * b₂ = (List.ofFn fun j => q j ^ (rowsMat 3 8 YRows i j).val).prod * zq ^ cY i := by
  have h := regUnit_conj (spec3 253) hCt (mem_facts _ (fact_act_h i))
    (mem_facts 130 rfl : MFact.ord 46 16 ∈ Ct.facts) (hasOrd_regs (by fin_cases i <;> decide))
    (hasOrd_fullWord _ _ i)
  rw [Wd_filter, Wd_fullWord, Wd_single, ← q_def] at h
  rw [b₂, inv_inv]
  exact h

end Certificate

section Kill


theorem finite_Fi23 : Finite NativeSporadic.Fi23 :=
  Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi23.card_Fi23]; norm_num)

theorem factorization_card_Fi23 : (Nat.card NativeSporadic.Fi23).factorization 3 = 13 := by
  rw [CFSG.Sporadic.Fi23.card_Fi23, show (4089470473293004800 : ℕ) = 3 ^ 13 * 2565020057600 by
      norm_num, Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem _root_.CFSG.HardMathSupport.Foote.E27.E27Config.false_of_fi23 {X : Type} [Group X]
    [Finite X] {K R T : Subgroup X} {z : X} (hc : E27Config X K R T z) (hz : z ∈ K)
    (e : ↥K ≃* NativeSporadic.Fi23) : False := by
  have hfin := finite_Fi23
  obtain ⟨hLQ, hL⟩ := @local_of_rel NativeSporadic.Fi23 inferInstance hfin 8 MFi q zq b₁ b₂
    commData XU YU cX cY conj_b₁ conj_b₂ 4 three_pow_four_dvd_card_K
  refine @E27Config.false_of_commData X _ _ K R T z hc hz NativeSporadic.Fi23 inferInstance hfin
    e 4 le_rfl q zq MFi commData _ hLQ ?_
  rw [factorization_card_Fi23]
  exact hL

theorem _root_.CFSG.HardMathSupport.Foote.E27.E27Config.false_of_sporadic_fi23 {X : Type}
    [Group X] [Finite X] {K R T : Subgroup X} {z : X} (hc : E27Config X K R T z) (hz : z ∈ K)
    (hbr : Nonempty (NativeSporadic.Carrier .Fi23 ≃* (TauCeti.CFSGIndex.sporadic .Fi23).Group))
    (e : ↥K ≃* (TauCeti.CFSGIndex.sporadic .Fi23).Group) : False :=
  hc.false_of_fi23 hz (e.trans hbr.some.symm)

end Kill

end CFSG.HardMathSupport.Foote.E27.Fi23
