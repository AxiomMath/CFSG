module

public import CFSG.HardMathSupport.Foote.E27.SporCommData
public import CFSG.HardMathSupport.Foote.E27.SporFi24Action
public import CFSG.RankThree.Asc83Table.MatCert
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi24ThreeChecks
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TcGenSound
public import Certificates.Certificate9509
public import Certificates.Certificate9510
public import CFSG.Sporadic.Fi24.Simple
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.Fi24.Faithful
public import CFSG.Sporadic.Fi24.SepSpec
public import Certificates.Certificate1016Base

public section

namespace CFSG.HardMathSupport.Foote.E27.Fi24

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table
  CFSG.RankThree.Asc83Table.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.Fi24Three
  CFSG.Monster.B.Pinned

abbrev Ct : MCert := ⟨tcNregs, tcProg, tcSpec.facts⟩

@[expose] def creg : Fin 10 → ℕ := ![22, 24, 25, 26, 27, 28, 29, 30, 31, 32]

@[expose] def cbase : Fin 10 → ℕ := ![6, 18, 29, 39, 48, 56, 63, 69, 74, 78]

@[expose] def MRows : List (List ℕ) :=
  [[0, 2, 0, 1, 2, 0, 0, 1, 0, 1], [1, 0, 0, 0, 0, 0, 0, 0, 2, 0],
    [0, 0, 0, 0, 1, 2, 0, 0, 2, 2], [2, 0, 0, 0, 2, 1, 1, 2, 1, 1],
    [1, 0, 2, 1, 0, 2, 2, 2, 0, 2], [0, 0, 1, 2, 1, 0, 0, 2, 2, 2],
    [0, 0, 0, 2, 1, 0, 0, 1, 1, 2], [2, 0, 0, 1, 1, 1, 2, 0, 1, 1],
    [0, 1, 1, 2, 0, 1, 2, 2, 0, 2], [2, 0, 1, 2, 1, 1, 1, 2, 1, 0]]

@[expose] def MiRows : List (List ℕ) :=
  [[0, 2, 1, 0, 1, 1, 2, 2, 0, 0], [1, 0, 2, 0, 2, 0, 0, 2, 2, 0],
    [2, 1, 0, 0, 0, 2, 2, 1, 2, 0], [0, 0, 0, 0, 1, 0, 2, 0, 0, 1],
    [2, 1, 0, 2, 0, 0, 0, 1, 2, 1], [2, 0, 1, 0, 0, 0, 1, 2, 2, 1],
    [1, 0, 1, 1, 0, 2, 0, 2, 1, 0], [1, 1, 2, 0, 2, 1, 1, 0, 1, 0],
    [0, 1, 1, 0, 1, 1, 2, 2, 0, 0], [0, 0, 0, 2, 2, 2, 0, 0, 0, 0]]

@[expose] def MFi : Matrix (Fin 10) (Fin 10) (ZMod 3) := rowsMat 3 10 MRows

theorem M_mul_inv : MFi * rowsMat 3 10 MiRows = 1 := by decide +kernel

theorem M_antisymm (i j : Fin 10) : MFi i j = - MFi j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem M_diag (i : Fin 10) : MFi i i = 0 := by
  fin_cases i <;> rfl

@[expose] def cX : Fin 10 → ℕ := ![1, 0, 1, 1, 2, 1, 0, 1, 2, 1]

@[expose] def cY : Fin 10 → ℕ := ![1, 1, 1, 2, 0, 1, 0, 0, 2, 1]

@[expose] def fullWord (A : Matrix (Fin 10) (Fin 10) (ZMod 3)) (c : Fin 10 → ℕ) (i : Fin 10) :
    Word :=
  List.ofFn (fun j : Fin 10 => (34 + (j : ℕ), (A i j).val)) ++ [(44, c i)]

@[expose] def chainWord (i j : Fin 10) : Word :=
  [(creg j, 1), (33, (MFi i j).val)].filter fun a => a.2 ≠ 0

theorem fact_ord_q (j : Fin 10) : Ct.facts[81 + 2 * (j : ℕ)]? = some (MFact.ord (34 + j) 3) := by
  fin_cases j <;> rfl

theorem fact_eq_q (j : Fin 10) :
    Ct.facts[82 + 2 * (j : ℕ)]? = some (MFact.eq [(34 + (j : ℕ), 1)] [(creg j, 1)]) := by
  fin_cases j <;> rfl

theorem fact_ord_chain (j : Fin 10) : Ct.facts[cbase j - 2]? = some (MFact.ord (creg j) 3) := by
  fin_cases j <;> rfl

theorem fact_chain (i j : Fin 10) (hij : i < j) :
    Ct.facts[cbase i + ((j : ℕ) - i - 1)]? =
      some (MFact.conj (creg i) [(creg j, 1)] (chainWord i j)) := by
  fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | rfl

theorem fact_zc (i : Fin 10) :
    Ct.facts[cbase i + (9 - (i : ℕ))]? = some (MFact.conj (creg i) [(33, 1)] [(33, 1)]) := by
  fin_cases i <;> rfl

theorem fact_act_x (i : Fin 10) :
    Ct.facts[150 + (i : ℕ)]? = some (MFact.conj 49 [(34 + (i : ℕ), 1)]
      ((fullWord (rowsMat 3 10 XRows) cX i).filter fun a => a.2 ≠ 0)) := by
  fin_cases i <;> rfl

theorem fact_act_h (i : Fin 10) :
    Ct.facts[162 + (i : ℕ)]? = some (MFact.conj 50 [(34 + (i : ℕ), 1)]
      ((fullWord (rowsMat 3 10 YRows) cY i).filter fun a => a.2 ≠ 0)) := by
  fin_cases i <;> rfl

@[expose] def ordRegs : List ℕ :=
  [22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 46, 47,
    48, 49, 50]

theorem hasOrd_regs {w : Word} (hw : ∀ a ∈ w, a.1 ∈ ordRegs) : HasOrd Ct w := by
  have hord : ∀ r ∈ ordRegs, ∃ e, MFact.ord r e ∈ Ct.facts := by
    intro r hr
    have h1 : HasOrd Ct [(r, 0)] := by
      simp only [ordRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl <;> exact hasOrd_of_bool (by decide +kernel)
    exact h1 (r, 0) (by simp)
  intro a ha
  exact hord a.1 (hw a ha)

theorem hasOrd_fullWord (A : Matrix (Fin 10) (Fin 10) (ZMod 3)) (c : Fin 10 → ℕ) (i : Fin 10) :
    HasOrd Ct ((fullWord A c i).filter fun a => a.2 ≠ 0) := by
  apply hasOrd_regs
  intro a ha
  have ha' := List.mem_of_mem_filter ha
  simp only [fullWord, List.mem_append, List.mem_ofFn, List.mem_cons, List.not_mem_nil,
    or_false] at ha'
  have hj : ∀ j : Fin 10, 34 + (j : ℕ) ∈ ordRegs := by decide
  rcases ha' with ⟨j, rfl⟩ | rfl
  · exact hj j
  · show 44 ∈ _
    decide

section Certificate


theorem hCt : mcertCheck (matOps 3 781) NativeSporadic.Fi24primeSeed1
    NativeSporadic.Fi24primeSeed2 Ct = true := by
  have h := tcCheck_Fi24
  unfold tcCheck at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1

local notation "Rg" r => regUnit (matOpsSpec 3 781) hCt r

local notation "Wd" w => wordUnit (matOpsSpec 3 781) hCt w

theorem Wd_single (r : ℕ) : (Wd [(r, 1)]) = Rg r := by
  rw [wordUnit_cons, wordUnit_nil, pow_one, mul_one]

theorem Wd_filter : ∀ w : Word, (Wd (w.filter fun a => a.2 ≠ 0)) = Wd w
  | [] => rfl
  | a :: w => by
    by_cases h : a.2 = 0
    · rw [List.filter_cons_of_neg (by simpa using h), Wd_filter w, wordUnit_cons, h, pow_zero,
        one_mul]
    · rw [List.filter_cons_of_pos (by simpa using h), wordUnit_cons, wordUnit_cons, Wd_filter w]

@[expose] noncomputable def q (i : Fin 10) : NativeSporadic.Fi24prime := Rg (34 + (i : ℕ))

@[expose] noncomputable def zq : NativeSporadic.Fi24prime := Rg 33

theorem q_def (i : Fin 10) : q i = Rg (34 + (i : ℕ)) := rfl

theorem zq_def : zq = Rg 33 := rfl

theorem Rg_creg (j : Fin 10) : (Rg (creg j)) = q j := by
  have h := regUnit_eq (matOpsSpec 3 781) hCt (mem_facts _ (fact_eq_q j))
    (hasOrd_regs (by fin_cases j <;> decide)) (hasOrd_regs (by fin_cases j <;> decide))
  rw [Wd_single, Wd_single] at h
  rw [q_def, h]

theorem Rg_44 : (Rg 44) = zq ^ 2 := by
  have h := regUnit_eq (matOpsSpec 3 781) hCt (mem_facts 102 rfl : MFact.eq [(44, 1)] [(33, 2)] ∈ Ct.facts)
    (hasOrd_regs (by decide)) (hasOrd_regs (by decide))
  rw [Wd_single, wordUnit_cons, wordUnit_nil, mul_one] at h
  rw [zq_def, h]

theorem q_pow (i : Fin 10) : q i ^ 3 = 1 :=
  regUnit_pow (matOpsSpec 3 781) hCt (mem_facts _ (fact_ord_q i))

theorem zq_pow : zq ^ 3 = 1 := regUnit_pow (matOpsSpec 3 781) hCt (mem_facts 79 rfl)

theorem zq_ne_one : zq ≠ 1 := by
  have h := regUnit_ne (matOpsSpec 3 781) hCt
    (mem_facts 123 rfl : MFact.ne [(46, 0), (47, 0), (48, 1)] [] 0 ∈ Ct.facts)
    (hasOrd_regs (by decide)) (hasOrd_regs (by decide))
  have h48 := regUnit_eq (matOpsSpec 3 781) hCt
    (mem_facts 108 rfl : MFact.eq [(48, 1)] [(33, 2)] ∈ Ct.facts) (hasOrd_regs (by decide))
    (hasOrd_regs (by decide))
  rw [Wd_single, wordUnit_cons, wordUnit_nil, mul_one] at h48
  simp only [wordUnit_cons, wordUnit_nil, pow_zero, pow_one, one_mul, mul_one] at h
  rw [h48, ← zq_def] at h
  intro hz
  apply h
  rw [hz, one_pow]

theorem conj_zq (i : Fin 10) : q i * zq * (q i)⁻¹ = zq := by
  have h := regUnit_conj (matOpsSpec 3 781) hCt (mem_facts _ (fact_zc i))
    (mem_facts _ (fact_ord_chain i)) (hasOrd_regs (by decide)) (hasOrd_regs (by decide))
  rw [Wd_single, Rg_creg, ← zq_def] at h
  exact h

theorem conj_chain (i j : Fin 10) (hij : i < j) :
    q i * q j * (q i)⁻¹ = q j * zq ^ (MFi i j).val := by
  have h := regUnit_conj (matOpsSpec 3 781) hCt (mem_facts _ (fact_chain i j hij))
    (mem_facts _ (fact_ord_chain i)) (hasOrd_regs (by fin_cases j <;> decide))
    (hasOrd_regs (by
      intro a ha
      have ha' := List.mem_of_mem_filter ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
      rcases ha' with rfl | rfl
      · fin_cases j <;> decide
      · show 33 ∈ _
        decide))
  rw [chainWord, Wd_filter] at h
  simp only [wordUnit_cons, wordUnit_nil, pow_one, mul_one] at h
  rw [Rg_creg, Rg_creg, ← zq_def] at h
  exact h

theorem commData : CommData 3 q zq MFi :=
  commData_of_rel M_antisymm M_diag (Matrix.isUnit_det_of_right_inverse M_mul_inv) (i₀ := 0)
    (j₀ := 3) (by decide +kernel) q_pow zq_pow zq_ne_one conj_zq conj_chain

theorem Wd_fullWord (A : Matrix (Fin 10) (Fin 10) (ZMod 3)) (c : Fin 10 → ℕ) (i : Fin 10) :
    (Wd (fullWord A c i)) = (List.ofFn fun j => q j ^ (A i j).val).prod * zq ^ (2 * c i) := by
  rw [fullWord, wordUnit_append, wordUnit_cons, wordUnit_nil, mul_one]
  have h1 : (Wd (List.ofFn fun j : Fin 10 => (34 + (j : ℕ), (A i j).val))) =
      (List.ofFn fun j => q j ^ (A i j).val).prod := by
    rw [wordUnit, List.map_ofFn]
    rfl
  have h2 : (Rg ((44, c i) : ℕ × ℕ).1) ^ ((44, c i) : ℕ × ℕ).2 = zq ^ (2 * c i) := by
    show (Rg 44) ^ c i = _
    rw [Rg_44, ← pow_mul]
  rw [h1, h2]

@[expose] noncomputable def b₁ : NativeSporadic.Fi24prime := (Rg 49)⁻¹

@[expose] noncomputable def b₂ : NativeSporadic.Fi24prime := (Rg 50)⁻¹

theorem conj_b₁ (i : Fin 10) :
    b₁⁻¹ * q i * b₁ = (List.ofFn fun j =>
      q j ^ ((XU : Matrix (Fin 10) (Fin 10) (ZMod 3)) i j).val).prod * zq ^ (2 * cX i) := by
  have h := regUnit_conj (matOpsSpec 3 781) hCt (mem_facts _ (fact_act_x i))
    (mem_facts 149 rfl : MFact.ord 49 36 ∈ Ct.facts) (hasOrd_regs (by fin_cases i <;> decide))
    (hasOrd_fullWord _ _ i)
  rw [Wd_filter, Wd_fullWord, Wd_single, ← q_def] at h
  rw [b₁, inv_inv, coe_XU]
  exact h

theorem conj_b₂ (i : Fin 10) :
    b₂⁻¹ * q i * b₂ = (List.ofFn fun j =>
      q j ^ ((YU : Matrix (Fin 10) (Fin 10) (ZMod 3)) i j).val).prod * zq ^ (2 * cY i) := by
  have h := regUnit_conj (matOpsSpec 3 781) hCt (mem_facts _ (fact_act_h i))
    (mem_facts 161 rfl : MFact.ord 50 12 ∈ Ct.facts) (hasOrd_regs (by fin_cases i <;> decide))
    (hasOrd_fullWord _ _ i)
  rw [Wd_filter, Wd_fullWord, Wd_single, ← q_def] at h
  rw [b₂, inv_inv, coe_YU]
  exact h

end Certificate

section Kill


theorem finite_Fi24 : Finite NativeSporadic.Fi24prime :=
  Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_Fi24prime]; norm_num)

theorem factorization_card_Fi24 : (Nat.card NativeSporadic.Fi24prime).factorization 3 = 16 := by
  rw [CFSG.Sporadic.Fi24.card_Fi24prime,
    show (1255205709190661721292800 : ℕ) = 3 ^ 16 * 29159148014796800 by norm_num,
    Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem _root_.CFSG.HardMathSupport.Foote.E27.E27Config.false_of_fi24 {X : Type} [Group X]
    [Finite X] {K R T : Subgroup X} {z : X} (hc : E27Config X K R T z) (hz : z ∈ K)
    (e : ↥K ≃* NativeSporadic.Fi24prime) : False := by
  have hfin := finite_Fi24
  obtain ⟨hLQ, hL⟩ := @local_of_rel NativeSporadic.Fi24prime inferInstance hfin 10 MFi q zq b₁ b₂
    commData XU YU (fun i => 2 * cX i) (fun i => 2 * cY i) conj_b₁ conj_b₂ 5
    three_pow_five_dvd_card_K
  refine @E27Config.false_of_commData X _ _ K R T z hc hz NativeSporadic.Fi24prime inferInstance
    hfin e 5 (by norm_num) q zq MFi commData _ hLQ ?_
  rw [factorization_card_Fi24]
  exact hL

theorem _root_.CFSG.HardMathSupport.Foote.E27.E27Config.false_of_sporadic_fi24 {X : Type}
    [Group X] [Finite X] {K R T : Subgroup X} {z : X} (hc : E27Config X K R T z) (hz : z ∈ K)
    (hbr : Nonempty (NativeSporadic.Carrier .Fi24Prime ≃*
      (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group))
    (e : ↥K ≃* (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group) : False :=
  hc.false_of_fi24 hz (e.trans hbr.some.symm)

end Kill

end CFSG.HardMathSupport.Foote.E27.Fi24
