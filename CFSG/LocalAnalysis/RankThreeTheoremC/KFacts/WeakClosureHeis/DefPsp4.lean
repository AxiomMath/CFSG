module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.LieDispatch
public import CFSG.RankThree.PartOne.CTP.StrongPNoncentral
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.FamilyTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.RankThree.PartOne.StrongP
open scoped MatrixGroups commutatorElement Matrix

namespace Psp4Aux

section Matrices

variable {F : Type} [Field F]

abbrev PIx := Fin 2 ⊕ Fin 2

def pRk : PIx → ℕ := Sum.elim (fun i => i.val) (fun i => 3 - i.val)

theorem pRk_lt (i : PIx) : pRk i < 4 := by
  rcases i with i | i <;> simp [pRk] <;> omega

def pZ (T : Matrix (Fin 2) (Fin 2) F) : Matrix PIx PIx F := Matrix.fromBlocks 1 T 0 1

theorem pZ_mul (T T' : Matrix (Fin 2) (Fin 2) F) : pZ T * pZ T' = pZ (T + T') := by
  simp only [pZ, Matrix.fromBlocks_multiply]
  simp [add_comm]

theorem pZ_zero : pZ (0 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  simp [pZ, ← Matrix.fromBlocks_one]

def pZU (T : Matrix (Fin 2) (Fin 2) F) : GL PIx F :=
  ⟨pZ T, pZ (-T), by rw [pZ_mul, add_neg_cancel, pZ_zero],
    by rw [pZ_mul, neg_add_cancel, pZ_zero]⟩

theorem pZU_mul (T T' : Matrix (Fin 2) (Fin 2) F) : pZU T * pZU T' = pZU (T + T') :=
  Units.ext (pZ_mul T T')

theorem pZU_zero : pZU (0 : Matrix (Fin 2) (Fin 2) F) = 1 := Units.ext pZ_zero

theorem pZU_inv (T : Matrix (Fin 2) (Fin 2) F) : (pZU T)⁻¹ = pZU (-T) :=
  inv_eq_of_mul_eq_one_right (by rw [pZU_mul, add_neg_cancel, pZU_zero])

theorem pZU_pow (T : Matrix (Fin 2) (Fin 2) F) (n : ℕ) : pZU T ^ n = pZU (n • T) := by
  induction n with
  | zero => simp [pZU_zero]
  | succ n ih => rw [pow_succ, ih, pZU_mul, succ_nsmul]

def pA : Matrix (Fin 2) (Fin 2) F := !![1, 1; 0, 1]
def pAi : Matrix (Fin 2) (Fin 2) F := !![1, -1; 0, 1]
def pD : Matrix (Fin 2) (Fin 2) F := !![1, 0; -1, 1]
def pDi : Matrix (Fin 2) (Fin 2) F := !![1, 0; 1, 1]

theorem pA_mul_Ai : (pA : Matrix (Fin 2) (Fin 2) F) * pAi = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pA, pAi, Matrix.mul_apply, Fin.sum_univ_two]

theorem pAi_mul_A : (pAi : Matrix (Fin 2) (Fin 2) F) * pA = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pA, pAi, Matrix.mul_apply, Fin.sum_univ_two]

theorem pD_mul_Di : (pD : Matrix (Fin 2) (Fin 2) F) * pDi = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pD, pDi, Matrix.mul_apply, Fin.sum_univ_two]

theorem pDi_mul_D : (pDi : Matrix (Fin 2) (Fin 2) F) * pD = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pD, pDi, Matrix.mul_apply, Fin.sum_univ_two]

def pY : Matrix PIx PIx F := Matrix.fromBlocks pA 0 0 pD
def pYi : Matrix PIx PIx F := Matrix.fromBlocks pAi 0 0 pDi

theorem pY_mul_Yi : (pY : Matrix PIx PIx F) * pYi = 1 := by
  simp [pY, pYi, Matrix.fromBlocks_multiply, pA_mul_Ai, pD_mul_Di, ← Matrix.fromBlocks_one]

theorem pYi_mul_Y : (pYi : Matrix PIx PIx F) * pY = 1 := by
  simp [pY, pYi, Matrix.fromBlocks_multiply, pAi_mul_A, pDi_mul_D, ← Matrix.fromBlocks_one]

def pYU : GL PIx F := ⟨pY, pYi, pY_mul_Yi, pYi_mul_Y⟩

theorem pYU_conj (T : Matrix (Fin 2) (Fin 2) F) :
    pYU * pZU T * pYU⁻¹ = pZU (pA * T * pDi) := by
  apply Units.ext
  show pY * pZ T * pYi = pZ _
  simp [pY, pZ, pYi, Matrix.fromBlocks_multiply, pA_mul_Ai, pD_mul_Di]

def pS : Matrix (Fin 2) (Fin 2) F := !![0, 0; 0, 1]
def pT1 : Matrix (Fin 2) (Fin 2) F := !![1, 1; 1, 0]
def pT2 : Matrix (Fin 2) (Fin 2) F := !![2, 0; 0, 0]

theorem pA_S_Di : (pA * pS * pDi : Matrix (Fin 2) (Fin 2) F) + -pS = pT1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pA, pS, pDi, pT1, Matrix.mul_apply, Fin.sum_univ_two]

theorem pA_T1_Di : (pA * pT1 * pDi : Matrix (Fin 2) (Fin 2) F) + -pT1 = pT2 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pA, pT1, pT2, pDi, Matrix.mul_apply, Fin.sum_univ_two, one_add_one_eq_two]

theorem pYU_comm_Z_S : ⁅(pYU : GL PIx F), pZU (pS : Matrix (Fin 2) (Fin 2) F)⁆ = pZU pT1 := by
  rw [commutatorElement_def, pYU_conj, pZU_inv, pZU_mul, pA_S_Di]

theorem pYU_comm_Z_T1 : ⁅(pYU : GL PIx F), pZU (pT1 : Matrix (Fin 2) (Fin 2) F)⁆ = pZU pT2 := by
  rw [commutatorElement_def, pYU_conj, pZU_inv, pZU_mul, pA_T1_Di]

theorem pZU_unitri (T : Matrix (Fin 2) (Fin 2) F) : IsUnitri pRk (pZU T) := by
  intro i j h
  change ((pZ T : Matrix PIx PIx F) - 1) i j ≠ 0 at h
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [pZ, pRk, Matrix.fromBlocks] at h ⊢

theorem pYU_unitri : IsUnitri pRk (pYU : GL PIx F) := by
  intro i j h
  change ((pY : Matrix PIx PIx F) - 1) i j ≠ 0 at h
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [pY, pA, pD, pRk, Matrix.fromBlocks] at h ⊢

theorem pS_transpose : (pS : Matrix (Fin 2) (Fin 2) F)ᵀ = pS := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pS]

theorem pA_transpose : (pA : Matrix (Fin 2) (Fin 2) F)ᵀ = pDi := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pA, pDi]

theorem pD_transpose : (pD : Matrix (Fin 2) (Fin 2) F)ᵀ = pAi := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [pD, pAi]

theorem pZU_mem (S : Matrix (Fin 2) (Fin 2) F) (hS : Sᵀ = S) : pZU S ∈ StatedSp 2 F := by
  apply Subgroup.subset_closure
  show (pZ S)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * pZ S = Matrix.fromBlocks 0 1 (-1) 0
  simp [pZ, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, hS]

theorem pYU_mem : (pYU : GL PIx F) ∈ StatedSp 2 F := by
  apply Subgroup.subset_closure
  show (pY)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * pY = Matrix.fromBlocks 0 1 (-1) 0
  simp [pY, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, pA_transpose,
    pD_transpose, pDi_mul_D, pAi_mul_A]

end Matrices

section Group

variable {F : Type} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p]

def pW (F : Type) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] : Subgroup (StatedSp 2 F) :=
  (unitriSubgroup p pRk 4 pRk_lt).subgroupOf (StatedSp 2 F)

theorem mem_pW {g : StatedSp 2 F} : g ∈ pW F p ↔ IsUnitri pRk (g : GL PIx F) := Iff.rfl

theorem pW_pow (h4 : 4 ≤ p) {g : StatedSp 2 F} (hg : g ∈ pW F p) : g ^ p = 1 := by
  apply Subtype.ext
  have := IsUnitri.pow_eq_one (p := p) pRk_lt (mem_pW.1 hg) 1 (by simpa using h4)
  simpa using this

theorem mk_inj {g h : StatedSp 2 F} (hg : g ∈ pW F p) (hh : h ∈ pW F p)
    (hgh : (QuotientGroup.mk g : StatedProj (StatedSp 2 F)) = QuotientGroup.mk h) : g = h := by
  rw [QuotientGroup.eq] at hgh
  have hs : ((g⁻¹ * h : StatedSp 2 F) : GL PIx F) ∈ StatedScalars PIx F := hgh
  have hu : IsUnitri pRk ((g⁻¹ * h : StatedSp 2 F) : GL PIx F) :=
    mem_pW.1 ((pW F p).mul_mem ((pW F p).inv_mem hg) hh)
  obtain ⟨c, hc⟩ := hs
  have hd := hu.diag (Sum.inl 0)
  rw [← hc] at hd
  simp at hd
  rw [hd, map_one] at hc
  have : g⁻¹ * h = 1 := Subtype.ext hc.symm
  exact inv_mul_eq_one.1 this

theorem commutator_mem_of_mem {G : Type*} [Group G] (H : Subgroup G) {a b : G} (ha : a ∈ H)
    (hb : b ∈ H) : ⁅a, b⁆ ∈ H := by
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem sylowDichotomyAt_proj_sp4 (h5 : 5 ≤ p) [Finite (StatedProj (StatedSp 2 F))] :
    SylowDichotomyAt (StatedProj (StatedSp 2 F)) p := by
  have hF2 : (2 : F) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) ((CharP.cast_eq_zero_iff F p 2).1 h')
    omega
  let φ : StatedSp 2 F →* StatedProj (StatedSp 2 F) := QuotientGroup.mk' _
  let U : Subgroup (StatedProj (StatedSp 2 F)) := (pW F p).map φ
  let x0 : StatedSp 2 F := ⟨pZU pS, pZU_mem pS pS_transpose⟩
  let y0 : StatedSp 2 F := ⟨pYU, pYU_mem⟩
  have hx0 : x0 ∈ pW F p := mem_pW.2 (pZU_unitri _)
  have hy0 : y0 ∈ pW F p := mem_pW.2 pYU_unitri
  have ha0 : ⁅y0, x0⁆ ∈ pW F p := commutator_mem_of_mem _ hy0 hx0
  have hb0 : ⁅y0, ⁅y0, x0⁆⁆ ∈ pW F p := commutator_mem_of_mem _ hy0 ha0
  have ha0val : ((⁅y0, x0⁆ : StatedSp 2 F) : GL PIx F) = pZU pT1 :=
    (map_commutatorElement (StatedSp 2 F).subtype y0 x0).trans pYU_comm_Z_S
  have hb0val : ((⁅y0, ⁅y0, x0⁆⁆ : StatedSp 2 F) : GL PIx F) = pZU pT2 := by
    calc ((⁅y0, ⁅y0, x0⁆⁆ : StatedSp 2 F) : GL PIx F)
        = ⁅(y0 : GL PIx F), ((⁅y0, x0⁆ : StatedSp 2 F) : GL PIx F)⁆ :=
          map_commutatorElement (StatedSp 2 F).subtype y0 ⁅y0, x0⁆
      _ = ⁅(pYU : GL PIx F), pZU pT1⁆ := by rw [ha0val]
      _ = pZU pT2 := pYU_comm_Z_T1
  have hp4 : 4 ≤ p := by omega
  refine SylowDichotomyAt.of_not_cyclic_derived (U := U) ?_ ?_
  ·
    intro u
    obtain ⟨g, hg, hgu⟩ := Subgroup.mem_map.1 u.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hgu]
    change φ g ^ p = 1
    rw [← map_pow, pW_pow hp4 hg, map_one]
  ·
    intro hcyc
    have hyU : φ y0 ∈ U := Subgroup.mem_map_of_mem φ hy0
    have hxU : φ x0 ∈ U := Subgroup.mem_map_of_mem φ hx0
    have haU : φ ⁅y0, x0⁆ ∈ U := Subgroup.mem_map_of_mem φ ha0
    have hA : φ ⁅y0, x0⁆ ∈ ⁅U, U⁆ := by
      rw [map_commutatorElement]
      exact Subgroup.commutator_mem_commutator hyU hxU
    have hB : φ ⁅y0, ⁅y0, x0⁆⁆ ∈ ⁅U, U⁆ := by
      rw [map_commutatorElement]
      exact Subgroup.commutator_mem_commutator hyU haU
    let a' : ↥⁅U, U⁆ := ⟨φ ⁅y0, x0⁆, hA⟩
    let b' : ↥⁅U, U⁆ := ⟨φ ⁅y0, ⁅y0, x0⁆⁆, hB⟩
    have hap : a' ^ p = 1 := by
      apply Subtype.ext
      change φ ⁅y0, x0⁆ ^ p = 1
      rw [← map_pow, pW_pow hp4 ha0, map_one]
    have hbp : b' ^ p = 1 := by
      apply Subtype.ext
      change φ ⁅y0, ⁅y0, x0⁆⁆ ^ p = 1
      rw [← map_pow, pW_pow hp4 hb0, map_one]
    have hb1 : b' ≠ 1 := by
      intro h
      have h1 : φ ⁅y0, ⁅y0, x0⁆⁆ = 1 := congrArg Subtype.val h
      have h2 : (⁅y0, ⁅y0, x0⁆⁆ : StatedSp 2 F) = 1 :=
        mk_inj hb0 (pW F p).one_mem (h1.trans (map_one φ).symm)
      have h3 : pZU (pT2 : Matrix (Fin 2) (Fin 2) F) = (1 : GL PIx F) := by
        rw [← hb0val, h2]; rfl
      have h4 : pZ (pT2 : Matrix (Fin 2) (Fin 2) F) = (1 : Matrix PIx PIx F) :=
        congrArg Units.val h3
      have h5' := congrFun (congrFun h4 (Sum.inl 0)) (Sum.inr 0)
      simp [pZ, pT2, Matrix.fromBlocks, Matrix.one_apply] at h5'
      exact hF2 h5'
    haveI : IsCyclic ↥⁅U, U⁆ := hcyc
    have hord : orderOf b' = p := orderOf_eq_prime hbp hb1
    have hcard : Nat.card (Subgroup.zpowers a') ∣ Nat.card (Subgroup.zpowers b') := by
      rw [Nat.card_zpowers, Nat.card_zpowers, hord]
      exact orderOf_dvd_of_pow_eq_one hap
    have hle : Subgroup.zpowers a' ≤ Subgroup.zpowers b' :=
      IsCyclic.subgroup_le_iff_card_dvd.2 hcard
    have hmem : a' ∈ Subgroup.zpowers b' := hle (Subgroup.mem_zpowers a')
    obtain ⟨n, hn⟩ : ∃ n : ℕ, b' ^ n = a' :=
      (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hmem)
    have hBA : φ ⁅y0, ⁅y0, x0⁆⁆ ^ n = φ ⁅y0, x0⁆ := congrArg Subtype.val hn
    have hq : φ (⁅y0, ⁅y0, x0⁆⁆ ^ n) = φ ⁅y0, x0⁆ := by rw [map_pow]; exact hBA
    have heq : (⁅y0, ⁅y0, x0⁆⁆ ^ n : StatedSp 2 F) = ⁅y0, x0⁆ :=
      mk_inj ((pW F p).pow_mem hb0 n) ha0 hq
    have hGL : (pZU (pT2 : Matrix (Fin 2) (Fin 2) F)) ^ n = pZU pT1 := by
      have := congrArg (fun g : StatedSp 2 F => (g : GL PIx F)) heq
      simp only [Subgroup.coe_pow] at this
      rw [hb0val, ha0val] at this
      exact this
    rw [pZU_pow] at hGL
    have hM : pZ (n • (pT2 : Matrix (Fin 2) (Fin 2) F)) = pZ (pT1 : Matrix (Fin 2) (Fin 2) F) :=
      congrArg Units.val hGL
    have := congrFun (congrFun hM (Sum.inl 0)) (Sum.inr 1)
    simp [pZ, pT1, pT2, Matrix.fromBlocks] at this

end Group

end Psp4Aux

theorem sdPsp4_holds : SDPsp4 := by
  intro K _ _ p hp h5 hmodel
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hmodel.statedClassicalModel_of_ne_zero (by norm_num)
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F p := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hcard, pow_one])
  haveI : Finite (StatedProj (StatedSp 2 F)) := Finite.of_equiv K e.toEquiv
  exact SylowDichotomyAt.of_mulEquiv hp e (Psp4Aux.sylowDichotomyAt_proj_sp4 h5)

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
