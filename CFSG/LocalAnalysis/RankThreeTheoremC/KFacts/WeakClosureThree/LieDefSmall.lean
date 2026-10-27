module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.Witness
public import CFSG.RankThree.PartOne.CTP.StrongPNoncentral
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.DefG2
public import CFSG.LocalAnalysis.SectionRank.SmallRee
public import CFSG.RankThree.PartOne.CTP.StrongPG2

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartOne.StrongP
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
open scoped MatrixGroups commutatorElement Matrix

namespace Psp4Three

open Matrix

section Matrices

variable {F : Type} [Field F]

abbrev Ix := Fin 2 ⊕ Fin 2

@[expose] def rk : Ix → ℕ := Sum.elim (fun i => i.val) (fun i => 3 - i.val)

theorem rk_lt (i : Ix) : rk i < 4 := by
  rcases i with i | i <;> simp [rk] <;> omega

@[expose] def rk2 : Ix → ℕ := Sum.elim (fun i => i.val) (fun i => 1 - i.val)

theorem rk2_lt (i : Ix) : rk2 i < 2 := by
  rcases i with i | i <;> simp [rk2] <;> omega

@[expose] def Xm (T : Matrix (Fin 2) (Fin 2) F) : Matrix Ix Ix F := fromBlocks 1 T 0 1

theorem Xm_mul (T T' : Matrix (Fin 2) (Fin 2) F) : Xm T * Xm T' = Xm (T + T') := by
  simp only [Xm, fromBlocks_multiply]
  simp [add_comm]

theorem Xm_zero : Xm (0 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  simp [Xm, ← fromBlocks_one]

@[expose] def XU (T : Matrix (Fin 2) (Fin 2) F) : GL Ix F :=
  ⟨Xm T, Xm (-T), by rw [Xm_mul, add_neg_cancel, Xm_zero],
    by rw [Xm_mul, neg_add_cancel, Xm_zero]⟩

theorem XU_mul (T T' : Matrix (Fin 2) (Fin 2) F) : XU T * XU T' = XU (T + T') :=
  Units.ext (Xm_mul T T')

theorem XU_zero : XU (0 : Matrix (Fin 2) (Fin 2) F) = 1 := Units.ext Xm_zero

theorem XU_pow (T : Matrix (Fin 2) (Fin 2) F) (n : ℕ) : XU T ^ n = XU (n • T) := by
  induction n with
  | zero => simp [XU_zero]
  | succ n ih => rw [pow_succ, ih, XU_mul, succ_nsmul]

theorem XU_ne {T T' : Matrix (Fin 2) (Fin 2) F} (i j : Fin 2) (h : T i j ≠ T' i j) :
    XU T ≠ XU T' := by
  intro he
  have h4 : Xm T = Xm T' := congrArg Units.val he
  have := congrFun (congrFun h4 (Sum.inl i)) (Sum.inr j)
  simp [Xm, fromBlocks] at this
  exact h this

@[expose] def mA : Matrix (Fin 2) (Fin 2) F := !![1, 1; 0, 1]
@[expose] def mAi : Matrix (Fin 2) (Fin 2) F := !![1, -1; 0, 1]
@[expose] def mD : Matrix (Fin 2) (Fin 2) F := !![1, 0; -1, 1]
@[expose] def mDi : Matrix (Fin 2) (Fin 2) F := !![1, 0; 1, 1]

theorem mA_mul_mAi : (mA : Matrix (Fin 2) (Fin 2) F) * mAi = 1 := by
  rw [mA, mAi, Matrix.mul_fin_two, Matrix.one_fin_two]; simp

theorem mAi_mul_mA : (mAi : Matrix (Fin 2) (Fin 2) F) * mA = 1 := by
  rw [mA, mAi, Matrix.mul_fin_two, Matrix.one_fin_two]; simp

theorem mD_mul_mDi : (mD : Matrix (Fin 2) (Fin 2) F) * mDi = 1 := by
  rw [mD, mDi, Matrix.mul_fin_two, Matrix.one_fin_two]; simp

theorem mDi_mul_mD : (mDi : Matrix (Fin 2) (Fin 2) F) * mD = 1 := by
  rw [mD, mDi, Matrix.mul_fin_two, Matrix.one_fin_two]; simp

@[expose] def Ym : Matrix Ix Ix F := fromBlocks mA 0 0 mD

@[expose] def Ymi : Matrix Ix Ix F := fromBlocks mAi 0 0 mDi

@[expose] def YU : GL Ix F :=
  ⟨Ym, Ymi, by simp [Ym, Ymi, fromBlocks_multiply, mA_mul_mAi, mD_mul_mDi, ← fromBlocks_one],
    by simp [Ym, Ymi, fromBlocks_multiply, mAi_mul_mA, mDi_mul_mD, ← fromBlocks_one]⟩

theorem comm_YU_XU (T : Matrix (Fin 2) (Fin 2) F) :
    ⁅(YU : GL Ix F), XU T⁆ = XU (mA * T * mDi - T) := by
  apply Units.ext
  rw [commutatorElement_def]
  show Ym * Xm T * Ymi * Xm (-T) = Xm (mA * T * mDi - T)
  have h1 : Ym * Xm T * Ymi = Xm (mA * T * mDi) := by
    simp only [Ym, Ymi, Xm, fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, mA_mul_mAi, mD_mul_mDi]
  rw [h1, Xm_mul, sub_eq_add_neg]

@[expose] def mS : Matrix (Fin 2) (Fin 2) F := !![0, 0; 0, 1]
@[expose] def mT1 : Matrix (Fin 2) (Fin 2) F := !![1, 1; 1, 0]
@[expose] def mT2 : Matrix (Fin 2) (Fin 2) F := !![2, 0; 0, 0]

theorem comm_S :
    ⁅(YU : GL Ix F), XU (mS : Matrix (Fin 2) (Fin 2) F)⁆ = XU (mT1 : Matrix (Fin 2) (Fin 2) F) := by
  rw [comm_YU_XU]
  congr 1
  rw [mA, mS, mDi, mT1, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem comm_T1 : ⁅(YU : GL Ix F), XU (mT1 : Matrix (Fin 2) (Fin 2) F)⁆ =
    XU (mT2 : Matrix (Fin 2) (Fin 2) F) := by
  rw [comm_YU_XU]
  congr 1
  rw [mA, mT1, mDi, mT2, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

theorem XU_mem (S : Matrix (Fin 2) (Fin 2) F) (hS : Sᵀ = S) : XU S ∈ StatedSp 2 F := by
  apply Subgroup.subset_closure
  show (Xm S)ᵀ * fromBlocks 0 1 (-1) 0 * Xm S = fromBlocks 0 1 (-1) 0
  simp [Xm, fromBlocks_transpose, fromBlocks_multiply, hS]

theorem mS_transpose : (mS : Matrix (Fin 2) (Fin 2) F)ᵀ = mS := by
  rw [mS]; ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem YU_mem : (YU : GL Ix F) ∈ StatedSp 2 F := by
  apply Subgroup.subset_closure
  show (Ym)ᵀ * fromBlocks 0 1 (-1) 0 * Ym = fromBlocks 0 1 (-1) 0
  have h1 : (mA : Matrix (Fin 2) (Fin 2) F)ᵀ = mDi := by
    rw [mA, mDi]; ext i j; fin_cases i <;> fin_cases j <;> rfl
  have h2 : (mD : Matrix (Fin 2) (Fin 2) F)ᵀ = mAi := by
    rw [mD, mAi]; ext i j; fin_cases i <;> fin_cases j <;> rfl
  simp [Ym, fromBlocks_transpose, fromBlocks_multiply, h1, h2, mDi_mul_mD, mAi_mul_mA]

theorem XU_unitri (T : Matrix (Fin 2) (Fin 2) F) : IsUnitri rk (XU T) := by
  intro i j h
  change ((Xm T : Matrix Ix Ix F) - 1) i j ≠ 0 at h
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Xm, rk, fromBlocks] at h ⊢

theorem YU_unitri : IsUnitri rk (YU : GL Ix F) := by
  intro i j h
  change ((Ym : Matrix Ix Ix F) - 1) i j ≠ 0 at h
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Ym, mA, mD, rk, fromBlocks] at h ⊢

theorem YU_unitri2 : IsUnitri rk2 (YU : GL Ix F) := by
  intro i j h
  change ((Ym : Matrix Ix Ix F) - 1) i j ≠ 0 at h
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Ym, mA, mD, rk2, fromBlocks] at h ⊢

end Matrices

section Group

variable {F : Type} [Field F] [Fact (Nat.Prime 3)] [CharP F 3]

@[expose] def W (F : Type) [Field F] [Fact (Nat.Prime 3)] [CharP F 3] :
    Subgroup (StatedSp 2 F) :=
  (unitriSubgroup 3 rk 4 rk_lt).subgroupOf (StatedSp 2 F)

theorem mem_W {g : StatedSp 2 F} : g ∈ W F ↔ IsUnitri rk (g : GL Ix F) := Iff.rfl

theorem W_pow_nine {g : StatedSp 2 F} (hg : g ∈ W F) : g ^ 9 = 1 := by
  apply Subtype.ext
  simpa using IsUnitri.pow_eq_one (p := 3) rk_lt (mem_W.1 hg) 2 (by norm_num)

theorem YU_pow_three : (YU : GL Ix F) ^ 3 = 1 := by
  simpa using IsUnitri.pow_eq_one (p := 3) rk2_lt (YU_unitri2 (F := F)) 1 (by norm_num)

theorem XU_pow_three (T : Matrix (Fin 2) (Fin 2) F) : XU T ^ 3 = 1 := by
  rw [XU_pow, show (3 • T : Matrix (Fin 2) (Fin 2) F) = 0 by
    rw [← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero, zero_smul], XU_zero]

theorem mk_inj {g h : StatedSp 2 F} (hg : g ∈ W F) (hh : h ∈ W F)
    (hgh : (QuotientGroup.mk g : StatedProj (StatedSp 2 F)) = QuotientGroup.mk h) : g = h := by
  rw [QuotientGroup.eq] at hgh
  have hs : ((g⁻¹ * h : StatedSp 2 F) : GL Ix F) ∈ StatedScalars Ix F := hgh
  have hu : IsUnitri rk ((g⁻¹ * h : StatedSp 2 F) : GL Ix F) :=
    mem_W.1 ((W F).mul_mem ((W F).inv_mem hg) hh)
  obtain ⟨c, hc⟩ := hs
  have hd := hu.diag (Sum.inl 0)
  rw [← hc] at hd
  simp at hd
  rw [hd, map_one] at hc
  have : g⁻¹ * h = 1 := Subtype.ext hc.symm
  exact inv_mul_eq_one.1 this

theorem dichThreeLieAt_proj_sp4 [Finite (StatedProj (StatedSp 2 F))] :
    DichThreeLieAt (StatedProj (StatedSp 2 F)) := by
  have hF2 : (2 : F) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) ((CharP.cast_eq_zero_iff F 3 2).1 h')
    omega
  let φ : StatedSp 2 F →* StatedProj (StatedSp 2 F) := QuotientGroup.mk' _
  let U : Subgroup (StatedProj (StatedSp 2 F)) := (W F).map φ
  let x0 : StatedSp 2 F := ⟨XU mS, XU_mem mS mS_transpose⟩
  let y0 : StatedSp 2 F := ⟨YU, YU_mem⟩
  have hx0 : x0 ∈ W F := mem_W.2 (XU_unitri _)
  have hy0 : y0 ∈ W F := mem_W.2 YU_unitri
  have hcm : ∀ {a b : StatedSp 2 F}, a ∈ W F → b ∈ W F → ⁅a, b⁆ ∈ W F := fun ha hb => by
    rw [commutatorElement_def]
    exact (W F).mul_mem ((W F).mul_mem ((W F).mul_mem ha hb) ((W F).inv_mem ha))
      ((W F).inv_mem hb)
  have ha0 : ⁅y0, x0⁆ ∈ W F := hcm hy0 hx0
  have hb0 : ⁅y0, ⁅y0, x0⁆⁆ ∈ W F := hcm hy0 ha0
  have ha0val : ((⁅y0, x0⁆ : StatedSp 2 F) : GL Ix F) = XU mT1 :=
    (map_commutatorElement (StatedSp 2 F).subtype y0 x0).trans comm_S
  have hb0val : ((⁅y0, ⁅y0, x0⁆⁆ : StatedSp 2 F) : GL Ix F) = XU mT2 := by
    calc ((⁅y0, ⁅y0, x0⁆⁆ : StatedSp 2 F) : GL Ix F)
        = ⁅(y0 : GL Ix F), ((⁅y0, x0⁆ : StatedSp 2 F) : GL Ix F)⁆ :=
          map_commutatorElement (StatedSp 2 F).subtype y0 ⁅y0, x0⁆
      _ = ⁅(YU : GL Ix F), XU mT1⁆ := by rw [ha0val]
      _ = XU mT2 := comm_T1
  have hcube : ∀ g : StatedSp 2 F, ∀ T, (g : GL Ix F) = XU T → φ g ^ 3 = 1 := by
    intro g T hg
    have : g ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, hg, XU_pow_three, Subgroup.coe_one])
    rw [← map_pow, this, map_one]
  have hx3 : φ x0 ^ 3 = 1 := hcube x0 mS rfl
  have hy3 : φ y0 ^ 3 = 1 := by
    have : y0 ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]; exact YU_pow_three)
    rw [← map_pow, this, map_one]
  have hU : IsPGroup 3 U := by
    intro u
    obtain ⟨g, hg, hgu⟩ := Subgroup.mem_map.1 u.2
    refine ⟨2, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hgu]
    change φ g ^ 9 = 1
    rw [← map_pow, W_pow_nine hg, map_one]
  have hyU : φ y0 ∈ U := Subgroup.mem_map_of_mem φ hy0
  have hxU : φ x0 ∈ U := Subgroup.mem_map_of_mem φ hx0
  have haU : φ ⁅y0, x0⁆ ∈ U := Subgroup.mem_map_of_mem φ ha0
  have hpair : HasNoncommPair 3 (StatedProj (StatedSp 2 F)) := by
    refine ⟨φ y0, φ x0, hy3, hx3, fun h => ?_, hU.to_le ((Subgroup.closure_le _).2
      (Set.insert_subset_iff.2 ⟨hyU, Set.singleton_subset_iff.2 hxU⟩))⟩
    have h1 : φ ⁅y0, x0⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_def, h]
      group
    have h2 : (⁅y0, x0⁆ : StatedSp 2 F) = 1 :=
      mk_inj ha0 (W F).one_mem (h1.trans (map_one φ).symm)
    have h3 : XU (mT1 : Matrix (Fin 2) (Fin 2) F) = XU 0 := by
      rw [← ha0val, h2, XU_zero]
      rfl
    exact XU_ne 0 0 (by simp [mT1]) h3
  refine dichThreeLieAt_of_pair_derived hpair hU ?_
  intro hcyc
  have hA : φ ⁅y0, x0⁆ ∈ ⁅U, U⁆ := by
    rw [map_commutatorElement]
    exact Subgroup.commutator_mem_commutator hyU hxU
  have hB : φ ⁅y0, ⁅y0, x0⁆⁆ ∈ ⁅U, U⁆ := by
    rw [map_commutatorElement]
    exact Subgroup.commutator_mem_commutator hyU haU
  let a' : ↥⁅U, U⁆ := ⟨φ ⁅y0, x0⁆, hA⟩
  let b' : ↥⁅U, U⁆ := ⟨φ ⁅y0, ⁅y0, x0⁆⁆, hB⟩
  have hap : a' ^ 3 = 1 := Subtype.ext (hcube _ _ ha0val)
  have hbp : b' ^ 3 = 1 := Subtype.ext (hcube _ _ hb0val)
  have hb1 : b' ≠ 1 := by
    intro h
    have h1 : φ ⁅y0, ⁅y0, x0⁆⁆ = 1 := congrArg Subtype.val h
    have h2 : (⁅y0, ⁅y0, x0⁆⁆ : StatedSp 2 F) = 1 :=
      mk_inj hb0 (W F).one_mem (h1.trans (map_one φ).symm)
    have h3 : XU (mT2 : Matrix (Fin 2) (Fin 2) F) = XU 0 := by
      rw [← hb0val, h2, XU_zero]
      rfl
    exact XU_ne 0 0 (by simpa [mT2] using hF2) h3
  haveI : IsCyclic ↥⁅U, U⁆ := hcyc
  have hord : orderOf b' = 3 := orderOf_eq_prime hbp hb1
  have hcard : Nat.card (Subgroup.zpowers a') ∣ Nat.card (Subgroup.zpowers b') := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hord]
    exact orderOf_dvd_of_pow_eq_one hap
  have hmem : a' ∈ Subgroup.zpowers b' :=
    IsCyclic.subgroup_le_iff_card_dvd.2 hcard (Subgroup.mem_zpowers a')
  obtain ⟨n, hn⟩ : ∃ n : ℕ, b' ^ n = a' :=
    (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hmem)
  have hq : φ (⁅y0, ⁅y0, x0⁆⁆ ^ n) = φ ⁅y0, x0⁆ := by
    rw [map_pow]
    exact congrArg Subtype.val hn
  have heq : (⁅y0, ⁅y0, x0⁆⁆ ^ n : StatedSp 2 F) = ⁅y0, x0⁆ :=
    mk_inj ((W F).pow_mem hb0 n) ha0 hq
  have hGL : XU (n • (mT2 : Matrix (Fin 2) (Fin 2) F)) = XU mT1 := by
    have := congrArg (fun g : StatedSp 2 F => (g : GL Ix F)) heq
    simp only [Subgroup.coe_pow] at this
    rwa [hb0val, ha0val, XU_pow] at this
  exact XU_ne 0 1 (by simp [mT1, mT2]) hGL

end Group

end Psp4Three

section Certified


theorem dichThreeLieAt_psp4_three (K : Type) [Group K] [Finite K]
    (hmodel : LieModel K .PSp 2 3 1) : DichThreeLieAt K := by
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hmodel.statedClassicalModel_of_ne_zero (by norm_num)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 3 :=
    charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hcard, pow_one])
  haveI : Finite (StatedProj (StatedSp 2 F)) := Finite.of_equiv K e.toEquiv
  exact DichThreeLieAt.of_mulEquiv e (Psp4Three.dichThreeLieAt_proj_sp4 (F := F))

theorem dichThreeLieAt_G2_three (K : Type) [Group K] [Finite K]
    (hmodel : LieModel K .G2 0 3 1) : DichThreeLieAt K := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hmodel.chevalleyExceptionalModel (by decide)
  have hZ : Subgroup.center ↥(adjointGroup .G2 F) = ⊥ := center_adjointGroup_eq_bot
  let e2 : AdjointQuotient .G2 F ≃* ↥(adjointGroup .G2 F) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let e3 : K ≃* ↥(adjointGroup .G2 F) := e.trans e2
  haveI : Finite ↥(adjointGroup .G2 F) := Finite.of_equiv K e3.toEquiv
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF3 : Nat.card F = 3 := by simpa using hF
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hF3])
  have hpow := G2Radical.radG2_pow F Nat.prime_three (by norm_num) hF3
  refine DichThreeLieAt.of_mulEquiv e3 (dichThreeLieAt_of_pair_exponent
    (hasNoncommPair_adjointG2 (K := F) (p := 3)) (U := G2Radical.radG2 F) ?_ hpow ?_)
  · intro g
    exact ⟨1, by rw [pow_one]; exact Subtype.ext (hpow g g.2)⟩
  · have := G2Radical.radG2_card F
    rwa [hF3] at this

theorem dichThreeLieAt_ree (K : Type) [Group K] [Finite K] (f : ℕ)
    (hmodel : LieModel K .twistedG2 0 3 f) : DichThreeLieAt K := by
  rcases hmodel with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, hree⟩ | ⟨-, h, -⟩
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · obtain ⟨-, h3, hr⟩ := CFSG.SectionRank.smallReeModel_rank hree
    exact dichThreeLieAt_of_four_le_pRank (by omega)
  · cases h

end Certified

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree
