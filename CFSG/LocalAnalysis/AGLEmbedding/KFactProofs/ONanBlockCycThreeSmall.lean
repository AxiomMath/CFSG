module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycThreeAut
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineSylow
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycNodes
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrDispatch
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedMain
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.RankThree.PartOne.N143.Inspect613Even
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.AGLEmbedding.BlockCyc

open Matrix CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabAutIrr
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LinearGroups.UnitaryThreeOverNine

section Alt

theorem aut3Le_alternatingGroup_five : Aut3Le (alternatingGroup (Fin 5)) := by
  refine aut3Le_of_not_nine_dvd ?_
  have h : Nat.card (MulAut (alternatingGroup (Fin 5))) = 120 := by
    rw [← Nat.card_congr (Equiv.ofBijective _
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
        (by norm_num))), Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  rw [h]
  norm_num

theorem aut3Le_of_model_psl_three_two {Y : Type} [Group Y] [Finite Y]
    (h : StatedClassicalModel Y .PSL 3 2 1) : Aut3Le Y := by
  refine aut3Le_of_outPInner (outPInner_psl_two h Nat.prime_three (by norm_num)) ?_
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_equiv_projectiveSL h
  have hdvd : Nat.card Y ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) := by
    rw [Nat.card_congr e.toEquiv]
    exact Subgroup.index_dvd_card (scalars 3 K)
  have hK2 : Nat.card K = 2 := by simpa using hK
  have hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) = 168 := by
    rw [card_SL_eq (by norm_num), hK2]
    decide
  intro h9
  have := h9.trans (hcard ▸ hdvd)
  omega

end Alt

section Matrices

variable {K : Type} [Field K] (u : K)

@[expose] def gM : Matrix (Fin 3) (Fin 3) K := !![1 + u, u, u; u, 1 + u, u; u, u, 1 + u]

@[expose] def pM : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

@[expose] def b1M : Matrix (Fin 3) (Fin 3) K := !![-1, 0, 0; 0, -1, 0; 0, 0, 1]

@[expose] def b2M : Matrix (Fin 3) (Fin 3) K := !![0, -1, 0; -1, 0, 0; 0, 0, -1]

variable (hu : u ^ 2 = -1) (h3 : (3 : K) = 0)

include hu h3 in
theorem gM_unitary : ((gM u).map (· ^ 3))ᵀ * gM u = 1 := by
  have e1 : (1 + u) ^ 3 = 1 - u := by linear_combination (u + u ^ 2) * h3 + u * hu
  have e2 : u ^ 3 = -u := by linear_combination u * hu
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gM, Matrix.mul_apply, Fin.sum_univ_three, e1, e2] <;>
    linear_combination (-u ^ 2) * h3

include h3 in
theorem gM_det : (gM u).det = 1 := by
  simp [gM, Matrix.det_fin_three]
  linear_combination u * h3

include h3 in
theorem gM_cube : gM u ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gM, pow_succ, Matrix.mul_apply, Fin.sum_univ_three] <;>
    linear_combination (u + 3 * u ^ 2 + 3 * u ^ 3) * h3

theorem gM_comm_pM : gM u * pM = pM * gM u := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gM, pM, Matrix.mul_apply, Fin.sum_univ_three]

theorem b2M_comm_gM : b2M * gM u = gM u * b2M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gM, b2M, Matrix.mul_apply, Fin.sum_univ_three]

include hu h3 in
theorem b1M_not_comm_gM : ¬ (b1M * gM u = gM u * b1M) := by
  intro h
  have := congrFun (congrFun h 0) 2
  simp [b1M, gM, Matrix.mul_apply, Fin.sum_univ_three] at this
  have hu0 : u = 0 := by linear_combination u * h3 + this
  rw [hu0] at hu
  simp at hu

variable (K) in
theorem b2M_not_comm_pM : ¬ ((b2M : Matrix (Fin 3) (Fin 3) K) * pM = pM * b2M) := by
  intro h
  have := congrFun (congrFun h 0) 0
  simp [b2M, pM, Matrix.mul_apply, Fin.sum_univ_three] at this

variable (K) in
theorem pM_unitary : (((pM : Matrix (Fin 3) (Fin 3) K)).map (· ^ 3))ᵀ * pM = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pM, Matrix.mul_apply, Fin.sum_univ_three]

variable (K) in
theorem pM_det : (pM : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [pM, Matrix.det_fin_three]

variable (K) in
theorem pM_cube : (pM : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pM, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

variable (K) in
theorem b1M_unitary : (((b1M : Matrix (Fin 3) (Fin 3) K)).map (· ^ 3))ᵀ * b1M = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [b1M, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

variable (K) in
theorem b1M_det : (b1M : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [b1M, Matrix.det_fin_three]

variable (K) in
theorem b2M_unitary : (((b2M : Matrix (Fin 3) (Fin 3) K)).map (· ^ 3))ᵀ * b2M = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [b2M, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

variable (K) in
theorem b2M_det : (b2M : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [b2M, Matrix.det_fin_three]

end Matrices

section U33

variable {K : Type} [Field K]

@[expose] noncomputable def suElt (hK : Nat.card K = 9) (A : Matrix (Fin 3) (Fin 3) K)
    (h1 : (A.map (· ^ 3))ᵀ * A = 1) (h2 : A.det = 1) : StatedSU 3 3 K :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A (by rw [h2]; exact one_ne_zero), by
    rw [← SetLike.mem_coe, coe_statedSU hK, Set.mem_ofPred_eq]
    exact ⟨h1, h2⟩⟩

theorem ext_statedSU {a b : StatedSU 3 3 K}
    (h : ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = ((b : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) : a = b :=
  Subtype.ext (Units.ext h)

theorem coe_statedSU_mul (a b : StatedSU 3 3 K) :
    (((a * b : StatedSU 3 3 K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((b : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) := rfl

theorem coe_statedSU_pow (a : StatedSU 3 3 K) (n : ℕ) :
    (((a ^ n : StatedSU 3 3 K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ n := by
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]

theorem three_eq_zero_of_card_nine (hK : Nat.card K = 9) : (3 : K) = 0 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have := Fintype.ofFinite K
  have : CharP K 3 :=
    charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  exact_mod_cast CharP.cast_eq_zero K 3

theorem hasE9_statedSU (hK : Nat.card K = 9) : HasE9 (StatedSU 3 3 K) := by
  have h3 := three_eq_zero_of_card_nine hK
  obtain ⟨i, hi4⟩ := exists_units_orderOf_eq_four hK
  have hu : (i : K) ^ 2 = -1 := sq_eq_neg_one_of_orderOf hi4
  set g : StatedSU 3 3 K := suElt hK (gM (i : K)) (gM_unitary _ hu h3) (gM_det _ h3) with hg
  set P : StatedSU 3 3 K := suElt hK pM (pM_unitary K) (pM_det K) with hP
  set b1 : StatedSU 3 3 K := suElt hK b1M (b1M_unitary K) (b1M_det K) with hb1
  set b2 : StatedSU 3 3 K := suElt hK b2M (b2M_unitary K) (b2M_det K) with hb2
  refine hasE9_of_commuting_orders (MonoidHom.id (StatedSU 3 3 K)) (fun z hz => ?_)
    (a₁ := g) (a₂ := P) (b₁ := b1) (b₂ := b2) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hz
    rw [hz]
    exact Subgroup.one_mem _
  · exact ext_statedSU (by
      rw [coe_statedSU_pow, Subgroup.coe_one, Units.val_one]
      exact gM_cube _ h3)
  · exact ext_statedSU (by
      rw [coe_statedSU_pow, Subgroup.coe_one, Units.val_one]
      exact pM_cube K)
  · exact ext_statedSU (by rw [coe_statedSU_mul, coe_statedSU_mul]; exact gM_comm_pM _)
  · exact ext_statedSU (by rw [coe_statedSU_mul, coe_statedSU_mul]; exact b2M_comm_gM _)
  · intro hc
    exact b2M_not_comm_pM K (congrArg
      (fun x : StatedSU 3 3 K => ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hc.eq)
  · intro hc
    exact b1M_not_comm_gM _ hu h3 (congrArg
      (fun x : StatedSU 3 3 K => ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hc.eq)

theorem hasE9_of_model_psu_three_three {Y : Type} [Group Y]
    (h : StatedClassicalModel Y .PSU 3 3 1) : HasE9 Y := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hK9 : Nat.card K = 9 := by rw [hK]; norm_num
  have eY : Y ≃* StatedSU 3 3 K := e.trans
    ((QuotientGroup.quotientMulEquivOfEq (statedScalars_subgroupOf_statedSU_eq_bot hK9)).trans
      QuotientGroup.quotientBot)
  exact hasE9_of_mulEquiv eY.symm (hasE9_statedSU hK9)

end U33

section Small

theorem hasE9_or_aut3Le_of_small {Y : Type} [Group Y] [Finite Y] (hS : IsSmallTwo Y) :
    HasE9 Y ∨ Aut3Le Y := by
  rcases hS with ⟨n, hn, ⟨e⟩⟩ | ⟨⟨idx, hv⟩, hd, ⟨e⟩⟩
  · rcases hn with rfl | rfl | rfl
    · exact Or.inr (aut3Le_of_mulEquiv e.symm aut3Le_alternatingGroup_five)
    · exact Or.inl (hasE9_of_mulEquiv e.symm (hasE9_alternatingGroup (by norm_num)))
    · exact Or.inl (hasE9_of_mulEquiv e.symm (hasE9_alternatingGroup (by norm_num)))
  · rcases hd with ⟨q, hq7, hd1⟩ | ⟨q, hq3, hd1⟩
    ·
      obtain rfl : idx = .A 1 q := hd1
      have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      have hpe : q.p = 7 ∧ q.exponent = 1 := by
        have h7 : q.p ^ q.exponent = 7 := by rw [← TauCeti.PrimePower.card_def]; exact hq7
        exact (Nat.Prime.pow_eq_iff (by norm_num)).1 h7
      rw [hpe.1, hpe.2] at h
      exact Or.inr (aut3Le_of_model_psl_three_two
        (CFSG.QuasithinUnique.Vol2Native.L239.statedClassicalModel_psl_three_two_of_psl_two_seven
          h))
    ·
      obtain rfl : idx = .twistedA 2 q := hd1
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
      have hpe : q.p = 3 ∧ q.exponent = 1 := by
        have h3 : q.p ^ q.exponent = 3 := by rw [← TauCeti.PrimePower.card_def]; exact hq3
        exact (Nat.Prime.pow_eq_iff (by norm_num)).1 h3
      rw [hpe.1, hpe.2] at h
      exact Or.inl (hasE9_of_model_psu_three_three h)

end Small

end CFSG.AGLEmbedding.BlockCyc
