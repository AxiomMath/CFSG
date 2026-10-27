module

public import CFSG.ClassicalInvolution.Q3.Q3OFSplitTwLay
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCModel
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2
public import CFSG.ClassicalInvolution.ModelFacts.Orth15ChainLModel
public import CFSG.ClassicalInvolution.Q3.Q3NHMain
public import CFSG.ClassicalInvolution.Q3.Q3NTUnitary
public import CFSG.ClassicalInvolution.Q3.Q3OFProd
public import CFSG.ClassicalInvolution.Q3.Q3OFSplitTwLift
public import CFSG.ClassicalInvolution.Q3.Q3OFUnique
public import CFSG.ClassicalInvolution.Q3.Q3PPCommFund
public import CFSG.ClassicalInvolution.Q3.Q3PPEdgeKinds
public import CFSG.ClassicalInvolution.Q3.Q3PPEdgeShape
public import CFSG.ClassicalInvolution.Q3.Q3TCPartner
public import CFSG.ClassicalInvolution.Q3.Q3URDict
public import CFSG.ClassicalInvolution.Q3.Q3URStd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3OF

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSp
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3PP
  CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped Matrix

local notation "𝔽₃" => GaloisField 3 1

section Mod3

abbrev M3 : Type := Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3)

@[expose] def p2 (a b c d : ZMod 3) : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![a, b; c, d]

@[expose] def gramZ : M3 := Matrix.fromBlocks 0 1 (-1) 0

@[expose] def mσ : M3 := Matrix.fromBlocks (p2 0 1 1 0) 0 0 (p2 0 1 1 0)

@[expose] def mg0 : M3 := Matrix.fromBlocks (p2 1 1 (-1) 1) 0 0 (p2 (-1) (-1) 1 (-1))

@[expose] def mr0 : M3 := Matrix.fromBlocks (p2 (-1) 0 0 1) 0 0 (p2 (-1) 0 0 1)

@[expose] def mzS : M3 := Matrix.fromBlocks (p2 1 0 0 (-1)) 0 0 (p2 1 0 0 (-1))

@[expose] def mc : M3 := -1

@[expose] def blk (a b c d : ZMod 3) : M3 :=
  Matrix.fromBlocks (p2 a 0 0 1) (p2 b 0 0 0) (p2 c 0 0 0) (p2 d 0 0 1)

@[expose] def mui : M3 := blk 0 1 (-1) 0
@[expose] def muj : M3 := blk 1 1 1 (-1)
@[expose] def muk : M3 := blk 1 (-1) (-1) (-1)
@[expose] def mui' : M3 := blk 0 (-1) 1 0
@[expose] def muj' : M3 := blk (-1) (-1) (-1) 1
@[expose] def muk' : M3 := blk (-1) 1 1 1

@[expose] def ma1 : M3 := mr0 * mui
@[expose] def ma2 : M3 := muj
@[expose] def ma3 : M3 := mr0 * muk
@[expose] def mb1 : M3 := mui' * mr0
@[expose] def mb2 : M3 := muj'
@[expose] def mb3 : M3 := muk' * mr0

theorem sp_σ : mσᵀ * gramZ * mσ = gramZ := by decide +kernel
theorem sp_g0 : mg0ᵀ * gramZ * mg0 = gramZ := by decide +kernel
theorem sp_r0 : mr0ᵀ * gramZ * mr0 = gramZ := by decide +kernel
theorem sp_zS : mzSᵀ * gramZ * mzS = gramZ := by decide +kernel
theorem sp_c : mcᵀ * gramZ * mc = gramZ := by decide +kernel
theorem sp_a1 : ma1ᵀ * gramZ * ma1 = gramZ := by decide +kernel
theorem sp_a2 : ma2ᵀ * gramZ * ma2 = gramZ := by decide +kernel
theorem sp_a3 : ma3ᵀ * gramZ * ma3 = gramZ := by decide +kernel
theorem sp_b1 : mb1ᵀ * gramZ * mb1 = gramZ := by decide +kernel
theorem sp_b2 : mb2ᵀ * gramZ * mb2 = gramZ := by decide +kernel
theorem sp_b3 : mb3ᵀ * gramZ * mb3 = gramZ := by decide +kernel

theorem inv_a1 : ma1 * mb1 = 1 := by decide +kernel
theorem inv_a2 : ma2 * mb2 = 1 := by decide +kernel
theorem inv_a3 : ma3 * mb3 = 1 := by decide +kernel
theorem σ_sq : mσ * mσ = 1 := by decide +kernel
theorem r0_sq : mr0 * mr0 = 1 := by decide +kernel
theorem g0_conj : mg0 * mr0 = mσ * mg0 := by decide +kernel
theorem r0_zS : mzS * mr0 = mc := by decide +kernel
theorem comm_a1 : (ma1 * mσ * mb1) * mr0 * (ma1 * mσ * mb1) * mr0 = mc := by decide +kernel
theorem comm_a2 : (ma2 * mσ * mb2) * mr0 * (ma2 * mσ * mb2) * mr0 = mc := by decide +kernel
theorem comm_a3 : (ma3 * mσ * mb3) * mr0 * (ma3 * mσ * mb3) * mr0 = mc := by decide +kernel
theorem comm_a0 : mσ * mr0 * mσ * mr0 = mc := by decide +kernel
theorem rel_zS : mr0 * mc =
    (ma2 * mσ * mb2) * (ma3 * mσ * mb3) * ((ma1 * mσ * mb1) * mσ) := by decide +kernel
end Mod3

section Transfer

@[expose] noncomputable def castF : ZMod 3 →+* 𝔽₃ := ZMod.castHom (dvd_refl 3) 𝔽₃

theorem castF_zero : castF 0 = 0 := map_zero castF
theorem castF_one : castF 1 = 1 := map_one castF
theorem castF_neg (a : ZMod 3) : castF (-a) = -castF a := map_neg castF a
theorem castF_neg_one : castF (-1) = -1 := (castF_neg 1).trans (by rw [castF_one])

@[expose] noncomputable def toF (M : M3) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) 𝔽₃ := M.map castF

theorem toF_mul (A B : M3) : toF (A * B) = toF A * toF B := Matrix.map_mul

theorem toF_one : toF 1 = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem toF_transpose (M : M3) : toF Mᵀ = (toF M)ᵀ := Matrix.transpose_map

theorem toF_gram : toF gramZ = gram 𝔽₃ 2 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [toF, gramZ, gram, Matrix.fromBlocks, Matrix.one_apply, Matrix.map_apply,
      Matrix.neg_apply, castF_neg, castF_zero]

theorem toF_neg_one : toF (-1 : M3) = -1 := by
  ext i j
  simp [toF, Matrix.map_apply, Matrix.neg_apply, Matrix.one_apply, castF_neg]

@[expose] noncomputable def elt (M : M3) (h : Mᵀ * gramZ * M = gramZ) : StatedSp 2 𝔽₃ :=
  ofSymplecticMat (toF M) (by
    have := congrArg toF h
    rwa [toF_mul, toF_mul, toF_transpose, toF_gram] at this)

theorem mat_elt (M : M3) (h : Mᵀ * gramZ * M = gramZ) : mat 2 𝔽₃ (elt M h) = toF M := rfl

theorem mat_mul_elt {x y : StatedSp 2 𝔽₃} {A B : M3} (hx : mat 2 𝔽₃ x = toF A)
    (hy : mat 2 𝔽₃ y = toF B) : mat 2 𝔽₃ (x * y) = toF (A * B) := by
  rw [map_mul, hx, hy, toF_mul]

theorem eq_of_mat {x y : StatedSp 2 𝔽₃} {A B : M3} (hx : mat 2 𝔽₃ x = toF A)
    (hy : mat 2 𝔽₃ y = toF B) (h : A = B) : x = y :=
  mat_injective (by rw [hx, hy, h])

theorem mat_longInv_zero : mat 2 𝔽₃ (longInv 𝔽₃ 2 0) = toF mr0 := by
  rw [mat_longInv]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [coords, toF, mr0, p2, Matrix.fromBlocks, castF_neg_one, castF_one, castF_zero]

theorem mat_longInv_one : mat 2 𝔽₃ (longInv 𝔽₃ 2 1) = toF mzS := by
  rw [mat_longInv]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [coords, toF, mzS, p2, Matrix.fromBlocks, castF_neg_one, castF_one, castF_zero]

end Transfer

section Elements

@[expose] noncomputable def ec : StatedSp 2 𝔽₃ := elt mc sp_c
@[expose] noncomputable def eσ : StatedSp 2 𝔽₃ := elt mσ sp_σ
@[expose] noncomputable def eg0 : StatedSp 2 𝔽₃ := elt mg0 sp_g0
@[expose] noncomputable def er0 : StatedSp 2 𝔽₃ := elt mr0 sp_r0
@[expose] noncomputable def es0 : StatedSp 2 𝔽₃ := elt mzS sp_zS
@[expose] noncomputable def ea1 : StatedSp 2 𝔽₃ := elt ma1 sp_a1
@[expose] noncomputable def ea2 : StatedSp 2 𝔽₃ := elt ma2 sp_a2
@[expose] noncomputable def ea3 : StatedSp 2 𝔽₃ := elt ma3 sp_a3
@[expose] noncomputable def eb1 : StatedSp 2 𝔽₃ := elt mb1 sp_b1
@[expose] noncomputable def eb2 : StatedSp 2 𝔽₃ := elt mb2 sp_b2
@[expose] noncomputable def eb3 : StatedSp 2 𝔽₃ := elt mb3 sp_b3

theorem mat_one' : mat 2 𝔽₃ 1 = toF 1 := (map_one _).trans toF_one.symm

theorem mat_ec : mat 2 𝔽₃ ec = -1 := (mat_elt mc sp_c).trans toF_neg_one

theorem ec_central : ec ∈ Subgroup.center (StatedSp 2 𝔽₃) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply mat_injective
  rw [map_mul, map_mul, mat_ec]
  simp

theorem longInv_zero_eq : longInv 𝔽₃ 2 0 = er0 :=
  mat_injective (mat_longInv_zero.trans (mat_elt mr0 sp_r0).symm)

theorem longInv_one_eq : longInv 𝔽₃ 2 1 = es0 :=
  mat_injective (mat_longInv_one.trans (mat_elt mzS sp_zS).symm)

theorem eσ_sq : eσ * eσ = 1 :=
  eq_of_mat (mat_mul_elt (mat_elt mσ sp_σ) (mat_elt mσ sp_σ)) mat_one' σ_sq

theorem er0_sq : er0 * er0 = 1 :=
  eq_of_mat (mat_mul_elt (mat_elt mr0 sp_r0) (mat_elt mr0 sp_r0)) mat_one' r0_sq

theorem er0_ne_one : er0 ≠ 1 := by
  intro h
  have h1 : toF mr0 = 1 := by
    rw [← mat_elt mr0 sp_r0]
    exact (congrArg (mat 2 𝔽₃) h).trans (map_one _)
  have h2 := congrFun (congrFun h1 (Sum.inl 0)) (Sum.inl 0)
  simp [toF, mr0, p2, Matrix.fromBlocks, castF_neg_one] at h2
  exact two_ne_zero_gf3 (by linear_combination -h2)

theorem eσ_conj : eσ = eg0 * er0 * eg0⁻¹ := by
  have h : eg0 * er0 = eσ * eg0 :=
    eq_of_mat (mat_mul_elt (mat_elt mg0 sp_g0) (mat_elt mr0 sp_r0))
      (mat_mul_elt (mat_elt mσ sp_σ) (mat_elt mg0 sp_g0)) g0_conj
  rw [h]
  group

theorem es0_er0 : es0 * er0 = ec :=
  eq_of_mat (mat_mul_elt (mat_elt mzS sp_zS) (mat_elt mr0 sp_r0)) (mat_elt mc sp_c) r0_zS

theorem es0_er0_inv : es0 * er0⁻¹ = ec := by
  have h2 : er0⁻¹ = er0 := inv_eq_of_mul_eq_one_right er0_sq
  rw [h2]
  exact es0_er0

theorem es0_sq : es0 * es0 = 1 :=
  eq_of_mat (mat_mul_elt (mat_elt mzS sp_zS) (mat_elt mzS sp_zS)) mat_one' (by decide +kernel)

theorem es0_ne_one : es0 ≠ 1 := by
  intro h
  have h1 : toF mzS = 1 := by
    rw [← mat_elt mzS sp_zS]
    exact (congrArg (mat 2 𝔽₃) h).trans (map_one _)
  have h2 := congrFun (congrFun h1 (Sum.inl 1)) (Sum.inl 1)
  simp [toF, mzS, p2, Matrix.fromBlocks, castF_neg_one] at h2
  exact two_ne_zero_gf3 (by linear_combination -h2)

end Elements

section Words

theorem ea1_inv : ea1⁻¹ = eb1 :=
  inv_eq_of_mul_eq_one_right
    (eq_of_mat (mat_mul_elt (mat_elt ma1 sp_a1) (mat_elt mb1 sp_b1)) mat_one' inv_a1)

theorem ea2_inv : ea2⁻¹ = eb2 :=
  inv_eq_of_mul_eq_one_right
    (eq_of_mat (mat_mul_elt (mat_elt ma2 sp_a2) (mat_elt mb2 sp_b2)) mat_one' inv_a2)

theorem ea3_inv : ea3⁻¹ = eb3 :=
  inv_eq_of_mul_eq_one_right
    (eq_of_mat (mat_mul_elt (mat_elt ma3 sp_a3) (mat_elt mb3 sp_b3)) mat_one' inv_a3)

@[expose] noncomputable def ew1 : StatedSp 2 𝔽₃ := ea1 * eσ * ea1⁻¹
@[expose] noncomputable def ew2 : StatedSp 2 𝔽₃ := ea2 * eσ * ea2⁻¹
@[expose] noncomputable def ew3 : StatedSp 2 𝔽₃ := ea3 * eσ * ea3⁻¹

theorem mat_ew1 : mat 2 𝔽₃ ew1 = toF (ma1 * mσ * mb1) := by
  rw [ew1, ea1_inv]
  exact mat_mul_elt (mat_mul_elt (mat_elt ma1 sp_a1) (mat_elt mσ sp_σ)) (mat_elt mb1 sp_b1)

theorem mat_ew2 : mat 2 𝔽₃ ew2 = toF (ma2 * mσ * mb2) := by
  rw [ew2, ea2_inv]
  exact mat_mul_elt (mat_mul_elt (mat_elt ma2 sp_a2) (mat_elt mσ sp_σ)) (mat_elt mb2 sp_b2)

theorem mat_ew3 : mat 2 𝔽₃ ew3 = toF (ma3 * mσ * mb3) := by
  rw [ew3, ea3_inv]
  exact mat_mul_elt (mat_mul_elt (mat_elt ma3 sp_a3) (mat_elt mσ sp_σ)) (mat_elt mb3 sp_b3)

theorem ew1_sq : ew1 * ew1 = 1 := by
  calc ew1 * ew1 = ea1 * (eσ * eσ) * ea1⁻¹ := by unfold ew1; group
    _ = 1 := by rw [eσ_sq]; group

theorem ew2_sq : ew2 * ew2 = 1 := by
  calc ew2 * ew2 = ea2 * (eσ * eσ) * ea2⁻¹ := by unfold ew2; group
    _ = 1 := by rw [eσ_sq]; group

theorem ew3_sq : ew3 * ew3 = 1 := by
  calc ew3 * ew3 = ea3 * (eσ * eσ) * ea3⁻¹ := by unfold ew3; group
    _ = 1 := by rw [eσ_sq]; group

theorem ew1_conj : ew1 = (ea1 * eg0) * er0 * (ea1 * eg0)⁻¹ := by
  unfold ew1
  rw [eσ_conj]
  group

theorem ew2_conj : ew2 = (ea2 * eg0) * er0 * (ea2 * eg0)⁻¹ := by
  unfold ew2
  rw [eσ_conj]
  group

theorem ew3_conj : ew3 = (ea3 * eg0) * er0 * (ea3 * eg0)⁻¹ := by
  unfold ew3
  rw [eσ_conj]
  group

theorem ew1_comm : ew1 * er0 * ew1 * er0 = ec :=
  eq_of_mat (mat_mul_elt (mat_mul_elt (mat_mul_elt mat_ew1 (mat_elt mr0 sp_r0)) mat_ew1)
    (mat_elt mr0 sp_r0)) (mat_elt mc sp_c) comm_a1

theorem ew2_comm : ew2 * er0 * ew2 * er0 = ec :=
  eq_of_mat (mat_mul_elt (mat_mul_elt (mat_mul_elt mat_ew2 (mat_elt mr0 sp_r0)) mat_ew2)
    (mat_elt mr0 sp_r0)) (mat_elt mc sp_c) comm_a2

theorem ew3_comm : ew3 * er0 * ew3 * er0 = ec :=
  eq_of_mat (mat_mul_elt (mat_mul_elt (mat_mul_elt mat_ew3 (mat_elt mr0 sp_r0)) mat_ew3)
    (mat_elt mr0 sp_r0)) (mat_elt mc sp_c) comm_a3

theorem eσ_comm : eσ * er0 * eσ * er0 = ec :=
  eq_of_mat (mat_mul_elt (mat_mul_elt (mat_mul_elt (mat_elt mσ sp_σ) (mat_elt mr0 sp_r0))
    (mat_elt mσ sp_σ)) (mat_elt mr0 sp_r0)) (mat_elt mc sp_c) comm_a0

theorem er0_ec_rel : er0 * ec = (ew2 * ew3) * (ew1 * eσ) :=
  eq_of_mat (mat_mul_elt (mat_elt mr0 sp_r0) (mat_elt mc sp_c))
    (mat_mul_elt (mat_mul_elt mat_ew2 mat_ew3) (mat_mul_elt mat_ew1 (mat_elt mσ sp_σ))) rel_zS

theorem er0_ec_mem_closure : er0 * ec ∈ Subgroup.closure
    (Set.image2 (· * ·) (insert er0 ({eσ, ew1, ew2, ew3} : Set (StatedSp 2 𝔽₃)))
      (insert er0 ({eσ, ew1, ew2, ew3} : Set (StatedSp 2 𝔽₃)))) := by
  rw [er0_ec_rel]
  refine Subgroup.mul_mem _ (Subgroup.subset_closure ?_) (Subgroup.subset_closure ?_)
  · exact ⟨ew2, by simp, ew3, by simp, rfl⟩
  · exact ⟨ew1, by simp, eσ, by simp, rfl⟩

theorem mem_zpowers_ec_of {w : StatedSp 2 𝔽₃} (hw : w * w = 1) (hc : w * er0 * w * er0 = ec) :
    w * er0 * w⁻¹ * er0⁻¹ ∈ Subgroup.zpowers ec := by
  rw [inv_eq_of_mul_eq_one_right hw, inv_eq_of_mul_eq_one_right er0_sq, hc]
  exact Subgroup.mem_zpowers ec

theorem swap_data : ∀ w ∈ ({eσ, ew1, ew2, ew3} : Set (StatedSp 2 𝔽₃)),
    (∃ a : StatedSp 2 𝔽₃, w = a * er0 * a⁻¹) ∧ w * er0 * w⁻¹ * er0⁻¹ ∈ Subgroup.zpowers ec := by
  intro w hw
  rcases hw with rfl | rfl | rfl | hw
  · exact ⟨⟨eg0, eσ_conj⟩, mem_zpowers_ec_of eσ_sq eσ_comm⟩
  · exact ⟨⟨ea1 * eg0, ew1_conj⟩, mem_zpowers_ec_of ew1_sq ew1_comm⟩
  · exact ⟨⟨ea2 * eg0, ew2_conj⟩, mem_zpowers_ec_of ew2_sq ew2_comm⟩
  · rw [Set.mem_singleton_iff] at hw
    subst hw
    exact ⟨⟨ea3 * eg0, ew3_conj⟩, mem_zpowers_ec_of ew3_sq ew3_comm⟩

end Words

section Data

theorem longRootSp2_mem_fund {m : ℕ} (hadm : StatedLieAdmissible .PSp m 3 1) (k : Fin m) :
    longRootSp2 𝔽₃ m k ∈ (CompData.model .PSp m).fund :=
  (mem_fundamentalSubgroups_PSp_iff hadm _).mpr ((exists_conj_longBlock_iff k _).1
    ⟨1, by ext x; simp [longRootSp2]⟩)

theorem psp_data {c : CompData} (hc : c = CompData.model .PSp 2)
    (hadm : StatedLieAdmissible .PSp 2 3 1) :
    ∃ (N R₀ S₀ : Subgroup c.G) (r₀ s₀ : c.G), ParityData c N ∧ R₀ ∈ c.fund ∧ S₀ ∈ c.fund ∧
      Commutes R₀ S₀ ∧ r₀ ∈ R₀ ∧ r₀ * r₀ = 1 ∧ r₀ ≠ 1 ∧ s₀ ∈ S₀ ∧ s₀ * s₀ = 1 ∧ s₀ ≠ 1 ∧
      s₀ * r₀⁻¹ ∈ Subgroup.center c.G ∧ N = Subgroup.zpowers (s₀ * r₀⁻¹) := by
  subst hc
  have hft : IsFundTag .PSp := trivial
  have hF : KindFund3 (CompData.model .PSp 2) :=
    kindFund3_model hft hadm (by decide) (by decide)
  have hconj : FundConjClosed3 (CompData.model .PSp 2) := fundConjClosed3_model _ _
  have hsingle : ∀ R ∈ (CompData.model .PSp 2).fund, ∀ R' ∈ (CompData.model .PSp 2).fund,
      ∃ g : (CompData.model .PSp 2).G, R' = conjSub g R :=
    Q3W.EX.singleClass_of_kind rfl hft hadm (by decide) (by decide)
  have hR₀f := longRootSp2_mem_fund hadm 0
  have hS₀f := longRootSp2_mem_fund hadm 1
  have hr₀R : er0 ∈ longRootSp2 𝔽₃ 2 0 := longInv_zero_eq ▸ longInv_mem_longRootSp2 0
  have hs₀S : es0 ∈ longRootSp2 𝔽₃ 2 1 := longInv_one_eq ▸ longInv_mem_longRootSp2 1
  have hcen : es0 * er0⁻¹ ∈ Subgroup.center (StatedSp 2 𝔽₃) := es0_er0_inv ▸ ec_central
  refine ⟨Subgroup.zpowers ec, longRootSp2 𝔽₃ 2 0, longRootSp2 𝔽₃ 2 1, er0, es0, ?_, hR₀f, hS₀f,
    ?_, hr₀R, er0_sq, er0_ne_one, hs₀S, es0_sq, es0_ne_one, hcen,
    congrArg Subgroup.zpowers es0_er0_inv.symm⟩
  · exact ⟨hF, hconj, hsingle, Subgroup.zpowers_le.mpr ec_central, longRootSp2 𝔽₃ 2 0, hR₀f, er0,
      hr₀R, er0_sq, er0_ne_one, {eσ, ew1, ew2, ew3}, swap_data, ec, Subgroup.mem_zpowers ec,
      er0_ec_mem_closure⟩
  · exact fun x hx y hy => (commute_longRootSp2 (show (0 : Fin 2) ≠ 1 by decide) hx hy).eq

end Data

end CFSG.ClassicalInvolution.Q3.Q3OF
