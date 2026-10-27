module

public import CFSG.GH74.Generic.BProg.B1.PilotS3Facts
public import CFSG.GH74.Generic.S3.L3Class
public import CFSG.ClassicalInvolution.Models.Transfer.Unitary

public section

namespace CFSG.GH74.Generic.BProg.B1.PilotS3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Generic.S3
  CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Models.Transfer
open scoped MatrixGroups commutatorElement

section Matrix

variable {K : Type} [Field K]

theorem one_add_negBlock_three : (1 : Matrix (Fin 3) (Fin 3) K) + negBlock K 3 0 =
    !![0, 0, 0; 0, 0, 0; 0, 0, 2] := by
  rw [negBlock_three_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> (simp; try norm_num)

theorem entries_of_commute (h2 : (2 : K) ≠ 0) {X : Matrix (Fin 3) (Fin 3) K}
    (hX : X * negBlock K 3 0 = negBlock K 3 0 * X) :
    X 0 2 = 0 ∧ X 1 2 = 0 ∧ X 2 0 = 0 ∧ X 2 1 = 0 := by
  rw [negBlock_three_zero] at hX
  have h02 := congrFun (congrFun hX 0) 2
  have h12 := congrFun (congrFun hX 1) 2
  have h20 := congrFun (congrFun hX 2) 0
  have h21 := congrFun (congrFun hX 2) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at h02 h12 h20 h21
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : (2 : K) * X 0 2 = 0 := by linear_combination h02
    exact (mul_eq_zero.1 this).resolve_left h2
  · have : (2 : K) * X 1 2 = 0 := by linear_combination h12
    exact (mul_eq_zero.1 this).resolve_left h2
  · have : (2 : K) * X 2 0 = 0 := by linear_combination -h20
    exact (mul_eq_zero.1 this).resolve_left h2
  · have : (2 : K) * X 2 1 = 0 := by linear_combination -h21
    exact (mul_eq_zero.1 this).resolve_left h2

theorem mul_W_of_commute (h2 : (2 : K) ≠ 0) {X : Matrix (Fin 3) (Fin 3) K}
    (hX : X * negBlock K 3 0 = negBlock K 3 0 * X) :
    X * (1 + negBlock K 3 0) = X 2 2 • (1 + negBlock K 3 0) := by
  obtain ⟨h02, h12, h20, h21⟩ := entries_of_commute h2 hX
  rw [one_add_negBlock_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, h02, h12]

theorem commute_inv_of_commute {z : SL(3, K)}
    (hz : (z : Matrix (Fin 3) (Fin 3) K) * negBlock K 3 0 = negBlock K 3 0 * z) :
    ((z⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) * negBlock K 3 0 =
      negBlock K 3 0 * ((z⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) := by
  have e1 := coe_inv_mul_coe z
  have e2 := coe_mul_coe_inv z
  calc ((z⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) * negBlock K 3 0
      = ((z⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) * negBlock K 3 0 *
          ((z : Matrix (Fin 3) (Fin 3) K) * ((z⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)) := by
        rw [e2, Matrix.mul_one]
    _ = ((z⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) * ((negBlock K 3 0 * z) *
          ((z⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)) := by simp only [Matrix.mul_assoc]
    _ = negBlock K 3 0 * ((z⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) := by
        rw [← hz]
        calc ((z⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) * (((z : Matrix (Fin 3) (Fin 3) K) *
              negBlock K 3 0) * ((z⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K))
            = (((z⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) * (z : Matrix (Fin 3) (Fin 3) K)) *
              negBlock K 3 0 * ((z⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) := by
              simp only [Matrix.mul_assoc]
          _ = _ := by rw [e1, Matrix.one_mul]

theorem commute_mul_of_commute {a b : SL(3, K)}
    (ha : (a : Matrix (Fin 3) (Fin 3) K) * negBlock K 3 0 = negBlock K 3 0 * a)
    (hb : (b : Matrix (Fin 3) (Fin 3) K) * negBlock K 3 0 = negBlock K 3 0 * b) :
    ((a * b : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) * negBlock K 3 0 =
      negBlock K 3 0 * ((a * b : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha,
    Matrix.mul_assoc]

theorem commutator_mem_longRootGroup (h2 : (2 : K) ≠ 0) {x y : SL(3, K)}
    (hx : (x : Matrix (Fin 3) (Fin 3) K) * negBlock K 3 0 = negBlock K 3 0 * x)
    (hy : (y : Matrix (Fin 3) (Fin 3) K) * negBlock K 3 0 = negBlock K 3 0 * y) :
    ⁅x, y⁆ ∈ longRootGroup (negBlock K 3 0) := by
  have hx' := commute_inv_of_commute hx
  have hy' := commute_inv_of_commute hy
  have hc : ⁅x, y⁆ = x * y * x⁻¹ * y⁻¹ := commutatorElement_def x y
  have hcomm : ((⁅x, y⁆ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) * negBlock K 3 0 =
      negBlock K 3 0 * ((⁅x, y⁆ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) := by
    rw [hc]
    exact commute_mul_of_commute (commute_mul_of_commute (commute_mul_of_commute hx hy) hx') hy'
  refine ⟨hcomm, ?_⟩
  have hW22 : (1 + negBlock K 3 0 : Matrix (Fin 3) (Fin 3) K) 2 2 = 2 := by
    rw [one_add_negBlock_three]; simp
  have ex := mul_W_of_commute h2 hx
  have ey := mul_W_of_commute h2 hy
  have ex' := mul_W_of_commute h2 hx'
  have ey' := mul_W_of_commute h2 hy'
  have inv_eig : ∀ (z : SL(3, K)),
      (z : Matrix (Fin 3) (Fin 3) K) * negBlock K 3 0 = negBlock K 3 0 * z →
      (z : Matrix (Fin 3) (Fin 3) K) 2 2 *
        ((z⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
    intro z hz
    have h1 := mul_W_of_commute h2 hz
    have h1' := mul_W_of_commute h2 (commute_inv_of_commute hz)
    have h3 : (z : Matrix (Fin 3) (Fin 3) K) * (((z⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *
        (1 + negBlock K 3 0)) = 1 + negBlock K 3 0 := by
      rw [← Matrix.mul_assoc, coe_mul_coe_inv, Matrix.one_mul]
    rw [h1', Matrix.mul_smul, h1, smul_smul] at h3
    have h4 := congrFun (congrFun h3 2) 2
    simp only [Matrix.smul_apply, smul_eq_mul, hW22] at h4
    have h5 : (2 : K) * (((z⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 2 *
        (z : Matrix (Fin 3) (Fin 3) K) 2 2 - 1) = 0 := by linear_combination h4
    have h6 := (mul_eq_zero.1 h5).resolve_left h2
    linear_combination h6
  have ix := inv_eig x hx
  have iy := inv_eig y hy
  rw [hc, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul]
  simp only [Matrix.mul_assoc, ey', ex', ey, ex, Matrix.mul_smul, smul_smul]
  have : ((y⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 2 *
      ((x⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 2 * (y : Matrix (Fin 3) (Fin 3) K) 2 2 *
        (x : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
    linear_combination ((y : Matrix (Fin 3) (Fin 3) K) 2 2 *
      ((y⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) 2 2) * ix + iy
  rw [this, one_smul]

theorem commutator_mem_rootSL2 (h2 : (2 : K) ≠ 0) {x y : SL(3, K)}
    (hx : x ∈ Subgroup.centralizer ({rootInv K (by norm_num : 2 ≤ 3)} : Set SL(3, K)))
    (hy : y ∈ Subgroup.centralizer ({rootInv K (by norm_num : 2 ≤ 3)} : Set SL(3, K))) :
    ⁅x, y⁆ ∈ rootSL2 K (by norm_num : 2 ≤ 3) := by
  have e : ∀ {c : SL(3, K)},
      c ∈ Subgroup.centralizer ({rootInv K (by norm_num : 2 ≤ 3)} : Set SL(3, K)) →
      (c : Matrix (Fin 3) (Fin 3) K) * negBlock K 3 0 = negBlock K 3 0 * c := fun {c} hc => by
    have := congrArg (fun g : SL(3, K) => (g : Matrix (Fin 3) (Fin 3) K))
      (Subgroup.mem_centralizer_singleton_iff.mp hc)
    simpa [coe_rootInv] using this
  rw [rootSL2_eq_longRootGroup h2 (by norm_num : 2 ≤ 3)]
  exact commutator_mem_longRootGroup h2 (e hx) (e hy)

open CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits in
theorem commutator_mem_rootSU2 {p f : ℕ} [Finite K] [Fact p.Prime] [CharP K p] (h2 : (2 : K) ≠ 0)
    {x y : Su K p f 3}
    (hx : x ∈ Subgroup.centralizer ({rootInvSU K p f (by norm_num : 2 ≤ 3)} : Set (Su K p f 3)))
    (hy : y ∈ Subgroup.centralizer ({rootInvSU K p f (by norm_num : 2 ≤ 3)} : Set (Su K p f 3))) :
    ⁅x, y⁆ ∈ rootSU2 K p f (by norm_num : 2 ≤ 3) := by
  have e : ∀ {c : Su K p f 3}, c ∈ Subgroup.centralizer
      ({rootInvSU K p f (by norm_num : 2 ≤ 3)} : Set (Su K p f 3)) →
      suMat c * negBlock K 3 0 = negBlock K 3 0 * suMat c := fun {c} hc => by
    have := congrArg suMat (Subgroup.mem_centralizer_singleton_iff.mp hc)
    simpa [suMat_rootInvSU] using this
  rw [rootSU2_eq_longRootGroupSU h2 (by norm_num : 2 ≤ 3)]
  have h := commutator_mem_longRootGroup h2 (x := suToSL (unitaryInvolution K p f) 3 x)
    (y := suToSL (unitaryInvolution K p f) 3 y) (e hx) (e hy)
  rw [← map_commutatorElement] at h
  exact h

end Matrix

section Linear

variable (F : Type) [Field F]

@[expose] noncomputable def thetaLin : SL(3, F) →* StatedProj (StatedSL 3 F) :=
  (projectiveSpecialLinearGroupEquivStatedProj 3 F).toMonoidHom.comp
    (QuotientGroup.mk' (center SL(3, F)))

variable {F}

theorem thetaLin_surjective : Function.Surjective (thetaLin F) :=
  (projectiveSpecialLinearGroupEquivStatedProj 3 F).surjective.comp (QuotientGroup.mk'_surjective _)

theorem thetaLin_ker_le_center : (thetaLin F).ker ≤ center SL(3, F) := by
  intro z hz
  have h1 : (projectiveSpecialLinearGroupEquivStatedProj 3 F)
      (QuotientGroup.mk' (center SL(3, F)) z) = 1 := hz
  have h2 : QuotientGroup.mk' (center SL(3, F)) z = 1 := by
    apply (projectiveSpecialLinearGroupEquivStatedProj 3 F).injective
    rw [h1, map_one]
  exact (QuotientGroup.eq_one_iff z).1 h2

theorem grpS3_psl [Finite F] (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) :
    GrpS3 F (StatedProj (StatedSL 3 F)) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_natCard hodd
  have hn : (2 : ℕ) ≤ 3 := by norm_num
  have hsurj : Function.Surjective (thetaLin F) := thetaLin_surjective
  have hker : (thetaLin F).ker ≤ center SL(3, F) := thetaLin_ker_le_center
  have hlift : (3 : ℕ) ≠ 4 ∨ KerInvolutionFree (thetaLin F) := Or.inl (by norm_num)
  have hlr : IsLongRootImage (thetaLin F) hn ((rootSL2 F hn).map (thetaLin F))
      (thetaLin F (rootInv F hn)) :=
    ⟨rootSL2 F hn, rootInv F hn, isLongRootSL2_standard hn, rfl, rfl⟩
  have hcl : IsClassicalSL2 F ((rootSL2 F hn).map (thetaLin F)) (thetaLin F (rootInv F hn)) :=
    IsLongRootImage.isClassicalSL2 hodd (by norm_num) hsurj hker hlift hlr
  have hC := centralizer_map_eq_of_isLongRootSL2 h2 hsurj hker hlift (isLongRootSL2_standard hn)
  refine GrpS3.of_single hodd (by omega) (singleInv_psl h2) hcl.orderOf_eq_two hcl.le_centralizer
    ?_ hcl.nonempty_mulEquiv
  intro a b ha hb
  have ha' : a ∈ Subgroup.centralizer ({thetaLin F (rootInv F hn)} : Set _) :=
    Subgroup.mem_centralizer_singleton_iff.2 ha
  have hb' : b ∈ Subgroup.centralizer ({thetaLin F (rootInv F hn)} : Set _) :=
    Subgroup.mem_centralizer_singleton_iff.2 hb
  rw [hC] at ha' hb'
  obtain ⟨x, hx, rfl⟩ := ha'
  obtain ⟨y, hy, rfl⟩ := hb'
  rw [← map_commutatorElement]
  exact ⟨_, commutator_mem_rootSL2 h2 hx hy, rfl⟩

end Linear

section Unitary

open CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Steinberg

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

@[expose] noncomputable def thetaUni (hU : UnitaryFieldData p f K) :
    Su K p f 3 →* StatedProj (StatedSU 3 (p ^ f) K) :=
  (unitaryPSUEquiv hU (n := 3) (by norm_num)).toMonoidHom.comp
    ((unitaryProj hU 3).comp
      (MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hU.card_eq_sq 3)).toMonoidHom)

theorem thetaUni_surjective (hU : UnitaryFieldData p f K) : Function.Surjective (thetaUni hU) :=
  (unitaryPSUEquiv hU (n := 3) (by norm_num)).surjective.comp
    ((unitaryProj_surjective hU 3).comp
      (MulEquiv.subgroupCongr
        (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hU.card_eq_sq 3)).surjective)

theorem thetaUni_ker_le_center (hU : UnitaryFieldData p f K) :
    (thetaUni hU).ker ≤ center (Su K p f 3) := by
  intro z hz
  set e := MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hU.card_eq_sq 3)
    with he
  have h1 : (unitaryPSUEquiv hU (n := 3) (by norm_num)) (unitaryProj hU 3 (e z)) = 1 := hz
  have h2 : unitaryProj hU 3 (e z) = 1 := by
    apply (unitaryPSUEquiv hU (n := 3) (by norm_num)).injective
    rw [h1, map_one]
  have h3 : e z ∈ unitaryScalars hU 3 := by
    rw [← ker_unitaryProj]; exact h2
  have h4 := unitaryScalars_le_center hU 3 h3
  rw [Subgroup.mem_center_iff] at h4 ⊢
  intro g
  apply e.injective
  rw [map_mul, map_mul]
  exact h4 (e g)

theorem grpS3_psu (hU : UnitaryFieldData p f K) (hp : p ≠ 2)
    (h5 : 5 ≤ p ^ f) : GrpS3 (fixedSubfield K p f) (StatedProj (StatedSU 3 (p ^ f) K)) := by
  have hK : Nat.card K = (p ^ f) ^ 2 := hU.card_eq_sq
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two hp
  have hodd : Odd (Nat.card (fixedSubfield K p f)) := odd_natCard_fixedSubfield hK hp
  have hcard : Nat.card (fixedSubfield K p f) = p ^ f := card_fixedSubfield hK
  have hn : (2 : ℕ) ≤ 3 := by norm_num
  have hsurj := thetaUni_surjective hU
  have hker := thetaUni_ker_le_center hU
  have hlift : (3 : ℕ) ≠ 4 ∨ KerInvolutionFree (thetaUni hU) := Or.inl (by norm_num)
  have hlr : IsLongRootSU2Image (thetaUni hU) hn ((rootSU2 K p f hn).map (thetaUni hU))
      (thetaUni hU (rootInvSU K p f hn)) :=
    ⟨rootSU2 K p f hn, rootInvSU K p f hn, isLongRootSU2_standard hn, rfl, rfl⟩
  have hcl : IsClassicalSL2 (fixedSubfield K p f) ((rootSU2 K p f hn).map (thetaUni hU))
      (thetaUni hU (rootInvSU K p f hn)) :=
    IsLongRootSU2Image.isClassicalSL2 hK hp h5 (by norm_num) hsurj hker hlift hlr
  have hC := centralizer_map_eq_of_isLongRootSU2 hK hp h5 (by norm_num) hsurj hker hlift
    (isLongRootSU2_standard hn)
  refine GrpS3.of_single hodd (by omega) (singleInv_psu hU hp) hcl.orderOf_eq_two hcl.le_centralizer
    ?_ hcl.nonempty_mulEquiv
  intro a b ha hb
  have ha' : a ∈ Subgroup.centralizer ({thetaUni hU (rootInvSU K p f hn)} : Set _) :=
    Subgroup.mem_centralizer_singleton_iff.2 ha
  have hb' : b ∈ Subgroup.centralizer ({thetaUni hU (rootInvSU K p f hn)} : Set _) :=
    Subgroup.mem_centralizer_singleton_iff.2 hb
  rw [hC] at ha' hb'
  obtain ⟨x, hx, rfl⟩ := ha'
  obtain ⟨y, hy, rfl⟩ := hb'
  rw [← map_commutatorElement]
  exact ⟨_, commutator_mem_rootSU2 h2 hx hy, rfl⟩

end Unitary

section Shape

open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Steinberg

theorem exists_equiv_grpS3_of_qShape3 {Kt : Type} [Group Kt] (h : QShape3 Kt) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (P : Type) (_ : Group P), Nonempty (Kt ≃* P) ∧
      GrpS3 F P := by
  obtain ⟨p, f, hp, hp2, hq, hmod⟩ := h
  have hpodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hodd : (p ^ f) % 2 = 1 := Nat.odd_iff.1 hpodd
  have h5 : 5 ≤ p ^ f := by omega
  rcases hmod with hm | hm
  · obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl_data hm
    have hodd' : Odd (Nat.card F) := by rw [hF]; exact hpodd
    exact ⟨F, inferInstance, inferInstance, _, inferInstance, ⟨e⟩,
      grpS3_psl hodd' (by rw [hF]; exact h5)⟩
  · obtain ⟨-, hf, K, _, _, hK, ⟨e⟩⟩ := lieModel_psu_data hm
    have hU : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
    have : Fact p.Prime := ⟨hp⟩
    have : CharP K p := hU.charP
    exact ⟨↥(fixedSubfield K p f), inferInstance, inferInstance, _, inferInstance, ⟨e⟩,
      grpS3_psu hU hp2 h5⟩

end Shape

end CFSG.GH74.Generic.BProg.B1.PilotS3
