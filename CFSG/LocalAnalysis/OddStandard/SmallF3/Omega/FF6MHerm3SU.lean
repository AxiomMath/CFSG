module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2HermSU
public import CFSG.GH74.L5U5.IdentUnitary
public import CFSG.Open.StatedCenterThree
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeDerived
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import Certificates.Data.ExceptionalSL3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary Matrix
  CFSG.ComponentClassification.CatalogueBUnitaryIsometry CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary CFSG.Blueprint

@[expose] noncomputable def suToOrth3 : Su F9 3 1 3 →* OGroup (hermForm 3) :=
  (uidToOrth 3).comp (Subgroup.inclusion (SUid_le_Uid σ9 3))

theorem suToOrth3_injective : Function.Injective suToOrth3 :=
  (uidToOrth_injective 3).comp (Subgroup.inclusion_injective _)

private theorem center_statedSU_three_three :
    Subgroup.center ↥(CFSG.Open.StatedSU 3 (3 ^ 1) F9) = ⊥ := by
  apply le_antisymm _ bot_le
  intro z hz
  obtain ⟨a, ha⟩ := CFSG.Open.StatedCenterThree.exists_orderOf_eq (K := F9) (q := 3) natCard_F9
  have haq : a ^ (3 ^ 1 + 1) = 1 := ha ▸ pow_orderOf_eq_one a
  have ha1 : (a : F9) ≠ 1 := fun h => by
    have : a = 1 := Units.ext h
    rw [this, orderOf_one] at ha
    omega
  have ha2 : (a : F9) ≠ ((a⁻¹ : F9ˣ) : F9) := fun h => by
    have h' : a ^ 2 = 1 := by
      rw [_root_.sq]
      nth_rw 2 [Units.ext h]
      exact mul_inv_cancel a
    have hd := orderOf_dvd_of_pow_eq_one h'
    rw [ha] at hd
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  have hb1 : ((a⁻¹ : F9ˣ) : F9) ≠ 1 := fun h => ha1 (by
    have : a⁻¹ = 1 := Units.ext h
    rw [inv_eq_one.mp this, Units.val_one])
  have hinj : Function.Injective ![(a : F9), ((a⁻¹ : F9ˣ) : F9), 1] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  let S := CFSG.Open.StatedSU 3 (3 ^ 1) F9
  set M : Matrix (Fin 3) (Fin 3) F9 :=
    (((z : ↥S) : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9)
  have hcomm : ∀ g : ↥S, ((g : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9) * M =
      M * ((g : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9) := fun g => by
    have := Subgroup.mem_center_iff.mp hz g
    exact congrArg (fun x : ↥S => ((x : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9)) this
  have hD := hcomm ⟨CFSG.Open.StatedCenterThree.diagGL a,
    CFSG.Open.StatedCenterThree.diagGL_mem (q := 3 ^ 1) (by norm_num) haq⟩
  have hdiag := CFSG.Open.StatedCenterThree.eq_diagonal_of_commute hinj hD.symm
  have hP := hcomm ⟨CFSG.Open.StatedCenterThree.cyc3GL,
    CFSG.Open.StatedCenterThree.cyc3GL_mem (q := 3 ^ 1) (by norm_num)⟩
  change CFSG.Open.StatedCenterThree.cyc3 * M = M * CFSG.Open.StatedCenterThree.cyc3 at hP
  rw [hdiag] at hP
  obtain ⟨h1, h2⟩ := CFSG.Open.StatedCenterThree.eq_of_diagonal_commute_cyc3 hP.symm
  have hMs : M = Matrix.scalar (Fin 3) (M 0 0) := by
    rw [hdiag, Matrix.scalar_apply]
    congr 1
    funext i
    fin_cases i
    · rfl
    · exact h1
    · exact h2
  have hdet := CFSG.Open.StatedAPI.det_of_mem_statedSU z.2
  change M.det = 1 at hdet
  rw [hMs, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hdet
  have hne : M 0 0 ≠ 0 := fun h0 => by rw [h0] at hdet; simp at hdet
  let c : F9ˣ := Units.mk0 (M 0 0) hne
  have hc3 : c ^ 3 = 1 := by
    apply Units.ext
    simpa [c] using hdet
  have hc8 : c ^ 8 = 1 := by
    have h8 : Nat.card F9ˣ = 8 := by rw [Nat.card_units, natCard_F9]; norm_num
    have h := pow_card_eq_one' (G := F9ˣ) (x := c)
    rwa [h8] at h
  have hone : orderOf c = 1 := by
    have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc3) (orderOf_dvd_of_pow_eq_one hc8)
    have hg : Nat.gcd 3 8 = 1 := by norm_num
    rw [hg] at h
    exact Nat.dvd_one.mp h
  have hM00 : M 0 0 = 1 := by
    have := congrArg (fun u : F9ˣ => (u : F9)) (orderOf_eq_one_iff.mp hone)
    simpa [c] using this
  have hM1 : M = 1 := by
    rw [hMs, Matrix.scalar_apply, hM00, diagonal_one]
  have hz1 : z = 1 := by
    apply Subtype.ext
    apply Units.ext
    change M = 1
    exact hM1
  exact Subgroup.mem_bot.mpr hz1

theorem su3_center_eq_bot : Subgroup.center (Su F9 3 1 3) = ⊥ := by
  have hcard : Nat.card (Subgroup.center (Su F9 3 1 3)) = 1 := by
    change Nat.card (Subgroup.center ↥(SUid σ9 3)) = 1
    rw [Nat.card_congr (Subgroup.centerCongr
      (MulEquiv.subgroupCongr (SUid_eq_statedSU natCard_F9 3))).toEquiv]
    exact (Subgroup.card_eq_one).mpr center_statedSU_three_three
  exact Subgroup.card_eq_one.mp hcard

theorem su3_lieModel : LieModel (Su F9 3 1 3) .PSU 3 3 1 := by
  have hadm : CFSG.Open.StatedLieAdmissible .PSU 3 3 1 :=
    ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩
  let e : Su F9 3 1 3 ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (3 ^ 1) F9) :=
    ((QuotientGroup.quotientMulEquivOfEq su3_center_eq_bot).trans
      QuotientGroup.quotientBot).symm.trans
        (CFSG.GH74.L5U5.centerQuotientEquivStatedProjSu (p := 3) (f := 1) natCard_F9
          (by norm_num : 3 ≤ 3) (by decide))
  exact Or.inl ⟨by decide, hadm, F9, inferInstance, inferInstance, natCard_F9, ⟨e⟩⟩

theorem su3_commutator_eq_top : commutator (Su F9 3 1 3) = ⊤ :=
  (CFSG.GH74.L5U5.isQuasisimple_su natCard_F9 (by norm_num : 3 ≤ 3)
    (by decide)).1.commutator_eq_top

theorem suToOrth3_mem_omega (s : Su F9 3 1 3) :
    suToOrth3 s ∈ omegaGroup (hermForm_nondegenerate 3) := by
  rw [omegaGroup_eq_commutator _ (by rw [finrank_hermSpace]; norm_num), commutator_def]
  have hs : s ∈ commutator (Su F9 3 1 3) := by
    rw [su3_commutator_eq_top]
    trivial
  rw [commutator_def] at hs
  have h1 := Subgroup.mem_map_of_mem suToOrth3 hs
  rw [Subgroup.map_commutator] at h1
  exact Subgroup.commutator_mono le_top le_top h1

theorem suToOrth3_pi_not_mem : piOrth (hermForm 3) ∉ suToOrth3.range := by
  rintro ⟨s, hs⟩
  have hvec : ∀ x : Fin 3 → F9, suMat s *ᵥ x = -x := by
    intro x
    have h1 : ((suToOrth3 s : OGroup (hermForm 3)) :
        (Fin 3 → F9) ≃ₗ[ZMod 3] (Fin 3 → F9)) x = suMat s *ᵥ x := rfl
    rw [hs] at h1
    rw [coe_piOrth_apply] at h1
    exact h1.symm
  have hmat : suMat s = -1 := by
    rw [Matrix.ext_iff_mulVec]
    intro x
    rw [hvec x, Matrix.neg_mulVec, Matrix.one_mulVec]
  have hdet : (suMat s).det = 1 := s.2.1
  rw [hmat, Matrix.det_neg, Matrix.det_one, Fintype.card_fin] at hdet
  have h3 : (-1 : F9) ^ 3 = -1 := by ring
  rw [h3, mul_one] at hdet
  exact neg_one_ne_one_F9 hdet

end CFSG.OddStandard.SmallF3.Omega
