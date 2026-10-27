module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Uni8

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

variable {n : ℕ} {F : Type} [Field F] [Finite F] (h : UnitaryFieldData 2 n F)

theorem sesqSpecialUnitaryGroupLE_eq_map {V : Type*} [AddCommGroup V] [Module F V]
    {σ : F →+* F} {B : V →ₛₗ[σ] V →ₗ[F] F} :
    sesqSpecialUnitaryGroupLE B =
      (sesqSpecialUnitaryGroup B).map
        (LinearMap.GeneralLinearGroup.generalLinearEquiv F V).toMonoidHom := by
  refine le_antisymm ?_ ?_
  · intro g hg
    rw [mem_sesqSpecialUnitaryGroupLE] at hg
    have hcoe : ((LinearMap.GeneralLinearGroup.ofLinearEquiv g : LinearMap.GeneralLinearGroup F V) :
        V →ₗ[F] V) = (g : V →ₗ[F] V) := rfl
    refine Subgroup.mem_map.mpr
      ⟨LinearMap.GeneralLinearGroup.ofLinearEquiv g,
        (mem_sesqSpecialUnitaryGroup).mpr ⟨hg.1, ?_⟩, LinearEquiv.ext fun x => rfl⟩
    rw [hcoe]
    exact hg.2
  · rintro g ⟨v, hv, rfl⟩
    have hv' := (mem_sesqSpecialUnitaryGroup (B := B)).mp hv
    exact (mem_sesqSpecialUnitaryGroupLE (B := B)).mpr
      ⟨(mem_sesqUnitaryGroup (B := B)).mp hv'.1, by simpa using hv'.2⟩

theorem map_toLin_statedSU (N : ℕ) :
    (StatedSU N (2 ^ n) F).map
        (Matrix.GeneralLinearGroup.toLin (n := Fin N) (R := F)).toMonoidHom =
      sesqSpecialUnitaryGroup (idForm h N) := by
  refine le_antisymm ?_ ?_
  · rintro g ⟨M, hM, rfl⟩
    change M ∈ CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 n F N at hM
    rw [CFSG.ClassicalGroups.UnitaryFlag.unitarySU_eq_gramSU h] at hM
    exact CFSG.ClassicalGroups.UnitaryFlag.toLin_mem_sesqSpecialUnitaryGroup_iff h
      (idGram F N) M |>.mpr hM
  · intro g hg
    have hM : Matrix.GeneralLinearGroup.toLin.symm g ∈ StatedSU N (2 ^ n) F := by
      change Matrix.GeneralLinearGroup.toLin.symm g ∈
        CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 n F N
      rw [CFSG.ClassicalGroups.UnitaryFlag.unitarySU_eq_gramSU h]
      change Matrix.GeneralLinearGroup.toLin.symm g ∈
        CFSG.ClassicalGroups.UnitaryFlag.gramSU h (idGram F N)
      rw [← CFSG.ClassicalGroups.UnitaryFlag.toLin_mem_sesqSpecialUnitaryGroup_iff h
        (idGram F N), MulEquiv.apply_symm_apply]
      exact hg
    exact ⟨_, hM, MulEquiv.apply_symm_apply _ _⟩

theorem map_toLinGen_statedSU (N : ℕ) :
    (StatedSU N (2 ^ n) F).map
        (↑(Matrix.GeneralLinearGroup.toLin.trans
          (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin N → F)))) =
      sesqSpecialUnitaryGroupLE (idForm h N) := by
  rw [show (↑(Matrix.GeneralLinearGroup.toLin.trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin N → F))) :
          GL (Fin N) F →* ((Fin N → F) ≃ₗ[F] (Fin N → F))) =
      (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin N → F)).toMonoidHom.comp
        (Matrix.GeneralLinearGroup.toLin (n := Fin N) (R := F)).toMonoidHom from rfl,
    ← Subgroup.map_map, map_toLin_statedSU, sesqSpecialUnitaryGroupLE_eq_map]

noncomputable def statedSUEquivSesqLE (N : ℕ) :
    ↥(StatedSU N (2 ^ n) F) ≃* ↥(sesqSpecialUnitaryGroupLE (idForm h N)) :=
  ((Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin N → F))).subgroupMap
    (StatedSU N (2 ^ n) F)).trans
    (MulEquiv.subgroupCongr (map_toLinGen_statedSU h N))

theorem statedSUEquivSesqLE_apply (N : ℕ) (M : ↥(StatedSU N (2 ^ n) F)) :
    ((statedSUEquivSesqLE h N M : (Fin N → F) ≃ₗ[F] (Fin N → F)) :
        (Fin N → F) →ₗ[F] (Fin N → F)) =
      ((Matrix.GeneralLinearGroup.toLin M : LinearMap.GeneralLinearGroup F (Fin N → F)) :
        (Fin N → F) →ₗ[F] (Fin N → F)) := by
  rw [statedSUEquivSesqLE, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    MulEquiv.coe_subgroupMap_apply]
  simp

theorem mulVecLin_scalar {N : ℕ} (a : F) :
    (Matrix.mulVecLin (Matrix.scalar (Fin N) a) : (Fin N → F) →ₗ[F] (Fin N → F)) =
      a • LinearMap.id := by
  have h1 : Matrix.scalar (Fin N) a = a • (1 : Matrix (Fin N) (Fin N) F) := by
    ext i j
    rw [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply]
    by_cases h : i = j <;> simp [h]
  rw [h1]
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.smul_apply, LinearMap.id_apply, Matrix.mulVecLin_apply, Matrix.smul_mulVec,
    Matrix.one_mulVec]

theorem exists_eq_smul_id_of_mem_statedScalars {N : ℕ} {M : ↥(StatedSU N (2 ^ n) F)}
    (hM : M ∈ (StatedScalars (Fin N) F).subgroupOf (StatedSU N (2 ^ n) F)) :
    ∃ c : Fˣ,
      (statedSUEquivSesqLE h N M : (Fin N → F) →ₗ[F] (Fin N → F)) = (c : F) • LinearMap.id := by
  simp only [Subgroup.mem_subgroupOf] at hM
  obtain ⟨c, hc⟩ := hM
  refine ⟨c, ?_⟩
  rw [statedSUEquivSesqLE_apply, ← hc, Matrix.GeneralLinearGroup.coe_toLin,
    Matrix.GeneralLinearGroup.coe_scalar]
  exact mulVecLin_scalar (c : F)

theorem two_le_orderOf_neg_two_pow {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hQ : ¬ p ∣ 2 ^ n + 1) :
    2 ≤ orderOf (-(2 ^ n) : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hx0 : (-(2 ^ n) : ZMod p) ≠ 0 := by
    intro h0
    have h2 : ((2 ^ n : ℕ) : ZMod p) = 0 := by
      simpa using neg_eq_zero.mp h0
    have hdiv : p ∣ 2 ^ n := (ZMod.natCast_eq_zero_iff (2 ^ n) p).mp h2
    have hp2' : p ∣ 2 := hp.dvd_of_dvd_pow hdiv
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2')
  have hpos : 0 < orderOf (-(2 ^ n) : ZMod p) :=
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨p - 1, by have := hp.two_le; omega,
      ZMod.pow_card_sub_one_eq_one hx0⟩).orderOf_pos
  rcases Nat.lt_or_ge (orderOf (-(2 ^ n) : ZMod p)) 2 with hlt | hge
  · have h1 : orderOf (-(2 ^ n) : ZMod p) = 1 := by omega
    have hx : (-(2 ^ n) : ZMod p) = 1 := orderOf_eq_one_iff.mp h1
    have hsum : ((2 ^ n + 1 : ℕ) : ZMod p) = 0 := by
      have hneg : ((2 ^ n : ℕ) : ZMod p) = -1 := by
        have h := congrArg (fun z : ZMod p => -z) hx
        simpa using h
      rw [Nat.cast_add, Nat.cast_one, hneg]; ring
    exact (hQ ((ZMod.natCast_eq_zero_iff (2 ^ n + 1) p).mp hsum)).elim
  · exact hge


end CFSG.LocalAnalysis.GLTheoremA.Y10F
