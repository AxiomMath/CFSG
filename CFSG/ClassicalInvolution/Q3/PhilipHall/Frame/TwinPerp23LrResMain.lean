module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23LcFacts
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23LrResLift
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23LrResSL4Inv
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23LrResSL4Gauss
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23LrResSp4

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lc

open scoped MatrixGroups Matrix

namespace Res

theorem eq_bot_of_perfect_of_solvable {K : Type*} [Group K] {S C : Subgroup K}
    (hS : Group.IsPerfect S) (hC : Group.IsSolvable C) (hSC : S ≤ C) : S = ⊥ := by
  by_contra hne
  haveI : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).mpr hne
  haveI : Group.IsSolvable S := solvable_of_solvable_injective (Subgroup.inclusion_injective hSC)
  exact Group.IsPerfect.not_isSolvable S inferInstance

theorem lift_facts {K L : Type*} [Group K] [Group L] (φ : K →* L) (hs : Function.Surjective φ)
    (hk : φ.ker ≤ Subgroup.center K) {y : L} (hy2 : y * y = 1) (hyc : y ∉ Subgroup.center L)
    {g : K} (hg : φ g = y) :
    g * g ∈ Subgroup.center K ∧ g ∉ Subgroup.center K := by
  refine ⟨hk (by rw [MonoidHom.mem_ker, map_mul, hg, hy2]), fun hgc => hyc ?_⟩
  rw [← hg, Subgroup.mem_center_iff]
  intro l
  obtain ⟨k, rfl⟩ := hs l
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hgc k]

theorem res_of_solvable {K L : Type} [Group K] [Group L] [Finite K] (φ : K →* L)
    (hs : Function.Surjective φ) (hk : φ.ker ≤ Subgroup.center K) {g : K}
    (hC : Group.IsSolvable (Subgroup.centralizer ({g} : Set K))) :
    ∃ A : Subgroup L, (∀ x ∈ A, x * φ g = φ g * x) ∧
      (A = ⊥ ∨ Nonempty (↥A ≃* alternatingGroup (Fin 6))) ∧
      ∀ Q : Subgroup L, (∀ x ∈ Q, x * φ g = φ g * x) → Group.IsPerfect ↥Q → Q ≤ A := by
  refine ⟨⊥, fun x hx => ?_, Or.inl rfl, ?_⟩
  · rw [Subgroup.mem_bot] at hx
    rw [hx, one_mul, mul_one]
  · intro Q hQg hQ
    obtain ⟨S, hS, hSg, hSQ⟩ := exists_perfect_lift φ hk g hQ
      (fun x _ => by
        obtain ⟨k, rfl⟩ := hs x
        exact ⟨k, rfl⟩) hQg
    have hSC : S ≤ Subgroup.centralizer ({g} : Set K) := fun s hs' =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hSg s hs')
    have hbot := eq_bot_of_perfect_of_solvable hS hC hSC
    rw [← hSQ, hbot, Subgroup.map_bot]

noncomputable def slCongr {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (n : ℕ) :
    SL(n, R) ≃* SL(n, S) where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv A := by
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  right_inv A := by
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  map_mul' A B := map_mul _ A B

noncomputable def glMapEquiv {ι : Type} [Fintype ι] [DecidableEq ι] {K L : Type} [Field K]
    [Field L] (e : K ≃+* L) : Matrix.GeneralLinearGroup ι K ≃* Matrix.GeneralLinearGroup ι L :=
  Units.mapEquiv (RingEquiv.mapMatrix (m := ι) e).toMulEquiv

theorem glMapEquiv_mem_statedSp {K L : Type} [Field K] [Field L] (e : K ≃+* L)
    (A : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
    glMapEquiv e A ∈ CFSG.Open.StatedSp 2 L ↔ A ∈ CFSG.Open.StatedSp 2 K := by
  have hJ : (Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) K) (1 : Matrix (Fin 2) (Fin 2) K)
      (-1 : Matrix (Fin 2) (Fin 2) K) (0 : Matrix (Fin 2) (Fin 2) K)).map e =
      Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) L) (1 : Matrix (Fin 2) (Fin 2) L)
        (-1 : Matrix (Fin 2) (Fin 2) L) (0 : Matrix (Fin 2) (Fin 2) L) := by
    rw [Matrix.fromBlocks_map]
    simp [Matrix.map_zero, Matrix.map_one, Matrix.map_neg]
  rw [CFSG.Open.StatedAPI.mem_statedSp_iff, CFSG.Open.StatedAPI.mem_statedSp_iff]
  change ((A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map e)ᵀ *
      Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) L) (1 : Matrix (Fin 2) (Fin 2) L)
        (-1 : Matrix (Fin 2) (Fin 2) L) (0 : Matrix (Fin 2) (Fin 2) L) *
        (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).map e =
      Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) L) (1 : Matrix (Fin 2) (Fin 2) L)
        (-1 : Matrix (Fin 2) (Fin 2) L) (0 : Matrix (Fin 2) (Fin 2) L) ↔ _
  rw [← hJ, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
  constructor
  · intro h
    exact Matrix.map_injective e.injective h
  · intro h
    rw [h]

noncomputable def spCongr {K L : Type} [Field K] [Field L] (e : K ≃+* L) :
    CFSG.Open.StatedSp 2 K ≃* CFSG.Open.StatedSp 2 L :=
  (Subgroup.equivMapOfInjective (CFSG.Open.StatedSp 2 K) (glMapEquiv e).toMonoidHom
    (glMapEquiv e).injective).trans
    (MulEquiv.subgroupCongr (by
      ext B
      simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨A, hA, rfl⟩
        exact (glMapEquiv_mem_statedSp e A).mpr hA
      · intro hB
        refine ⟨(glMapEquiv e).symm B, (glMapEquiv_mem_statedSp e _).mp ?_, by simp⟩
        simpa using hB))

theorem central_kernel_comp {K K' L : Type*} [Group K] [Group K'] [Group L] (τ : K ≃* K')
    (φ : K' →* L) (hk : φ.ker ≤ Subgroup.center K') :
    (φ.comp τ.toMonoidHom).ker ≤ Subgroup.center K := by
  intro x hx
  have h1 : τ x ∈ Subgroup.center K' := hk (show φ (τ x) = 1 from MonoidHom.mem_ker.mp hx)
  rw [← Subgroup.map_center_eq τ] at h1
  obtain ⟨z, hz, hzx⟩ := h1
  have : z = x := τ.injective hzx
  rw [← this]
  exact hz

theorem res_sl4 {L : Type} [Group L] [Finite L] (φ : SL(4, ZMod 3) →* L)
    (hs : Function.Surjective φ) (hk : φ.ker ≤ Subgroup.center SL(4, ZMod 3)) {y : L}
    (hy2 : y * y = 1) (hyc : y ∉ Subgroup.center L) :
    ∃ A : Subgroup L, (∀ x ∈ A, x * y = y * x) ∧
      (A = ⊥ ∨ Nonempty (↥A ≃* alternatingGroup (Fin 6))) ∧
      ∀ Q : Subgroup L, (∀ x ∈ Q, x * y = y * x) → Group.IsPerfect ↥Q → Q ≤ A := by
  obtain ⟨g, hg⟩ := hs y
  obtain ⟨hg2, hgc⟩ := lift_facts φ hs hk hy2 hyc hg
  subst hg
  rcases (CFSG.CGT.PushingUpLit.SolKNA.PSL4Twin.mem_center_sl4 (g * g)).mp hg2 with h1 | h1
  · have hg1 : (g : Matrix (Fin 4) (Fin 4) (ZMod 3)) * g = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul]
      exact h1
    exact res_of_solvable φ hs hk (isSolvable_centralizer_of_sq_eq_one g hg1 hgc)
  · have hg1 : (g : Matrix (Fin 4) (Fin 4) (ZMod 3)) * g = -1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul]
      exact h1
    obtain ⟨A, h2, h3, h4⟩ := part_B φ hk hg1 hy2
    exact ⟨A, h2, Or.inr h3, fun Q hQ hQp =>
      h4 Q hQ hQp (fun x _ => by
        obtain ⟨k, rfl⟩ := hs x
        exact ⟨k, rfl⟩)⟩

theorem res_sp4 {L : Type} [Group L] [Finite L] (φ : CFSG.Open.StatedSp 2 (ZMod 3) →* L)
    (hs : Function.Surjective φ) (hk : φ.ker ≤ Subgroup.center (CFSG.Open.StatedSp 2 (ZMod 3)))
    {y : L} (hy2 : y * y = 1) (hyc : y ∉ Subgroup.center L) :
    ∃ A : Subgroup L, (∀ x ∈ A, x * y = y * x) ∧
      (A = ⊥ ∨ Nonempty (↥A ≃* alternatingGroup (Fin 6))) ∧
      ∀ Q : Subgroup L, (∀ x ∈ Q, x * y = y * x) → Group.IsPerfect ↥Q → Q ≤ A := by
  obtain ⟨g, hg⟩ := hs y
  obtain ⟨hg2, hgc⟩ := lift_facts φ hs hk hy2 hyc hg
  subst hg
  exact res_of_solvable φ hs hk (isSolvable_centralizer_of_sq_mem_center g hg2 hgc)

end Res

theorem luResFact_proved : LuResFact := by
  intro L _ _ hL y hy2 hyc
  have e : ZMod 3 ≃+* GaloisField 3 1 := (GaloisField.equivZmodP 3).toRingEquiv.symm
  rcases hL with ⟨φ, hφs, hφk⟩ | ⟨φ, hφs, hφk⟩
  · let τ := Res.slCongr e 4
    exact Res.res_sl4 (φ.comp τ.toMonoidHom) (hφs.comp τ.surjective)
      (Res.central_kernel_comp τ φ hφk) hy2 hyc
  · let τ := Res.spCongr e
    exact Res.res_sp4 (φ.comp τ.toMonoidHom) (hφs.comp τ.surjective)
      (Res.central_kernel_comp τ φ hφk) hy2 hyc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lc
