module

public import CFSG.LargeExtraspecial.DWModelHom

public section

namespace CFSG.LargeExtraspecial.DW.W4

open Subgroup Module Matrix CFSG.GroupTheory.GLnTwoSplitting CFSG.LargeExtraspecial.DW
open scoped IsMulCommutative

variable {H : Type*} [Group H] (V : Subgroup H) [V.Normal] [IsElementaryAbelian 2 V]

structure SplittingOn (Γ : Subgroup (Additive V ≃ₗ[ZMod 2] Additive V)) where
  centralizer_le : centralizer (V : Set H) ≤ V
  mem : ∀ h, conjLinear V h ∈ Γ
  σ : Γ →* H
  conjLinear_σ : ∀ f : Γ, conjLinear V (σ f) = f

namespace SplittingOn

variable {V} {Γ : Subgroup (Additive V ≃ₗ[ZMod 2] Additive V)} (X : SplittingOn V Γ)

include X in
theorem conjLinear_eq_one_iff' (h : H) : conjLinear V h = 1 ↔ h ∈ V := by
  rw [conjLinear_eq_one_iff V X.centralizer_le]
  exact ⟨fun ⟨e, he⟩ => he ▸ (Additive.toMul e).2, fun hh => ⟨Additive.ofMul ⟨h, hh⟩, rfl⟩⟩

@[expose] noncomputable def πΓ : H →* Γ := (conjLinear V).codRestrict Γ X.mem

theorem coe_πΓ (h : H) : ((X.πΓ h : Γ) : Additive V ≃ₗ[ZMod 2] Additive V) = conjLinear V h :=
  rfl

theorem πΓ_σ (f : Γ) : X.πΓ (X.σ f) = f := Subtype.ext (X.conjLinear_σ f)

theorem πΓ_eq_one_of_mem {v : H} (hv : v ∈ V) : X.πΓ v = 1 :=
  Subtype.ext ((X.conjLinear_eq_one_iff' v).mpr hv)

theorem mul_inv_σ_mem (h : H) : h * (X.σ (X.πΓ h))⁻¹ ∈ V := by
  rw [← X.conjLinear_eq_one_iff', map_mul, map_inv, X.conjLinear_σ, coe_πΓ, mul_inv_cancel]

@[expose] noncomputable def transl (h : H) : Additive V :=
  Additive.ofMul ⟨h * (X.σ (X.πΓ h))⁻¹, X.mul_inv_σ_mem h⟩

theorem coe_transl (h : H) :
    ((Additive.toMul (X.transl h) : V) : H) = h * (X.σ (X.πΓ h))⁻¹ := rfl

theorem transl_mul (h h' : H) :
    X.transl (h * h') = X.transl h + conjLinear V h (X.transl h') := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [toMul_add, mul_comm, Subgroup.coe_mul, coe_conjLinear_apply, coe_transl, coe_transl,
    coe_transl, map_mul, map_mul]
  group

theorem transl_one : X.transl 1 = 0 := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [coe_transl, map_one, map_one, inv_one, mul_one]
  rfl

theorem transl_of_mem {v : H} (hv : v ∈ V) : X.transl v = Additive.ofMul ⟨v, hv⟩ := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [coe_transl, X.πΓ_eq_one_of_mem hv, map_one, inv_one, mul_one]
  rfl

theorem transl_σ (f : Γ) : X.transl (X.σ f) = 0 := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [coe_transl, X.πΓ_σ, mul_inv_cancel]
  rfl

variable {m : ℕ} (b : Basis (Fin m) (ZMod 2) (Additive V))

@[expose] noncomputable def toSL : H →* SpecialLinearGroup (Fin (m + 1)) (ZMod 2) where
  toFun h := ⟨affMat (b.repr (X.transl h)) (Splitting.mat b h), by
    rw [det_affMat]
    exact det_eq_one_of_ne_zero_zmod_two (Splitting.det_mat_ne_zero b h)⟩
  map_one' := by
    apply Subtype.ext
    change affMat (b.repr (X.transl 1)) (Splitting.mat b 1) = 1
    rw [X.transl_one, map_zero, Finsupp.coe_zero, Splitting.mat_one, affMat_zero_one]
  map_mul' h h' := by
    apply Subtype.ext
    change affMat _ _ = affMat _ _ * affMat _ _
    rw [affMat_mul, ← Splitting.mat_mul, X.transl_mul, map_add, Finsupp.coe_add,
      Splitting.mat_mulVec]

theorem coe_toSL (h : H) :
    ((X.toSL b h : SpecialLinearGroup (Fin (m + 1)) (ZMod 2)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) =
        affMat (b.repr (X.transl h)) (Splitting.mat b h) :=
  rfl

theorem toSL_injective : Function.Injective (X.toSL b) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro h hh
  rw [MonoidHom.mem_ker] at hh
  have h1 : affMat (b.repr (X.transl h)) (Splitting.mat b h) = affMat 0 1 := by
    rw [affMat_zero_one, ← coe_toSL]
    exact (congrArg (fun A : SpecialLinearGroup (Fin (m + 1)) (ZMod 2) =>
      (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2))) hh).trans
      Matrix.SpecialLinearGroup.coe_one
  obtain ⟨hw, hg⟩ := affMat_injective h1
  have hπ : conjLinear V h = 1 := by
    have : (conjLinear V h : Additive V →ₗ[ZMod 2] Additive V) = LinearMap.id :=
      (LinearMap.toMatrix b b).injective (by rw [LinearMap.toMatrix_id]; exact hg)
    exact LinearEquiv.ext fun x => LinearMap.congr_fun this x
  have hπ' : X.πΓ h = 1 := Subtype.ext hπ
  have hτ : X.transl h = 0 := by
    have : b.repr (X.transl h) = 0 := Finsupp.ext fun i => congrFun hw i
    simpa using this
  have h2 := congrArg (fun e : Additive V => ((Additive.toMul e : V) : H)) hτ
  simp only [coe_transl, hπ', map_one, inv_one, mul_one] at h2
  rw [mem_bot]
  exact h2

theorem coe_toSL_of_mem {v : H} (hv : v ∈ V) :
    ((X.toSL b v : SpecialLinearGroup (Fin (m + 1)) (ZMod 2)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) =
        affMat (b.repr (Additive.ofMul ⟨v, hv⟩)) 1 := by
  rw [coe_toSL, X.transl_of_mem hv, Splitting.mat, (X.conjLinear_eq_one_iff' v).mpr hv]
  congr 1
  exact LinearMap.toMatrix_id b

theorem exists_toSL_eq (w : Fin m → ZMod 2) {f : Additive V ≃ₗ[ZMod 2] Additive V} (hf : f ∈ Γ) :
    ∃ h, ((X.toSL b h : SpecialLinearGroup (Fin (m + 1)) (ZMod 2)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) =
        affMat w (LinearMap.toMatrix b b (f : Additive V →ₗ[ZMod 2] Additive V)) := by
  set x : Additive V := b.equivFun.symm w
  refine ⟨((Additive.toMul x : V) : H) * X.σ ⟨f, hf⟩, ?_⟩
  have hxV : ((Additive.toMul x : V) : H) ∈ V := (Additive.toMul x).2
  have hπ : conjLinear V (((Additive.toMul x : V) : H) * X.σ ⟨f, hf⟩) = f := by
    rw [map_mul, (X.conjLinear_eq_one_iff' _).mpr hxV, one_mul, X.conjLinear_σ]
  have hτ : X.transl (((Additive.toMul x : V) : H) * X.σ ⟨f, hf⟩) = x := by
    rw [X.transl_mul, X.transl_σ, map_zero, add_zero, X.transl_of_mem hxV]
    rfl
  rw [coe_toSL, hτ, Splitting.mat, hπ]
  congr 1
  rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

theorem mulVec_single_of_commute (hN : 2 ≤ m + 1) {w : Fin m → ZMod 2}
    {g : Matrix (Fin m) (Fin m) (ZMod 2)}
    (hc : affMat w g * affMat (Pi.single ⟨0, by omega⟩ 1) 1 =
      affMat (Pi.single ⟨0, by omega⟩ 1) 1 * affMat w g) :
    g *ᵥ Pi.single ⟨0, by omega⟩ 1 = Pi.single ⟨0, by omega⟩ 1 := by
  rw [affMat_mul, affMat_mul, Matrix.one_mulVec, Matrix.one_mul] at hc
  have h := (affMat_injective hc).1
  rw [add_comm] at h
  exact add_right_cancel h

include X in
theorem nonempty_centralizer_mulEquiv (hN : 2 ≤ m + 1) {z : H} (hz : z ∈ V)
    (hb : b ⟨0, by omega⟩ = Additive.ofMul ⟨z, hz⟩)
    (hΓ : ∀ f : Additive V ≃ₗ[ZMod 2] Additive V, f (b ⟨0, by omega⟩) = b ⟨0, by omega⟩ → f ∈ Γ) :
    Nonempty (centralizer ({z} : Set H) ≃*
      centralizer ({cornerTransvection hN} : Set (SpecialLinearGroup (Fin (m + 1)) (ZMod 2)))) := by
  have htz : X.toSL b z = cornerTransvection hN := by
    apply Subtype.ext
    rw [coe_toSL_of_mem X b hz, coe_cornerTransvection_eq_affMat, ← hb, Basis.repr_self,
      Finsupp.single_eq_pi_single]
  have hmem : ∀ c : centralizer ({z} : Set H),
      X.toSL b c ∈ centralizer ({cornerTransvection hN} :
        Set (SpecialLinearGroup (Fin (m + 1)) (ZMod 2))) := by
    intro c
    rw [mem_centralizer_singleton_iff, ← htz, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.mp c.2]
  let φ : centralizer ({z} : Set H) →* centralizer ({cornerTransvection hN} :
      Set (SpecialLinearGroup (Fin (m + 1)) (ZMod 2))) :=
    ((X.toSL b).comp (centralizer ({z} : Set H)).subtype).codRestrict _ hmem
  refine ⟨MulEquiv.ofBijective φ ⟨fun c c' hcc' => ?_, fun M => ?_⟩⟩
  · exact Subtype.ext (X.toSL_injective b (congrArg Subtype.val hcc'))
  · have hMc := mem_centralizer_singleton_iff.mp M.2
    have hdet : ((M : SpecialLinearGroup (Fin (m + 1)) (ZMod 2)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)).det ≠ 0 := by
      rw [(M : SpecialLinearGroup (Fin (m + 1)) (ZMod 2)).2]
      exact one_ne_zero
    have hMc' : ((M : SpecialLinearGroup (Fin (m + 1)) (ZMod 2)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) *
          (cornerTransvection hN : SpecialLinearGroup (Fin (m + 1)) (ZMod 2)) =
        (cornerTransvection hN : SpecialLinearGroup (Fin (m + 1)) (ZMod 2)) *
          ((M : SpecialLinearGroup (Fin (m + 1)) (ZMod 2)) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) := by
      simpa using congrArg (fun A : SpecialLinearGroup (Fin (m + 1)) (ZMod 2) =>
        (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2))) hMc
    obtain ⟨w, g, hwg⟩ := exists_eq_affMat_of_commute hN hdet hMc'
    have hg : g.det ≠ 0 := by
      rw [← det_affMat w g, ← hwg]
      exact hdet
    have hge : g *ᵥ Pi.single ⟨0, by omega⟩ 1 = Pi.single ⟨0, by omega⟩ 1 := by
      refine mulVec_single_of_commute (w := w) hN ?_
      rw [← hwg, ← coe_cornerTransvection_eq_affMat hN]
      exact hMc'
    have hu : IsUnit (LinearMap.toMatrix b b (Matrix.toLin b b g)).det := by
      rw [LinearMap.toMatrix_toLin]
      exact isUnit_iff_ne_zero.mpr hg
    set f : Additive V ≃ₗ[ZMod 2] Additive V := LinearEquiv.ofIsUnitDet hu
    have hfg : LinearMap.toMatrix b b (f : Additive V →ₗ[ZMod 2] Additive V) = g := by
      have hf : (f : Additive V →ₗ[ZMod 2] Additive V) = Matrix.toLin b b g := by
        ext y
        rfl
      rw [hf, LinearMap.toMatrix_toLin]
    have hfb : f (b ⟨0, by omega⟩) = b ⟨0, by omega⟩ := by
      apply b.repr.injective
      apply Finsupp.ext
      intro i
      have h1 := LinearMap.toMatrix_mulVec_repr b b (f : Additive V →ₗ[ZMod 2] Additive V)
        (b ⟨0, by omega⟩)
      rw [hfg, Basis.repr_self, Finsupp.single_eq_pi_single, hge] at h1
      have h2 := congrFun h1 i
      rw [Basis.repr_self, Finsupp.single_eq_pi_single]
      exact h2.symm
    obtain ⟨h, hh⟩ := X.exists_toSL_eq b w (hΓ f hfb)
    rw [hfg] at hh
    have hhM : X.toSL b h = M := Subtype.ext (hh.trans hwg.symm)
    have hcent : h ∈ centralizer ({z} : Set H) := by
      rw [mem_centralizer_singleton_iff]
      refine X.toSL_injective b ?_
      rw [map_mul, map_mul, hhM, htz, hMc]
    exact ⟨⟨h, hcent⟩, Subtype.ext hhM⟩

end SplittingOn

theorem card_stabilizer_of_finrank_five {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] (hE : finrank (ZMod 2) E = 5) {e : E} (he : e ≠ 0) :
    Nat.card (MulAction.stabilizer (E ≃ₗ[ZMod 2] E) e) = 322560 := by
  have horbit : MulAction.orbit (E ≃ₗ[ZMod 2] E) e = {v | v ≠ 0} := by
    ext v
    constructor
    · rintro ⟨g, rfl⟩
      exact fun h => he (g.injective (by rw [map_zero]; exact h))
    · intro hv
      obtain ⟨f, d, hfd, hτ⟩ := exists_transvection_apply_eq he hv
      exact ⟨LinearEquiv.transvection hfd, hτ⟩
  have : Finite E := Module.finite_of_finite (ZMod 2)
  have hcardE : Nat.card E = 32 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hE]
    norm_num
  have hidx : (MulAction.stabilizer (E ≃ₗ[ZMod 2] E) e).index = 31 := by
    rw [MulAction.index_stabilizer, horbit, show {v : E | v ≠ 0} = Set.univ \ {0} by
      ext v
      simp, Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ, hcardE]
  have hGL : Nat.card (E ≃ₗ[ZMod 2] E) = 9999360 := by
    rw [card_linearEquiv_eq hE, Matrix.card_GL_field]
    simp [Fin.prod_univ_five, ZMod.card]
  have h := Subgroup.card_mul_index (MulAction.stabilizer (E ≃ₗ[ZMod 2] E) e)
  rw [hidx, hGL] at h
  omega

end CFSG.LargeExtraspecial.DW.W4
