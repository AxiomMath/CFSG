module

public import CFSG.Open.StatedDefs
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.LinearAlgebra.BilinearForm.Basic
import CFSG.RankThree.SubgroupLists.SymplecticTransvections
import CFSG.LinearAlgebra.LinearGroups.QuadraticActions
import CFSG.GH74.GLS.IVK.Proofs2.Ivk95LinSL
import CFSG.HardMathSupport.Dickson.Sec6.Up34Aux.L364Lin
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.Determinant
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Centralizer

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

open LinearMap Matrix

variable {p : ℕ} [Fact p.Prime]

private theorem no_invariant_line_of_perfect
    {F : Type*} [Field F] [Finite F] {W : Type*} [AddCommGroup W] [Module F W]
    (H : Subgroup (Module.End F W)ˣ)
    (hH : Group.IsPerfect ↥H)
    (hfix : ∀ v : W, (∀ g ∈ H, (g : Module.End F W) v = v) → v = 0)
    {P : Submodule F W}
    (hP : ∀ g ∈ H, ∀ v ∈ P, (g : Module.End F W) v ∈ P)
    (hP1 : Module.finrank F P = 1) : False := by
  have hcomm : ⁅H, H⁆ = H := Subgroup.commutator_eq_self
  have hfixline :=
    CFSG.HardMathSupport.Dickson.Sec6.Up34Lin.perfect_fixes_line hcomm hP1 hP
  haveI : Nontrivial ↥P := Module.nontrivial_of_finrank_pos (R := F)
    (by rw [hP1]; norm_num)
  obtain ⟨v, hv0⟩ := exists_ne (0 : ↥P)
  exact hv0 (Subtype.ext (hfix v.val fun g hg => hfixline g hg v.val v.2))

private theorem range_ne_top_of_pow_eq_zero {R M : Type*} [DivisionRing R] [AddCommGroup M]
    [Module R M] [FiniteDimensional R M] [Nontrivial M] (f : Module.End R M) {m : ℕ}
    (hm : 0 < m) (h : f ^ m = 0) : f.range ≠ ⊤ := by
  intro htop
  have hsurj : Function.Surjective f := LinearMap.range_eq_top.mp htop
  have hinj : Function.Injective f := LinearMap.injective_iff_surjective.mpr hsurj
  have hunit : IsUnit f := (Module.End.isUnit_iff f).mpr ⟨hinj, hsurj⟩
  have hpow : IsUnit (f ^ m) := hunit.pow m
  rw [h] at hpow
  exact not_isUnit_zero hpow

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

open LinearMap Matrix

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [CharP F p] [Finite F]

private abbrev Sp4VecF (F : Type) := (Fin 2 ⊕ Fin 2) → F

private abbrev Sp4MatF (F : Type) := Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F

private theorem eq_bot_of_pow_eq_zero_of_disjoint_ker {F V : Type*} [Field F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (f : Module.End F V) {P : Submodule F V} [Nontrivial P]
    (hP : ∀ x ∈ P, f x ∈ P) (hdisj : P ⊓ f.ker = ⊥) {m : ℕ}
    (h : f ^ m = 0) : P = ⊥ := by
  let fP : Module.End F P := f.restrict (p := P) (q := P) hP
  have hfPpow : ∀ n : ℕ, ∀ x : P, ((fP ^ n) x : V) = (f ^ n) x.val := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
        rfl
  have hfP : fP ^ m = 0 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rw [hfPpow, h]
    rfl
  have hinj : Function.Injective fP := by
    intro x y hxy
    have hxyV : f x.val = f y.val := congrArg Subtype.val hxy
    have hdiff : f (x.val - y.val) = 0 := by rw [map_sub, hxyV, sub_self]
    have hmemP : x.val - y.val ∈ P := P.sub_mem x.2 y.2
    have hmemK : x.val - y.val ∈ f.ker := LinearMap.mem_ker.mpr hdiff
    have hzero : x.val - y.val = 0 := by
      have hmem : x.val - y.val ∈ P ⊓ f.ker := ⟨hmemP, hmemK⟩
      rw [hdisj] at hmem
      simpa using hmem
    exact Subtype.ext (sub_eq_zero.mp hzero)
  have hunit : IsUnit fP := (LinearMap.isUnit_iff_ker_eq_bot fP).mpr
    (LinearMap.ker_eq_bot.mpr hinj)
  have hpow : IsUnit (fP ^ m) := hunit.pow m
  rw [hfP] at hpow
  exact (not_isUnit_zero hpow).elim

private theorem exists_alternating_plane_form {F : Type*} [Field F] {U : Type*}
    [AddCommGroup U] [Module F U] (hU : Module.finrank F U = 2) :
    ∃ (b : Module.Basis (Fin 2) F U) (ω : LinearMap.BilinForm F U),
      ω.IsAlt ∧ ω.Nondegenerate ∧ ω ≠ 0 := by
  haveI : FiniteDimensional F U :=
    FiniteDimensional.of_finrank_pos (by rw [hU]; norm_num)
  haveI : Nontrivial U := Module.nontrivial_of_finrank_pos (R := F) (by rw [hU]; norm_num)
  let b : Module.Basis (Fin 2) F U := (Module.finBasis F U).reindex (finCongr hU)
  let J : Matrix (Fin 2) (Fin 2) F := !![0, 1; -1, 0]
  let Bc : LinearMap.BilinForm F (Fin 2 → F) := Matrix.toBilin' J
  let ω : LinearMap.BilinForm F U := BilinForm.congr b.equivFun.symm Bc
  have hBcalt : Bc.IsAlt := by
    intro x
    rw [show Bc = Matrix.toBilin' J from rfl, Matrix.toBilin'_apply']
    simp [J, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply]
    ring
  have hBcnd : Bc.Nondegenerate := by
    rw [BilinForm.nondegenerate_toBilin'_iff_det_ne_zero]
    simp [J, Matrix.det_fin_two]
  have hωalt : ω.IsAlt := by
    intro u
    dsimp only [ω]
    rw [BilinForm.congr_apply]
    exact hBcalt (b.equivFun u)
  have hωnd : ω.Nondegenerate := hBcnd.congr b.equivFun.symm
  have hωsep : ∀ u : U, (∀ v : U, ω u v = 0) → u = 0 := hωnd.1
  have hωne : ω ≠ 0 := by
    intro h
    obtain ⟨u, hu⟩ := exists_ne (0 : U)
    exact hu (hωsep u (by rw [h]; simp))
  exact ⟨b, ω, hωalt, hωnd, hωne⟩

private theorem det_eq_one_of_perfect_isometry {F : Type*} [Field F] {U : Type*}
    [AddCommGroup U] [Module F U] (hU : Module.finrank F U = 2) {L : Type*} [Group L]
    (hL : Group.IsPerfect L) (ρ : L →* (Module.End F U)ˣ) :
    ∀ g : L, LinearMap.det (ρ g : Module.End F U) = 1 := by
  haveI : FiniteDimensional F U :=
    FiniteDimensional.of_finrank_pos (by rw [hU]; norm_num)
  have hχ : (Units.map (LinearMap.det (A := F) (M := U))).comp ρ = 1 :=
    CFSG.GH74.GLS.IVK.Proofs2.ivk95l_hom_one_of_perfect hL _
  intro g
  have h := congrArg (fun u : Fˣ => (u : F))
    (congrArg (fun f : L →* Fˣ => f g) hχ)
  simpa [Units.coe_map] using h

private theorem alt_form_preserved_of_det_one {F : Type*} [Field F] {U : Type*}
    [AddCommGroup U] [Module F U] (b : Module.Basis (Fin 2) F U)
    (ω : LinearMap.BilinForm F U) (hωalt : ω.IsAlt) {L : Type*} [Group L]
    (ρ : L →* (Module.End F U)ˣ) (hdet : ∀ g : L, LinearMap.det (ρ g : Module.End F U) = 1) :
    ∀ g : L, ∀ u v : U,
      ω ((ρ g : Module.End F U) u) ((ρ g : Module.End F U) v) = ω u v := by
  intro g u v
  have h := LinearMap.IsAlt.compl₁₂_self_eq_det_smul b hωalt (ρ g : Module.End F U)
  rw [hdet g, one_smul] at h
  exact LinearMap.congr_fun₂ h u v

private theorem exists_adjoint_nonscalar {F : Type*} [Field F] {U : Type*}
    [AddCommGroup U] [Module F U] (hU : Module.finrank F U = 2) (h2 : (2 : F) ≠ 0)
    (β : LinearMap.BilinForm F U)
    (hβ : ∀ u v, β u v = β v u) (hβnd : ∀ u : U, (∀ v : U, β u v = 0) → u = 0)
    (ω : LinearMap.BilinForm F U) (hωalt : ω.IsAlt) (hωnd : ω.Nondegenerate)
    (hωne : ω ≠ 0) :
    ∃ eT : U ≃ₗ[F] U,
      (∀ u v : U, β (eT u) v = ω u v) ∧
        ∀ t : F, (eT : Module.End F U) ≠ t • 1 := by
  haveI : FiniteDimensional F U :=
    FiniteDimensional.of_finrank_pos (by rw [hU]; norm_num)
  haveI : Nontrivial U :=
    Module.nontrivial_of_finrank_pos (R := F) (by rw [hU]; norm_num)
  have hβnd' : β.Nondegenerate := BilinForm.Nondegenerate.ofSeparatingLeft hβnd
  let eT : U ≃ₗ[F] U := (ω.toDual hωnd).trans (β.toDual hβnd').symm
  have hTapply : ∀ u v : U, β (eT u) v = ω u v := by
    intro u v
    change β ((β.toDual hβnd').symm ((ω.toDual hωnd) u)) v = ω u v
    rw [BilinForm.apply_toDual_symm_apply, BilinForm.toDual_def]
  refine ⟨eT, hTapply, ?_⟩
  intro t ht
  have hωeq : ω = t • β := by
    ext u v
    have hTu : eT u = t • u := by
      change (eT : Module.End F U) u = t • u
      rw [ht]; simp
    calc ω u v = β (eT u) v := (hTapply u v).symm
      _ = β (t • u) v := by rw [hTu]
      _ = t * β u v := by simp [map_smul, smul_eq_mul]
      _ = (t • β) u v := by simp [LinearMap.smul_apply, smul_eq_mul]
  obtain ⟨u, hu⟩ := exists_ne (0 : U)
  have hv : ∃ v : U, β u v ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (hβnd u h)
  obtain ⟨v, hv⟩ := hv
  have halt : ω v u = - ω u v := (BilinForm.IsAlt.neg_eq hωalt u v).symm
  have h2t : (2 : F) * (t * β u v) = 0 := by
    have h1 : ω u v = t * β u v := by rw [hωeq]; simp [LinearMap.smul_apply, smul_eq_mul]
    have h1' : ω v u = t * β u v := by
      rw [hωeq]; simp [LinearMap.smul_apply, smul_eq_mul, hβ u v]
    rw [h1', h1] at halt
    linear_combination halt
  have ht0 : t = 0 := by
    have h2t' : t * β u v = 0 := (mul_eq_zero.mp h2t).resolve_left h2
    exact (mul_eq_zero.mp h2t').resolve_right hv
  apply hωne
  rw [hωeq, ht0, zero_smul]

private theorem adjoint_commutes {F : Type*} [Field F] {U : Type*}
    [AddCommGroup U] [Module F U] (β : LinearMap.BilinForm F U)
    (hβnd : ∀ u : U, (∀ v : U, β u v = 0) → u = 0)
    {L : Type*} [Group L] (ρ : L →* (Module.End F U)ˣ)
    (hρ : ∀ g u v, β ((ρ g : Module.End F U) u) ((ρ g : Module.End F U) v) = β u v)
    (ω : LinearMap.BilinForm F U)
    (hωiso : ∀ g : L, ∀ u v : U,
      ω ((ρ g : Module.End F U) u) ((ρ g : Module.End F U) v) = ω u v)
    (eT : U ≃ₗ[F] U) (hTapply : ∀ u v : U, β (eT u) v = ω u v) :
    ∀ g : L, (eT : Module.End F U) * (ρ g : Module.End F U) =
      (ρ g : Module.End F U) * (eT : Module.End F U) := by
  intro g
  apply LinearMap.ext
  intro u
  rw [← sub_eq_zero]
  apply hβnd ((eT : Module.End F U) ((ρ g : Module.End F U) u) -
    (ρ g : Module.End F U) ((eT : Module.End F U) u))
  intro v
  have hinner : ((ρ g : Module.End F U)) ((((ρ g)⁻¹ : (Module.End F U)ˣ) :
      Module.End F U) v) = v := by
    rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply]
  have h1 : β ((eT : Module.End F U) ((ρ g : Module.End F U) u)) v =
      ω ((ρ g : Module.End F U) u) v := hTapply _ _
  have h2 : β ((ρ g : Module.End F U) ((eT : Module.End F U) u)) v =
      β ((eT : Module.End F U) u) ((((ρ g)⁻¹ : (Module.End F U)ˣ) :
        Module.End F U) v) := by
    have h := hρ g ((eT : Module.End F U) u) ((((ρ g)⁻¹ : (Module.End F U)ˣ) :
      Module.End F U) v)
    rwa [hinner] at h
  have h3 : ω ((ρ g : Module.End F U) u) v =
      ω u ((((ρ g)⁻¹ : (Module.End F U)ˣ) : Module.End F U) v) := by
    have h := hωiso g u ((((ρ g)⁻¹ : (Module.End F U)ˣ) : Module.End F U) v)
    rwa [hinner] at h
  have h4 : ω u ((((ρ g)⁻¹ : (Module.End F U)ˣ) : Module.End F U) v) =
      β ((eT : Module.End F U) u) ((((ρ g)⁻¹ : (Module.End F U)ˣ) :
        Module.End F U) v) := (hTapply u _).symm
  rw [map_sub, LinearMap.sub_apply, h1, h2, h3, h4, sub_self]

private theorem centralizer_pairwise_commute {F : Type*} [Field F] {U : Type*}
    [AddCommGroup U] [Module F U] (b : Module.Basis (Fin 2) F U) {L : Type*} [Group L]
    (ρ : L →* (Module.End F U)ˣ) (eT : U ≃ₗ[F] U)
    (hTcomm : ∀ g : L, (eT : Module.End F U) * (ρ g : Module.End F U) =
      (ρ g : Module.End F U) * (eT : Module.End F U))
    (hT_not_scalar : ∀ t : F, (eT : Module.End F U) ≠ t • 1) :
    ∀ g h : L, (ρ g : Module.End F U) * (ρ h) = (ρ h) * (ρ g) := by
  let T : Module.End F U := eT
  let T_unit : (Module.End F U)ˣ :=
    { val := T
      inv := eT.symm.toLinearMap
      val_inv := by ext u; exact eT.apply_symm_apply u
      inv_val := by ext u; exact eT.symm_apply_apply u }
  let φ : (Module.End F U) ≃ₐ[F] Matrix (Fin 2) (Fin 2) F := LinearMap.toMatrixAlgEquiv b
  let a : GL (Fin 2) F := Units.map φ.toMulEquiv.toMonoidHom T_unit
  have hcoea : (a : Matrix (Fin 2) (Fin 2) F) = φ T := by simp [a, T, T_unit]
  have hA_not : (a : Matrix (Fin 2) (Fin 2) F) ∉ Set.range (Matrix.scalar (Fin 2)) := by
    rintro ⟨t, ht⟩
    apply hT_not_scalar t
    apply φ.injective
    rw [map_smul, map_one, ← hcoea, ← ht]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal, Matrix.smul_apply, Matrix.one_apply]
  haveI hcent : IsMulCommutative ↥(Subgroup.centralizer ({a} : Set (GL (Fin 2) F))) :=
    TauCeti.isMulCommutative_centralizer_of_notMem_range_scalar (g := a) hA_not
  intro g h
  let bg : GL (Fin 2) F := Units.map φ.toMulEquiv.toMonoidHom (ρ g)
  let bh : GL (Fin 2) F := Units.map φ.toMulEquiv.toMonoidHom (ρ h)
  have hcbg : (bg : Matrix (Fin 2) (Fin 2) F) = φ (ρ g : Module.End F U) := by simp [bg]
  have hcbh : (bh : Matrix (Fin 2) (Fin 2) F) = φ (ρ h : Module.End F U) := by simp [bh]
  have hbg : bg ∈ Subgroup.centralizer ({a} : Set (GL (Fin 2) F)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Units.ext
    simp only [Units.val_mul, hcbg, hcoea, ← map_mul, ← map_mul, T, hTcomm g]
  have hbh : bh ∈ Subgroup.centralizer ({a} : Set (GL (Fin 2) F)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Units.ext
    simp only [Units.val_mul, hcbh, hcoea, ← map_mul, ← map_mul, T, hTcomm h]
  have hcommb : bg * bh = bh * bg := by
    have h := (IsMulCommutative.is_comm
      (M := ↥(Subgroup.centralizer ({a} : Set (GL (Fin 2) F))))).comm
      ⟨bg, hbg⟩ ⟨bh, hbh⟩
    exact congrArg Subtype.val h
  apply φ.injective
  rw [map_mul, map_mul]
  have := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F)) hcommb
  simpa only [Units.val_mul, hcbg, hcbh] using this

theorem eq_one_of_perfect_of_isSymm {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {U : Type*}
    [AddCommGroup U] [Module F U] (hU : Module.finrank F U = 2) (β : LinearMap.BilinForm F U)
    (hβ : ∀ u v, β u v = β v u) (hβnd : ∀ u : U, (∀ v : U, β u v = 0) → u = 0)
    {L : Type*} [Group L] (hL : Group.IsPerfect L) (ρ : L →* (Module.End F U)ˣ)
    (hρ : ∀ g u v, β ((ρ g : Module.End F U) u) ((ρ g : Module.End F U) v) = β u v) :
    ∀ g, ρ g = 1 := by
  obtain ⟨b, ω, hωalt, hωnd, hωne⟩ := exists_alternating_plane_form hU
  have hdet := det_eq_one_of_perfect_isometry hU hL ρ
  have hωiso := alt_form_preserved_of_det_one b ω hωalt ρ hdet
  obtain ⟨eT, hTapply, hT_not_scalar⟩ :=
    exists_adjoint_nonscalar hU h2 β hβ hβnd ω hωalt hωnd hωne
  have hTcomm := adjoint_commutes β hβnd ρ hρ ω hωiso eT hTapply
  have hpair := centralizer_pairwise_commute b ρ eT hTcomm hT_not_scalar
  haveI : IsMulCommutative ρ.range :=
    IsMulCommutative.mk (Std.Commutative.mk fun x y => by
      obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp x.2
      obtain ⟨h, hh⟩ := MonoidHom.mem_range.mp y.2
      apply Subtype.ext
      change x.val * y.val = y.val * x.val
      rw [← hg, ← hh]
      apply Units.ext
      simpa only [Units.val_mul] using hpair g h)
  haveI : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
  haveI : Subsingleton ρ.range := Group.IsPerfect.subsingleton_of_isMulCommutative
  intro g
  apply Units.ext
  have h : (⟨ρ g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩ : ρ.range) = 1 := Subsingleton.elim _ _
  simpa using congrArg Subtype.val h

private theorem range_ker_invariant_of_commute {V : Type*} [AddCommGroup V] [Module F V]
    {H : Subgroup (LinearMap.GeneralLinearGroup F V)} {N : Module.End F V}
    (hcomm : ∀ g ∈ H, N * (g : Module.End F V) = (g : Module.End F V) * N) :
    (∀ g ∈ H, ∀ v ∈ LinearMap.range N, (g : Module.End F V) v ∈ LinearMap.range N) ∧
      ∀ g ∈ H, ∀ v ∈ LinearMap.ker N, (g : Module.End F V) v ∈ LinearMap.ker N := by
  constructor
  · intro g hg v hv
    obtain ⟨u, rfl⟩ := hv
    exact ⟨(g : Module.End F V) u, by
      rw [← Module.End.mul_apply, hcomm g hg, Module.End.mul_apply]⟩
  · intro g hg v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [← Module.End.mul_apply, hcomm g hg, Module.End.mul_apply, hv, map_zero]

private theorem range_eq_ker_of_perfect {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [Finite F] (hV : Module.finrank F V = 4)
    (H : Subgroup (LinearMap.GeneralLinearGroup F V)) (hH : Group.IsPerfect ↥H)
    (hfix : ∀ v : V, (∀ g ∈ H, (g : Module.End F V) v = v) → v = 0)
    {N : Module.End F V} (hN : N ≠ 0) {m : ℕ} (hm : 0 < m) (hNm : N ^ m = 0)
    (hcomm : ∀ g ∈ H, N * (g : Module.End F V) = (g : Module.End F V) * N) :
    LinearMap.range N = LinearMap.ker N ∧ Module.finrank F (LinearMap.range N) = 2 := by
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hV]; norm_num)
  have hinv := range_ker_invariant_of_commute hcomm
  let I : Submodule F V := LinearMap.range N
  let K : Submodule F V := LinearMap.ker N
  have hInebot : I ≠ ⊥ := fun h => hN (LinearMap.range_eq_bot.mp h)
  have hInetop : I ≠ ⊤ := range_ne_top_of_pow_eq_zero N hm hNm
  have hranksum : Module.finrank F I + Module.finrank F K = 4 := by
    have h := LinearMap.finrank_range_add_finrank_ker N
    rwa [hV] at h
  have hfinI : Module.finrank F I = 2 := by
    have hpos : 0 < Module.finrank F I :=
      Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hInebot)
    have hlt : Module.finrank F I < 4 := by
      have := Submodule.finrank_lt hInetop
      omega
    have hne1 : Module.finrank F I ≠ 1 := fun h1 =>
      no_invariant_line_of_perfect H hH hfix hinv.1 h1
    have hne3 : Module.finrank F I ≠ 3 := by
      intro h3
      have hK1 : Module.finrank F K = 1 := by omega
      exact no_invariant_line_of_perfect H hH hfix (P := K) hinv.2 hK1
    omega
  have hfinK : Module.finrank F K = 2 := by omega
  haveI : Nontrivial I := Submodule.nontrivial_iff_ne_bot.mpr hInebot
  have hIK_ne_bot : I ⊓ K ≠ ⊥ := by
    intro hbot
    exact hInebot (eq_bot_of_pow_eq_zero_of_disjoint_ker N (fun x _ => ⟨x, rfl⟩) hbot hNm)
  have hIK_inv : ∀ g ∈ H, ∀ v ∈ I ⊓ K, (g : Module.End F V) v ∈ I ⊓ K :=
    fun g hg v hv => ⟨hinv.1 g hg v hv.1, hinv.2 g hg v hv.2⟩
  have hIK_fin : Module.finrank F ↥(I ⊓ K) = 2 := by
    have hpos : 0 < Module.finrank F ↥(I ⊓ K) :=
      Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hIK_ne_bot)
    have hle : Module.finrank F ↥(I ⊓ K) ≤ 2 := by
      simpa [hfinI] using Submodule.finrank_mono (s := I ⊓ K) (t := I) inf_le_left
    have hne1 : Module.finrank F ↥(I ⊓ K) ≠ 1 := fun h1 =>
      no_invariant_line_of_perfect H hH hfix hIK_inv h1
    omega
  have hI_le_K : I ≤ K := by
    have h : I ⊓ K = I :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [hIK_fin, hfinI])
    rw [← h]
    exact inf_le_right
  exact ⟨Submodule.eq_of_le_of_finrank_eq hI_le_K (by rw [hfinI, hfinK]), hfinI⟩

private theorem adjoint_of_isometry {V : Type*} [AddCommGroup V] [Module F V]
    {B : LinearMap.BilinForm F V} (hB : B.IsAlt)
    {N : Module.End F V} (hN2 : N * N = 0)
    (hiso : ∀ u v, B (u + N u) (v + N v) = B u v) :
    (∀ v w, B (N v) w = B (N w) v) ∧ ∀ v w, B (N v) (N w) = 0 := by
  have hCD : (1 + N) * (1 - N) = 1 := by
    have h : (1 + N) * (1 - N) = 1 - N * N := by
      calc (1 + N) * (1 - N)
          = 1 * (1 - N) + N * (1 - N) := by rw [add_mul]
        _ = (1 - N) + (N * 1 - N * N) := by rw [one_mul, mul_sub, mul_one]
        _ = 1 - N + (N - N * N) := by rw [mul_one]
        _ = 1 - N * N := by abel
    rw [h, hN2, sub_zero]
  have hCDapply : ∀ w : V, w - N w + N (w - N w) = w := by
    intro w
    have h := congrArg (fun f : Module.End F V => f w) hCD
    rw [Module.End.mul_apply, Module.End.one_apply] at h
    simpa using h
  have hNadj : ∀ v w : V, B (N v) w = B (N w) v := by
    intro v w
    have h1 : B (v + N v) w = B v (w - N w) := by
      have h := hiso v (w - N w)
      rwa [hCDapply w] at h
    rw [map_add, LinearMap.add_apply, map_sub] at h1
    have h3 : B (N v) w = - B v (N w) := by
      rw [sub_eq_add_neg] at h1
      exact add_left_cancel h1
    have h4 : B (N w) v = - B v (N w) := (BilinForm.IsAlt.neg_eq hB v (N w)).symm
    exact h3.trans h4.symm
  refine ⟨hNadj, ?_⟩
  intro v w
  have h := hNadj (N v) w
  have hN2apply : N (N v) = 0 := by
    rw [← Module.End.mul_apply, hN2, LinearMap.zero_apply]
  rw [hN2apply] at h
  have h' : B (N w) (N v) = 0 := by simpa using h.symm
  have hneg : B (N v) (N w) = - B (N w) (N v) :=
    (BilinForm.IsAlt.neg_eq hB (N w) (N v)).symm
  rw [h', neg_zero] at hneg
  exact hneg

private theorem exists_form_on_range {V : Type*} [AddCommGroup V] [Module F V]
    {B : LinearMap.BilinForm F V} {N : Module.End F V}
    (hN2 : N * N = 0) (hker : LinearMap.ker N ≤ LinearMap.range N)
    (hadj : ∀ v w, B (N v) w = B (N w) v) :
    ∃ β : LinearMap.BilinForm F (LinearMap.range N),
      ∀ v w, β ⟨N v, v, rfl⟩ ⟨N w, w, rfl⟩ = B (N v) w := by
  let f : V →ₗ[F] LinearMap.range N := N.rangeRestrict
  have hf : f.range = ⊤ := LinearMap.range_eq_top.mpr (fun x => by
    obtain ⟨v, hv⟩ := x.2
    exact ⟨v, Subtype.ext (by change N v = x.val; exact hv)⟩)
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective f hf
  refine ⟨B.comp (LinearMap.range N).subtype s, ?_⟩
  have hNs : ∀ y : LinearMap.range N, N (s y) = y.val := by
    intro y
    have h := congrArg (fun (g : LinearMap.range N →ₗ[F] LinearMap.range N) => g y) hs
    rw [LinearMap.comp_apply, LinearMap.id_apply] at h
    exact congrArg Subtype.val h
  intro v w
  rw [BilinForm.comp_apply]
  change B (N v) (s ⟨N w, w, rfl⟩) = B (N v) w
  have hdiff : s ⟨N w, w, rfl⟩ - w ∈ LinearMap.ker N := by
    rw [LinearMap.mem_ker, map_sub, hNs, sub_self]
  obtain ⟨u, hu⟩ := hker hdiff
  have hzero : B (N v) (s ⟨N w, w, rfl⟩ - w) = 0 := by
    rw [← hu]
    have hN2apply : N (N u) = 0 := by
      rw [← Module.End.mul_apply, hN2, LinearMap.zero_apply]
    rw [hadj v (N u), hN2apply]
    simp
  rwa [map_sub, sub_eq_zero] at hzero

private theorem form_on_range_symm {V : Type*} [AddCommGroup V] [Module F V]
    {B : LinearMap.BilinForm F V} {N : Module.End F V}
    {β : LinearMap.BilinForm F (LinearMap.range N)}
    (hβ : ∀ v w, β ⟨N v, v, rfl⟩ ⟨N w, w, rfl⟩ = B (N v) w)
    (hadj : ∀ v w, B (N v) w = B (N w) v) : ∀ x y, β x y = β y x := by
  intro x y
  obtain ⟨v, hv⟩ := x.2
  obtain ⟨w, hw⟩ := y.2
  have hx : x = ⟨N v, v, rfl⟩ := Subtype.ext hv.symm
  have hy : y = ⟨N w, w, rfl⟩ := Subtype.ext hw.symm
  rw [hx, hy, hβ, hβ]
  exact hadj v w

private theorem form_on_range_nondegenerate {V : Type*} [AddCommGroup V] [Module F V]
    {B : LinearMap.BilinForm F V} (hBnd : B.Nondegenerate)
    {N : Module.End F V} {β : LinearMap.BilinForm F (LinearMap.range N)}
    (hβ : ∀ v w, β ⟨N v, v, rfl⟩ ⟨N w, w, rfl⟩ = B (N v) w) :
    ∀ x, (∀ y, β x y = 0) → x = 0 := by
  intro x hx
  obtain ⟨v, hv⟩ := x.2
  have hx' : x = ⟨N v, v, rfl⟩ := Subtype.ext hv.symm
  rw [hx'] at hx ⊢
  apply Subtype.ext
  apply hBnd.1 (N v)
  intro w
  have h := hx ⟨N w, w, rfl⟩
  rwa [hβ] at h

private theorem form_on_range_invariant {V : Type*} [AddCommGroup V] [Module F V]
    {B : LinearMap.BilinForm F V} {N : Module.End F V}
    {β : LinearMap.BilinForm F (LinearMap.range N)}
    (hβ : ∀ v w, β ⟨N v, v, rfl⟩ ⟨N w, w, rfl⟩ = B (N v) w) {g : Module.End F V}
    (hg : ∀ u v, B (g u) (g v) = B u v) (hgN : g * N = N * g)
    (hgI : ∀ x ∈ LinearMap.range N, g x ∈ LinearMap.range N) (x y : LinearMap.range N) :
    β ⟨g x.val, hgI x.val x.2⟩ ⟨g y.val, hgI y.val y.2⟩ = β x y := by
  obtain ⟨v, hv⟩ := x.2
  obtain ⟨w, hw⟩ := y.2
  obtain rfl : x = ⟨N v, v, rfl⟩ := Subtype.ext hv.symm
  obtain rfl : y = ⟨N w, w, rfl⟩ := Subtype.ext hw.symm
  have hgv : g (N v) = N (g v) := by
    have := congrArg (fun f : Module.End F V => f v) hgN
    simpa [Module.End.mul_apply] using this
  have hgw : g (N w) = N (g w) := by
    have := congrArg (fun f : Module.End F V => f w) hgN
    simpa [Module.End.mul_apply] using this
  have e1 : (⟨g (N v), hgI (N v) ⟨v, rfl⟩⟩ : LinearMap.range N) =
      ⟨N (g v), g v, rfl⟩ := Subtype.ext hgv
  have e2 : (⟨g (N w), hgI (N w) ⟨w, rfl⟩⟩ : LinearMap.range N) =
      ⟨N (g w), g w, rfl⟩ := Subtype.ext hgw
  rw [e1, e2, hβ, hβ, ← hgv]
  exact hg (N v) w

private theorem eq_bot_of_perfect_of_isSymm {V : Type*} [AddCommGroup V] [Module F V]
    (h2 : (2 : F) ≠ 0) (H : Subgroup (LinearMap.GeneralLinearGroup F V))
    (hH : Group.IsPerfect ↥H)
    (hfix : ∀ v : V, (∀ g ∈ H, (g : Module.End F V) v = v) → v = 0)
    {I : Submodule F V} (hI : ∀ g ∈ H, ∀ v ∈ I, (g : Module.End F V) v ∈ I)
    (hI2 : Module.finrank F I = 2) {β : LinearMap.BilinForm F I}
    (hβsym : ∀ x y, β x y = β y x)
    (hβnd : ∀ x, (∀ y, β x y = 0) → x = 0)
    (hβinv : ∀ g : ↥H, ∀ x y : I,
      β (((CFSG.LinearGroups.invariantRestrict H I hI g : (Module.End F I)ˣ) :
          Module.End F I) x)
        (((CFSG.LinearGroups.invariantRestrict H I hI g : (Module.End F I)ˣ) :
          Module.End F I) y) = β x y) :
    I = ⊥ := by
  by_contra hbot
  haveI : Nontrivial I := Submodule.nontrivial_iff_ne_bot.mpr hbot
  obtain ⟨v, hv0⟩ := exists_ne (0 : I)
  apply hv0
  apply Subtype.ext
  apply hfix v.val
  intro g hg
  have h1 : CFSG.LinearGroups.invariantRestrict H I hI ⟨g, hg⟩ = 1 :=
    (eq_one_of_perfect_of_isSymm h2 hI2 β hβsym hβnd hH
      (CFSG.LinearGroups.invariantRestrict H I hI) hβinv) ⟨g, hg⟩
  have h2' : (((CFSG.LinearGroups.invariantRestrict H I hI ⟨g, hg⟩ :
      (Module.End F I)ˣ) : Module.End F I) v) = v := by rw [h1]; rfl
  have h3 := congrArg Subtype.val h2'
  rw [CFSG.LinearGroups.coe_invariantRestrict_apply] at h3
  exact h3

private noncomputable def sp4Diff (c : GL (Fin 2 ⊕ Fin 2) F) :
    Module.End F (Sp4VecF F) :=
  Matrix.toLin' ((c : Sp4MatF F) - 1)

private noncomputable def sp4Image (L : Subgroup (GL (Fin 2 ⊕ Fin 2) F)) :
    Subgroup (LinearMap.GeneralLinearGroup F (Sp4VecF F)) :=
  (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp L.subtype).range

private theorem sp4Diff_ne_zero {c : GL (Fin 2 ⊕ Fin 2) F} (hc : c ≠ 1) :
    sp4Diff c ≠ 0 := by
  intro h
  apply hc
  apply Units.ext
  have hA : (c : Sp4MatF F) - 1 = 0 := by
    have h' := congrArg Matrix.toLin'.symm h
    simpa [sp4Diff, LinearMap.toMatrix'_toLin'] using h'
  simpa using sub_eq_zero.mp hA

private theorem sp4Diff_pow_eq_zero {c : GL (Fin 2 ⊕ Fin 2) F} {k : ℕ}
    (hcp : c ^ p ^ k = 1) : sp4Diff c ^ p ^ k = 0 := by
  have hcmat : (c : Sp4MatF F) ^ (p ^ k) = 1 := by
    rw [← Units.val_pow_eq_pow_val, hcp, Units.val_one]
  have hA : ((c : Sp4MatF F) - 1) ^ (p ^ k) = 0 := by
    have h := sub_pow_char_pow_of_commute (R := Sp4MatF F) p k
      (Commute.one_right (c : Sp4MatF F))
    rwa [hcmat, one_pow, sub_self] at h
  rw [sp4Diff, ← Matrix.toLin'_pow, hA, map_zero]

private theorem sp4Diff_isometry {c : GL (Fin 2 ⊕ Fin 2) F}
    (hc : c ∈ CFSG.Open.StatedSp 2 F) :
    ∀ u v : Sp4VecF F,
      CFSG.RankThree.SubgroupLists.spForm 2 F (u + sp4Diff c u) (v + sp4Diff c v) =
        CFSG.RankThree.SubgroupLists.spForm 2 F u v := by
  intro u v
  have h := CFSG.RankThree.SubgroupLists.mem_statedSp_iff_preserves.mp hc u v
  have hC : ∀ u : Sp4VecF F, (c : Sp4MatF F) *ᵥ u = u + sp4Diff c u := by
    intro u
    rw [sp4Diff, Matrix.toLin'_apply, sub_mulVec, Matrix.one_mulVec]
    abel
  simpa [hC] using h

private theorem sp4Image_fix {L : Subgroup (GL (Fin 2 ⊕ Fin 2) F)}
    (hfix : ∀ v : Sp4VecF F, (∀ g ∈ L, (g : Sp4MatF F) *ᵥ v = v) → v = 0) :
    ∀ v : Sp4VecF F,
      (∀ g ∈ sp4Image L,
        ((g : LinearMap.GeneralLinearGroup F (Sp4VecF F)) : Module.End F (Sp4VecF F)) v = v) →
      v = 0 := by
  intro v hv
  apply hfix v
  intro g hg
  have hmem : Matrix.GeneralLinearGroup.toLin g ∈ sp4Image L :=
    MonoidHom.mem_range.mpr ⟨⟨g, hg⟩, rfl⟩
  have h := hv (Matrix.GeneralLinearGroup.toLin g) hmem
  simpa [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVec_mulVec] using h

private theorem sp4Diff_commutes {L : Subgroup (GL (Fin 2 ⊕ Fin 2) F)}
    {c : GL (Fin 2 ⊕ Fin 2) F} (hcomm : ∀ g ∈ L, c * g = g * c) :
    ∀ g ∈ sp4Image L,
      sp4Diff c * ((g : LinearMap.GeneralLinearGroup F (Sp4VecF F)) :
        Module.End F (Sp4VecF F)) =
      ((g : LinearMap.GeneralLinearGroup F (Sp4VecF F)) :
        Module.End F (Sp4VecF F)) * sp4Diff c := by
  intro g hg
  obtain ⟨l, rfl⟩ := MonoidHom.mem_range.mp hg
  change sp4Diff c * ((Matrix.GeneralLinearGroup.toLin l :
      LinearMap.GeneralLinearGroup F (Sp4VecF F)) : Module.End F (Sp4VecF F)) =
    ((Matrix.GeneralLinearGroup.toLin l :
      LinearMap.GeneralLinearGroup F (Sp4VecF F)) : Module.End F (Sp4VecF F)) * sp4Diff c
  have hmat : (c : Sp4MatF F) * ((l : GL (Fin 2 ⊕ Fin 2) F) : Sp4MatF F) =
      ((l : GL (Fin 2 ⊕ Fin 2) F) : Sp4MatF F) * (c : Sp4MatF F) := by
    have h := congrArg (fun u : GL (Fin 2 ⊕ Fin 2) F => (u : Sp4MatF F)) (hcomm l l.2)
    simpa using h
  have hmatA : ((c : Sp4MatF F) - 1) * ((l : GL (Fin 2 ⊕ Fin 2) F) : Sp4MatF F) =
      ((l : GL (Fin 2 ⊕ Fin 2) F) : Sp4MatF F) * ((c : Sp4MatF F) - 1) := by
    rw [sub_mul, mul_sub, hmat]
    simp
  have hgval : ((Matrix.GeneralLinearGroup.toLin l :
      LinearMap.GeneralLinearGroup F (Sp4VecF F)) : Module.End F (Sp4VecF F)) =
      Matrix.toLin' ((l : GL (Fin 2 ⊕ Fin 2) F) : Sp4MatF F) := by
    rw [Matrix.GeneralLinearGroup.coe_toLin]
    apply LinearMap.ext
    intro u
    rw [Matrix.mulVecLin_apply, Matrix.toLin'_apply]
  rw [sp4Diff, hgval, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
    ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hmatA]

private theorem sp4Image_isometry {L : Subgroup (GL (Fin 2 ⊕ Fin 2) F)}
    (hLS : L ≤ CFSG.Open.StatedSp 2 F) :
    ∀ g ∈ sp4Image L, ∀ u v : Sp4VecF F,
      CFSG.RankThree.SubgroupLists.spForm 2 F
        (((g : LinearMap.GeneralLinearGroup F (Sp4VecF F)) : Module.End F (Sp4VecF F)) u)
        (((g : LinearMap.GeneralLinearGroup F (Sp4VecF F)) : Module.End F (Sp4VecF F)) v) =
        CFSG.RankThree.SubgroupLists.spForm 2 F u v := by
  intro g hg u v
  obtain ⟨l, rfl⟩ := MonoidHom.mem_range.mp hg
  have h := CFSG.RankThree.SubgroupLists.mem_statedSp_iff_preserves.mp (hLS l.2) u v
  simpa [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVec_mulVec] using h

private theorem false_of_perfect_nilpotent_isometry {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (h2 : (2 : F) ≠ 0) (hV : Module.finrank F V = 4)
    (H : Subgroup (LinearMap.GeneralLinearGroup F V)) (hH : Group.IsPerfect ↥H)
    (hfix : ∀ v : V, (∀ g ∈ H, (g : Module.End F V) v = v) → v = 0)
    {B : LinearMap.BilinForm F V} (hBalt : B.IsAlt) (hBnd : B.Nondegenerate)
    {N : Module.End F V} (hN : N ≠ 0) {m : ℕ} (hm : 0 < m) (hNm : N ^ m = 0)
    (hcomm : ∀ g ∈ H, N * (g : Module.End F V) = (g : Module.End F V) * N)
    (hiso : ∀ u v, B (u + N u) (v + N v) = B u v)
    (hisoH : ∀ g ∈ H, ∀ u v : V,
      B ((g : Module.End F V) u) ((g : Module.End F V) v) = B u v) : False := by
  have hA := range_eq_ker_of_perfect hV H hH hfix hN hm hNm hcomm
  have hIinv := (range_ker_invariant_of_commute hcomm).1
  have hN2 : N * N = 0 := by
    apply LinearMap.ext
    intro v
    have hv : N v ∈ LinearMap.ker N := hA.1 ▸ ⟨v, rfl⟩
    rw [Module.End.mul_apply]
    exact LinearMap.mem_ker.mp hv
  have hB := adjoint_of_isometry hBalt hN2 hiso
  obtain ⟨β, hβ⟩ := exists_form_on_range hN2 (le_of_eq hA.1.symm) hB.1
  have hβsym := form_on_range_symm hβ hB.1
  have hβnd := form_on_range_nondegenerate hBnd hβ
  have hβinv : ∀ g : ↥H, ∀ x y : LinearMap.range N,
      β (((CFSG.LinearGroups.invariantRestrict H (LinearMap.range N) hIinv g :
          (Module.End F (LinearMap.range N))ˣ) : Module.End F (LinearMap.range N)) x)
        (((CFSG.LinearGroups.invariantRestrict H (LinearMap.range N) hIinv g :
          (Module.End F (LinearMap.range N))ˣ) : Module.End F (LinearMap.range N)) y) =
        β x y := by
    intro g x y
    change β ⟨((g : LinearMap.GeneralLinearGroup F V) : Module.End F V) x.val,
        hIinv g g.2 x.val x.2⟩
      ⟨((g : LinearMap.GeneralLinearGroup F V) : Module.End F V) y.val,
        hIinv g g.2 y.val y.2⟩ = β x y
    exact form_on_range_invariant hβ (hisoH g g.2) (hcomm g g.2).symm (hIinv g g.2) x y
  have hbot := eq_bot_of_perfect_of_isSymm h2 H hH hfix hIinv hA.2 hβsym hβnd hβinv
  exact (fun h => hN (LinearMap.range_eq_bot.mp h)) hbot

private theorem eq_one_of_commute_of_perfect_aux (hp2 : p ≠ 2)
    {L : Subgroup (GL (Fin 2 ⊕ Fin 2) F)} (hLS : L ≤ CFSG.Open.StatedSp 2 F)
    (hL : Group.IsPerfect ↥L)
    (hfix : ∀ v : Sp4VecF F,
      (∀ g ∈ L, (g : Sp4MatF F) *ᵥ v = v) → v = 0)
    {c : GL (Fin 2 ⊕ Fin 2) F} (hc : c ∈ CFSG.Open.StatedSp 2 F) {k : ℕ}
    (hcp : c ^ p ^ k = 1) (hcomm : ∀ g ∈ L, c * g = g * c) : c = 1 := by
  classical
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).mp h
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact (Fact.out : p.Prime).ne_one h1
    · exact hp2 h2
  by_contra hc1
  have hVdim : Module.finrank F (Sp4VecF F) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum]
    norm_num
  exact false_of_perfect_nilpotent_isometry h2 hVdim (sp4Image L)
    (Group.IsPerfect.range _) (sp4Image_fix hfix)
    CFSG.RankThree.SubgroupLists.spForm_isAlt
    CFSG.RankThree.SubgroupLists.spForm_nondegenerate
    (sp4Diff_ne_zero hc1) (pow_pos (Fact.out : p.Prime).pos k) (sp4Diff_pow_eq_zero hcp)
    (sp4Diff_commutes hcomm) (sp4Diff_isometry hc) (sp4Image_isometry hLS)

theorem eq_one_of_commute_of_perfect {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {L : Subgroup (GL (Fin 2 ⊕ Fin 2) (ZMod p))} (hLS : L ≤ CFSG.Open.StatedSp 2 (ZMod p))
    (hL : Group.IsPerfect ↥L)
    (hfix : ∀ v : Fin 2 ⊕ Fin 2 → ZMod p,
      (∀ g ∈ L, (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod p)) *ᵥ v = v) → v = 0)
    {c : GL (Fin 2 ⊕ Fin 2) (ZMod p)} (hc : c ∈ CFSG.Open.StatedSp 2 (ZMod p)) {k : ℕ}
    (hcp : c ^ p ^ k = 1) (hcomm : ∀ g ∈ L, c * g = g * c) : c = 1 :=
  eq_one_of_commute_of_perfect_aux (F := ZMod p) hp2 hLS hL hfix hc hcp hcomm

