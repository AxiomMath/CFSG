module

public import CFSG.Fischer.Classification.Recognition.SymOBasic
public import CFSG.ClassicalGroups.Orthogonal.CharTwoTransvection
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
import CFSG.ClassicalGroups.Symplectic.Simple
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

public section

namespace CFSG.Fischer.Classification.Recognition.SymO

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Open QuadraticMap Submodule CFSG.ClassicalGroups.Orthogonal
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open LinearMap (BilinForm)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

theorem zmod_two_eq_zero_or_eq_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem zmod_two_mul_self (a : ZMod 2) : a * a = a := by
  revert a
  decide

variable (Q) in
abbrev bil : BilinForm (ZMod 2) V := polarBilin Q

theorem bil_apply (x y : V) : bil Q x y = polar Q x y := polarBilin_apply_apply Q x y

variable (Q) in
theorem bil_isAlt : (bil Q).IsAlt := fun x => by
  rw [bil_apply, polar_self_eq_two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul]

theorem polar_self_zmod_two (x : V) : polar Q x x = 0 := by
  rw [polar_self_eq_two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul]

theorem map_add_smul {x v : V} (hv : Q v = 1) (hxv : polar Q x v = 0) (c : ZMod 2) :
    Q (x + c • v) = Q x + c := by
  rw [QuadraticMap.map_add (⇑Q), QuadraticMap.map_smul, hv, polar_smul_right, hxv, smul_zero,
    add_zero, smul_eq_mul, mul_one, zmod_two_mul_self]

section Fix

variable (hnd : (polarBilin Q).Nondegenerate) {v : V} (hv : Q v = 1)
include hnd hv

theorem exists_polar_eq_one : ∃ y, polar Q y v = 1 := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hv
    exact zero_ne_one hv
  obtain ⟨y, hy⟩ := exists_polar_ne_zero hnd hv0
  exact ⟨y, by rw [polar_comm]; exact (zmod_two_eq_zero_or_eq_one _).resolve_left hy⟩

theorem apply_eq_self_of_commute {g t : V ≃ₗ[ZMod 2] V}
    (ht : ∀ x, t x = x + polar Q x v • v) (hgt : g * t = t * g) : g v = v := by
  obtain ⟨x, hx⟩ := exists_polar_eq_one hnd hv
  have key := DFunLike.congr_fun hgt x
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ht, ht, map_add, map_smul, hx, one_smul]
    at key
  have key' := add_left_cancel key
  rcases zmod_two_eq_zero_or_eq_one (polar Q (g x) v) with h | h
  · rw [h, zero_smul, LinearEquiv.map_eq_zero_iff] at key'
    rw [key', QuadraticMap.map_zero] at hv
    exact absurd hv zero_ne_one
  · rwa [h, one_smul] at key'

end Fix

section Restr

variable {v y : V}

variable (Q v y) in
abbrev perp : Submodule (ZMod 2) V := (bil Q).orthogonal (span (ZMod 2) {v, y})

theorem mem_perp {w : V} : w ∈ perp Q v y ↔ polar Q v w = 0 ∧ polar Q y w = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_span_pair_iff, bil_apply, bil_apply]

theorem polar_perp_left (w : perp Q v y) : polar Q w v = 0 := by
  rw [polar_comm]
  exact (mem_perp.mp w.2).1

variable (hyv : polar Q y v = 1)
include hyv

theorem bil_eq_one : bil Q y v = 1 := by
  rwa [bil_apply]

abbrev proj : V →ₗ[ZMod 2] perp Q v y :=
  pairProj (bil_isAlt Q) (bil_eq_one hyv)

theorem coe_proj (u : V) : (proj hyv u : V) = u - polar Q y u • v + polar Q v u • y := by
  rw [coe_pairProj, bil_apply, bil_apply]

theorem proj_coe (w : perp Q v y) : proj hyv w = w := pairProj_coe _ _ w

theorem proj_left : proj hyv v = 0 := pairProj_left _ _

theorem eq_proj_add (u : V) : u = (proj hyv u : V) + (polar Q y u • v - polar Q v u • y) := by
  rw [← bil_apply, ← bil_apply, ← sub_pairProj (bil_isAlt Q) (bil_eq_one hyv)]
  abel

@[expose] def restr (g : V →ₗ[ZMod 2] V) : perp Q v y →ₗ[ZMod 2] perp Q v y :=
  proj hyv ∘ₗ g ∘ₗ (perp Q v y).subtype

theorem restr_apply (g : V →ₗ[ZMod 2] V) (w : perp Q v y) : restr hyv g w = proj hyv (g w) :=
  rfl

variable {g h : V ≃ₗ[ZMod 2] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgv : g v = v)
include hg hgv

omit hyv in
theorem polar_apply_fix (x : V) : polar Q v (g x) = polar Q v x := by
  rw [← polar_map_of_mem hg v x, hgv]

omit hyv in
theorem polar_apply_fix' (x : V) : polar Q (g x) v = polar Q x v := by
  rw [polar_comm, polar_apply_fix hg hgv, polar_comm]

theorem coe_restr (w : perp Q v y) :
    (restr hyv g w : V) = g w - polar Q y (g w) • v := by
  rw [restr_apply, coe_proj, LinearEquiv.coe_coe, polar_apply_fix hg hgv, (mem_perp.mp w.2).1,
    zero_smul, add_zero]

theorem isIsometry_restr :
    TauCeti.BilinForm.IsIsometry ((bil Q).restrict (perp Q v y)) (restr hyv g) := by
  rw [TauCeti.BilinForm.isIsometry_iff]
  intro w w'
  simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply, bil_apply]
  have h1 : polar Q (g w) v = 0 := by rw [polar_apply_fix' hg hgv, polar_perp_left]
  have h2 : polar Q v (g w') = 0 := by rw [polar_apply_fix hg hgv, polar_comm, polar_perp_left]
  rw [coe_restr hyv hg hgv, coe_restr hyv hg hgv, polar_sub_left, polar_sub_right,
    polar_sub_right, polar_smul_left, polar_smul_right, polar_smul_right, polar_smul_left, h1, h2,
    polar_self_zmod_two, polar_map_of_mem hg]
  simp

omit hg in
theorem restr_mul (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hhv : h v = v)
    (w : perp Q v y) :
    restr hyv ((g * h : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) w =
      restr hyv g (restr hyv h w) := by
  rw [restr_apply, restr_apply hyv g, coe_restr hyv hh hhv, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, map_sub, map_smul, hgv, map_sub, map_smul, proj_left, smul_zero, sub_zero,
    LinearEquiv.mul_apply]

end Restr

section Kernel

variable {v y : V} (hv : Q v = 1) (hyv : polar Q y v = 1)

include hv hyv in
theorem apply_eq_of_restr_eq_id {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgv : g v = v)
    (h1 : ∀ w, restr hyv g w = w) (x : V) : g x = x - polar Q v x • (g y - y) := by
  have hW : ∀ w : perp Q v y, g w = w := by
    intro w
    have hc := congrArg Subtype.val (h1 w)
    rw [coe_restr hyv hg hgv] at hc
    have hgw : g w = w + polar Q y (g w) • v := eq_add_of_sub_eq hc
    have hQ := map_of_mem hg (w : V)
    rw [hgw, map_add_smul hv (polar_perp_left w)] at hQ
    have hc0 : polar Q y (g w) = 0 := by simpa using hQ
    rw [hgw, hc0, zero_smul, add_zero]
  have hx := eq_proj_add hyv x
  conv_lhs => rw [hx]
  rw [map_add, hW, map_sub, map_smul, map_smul, hgv]
  conv_rhs => arg 1; rw [hx]
  rw [smul_sub]
  abel

include hv hyv in
theorem commute_of_restr_eq_id {g h : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgv : g v = v)
    (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hhv : h v = v)
    (h1g : ∀ w, restr hyv g w = w) (h1h : ∀ w, restr hyv h w = w) : g * h = h * g := by
  have eg := apply_eq_of_restr_eq_id hv hyv hg hgv h1g
  have eh := apply_eq_of_restr_eq_id hv hyv hh hhv h1h
  refine LinearEquiv.ext fun x => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, eg (h x), eh x, eh (g x), eg x]
  simp only [polar_sub_right, polar_smul_right, polar_apply_fix hg hgv, polar_apply_fix hh hhv,
    sub_self, smul_zero, sub_zero]
  abel

end Kernel

section Lift

variable {v y : V} (hv : Q v = 1)

variable (Q v) in
def lift (w : V) : V := w + (Q w + 1) • v

include hv

theorem map_lift (w : perp Q v y) : Q (lift Q v w) = 1 := by
  rw [lift, map_add_smul hv (polar_perp_left w)]
  generalize Q w = a
  revert a
  decide

omit hv in
theorem polar_lift (w : perp Q v y) : polar Q (lift Q v w) v = 0 := by
  rw [lift, polar_add_left, polar_smul_left, polar_perp_left, polar_self_zmod_two, smul_zero,
    add_zero]

omit hv in
theorem polar_lift_right (w x : perp Q v y) : polar Q x (lift Q v w) = polar Q x w := by
  rw [lift, polar_add_right, polar_smul_right, polar_perp_left, smul_zero, add_zero]

theorem reflect_lift_apply (w : perp Q v y) (x : V) :
    reflect Q (lift Q v w) x = x + polar Q x (lift Q v w) • lift Q v w :=
  reflect_apply_of_map_eq_one (map_lift hv w) x

variable (hyv : polar Q y v = 1)
include hyv

omit hv in
theorem proj_lift (w : perp Q v y) : proj hyv (lift Q v w) = w := by
  rw [lift, map_add, map_smul, proj_left, smul_zero, add_zero, proj_coe]

theorem restr_reflect_lift (w x : perp Q v y) :
    restr hyv (reflect Q (lift Q v w) : V →ₗ[ZMod 2] V) x = x + polar Q x w • w := by
  rw [restr_apply, LinearEquiv.coe_coe, reflect_lift_apply hv, map_add, map_smul, proj_coe,
    proj_lift hyv, polar_lift_right]

omit hyv in
theorem reflect_lift_commute {t : V ≃ₗ[ZMod 2] V} (ht : ∀ x, t x = x + polar Q x v • v)
    (w : perp Q v y) : reflect Q (lift Q v w) * t = t * reflect Q (lift Q v w) := by
  have h1 := polar_lift w
  have h2 : polar Q v (lift Q v w) = 0 := by rw [polar_comm, h1]
  refine LinearEquiv.ext fun x => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ht, ht, reflect_lift_apply hv,
    reflect_lift_apply hv, polar_add_left, polar_add_left, polar_smul_left, polar_smul_left, h1, h2,
    smul_zero, add_zero, smul_zero, add_zero]
  abel

end Lift

section Rho

variable [FiniteDimensional (ZMod 2) V] (hnd : (polarBilin Q).Nondegenerate) {v y : V}
  (hv : Q v = 1) (hyv : polar Q y v = 1) (t : TauCeti.QuadraticMap.orthogonalGroup Q)
  (ht : ∀ x, (t : V ≃ₗ[ZMod 2] V) x = x + polar Q x v • v)

omit [FiniteDimensional (ZMod 2) V] in
include hnd hv ht in
theorem apply_eq_self_of_mem_centralizer {c : TauCeti.QuadraticMap.orthogonalGroup Q}
    (hc : c ∈ Subgroup.centralizer {t}) : (c : V ≃ₗ[ZMod 2] V) v = v :=
  apply_eq_self_of_commute hnd hv ht
    (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc))

omit [FiniteDimensional (ZMod 2) V] in
include hnd hyv in
theorem separatingLeft_restrict : ((bil Q).restrict (perp Q v y)).SeparatingLeft :=
  ((bil_isAlt Q).restrict_nondegenerate_orthogonal_span_pair (bil_eq_one hyv) hnd).1

noncomputable def rhoFun (c : Subgroup.centralizer {t}) :
    TauCeti.BilinForm.isometryGroup ((bil Q).restrict (perp Q v y)) :=
  TauCeti.BilinForm.IsIsometry.toIsometryGroup (separatingLeft_restrict hnd hyv)
    (isIsometry_restr hyv (c : TauCeti.QuadraticMap.orthogonalGroup Q).2
      (apply_eq_self_of_mem_centralizer hnd hv t ht c.2))

theorem rhoFun_apply (c : Subgroup.centralizer {t}) (w : perp Q v y) :
    (rhoFun hnd hv hyv t ht c : perp Q v y ≃ₗ[ZMod 2] perp Q v y) w =
      restr hyv ((c : TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[ZMod 2] V) w :=
  TauCeti.BilinForm.IsIsometry.toIsometryGroup_apply _ _ _

noncomputable def rho : Subgroup.centralizer {t} →*
    TauCeti.BilinForm.isometryGroup ((bil Q).restrict (perp Q v y)) where
  toFun := rhoFun hnd hv hyv t ht
  map_one' := by
    refine Subtype.ext (LinearEquiv.ext fun w => ?_)
    rw [rhoFun_apply, restr_apply]
    exact proj_coe hyv w
  map_mul' c d := by
    refine Subtype.ext (LinearEquiv.ext fun w => ?_)
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, rhoFun_apply, rhoFun_apply, rhoFun_apply]
    exact restr_mul hyv (apply_eq_self_of_mem_centralizer hnd hv t ht c.2)
      (d : TauCeti.QuadraticMap.orthogonalGroup Q).2
      (apply_eq_self_of_mem_centralizer hnd hv t ht d.2) w

theorem rho_apply (c : Subgroup.centralizer {t}) (w : perp Q v y) :
    (rho hnd hv hyv t ht c : perp Q v y ≃ₗ[ZMod 2] perp Q v y) w =
      restr hyv ((c : TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[ZMod 2] V) w :=
  rhoFun_apply hnd hv hyv t ht c w

theorem rho_ker_commute : ∀ a ∈ (rho hnd hv hyv t ht).ker, ∀ b ∈ (rho hnd hv hyv t ht).ker,
    a * b = b * a := by
  intro a ha b hb
  have h1 : ∀ c ∈ (rho hnd hv hyv t ht).ker, ∀ w,
      restr hyv ((c : TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[ZMod 2] V) w = w := by
    intro c hc w
    rw [← rho_apply hnd hv hyv t ht, MonoidHom.mem_ker.mp hc]
    rfl
  refine Subtype.ext (Subtype.ext ?_)
  exact commute_of_restr_eq_id hv hyv (a : TauCeti.QuadraticMap.orthogonalGroup Q).2
    (apply_eq_self_of_mem_centralizer hnd hv t ht a.2)
    (b : TauCeti.QuadraticMap.orthogonalGroup Q).2
    (apply_eq_self_of_mem_centralizer hnd hv t ht b.2) (h1 a ha) (h1 b hb)

theorem exists_rho_eq (w : perp Q v y) : ∃ c, ∀ x,
    (rho hnd hv hyv t ht c : perp Q v y ≃ₗ[ZMod 2] perp Q v y) x = x + polar Q x w • w := by
  refine ⟨⟨⟨reflect Q (lift Q v w), reflect_mem_orthogonalGroup Q _⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext ?_)⟩, fun x => ?_⟩
  · exact reflect_lift_commute hv ht w
  · rw [rho_apply]
    exact restr_reflect_lift hv hyv w x

theorem rho_surjective
    (hS : IsSimpleGroup (TauCeti.BilinForm.isometryGroup ((bil Q).restrict (perp Q v y))))
    (hW : ∃ w : perp Q v y, w ≠ 0) : Function.Surjective (rho hnd hv hyv t ht) := by
  set T : Set (TauCeti.BilinForm.isometryGroup ((bil Q).restrict (perp Q v y))) :=
    {σ | ∃ w : perp Q v y, ∀ x, (σ : perp Q v y ≃ₗ[ZMod 2] perp Q v y) x = x + polar Q x w • w}
  have hTρ : T ⊆ (rho hnd hv hyv t ht).range := by
    rintro σ ⟨w, hw⟩
    obtain ⟨c, hc⟩ := exists_rho_eq hnd hv hyv t ht w
    exact ⟨c, Subtype.ext (LinearEquiv.ext fun x => (hc x).trans (hw x).symm)⟩
  have hconj : Group.conjugatesOfSet T ⊆ T := by
    intro σ hσ
    obtain ⟨τ, ⟨w, hw⟩, hτσ⟩ := Group.mem_conjugatesOfSet_iff.mp hσ
    obtain ⟨s, rfl⟩ := isConj_iff.mp hτσ
    refine ⟨(s : perp Q v y ≃ₗ[ZMod 2] perp Q v y) w, fun x => ?_⟩
    have key : polar Q ((s : perp Q v y ≃ₗ[ZMod 2] perp Q v y)⁻¹ x : V) w =
        polar Q x ((s : perp Q v y ≃ₗ[ZMod 2] perp Q v y) w) := by
      have := TauCeti.BilinForm.mem_isometryGroup_iff.mp s.2
        ((s : perp Q v y ≃ₗ[ZMod 2] perp Q v y)⁻¹ x) w
      simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply, bil_apply,
        LinearEquiv.apply_inv_apply'] at this
      exact this.symm
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, hw, map_add, map_smul, LinearEquiv.apply_inv_apply', key]
  obtain ⟨w, hw0⟩ := hW
  obtain ⟨x, hx⟩ : ∃ x : perp Q v y, polar Q x w = 1 := by
    by_contra! h
    refine hw0 (separatingLeft_restrict hnd hyv w fun x => ?_)
    simp only [LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply, bil_apply]
    rw [polar_comm]
    exact (zmod_two_eq_zero_or_eq_one _).resolve_right (h x)
  obtain ⟨c, hc⟩ := exists_rho_eq hnd hv hyv t ht w
  have hne : Subgroup.normalClosure T ≠ ⊥ := by
    intro h
    have hmem : rho hnd hv hyv t ht c ∈ Subgroup.normalClosure T :=
      Subgroup.subset_normalClosure ⟨w, hc⟩
    rw [h, Subgroup.mem_bot] at hmem
    have := hc x
    rw [hmem, hx, one_smul] at this
    exact hw0 (by simpa using this)
  have htop := (hS.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure T)).resolve_left hne
  have hle : Subgroup.normalClosure T ≤ (rho hnd hv hyv t ht).range :=
    (Subgroup.closure_le _).mpr (hconj.trans hTρ)
  intro σ
  exact MonoidHom.mem_range.mp (hle (htop ▸ Subgroup.mem_top σ))

end Rho

section Symplectic

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  (B : BilinForm (ZMod 2) W) (hB : B.IsAlt) (hnd : B.Nondegenerate) {k : ℕ}
  (hk : Module.finrank (ZMod 2) W = 2 * k)
include hB hnd hk

theorem card_isometryGroup_two :
    Nat.card (TauCeti.BilinForm.isometryGroup B) =
      2 ^ (k ^ 2) * ∏ j ∈ Finset.Icc 1 k, (2 ^ (2 * j) - 1) := by
  rw [card_isometryGroup k B hB hnd hk, Nat.card_zmod]

theorem isSimpleGroup_isometryGroup (hk3 : 3 ≤ k) :
    IsSimpleGroup (TauCeti.BilinForm.isometryGroup B) := by
  obtain ⟨k', b, hk', hb⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_symplectic_basis B hB hnd
  obtain rfl : k' = k := by omega
  have : Subsingleton (ZMod 2)ˣ := ⟨by decide⟩
  have hscal : (CFSG.Assembly.LowTwoRank.StatedScalars (Fin k' ⊕ Fin k') (ZMod 2)).subgroupOf
      (CFSG.Assembly.LowTwoRank.StatedSp k' (ZMod 2)) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hg
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hc, Subsingleton.elim c 1, map_one]
    rfl
  have : IsSimpleGroup (CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSp k' (ZMod 2))) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp (ZMod 2) k' (by omega)
      (Or.inr (Or.inr ⟨Nat.card_zmod 2, hk3⟩))
  exact ((CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometryMatrixEquiv b B
    hb).trans ((MulEquiv.subgroupCongr
      CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic.symm).trans
        ((QuotientGroup.quotientMulEquivOfEq hscal).trans
          QuotientGroup.quotientBot).symm)).isSimpleGroup

end Symplectic

theorem componentOrder_orthogonal [Finite V] [FiniteDimensional (ZMod 2) V]
    (hnd : (polarBilin Q).Nondegenerate) {v : V} (hv : Q v = 1)
    (t : TauCeti.QuadraticMap.orthogonalGroup Q)
    (ht : ∀ x, (t : V ≃ₗ[ZMod 2] V) x = x + polar Q x v • v)
    {K : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)}
    (hK : IsComponentOf K (Subgroup.centralizer {t})) :
    Nat.card (K ⧸ Subgroup.center K) ∉ fischerComponentOrders := by
  obtain ⟨y, hyv⟩ := exists_polar_eq_one hnd hv
  have hB' : ((bil Q).restrict (perp Q v y)).IsAlt := fun x => (bil_isAlt Q).self_eq_zero x
  have hnd' : ((bil Q).restrict (perp Q v y)).Nondegenerate :=
    (bil_isAlt Q).restrict_nondegenerate_orthogonal_span_pair (bil_eq_one hyv) hnd
  obtain ⟨k, hk⟩ := hB'.even_finrank hnd'
  have hk2 : Module.finrank (ZMod 2) (perp Q v y) = 2 * k := by omega
  have hcard := card_isometryGroup_two _ hB' hnd' hk2
  have : Finite (V ≃ₗ[ZMod 2] V) := Finite.of_injective _ DFunLike.coe_injective
  have : Finite (perp Q v y ≃ₗ[ZMod 2] perp Q v y) := Finite.of_injective _ DFunLike.coe_injective
  set ρ := rho hnd hv hyv t ht
  set f : K →* TauCeti.BilinForm.isometryGroup ((bil Q).restrict (perp Q v y)) :=
    ρ.comp (Subgroup.inclusion hK.1)
  have hf : ∀ a ∈ f.ker, ∀ b ∈ f.ker, a * b = b * a := fun a ha b hb =>
    Subgroup.inclusion_injective hK.1 (by
      simpa only [map_mul] using rho_ker_commute hnd hv hyv t ht _ ha _ hb)
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  ·
    refine notMem_of_lt (lt_of_le_of_lt (card_quotient_center_le hK.2.2 f hf) ?_)
    rw [hcard]
    interval_cases k <;> decide
  ·
    have hS := isSimpleGroup_isometryGroup _ hB' hnd' hk2 hk3
    have : Nontrivial (perp Q v y) := by
      apply Module.nontrivial_of_finrank_pos (R := ZMod 2)
      omega
    have hsurj := rho_surjective hnd hv hyv t ht hS (exists_ne 0)
    have hfsurj : Function.Surjective f := by
      rcases IsSubnormal.map_eq_bot_or_eq_top hK.2.1 hS ρ hsurj with h | h
      · refine (IsQuasisimple.not_le_of_comm hK.2.2 (A := K) ?_ le_rfl).elim
        have hker : ∀ a (ha : a ∈ K), (⟨a, hK.1 ha⟩ : Subgroup.centralizer {t}) ∈ ρ.ker := by
          intro a ha
          rw [MonoidHom.mem_ker, ← Subgroup.mem_bot, ← h]
          exact Subgroup.mem_map_of_mem ρ ha
        intro a ha b hb
        exact congrArg Subtype.val (rho_ker_commute hnd hv hyv t ht _ (hker a ha) _ (hker b hb))
      · rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.inclusion_range, h]
    rw [card_quotient_center_eq hS hK.2.2 f hfsurj hf, hcard]
    exact two_pow_mul_notMem k (odd_prod_two_pow_sub_one k)

end CFSG.Fischer.Classification.Recognition.SymO
