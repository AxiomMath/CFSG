module

public import CFSG.ClassicalGroups.Alternating.Transvections
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import CFSG.LinearAlgebra.LinearGroups.UnitaryBasics
import CFSG.LinearAlgebra.LinearGroups.QuadraticActions

public section

namespace CFSG.ClassicalGroups.Alternating

open Module Submodule
open LinearMap (BilinForm)
open CFSG.LocalAnalysis.ComponentInitial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : BilinForm K V}

theorem isAlt_restrict (hB : B.IsAlt) (W : Submodule K V) : (B.restrict W).IsAlt :=
  fun x => hB x

private theorem gl_inv_apply_apply (g : LinearMap.GeneralLinearGroup K V) (x : V) :
    ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) ((g : V →ₗ[K] V) x) = x :=
  CFSG.LinearGroups.generalLinearGroup_inv_apply_apply g x

private theorem gl_apply_inv_apply (g : LinearMap.GeneralLinearGroup K V) (x : V) :
    (g : V →ₗ[K] V) (((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x) = x :=
  CFSG.LinearGroups.generalLinearGroup_apply_inv_apply g x

section Extension

variable {H W : Submodule K V}

private noncomputable def extendEquiv (h : IsCompl H W) (φ : W ≃ₗ[K] W) : V ≃ₗ[K] V :=
  (Submodule.prodEquivOfIsCompl H W h).symm ≪≫ₗ ((LinearEquiv.refl K H).prodCongr φ) ≪≫ₗ
    Submodule.prodEquivOfIsCompl H W h

private theorem extendEquiv_apply_left (h : IsCompl H W) (φ : W ≃ₗ[K] W) {x : V}
    (hx : x ∈ H) : extendEquiv h φ x = x := by
  rw [extendEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    show x = ((⟨x, hx⟩ : H) : V) from rfl, Submodule.prodEquivOfIsCompl_symm_apply_left,
    LinearEquiv.prodCongr_apply, map_zero, LinearEquiv.refl_apply,
    Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, add_zero]

private theorem extendEquiv_apply_right (h : IsCompl H W) (φ : W ≃ₗ[K] W) (w : W) :
    extendEquiv h φ w = φ w := by
  rw [extendEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    Submodule.prodEquivOfIsCompl_symm_apply_right, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, Submodule.coe_prodEquivOfIsCompl', ZeroMemClass.coe_zero, zero_add]

private noncomputable def extendGL (h : IsCompl H W) :
    LinearMap.GeneralLinearGroup K W →* LinearMap.GeneralLinearGroup K V where
  toFun φ := LinearMap.GeneralLinearGroup.ofLinearEquiv (extendEquiv h φ.toLinearEquiv)
  map_one' := Units.ext <| LinearMap.ext_on_codisjoint h.codisjoint
    (fun x hx => extendEquiv_apply_left h _ hx)
    (fun x hx => extendEquiv_apply_right h _ ⟨x, hx⟩)
  map_mul' φ ψ := Units.ext <| LinearMap.ext_on_codisjoint h.codisjoint
    (fun x hx => by
      change extendEquiv h _ x = extendEquiv h _ (extendEquiv h _ x)
      rw [extendEquiv_apply_left h _ hx, extendEquiv_apply_left h _ hx,
        extendEquiv_apply_left h _ hx])
    (fun x hx => by
      change extendEquiv h _ ((⟨x, hx⟩ : W) : V) =
        extendEquiv h _ (extendEquiv h _ ((⟨x, hx⟩ : W) : V))
      rw [extendEquiv_apply_right, extendEquiv_apply_right, extendEquiv_apply_right]
      rfl)

private theorem extendGL_apply_left (h : IsCompl H W) (φ : LinearMap.GeneralLinearGroup K W)
    {x : V} (hx : x ∈ H) : (extendGL h φ : V →ₗ[K] V) x = x :=
  extendEquiv_apply_left h _ hx

private theorem extendGL_apply_right (h : IsCompl H W) (φ : LinearMap.GeneralLinearGroup K W)
    (w : W) : (extendGL h φ : V →ₗ[K] V) w = (φ : W →ₗ[K] W) w :=
  extendEquiv_apply_right h _ w

private theorem extendGL_symplecticTransvection (hB : B.IsAlt) (h : IsCompl H W)
    (hHW : ∀ x ∈ H, ∀ y ∈ W, B x y = 0) (w : W) (c : K) :
    extendGL h (symplecticTransvection (B.restrict W) (isAlt_restrict hB W) w c) =
      symplecticTransvection B hB w c :=
  Units.ext <| LinearMap.ext_on_codisjoint h.codisjoint
    (fun x hx => by
      rw [extendGL_apply_left h _ hx, symplecticTransvection_apply, hHW x hx w w.2, mul_zero,
        zero_smul, add_zero])
    (fun x hx => by
      change (extendGL h _ : V →ₗ[K] V) ((⟨x, hx⟩ : W) : V) =
        (symplecticTransvection B hB w c : V →ₗ[K] V) x
      rw [extendGL_apply_right, symplecticTransvection_apply, symplecticTransvection_apply]
      rfl)

end Extension

theorem apply_mem_orthogonal_span_pair {g : LinearMap.GeneralLinearGroup K V}
    (hg : g ∈ bilinIsometryGroup B) {u v : V} (hgu : (g : V →ₗ[K] V) u = u)
    (hgv : (g : V →ₗ[K] V) v = v) {x : V} (hx : x ∈ B.orthogonal (span K {u, v})) :
    (g : V →ₗ[K] V) x ∈ B.orthogonal (span K {u, v}) := by
  rw [LinearMap.BilinForm.mem_orthogonal_span_pair_iff] at hx ⊢
  exact ⟨by rw [← hgu, hg u x, hx.1], by rw [← hgv, hg v x, hx.2]⟩

private def restrictGL {W : Submodule K V} (g : LinearMap.GeneralLinearGroup K V)
    (hg : ∀ x ∈ W, (g : V →ₗ[K] V) x ∈ W)
    (hg' : ∀ x ∈ W, ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x ∈ W) :
    LinearMap.GeneralLinearGroup K W where
  val := (g : V →ₗ[K] V).restrict hg
  inv := ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V).restrict hg'
  val_inv := LinearMap.ext fun x => Subtype.ext (gl_apply_inv_apply g x)
  inv_val := LinearMap.ext fun x => Subtype.ext (gl_inv_apply_apply g x)

private theorem mem_closure_of_fix_pair_of_le [FiniteDimensional K V] (hB : B.IsAlt)
    (hBn : B.Nondegenerate) {u v : V} (huv : B u v = 1)
    (hW : bilinIsometryGroup (B.restrict (B.orthogonal (span K {u, v}))) ≤
      Subgroup.closure {φ | ∃ w c, φ = symplecticTransvection
        (B.restrict (B.orthogonal (span K {u, v}))) (isAlt_restrict hB _) w c})
    {g : LinearMap.GeneralLinearGroup K V} (hg : g ∈ bilinIsometryGroup B)
    (hgu : (g : V →ₗ[K] V) u = u) (hgv : (g : V →ₗ[K] V) v = v) :
    g ∈ Subgroup.closure {t | ∃ w ∈ B.orthogonal (span K {u, v}), ∃ c : K,
      t = symplecticTransvection B hB w c} := by
  set W := B.orthogonal (span K {u, v})
  have hu : u ≠ 0 := by
    rintro rfl
    rw [map_zero, LinearMap.zero_apply] at huv
    exact zero_ne_one huv
  have hc : IsCompl (span K {u, v}) W :=
    ((alternating_hyperbolic_splitting hB hBn hu).2 v huv).2.2.2.1
  have hginv : g⁻¹ ∈ bilinIsometryGroup B := inv_mem hg
  have hginvu : ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) u = u := by
    conv_lhs => rw [← hgu]
    exact gl_inv_apply_apply g u
  have hginvv : ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) v = v := by
    conv_lhs => rw [← hgv]
    exact gl_inv_apply_apply g v
  let φ := restrictGL (W := W) g (fun x hx => apply_mem_orthogonal_span_pair hg hgu hgv hx)
    (fun x hx => apply_mem_orthogonal_span_pair hginv hginvu hginvv hx)
  have hφ : φ ∈ bilinIsometryGroup (B.restrict W) := fun x y => hg x y
  have hφg : extendGL hc φ = g := by
    refine Units.ext (LinearMap.ext_on_codisjoint hc.codisjoint (fun x hx => ?_)
      (fun x hx => ?_))
    · rw [extendGL_apply_left hc φ hx]
      obtain ⟨r, s, rfl⟩ := Submodule.mem_span_pair.mp hx
      rw [map_add, map_smul, map_smul, hgu, hgv]
    · change (extendGL hc φ : V →ₗ[K] V) ((⟨x, hx⟩ : W) : V) = (g : V →ₗ[K] V) x
      rw [extendGL_apply_right]
      rfl
  have hHW : ∀ x ∈ span K {u, v}, ∀ y ∈ W, B x y = 0 := fun x hx y hy => hy x hx
  rw [← hφg]
  have hmem := Subgroup.mem_map_of_mem (extendGL hc) (hW hφ)
  rw [MonoidHom.map_closure] at hmem
  refine Subgroup.closure_mono ?_ hmem
  rintro _ ⟨_, ⟨w, c, rfl⟩, rfl⟩
  exact ⟨w, w.2, c, extendGL_symplecticTransvection hB hc hHW w c⟩

omit [AddCommGroup V] [Module K V] in
private theorem le_closure_of_finrank_eq (n : ℕ) :
    ∀ (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V],
      finrank K V = n → ∀ (B : BilinForm K V) (hB : B.IsAlt), B.Nondegenerate →
        bilinIsometryGroup B ≤
          Subgroup.closure {g | ∃ (a : V) (c : K), g = symplecticTransvection B hB a c} := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ hn B hB hBn g hg
  rcases subsingleton_or_nontrivial V with hV | hV
  · have h1 : g = 1 := Units.ext (LinearMap.ext fun x => Subsingleton.elim _ _)
    rw [h1]
    exact one_mem _
  obtain ⟨u, hu⟩ := exists_ne (0 : V)
  obtain ⟨⟨v, huv⟩, hsplit⟩ := alternating_hyperbolic_splitting hB hBn hu
  obtain ⟨-, -, -, -, hWnd, hWdim⟩ := hsplit v huv
  have hlt : finrank K (B.orthogonal (span K {u, v})) < n := by
    have := Module.finrank_pos (R := K) (M := V)
    omega
  have hIH := ih _ hlt _ rfl _ (isAlt_restrict hB _) hWnd
  have hgu0 : (g : V →ₗ[K] V) u ≠ 0 := fun h0 => hu (by
    rw [← gl_inv_apply_apply g u, h0, map_zero])
  obtain ⟨h, hh, hhu⟩ := (alternating_transvection_vector_transitivity hB hBn).2 _ _ hgu0 hu
  have hhg : h * g ∈ bilinIsometryGroup B :=
    mul_mem (closure_symplecticTransvection_le_bilinIsometryGroup hB hh) hg
  have hhgu : ((h * g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) u = u := hhu
  have hx : B u (((h * g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) v) = 1 := by
    conv_lhs => rw [← hhgu]
    rw [hhg u v, huv]
  obtain ⟨l, -, -, hlu, hlv⟩ := alternating_fixed_vector_pair_adjustment hB hx huv
  set k := (l.map fun p => symplecticTransvection B hB p.1 p.2).prod
  have hk : k ∈ Subgroup.closure {g | ∃ (a : V) (c : K), g = symplecticTransvection B hB a c} :=
    list_prod_map_symplecticTransvection_mem_closure hB l
  have hkhg := mem_closure_of_fix_pair_of_le hB hBn huv hIH (g := k * (h * g))
    (mul_mem (closure_symplecticTransvection_le_bilinIsometryGroup hB hk) hhg)
    (by rw [Units.val_mul, Module.End.mul_apply, hhgu, hlu]) hlv
  have hg_eq : g = h⁻¹ * k⁻¹ * (k * (h * g)) := by group
  rw [hg_eq]
  refine mul_mem (mul_mem (inv_mem hh) (inv_mem hk)) (Subgroup.closure_mono ?_ hkhg)
  rintro _ ⟨w, -, c, rfl⟩
  exact ⟨w, c, rfl⟩

theorem alternating_transvection_generation [FiniteDimensional K V] (hB : B.IsAlt)
    (hBn : B.Nondegenerate) :
    bilinIsometryGroup B =
      Subgroup.closure {g | ∃ (a : V) (c : K), g = symplecticTransvection B hB a c} :=
  le_antisymm (le_closure_of_finrank_eq _ V rfl B hB hBn)
    (closure_symplecticTransvection_le_bilinIsometryGroup hB)

theorem mem_closure_symplecticTransvection_of_apply_eq_of_apply_eq [FiniteDimensional K V]
    (hB : B.IsAlt) (hBn : B.Nondegenerate) {u v : V} (huv : B u v = 1)
    {g : LinearMap.GeneralLinearGroup K V} (hg : g ∈ bilinIsometryGroup B)
    (hgu : (g : V →ₗ[K] V) u = u) (hgv : (g : V →ₗ[K] V) v = v) :
    g ∈ Subgroup.closure {t | ∃ w ∈ B.orthogonal (span K {u, v}), ∃ c : K,
      t = symplecticTransvection B hB w c} := by
  have hu : u ≠ 0 := by
    rintro rfl
    rw [map_zero, LinearMap.zero_apply] at huv
    exact zero_ne_one huv
  have hWnd := ((alternating_hyperbolic_splitting hB hBn hu).2 v huv).2.2.2.2.1
  exact mem_closure_of_fix_pair_of_le hB hBn huv
    (alternating_transvection_generation (isAlt_restrict hB _) hWnd).le hg hgu hgv

end CFSG.ClassicalGroups.Alternating
