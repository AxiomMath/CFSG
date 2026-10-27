module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryRankOne
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitUnipotentInvariant

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open Matrix SymplecticTorusWeyl CFSG.LieType.Universal.SpecialLinear CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal.Spin
open scoped Pointwise

variable {r : ℕ} {K : Type*} [Field K]

theorem eq_or_eq_swap_of_coordIdx_eq {a b : Fin r ⊕ Fin r} (h : coordIdx a = coordIdx b) :
    b = a ∨ b = a.swap := by
  rcases a with i | i <;> rcases b with j | j <;> simp_all

theorem coordIdx_ne_of_mem_signedPermGroup {σ : Equiv.Perm (Fin r ⊕ Fin r)}
    (hσ : σ ∈ signedPermGroup r) {a b : Fin r ⊕ Fin r} (h : coordIdx a ≠ coordIdx b) :
    coordIdx (σ a) ≠ coordIdx (σ b) := by
  intro he
  rcases eq_or_eq_swap_of_coordIdx_eq he with h' | h'
  · exact ne_of_coordIdx_ne h (σ.injective h').symm
  · rw [← hσ a] at h'
    exact ne_swap_of_coordIdx_ne (Ne.symm h) (σ.injective h')

section WtHom

theorem eps_eq_basisFun (i : Fin r) : eps r i = Pi.basisFun ℤ (Fin r) i := by
  rw [Pi.basisFun_apply]
  rfl

@[expose] noncomputable def wtLin (σ : Equiv.Perm (Fin r ⊕ Fin r)) :
    (Fin r → ℤ) →ₗ[ℤ] (Fin r → ℤ) :=
  (Pi.basisFun ℤ (Fin r)).constr ℤ fun i => coordWt (σ (Sum.inl i))

theorem wtLin_eps (σ : Equiv.Perm (Fin r ⊕ Fin r)) (i : Fin r) :
    wtLin σ (eps r i) = coordWt (σ (Sum.inl i)) := by
  rw [eps_eq_basisFun, wtLin, Module.Basis.constr_basis]

theorem linearMap_ext_eps {f g : (Fin r → ℤ) →ₗ[ℤ] (Fin r → ℤ)}
    (h : ∀ i, f (eps r i) = g (eps r i)) : f = g :=
  (Pi.basisFun ℤ (Fin r)).ext fun i => by rw [← eps_eq_basisFun]; exact h i

theorem wtLin_coordWt {σ : Equiv.Perm (Fin r ⊕ Fin r)} (hσ : σ ∈ signedPermGroup r)
    (c : Fin r ⊕ Fin r) : wtLin σ (coordWt c) = coordWt (σ c) := by
  rcases c with i | i
  · exact wtLin_eps σ i
  · rw [coordWt_inr, map_neg, wtLin_eps, ← coordWt_swap, ← hσ]
    rfl

theorem wtLin_one : wtLin (1 : Equiv.Perm (Fin r ⊕ Fin r)) = LinearMap.id :=
  linearMap_ext_eps fun i => by rw [wtLin_eps]; rfl

theorem wtLin_mul {σ : Equiv.Perm (Fin r ⊕ Fin r)} (hσ : σ ∈ signedPermGroup r)
    (τ : Equiv.Perm (Fin r ⊕ Fin r)) : wtLin (σ * τ) = wtLin σ ∘ₗ wtLin τ :=
  linearMap_ext_eps fun i => by
    rw [wtLin_eps, LinearMap.comp_apply, wtLin_eps, wtLin_coordWt hσ]
    rfl

@[expose] noncomputable def wtHom : signedPermGroup r →* ((Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) where
  toFun σ := LinearEquiv.ofLinearMap (wtLin (σ : Equiv.Perm (Fin r ⊕ Fin r)))
    (wtLin ((σ⁻¹ : signedPermGroup r) : Equiv.Perm (Fin r ⊕ Fin r)))
    (by rw [← wtLin_mul σ.2, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, wtLin_one])
    (by rw [← wtLin_mul (σ⁻¹).2, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
      wtLin_one])
  map_one' := LinearEquiv.ext fun x => by
    rw [LinearEquiv.coe_ofLinearMap, Subgroup.coe_one, wtLin_one]
    rfl
  map_mul' σ τ := LinearEquiv.ext fun x => by
    rw [LinearEquiv.coe_ofLinearMap, Subgroup.coe_mul, wtLin_mul σ.2, LinearEquiv.mul_apply,
      LinearEquiv.coe_ofLinearMap, LinearEquiv.coe_ofLinearMap]
    rfl

theorem wtHom_coordWt (σ : signedPermGroup r) (c : Fin r ⊕ Fin r) :
    wtHom σ (coordWt c) = coordWt ((σ : Equiv.Perm (Fin r ⊕ Fin r)) c) :=
  wtLin_coordWt σ.2 c

theorem wtHom_injective : Function.Injective (wtHom (r := r)) := by
  intro σ τ h
  refine Subtype.ext (Equiv.ext fun c => coordWt_injective ?_)
  rw [← wtHom_coordWt, ← wtHom_coordWt, h]

end WtHom

section SignedPerm

theorem eq_of_signedPerm_eq {σ τ : Equiv.Perm (Fin r ⊕ Fin r)} {μ ν : Fin r ⊕ Fin r → K}
    (hμ : ∀ c, μ c ≠ 0) (h : signedPerm σ μ = signedPerm τ ν) : σ = τ := by
  refine Equiv.ext fun c => ?_
  have he := congrFun (congrFun h (σ c)) c
  rw [signedPerm_apply, signedPerm_apply, ite_eq_left rfl] at he
  by_contra hne
  rw [ite_eq_right hne] at he
  exact hμ c he

theorem signedPerm_mulVec_single (σ : Equiv.Perm (Fin r ⊕ Fin r)) (μ : Fin r ⊕ Fin r → K)
    (c : Fin r ⊕ Fin r) : signedPerm σ μ *ᵥ Pi.single c 1 = μ c • Pi.single (σ c) 1 := by
  funext x
  rw [mulVec, dotProduct, Finset.sum_eq_single c
    (fun y _ hy => by rw [Pi.single_eq_of_ne hy, mul_zero]) (by simp), Pi.single_eq_same,
    mul_one, signedPerm_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp

theorem units_swap_mul_self {μ : Fin r ⊕ Fin r → Kˣ} (hμ : ∀ c, μ c.swap = (μ c)⁻¹)
    (c : Fin r ⊕ Fin r) : (μ c.swap : K) * μ c = 1 := by
  rw [hμ, Units.inv_mul]

end SignedPerm

section MonoAut

variable (r K) in
@[expose] def monoAut : Subgroup ((Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) where
  carrier := {g | ∃ σ ∈ signedPermGroup r, ∃ μ : Fin r ⊕ Fin r → Kˣ,
    (∀ c, μ c.swap = (μ c)⁻¹) ∧ autMat g = signedPerm σ fun c => (μ c : K)}
  mul_mem' := by
    rintro g h ⟨σ, hσ, μ, hμ, hg⟩ ⟨τ, hτ, ν, hν, hh⟩
    refine ⟨σ * τ, mul_mem hσ hτ, fun s => μ (τ s) * ν s, fun c => ?_, ?_⟩
    · change μ (τ c.swap) * ν c.swap = (μ (τ c) * ν c)⁻¹
      rw [hτ c, hμ, hν, mul_inv]
    · rw [map_mul, hg, hh, signedPerm_mul_signedPerm]
      simp only [Units.val_mul]
  one_mem' := ⟨1, one_mem _, 1, fun c => by simp, by
    rw [map_one, signedPerm_one]
    simp⟩
  inv_mem' := by
    rintro g ⟨σ, hσ, μ, hμ, hg⟩
    refine ⟨σ⁻¹, inv_mem hσ, fun s => (μ (σ⁻¹ s))⁻¹, fun c => ?_, ?_⟩
    · change (μ (σ⁻¹ c.swap))⁻¹ = ((μ (σ⁻¹ c))⁻¹)⁻¹
      rw [(inv_mem hσ) c, hμ]
    · have h1 : signedPerm σ (fun c => (μ c : K)) *
          signedPerm σ⁻¹ (fun s => (((μ (σ⁻¹ s))⁻¹ : Kˣ) : K)) = 1 := by
        rw [signedPerm_mul_signedPerm, mul_inv_cancel, signedPerm_one]
        simp
      calc autMat g⁻¹ = autMat g⁻¹ * (autMat g *
              signedPerm σ⁻¹ (fun s => (((μ (σ⁻¹ s))⁻¹ : Kˣ) : K))) := by rw [hg, h1, mul_one]
        _ = signedPerm σ⁻¹ (fun s => (((μ (σ⁻¹ s))⁻¹ : Kˣ) : K)) := by
          rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

theorem torusElt_mem_monoAut (d : Fin r → Kˣ) : torusElt r K d ∈ monoAut r K := by
  refine ⟨1, one_mem _, Sum.elim d d⁻¹, fun c => ?_, ?_⟩
  · rcases c with i | i <;> simp
  · rw [autMat_torusElt, signedPerm_one]

@[expose] noncomputable def monoPermFun (g : monoAut r K) : Equiv.Perm (Fin r ⊕ Fin r) :=
  g.2.choose

theorem monoPermFun_mem (g : monoAut r K) : monoPermFun g ∈ signedPermGroup r :=
  g.2.choose_spec.1

theorem exists_autMat_eq_monoPermFun (g : monoAut r K) : ∃ μ : Fin r ⊕ Fin r → Kˣ,
    (∀ c, μ c.swap = (μ c)⁻¹) ∧
      autMat (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] _) = signedPerm (monoPermFun g) fun c => (μ c : K) :=
  g.2.choose_spec.2

theorem monoPermFun_eq {g : monoAut r K} {σ : Equiv.Perm (Fin r ⊕ Fin r)}
    {μ : Fin r ⊕ Fin r → K}
    (h : autMat (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] _) = signedPerm σ μ) : monoPermFun g = σ := by
  obtain ⟨ν, -, hν⟩ := exists_autMat_eq_monoPermFun g
  exact eq_of_signedPerm_eq (fun c => (ν c).ne_zero) (hν.symm.trans h)

variable (r K) in
@[expose] noncomputable def monoPerm : monoAut r K →* signedPermGroup r where
  toFun g := ⟨monoPermFun g, monoPermFun_mem g⟩
  map_one' := Subtype.ext (monoPermFun_eq (σ := 1) (μ := fun _ => 1) (by
    rw [OneMemClass.coe_one, map_one, signedPerm_one, diagonal_one]))
  map_mul' g h := by
    obtain ⟨μ, -, hμ⟩ := exists_autMat_eq_monoPermFun g
    obtain ⟨ν, -, hν⟩ := exists_autMat_eq_monoPermFun h
    refine Subtype.ext (monoPermFun_eq (σ := monoPermFun g * monoPermFun h)
      (μ := fun s => (μ (monoPermFun h s) : K) * ν s) ?_)
    rw [Subgroup.coe_mul, map_mul, hμ, hν, signedPerm_mul_signedPerm]

theorem coe_monoPerm (g : monoAut r K) :
    ((monoPerm r K g : signedPermGroup r) : Equiv.Perm (Fin r ⊕ Fin r)) = monoPermFun g :=
  rfl

variable (r K) in
@[expose] noncomputable def nuMono : monoAut r K →* ((Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)) :=
  wtHom.comp (monoPerm r K)

theorem nuMono_coordWt (g : monoAut r K) (c : Fin r ⊕ Fin r) :
    nuMono r K g (coordWt c) = coordWt (monoPermFun g c) :=
  wtHom_coordWt _ c

theorem apply_single_of_autMat {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    {σ : Equiv.Perm (Fin r ⊕ Fin r)} {μ : Fin r ⊕ Fin r → K}
    (hg : autMat g = signedPerm σ μ) (c : Fin r ⊕ Fin r) :
    g (Pi.single c 1) = μ c • Pi.single (σ c) 1 := by
  rw [apply_eq_autMat_mulVec, hg, signedPerm_mulVec_single]

end MonoAut

section Conj

variable {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)} {σ : Equiv.Perm (Fin r ⊕ Fin r)}
  {μ : Fin r ⊕ Fin r → Kˣ}

theorem signedPerm_mul_rpMat (hσ : σ ∈ signedPermGroup r) (hμ : ∀ c, μ c.swap = (μ c)⁻¹)
    (a b : Fin r ⊕ Fin r) :
    signedPerm σ (fun c => (μ c : K)) * rpMat K a b =
      ((μ a : K) * (μ b : K)⁻¹) • (rpMat K (σ a) (σ b) * signedPerm σ fun c => (μ c : K)) := by
  have hsa : σ.symm (σ a).swap = a.swap := by
    rw [Equiv.symm_apply_eq, hσ a]
  rw [rpMat, rpMat, mul_sub, sub_mul, signedPerm_mul_single, signedPerm_mul_single,
    single_mul_signedPerm, single_mul_signedPerm, Equiv.symm_apply_apply, hsa, hσ b, smul_sub,
    smul_single, smul_single, smul_eq_mul, smul_eq_mul, hμ a, hμ b, mul_one, mul_one, one_mul,
    one_mul]
  congr 2
  · field_simp
  · rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val]
    field_simp

theorem mul_rpElt_eq (hσ : σ ∈ signedPermGroup r) (hμ : ∀ c, μ c.swap = (μ c)⁻¹)
    (hg : autMat g = signedPerm σ fun c => (μ c : K)) {a b : Fin r ⊕ Fin r}
    (hab : coordIdx a ≠ coordIdx b) (t : K) :
    g * rpElt a b t = rpElt (σ a) (σ b) ((μ a : K) * (μ b : K)⁻¹ * t) * g := by
  apply autMat_injective
  rw [map_mul, map_mul, hg, autMat_rpElt hab,
    autMat_rpElt (coordIdx_ne_of_mem_signedPermGroup hσ hab), mul_add, mul_one, add_mul,
    one_mul, mul_smul_comm, signedPerm_mul_rpMat hσ hμ, smul_smul, smul_mul_assoc, mul_comm t]

theorem map_conj_rootSubgroup_of_autMat (hσ : σ ∈ signedPermGroup r)
    (hμ : ∀ c, μ c.swap = (μ c)⁻¹) (hg : autMat g = signedPerm σ fun c => (μ c : K))
    {α : Fin r → ℤ} (hα : α ∈ roots r) {β : Fin r → ℤ}
    (hβ : ∀ a b : Fin r ⊕ Fin r, coordWt a - coordWt b = α →
      coordWt (σ a) - coordWt (σ b) = β) :
    (rootSubgroup r K α).map (MulAut.conj g).toMonoidHom = rootSubgroup r K β := by
  obtain ⟨a, b, hab, hw, h1, -⟩ := exists_rootElt_eq_rpElt (K := K) hα
  have hab' := coordIdx_ne_of_mem_signedPermGroup hσ hab
  obtain ⟨ε, hε, h2, -⟩ := exists_sign_rootElt_eq_rpElt (K := K) hab'
  rw [hβ a b hw] at h2
  have hsq : (ε : K) * ε = 1 := by rcases hε with rfl | rfl <;> simp
  have hconj : ∀ t : K, MulAut.conj g (rootElt r K α t) =
      rootElt r K β ((ε : K) * ((μ a : K) * (μ b : K)⁻¹ * t)) := fun t => by
    rw [h2, ← mul_assoc, hsq, one_mul, MulAut.conj_apply, h1, mul_rpElt_eq hσ hμ hg hab,
      mul_inv_cancel_right]
  ext x
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨_, (hconj t).symm⟩
  · rintro ⟨s, rfl⟩
    refine ⟨rootElt r K α ((μ b : K) * (μ a : K)⁻¹ * ((ε : K) * s)), ⟨_, rfl⟩, ?_⟩
    change MulAut.conj g _ = _
    rw [hconj]
    congr 1
    field_simp
    linear_combination s * hsq

theorem map_conj_rootSubgroup (g : monoAut r K) {α : Fin r → ℤ} (hα : α ∈ roots r) :
    (rootSubgroup r K α).map (MulAut.conj (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] _)).toMonoidHom =
      rootSubgroup r K (nuMono r K g α) := by
  obtain ⟨μ, hμ, hg⟩ := exists_autMat_eq_monoPermFun g
  refine map_conj_rootSubgroup_of_autMat (monoPermFun_mem g) hμ hg hα fun a b hw => ?_
  rw [← hw, map_sub, nuMono_coordWt, nuMono_coordWt]

end Conj

section CoordSpan

variable (K) in
@[expose] def coordSpan (S : Set (Fin r ⊕ Fin r)) : Submodule K (Fin r ⊕ Fin r → K) :=
  Submodule.span K ((fun c => (Pi.single c 1 : Fin r ⊕ Fin r → K)) '' S)

theorem apply_eq_zero_of_mem_coordSpan {S : Set (Fin r ⊕ Fin r)} {v : Fin r ⊕ Fin r → K}
    (hv : v ∈ coordSpan K S) {x : Fin r ⊕ Fin r} (hx : x ∉ S) : v x = 0 := by
  have hle : coordSpan K S ≤ LinearMap.ker (LinearMap.proj (R := K) (φ := fun _ => K) x) := by
    rw [coordSpan, Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.proj_apply]
    change (Pi.single c 1 : Fin r ⊕ Fin r → K) x = 0
    rw [Pi.single_apply, ite_eq_right]
    rintro rfl
    exact hx hc
  have := hle hv
  rwa [LinearMap.mem_ker, LinearMap.proj_apply] at this

theorem single_mem_coordSpan_iff {S : Set (Fin r ⊕ Fin r)} {c : Fin r ⊕ Fin r} :
    (Pi.single c 1 : Fin r ⊕ Fin r → K) ∈ coordSpan K S ↔ c ∈ S := by
  refine ⟨fun h => ?_, fun h => Submodule.subset_span ⟨c, h, rfl⟩⟩
  by_contra hc
  have := apply_eq_zero_of_mem_coordSpan h hc
  simp at this

theorem coordSpan_injective : Function.Injective (coordSpan (r := r) K) := by
  intro S T h
  ext c
  rw [← single_mem_coordSpan_iff (K := K), h, single_mem_coordSpan_iff]

theorem smul_coordSpan {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    {σ : Equiv.Perm (Fin r ⊕ Fin r)} {μ : Fin r ⊕ Fin r → K} (hμ : ∀ c, μ c ≠ 0)
    (hg : autMat g = signedPerm σ μ) (S : Set (Fin r ⊕ Fin r)) :
    g • coordSpan K S = coordSpan K (σ '' S) := by
  rw [Submodule.pointwise_smul_def, coordSpan, Submodule.map_span, coordSpan]
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    change g (Pi.single c 1) ∈ _
    rw [apply_single_of_autMat hg]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ c, ⟨c, hc, rfl⟩, rfl⟩)
  · rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    have h1 : (Pi.single (σ c) 1 : Fin r ⊕ Fin r → K) = (μ c)⁻¹ • g (Pi.single c 1) := by
      rw [apply_single_of_autMat hg, smul_smul, inv_mul_cancel₀ (hμ c), one_smul]
    change (Pi.single (σ c) 1 : Fin r ⊕ Fin r → K) ∈ _
    rw [h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨c, hc, rfl⟩, rfl⟩)

theorem smul_coordSpan_eq_iff {g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)}
    {σ : Equiv.Perm (Fin r ⊕ Fin r)} {μ : Fin r ⊕ Fin r → K} (hμ : ∀ c, μ c ≠ 0)
    (hg : autMat g = signedPerm σ μ) (S : Set (Fin r ⊕ Fin r)) :
    g • coordSpan K S = coordSpan K S ↔ σ '' S = S := by
  rw [smul_coordSpan hμ hg]
  exact coordSpan_injective.eq_iff

theorem flag_eq_coordSpan (i : ℕ) :
    flag r K i = coordSpan K (Sum.inl '' {j : Fin r | (j : ℕ) < i}) := by
  rw [flag, coordSpan, Set.image_image]

theorem Xstar_eq_coordSpan (hr : 0 < r) :
    Xstar r K hr = coordSpan K (Sum.inl '' {j : Fin r | (j : ℕ) < r - 1} ∪
      {Sum.inr ⟨r - 1, by omega⟩}) := by
  rw [Xstar, coordSpan, Set.image_union, Submodule.span_union, ← coordSpan, ← flag_eq_coordSpan,
    Set.image_singleton]

end CoordSpan

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
