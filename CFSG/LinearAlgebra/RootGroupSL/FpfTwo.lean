module

public import CFSG.LinearAlgebra.RootGroupSL.FpfCommon
public import CFSG.LinearAlgebra.RootGroupSL.FpfArith

public section

namespace CFSG.LinearAlgebra.RootGroupSL

variable {k E X : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup X] [Module k X]

private lemma eq_mulLeft_of_commute_mulLeft (ψ : E →ₗ[k] E) {ν : E}
    (hν : ∀ t, ν * ψ t = ψ (ν * t))
    (hgen : Algebra.adjoin k ({ν} : Set E) = ⊤) :
    ψ = LinearMap.mulLeft k (ψ 1) := by
  let T : Subalgebra k E :=
    { carrier := {x | ∀ y, x * ψ y = ψ (x * y)}
      mul_mem' := by
        rintro x y hx hy z
        rw [mul_assoc, hy z, hx (y * z), mul_assoc]
      add_mem' := by
        rintro x y hx hy z
        rw [show (x + y) * ψ z = x * ψ z + y * ψ z by ring,
          show (x + y) * z = x * z + y * z by ring, map_add, hx z, hy z]
      algebraMap_mem' := by
        intro r y
        simp only [Algebra.algebraMap_eq_smul_one, Algebra.smul_mul_assoc, one_mul,
          map_smul] }
  have hle : Algebra.adjoin k ({ν} : Set E) ≤ T :=
    Algebra.adjoin_le (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hν)
  have hT : T = ⊤ := by
    apply le_antisymm le_top
    rw [← hgen]
    exact hle
  ext t
  have htT : t ∈ T := by rw [hT]; trivial
  have h := htT 1
  rw [mul_one] at h
  rw [LinearMap.mulLeft_apply, mul_comm]
  exact h.symm

private lemma mulLeftEquiv_toLinearMap (s : Eˣ) :
    (mulLeftEquiv k s).toLinearMap = LinearMap.mulLeft k (s : E) := rfl

private lemma mulLeftEquiv_symm_apply (s : Eˣ) (x : E) :
    (mulLeftEquiv k s).symm x = ((s⁻¹ : Eˣ) : E) * x := by
  apply (mulLeftEquiv k s).injective
  rw [LinearEquiv.apply_symm_apply, mulLeftEquiv_apply]
  rw [← mul_assoc, Units.mul_inv, one_mul]

private lemma mulLeftEquiv_symm_toLinearMap (s : Eˣ) :
    (mulLeftEquiv k s).symm.toLinearMap = LinearMap.mulLeft k ((s⁻¹ : Eˣ) : E) := by
  ext x
  change (mulLeftEquiv k s).symm x = ((s⁻¹ : Eˣ) : E) * x
  rw [mulLeftEquiv_symm_apply]

private lemma mulLeftEquiv_mul (s t : Eˣ) :
    mulLeftEquiv k s * mulLeftEquiv k t = mulLeftEquiv k (s * t) := by
  ext x
  rw [LinearEquiv.mul_apply, mulLeftEquiv_apply, mulLeftEquiv_apply, mulLeftEquiv_apply,
    Units.val_mul, mul_assoc]

private lemma mulLeftEquiv_one : mulLeftEquiv k (1 : Eˣ) = 1 := by
  ext x
  rw [mulLeftEquiv_apply]
  simp

private lemma mulLeftEquiv_pow (s : Eˣ) (n : ℕ) :
    (mulLeftEquiv k s) ^ n = mulLeftEquiv k (s ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, mulLeftEquiv_one]
  | succ n ih => rw [pow_succ, ih, mulLeftEquiv_mul, pow_succ]

private lemma det_mulLeftEquiv (s : Eˣ) :
    ((LinearEquiv.det (mulLeftEquiv k s) : kˣ) : k) = Algebra.norm k (s : E) :=
  det_mulLeft_eq_norm (mulLeftEquiv k s) (s : E) (mulLeftEquiv_toLinearMap s)

private lemma det_mulLeftEquiv_eq_one (s : Eˣ) (hs : Algebra.norm k (s : E) = 1) :
    LinearEquiv.det (mulLeftEquiv k s) = 1 := by
  apply Units.ext
  rw [det_mulLeftEquiv, hs]
  simp

variable [Finite k] [Finite E] [Module.Finite k X] [CharP k 2]

theorem exists_fpf_of_two_le_finrank (hd : 2 ≤ Module.finrank k E) :
    ∃ h ∈ Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))),
      Odd (orderOf h) ∧
      Subgroup.centralizer ({h} : Set (SpecialLinearGroup k (DSpace E X))) ⊓ QK k E X =
        rootSL k E X := by
  classical
  obtain ⟨ν, hnorm, hgen⟩ := exists_norm_eq_one_adjoin_eq_top (k := k) (E := E) hd
  have hν0 : ν ≠ 0 := by
    intro h0
    rw [h0, Algebra.norm_zero] at hnorm
    exact one_ne_zero hnorm.symm
  have hνne : ν ≠ 1 := by
    intro hν1
    have hbot : IntermediateField.adjoin k ({ν} : Set E) = ⊥ := by
      rw [hν1, IntermediateField.adjoin_one]
    rw [hgen] at hbot
    have hfr : Module.finrank k E = 1 := by
      have h := congrArg (fun L : IntermediateField k E => Module.finrank k L) hbot
      rwa [IntermediateField.finrank_top', IntermediateField.finrank_bot] at h
    omega
  let ν' : Eˣ := Units.mk0 ν hν0
  have hν'val : (ν' : E) = ν := Units.val_mk0 hν0
  have hν'Ene : (ν' : E) ≠ 1 := by rw [hν'val]; exact hνne
  have hnorm' : Algebra.norm k (ν' : E) = 1 := by rw [hν'val]; exact hnorm
  have hadj : Algebra.adjoin k ({ν} : Set E) = ⊤ := by
    rw [← IntermediateField.adjoin_toSubalgebra (F := k) ({ν} : Set E), hgen]
    simp
  have hdet : LinearEquiv.det (mulLeftEquiv k ν') * LinearEquiv.det (1 : X ≃ₗ[k] X) *
      LinearEquiv.det (mulLeftEquiv k ν') = 1 := by
    rw [det_mulLeftEquiv_eq_one ν' hnorm', map_one]
    simp
  let h : SpecialLinearGroup k (DSpace E X) :=
    blockSL (mulLeftEquiv k ν') 1 (mulLeftEquiv k ν') hdet
  have hconjmaps : ∀ t : E, (mulLeftEquiv k ν').toLinearMap ∘ₗ LinearMap.mulLeft k t ∘ₗ
      (mulLeftEquiv k ν').symm.toLinearMap = LinearMap.mulLeft k t := by
    have hν'0 : (ν' : E) ≠ 0 := by rw [hν'val]; exact hν0
    intro t
    ext y
    rw [LinearMap.comp_apply, LinearMap.comp_apply, mulLeftEquiv_toLinearMap,
      mulLeftEquiv_symm_toLinearMap, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply,
      LinearMap.mulLeft_apply]
    simp only [LinearMap.mulLeft_apply]
    rw [Units.val_inv_eq_inv_val]
    field_simp
  have hnorm_mem : h ∈
      Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))) := by
    change blockSL (mulLeftEquiv k ν') 1 (mulLeftEquiv k ν') hdet ∈ _
    rw [blockSL_mem_normalizer_iff]
    intro t
    exact ⟨t, hconjmaps t⟩
  have hodd : Odd (orderOf h) := by
    have hpow : h ^ orderOf ν' = 1 := by
      apply SpecialLinearGroup.toLinearEquiv_injective
      rw [map_pow, map_one]
      change (blockDiag (mulLeftEquiv k ν') 1 (mulLeftEquiv k ν')) ^ orderOf ν' = 1
      rw [blockDiag_pow, mulLeftEquiv_pow, pow_orderOf_eq_one, mulLeftEquiv_one, one_pow]
      rw [blockDiag_one]
    have hdvd : orderOf h ∣ orderOf ν' := orderOf_dvd_iff_pow_eq_one.mpr hpow
    have hEodd : Odd (Nat.card Eˣ) := by
      haveI : Fintype E := Fintype.ofFinite E
      haveI : CharP E 2 := charP_of_injective_algebraMap' k 2
      rw [Nat.card_units]
      obtain ⟨n, _, hcard⟩ := FiniteField.card E 2
      rw [Nat.card_eq_fintype_card, hcard]
      exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by norm_num))
        (Even.pow_of_ne_zero even_two (Nat.pos_iff_ne_zero.mp n.pos)) odd_one
    exact Odd.of_dvd_nat hEodd (hdvd.trans (orderOf_dvd_natCard ν'))
  refine ⟨h, hnorm_mem, hodd, ?_⟩
  apply le_antisymm
  · intro g' hg'
    rw [Subgroup.mem_inf] at hg'
    obtain ⟨hg'cent, hg'QK⟩ := hg'
    obtain ⟨φ, χ, ψ, hg'eq⟩ := exists_unipElt_of_mem_unipRad (mem_QK_iff.mp hg'QK)
    have hfix_sl : h * g' * h⁻¹ = g' := by
      rw [Subgroup.mem_centralizer_iff] at hg'cent
      have hcomm := hg'cent h (by simp)
      calc h * g' * h⁻¹ = (h * g') * h⁻¹ := by group
        _ = (g' * h) * h⁻¹ := by rw [hcomm]
        _ = g' := by group
    have hfix : blockDiag (mulLeftEquiv k ν') 1 (mulLeftEquiv k ν') * unipElt φ χ ψ *
        (blockDiag (mulLeftEquiv k ν') 1 (mulLeftEquiv k ν'))⁻¹ = unipElt φ χ ψ :=
      blockDiag_conj_of_centralizer hfix_sl rfl hg'eq
    obtain ⟨hφ, hχ, hψ⟩ := (blockDiag_conj_unipElt_eq_iff _ _ _ φ χ ψ).mp hfix
    have hφ' : ∀ x : X, (ν' : E) * φ x = φ x := by
      intro x
      have h := congrArg (fun f : X →ₗ[k] E => f x) hφ
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
      simpa [mulLeftEquiv_toLinearMap, LinearMap.mulLeft_apply] using h
    have hχ' : ∀ t : E, χ ((ν' : E) * t) = χ t := by
      intro t
      have h := congrArg (fun f : E →ₗ[k] X => f t) hχ
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
      simpa [mulLeftEquiv_toLinearMap, LinearMap.mulLeft_apply] using h.symm
    have hψ' : ∀ t : E, (ν' : E) * ψ t = ψ ((ν' : E) * t) := by
      intro t
      have h := congrArg (fun f : E →ₗ[k] E => f t) hψ
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
      simpa [mulLeftEquiv_toLinearMap, LinearMap.mulLeft_apply] using h
    have hψ'' : ∀ t : E, ν * ψ t = ψ (ν * t) := by
      intro t
      rw [← hν'val]
      exact hψ' t
    have hφ0 : φ = 0 := by
      ext x
      have h := hφ' x
      have h2 : ((ν' : E) - 1) * φ x = 0 := by rw [sub_mul, one_mul, h, sub_self]
      exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hν'Ene)
    have hχ0 : χ = 0 := by
      ext t
      have hne : (ν' : E) - 1 ≠ 0 := sub_ne_zero.mpr hν'Ene
      have hsub : ∀ u : E, χ (((ν' : E) - 1) * u) = 0 := by
        intro u
        rw [sub_mul, one_mul, map_sub, hχ' u, sub_self]
      conv_lhs => rw [show t = ((ν' : E) - 1) * (((ν' : E) - 1)⁻¹ * t) from by
        rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]]
      exact hsub (((ν' : E) - 1)⁻¹ * t)
    have hψ0 : ψ = LinearMap.mulLeft k (ψ 1) :=
      eq_mulLeft_of_commute_mulLeft ψ hψ'' hadj
    rw [mem_rootSL_iff]
    refine ⟨ψ 1, ?_⟩
    rw [hg'eq, hφ0, hχ0, hψ0]
    rw [LinearMap.mulLeft_apply, mul_one]
    exact (shearE_eq_unipElt (X := X) (LinearMap.mulLeft k (ψ 1))).symm
  · intro r hr
    rw [Subgroup.mem_inf]
    refine ⟨?_, rootSL_le_QK hr⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    obtain ⟨t, ht⟩ := mem_rootSL_iff.mp hr
    have hr_eq : r = rootElt k X t := by
      apply Subtype.ext
      exact ht
    rw [hr_eq]
    have hconj := blockSL_conj_rootElt (mulLeftEquiv k ν') 1 (mulLeftEquiv k ν') hdet t
      (hconjmaps t)
    have hcomm : h * rootElt k X t = rootElt k X t * h := by
      have hconj' : h * rootElt k X t * h⁻¹ = rootElt k X t := by
        change blockSL (mulLeftEquiv k ν') 1 (mulLeftEquiv k ν') hdet * rootElt k X t *
          (blockSL (mulLeftEquiv k ν') 1 (mulLeftEquiv k ν') hdet)⁻¹ = rootElt k X t
        exact hconj
      calc h * rootElt k X t = h * rootElt k X t * h⁻¹ * h := by group
        _ = rootElt k X t * h := by rw [hconj']
    exact hcomm

end CFSG.LinearAlgebra.RootGroupSL
