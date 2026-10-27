module

public import CFSG.LinearAlgebra.RootGroupSL.FpfCommon
public import CFSG.LinearAlgebra.RootGroupSL.FpfArith

public section

namespace CFSG.LinearAlgebra.RootGroupSL

variable {k E X : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup X] [Module k X]

private def scalarEquiv (s : kˣ) : E ≃ₗ[k] E where
  toFun x := (s : k) • x
  invFun x := ((s⁻¹ : kˣ) : k) • x
  map_add' x y := by rw [smul_add]
  map_smul' c x := by
    simp only [RingHom.id_apply]
    rw [smul_comm c (s : k) x]
  left_inv x := by
    change ((s⁻¹ : kˣ) : k) • ((s : k) • x) = x
    rw [smul_smul, Units.inv_mul, one_smul]
  right_inv x := by
    change (s : k) • (((s⁻¹ : kˣ) : k) • x) = x
    rw [smul_smul, Units.mul_inv, one_smul]

private lemma scalarEquiv_toLinearMap (s : kˣ) :
    (scalarEquiv (E := E) s).toLinearMap = Algebra.lsmul k k E (s : k) := by
  ext x
  rw [Algebra.lsmul_apply]
  rfl

private lemma scalarEquiv_symm_toLinearMap (s : kˣ) :
    (scalarEquiv (E := E) s).symm.toLinearMap = Algebra.lsmul k k E ((s⁻¹ : kˣ) : k) := by
  ext x
  rw [Algebra.lsmul_apply]
  rfl

private lemma scalarEquiv_mul (s t : kˣ) :
    scalarEquiv (E := E) s * scalarEquiv (E := E) t = scalarEquiv (E := E) (s * t) := by
  ext x
  change (s : k) • ((t : k) • x) = ((s * t : kˣ) : k) • x
  rw [smul_smul, Units.val_mul]

private lemma scalarEquiv_one : scalarEquiv (E := E) (1 : kˣ) = 1 := by
  ext x
  simp [scalarEquiv]

private lemma scalarEquiv_pow (s : kˣ) (n : ℕ) :
    (scalarEquiv (E := E) s) ^ n = scalarEquiv (E := E) (s ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, scalarEquiv_one]
  | succ n ih => rw [pow_succ, ih, scalarEquiv_mul, pow_succ]

private lemma det_scalarEquiv (hd : Module.finrank k E = 1) (s : kˣ) :
    LinearEquiv.det (scalarEquiv (E := E) s) = s := by
  apply Units.ext
  rw [LinearEquiv.coe_det]
  rw [show (scalarEquiv (E := E) s : E →ₗ[k] E) = Algebra.lsmul k k E (s : k) from
    scalarEquiv_toLinearMap s]
  rw [Algebra.det_lsmul, hd, pow_one]

private lemma eq_mulLeft_of_finrank_eq_one (hd : Module.finrank k E = 1) (ψ : E →ₗ[k] E) :
    ψ = LinearMap.mulLeft k (ψ 1) := by
  ext t
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero' (K := k) (V := E) (1 : E) one_ne_zero).mp hd t
  rw [← hc, map_smul, LinearMap.mulLeft_apply, Algebra.mul_smul_comm, mul_one]

variable [Finite k] [Finite E] [Module.Finite k X] [CharP k 2]

theorem exists_fpf_of_finrank_eq_one (hd : Module.finrank k E = 1) (hk : 4 ≤ Nat.card k)
    (hX : 2 ≤ Module.finrank k X) :
    ∃ h ∈ Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))),
      Odd (orderOf h) ∧
      Subgroup.centralizer ({h} : Set (SpecialLinearGroup k (DSpace E X))) ⊓ QK k E X =
        rootSL k E X := by
  classical
  haveI : Fintype k := Fintype.ofFinite k
  have hkf : 1 < Fintype.card kˣ := by
    have h : 1 < Nat.card kˣ := by
      rw [Nat.card_units]
      omega
    rwa [Nat.card_eq_fintype_card] at h
  haveI : Nontrivial kˣ := Fintype.one_lt_card_iff_nontrivial.mp hkf
  obtain ⟨s, hs⟩ := exists_ne (1 : kˣ)
  have hkodd : Odd (Nat.card kˣ) := by
    rw [Nat.card_units]
    obtain ⟨n, _, hcard⟩ := FiniteField.card k 2
    rw [Nat.card_eq_fintype_card, hcard]
    exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by norm_num))
      (Even.pow_of_ne_zero even_two (Nat.pos_iff_ne_zero.mp n.pos)) odd_one
  have hsodd : Odd (orderOf s) := Odd.of_dvd_nat hkodd (orderOf_dvd_natCard s)
  have hs2 : s ^ 2 ≠ 1 := by
    intro h2
    have hdvd : orderOf s ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    rcases hsodd with ⟨m, hm⟩
    have hle : 2 * m + 1 ≤ 2 := by
      rw [← hm]
      exact Nat.le_of_dvd (by norm_num) hdvd
    have hone : orderOf s = 1 := by omega
    exact hs (orderOf_eq_one_iff.mp hone)
  obtain ⟨g, hgdet, hgpow, hgnoeig, _⟩ :=
    exists_linearEquiv_det_pow_no_eigenvalue 2 hX s hs hs2
  have hdet : LinearEquiv.det (scalarEquiv (E := E) s) * LinearEquiv.det g *
      LinearEquiv.det (scalarEquiv (E := E) s) = 1 := by
    rw [det_scalarEquiv hd s, hgdet, pow_two]
    group
  let h : SpecialLinearGroup k (DSpace E X) :=
    blockSL (scalarEquiv (E := E) s) g (scalarEquiv (E := E) s) hdet
  have hconjmaps : ∀ t : E, (scalarEquiv (E := E) s).toLinearMap ∘ₗ LinearMap.mulLeft k t ∘ₗ
      (scalarEquiv (E := E) s).symm.toLinearMap = LinearMap.mulLeft k t := by
    have hs0 : (s : k) ≠ 0 := Units.ne_zero s
    intro t
    ext y
    rw [LinearMap.comp_apply, LinearMap.comp_apply, scalarEquiv_toLinearMap,
      scalarEquiv_symm_toLinearMap, Algebra.lsmul_apply, LinearMap.mulLeft_apply,
      Algebra.lsmul_apply, LinearMap.mulLeft_apply]
    rw [Algebra.mul_smul_comm, smul_smul, Units.mul_inv, one_smul]
  have hnorm_mem : h ∈
      Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))) := by
    change blockSL (scalarEquiv (E := E) s) g (scalarEquiv (E := E) s) hdet ∈ _
    rw [blockSL_mem_normalizer_iff]
    intro t
    exact ⟨t, hconjmaps t⟩
  have hodd : Odd (orderOf h) := by
    have hpow : h ^ orderOf s = 1 := by
      apply SpecialLinearGroup.toLinearEquiv_injective
      rw [map_pow, map_one]
      change (blockDiag (scalarEquiv (E := E) s) g (scalarEquiv (E := E) s)) ^ orderOf s = 1
      rw [blockDiag_pow, scalarEquiv_pow, pow_orderOf_eq_one, scalarEquiv_one, hgpow,
        blockDiag_one]
    exact Odd.of_dvd_nat hsodd (orderOf_dvd_iff_pow_eq_one.mpr hpow)
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
    have hfix : blockDiag (scalarEquiv (E := E) s) g (scalarEquiv (E := E) s) * unipElt φ χ ψ *
        (blockDiag (scalarEquiv (E := E) s) g (scalarEquiv (E := E) s))⁻¹ =
        unipElt φ χ ψ :=
      blockDiag_conj_of_centralizer hfix_sl rfl hg'eq
    obtain ⟨hφ, hχ, hψ⟩ := (blockDiag_conj_unipElt_eq_iff _ _ _ φ χ ψ).mp hfix
    have hφ' : ∀ x : X, (s : k) • φ x = φ (g x) := by
      intro x
      have h := congrArg (fun f : X →ₗ[k] E => f x) hφ
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
      simpa [scalarEquiv_toLinearMap, Algebra.lsmul_apply] using h
    have hχ' : ∀ t : E, g (χ t) = (s : k) • χ t := by
      intro t
      have h := congrArg (fun f : E →ₗ[k] X => f t) hχ
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
      change g (χ t) = χ ((s : k) • t) at h
      rw [map_smul] at h
      exact h
    have hφ0 : φ = 0 := by
      ext y
      have hinj : Function.Injective
          (g.toLinearMap - (s : k) • (LinearMap.id : X →ₗ[k] X)) := by
        intro x1 x2 hx
        have hsub : (g.toLinearMap - (s : k) • (LinearMap.id : X →ₗ[k] X)) (x1 - x2) = 0 := by
          rw [map_sub, hx, sub_self]
        have hgs : g (x1 - x2) = (s : k) • (x1 - x2) := by
          have := sub_eq_zero.mp hsub
          simpa [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] using this
        exact sub_eq_zero.mp (hgnoeig (x1 - x2) hgs)
      have hsurj : Function.Surjective
          (g.toLinearMap - (s : k) • (LinearMap.id : X →ₗ[k] X)) :=
        LinearMap.surjective_of_injective hinj
      obtain ⟨x, hx⟩ := hsurj y
      have hval : (g.toLinearMap - (s : k) • (LinearMap.id : X →ₗ[k] X)) x =
          g x - (s : k) • x := by
        simp [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
      have hzero : φ (g x - (s : k) • x) = 0 := by
        rw [map_sub, map_smul, hφ' x, sub_self]
      rw [← hval] at hzero
      rwa [hx] at hzero
    have hχ0 : χ = 0 := by
      ext t
      exact hgnoeig (χ t) (hχ' t)
    have hψ0 : ψ = LinearMap.mulLeft k (ψ 1) := eq_mulLeft_of_finrank_eq_one hd ψ
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
    have hconj := blockSL_conj_rootElt (scalarEquiv (E := E) s) g (scalarEquiv (E := E) s) hdet t
      (hconjmaps t)
    have hcomm : h * rootElt k X t = rootElt k X t * h := by
      have hconj' : h * rootElt k X t * h⁻¹ = rootElt k X t := by
        change blockSL (scalarEquiv (E := E) s) g (scalarEquiv (E := E) s) hdet * rootElt k X t *
          (blockSL (scalarEquiv (E := E) s) g (scalarEquiv (E := E) s) hdet)⁻¹ =
          rootElt k X t
        exact hconj
      calc h * rootElt k X t = h * rootElt k X t * h⁻¹ * h := by group
        _ = rootElt k X t * h := by rw [hconj']
    exact hcomm

end CFSG.LinearAlgebra.RootGroupSL
