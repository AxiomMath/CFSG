module

public import CFSG.LinearAlgebra.RootGroupSL.Datum
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LinearAlgebra.RootGroupSL

open CFSG.Open

variable {k E X : Type} [Field k] [Field E] [Algebra k E] [AddCommGroup X] [Module k X]

private lemma add_self_eq_zero_of_charTwo (K : Type*) [Field K] [CharP K 2]
    {A : Type*} [AddCommGroup A] [Module K A] (x : A) : x + x = 0 := by
  calc x + x = (1 : K) • x + (1 : K) • x := by rw [one_smul]
    _ = ((1 : K) + 1) • x := (add_smul _ _ _).symm
    _ = 0 := by rw [CharTwo.add_self_eq_zero (1 : K), zero_smul]

private def rootEquivSubOne (t : E) : DSpace E X →ₗ[k] DSpace E X :=
  (rootEquiv k X t : DSpace E X →ₗ[k] DSpace E X) - (1 : DSpace E X →ₗ[k] DSpace E X)

private lemma rootEquivSubOne_apply (t : E) (v : DSpace E X) :
    rootEquivSubOne (k := k) t v = (t * v.2.2, 0, 0) := by
  ext <;> simp [rootEquivSubOne, rootEquiv, shearE, LinearMap.mulLeft_apply]

private lemma det_shearE_general (φ : E →ₗ[k] E) :
    LinearEquiv.det (shearE X φ) = 1 := by
  by_cases h : Module.Finite k (DSpace E X)
  · have hE : Module.Finite k E :=
      h.of_surjective (LinearMap.fst k E (X × E))
        (LinearMap.fst_surjective (R := k) (M := E) (M₂ := X × E))
    have hX : Module.Finite k X :=
      h.of_surjective ((LinearMap.fst k X E).comp (LinearMap.snd k E (X × E)))
        ((LinearMap.fst_surjective (R := k) (M := X) (M₂ := E)).comp
          (LinearMap.snd_surjective (R := k) (M := E) (M₂ := X × E)))
    haveI : Module.Finite k E := hE
    haveI : Module.Finite k X := hX
    exact det_shearE (X := X) φ
  · apply Units.ext
    rw [LinearEquiv.coe_det, Units.val_one]
    exact LinearMap.det_eq_one_of_not_module_finite h _

private def rootElt' (t : E) : SpecialLinearGroup k (DSpace E X) :=
  ⟨rootEquiv k X t, det_shearE_general (LinearMap.mulLeft k t)⟩

private lemma rootElt'_mem (t : E) : rootElt' t ∈ rootSL k E X :=
  mem_rootSL_iff.mpr ⟨t, rfl⟩

private lemma rootEquiv_conj_mem {g : SpecialLinearGroup k (DSpace E X)}
    (hg : g ∈ Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))))
    (t : E) :
    ∃ s : E, (g : DSpace E X ≃ₗ[k] DSpace E X) * rootEquiv k X t *
        (g : DSpace E X ≃ₗ[k] DSpace E X)⁻¹ = rootEquiv k X s := by
  have hmem : g * rootElt' t * g⁻¹ ∈ rootSL k E X :=
    (Subgroup.mem_normalizer_iff.mp hg (rootElt' t)).mp (rootElt'_mem t)
  obtain ⟨s, hs⟩ := mem_rootSL_iff.mp hmem
  exact ⟨s, by simpa [rootElt'] using hs⟩

private lemma rootEquiv_conj_mem_ne_zero {g : SpecialLinearGroup k (DSpace E X)}
    (hg : g ∈ Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))))
    {t : E} (ht : t ≠ 0) :
    ∃ s : E, s ≠ 0 ∧ (g : DSpace E X ≃ₗ[k] DSpace E X) * rootEquiv k X t *
        (g : DSpace E X ≃ₗ[k] DSpace E X)⁻¹ = rootEquiv k X s := by
  obtain ⟨s, hs⟩ := rootEquiv_conj_mem hg t
  refine ⟨s, ?_, hs⟩
  intro hs0
  have hr : rootEquiv k X t = 1 := by
    have h0 : rootEquiv k X (0 : E) = 1 := by
      ext v <;> simp [rootEquiv, shearE]
    rw [hs0, h0] at hs
    calc rootEquiv k X t =
          (g : DSpace E X ≃ₗ[k] DSpace E X)⁻¹ *
            ((g : DSpace E X ≃ₗ[k] DSpace E X) * rootEquiv k X t *
              (g : DSpace E X ≃ₗ[k] DSpace E X)⁻¹) *
            (g : DSpace E X ≃ₗ[k] DSpace E X) := by group
      _ = (g : DSpace E X ≃ₗ[k] DSpace E X)⁻¹ * 1 *
            (g : DSpace E X ≃ₗ[k] DSpace E X) := by rw [hs]
      _ = 1 := by group
  have ht0 : t = 0 := by
    have h := congrArg (fun (e : DSpace E X ≃ₗ[k] DSpace E X) =>
      (e (0, (0 : X), (1 : E))).1) hr
    simpa [rootEquiv, shearE, LinearMap.mulLeft_apply] using h
  exact ht ht0

private lemma range_rootEquivSubOne {t : E} (ht : t ≠ 0) :
    LinearMap.range (rootEquivSubOne (k := k) (X := X) t) = flagW k E X := by
  ext w
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨v, hv⟩
    rw [rootEquivSubOne_apply] at hv
    rw [flagW, LinearMap.mem_ker, LinearMap.snd_apply, ← hv]
    rfl
  · intro hw
    rw [flagW, LinearMap.mem_ker, LinearMap.snd_apply] at hw
    refine ⟨(0, (0 : X), t⁻¹ * w.1), ?_⟩
    rw [rootEquivSubOne_apply]
    have hw' : w = (w.1, (0 : X), (0 : E)) := by ext <;> simp [hw]
    rw [hw', mul_inv_cancel_left₀ ht]

private lemma ker_rootEquivSubOne {t : E} (ht : t ≠ 0) :
    LinearMap.ker (rootEquivSubOne (k := k) (X := X) t) = flagK k E X := by
  ext w
  rw [LinearMap.mem_ker, rootEquivSubOne_apply]
  constructor
  · intro h
    have h1 : t * w.2.2 = 0 := by
      simpa using congrArg (fun v : DSpace E X => v.1) h
    have h2 : w.2.2 = 0 := (mul_eq_zero.mp h1).resolve_left ht
    rw [flagK, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.snd_apply, LinearMap.snd_apply]
    exact h2
  · intro hw
    rw [flagK, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.snd_apply,
      LinearMap.snd_apply] at hw
    rw [hw, mul_zero]
    rfl

private lemma range_conj_iff {g : SpecialLinearGroup k (DSpace E X)} {s t : E}
    (hconj : ∀ w : DSpace E X,
      (g : DSpace E X ≃ₗ[k] DSpace E X) (rootEquivSubOne (k := k) s w) =
        rootEquivSubOne (k := k) t ((g : DSpace E X ≃ₗ[k] DSpace E X) w)) (v : DSpace E X) :
    g v ∈ LinearMap.range (rootEquivSubOne (k := k) (X := X) t) ↔
      v ∈ LinearMap.range (rootEquivSubOne (k := k) (X := X) s) := by
  rw [LinearMap.mem_range, LinearMap.mem_range]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨(g : DSpace E X ≃ₗ[k] DSpace E X)⁻¹ w, ?_⟩
    have h := hconj ((g : DSpace E X ≃ₗ[k] DSpace E X)⁻¹ w)
    simp only [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] at h
    rw [hw] at h
    exact (g : DSpace E X ≃ₗ[k] DSpace E X).injective h
  · rintro ⟨w, hw⟩
    refine ⟨(g : DSpace E X ≃ₗ[k] DSpace E X) w, ?_⟩
    rw [← hconj w, hw]

private lemma normalizer_conj_subOne {g : SpecialLinearGroup k (DSpace E X)}
    (hg : g ∈ Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))))
    {s : E} (hs : s ≠ 0) :
    ∃ t : E, t ≠ 0 ∧ ∀ w : DSpace E X,
      (g : DSpace E X ≃ₗ[k] DSpace E X) (rootEquivSubOne (k := k) s w) =
        rootEquivSubOne (k := k) t ((g : DSpace E X ≃ₗ[k] DSpace E X) w) := by
  obtain ⟨t, ht, hconj⟩ := rootEquiv_conj_mem_ne_zero hg hs
  refine ⟨t, ht, ?_⟩
  intro w
  have hsplit : (g : DSpace E X ≃ₗ[k] DSpace E X) * rootEquiv k X s =
      rootEquiv k X t * (g : DSpace E X ≃ₗ[k] DSpace E X) := by
    have := congrArg (fun e : DSpace E X ≃ₗ[k] DSpace E X =>
      e * (g : DSpace E X ≃ₗ[k] DSpace E X)) hconj
    rwa [mul_assoc, inv_mul_cancel, mul_one] at this
  have h := congrArg (fun (e : DSpace E X ≃ₗ[k] DSpace E X) => e w) hsplit
  simp only [LinearEquiv.mul_apply] at h
  simp only [rootEquivSubOne, LinearMap.sub_apply, LinearEquiv.coe_toLinearMap]
  rw [map_sub, h]
  rfl

theorem QK_le_centralizer_rootSL :
    QK k E X ≤ Subgroup.centralizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  obtain ⟨t, ht⟩ := mem_rootSL_iff.mp hh
  obtain ⟨φ, χ, ψ, hg_eq⟩ := exists_unipElt_of_mem_unipRad (mem_QK_iff.mp hg)
  apply SpecialLinearGroup.ext
  intro v
  change ((h : DSpace E X ≃ₗ[k] DSpace E X) * (g : DSpace E X ≃ₗ[k] DSpace E X)) v =
    ((g : DSpace E X ≃ₗ[k] DSpace E X) * (h : DSpace E X ≃ₗ[k] DSpace E X)) v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hg_eq, ht]
  obtain ⟨a, x, b⟩ := v
  simp [rootEquiv, shearE, unipElt, LinearMap.mulLeft_apply]
  abel

theorem mem_flagW_iff_of_mem_normalizer {g : SpecialLinearGroup k (DSpace E X)}
    (hg : g ∈ Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))))
    (v : DSpace E X) : g v ∈ flagW k E X ↔ v ∈ flagW k E X := by
  obtain ⟨t, ht, hconj⟩ := normalizer_conj_subOne hg (s := 1) one_ne_zero
  have e2 : flagW k E X = LinearMap.range (rootEquivSubOne (k := k) (X := X) t) :=
    (range_rootEquivSubOne ht).symm
  have e1 : flagW k E X = LinearMap.range (rootEquivSubOne (k := k) (X := X) 1) :=
    (range_rootEquivSubOne one_ne_zero).symm
  conv_lhs => rw [e2]
  conv_rhs => rw [e1]
  exact range_conj_iff hconj v

theorem mem_flagK_iff_of_mem_normalizer {g : SpecialLinearGroup k (DSpace E X)}
    (hg : g ∈ Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))))
    (v : DSpace E X) : g v ∈ flagK k E X ↔ v ∈ flagK k E X := by
  obtain ⟨t, ht, hconj⟩ := normalizer_conj_subOne hg (s := 1) one_ne_zero
  have e2 : flagK k E X = LinearMap.ker (rootEquivSubOne (k := k) (X := X) t) :=
    (ker_rootEquivSubOne ht).symm
  have e1 : flagK k E X = LinearMap.ker (rootEquivSubOne (k := k) (X := X) 1) :=
    (ker_rootEquivSubOne one_ne_zero).symm
  conv_lhs => rw [e2]
  conv_rhs => rw [e1]
  rw [LinearMap.mem_ker, LinearMap.mem_ker, ← hconj v]
  constructor
  · intro h
    exact (g : DSpace E X ≃ₗ[k] DSpace E X).injective (by rw [h, map_zero])
  · intro h
    rw [h, map_zero]

variable [Module.Finite k E] [Module.Finite k X] in
@[expose] def blockSL (a : E ≃ₗ[k] E) (g : X ≃ₗ[k] X) (b : E ≃ₗ[k] E)
    (h : LinearEquiv.det a * LinearEquiv.det g * LinearEquiv.det b = 1) :
    SpecialLinearGroup k (DSpace E X) :=
  ⟨blockDiag a g b, by rw [det_blockDiag]; exact h⟩

variable [Module.Finite k E] [Module.Finite k X] in
private lemma coe_blockSL_conj (a : E ≃ₗ[k] E) (g : X ≃ₗ[k] X) (b : E ≃ₗ[k] E)
    (h : LinearEquiv.det a * LinearEquiv.det g * LinearEquiv.det b = 1)
    (H : SpecialLinearGroup k (DSpace E X)) :
    ((blockSL a g b h * H * (blockSL a g b h)⁻¹ : SpecialLinearGroup k (DSpace E X)) :
        DSpace E X ≃ₗ[k] DSpace E X) =
      blockDiag a g b * (H : DSpace E X ≃ₗ[k] DSpace E X) * (blockDiag a g b)⁻¹ :=
  rfl

variable [Module.Finite k E] [Module.Finite k X] in
theorem blockSL_mem_normalizer_iff [Finite E] (a : E ≃ₗ[k] E) (g : X ≃ₗ[k] X) (b : E ≃ₗ[k] E)
    (h : LinearEquiv.det a * LinearEquiv.det g * LinearEquiv.det b = 1) :
    blockSL a g b h ∈
        Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))) ↔
      ∀ t : E, ∃ s : E,
        a.toLinearMap ∘ₗ LinearMap.mulLeft k t ∘ₗ b.symm.toLinearMap = LinearMap.mulLeft k s := by
  classical
  constructor
  · intro hB t
    have hmem : blockSL a g b h * rootElt k X t * (blockSL a g b h)⁻¹ ∈ rootSL k E X :=
      (Subgroup.mem_normalizer_iff.mp hB (rootElt k X t)).mp (rootElt_mem_rootSL t)
    obtain ⟨s, hs⟩ := mem_rootSL_iff.mp hmem
    refine ⟨s, ?_⟩
    rw [coe_blockSL_conj] at hs
    simp only [rootElt, rootEquiv] at hs
    rw [blockDiag_mul_shearE_mul_inv] at hs
    exact shearE_injective hs
  · intro hiff
    let σ : E → E := fun t => Classical.choose (hiff t)
    have hσ : ∀ t, a.toLinearMap ∘ₗ LinearMap.mulLeft k t ∘ₗ b.symm.toLinearMap =
        LinearMap.mulLeft k (σ t) := fun t => Classical.choose_spec (hiff t)
    have hφ_inj : Function.Injective
        (fun t : E => a.toLinearMap ∘ₗ LinearMap.mulLeft k t ∘ₗ b.symm.toLinearMap) := by
      intro t u htu
      have h1 : ∀ y : E, t * y = u * y := by
        intro y
        obtain ⟨x, rfl⟩ := b.symm.surjective y
        have h2 := congrArg (fun f : E →ₗ[k] E => f x) htu
        simp only [LinearMap.comp_apply] at h2
        exact a.injective h2
      simpa using h1 1
    have hσ_inj : Function.Injective σ := by
      intro t u htu
      apply hφ_inj
      change a.toLinearMap ∘ₗ LinearMap.mulLeft k t ∘ₗ b.symm.toLinearMap =
        a.toLinearMap ∘ₗ LinearMap.mulLeft k u ∘ₗ b.symm.toLinearMap
      rw [hσ t, hσ u, htu]
    have hσ_surj : Function.Surjective σ := Finite.surjective_of_injective hσ_inj
    have hconj_t : ∀ t : E, blockDiag a g b * rootEquiv k X t * (blockDiag a g b)⁻¹ =
        rootEquiv k X (σ t) := by
      intro t
      rw [rootEquiv, rootEquiv, blockDiag_mul_shearE_mul_inv, ← hσ t]
    rw [Subgroup.mem_normalizer_iff]
    intro H
    constructor
    · intro hH
      obtain ⟨t, ht⟩ := mem_rootSL_iff.mp hH
      refine mem_rootSL_iff.mpr ⟨σ t, ?_⟩
      rw [coe_blockSL_conj, ht, hconj_t]
    · intro hBH
      obtain ⟨u, hu⟩ := mem_rootSL_iff.mp hBH
      obtain ⟨t, ht⟩ := hσ_surj u
      refine mem_rootSL_iff.mpr ⟨t, ?_⟩
      have hu' : blockDiag a g b * (H : DSpace E X ≃ₗ[k] DSpace E X) * (blockDiag a g b)⁻¹ =
          rootEquiv k X (σ t) := by
        rw [← coe_blockSL_conj (h := h), hu, ← ht]
      calc (H : DSpace E X ≃ₗ[k] DSpace E X) =
            (blockDiag a g b)⁻¹ * (blockDiag a g b *
              (H : DSpace E X ≃ₗ[k] DSpace E X) * (blockDiag a g b)⁻¹) *
              (blockDiag a g b) := by group
        _ = (blockDiag a g b)⁻¹ * rootEquiv k X (σ t) * (blockDiag a g b) := by rw [hu']
        _ = (blockDiag a g b)⁻¹ * (blockDiag a g b * rootEquiv k X t *
              (blockDiag a g b)⁻¹) * (blockDiag a g b) := by rw [← hconj_t]
        _ = rootEquiv k X t := by group

private lemma unipElt_zero_sq [CharP k 2] (ψ : E →ₗ[k] E) :
    unipElt (0 : X →ₗ[k] E) (0 : E →ₗ[k] X) ψ ^ 2 = 1 := by
  rw [pow_two, unipElt_mul]
  simp [unipElt_zero, add_self_eq_zero_of_charTwo k]

private lemma unipElt_sq [CharP k 2] (φ : X →ₗ[k] E) (χ : E →ₗ[k] X) (ψ : E →ₗ[k] E) :
    unipElt φ χ ψ ^ 2 = unipElt 0 0 (φ ∘ₗ χ) := by
  rw [pow_two, unipElt_mul, add_self_eq_zero_of_charTwo k φ,
    add_self_eq_zero_of_charTwo k χ, add_self_eq_zero_of_charTwo k ψ, zero_add]

private lemma unipElt_pow_four [CharP k 2] (φ : X →ₗ[k] E) (χ : E →ₗ[k] X) (ψ : E →ₗ[k] E) :
    unipElt φ χ ψ ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, unipElt_sq]
  exact unipElt_zero_sq (φ ∘ₗ χ)

theorem isPGroup_QK [CharP k 2] : IsPGroup 2 (QK k E X) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  obtain ⟨φ, χ, ψ, hg_eq⟩ := exists_unipElt_of_mem_unipRad (mem_QK_iff.mp g.2)
  refine ⟨2, ?_⟩
  show g ^ (2 ^ 2) = 1
  rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_pow, SpecialLinearGroup.coe_one]
  rw [show ((g : SpecialLinearGroup k (DSpace E X)) : DSpace E X ≃ₗ[k] DSpace E X) =
      unipElt φ χ ψ from hg_eq]
  exact unipElt_pow_four φ χ ψ

private theorem le_pCoreOf_of_normal {G : Type*} [Group G] {p : ℕ} {N H : Subgroup G}
    (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal) (hp : IsPGroup p N) :
    N ≤ pCoreOf p H := by
  have hsub : IsPGroup p (N.subgroupOf H) :=
    hp.of_equiv (Subgroup.subgroupOfEquivOfLe hNH).symm
  have hcore : N.subgroupOf H ≤ CFSG.pCore p ↥H := by
    rw [CFSG.pCore_eq_iSup]
    exact le_iSup_of_le (N.subgroupOf H) (le_iSup_of_le hN (le_iSup_of_le hsub le_rfl))
  intro x hx
  refine Subgroup.mem_map.mpr ⟨⟨x, hNH hx⟩, ?_, rfl⟩
  exact hcore (Subgroup.mem_subgroupOf.mpr hx)

theorem QK_le_pCoreOf_normalizer [CharP k 2] :
    QK k E X ≤
      pCoreOf 2 (Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X)))) := by
  have hNH : QK k E X ≤
      Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))) :=
    QK_le_centralizer_rootSL.trans (Subgroup.centralizer_le_normalizer _)
  have hQKn : ((QK k E X).subgroupOf
      (Subgroup.normalizer (rootSL k E X : Set (SpecialLinearGroup k (DSpace E X))))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNH]
    intro q n hq hn
    refine mem_QK_iff.mpr ?_
    obtain ⟨hqW, hqK, hqM⟩ := mem_QK_iff.mp hq
    change (n : DSpace E X ≃ₗ[k] DSpace E X) * (q : DSpace E X ≃ₗ[k] DSpace E X) *
        (n : DSpace E X ≃ₗ[k] DSpace E X)⁻¹ ∈ unipRad k E X
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      have hnv : (n : DSpace E X ≃ₗ[k] DSpace E X).symm v ∈ flagW k E X :=
        (mem_flagW_iff_of_mem_normalizer hn ((n : DSpace E X ≃ₗ[k] DSpace E X).symm v)).mp
          (by simpa using hv)
      have hfix := hqW _ hnv
      simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv]
      rw [hfix, LinearEquiv.apply_symm_apply]
    · intro v hv
      have hnv : (n : DSpace E X ≃ₗ[k] DSpace E X).symm v ∈ flagK k E X :=
        (mem_flagK_iff_of_mem_normalizer hn ((n : DSpace E X ≃ₗ[k] DSpace E X).symm v)).mp
          (by simpa using hv)
      have hqK' := hqK _ hnv
      have h := (mem_flagW_iff_of_mem_normalizer hn _).mpr hqK'
      simpa [LinearEquiv.mul_apply, LinearEquiv.coe_inv, map_sub] using h
    · intro v
      have hqM' := hqM ((n : DSpace E X ≃ₗ[k] DSpace E X).symm v)
      have h := (mem_flagK_iff_of_mem_normalizer hn _).mpr hqM'
      simpa [LinearEquiv.mul_apply, LinearEquiv.coe_inv, map_sub] using h
  exact le_pCoreOf_of_normal hNH hQKn isPGroup_QK

end CFSG.LinearAlgebra.RootGroupSL
