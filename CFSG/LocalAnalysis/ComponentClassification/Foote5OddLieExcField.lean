module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcTools
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcTorus
public import CFSG.LocalAnalysis.ComponentClassification.SteinbergBNEvenInnerInvolutionOddCore
public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizer

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag}

theorem units_map_entrywiseHom_comp' {K : Type} [Field K] (σ σ' : K →+* K) (g : ModGL τ K) :
    Units.map (entrywiseHom σ) (Units.map (entrywiseHom σ') g) =
      Units.map (entrywiseHom (σ.comp σ')) g := by
  ext1
  simp only [Units.coe_map]
  exact entrywise_entrywise σ σ' _

@[expose] def UniqueFieldNormalForm (τ : Tag) (K : Type) [Field K] : Prop :=
  ∀ α : MulAut (adjointGroup τ K), ∃! gφ : adjointGroup τ K × (K ≃+* K),
    ∀ h : adjointGroup τ K, (α h : ModGL τ K) = (gφ.1 : ModGL τ K) *
      Units.map (entrywiseHom gφ.2.toRingHom) (h : ModGL τ K) * (gφ.1 : ModGL τ K)⁻¹

theorem uniqueFieldNormalForm_E8
    (K : Type) [Field K] [Finite K] : UniqueFieldNormalForm .E8 K := by
  have hτ : Tag.E8 = .E6 ∨ Tag.E8 = .E7 ∨ Tag.E8 = .E8 := Or.inr (Or.inr rfl)
  obtain ⟨-, -, hNF⟩ := ordinary_E_exact_automorphism_normal_form .E8 hτ K
  obtain ⟨Θ, -, hΘ, -, -, -⟩ := ordinary_E_field_graph_quotient_and_involutions .E8 hτ K
  have hZ := mulAut_conj_injective_of_center_eq_bot
    (center_adjointGroup_eq_bot (τ := .E8) (K := K))
  intro α
  obtain ⟨g, a, σ, ε, hα⟩ := hNF α
  have hQ : exactQ Tag.E8 K ε = 1 := rfl
  have hTG : torusGroup Tag.E8 K ≤ adjointGroup Tag.E8 K :=
    (Subgroup.closure_le _).2 fun _ ⟨q, hq⟩ => hq ▸ torusElt_mem_adjointGroup q.1 q.2
  obtain ⟨d, hd⟩ : ∃ d : adjointGroup Tag.E8 K, (d : ModGL Tag.E8 K) = rootDiagUnit Tag.E8 a :=
    ⟨⟨rootDiagUnit Tag.E8 a,
      hTG (rootDiagUnit_mem_torusGroup_of_det_one (Or.inr (Or.inr rfl)) a)⟩, rfl⟩
  have hform : ∀ h : adjointGroup Tag.E8 K, (α h : ModGL Tag.E8 K) =
      ((g * d : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) *
        Units.map (entrywiseHom σ.toRingHom) (h : ModGL Tag.E8 K) *
          ((g * d : adjointGroup Tag.E8 K) : ModGL Tag.E8 K)⁻¹ := fun h => by
    rw [hα h, hQ, Subgroup.coe_mul, hd]
    group
  refine ⟨(g * d, σ), hform, ?_⟩
  rintro ⟨g', σ'⟩ h'
  have h1 := hΘ α g a σ ε hα
  have h2 := hΘ α g' 1 σ' ⟨0, by decide⟩ fun h => by
    rw [h' h, rootDiagUnit_one, show exactQ Tag.E8 K ((⟨0, by decide⟩ : Fin (exactE Tag.E8)) : ℕ) =
      1 from rfl]
    group
  have hσ : σ' = σ := congrArg Prod.fst (h2.symm.trans h1)
  subst hσ
  obtain ⟨e, he⟩ := (Chevalley_coordinate_field_fixed_normal_subgroup Tag.E8 K σ').1
  have hconj : MulAut.conj g' = MulAut.conj (g * d) := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    have h5 : Units.map (entrywiseHom σ'.toRingHom)
        ((e⁻¹ h : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) = h := by
      rw [← he, MulAut.apply_inv_self]
    have h6 := (h' (e⁻¹ h)).symm.trans (hform (e⁻¹ h))
    rw [h5] at h6
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev,
      mul_assoc] at h6 ⊢
    exact h6
  exact Prod.ext (hZ hconj) rfl

theorem eq_one_or_eq_of_mem_zpowers_of_sq {G : Type*} [Group G] {x y : G} (hx : x ^ 2 = 1)
    (hy : y ∈ zpowers x) : y = 1 ∨ y = x := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hx2 : x ^ (2 : ℤ) = 1 := by rw [zpow_ofNat, hx]
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' n
  · left
    rw [zpow_mul, hx2, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, hx2, one_zpow, one_mul]

theorem outerCoreTrivAt_entrywise_field
    {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2) {q₀ : ℕ} (δ : K ≃+* K)
    (hδ : ∀ c, δ c = c ^ q₀) (hδ2 : δ ^ 2 = 1) (hNF : UniqueFieldNormalForm τ K)
    (hNFk : UniqueFieldNormalForm τ (fixSubfield δ))
    (hΓJ : entrywiseFixedGroup τ δ = fixedFieldImage τ δ) {β : MulAut (adjointGroup τ K)}
    (hβ : ∀ u, (β u : ModGL τ K) = Units.map (entrywiseHom δ.toRingHom) (u : ModGL τ K))
    (hβ2 : β ^ 2 = 1) : OuterCoreTrivAt β := by
  have hZ : center (adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  have : Finite (ModGL τ K) := finite_modGL
  have : Finite (fixSubfield δ) := Subtype.finite
  have hJC : fixedFieldImage τ δ ≤ adjointGroup τ K := fun x hx => (fixedFieldImage_le hx).1
  have hfix : ∀ s : adjointGroup τ K,
      β s = s ↔ s ∈ (fixedFieldImage τ δ).subgroupOf (adjointGroup τ K) := by
    intro s
    rw [Subgroup.mem_subgroupOf, ← hΓJ]
    constructor
    · intro hs
      refine mem_inf.2 ⟨s.2, ?_⟩
      change Units.map (entrywiseHom δ.toRingHom) (s : ModGL τ K) = s
      rw [← hβ, hs]
    · intro hs
      apply Subtype.ext
      rw [hβ]
      exact (mem_inf.1 hs).2
  obtain ⟨hJs0, hJna0, -⟩ :=
    odd_pinned_Chevalley_p_components τ (fixSubfield δ) (ringChar_fixSubfield_ne_two hK2 δ)
  have eJ : (fixedFieldImage τ δ).subgroupOf (adjointGroup τ K) ≃*
      adjointGroup τ (fixSubfield δ) :=
    (Subgroup.subgroupOfEquivOfLe hJC).trans (fixedFieldImageEquiv δ).symm
  have hJs : IsSimpleGroup ((fixedFieldImage τ δ).subgroupOf (adjointGroup τ K)) :=
    (MulEquiv.isSimpleGroup_congr eJ).2 hJs0
  have hJna : ∃ x y : (fixedFieldImage τ δ).subgroupOf (adjointGroup τ K), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hJna0
    exact ⟨eJ.symm x, eJ.symm y, fun h => hxy (eJ.symm.injective (by rw [map_mul, map_mul, h]))⟩
  have hφδ : ∀ φ : K ≃+* K, (δ.trans φ).toRingHom = φ.toRingHom.comp δ.toRingHom := fun _ => rfl
  have hδφ : ∀ φ : K ≃+* K, (δ.trans φ).toRingHom = δ.toRingHom.comp φ.toRingHom := by
    intro φ
    ext c
    change φ (δ c) = δ (φ c)
    rw [hδ, hδ, map_pow]
  have hid : ∀ x : ModGL τ K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) x = x :=
    fun x => Units.ext (entrywise_id _)
  intro R hRodd hRi hRc r hr
  have hrJ : ∀ j : adjointGroup τ K,
      j ∈ (fixedFieldImage τ δ).subgroupOf (adjointGroup τ K) → r j = j := fun j hj =>
    fix_of_fixed_simple hZ hRodd hRi hRc hfix hJs hJna hr hj
  obtain ⟨⟨g, φ⟩, hgφ, -⟩ := hNF r
  have hgφ' : ∀ h : adjointGroup τ K, (r h : ModGL τ K) = (g : ModGL τ K) *
      Units.map (entrywiseHom φ.toRingHom) (h : ModGL τ K) * (g : ModGL τ K)⁻¹ := hgφ
  have hγ1 : ∀ h : adjointGroup τ K, ((r * β) h : ModGL τ K) = (g : ModGL τ K) *
      Units.map (entrywiseHom (δ.trans φ).toRingHom) (h : ModGL τ K) * (g : ModGL τ K)⁻¹ :=
    fun h => by
      rw [MulAut.mul_apply, hgφ', hβ, units_map_entrywiseHom_comp', ← hφδ]
  have hγ2 : ∀ h : adjointGroup τ K, ((r * β) h : ModGL τ K) =
      ((β g : adjointGroup τ K) : ModGL τ K) *
        Units.map (entrywiseHom (δ.trans φ).toRingHom) (h : ModGL τ K) *
          ((β g : adjointGroup τ K) : ModGL τ K)⁻¹ := fun h => by
    rw [hRi r hr, MulAut.mul_apply, hβ, hgφ', map_mul, map_mul, map_inv, hβ g,
      units_map_entrywiseHom_comp', ← hδφ]
  obtain ⟨_, -, huniq⟩ := hNF (r * β)
  have hgg : (g, δ.trans φ) = (β g, δ.trans φ) :=
    (huniq (g, δ.trans φ) hγ1).trans (huniq (β g, δ.trans φ) hγ2).symm
  have hgΓ : (g : ModGL τ K) ∈ fixedFieldImage τ δ := by
    rw [← hΓJ]
    refine mem_inf.2 ⟨g.2, ?_⟩
    change Units.map (entrywiseHom δ.toRingHom) (g : ModGL τ K) = g
    have hg' : g = β g := congrArg Prod.fst hgg
    rw [← hβ, ← hg']
  obtain ⟨hg1, hφk⟩ := eq_one_of_forall_fixedFieldImage_of_normalForm hNFk hgΓ φ
    fun j hj => by
      rw [← hgφ' j]
      exact congrArg Subtype.val (hrJ j hj)
  have hφz : φ ∈ zpowers δ := UnbalancedCatalog.mem_zpowers_of_fixed fun x hx => hφk x hx
  subst hg1
  rcases eq_one_or_eq_of_mem_zpowers_of_sq hδ2 hφz with rfl | rfl
  · refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [hgφ', hid]
    simp
  · have hrβ : r = β := MulEquiv.ext fun h => Subtype.ext (by rw [hgφ', hβ]; simp)
    have hro := odd_orderOf_of_mem hRodd hr
    rw [hrβ] at hro ⊢
    exact eq_one_of_odd_of_mem_zpowers hβ2 (mem_zpowers β) hro

theorem outerCoreAt_quadratic_field
    {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2) {p e : ℕ} (hp : p.Prime)
    (he : 1 ≤ e) (hKe : Nat.card K = (p ^ e) ^ 2) (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ (p ^ e))
    (hNF : UniqueFieldNormalForm τ K) (hNFk : UniqueFieldNormalForm τ (fixSubfield δ))
    (hΓJ : entrywiseFixedGroup τ δ = fixedFieldImage τ δ)
    {α : MulAut (adjointGroup τ K)} {g : adjointGroup τ K} {a : Fin τ.rank → Kˣ}
    (hαg : ∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
      Units.map (entrywiseHom δ.toRingHom) (h : ModGL τ K) * (rootDiagUnit τ a)⁻¹ *
        (g : ModGL τ K)⁻¹)
    (hα : α ^ 2 = 1) : OuterCoreAt α := by
  obtain ⟨hQ1, -⟩ := exceptional_Lang_quadratic_field_coset_conjugacy hp he K hKe δ.toRingHom hδ
  obtain ⟨β, hβ, hβα⟩ := hQ1 τ
  obtain ⟨-, hconj⟩ := hβα g a
  obtain ⟨ψ, hψ, -⟩ := hconj α hαg (by rw [← sq]; exact hα)
  have hψ' : ψ * α * ψ⁻¹ = β := MulEquiv.ext fun u => Subtype.ext ((hψ u).trans (hβ u).symm)
  have hβ2 : β ^ 2 = 1 := by
    rw [← hψ', sq, show ψ * α * ψ⁻¹ * (ψ * α * ψ⁻¹) = ψ * (α * α) * ψ⁻¹ by group, ← sq, hα,
      mul_one, mul_inv_cancel]
  have hδ2 : δ ^ 2 = 1 := pow_eq_one_of_apply_eq_pow δ hKe hδ
  exact outerCoreAt_of_conj hψ'
    (outerCoreTrivAt_entrywise_field hK2 δ hδ hδ2 hNF hNFk hΓJ hβ hβ2).outerCoreAt

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
