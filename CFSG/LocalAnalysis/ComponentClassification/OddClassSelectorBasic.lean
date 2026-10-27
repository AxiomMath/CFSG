module

public import CFSG.LocalAnalysis.ComponentClassification.RestrictedStdInputs
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocleSteps
public import CFSG.LieType.CurtisTits.Conclusion
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI

public noncomputable section

namespace CFSG.ComponentClassification.OddClassSelector

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Witness

variable {P : Type*} [Group P]

@[expose] def NoTightWitness (X : Subgroup P) : Prop :=
  ∀ t g : P, orderOf t = 2 → (∀ x ∈ X, x * t = t * x) → g * t = t * g →
    g ∈ normalizer (X : Set P)

theorem mem_normalizer_of_isStandardSubgroup {G : Type*} [Group G] {L : Subgroup G}
    (hL : CFSG.IsStandardSubgroup L) {t g : G} (ht : orderOf t = 2)
    (htL : ∀ x ∈ L, x * t = t * x) (hgt : g * t = t * g) : g ∈ normalizer (L : Set G) :=
  CFSG.Open.standardComponentIsStandard.mem_normalizer_of_commute
    (CFSG.IsStandardSubgroup.standardComponentIsStandard hL)
    (mem_centralizer_iff.mpr fun x hx => htL x hx) ht hgt

theorem mem_map_conj_iff (hcj : Function.Injective (MulAut.conj : P →* MulAut P))
    (J : Subgroup P) (x : P) : MulAut.conj x ∈ J.map MulAut.conj ↔ x ∈ J := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    rwa [← hcj hxy]
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem noTightWitness_of_isStandardSubgroup {A : Type*} [Group A] {ρ : A →* MulAut P}
    (hinj : Function.Injective ρ) (hinn : inner P ≤ ρ.range)
    (hcj : Function.Injective (MulAut.conj : P →* MulAut P)) {L : Subgroup A}
    (hstd : CFSG.IsStandardSubgroup L) {X : Subgroup P} (hLX : L.map ρ = X.map MulAut.conj) :
    NoTightWitness X := by
  intro t g ht htX hgt
  obtain ⟨tA, htA⟩ := hinn ⟨t, rfl⟩
  obtain ⟨gA, hgA⟩ := hinn ⟨g, rfl⟩
  have hmemL : ∀ y ∈ X, ∃ x ∈ L, ρ x = MulAut.conj y := fun y hy => by
    have : MulAut.conj y ∈ L.map ρ := hLX ▸ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hxy⟩ := this
    exact ⟨x, hx, hxy⟩
  have hmemX : ∀ x ∈ L, ∃ y ∈ X, ρ x = MulAut.conj y := fun x hx => by
    have : ρ x ∈ X.map MulAut.conj := hLX ▸ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := this
    exact ⟨y, hy, hxy.symm⟩
  have htA2 : orderOf tA = 2 := by
    rw [← orderOf_injective ρ hinj tA, htA, orderOf_injective _ hcj t, ht]
  have htAL : ∀ x ∈ L, x * tA = tA * x := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hmemX x hx
    apply hinj
    rw [map_mul, map_mul, hxy, htA, ← map_mul, ← map_mul, htX y hy]
  have hgtA : gA * tA = tA * gA := by
    apply hinj
    rw [map_mul, map_mul, htA, hgA, ← map_mul, ← map_mul, hgt]
  have hN := mem_normalizer_of_isStandardSubgroup hstd htA2 htAL hgtA
  rw [mem_normalizer_iff] at hN ⊢
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx, hxy⟩ := hmemL y hy
    obtain ⟨y', hy', hxy'⟩ := hmemX _ ((hN x).mp hx)
    rw [map_mul, map_mul, map_inv, hgA, hxy, ← map_inv, ← map_mul, ← map_mul] at hxy'
    rwa [hcj hxy']
  · intro hy
    obtain ⟨x, hx, hxy⟩ := hmemL _ hy
    have hx' : gA⁻¹ * x * gA ∈ L := by
      rw [hN]
      simpa [mul_assoc] using hx
    obtain ⟨y', hy', hxy'⟩ := hmemX _ hx'
    rw [map_mul, map_mul, map_inv, hgA, hxy, ← map_inv, ← map_mul, ← map_mul] at hxy'
    have : y = y' := hcj (by rw [← hxy']; group)
    rwa [this]

theorem NoTightWitness.map {P' : Type*} [Group P'] {X : Subgroup P} (hX : NoTightWitness X)
    (e : P ≃* P') : NoTightWitness (X.map e.toMonoidHom) := by
  intro t g ht htX hgt
  have ht' : orderOf (e.symm t) = 2 := by rw [MulEquiv.orderOf_eq, ht]
  have htX' : ∀ x ∈ X, x * e.symm t = e.symm t * x := by
    intro x hx
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact htX (e x) ⟨x, hx, rfl⟩
  have hgt' : e.symm g * e.symm t = e.symm t * e.symm g := by
    rw [← map_mul, ← map_mul, hgt]
  have hN := hX (e.symm t) (e.symm g) ht' htX' hgt'
  rw [mem_normalizer_iff] at hN ⊢
  intro y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨e.symm g * x * (e.symm g)⁻¹, (hN x).mp hx, ?_⟩
    simp
  · rintro ⟨x, hx, hxy⟩
    refine ⟨e.symm y, (hN (e.symm y)).mpr ?_, by simp⟩
    have : e.symm g * e.symm y * (e.symm g)⁻¹ = x := by
      rw [← map_inv, ← map_mul, ← map_mul]
      change e.symm (g * y * g⁻¹) = x
      rw [← hxy]
      simp
    rw [this]
    exact hx

end Witness

section Fixed

variable {P : Type*} [Group P]

theorem conj_mem_centralizer_iff (hcj : Function.Injective (MulAut.conj : P →* MulAut P))
    (α : MulAut P) (x : P) : MulAut.conj x ∈ centralizer {α} ↔ x ∈ fixedSubgroup α := by
  rw [mem_centralizer_singleton_iff]
  change _ ↔ α x = x
  constructor
  · intro h
    apply hcj
    ext y
    have := congrArg (fun χ : MulAut P => χ (α y)) h
    simp only [MulAut.mul_apply, MulAut.conj_apply] at this
    rw [MulAut.conj_apply, MulAut.conj_apply]
    have h2 : α (x * y * x⁻¹) = α x * α y * (α x)⁻¹ := by rw [map_mul, map_mul, map_inv]
    calc α x * y * (α x)⁻¹ = α x * α (α.symm y) * (α x)⁻¹ := by rw [MulEquiv.apply_symm_apply]
      _ = α (x * α.symm y * x⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = x * y * x⁻¹ := by
        have h3 := congrArg (fun χ : MulAut P => χ (α.symm y)) h
        simp only [MulAut.mul_apply, MulAut.conj_apply, MulEquiv.apply_symm_apply] at h3
        rw [h3]
  · intro h
    ext y
    simp only [MulAut.mul_apply, MulAut.conj_apply]
    rw [map_mul, map_mul, map_inv, h]

theorem map_conj_fixedSubgroup (hcj : Function.Injective (MulAut.conj : P →* MulAut P))
    (α : MulAut P) : (fixedSubgroup α).map MulAut.conj = inner P ⊓ centralizer {α} := by
  ext χ
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, (conj_mem_centralizer_iff hcj α x).mpr hx⟩
  · rintro ⟨⟨x, rfl⟩, hx⟩
    exact ⟨x, (conj_mem_centralizer_iff hcj α x).mp hx, rfl⟩

theorem isComponentOf_comap_conj (hcj : Function.Injective (MulAut.conj : P →* MulAut P))
    {α : MulAut P} {Y : Subgroup (MulAut P)}
    (hY : CFSG.Assembly.IsComponentOf Y (inner P ⊓ centralizer {α})) :
    CFSG.Assembly.IsComponentOf (Y.comap MulAut.conj) (fixedSubgroup α) ∧
      (Y.comap MulAut.conj).map MulAut.conj = Y := by
  have hYr : Y ≤ (MulAut.conj : P →* MulAut P).range := hY.1.trans inf_le_left
  have hmap : (Y.comap MulAut.conj).map MulAut.conj = Y := Subgroup.map_comap_eq_self hYr
  have hfix : (inner P ⊓ centralizer {α}).comap MulAut.conj = fixedSubgroup α := by
    rw [← map_conj_fixedSubgroup hcj α, Subgroup.comap_map_eq_self_of_injective hcj]
  refine ⟨⟨?_, ?_, ?_⟩, hmap⟩
  · rw [← hfix]
    exact Subgroup.comap_mono hY.1
  · rw [← hfix]
    exact LocalAnalysis.ComponentInitial.assembly_isSubnormal_comap _ hY.2.1
  · have hq := hY.2.2
    rw [AssemblyBPredicates.isQuasisimple_iff_native] at hq ⊢
    have e : ↥(Y.comap MulAut.conj) ≃* ↥Y :=
      ((Y.comap MulAut.conj).equivMapOfInjective _ hcj).trans (MulEquiv.subgroupCongr hmap)
    exact (LocalAnalysis.ComponentInitial.isQuasisimple_congr e).2 hq

end Fixed

section Socle

variable {P : Type*} [Group P]

theorem conj_injective (hZ : center P = ⊥) :
    Function.Injective (MulAut.conj : P →* MulAut P) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxc : x ∈ center P := by
    rw [mem_center_iff]
    intro y
    have h := congrArg (fun χ : MulAut P => χ y) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc y * x = x * y * x⁻¹ * x := by rw [h]
      _ = x * y := by group
  rw [hZ] at hxc
  exact hxc

theorem fixed_component_of_socle {A : Type*} [Group A] {W : Subgroup A} [W.Normal]
    (hCW : centralizer (W : Set A) = ⊥) (θ : W ≃* P) (hZ : center P = ⊥) {a : A}
    {L : Subgroup A} (hL : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a})) :
    ∃ (ρ : A →* MulAut P) (X : Subgroup P), Function.Injective ρ ∧ inner P ≤ ρ.range ∧
      CFSG.Assembly.IsComponentOf X (fixedSubgroup (ρ a)) ∧ L.map ρ = X.map MulAut.conj ∧
      Nonempty (L ≃* X) := by
  have hcj := conj_injective hZ
  obtain ⟨ρ, hinj, hρW, -, -⟩ := OutcomeLocal.socle_extension hCW θ hZ
  obtain ⟨hWimg, hCWimg, -⟩ := OutcomeLocal.socle_images hinj θ hρW a
  have hL₁ := SymmetricLocal.isComponentOf_map_of_injective ρ hinj hL
  rw [hCWimg] at hL₁
  obtain ⟨hX, hXmap⟩ := isComponentOf_comap_conj hcj hL₁
  refine ⟨ρ, (L.map ρ).comap MulAut.conj, hinj, ?_, hX, hXmap.symm, ⟨?_⟩⟩
  · rw [← hWimg]
    exact Subgroup.map_le_range ρ W
  · exact (L.equivMapOfInjective ρ hinj).trans ((MulEquiv.subgroupCongr hXmap.symm).trans
      (((L.map ρ).comap MulAut.conj).equivMapOfInjective _ hcj).symm)

theorem map_symm_fixedSubgroup (α β : MulAut P) :
    (fixedSubgroup α).map β.symm.toMonoidHom = fixedSubgroup (β⁻¹ * α * β) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change β.symm (α (β (β.symm x))) = β.symm x
    rw [MulEquiv.apply_symm_apply]
    exact congrArg β.symm hx
  · intro hy
    refine ⟨β y, ?_, by simp⟩
    change α (β y) = β y
    have h : β.symm (α (β y)) = y := hy
    calc α (β y) = β (β.symm (α (β y))) := by rw [MulEquiv.apply_symm_apply]
      _ = β y := by rw [h]

theorem isComponentOf_map_symm {α : MulAut P} (β : MulAut P) {X : Subgroup P}
    (hX : CFSG.Assembly.IsComponentOf X (fixedSubgroup α)) :
    CFSG.Assembly.IsComponentOf (X.map β.symm.toMonoidHom) (fixedSubgroup (β⁻¹ * α * β)) := by
  rw [← map_symm_fixedSubgroup]
  exact SymmetricLocal.isComponentOf_map_of_injective _ β.symm.injective hX

end Socle

theorem smallSource_of_mulEquiv {A B : Type} [Group A] [Group B] {L : Subgroup A}
    {X : Subgroup B} (e : L ≃* X) (hs : SmallSource L) : SmallSource X := by
  have eZ : L ⧸ center L ≃* X ⧸ center X :=
    QuotientGroup.congr (center L) (center X) e (Subgroup.map_center_eq e)
  have hc : Nat.card (center L) = Nat.card (center X) :=
    Nat.card_congr (Subgroup.centerCongr e).toEquiv
  rcases hs with ⟨p, f, hp, hp2, hf, h5, hm, hodd⟩ | ⟨⟨e7⟩, hodd⟩ | h34
  · exact Or.inl ⟨p, f, hp, hp2, hf, h5, LieType.CurtisTits.lieModel_of_mulEquiv eZ hm,
      hc ▸ hodd⟩
  · exact Or.inr (Or.inl ⟨⟨eZ.symm.trans e7⟩, hc ▸ hodd⟩)
  · exact Or.inr (Or.inr (LieType.CurtisTits.lieModel_of_mulEquiv eZ h34))

theorem statedClassicalModel_of_lieModel_psl {X : Type} [Group X] {n p f : ℕ}
    (h : LieModel X .PSL n p f) : StatedClassicalModel X .PSL n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

theorem exists_source_of_smallSource {A : Type} [Group A] {X : Subgroup A} (hs : SmallSource X) :
    ∃ p f : ℕ, p ≠ 2 ∧
      (StatedClassicalModel (X ⧸ center X) .PSL 2 p f ∨
        Nonempty (X ⧸ center X ≃* alternatingGroup (Fin 7)) ∨
        StatedClassicalModel (X ⧸ center X) .PSL 3 2 2) := by
  rcases hs with ⟨p, f, -, hp2, -, -, hm, -⟩ | ⟨h7, -⟩ | h34
  · exact ⟨p, f, hp2, Or.inl (statedClassicalModel_of_lieModel_psl hm)⟩
  · exact ⟨3, 1, by decide, Or.inr (Or.inl h7)⟩
  · exact ⟨3, 1, by decide, Or.inr (Or.inr (statedClassicalModel_of_lieModel_psl h34))⟩

theorem false_of_smallSource {A : Type} [Group A] {X : Subgroup A} (hs : SmallSource X)
    (hX : (∀ p f : ℕ, p ≠ 2 → ¬ StatedClassicalModel (X ⧸ center X) .PSL 2 p f) ∧
      IsEmpty (X ⧸ center X ≃* alternatingGroup (Fin 7)) ∧
      ¬ StatedClassicalModel (X ⧸ center X) .PSL 3 2 2) : False := by
  obtain ⟨p, f, hp2, hsrc⟩ := exists_source_of_smallSource hs
  rcases hsrc with h | h | h
  · exact hX.1 p f hp2 h
  · exact not_nonempty_iff.mpr hX.2.1 h
  · exact hX.2.2 h

theorem isComponentOf_comap_of_le_range {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) {Y K : Subgroup H} (hY : CFSG.Assembly.IsComponentOf Y K)
    (hK : K ≤ f.range) : CFSG.Assembly.IsComponentOf (Y.comap f) (K.comap f) := by
  have hYr : Y ≤ f.range := hY.1.trans hK
  have hmap : (Y.comap f).map f = Y := Subgroup.map_comap_eq_self hYr
  refine ⟨Subgroup.comap_mono hY.1, LocalAnalysis.ComponentInitial.assembly_isSubnormal_comap _
    hY.2.1, ?_⟩
  have hq := hY.2.2
  rw [AssemblyBPredicates.isQuasisimple_iff_native] at hq ⊢
  have e : ↥(Y.comap f) ≃* ↥Y :=
    ((Y.comap f).equivMapOfInjective _ hf).trans (MulEquiv.subgroupCongr hmap)
  exact (LocalAnalysis.ComponentInitial.isQuasisimple_congr e).2 hq

theorem ker_comp_le_center {H Y Z : Type*} [Group H] [Group Y] [Group Z] (ψ : H →* Y)
    (hψ : Function.Injective ψ) (σ : Y →* Z) (hσk : σ.ker ≤ center Y) :
    (σ.comp ψ).ker ≤ center H := by
  intro x hx
  have h1 : ψ x ∈ center Y := hσk hx
  rw [mem_center_iff]
  intro y
  apply hψ
  rw [map_mul, map_mul]
  exact mem_center_iff.mp h1 (ψ y)

theorem ker_comp_codRestrict_le_center {H G Y Z : Type*} [Group H] [Group G] [Group Y]
    [Group Z] (τ : H →* G) (hτ : ∀ x, (∀ y, τ y * τ x = τ x * τ y) → x ∈ center H)
    {J : Subgroup G} (hJ : ∀ x, τ x ∈ J) (φ : J ≃* Y) (σ : Y →* Z) (hσk : σ.ker ≤ center Y) :
    (σ.comp (φ.toMonoidHom.comp (τ.codRestrict J hJ))).ker ≤ center H := by
  intro x hx
  have h1 : φ (τ.codRestrict J hJ x) ∈ center Y := hσk hx
  refine hτ x fun y => ?_
  have h2 := mem_center_iff.mp h1 (φ (τ.codRestrict J hJ y))
  rw [← map_mul φ, ← map_mul φ] at h2
  exact congrArg Subtype.val (φ.injective h2)

end CFSG.ComponentClassification.OddClassSelector
