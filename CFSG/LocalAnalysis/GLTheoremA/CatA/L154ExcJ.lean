module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154LinAbs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Assembly (LargeEvenInduces)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup glaPComponent_map_fixSubgroup)
open CFSG.ComponentClassification.PerfectAutomorphisms (onCenterQuotient onCenterQuotient_apply_mk)
open scoped commutatorElement

@[expose] noncomputable def l154JImage (p : ℕ) {Ω : Type} [Group Ω] (S J : Subgroup Ω) {C : Type}
    [Group C] (θ : PSimple p S ≃* C) : Subgroup C :=
  (chevTransfer p S J).map θ.toMonoidHom

@[expose] noncomputable def l154JHom (p : ℕ) {Ω : Type} [Group Ω] {S J : Subgroup Ω} (hJS : J ≤ S)
    {C : Type} [Group C] (θ : PSimple p S ≃* C) : ↥J →* C :=
  (θ.toMonoidHom.comp (chevQuotHom p S)).comp (Subgroup.inclusion hJS)

theorem l154JHom_mem {p : ℕ} {Ω : Type} [Group Ω] {S J : Subgroup Ω} (hJS : J ≤ S) {C : Type}
    [Group C] (θ : PSimple p S ≃* C) (l : ↥J) : l154JHom p hJS θ l ∈ l154JImage p S J θ :=
  Subgroup.mem_map.2 ⟨chevQuotHom p S ⟨l.1, hJS l.2⟩,
    Subgroup.mem_map.2 ⟨⟨l.1, hJS l.2⟩, Subgroup.mem_subgroupOf.2 l.2, rfl⟩, rfl⟩

theorem exists_l154JHom_eq {p : ℕ} {Ω : Type} [Group Ω] {S J : Subgroup Ω} (hJS : J ≤ S)
    {C : Type} [Group C] (θ : PSimple p S ≃* C) {z : C} (hz : z ∈ l154JImage p S J θ) :
    ∃ l : ↥J, l154JHom p hJS θ l = z := by
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hz
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hc
  exact ⟨⟨s.1, Subgroup.mem_subgroupOf.1 hs⟩, rfl⟩

theorem l154JHom_ker_le_center {p : ℕ} {Ω : Type} [Group Ω] {S J : Subgroup Ω}
    (hSp : GLAPPrimeCore p ↥S = ⊥) (hJS : J ≤ S) {C : Type} [Group C] (θ : PSimple p S ≃* C) :
    (l154JHom p hJS θ).ker ≤ Subgroup.center ↥J := by
  intro l hl
  rw [MonoidHom.mem_ker] at hl
  have h1 : chevQuotHom p S ⟨l.1, hJS l.2⟩ = 1 := by
    have : θ (chevQuotHom p S ⟨l.1, hJS l.2⟩) = 1 := hl
    exact (map_eq_one_iff _ θ.injective).1 this
  have h2 : (QuotientGroup.mk (⟨l.1, hJS l.2⟩ : ↥S) : PQuot p S) ∈ Subgroup.center (PQuot p S) :=
    (QuotientGroup.eq_one_iff _).1 h1
  have h3 : ∀ s : ↥S, s * ⟨l.1, hJS l.2⟩ = ⟨l.1, hJS l.2⟩ * s := by
    intro s
    have h4 := Subgroup.mem_center_iff.1 h2 (QuotientGroup.mk s)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hSp,
      Subgroup.mem_bot] at h4
    exact inv_mul_eq_one.1 h4
  refine Subgroup.mem_center_iff.2 fun j => Subtype.ext ?_
  have h5 := h3 ⟨j.1, hJS j.2⟩
  show (j : Ω) * (l : Ω) = (l : Ω) * (j : Ω)
  exact congrArg Subtype.val h5

theorem l154JHom_conj {p : ℕ} {Ω : Type} [Group Ω] {S J : Subgroup Ω} {y : Ω} (hJS : J ≤ S)
    {C : Type} [Group C] (θ : PSimple p S ≃* C) (φy : MulAut C)
    (hindy : LargeEvenInduces θ (indRel p S y) φy) {l₁ l₂ : ↥J}
    (h : (l₂ : Ω) = y⁻¹ * l₁ * y) : φy (l154JHom p hJS θ l₁) = l154JHom p hJS θ l₂ :=
  hindy (QuotientGroup.mk ⟨l₁.1, hJS l₁.2⟩) (QuotientGroup.mk ⟨l₂.1, hJS l₂.2⟩)
    ⟨⟨l₁.1, hJS l₁.2⟩, ⟨l₂.1, hJS l₂.2⟩, rfl, rfl, h⟩

theorem l154_JImage_glaPComponent {p : ℕ} (hp : p.Prime) {Ω : Type} [Group Ω] [Finite Ω]
    {S J : Subgroup Ω} {x : Ω} {C : Type} [Group C] (hxp : x ^ p = 1)
    (hxN : x ∈ Subgroup.normalizer (S : Set Ω))
    (hJ : GLAPComponent p (S ⊓ Subgroup.centralizer ({x} : Set Ω)) J)
    (θ : PSimple p S ≃* C) (φx : MulAut C) (hindx : LargeEvenInduces θ (indRel p S x) φx) :
    GLAPComponent p (fixSubgroup φx) (l154JImage p S J θ) := by
  haveI : Finite C := Finite.of_equiv _ θ.toEquiv
  have hφx : φx = MulAut.congr θ (MI.indAut p S x hxN) := (MI.induces_indRel_iff hxN θ).1 hindx
  have hxN' : x⁻¹ ∈ Subgroup.normalizer (S : Set Ω) := Subgroup.inv_mem _ hxN
  have hJ' : GLAPComponent p (S ⊓ Subgroup.centralizer ({x⁻¹} : Set Ω)) J := by
    rw [l154_centralizer_inv_singleton]
    exact hJ
  have hT := glaPComponent_chevTransfer hp hxN'
    (l154_isPGroup_zpowers_of_pow_eq_one (by simp [inv_pow, hxp])) hJ'
  have hcompat : ∀ k : PSimple p S, θ (MI.indAut p S x hxN k) = φx (θ k) := by
    intro k
    rw [hφx]
    simp [MulAut.congr_apply]
  exact glaPComponent_map_fixSubgroup θ.toMonoidHom
    (by rw [(MonoidHom.ker_eq_bot_iff _).2 θ.injective]; exact bot_le) (MI.indAut p S x hxN) φx
    hcompat θ.surjective hp hT

theorem l154_JImage_map {p : ℕ} {Ω : Type} [Group Ω] {S J : Subgroup Ω} {y : Ω} {C : Type}
    [Group C] (hJS : J ≤ S) (hJy : y ∈ Subgroup.normalizer (J : Set Ω)) (θ : PSimple p S ≃* C)
    (φy : MulAut C) (hindy : LargeEvenInduces θ (indRel p S y) φy) :
    (l154JImage p S J θ).map φy.toMonoidHom = l154JImage p S J θ := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨l, rfl⟩ := exists_l154JHom_eq hJS θ hw
    have hmem : y⁻¹ * (l : Ω) * y ∈ J := (Subgroup.mem_normalizer_iff''.1 hJy l).1 l.2
    show φy (l154JHom p hJS θ l) ∈ _
    rw [l154JHom_conj hJS θ φy hindy (l₂ := ⟨y⁻¹ * (l : Ω) * y, hmem⟩) rfl]
    exact l154JHom_mem hJS θ _
  · intro hz
    obtain ⟨l, rfl⟩ := exists_l154JHom_eq hJS θ hz
    have hmem : y * (l : Ω) * y⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 hJy l).1 l.2
    refine ⟨l154JHom p hJS θ ⟨y * (l : Ω) * y⁻¹, hmem⟩, l154JHom_mem hJS θ _, ?_⟩
    show φy (l154JHom p hJS θ ⟨y * (l : Ω) * y⁻¹, hmem⟩) = _
    refine l154JHom_conj hJS θ φy hindy (l₁ := ⟨y * (l : Ω) * y⁻¹, hmem⟩) (l₂ := l) ?_
    show (l : Ω) = y⁻¹ * (y * (l : Ω) * y⁻¹) * y
    group

theorem l154_JImage_equiv {p : ℕ} (hp : p.Prime) {Ω : Type} [Group Ω] [Finite Ω]
    {S J : Subgroup Ω} {y : Ω} {C : Type} [Group C] (hSp : GLAPPrimeCore p ↥S = ⊥)
    {X : Subgroup Ω} (hJ : GLAPComponent p X J) (hJS : J ≤ S)
    (hJy : y ∈ Subgroup.normalizer (J : Set Ω)) (θ : PSimple p S ≃* C) (φy : MulAut C)
    (hindy : LargeEvenInduces θ (indRel p S y) φy)
    (hq : CFSG.Open.IsQuasisimple ↥(l154JImage p S J θ)) :
    ∃ (ψJ : MulAut ↥(l154JImage p S J θ))
      (e₀ : PSimple p J ≃* (↥(l154JImage p S J θ) ⧸ Subgroup.center ↥(l154JImage p S J θ))),
      (∀ j : ↥(l154JImage p S J θ), (ψJ j : C) = φy j) ∧
      ∀ s : PSimple p J, e₀ (MI.indAut p J y hJy s) = onCenterQuotient ψJ (e₀ s) := by
  set JI : Subgroup C := l154JImage p S J θ with hJI
  let ρ' : ↥J →* ↥JI := (l154JHom p hJS θ).codRestrict JI (l154JHom_mem hJS θ)
  let Θ : ↥J →* ↥JI ⧸ Subgroup.center ↥JI := (QuotientGroup.mk' (Subgroup.center ↥JI)).comp ρ'
  have hρ'surj : Function.Surjective ρ' := fun z => by
    obtain ⟨l, hl⟩ := exists_l154JHom_eq hJS θ z.2
    exact ⟨l, Subtype.ext hl⟩
  have hΘsurj : Function.Surjective Θ := (QuotientGroup.mk'_surjective _).comp hρ'surj
  have hperfJ : commutator ↥J = ⊤ :=
    (Subgroup.isPerfect_iff.2 (glaPComponent_perfect hJ)).commutator_eq_top
  have hΘker : Θ.ker ≤ Subgroup.center ↥J := by
    intro l hl
    have hc : ρ' l ∈ Subgroup.center ↥JI := (QuotientGroup.eq_one_iff (ρ' l)).1 hl
    refine Y10GInnLin.mem_center_of_commutator_mem_center hperfJ fun j => ?_
    apply l154JHom_ker_le_center hSp hJS θ
    have hcomm : l154JHom p hJS θ l * l154JHom p hJS θ j =
        l154JHom p hJS θ j * l154JHom p hJS θ l :=
      congrArg Subtype.val (Subgroup.mem_center_iff.1 hc (ρ' j)).symm
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm
  obtain ⟨e₀, he₀⟩ := l154_exists_pSimple_equiv hp hJ hq.2 Θ hΘsurj hΘker
  have hmap : JI.map φy.toMonoidHom = JI := l154_JImage_map hJS hJy θ φy hindy
  let ψJ : MulAut ↥JI := (φy.subgroupMap JI).trans (MulEquiv.subgroupCongr hmap)
  refine ⟨ψJ, e₀, fun j => rfl, fun s => ?_⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective s
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective a
  let l' : ↥J := ⟨y⁻¹ * (l : Ω) * y, (Subgroup.mem_normalizer_iff''.1 hJy l).1 l.2⟩
  have e3 : MI.indAut p J y hJy (QuotientGroup.mk (QuotientGroup.mk l)) =
      QuotientGroup.mk (QuotientGroup.mk l') := MI.indAut_apply_mk hJy ⟨l, l', rfl, rfl, rfl⟩
  rw [e3, he₀ l', he₀ l]
  show (QuotientGroup.mk' (Subgroup.center ↥JI)) (ρ' l') =
    onCenterQuotient ψJ ((QuotientGroup.mk' (Subgroup.center ↥JI)) (ρ' l))
  rw [onCenterQuotient_apply_mk]
  exact congrArg (QuotientGroup.mk' (Subgroup.center ↥JI))
    (Subtype.ext (l154JHom_conj hJS θ φy hindy (l₁ := l) (l₂ := l') rfl).symm)

end CFSG.LocalAnalysis.GLTheoremA.K155X
