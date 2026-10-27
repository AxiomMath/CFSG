module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Uniform.U5Comp
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM289

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Generic.DeltaClosure

section OddCore

variable {A B : Type*} [Group A] [Group B]

theorem oddCore_map_le (φ : A ≃* B) :
    (classicalInvolutionOddCore A).map φ.toMonoidHom ≤ classicalInvolutionOddCore B := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun N hN => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  refine le_sSup ⟨hN.1.map φ.toMonoidHom φ.surjective, ?_⟩
  have h : Nat.card (N.map φ.toMonoidHom) = Nat.card N :=
    Nat.card_congr (N.equivMapOfInjective φ.toMonoidHom φ.injective).symm.toEquiv
  rw [h]
  exact hN.2

theorem oddCore_map_mulEquiv (φ : A ≃* B) :
    (classicalInvolutionOddCore A).map φ.toMonoidHom = classicalInvolutionOddCore B := by
  refine le_antisymm (oddCore_map_le φ) ?_
  have h2 := Subgroup.map_mono (f := φ.toMonoidHom) (oddCore_map_le φ.symm)
  rwa [Subgroup.map_map, show φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id B from
    MonoidHom.ext fun x => φ.apply_symm_apply x, Subgroup.map_id] at h2

end OddCore

section Transport

variable {ι : Type} {Y Y' : Type} [Group Y] [Group Y']

@[expose] noncomputable def LieSystemData3.congrEquiv {Φ : Set (Subgroup Y)}
    {Φ' : Set (Subgroup Y')} (ψ : Y ≃* Y') (hΦ : ∀ L ∈ Φ', ∃ L₀ ∈ Φ, L = L₀.map ψ.toMonoidHom)
    (hΦ' : ∀ L₀ ∈ Φ, L₀.map ψ.toMonoidHom ∈ Φ') (D : LieSystemData3 ι Y Φ) :
    LieSystemData3 ι Y' Φ' where
  kind := D.kind
  valid := D.valid
  hom i := ψ.toMonoidHom.comp (D.hom i)
  ker_le_center i := by
    intro x hx
    have h1 : D.hom i x = 1 := by
      have : ψ (D.hom i x) = 1 := hx
      exact ψ.injective (by rw [this, map_one])
    exact D.ker_le_center i h1
  commute i j hij x y := by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, D.commute i j hij x y]
  generate := by
    have h : ∀ i, (ψ.toMonoidHom.comp (D.hom i)).range = (D.hom i).range.map ψ.toMonoidHom :=
      fun i => MonoidHom.range_comp _ _
    simp only [h]
    rw [← Subgroup.map_iSup, D.generate]
    exact Subgroup.map_top_of_surjective _ ψ.surjective
  fundamental L' hL' := by
    obtain ⟨L₀, hL₀, rfl⟩ := hΦ L' hL'
    obtain ⟨i, R, hR, hLR⟩ := D.fundamental L₀ hL₀
    exact ⟨i, R, hR, by rw [hLR, Subgroup.map_map]⟩
  meets i := by
    obtain ⟨R, hR, hRΦ⟩ := D.meets i
    refine ⟨R, hR, ?_⟩
    have := hΦ' _ hRΦ
    rwa [Subgroup.map_map] at this
  card_eq L' hL' := by
    obtain ⟨L₀, hL₀, rfl⟩ := hΦ L' hL'
    rw [← D.card_eq L₀ hL₀]
    exact Nat.card_congr (L₀.equivMapOfInjective ψ.toMonoidHom ψ.injective).symm.toEquiv

end Transport

section Conj

variable {G : Type} [Group G]

@[expose] noncomputable def conjIso (Y : Subgroup G) (g : G) : ↥Y ≃* ↥(conjSub g Y) :=
  (MulAut.conj g).subgroupMap Y

@[expose] noncomputable def conjSect (Y : Subgroup G) (g : G) :
    ↥Y ⧸ classicalInvolutionOddCore ↥Y ≃*
      ↥(conjSub g Y) ⧸ classicalInvolutionOddCore ↥(conjSub g Y) :=
  QuotientGroup.congr _ _ (conjIso Y g) (oddCore_map_mulEquiv (conjIso Y g))

theorem conjSect_comp_mk (Y : Subgroup G) (g : G) :
    (conjSect Y g).toMonoidHom.comp (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)) =
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(conjSub g Y))).comp
        (conjIso Y g).toMonoidHom :=
  MonoidHom.ext fun _ => rfl

theorem subgroupOf_map_conjIso {Y L : Subgroup G} (hLY : L ≤ Y) (g : G) :
    (L.subgroupOf Y).map (conjIso Y g).toMonoidHom =
      (conjSub g L).subgroupOf (conjSub g Y) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr ⟨(a : G), Subgroup.mem_subgroupOf.mp ha, rfl⟩
  · intro hx
    obtain ⟨l, hl, hlx⟩ := Subgroup.mem_subgroupOf.mp hx
    refine ⟨⟨l, hLY hl⟩, Subgroup.mem_subgroupOf.mpr hl, ?_⟩
    exact Subtype.ext hlx

theorem modOddIn_map_conjSect {Y L : Subgroup G} (hLY : L ≤ Y) (g : G) :
    (modOddIn Y L).map (conjSect Y g).toMonoidHom = modOddIn (conjSub g Y) (conjSub g L) := by
  unfold modOddIn
  rw [Subgroup.map_map, conjSect_comp_mk, ← Subgroup.map_map, subgroupOf_map_conjIso hLY g]

noncomputable def lieSystemData3_conj {ι : Type} {Y : Subgroup G} (g : G) {F₁ F₂ : Set (Subgroup G)}
    (h12 : ∀ L ∈ F₁, conjSub g L ∈ F₂) (h21 : ∀ L ∈ F₂, conjSub g⁻¹ L ∈ F₁)
    (D : LieSystemData3 ι (↥Y ⧸ classicalInvolutionOddCore ↥Y)
      (oddQuotientFamily (restrictFamily F₁ Y))) :
    LieSystemData3 ι (↥(conjSub g Y) ⧸ classicalInvolutionOddCore ↥(conjSub g Y))
      (oddQuotientFamily (restrictFamily F₂ (conjSub g Y))) :=
  LieSystemData3.congrEquiv (conjSect Y g)
    (by
      rintro L' ⟨_, ⟨M, hM, hMY, rfl⟩, rfl⟩
      have hL₀ : conjSub g⁻¹ M ∈ F₁ := h21 M hM
      have hL₀Y : conjSub g⁻¹ M ≤ Y := by
        have := conjSub_mono (n := g⁻¹) hMY
        rwa [conjSub_inv_conjSub] at this
      refine ⟨modOddIn Y (conjSub g⁻¹ M), ⟨_, ⟨conjSub g⁻¹ M, hL₀, hL₀Y, rfl⟩, rfl⟩, ?_⟩
      rw [modOddIn_map_conjSect hL₀Y g, conjSub_conjSub_inv]
      rfl)
    (by
      rintro _ ⟨_, ⟨M, hM, hMY, rfl⟩, rfl⟩
      have h := modOddIn_map_conjSect hMY g
      exact ⟨_, ⟨conjSub g M, h12 M hM, conjSub_mono hMY, rfl⟩, h.symm⟩)
    D

theorem exists_lieSystem_conj_of_eq {Y Y' : Subgroup G} (g : G) (hY' : Y' = conjSub g Y)
    {F₁ F₂ : Set (Subgroup G)} (h12 : ∀ L ∈ F₁, conjSub g L ∈ F₂)
    (h21 : ∀ L ∈ F₂, conjSub g⁻¹ L ∈ F₁) (P : CompData → Prop)
    (h : ∃ (ι : Type) (_ : Finite ι) (D : LieSystemData3 ι (↥Y ⧸ classicalInvolutionOddCore ↥Y)
        (oddQuotientFamily (restrictFamily F₁ Y))), ∃ i₁ : ι, (∀ i, i = i₁) ∧ P (D.kind i₁)) :
    ∃ (ι : Type) (_ : Finite ι) (D : LieSystemData3 ι (↥Y' ⧸ classicalInvolutionOddCore ↥Y')
        (oddQuotientFamily (restrictFamily F₂ Y'))), ∃ i₁ : ι, (∀ i, i = i₁) ∧ P (D.kind i₁) := by
  subst hY'
  obtain ⟨ι, hι, D, i₁, hi, hk⟩ := h
  exact ⟨ι, hι, lieSystemData3_conj g h12 h21 D, i₁, hi, hk⟩

end Conj

end CFSG.ClassicalInvolution.Q3.Q3AM289
