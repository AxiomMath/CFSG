module

public import CFSG.ClassicalInvolution.Q3.LieSystem

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

section Plain

variable {G : Type} [Group G]

theorem centralizingMembers_conj_image {Λ Λ' : Set (Subgroup G)} {g : G}
    (hΛ : Λ' = conjSub g '' Λ) (a : G) :
    centralizingMembers Λ' {g * a * g⁻¹} = conjSub g '' centralizingMembers Λ {a} := by
  subst hΛ
  ext L
  constructor
  · rintro ⟨⟨L₀, hL₀, rfl⟩, hLC⟩
    refine ⟨L₀, ⟨hL₀, fun y hy => ?_⟩, rfl⟩
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hLC (conj_mem_conjSub hy))
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * a = g⁻¹ * ((g * y * g⁻¹) * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * a * g⁻¹) * (g * y * g⁻¹)) * g := by rw [h]
      _ = a * y := by group
  · rintro ⟨L₀, ⟨hL₀, hL₀C⟩, rfl⟩
    refine ⟨⟨L₀, hL₀, rfl⟩, fun x hx => ?_⟩
    rw [mem_conjSub_iff] at hx
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hL₀C hx)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * (g * a * g⁻¹) = g * ((g⁻¹ * x * g) * a) * g⁻¹ := by group
      _ = g * (a * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
      _ = (g * a * g⁻¹) * x := by group

theorem centralizingLayer_conj_image {Λ Λ' : Set (Subgroup G)} {g : G}
    (hΛ : Λ' = conjSub g '' Λ) (a : G) :
    centralizingLayer Λ' {g * a * g⁻¹} = conjSub g (centralizingLayer Λ {a}) := by
  show _ = (centralizingLayer Λ {a}).map (MulAut.conj g).toMonoidHom
  unfold centralizingLayer
  rw [centralizingMembers_conj_image hΛ, Subgroup.map_iSup, iSup_image]
  refine iSup_congr fun L => ?_
  rw [Subgroup.map_iSup]
  rfl

@[expose] noncomputable def conjLayerEquiv (g : G) {Y Y' : Subgroup G} (h : Y' = conjSub g Y) :
    ↥Y ≃* ↥Y' :=
  ((MulAut.conj g).subgroupMap Y).trans (MulEquiv.subgroupCongr h.symm)

theorem coe_conjLayerEquiv (g : G) {Y Y' : Subgroup G} (h : Y' = conjSub g Y) (y : ↥Y) :
    ((conjLayerEquiv g h y : ↥Y') : G) = g * y * g⁻¹ := rfl

@[expose] noncomputable def conjQuotEquiv (g : G) {Y Y' : Subgroup G} (h : Y' = conjSub g Y) :
    (↥Y ⧸ classicalInvolutionOddCore ↥Y) ≃* (↥Y' ⧸ classicalInvolutionOddCore ↥Y') :=
  QuotientGroup.congr _ _ (conjLayerEquiv g h)
    (CFSG.ComponentClassification.OddCore.equiv_invariant (conjLayerEquiv g h))

theorem map_subgroupOf_conjLayerEquiv (g : G) {Y Y' : Subgroup G} (h : Y' = conjSub g Y)
    (L : Subgroup G) :
    (L.subgroupOf Y).map (conjLayerEquiv g h).toMonoidHom = (conjSub g L).subgroupOf Y' := by
  ext y'
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy2 : (y : G) ∈ L := hy
    show g * (y : G) * g⁻¹ ∈ conjSub g L
    rw [mem_conjSub_iff]
    simpa [mul_assoc] using hy2
  · intro hy'
    refine ⟨(conjLayerEquiv g h).symm y', ?_, (conjLayerEquiv g h).apply_symm_apply y'⟩
    have hy2 : g⁻¹ * (y' : G) * g ∈ L := mem_conjSub_iff.mp hy'
    have : ((conjLayerEquiv g h).symm y' : G) = g⁻¹ * (y' : G) * g := by
      have h1 := coe_conjLayerEquiv g h ((conjLayerEquiv g h).symm y')
      rw [(conjLayerEquiv g h).apply_symm_apply] at h1
      rw [h1]
      group
    show ((conjLayerEquiv g h).symm y' : G) ∈ L
    rw [this]
    exact hy2

theorem map_oddQuotientFamily_conj {Λ Λ' : Set (Subgroup G)} {g : G} {Y Y' : Subgroup G}
    (hY : Y' = conjSub g Y) (hΛ : Λ' = conjSub g '' Λ) :
    Subgroup.map (conjQuotEquiv g hY).toMonoidHom '' oddQuotientFamily (restrictFamily Λ Y) =
      oddQuotientFamily (restrictFamily Λ' Y') := by
  have key : ∀ L : Subgroup G,
      Subgroup.map (conjQuotEquiv g hY).toMonoidHom
          (Subgroup.map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)) (L.subgroupOf Y)) =
        Subgroup.map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y'))
          ((conjSub g L).subgroupOf Y') := by
    intro L
    rw [← map_subgroupOf_conjLayerEquiv g hY L, Subgroup.map_map, Subgroup.map_map]
    rfl
  ext K'
  constructor
  · rintro ⟨_, ⟨_, ⟨L, hL, hLY, rfl⟩, rfl⟩, rfl⟩
    have hLY' : conjSub g L ≤ Y' := by
      rw [hY]
      exact conjSub_mono hLY
    exact ⟨(conjSub g L).subgroupOf Y', ⟨conjSub g L, by rw [hΛ]; exact ⟨L, hL, rfl⟩, hLY', rfl⟩,
      (key L).symm⟩
  · rintro ⟨_, ⟨L', hL', hL'Y, rfl⟩, rfl⟩
    rw [hΛ] at hL'
    obtain ⟨L, hL, rfl⟩ := hL'
    have hLY : L ≤ Y := by
      rw [hY] at hL'Y
      have := conjSub_mono (n := g⁻¹) hL'Y
      rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
    exact ⟨_, ⟨_, ⟨L, hL, hLY, rfl⟩, rfl⟩, key L⟩

end Plain

section Lie

variable {ι : Type} {X : Type} [Group X] {Φ : Set (Subgroup X)}

@[expose] def ShapeSingle (D : LieSystemData3 ι X Φ) (c : CompData) (zb : X) : Prop :=
  ∃ i₁ : ι, (∀ i, i = i₁) ∧ D.kind i₁ = c ∧
    ∃ f ∈ Subgroup.center (D.kind i₁).G, D.hom i₁ f = zb

@[expose] noncomputable def lieSystemTransport {X' : Type} [Group X'] (e : X ≃* X')
    (D : LieSystemData3 ι X Φ) : LieSystemData3 ι X' (Subgroup.map e.toMonoidHom '' Φ) where
  kind := D.kind
  valid := D.valid
  hom i := e.toMonoidHom.comp (D.hom i)
  ker_le_center i := by
    intro x hx
    have h1 : D.hom i x = 1 := by
      have h2 : e (D.hom i x) = 1 := hx
      simpa using h2
    exact D.ker_le_center i (by simpa using h1)
  commute i j h x y := by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← map_mul]
    rw [D.commute i j h x y]
  generate := by
    have h1 : ∀ i, (e.toMonoidHom.comp (D.hom i)).range = (D.hom i).range.map e.toMonoidHom :=
      fun i => MonoidHom.range_comp _ _
    simp only [h1]
    rw [← Subgroup.map_iSup, D.generate, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr e.surjective
  fundamental := by
    rintro _ ⟨L, hL, rfl⟩
    obtain ⟨i, R, hR, rfl⟩ := D.fundamental L hL
    exact ⟨i, R, hR, Subgroup.map_map _ _ _⟩
  meets i := by
    obtain ⟨R, hR, hmem⟩ := D.meets i
    exact ⟨R, hR, ⟨_, hmem, Subgroup.map_map _ _ _⟩⟩
  card_eq := by
    rintro _ ⟨L, hL, rfl⟩
    rw [← D.card_eq L hL]
    exact Nat.card_congr (L.equivMapOfInjective e.toMonoidHom e.injective).toEquiv.symm

theorem ShapeSingle.conj_exists {X' : Type} [Group X'] {Φ' : Set (Subgroup X')} (e : X ≃* X')
    (h : Subgroup.map e.toMonoidHom '' Φ = Φ') (D : LieSystemData3 ι X Φ) {c : CompData}
    {zb : X} (hS : ShapeSingle D c zb) :
    ∃ D' : LieSystemData3 ι X' Φ', ShapeSingle D' c (e zb) := by
  subst h
  obtain ⟨i₁, hall, hk, f, hf, hfz⟩ := hS
  exact ⟨lieSystemTransport e D, i₁, hall, hk, f, hf, congrArg e hfz⟩

end Lie

end CFSG.ClassicalInvolution.Q3.Q3AM
