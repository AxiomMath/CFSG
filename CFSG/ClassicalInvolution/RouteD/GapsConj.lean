module

public import CFSG.ClassicalInvolution.RouteD.LocalPair

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem locLayer_conj {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (g x : G) :
    locLayer Ω (g * x * g⁻¹) = (locLayer Ω x).map (MulAut.conj g).toMonoidHom := by
  unfold locLayer centralizingLayer
  rw [centralizingMembers_conj hΩ, Subgroup.map_iSup, iSup_image]
  refine iSup_congr fun L => ?_
  rw [Subgroup.map_iSup]
  rfl

@[expose] noncomputable def locLayerConj {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (g x : G) :
    ↥(locLayer Ω x) ≃* ↥(locLayer Ω (g * x * g⁻¹)) :=
  ((MulAut.conj g).subgroupMap (locLayer Ω x)).trans
    (MulEquiv.subgroupCongr (locLayer_conj hΩ g x).symm)

theorem coe_locLayerConj {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (g x : G)
    (y : ↥(locLayer Ω x)) : ((locLayerConj hΩ g x y : ↥(locLayer Ω (g * x * g⁻¹))) : G) =
      g * y * g⁻¹ := rfl

@[expose] noncomputable def locQuotConj {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (g x : G) :
    locQuot Ω x ≃* locQuot Ω (g * x * g⁻¹) :=
  QuotientGroup.congr _ _ (locLayerConj hΩ g x)
    (CFSG.ComponentClassification.OddCore.equiv_invariant (locLayerConj hΩ g x))

theorem locQuotConj_mk {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (g x : G)
    (y : ↥(locLayer Ω x)) :
    locQuotConj hΩ g x (QuotientGroup.mk y) = QuotientGroup.mk (locLayerConj hΩ g x y) := rfl

theorem map_subgroupOf_locLayerConj {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (g x : G)
    (L : Subgroup G) :
    (L.subgroupOf (locLayer Ω x)).map (locLayerConj hΩ g x).toMonoidHom =
      (conjSub g L).subgroupOf (locLayer Ω (g * x * g⁻¹)) := by
  ext y'
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy2 : (y : G) ∈ L := hy
    show g * (y : G) * g⁻¹ ∈ conjSub g L
    rw [mem_conjSub_iff]
    simpa [mul_assoc] using hy2
  · intro hy'
    refine ⟨(locLayerConj hΩ g x).symm y', ?_, (locLayerConj hΩ g x).apply_symm_apply y'⟩
    have hy2 : g⁻¹ * (y' : G) * g ∈ L := mem_conjSub_iff.mp hy'
    have : ((locLayerConj hΩ g x).symm y' : G) = g⁻¹ * (y' : G) * g := by
      have h1 := coe_locLayerConj hΩ g x ((locLayerConj hΩ g x).symm y')
      rw [(locLayerConj hΩ g x).apply_symm_apply] at h1
      rw [h1]; group
    show ((locLayerConj hΩ g x).symm y' : G) ∈ L
    rw [this]
    exact hy2

theorem locImg_conj {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (g x : G) (L : Subgroup G) :
    locImg Ω (g * x * g⁻¹) (conjSub g L) =
      (locImg Ω x L).map (locQuotConj hΩ g x).toMonoidHom := by
  unfold locImg
  rw [← map_subgroupOf_locLayerConj hΩ g x L, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem locFamily_conj {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (g x : G) :
    Subgroup.map (locQuotConj hΩ g x).toMonoidHom '' locFamily Ω x =
      locFamily Ω (g * x * g⁻¹) := by
  rw [locFamily_eq_image, locFamily_eq_image, centralizingMembers_conj hΩ, Set.image_image,
    Set.image_image]
  exact Set.image_congr fun L _ => (locImg_conj hΩ g x L).symm

@[expose] noncomputable def transportLie {f : ℕ} {X X' : Type} [Group X] [Group X']
    {Φ : Set (Subgroup X)} (e : X ≃* X') (D : LieSystemData p f X Φ) :
    LieSystemData p f X' (Subgroup.map e.toMonoidHom '' Φ) where
  card := D.card
  tag := D.tag
  rank := D.rank
  exp := D.exp
  hom i := e.toMonoidHom.comp (D.hom i)
  isFundTag := D.isFundTag
  admissible := D.admissible
  exp_eq := D.exp_eq
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

theorem exists_lieSystemData_of_image_eq {f : ℕ} {X X' : Type} [Group X] [Group X']
    (e : X ≃* X') {Φ : Set (Subgroup X)} {Φ' : Set (Subgroup X')}
    (h : Subgroup.map e.toMonoidHom '' Φ = Φ') (D : LieSystemData p f X Φ) :
    ∃ D' : LieSystemData p f X' Φ', ∃ hc : D'.card = D.card, ∀ i : Fin D.card,
      D'.tag (Fin.cast hc.symm i) = D.tag i ∧ D'.rank (Fin.cast hc.symm i) = D.rank i ∧
        D'.exp (Fin.cast hc.symm i) = D.exp i := by
  subst h
  exact ⟨transportLie e D, rfl, fun i => ⟨rfl, rfl, rfl⟩⟩

theorem exists_lieSystemData_conj {f : ℕ} {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (g x : G)
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) :
    ∃ D' : LieSystemData p f (locQuot Ω (g * x * g⁻¹)) (locFamily Ω (g * x * g⁻¹)),
      ∃ h : D'.card = D.card, ∀ i : Fin D.card, D'.tag (Fin.cast h.symm i) = D.tag i ∧
        D'.rank (Fin.cast h.symm i) = D.rank i ∧ D'.exp (Fin.cast h.symm i) = D.exp i :=
  exists_lieSystemData_of_image_eq (locQuotConj hΩ g x) (locFamily_conj hΩ g x) D

theorem localOddCentral_conj {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (g x : G)
    (h : LocalOddCentral Ω {x}) : LocalOddCentral Ω {g * x * g⁻¹} := by
  have hO : (classicalInvolutionOddCore ↥(locLayer Ω x)).map (locLayerConj hΩ g x).toMonoidHom =
      classicalInvolutionOddCore ↥(locLayer Ω (g * x * g⁻¹)) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant (locLayerConj hΩ g x)
  intro z hz
  have hz' : z ∈ (classicalInvolutionOddCore ↥(locLayer Ω x)).map
      (locLayerConj hΩ g x).toMonoidHom := by
    rw [hO]; exact hz
  obtain ⟨z₀, hz₀, rfl⟩ := hz'
  rw [Subgroup.mem_center_iff]
  intro y'
  obtain ⟨y, rfl⟩ := (locLayerConj hΩ g x).surjective y'
  have := Subgroup.mem_center_iff.mp (h hz₀) y
  show locLayerConj hΩ g x y * locLayerConj hΩ g x z₀ =
    locLayerConj hΩ g x z₀ * locLayerConj hΩ g x y
  rw [← map_mul, ← map_mul, this]

end CFSG.ClassicalInvolution.RouteD.Gaps
