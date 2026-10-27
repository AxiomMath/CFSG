module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductN1Layer
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.FieldCaseSylow
public import CFSG.LocalAnalysis.EvenBN.Common.SL2CentralTwoSplit
public import CFSG.LocalAnalysis.EvenBN.Common.SL2Module
public import CFSG.LocalAnalysis.EvenBN.Common.CoprimeQuotient
public import CFSG.LocalAnalysis.EvenBN.Common.ProductSplitAmbient
public import CFSG.LocalAnalysis.EvenBN.U5.PrelimModules
public import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusNine
public import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusFive
public import CFSG.LocalAnalysis.EvenBN.Common.Diagonal
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.H13.J4Order
public import CFSG.LocalAnalysis.ABGTheoremB.Basic
public import CFSG.Quasithin.H13.J4OrderBase

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.LocalAnalysis.EvenBN.Common
open CFSG.ABGLocalTools (IsSylowOf)
open scoped MatrixGroups Pointwise commutatorElement

namespace ProductN1Aux

section Generic

variable {G : Type*} [Group G]

@[expose] def conjAutOfNormalizer (P : Subgroup G) {g : G} (hg : g ∈ normalizer (P : Set G)) :
    ↥P ≃* ↥P where
  toFun x := ⟨g * x * g⁻¹, (mem_normalizer_iff.1 hg x).1 x.2⟩
  invFun x := ⟨g⁻¹ * x * g, by
    have := (mem_normalizer_iff.1 (inv_mem hg) x).1 x.2
    simpa using this⟩
  left_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' x y := by
    apply Subtype.ext
    simp [mul_assoc]

theorem conjAutOfNormalizer_apply (P : Subgroup G) {g : G} (hg : g ∈ normalizer (P : Set G))
    (x : ↥P) : ((conjAutOfNormalizer P hg x : ↥P) : G) = g * x * g⁻¹ :=
  rfl

theorem mem_normalizer_map_upperCentralSeries {P : Subgroup G} {g : G}
    (hg : g ∈ normalizer (P : Set G)) (i : ℕ) :
    g ∈ normalizer (((Subgroup.upperCentralSeries ↥P i).map P.subtype : Subgroup G) : Set G) := by
  have hchar : (Subgroup.upperCentralSeries ↥P i).Characteristic := inferInstance
  have hfix := hchar.fixed (conjAutOfNormalizer P hg)
  have key : ∀ y : ↥P, y ∈ Subgroup.upperCentralSeries ↥P i ↔
      conjAutOfNormalizer P hg y ∈ Subgroup.upperCentralSeries ↥P i := fun y => by
    have := Subgroup.ext_iff.1 hfix y
    rw [Subgroup.mem_comap] at this
    exact this.symm
  refine mem_normalizer_iff.2 fun x => ?_
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, (key y).1 hy, rfl⟩
  · rintro ⟨y', hy', hy'x⟩
    refine ⟨(conjAutOfNormalizer P hg).symm y', ?_, ?_⟩
    · apply (key _).2
      rw [MulEquiv.apply_symm_apply]
      exact hy'
    · have h1 : g * (((conjAutOfNormalizer P hg).symm y' : ↥P) : G) * g⁻¹ = y' := by
        have := congrArg Subtype.val ((conjAutOfNormalizer P hg).apply_symm_apply y')
        rw [conjAutOfNormalizer_apply] at this
        exact this
      have h2 : g * (((conjAutOfNormalizer P hg).symm y' : ↥P) : G) * g⁻¹ = g * x * g⁻¹ := by
        rw [h1]
        exact hy'x
      exact mul_left_cancel (mul_right_cancel h2)

theorem mem_inf_centralizerMod_iff {P V W : Subgroup G} (hPV : P ≤ centralizer (V : Set G))
    (hWP : W ≤ P) {g : G} :
    g ∈ P ⊓ centralizerMod V W ↔ g ∈ P ∧ ∀ b ∈ W, g * b * g⁻¹ * b⁻¹ ∈ V := by
  have hN : ∀ x ∈ P, x ∈ normalizer (V : Set G) := fun x hx =>
    centralizer_le_normalizer V (hPV hx)
  rw [mem_inf, mem_centralizerMod_iff]
  constructor
  · rintro ⟨hgP, -, hc⟩
    exact ⟨hgP, fun b hb => hc b hb (hN b (hWP hb))⟩
  · rintro ⟨hgP, hc⟩
    exact ⟨hgP, hN g hgP, fun b hb hbN => hc b hb⟩

theorem mem_normalizer_inf_centralizerMod [Finite G] {P V W : Subgroup G}
    (hPV : P ≤ centralizer (V : Set G)) (hWP : W ≤ P) {g : G}
    (hgP : g ∈ normalizer (P : Set G)) (hgV : g ∈ normalizer (V : Set G))
    (hgW : g ∈ normalizer (W : Set G)) :
    g ∈ normalizer ((P ⊓ centralizerMod V W : Subgroup G) : Set G) := by
  refine mem_normalizer_fintype fun z hz => ?_
  have hz' := (mem_inf_centralizerMod_iff hPV hWP).1 hz
  refine (mem_inf_centralizerMod_iff hPV hWP).2 ⟨(mem_normalizer_iff.1 hgP z).1 hz'.1,
    fun b hb => ?_⟩
  have hb' : g⁻¹ * b * g ∈ W := by
    have := (mem_normalizer_iff.1 (inv_mem hgW) b).1 hb
    simpa using this
  have h1 := hz'.2 _ hb'
  have h2 := (mem_normalizer_iff.1 hgV _).1 h1
  have e : g * (z * (g⁻¹ * b * g) * z⁻¹ * (g⁻¹ * b * g)⁻¹) * g⁻¹ =
      g * z * g⁻¹ * b * (g * z * g⁻¹)⁻¹ * b⁻¹ := by group
  rwa [e] at h2

theorem commutator_commutator_involution {t : G} (htt : t * t = 1) (z : G) :
    (z * t * z⁻¹ * t⁻¹) * t * (z * t * z⁻¹ * t⁻¹)⁻¹ * t⁻¹ =
      (z * t * z⁻¹ * t⁻¹) * (z * t * z⁻¹ * t⁻¹) := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have h3 : ∀ x : G, t * (t * x) = x := fun x => by rw [← mul_assoc, htt, one_mul]
  simp only [hti, mul_inv_rev, inv_inv, mul_assoc, h3]

theorem mem_zpowers_involution {t b : G} (htt : t * t = 1) (hb : b ∈ zpowers t) :
    b = 1 ∨ b = t := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hb
  have hsq : t ^ 2 = 1 := by rw [pow_two]; exact htt
  have h1 : t ^ n = t ^ (n % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv n 2]
    rw [zpow_add, zpow_mul]
    have : t ^ (2 : ℤ) = 1 := by exact_mod_cast hsq
    rw [this, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left
    rw [h1, h, zpow_zero]
  · right
    rw [h1, h, zpow_one]

end Generic

section E1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem J_le_normalizer_P (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {j : L} (hj : j ∈ d.J) :
    (j : G) ∈ normalizer ((yamadaP d t : Subgroup G) : Set G) :=
  ncs_le_normalizer_yamadaP h d hlay (mem_inf.2 ⟨h.L_le_centralizer j.2,
    Setup.map_le_normalizer_map d.J_le_normalizer_S ⟨j, hj, rfl⟩⟩)

theorem D_map_le_yamadaD₅ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : d.D.map L.subtype ≤ yamadaD₅ d t :=
  le_inf ((h.D_map_le_yamadaC₁ d).trans (yamadaC₁_le_yamadaC₅ d t))
    ((map_mono d.D_le_S).trans (h.S_map_le_centralizer_yamadaV₁ d hlay))

theorem E1_core (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    yamadaP d t ⊓ centralizerMod (yamadaV₁ d t) (yamadaW₃ d t) = yamadaD₅ d t ∧
      ((yamadaD₅ d t).subgroupOf (yamadaP d t)).Characteristic ∧
      normalizer ((yamadaP d t : Subgroup G) : Set G) ≤
        normalizer ((yamadaD₅ d t : Subgroup G) : Set G) := by
  have hlay := hp.layer
  obtain ⟨hV₁C, -, -, -, -, -, hPC, -, -, -, -, -, -, -, -, hPD₅, -, -⟩ :=
    T4_series_free h d hp
  obtain ⟨hZ1, hZ2, hZ3, hZ4⟩ := S5_upperCentralSeries_P h d hlay
  have hPV₁ : yamadaP d t ≤ centralizer (yamadaV₁ d t : Set G) :=
    yamadaP_le_centralizer_yamadaV₁ d t
  have hD₅P : yamadaD₅ d t ≤ yamadaP d t := yamadaD₅_le_yamadaP d t
  have hW₃D₅ : yamadaW₃ d t ≤ yamadaD₅ d t := h.yamadaW₃_le_yamadaD₅_PA d hlay
  have hW₃P : yamadaW₃ d t ≤ yamadaP d t := hW₃D₅.trans hD₅P
  have htP : t ∈ normalizer (yamadaP d t : Set G) := h.t_mem_normalizer_yamadaP d hlay
  have hPN : yamadaP d t ≤ normalizer (yamadaD₅ d t : Set G) :=
    h.yamadaP_le_normalizer_yamadaD₅ d hlay
  have hcommD : ∀ x ∈ yamadaD₅ d t, ∀ y ∈ yamadaD₅ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaV₁ d t :=
    fun x hx y hy => h.commutator_mem_yamadaV₁_of_mem_yamadaD₅_PA d hlay hx hy
  have hNV : ∀ g, g ∈ normalizer (yamadaP d t : Set G) → g ∈ normalizer (yamadaV₁ d t : Set G) :=
    fun g hg => by
      have := mem_normalizer_map_upperCentralSeries hg 1
      rwa [hZ1] at this
  have hNW : ∀ g, g ∈ normalizer (yamadaP d t : Set G) → g ∈ normalizer (yamadaW₃ d t : Set G) :=
    fun g hg => by
      have := mem_normalizer_map_upperCentralSeries hg 3
      rwa [hZ3] at this
  have hmemZ : ∀ g, g ∈ yamadaP d t ⊓ centralizerMod (yamadaV₁ d t) (yamadaW₃ d t) ↔
      g ∈ yamadaP d t ∧ ∀ b ∈ yamadaW₃ d t, g * b * g⁻¹ * b⁻¹ ∈ yamadaV₁ d t := fun g =>
    mem_inf_centralizerMod_iff hPV₁ hW₃P
  have hD₅Z : yamadaD₅ d t ≤ yamadaP d t ⊓ centralizerMod (yamadaV₁ d t) (yamadaW₃ d t) :=
    fun g hg => (hmemZ g).2 ⟨hD₅P hg, fun b hb => hcommD g hg b (hW₃D₅ hb)⟩
  have hNZ : ∀ g, g ∈ normalizer (yamadaP d t : Set G) →
      g ∈ normalizer ((yamadaP d t ⊓ centralizerMod (yamadaV₁ d t) (yamadaW₃ d t) :
        Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_inf_centralizerMod hPV₁ hW₃P hg (hNV g hg) (hNW g hg)
  have hZD₅ : yamadaP d t ⊓ centralizerMod (yamadaV₁ d t) (yamadaW₃ d t) ≤ yamadaD₅ d t := by
    intro z hz
    by_contra hzD
    set Z := yamadaP d t ⊓ centralizerMod (yamadaV₁ d t) (yamadaW₃ d t) with hZdef
    have htt : t * t = 1 := h.t_mul_t
    have hzt : t * z * t⁻¹ ∈ Z := (mem_normalizer_iff.1 (hNZ t htP) z).1 hz
    set c := z * t * z⁻¹ * t⁻¹ with hc
    have hcZ : c ∈ Z := by
      have : c = z * (t * z * t⁻¹)⁻¹ := by simp [hc, mul_assoc]
      rw [this]
      exact mul_mem hz (inv_mem hzt)
    have hcP : c ∈ yamadaP d t := ((hmemZ c).1 hcZ).1
    have hzP : z ∈ yamadaP d t := ((hmemZ z).1 hz).1
    have hcc : c * c ∈ yamadaD₅ d t := hPD₅.1.mul_self_mem c hcP
    have hfixmod : ∀ x ∈ yamadaP d t, x * t * x⁻¹ * t⁻¹ ∈ yamadaD₅ d t →
        x ∈ (d.S.map L.subtype) ⊔ yamadaD₅ d t := by
      intro x hxP hxt
      have hx : x ∈ yamadaP d t ⊓ centralizerMod (yamadaD₅ d t) (zpowers t) := by
        rw [mem_inf, mem_centralizerMod_iff]
        refine ⟨hxP, hPN hxP, fun b hb hbN => ?_⟩
        rcases mem_zpowers_involution htt hb with rfl | rfl
        · simpa using one_mem (yamadaD₅ d t)
        · exact hxt
      rw [hPD₅.2.2, hPC] at hx
      exact hx
    obtain ⟨y, hyZ, hyS, hyD⟩ : ∃ y ∈ Z, y ∈ (d.S.map L.subtype) ⊔ yamadaD₅ d t ∧
        y ∉ yamadaD₅ d t := by
      by_cases hcD : c ∈ yamadaD₅ d t
      · exact ⟨z, hz, hfixmod z hzP hcD, hzD⟩
      · refine ⟨c, hcZ, hfixmod c hcP ?_, hcD⟩
        rw [hc, commutator_commutator_involution htt z]
        have := hcc
        rw [hc] at this
        exact this
    have hSN : (d.S.map L.subtype) ≤ normalizer (yamadaD₅ d t : Set G) :=
      (h.S_map_le_yamadaP d hlay).trans hPN
    have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (d.S.map L.subtype)
      (yamadaD₅ d t) hSN
    obtain ⟨s, hs, δ, hδ, hsδ⟩ : ∃ s ∈ d.S.map L.subtype, ∃ δ ∈ yamadaD₅ d t, s * δ = y := by
      have : y ∈ ((d.S.map L.subtype : Subgroup G) : Set G) * (yamadaD₅ d t : Set G) := by
        rw [← hmul]
        exact hyS
      exact Set.mem_mul.1 this
    have hsZ : s ∈ Z := by
      have : s = y * δ⁻¹ := by rw [← hsδ]; group
      rw [this]
      exact mul_mem hyZ (inv_mem (hD₅Z hδ))
    have hsD : s ∉ yamadaD₅ d t := fun hsD' => hyD (by rw [← hsδ]; exact mul_mem hsD' hδ)
    obtain ⟨sL, hsL, rfl⟩ := hs
    obtain ⟨a, n, hn, hsLe⟩ := d.mem_S_iff.1 hsL
    have hnD : ((n : L) : G) ∈ yamadaD₅ d t := D_map_le_yamadaD₅ h d hlay ⟨n, hn, rfl⟩
    have hx₁Z : ((d.x₁ a : L) : G) ∈ Z := by
      have : ((d.x₁ a : L) : G) = (sL : G) * ((n : L) : G)⁻¹ := by
        rw [← hsLe]
        simp
      rw [this]
      exact mul_mem hsZ (inv_mem (hD₅Z hnD))
    have ha : a ≠ 0 := by
      rintro rfl
      apply hsD
      have : (sL : G) = ((n : L) : G) := by
        rw [← hsLe, d.x₁_zero, one_mul]
      have hs' : (sL : G) ∈ yamadaD₅ d t := by
        rw [this]
        exact hnD
      exact hs'
    have hx₁1 : ((d.x₁ 1 : L) : G) ∈ Z := by
      let μ : d.Γˣ := Units.mk0 a⁻¹ (inv_ne_zero ha)
      have hj : d.torus ((1 : (d.Γ₀)ˣ), μ) ∈ d.J := d.torus_mem_J _
      have hjN := hNZ _ (J_le_normalizer_P h d hlay hj)
      have h1 := (mem_normalizer_iff.1 hjN _).1 hx₁Z
      have h2 := congrArg (fun x : L => (x : G)) (d.torus_x₁ ((1 : (d.Γ₀)ˣ), μ) a)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
      have e : (μ : d.Γ) * a = 1 := by simp [μ, ha]
      rw [h2] at h1
      simpa [e] using h1
    have hb : ((d.x₄ 1 : L) : G) ∈ yamadaW₃ d t :=
      h.W_map_le_yamadaW₃_S4C d hlay ⟨d.x₄ 1, d.x₄_mem_W 1, rfl⟩
    have h1 := ((hmemZ _).1 hx₁1).2 _ hb
    have e : ((d.x₁ 1 : L) : G) * ((d.x₄ 1 : L) : G) * ((d.x₁ 1 : L) : G)⁻¹ *
        ((d.x₄ 1 : L) : G)⁻¹ = ((d.x₅ (d.tr (1 * 1)) : L) : G) := by
      have := congrArg (fun x : L => (x : G)) (d.comm₁₄ 1 1)
      simpa [commutatorElement_def] using this
    rw [e] at h1
    have hct : ((d.x₅ (d.tr (1 * 1)) : L) : G) ∈ centralizer ({t} : Set G) :=
      h.L_le_centralizer (d.x₅ _).2
    have hVm : ((d.x₅ (d.tr (1 * 1)) : L) : G) ∈ d.V.map L.subtype := by
      rw [← hV₁C]
      exact mem_inf.2 ⟨h1, hct⟩
    obtain ⟨v, hv, hvx⟩ := hVm
    have hveq : v = d.x₅ (d.tr (1 * 1)) := Subtype.ext hvx
    rw [hveq] at hv
    have h0 : d.tr (1 * 1) = 0 := d.x₅_mem_V_iff.1 hv
    have h1' : d.tr (1 * 1) = 1 := by
      apply Subtype.ext
      have h2 : (1 : d.Γ) + 1 = 0 := CharTwo.add_self_eq_zero 1
      simp [TrialityD4Data.tr, coe_fixedTrace, h2]
    rw [h1'] at h0
    exact one_ne_zero h0
  have hEq : yamadaP d t ⊓ centralizerMod (yamadaV₁ d t) (yamadaW₃ d t) = yamadaD₅ d t :=
    le_antisymm hZD₅ hD₅Z
  have hchar : ∀ x : ↥(yamadaP d t), x ∈ (yamadaD₅ d t).subgroupOf (yamadaP d t) ↔
      ∀ w : ↥(yamadaP d t), w ∈ Subgroup.upperCentralSeries ↥(yamadaP d t) 3 →
        x * w * x⁻¹ * w⁻¹ ∈ Subgroup.upperCentralSeries ↥(yamadaP d t) 1 := by
    intro x
    have hW : ∀ w : ↥(yamadaP d t), w ∈ Subgroup.upperCentralSeries ↥(yamadaP d t) 3 ↔
        (w : G) ∈ yamadaW₃ d t := fun w => by
      rw [← hZ3]
      exact (Subgroup.mem_map_iff_mem (yamadaP d t).subtype_injective).symm
    have hV : ∀ w : ↥(yamadaP d t), w ∈ Subgroup.upperCentralSeries ↥(yamadaP d t) 1 ↔
        (w : G) ∈ yamadaV₁ d t := fun w => by
      rw [← hZ1]
      exact (Subgroup.mem_map_iff_mem (yamadaP d t).subtype_injective).symm
    rw [Subgroup.mem_subgroupOf, ← hEq, hmemZ]
    constructor
    · rintro ⟨-, hx⟩ w hw
      have := hx _ ((hW w).1 hw)
      exact (hV _).2 (by simpa using this)
    · intro hx
      refine ⟨x.2, fun b hb => ?_⟩
      have := (hV _).1 (hx ⟨b, hW₃P hb⟩ ((hW _).2 hb))
      simpa using this
  have hmapD : ∀ φ : ↥(yamadaP d t) ≃* ↥(yamadaP d t), ∀ x : ↥(yamadaP d t),
      x ∈ (yamadaD₅ d t).subgroupOf (yamadaP d t) →
        φ x ∈ (yamadaD₅ d t).subgroupOf (yamadaP d t) := by
    intro φ x hx
    have hcW : (Subgroup.upperCentralSeries ↥(yamadaP d t) 3).Characteristic := inferInstance
    have hcV : (Subgroup.upperCentralSeries ↥(yamadaP d t) 1).Characteristic := inferInstance
    have keyW := fun y => by
      have := Subgroup.ext_iff.1 (hcW.fixed φ) y
      rw [Subgroup.mem_comap] at this
      exact this.symm
    have keyV := fun y => by
      have := Subgroup.ext_iff.1 (hcV.fixed φ) y
      rw [Subgroup.mem_comap] at this
      exact this.symm
    rw [hchar] at hx ⊢
    intro w hw
    obtain ⟨w₀, rfl⟩ := φ.surjective w
    have hw₀ := (keyW w₀).2 hw
    have := (keyV _).1 (hx w₀ hw₀)
    simpa using this
  refine ⟨hEq, ⟨fun φ => ?_⟩, ?_⟩
  · ext x
    rw [Subgroup.mem_comap]
    constructor
    · intro hx
      have := hmapD φ.symm _ hx
      simpa using this
    · exact hmapD φ x
  · intro g hg
    refine mem_normalizer_fintype fun x hx => ?_
    have hxP : x ∈ yamadaP d t := hD₅P hx
    have hgx : g * x * g⁻¹ ∈ yamadaP d t := (mem_normalizer_iff.1 hg x).1 hxP
    have := hmapD (conjAutOfNormalizer (yamadaP d t) hg) ⟨x, hxP⟩
      (Subgroup.mem_subgroupOf.2 hx)
    exact Subgroup.mem_subgroupOf.1 this

end E1

section Generic

variable {G : Type*} [Group G]

theorem le_centralizer_of_sl2_quotient [Finite G] {k : Type} [Field k] [Finite k] [CharP k 2]
    {m d : ℕ} (hk : Nat.card k = 2 ^ m) (hm : 2 ≤ m) (hm3 : m ≠ 3) {K D V : Subgroup G}
    (hKV : K ≤ normalizer (V : Set G)) (hDV : D ≤ centralizer (V : Set G))
    (φ : ↥K →* SL(2, k)) (hφ : Function.Surjective φ)
    (hker : φ.ker = D.subgroupOf K) (hV : Nat.card V = 2 ^ d) (hd : d < 2 * m) :
    K ≤ centralizer (V : Set G) := by
  have hDn : (D.subgroupOf K).Normal := hker ▸ MonoidHom.normal_ker φ
  let ρ₀ : ↥K →* MulAut ↥V := CFSG.SL2MinimalFaithful.conjAction hKV
  have hle : D.subgroupOf K ≤ ρ₀.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    ext v
    have hxD : (x : G) ∈ D := Subgroup.mem_subgroupOf.1 hx
    have := mem_centralizer_iff.1 (hDV hxD) v v.2
    show ((CFSG.SL2MinimalFaithful.conjAction hKV x v : V) : G) = v
    rw [CFSG.SL2MinimalFaithful.conjAction_apply]
    calc (x : G) * v * (x : G)⁻¹ = (v : G) * x * (x : G)⁻¹ := by rw [← this]
      _ = v := by group
  let ρ : (↥K ⧸ D.subgroupOf K) →* MulAut ↥V := QuotientGroup.lift (D.subgroupOf K) ρ₀ hle
  let e : (↥K ⧸ D.subgroupOf K) ≃* SL(2, k) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  have h1 := eq_one_of_card_lt e hk hm hm3 ρ hV hd
  intro x hx
  rw [mem_centralizer_iff]
  intro v hv
  have h2 := congrArg (fun r : (↥K ⧸ D.subgroupOf K) →* MulAut ↥V =>
    ((r (QuotientGroup.mk ⟨x, hx⟩) ⟨v, hv⟩ : V) : G)) h1
  simp only [MonoidHom.one_apply, MulAut.one_apply] at h2
  have h3 : (x : G) * v * (x : G)⁻¹ = v := by
    have h4 : ((ρ₀ ⟨x, hx⟩ ⟨v, hv⟩ : V) : G) = v := h2
    have h5 := CFSG.SL2MinimalFaithful.conjAction_apply hKV ⟨x, hx⟩ ⟨v, hv⟩
    exact h5.symm.trans h4
  calc v * x = x * v * x⁻¹ * x := by rw [h3]
    _ = x * v := by group

end Generic

section Generic2

variable {G : Type*} [Group G]

theorem eq_commutator_sup_of_perfect_quotient {K' V : Subgroup G} (hVK : V ≤ K')
    [(V.subgroupOf K').Normal] (hperf : Group.IsPerfect (↥K' ⧸ V.subgroupOf K')) :
    K' = ⁅K', K'⁆ ⊔ V := by
  refine le_antisymm (fun x hx => ?_) (sup_le (commutator_le_of_le le_rfl le_rfl) hVK)
  have hmem : (QuotientGroup.mk ⟨x, hx⟩ : ↥K' ⧸ V.subgroupOf K') ∈
      commutator (↥K' ⧸ V.subgroupOf K') := by
    rw [Group.IsPerfect.commutator_eq_top (G := ↥K' ⧸ V.subgroupOf K')]
    exact Subgroup.mem_top _
  have h1 : Subgroup.map (QuotientGroup.mk' (V.subgroupOf K')) (commutator ↥K') =
      commutator (↥K' ⧸ V.subgroupOf K') := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  rw [← h1] at hmem
  obtain ⟨y, hy, hyx⟩ := hmem
  have hyx' : (QuotientGroup.mk y : ↥K' ⧸ V.subgroupOf K') = QuotientGroup.mk ⟨x, hx⟩ := hyx
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hyx'
  have hyK : (y : G) ∈ ⁅K', K'⁆ := by
    have hmap : (commutator ↥K').map K'.subtype ≤ ⁅K', K'⁆ := by
      rw [_root_.commutator_def, Subgroup.map_commutator]
      refine commutator_mono ?_ ?_ <;> rintro _ ⟨z, -, rfl⟩ <;> exact z.2
    exact hmap ⟨y, hy, rfl⟩
  have hx' : x = (y : G) * ((y : G)⁻¹ * x) := by group
  rw [hx']
  exact mul_mem_sup hyK (by simpa using hyx')

theorem commutator_commutator_eq_bot_of_central {A B V N : Subgroup G} (hA : A ≤ N) (hB : B ≤ N)
    (hAB : ⁅A, B⁆ ≤ V) (hV : V ≤ centralizer (N : Set G)) : ⁅⁅A, A⁆, ⁅B, B⁆⁆ = ⊥ := by
  have hVB : ⁅V, B⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.2 (hV.trans (centralizer_le hB))
  have hBA : ⁅B, A⁆ ≤ V := by
    rw [commutator_comm]
    exact hAB
  have h1 : ⁅⁅B, A⁆, B⁆ = ⊥ := eq_bot_iff.2 ((commutator_mono hBA le_rfl).trans hVB.le)
  have h2 : ⁅⁅A, B⁆, B⁆ = ⊥ := eq_bot_iff.2 ((commutator_mono hAB le_rfl).trans hVB.le)
  have hstepA : ⁅⁅B, B⁆, A⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate h1 h2
  have h3 : ⁅⁅A, ⁅B, B⁆⁆, A⁆ = ⊥ := by
    rw [commutator_comm A ⁅B, B⁆, hstepA]
    exact commutator_bot_left _
  have h4 : ⁅⁅⁅B, B⁆, A⁆, A⁆ = ⊥ := by
    rw [hstepA]
    exact commutator_bot_left _
  exact commutator_commutator_eq_bot_of_rotate h3 h4

end Generic2

section CLV

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ}

theorem cLV_perfect (d : TrialityD4Data L (2 ^ f)) : ⁅cLV d, cLV d⁆ = cLV d := by
  have h1 : cLV d = (d.D ⊔ d.leviShort).map L.subtype := by
    unfold cLV
    rw [d.centralizer_V_eq]
  rw [h1, ← Subgroup.map_commutator, d.commutator_D_sup_leviShort]

end CLV

section Conj

variable {G : Type*} [Group G]

theorem mem_conjg_iff {X : Subgroup G} {g x : G} : x ∈ Xᵍ[g] ↔ g * x * g⁻¹ ∈ X :=
  mem_map_conj_inv_iff

theorem conjg_inf (X Y : Subgroup G) (g : G) : (X ⊓ Y)ᵍ[g] = Xᵍ[g] ⊓ Yᵍ[g] :=
  Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective

theorem conjg_sup (X Y : Subgroup G) (g : G) : (X ⊔ Y)ᵍ[g] = Xᵍ[g] ⊔ Yᵍ[g] :=
  Subgroup.map_sup _ _ _

theorem card_conjg (X : Subgroup G) (g : G) : Nat.card ↥(Xᵍ[g]) = Nat.card X :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem conjg_mono {X Y : Subgroup G} (h : X ≤ Y) (g : G) : Xᵍ[g] ≤ Yᵍ[g] :=
  Subgroup.map_mono h

theorem conjg_conjg (X : Subgroup G) (g h : G) : (Xᵍ[g])ᵍ[h] = Xᵍ[g * h] := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem conjg_commutator (X Y : Subgroup G) (g : G) : ⁅X, Y⁆ᵍ[g] = ⁅Xᵍ[g], Yᵍ[g]⁆ :=
  Subgroup.map_commutator _ _ _

theorem conjg_one (X : Subgroup G) : Xᵍ[(1 : G)] = X := by
  ext x
  rw [mem_conjg_iff]
  simp

theorem zc_conjg (X : Subgroup G) (g : G) : zc (Xᵍ[g]) = (zc X)ᵍ[g] := by
  ext x
  simp only [zc, mem_inf, SetLike.mem_coe, mem_conjg_iff, mem_centralizer_iff]
  constructor
  · rintro ⟨hx, hc⟩
    refine ⟨hx, fun y hy => ?_⟩
    have := hc (g⁻¹ * y * g) (by rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group])
    have e : g * x * g⁻¹ * y = y * (g * x * g⁻¹) := by
      calc g * x * g⁻¹ * y = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by rw [this]
        _ = y * (g * x * g⁻¹) := by group
    exact e.symm
  · rintro ⟨hx, hc⟩
    refine ⟨hx, fun y hy => ?_⟩
    have hy' : g * y * g⁻¹ ∈ X := hy
    have := hc _ hy'
    calc y * x = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by rw [this]
      _ = x * y := by group

end Conj

structure E2Ctx {𝔊 : Type*} [Group 𝔊] (f : ℕ) (Γ : Type) [Field Γ] [Finite Γ]
    (t u : 𝔊) (K D P Y W F J J₀ C : Subgroup 𝔊) (φ : ↥K →* SL(2, Γ)) : Prop where
  two_le : 2 ≤ f
  card_Γ : Nat.card Γ = (2 ^ f) ^ 3
  charTwo : CharP Γ 2
  t_mul_t : t * t = 1
  u_mul_u : u * u = 1
  t_comm_u : t * u = u * t
  K_inf : K ⊓ Kᵍ[t] = D
  comm_le : ⁅K, Kᵍ[t]⁆ ≤ D
  φ_surj : Function.Surjective φ
  φ_ker : φ.ker = D.subgroupOf K
  D_comm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x
  D_sq : ∀ x ∈ D, x * x = 1
  D_le_P : D ≤ P
  P_le_N : P ≤ K ⊔ Kᵍ[t]
  P_pgroup : IsPGroup 2 P
  card_P : Nat.card P = Nat.card D * (2 ^ f) ^ 6
  P_conj : Pᵍ[t] = P
  mem_Y : ∀ x, x ∈ Y ↔ x ∈ P ∧ ∀ p ∈ P, x * p = p * x
  mem_W : ∀ x, x ∈ W ↔ x ∈ P ∧ ∀ p ∈ P, x * p * x⁻¹ * p⁻¹ ∈ Y
  mem_F : ∀ x, x ∈ F ↔ x ∈ P ∧ ∀ p ∈ P, x * p * x⁻¹ * p⁻¹ ∈ W
  F_le_D : F ≤ D
  card_Y : Nat.card Y = (2 ^ f) ^ 2
  card_W : Nat.card W = (2 ^ f) ^ 8
  card_F : Nat.card F = (2 ^ f) ^ 14
  card_D : Nat.card D = (2 ^ f) ^ 16
  Y_conj : Yᵍ[t] = Y
  W_conj : Wᵍ[t] = W
  u_mem_N : u ∈ K ⊔ Kᵍ[t]
  u_not_mem_normalizer_P : u ∉ normalizer (P : Set 𝔊)
  D_eq_sup : D = W ⊔ Wᵍ[u]
  W_inf : W ⊓ Wᵍ[u] = ⊥
  J_odd : Odd (Nat.card J)
  J_cen_t : J ≤ centralizer ({t} : Set 𝔊)
  J_nor_N : J ≤ normalizer ((K ⊔ Kᵍ[t] : Subgroup 𝔊) : Set 𝔊)
  J_nor_P : J ≤ normalizer (P : Set 𝔊)
  J_nor_Y : J ≤ normalizer (Y : Set 𝔊)
  J_nor_W : J ≤ normalizer (W : Set 𝔊)
  J_nor_F : J ≤ normalizer (F : Set 𝔊)
  J₀_le_J : J₀ ≤ J
  J_conj_u : ∀ j ∈ J, u * j * u⁻¹ ∈ J
  J₀_conj_u : ∀ j ∈ J₀, u * j * u⁻¹ ∈ J₀
  J₀_cen_Y : Y ≤ centralizer (J₀ : Set 𝔊)
  W_inf_cen : W ⊓ centralizer (J₀ : Set 𝔊) = Y
  D_J₀_le_F : ∀ x ∈ D, ∀ j ∈ J₀, x * j * x⁻¹ * j⁻¹ ∈ F
  W_fixed_not_le_Y : ¬ (W ⊓ centralizer ({t} : Set 𝔊) ≤ Y)
  J_inv_W : ∀ X : Subgroup 𝔊, Y ≤ X → X ≤ W → J ≤ normalizer (X : Set 𝔊) →
    X = Y ∨ Nat.card X = Nat.card Y * (2 ^ f) ^ 3 ∨ X = W
  J_inv_F : ∀ X : Subgroup 𝔊, W ≤ X → X ≤ F → J ≤ normalizer (X : Set 𝔊) →
    X = W ∨ Nat.card X = Nat.card W * (2 ^ f) ^ 3 ∨ X = F
  C_le_N : C ≤ K ⊔ Kᵍ[t]
  C_cen_t : C ≤ centralizer ({t} : Set 𝔊)
  C_perfect : ⁅C, C⁆ = C
  D₁_le_C : D ⊓ centralizer ({t} : Set 𝔊) ≤ C
  card_D₁ : Nat.card ↥(D ⊓ centralizer ({t} : Set 𝔊)) = (2 ^ f) ^ 8
  C_irr : ∀ X : Subgroup 𝔊, X ≤ D ⊓ centralizer ({t} : Set 𝔊) → C ≤ normalizer (X : Set 𝔊) →
    X = ⊥ ∨ X = D ⊓ centralizer ({t} : Set 𝔊)
  card_C : Nat.card C = Nat.card SL(2, Γ) * (2 ^ f) ^ 8

section GenericNormal

variable {G : Type*} [Group G] [Finite G]

theorem le_normalizer_of_commutator_le {X Y : Subgroup G} (h : ⁅X, Y⁆ ≤ X) :
    Y ≤ normalizer (X : Set G) := fun b hb => by
  refine mem_normalizer_fintype fun x hx => ?_
  have h1 : ⁅x, b⁆ ∈ X := h (commutator_mem_commutator hx hb)
  have : b * x * b⁻¹ = (⁅x, b⁆)⁻¹ * x := by
    rw [commutatorElement_def]
    group
  rw [this]
  exact mul_mem (inv_mem h1) hx

end GenericNormal

namespace E2Ctx

section Basic

variable {𝔊 : Type*} [Group 𝔊] [Finite 𝔊] {f : ℕ} {Γ : Type} [Field Γ] [Finite Γ]
  {t u : 𝔊} {K D P Y W F J J₀ C : Subgroup 𝔊} {φ : ↥K →* SL(2, Γ)}
  (c : E2Ctx f Γ t u K D P Y W F J J₀ C φ)

include c

theorem t_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right c.t_mul_t

theorem u_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right c.u_mul_u

theorem Kt_conj : (Kᵍ[t])ᵍ[t] = K := map_conj_inv_map_conj_inv c.t_mul_t K

theorem D_conj : Dᵍ[t] = D := by
  rw [← c.K_inf, conjg_inf, c.Kt_conj, inf_comm]

theorem D_le_K : D ≤ K := c.K_inf ▸ inf_le_left

theorem D_le_Kt : D ≤ Kᵍ[t] := c.K_inf ▸ inf_le_right

theorem K_le_N : K ≤ K ⊔ Kᵍ[t] := le_sup_left

theorem Kt_le_N : Kᵍ[t] ≤ K ⊔ Kᵍ[t] := le_sup_right

theorem Kt_le_normalizer_K : Kᵍ[t] ≤ normalizer (K : Set 𝔊) := by
  refine le_normalizer_of_commutator_le (le_trans ?_ c.D_le_K)
  exact c.comm_le

theorem K_le_normalizer_Kt : K ≤ normalizer ((Kᵍ[t] : Subgroup 𝔊) : Set 𝔊) := by
  refine le_normalizer_of_commutator_le (X := Kᵍ[t]) (Y := K) (le_trans ?_ c.D_le_Kt)
  rw [commutator_comm]
  exact c.comm_le

theorem N_le_normalizer_K : K ⊔ Kᵍ[t] ≤ normalizer (K : Set 𝔊) :=
  sup_le le_normalizer c.Kt_le_normalizer_K

theorem N_le_normalizer_Kt : K ⊔ Kᵍ[t] ≤ normalizer ((Kᵍ[t] : Subgroup 𝔊) : Set 𝔊) :=
  sup_le c.K_le_normalizer_Kt le_normalizer

theorem N_le_normalizer_D : K ⊔ Kᵍ[t] ≤ normalizer (D : Set 𝔊) := by
  intro g hg
  rw [← c.K_inf]
  exact Common.mem_normalizer_inf (c.N_le_normalizer_K hg) (c.N_le_normalizer_Kt hg)

theorem card_SL : Nat.card SL(2, Γ) = (2 ^ f) ^ 3 * (((2 ^ f) ^ 3) ^ 2 - 1) := by
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, c.card_Γ]

theorem card_K : Nat.card K = Nat.card D * Nat.card SL(2, Γ) := by
  have h1 := card_map_mul_card_inf_ker φ ⊤
  rw [Subgroup.map_top_of_surjective _ c.φ_surj, Subgroup.card_top, top_inf_eq, c.φ_ker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.D_le_K).toEquiv, Subgroup.card_top] at h1
  rw [← h1, mul_comm]

end Basic

end E2Ctx

section GenericSL

variable {G : Type*} [Group G]

theorem isSylowOf_top_sl2 {k : Type} [Field k] [Finite k] {m : ℕ} (hk : Nat.card k = 2 ^ m)
    (hm : 1 ≤ m) {S : Subgroup SL(2, k)} (hS : Nat.card S = Nat.card k) :
    IsSylowOf 2 S (⊤ : Subgroup SL(2, k)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨le_top, IsPGroup.of_card (n := m) (by rw [hS, hk]), ?_⟩
  have h1 := Subgroup.relIndex_mul_card S (⊤ : Subgroup SL(2, k))
  rw [inf_eq_left.mpr le_top, hS, Subgroup.card_top,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two] at h1
  have hpos : 0 < Nat.card k := Nat.card_pos
  have h2 : S.relIndex ⊤ = Nat.card k ^ 2 - 1 := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1]
    ring
  rw [h2]
  have h4 : 4 ≤ Nat.card k ^ 2 := by
    rw [hk, ← pow_mul]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (m * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have heven : Even (Nat.card k ^ 2) := by
    rw [hk, ← pow_mul]
    exact (Nat.even_pow' (by omega)).mpr even_two
  intro hdvd
  obtain ⟨r, hr⟩ := heven
  obtain ⟨s, hs⟩ := hdvd
  omega

end GenericSL

namespace E2Ctx

section SL

variable {𝔊 : Type*} [Group 𝔊] [Finite 𝔊] {f : ℕ} {Γ : Type} [Field Γ] [Finite Γ]
  {t u : 𝔊} {K D P Y W F J J₀ C : Subgroup 𝔊} {φ : ↥K →* SL(2, Γ)}
  (c : E2Ctx f Γ t u K D P Y W F J J₀ C φ)

include c

theorem card_Γ_pow : Nat.card Γ = 2 ^ (3 * f) := by
  rw [c.card_Γ, ← pow_mul, mul_comm]

theorem four_le_card_Γ : 4 ≤ Nat.card Γ := by
  rw [c.card_Γ_pow]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (3 * f) := Nat.pow_le_pow_right (by norm_num) (by have := c.two_le; omega)

theorem central_le_D {z : 𝔊} (hz : z ∈ K) (hc : ∀ k ∈ K, z * k = k * z) : z ∈ D := by
  haveI := c.charTwo
  have hcen : φ ⟨z, hz⟩ ∈ Subgroup.center SL(2, Γ) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := c.φ_surj g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc k.1 k.2).symm
  rw [center_sl2_eq_bot_of_charTwo, Subgroup.mem_bot] at hcen
  have : (⟨z, hz⟩ : ↥K) ∈ φ.ker := hcen
  rw [c.φ_ker, Subgroup.mem_subgroupOf] at this
  exact this

theorem normal_D : (D.subgroupOf K).Normal := c.φ_ker ▸ MonoidHom.normal_ker φ

theorem perfect_quotient [hDn : (D.subgroupOf K).Normal] :
    Group.IsPerfect (↥K ⧸ D.subgroupOf K) := by
  haveI := c.charTwo
  have hSL : Group.IsPerfect SL(2, Γ) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect (exists_finset_card_four
      c.four_le_card_Γ)
  haveI := hSL
  let e : (↥K ⧸ D.subgroupOf K) ≃* SL(2, Γ) :=
    (QuotientGroup.quotientMulEquivOfEq c.φ_ker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ c.φ_surj)
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem K_eq_commutator_sup : K = ⁅K, K⁆ ⊔ D := by
  haveI := c.normal_D
  exact eq_commutator_sup_of_perfect_quotient c.D_le_K c.perfect_quotient

end SL

end E2Ctx

namespace E2Ctx

section SL3

variable {𝔊 : Type*} [Group 𝔊] [Finite 𝔊] {f : ℕ} {Γ : Type} [Field Γ] [Finite Γ]
  {t u : 𝔊} {K D P Y W F J J₀ C : Subgroup 𝔊} {φ : ↥K →* SL(2, Γ)}
  (c : E2Ctx f Γ t u K D P Y W F J J₀ C φ)

include c

theorem card_map_φ {A : Subgroup 𝔊} (hDA : D ≤ A) (hAK : A ≤ K) :
    Nat.card ↥((A.subgroupOf K).map φ) * Nat.card D = Nat.card A := by
  have h1 := card_map_mul_card_inf_ker φ (A.subgroupOf K)
  have hle : D.subgroupOf K ≤ A.subgroupOf K := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hDA (Subgroup.mem_subgroupOf.1 hx))
  rw [c.φ_ker, inf_eq_right.mpr hle,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.D_le_K).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv] at h1
  exact h1

theorem comap_map_φ {A : Subgroup 𝔊} (hDA : D ≤ A) :
    ((A.subgroupOf K).map φ).comap φ = A.subgroupOf K := by
  apply Subgroup.comap_map_eq_self
  rw [c.φ_ker]
  exact fun x hx => Subgroup.mem_subgroupOf.2 (hDA (Subgroup.mem_subgroupOf.1 hx))

theorem sylow_sup_inf {A A' : Subgroup 𝔊} (hDA : D ≤ A) (hDA' : D ≤ A') (hAK : A ≤ K)
    (hA'K : A' ≤ K) (hcard : Nat.card A = Nat.card D * (2 ^ f) ^ 3)
    (hcard' : Nat.card A' = Nat.card D * (2 ^ f) ^ 3) (hne : A ≠ A') :
    A ⊔ A' = K ∧ A ⊓ A' = D := by
  haveI := c.charTwo
  have hDpos : 0 < Nat.card D := Nat.card_pos
  have hm : 1 ≤ 3 * f := by have := c.two_le; omega
  have hcardĀ : Nat.card ↥((A.subgroupOf K).map φ) = Nat.card Γ := by
    have := c.card_map_φ hDA hAK
    rw [hcard] at this
    rw [c.card_Γ]
    exact Nat.eq_of_mul_eq_mul_right hDpos (by rw [this]; ring)
  have hcardĀ' : Nat.card ↥((A'.subgroupOf K).map φ) = Nat.card Γ := by
    have := c.card_map_φ hDA' hA'K
    rw [hcard'] at this
    rw [c.card_Γ]
    exact Nat.eq_of_mul_eq_mul_right hDpos (by rw [this]; ring)
  have hne' : (A.subgroupOf K).map φ ≠ (A'.subgroupOf K).map φ := by
    intro h
    apply hne
    have h1 := c.comap_map_φ hDA
    have h2 := c.comap_map_φ hDA'
    rw [h] at h1
    have h3 : A.subgroupOf K = A'.subgroupOf K := h1.symm.trans h2
    ext x
    constructor
    · intro hx
      have := (Subgroup.ext_iff.1 h3 ⟨x, hAK hx⟩).1 (Subgroup.mem_subgroupOf.2 hx)
      exact Subgroup.mem_subgroupOf.1 this
    · intro hx
      have := (Subgroup.ext_iff.1 h3 ⟨x, hA'K hx⟩).2 (Subgroup.mem_subgroupOf.2 hx)
      exact Subgroup.mem_subgroupOf.1 this
  have hSylĀ := isSylowOf_top_sl2 c.card_Γ_pow hm hcardĀ
  have hSylĀ' := isSylowOf_top_sl2 c.card_Γ_pow hm hcardĀ'
  have hsup := CFSG.LocalAnalysis.EvenBN.U5.Prelim.sup_eq_of_isSylowOf_ne c.card_Γ_pow hm
    (Subgroup.topEquiv : (⊤ : Subgroup SL(2, Γ)) ≃* SL(2, Γ)) hSylĀ hSylĀ' hne'
  constructor
  · refine le_antisymm (sup_le hAK hA'K) (fun x hx => ?_)
    have hφx : φ ⟨x, hx⟩ ∈ (⊤ : Subgroup SL(2, Γ)) := Subgroup.mem_top _
    rw [← hsup, ← Subgroup.map_sup] at hφx
    obtain ⟨y, hy, hyx⟩ := hφx
    have hy' : y ∈ (A ⊔ A').subgroupOf K := by
      have : A.subgroupOf K ⊔ A'.subgroupOf K ≤ (A ⊔ A').subgroupOf K :=
        sup_le (fun z hz => Subgroup.mem_subgroupOf.2
            (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 hz)))
          (fun z hz => Subgroup.mem_subgroupOf.2
            (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.1 hz)))
      exact this hy
    have hker : y⁻¹ * ⟨x, hx⟩ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
    rw [c.φ_ker, Subgroup.mem_subgroupOf] at hker
    have hDM : D ≤ A ⊔ A' := hDA.trans le_sup_left
    have : x = (y : 𝔊) * ((y : 𝔊)⁻¹ * x) := by group
    rw [this]
    exact mul_mem (Subgroup.mem_subgroupOf.1 hy') (hDM hker)
  · refine le_antisymm (fun x hx => ?_) (le_inf hDA hDA')
    obtain ⟨hxA, hxA'⟩ := mem_inf.1 hx
    by_contra hxD
    have hxK : x ∈ K := hAK hxA
    have hφ1 : φ ⟨x, hxK⟩ ≠ 1 := by
      intro h1
      apply hxD
      have : (⟨x, hxK⟩ : ↥K) ∈ φ.ker := h1
      rw [c.φ_ker, Subgroup.mem_subgroupOf] at this
      exact this
    exact hne' (eq_of_mem_of_card (Subgroup.topEquiv : (⊤ : Subgroup SL(2, Γ)) ≃* SL(2, Γ))
      le_top le_top hcardĀ hcardĀ' (s := φ ⟨x, hxK⟩)
      ⟨⟨x, hxK⟩, Subgroup.mem_subgroupOf.2 hxA, rfl⟩
      ⟨⟨x, hxK⟩, Subgroup.mem_subgroupOf.2 hxA', rfl⟩ hφ1)

end SL3

end E2Ctx

section NumTheory

theorem eq_of_pow_mul_eq_pow_mul {a b r m : ℕ} (hr : Odd r) (hm : Odd m)
    (h : 2 ^ a * r = 2 ^ b * m) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exfalso
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hab
    have : 2 ^ a * r = 2 ^ a * (2 ^ (d + 1) * m) := by
      rw [h, pow_add, pow_add]
      ring
    have h2 : r = 2 ^ (d + 1) * m := Nat.eq_of_mul_eq_mul_left (by positivity) this
    have : Even r := by
      rw [h2, pow_succ]
      exact ⟨2 ^ d * m, by ring⟩
    exact (Nat.not_even_iff_odd.2 hr) this
  · exact hab
  · exfalso
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hab
    have : 2 ^ b * (2 ^ (d + 1) * r) = 2 ^ b * m := by
      rw [← h, pow_add, pow_add]
      ring
    have h2 : 2 ^ (d + 1) * r = m := Nat.eq_of_mul_eq_mul_left (by positivity) this
    have : Even m := by
      rw [← h2, pow_succ]
      exact ⟨2 ^ d * r, by ring⟩
    exact (Nat.not_even_iff_odd.2 hm) this

end NumTheory

namespace E2Ctx

section ASylow

variable {𝔊 : Type*} [Group 𝔊] [Finite 𝔊] {f : ℕ} {Γ : Type} [Field Γ] [Finite Γ]
  {t u : 𝔊} {K D P Y W F J J₀ C : Subgroup 𝔊} {φ : ↥K →* SL(2, Γ)}
  (c : E2Ctx f Γ t u K D P Y W F J J₀ C φ)

include c

theorem card_N_mul : Nat.card ↥(K ⊔ Kᵍ[t]) * Nat.card D = Nat.card K * Nat.card K := by
  have h := Common.card_sup_mul_card_inf_eq c.Kt_le_normalizer_K
  rw [c.K_inf, card_conjg] at h
  exact h

theorem card_N : Nat.card ↥(K ⊔ Kᵍ[t]) = Nat.card D * Nat.card SL(2, Γ) * Nat.card SL(2, Γ) := by
  have h := c.card_N_mul
  rw [c.card_K] at h
  have hpos : 0 < Nat.card D := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h]
  ring

theorem P_isSylowOf_N : IsSylowOf 2 P (K ⊔ Kᵍ[t]) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨c.P_le_N, c.P_pgroup, ?_⟩
  have h1 := Subgroup.relIndex_mul_card P (K ⊔ Kᵍ[t])
  rw [inf_eq_left.mpr c.P_le_N, c.card_P, c.card_N, c.card_SL] at h1
  have hDpos : 0 < Nat.card D := Nat.card_pos
  set Q : ℕ := (2 ^ f) ^ 3 with hQ
  have hQpos : 0 < Q := by positivity
  have h2 : P.relIndex (K ⊔ Kᵍ[t]) = (Q ^ 2 - 1) * (Q ^ 2 - 1) := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hDpos (pow_pos hQpos 2))
    have hq6 : (2 ^ f) ^ 6 = Q ^ 2 := by rw [hQ]; ring
    rw [hq6] at h1
    rw [h1]
    ring
  rw [h2]
  have hodd : Odd (Q ^ 2 - 1) := by
    have hQe : Even Q := by
      rw [hQ, ← pow_mul]
      exact (Nat.even_pow' (by have := c.two_le; omega)).2 even_two
    have h4 : 4 ≤ Q ^ 2 := by
      have : 2 ≤ Q := by
        rcases hQe with ⟨r, hr⟩
        omega
      nlinarith
    have : Even (Q ^ 2) := by
      rcases hQe with ⟨r, hr⟩
      exact ⟨2 * r * r, by rw [hr]; ring⟩
    obtain ⟨r, hr⟩ := this
    exact ⟨r - 1, by omega⟩
  intro hdvd
  exact (Nat.not_even_iff_odd.2 (hodd.mul hodd)) (even_iff_two_dvd.2 hdvd)

end ASylow

end E2Ctx

namespace E2Ctx

section ASylow2

variable {𝔊 : Type*} [Group 𝔊] [Finite 𝔊] {f : ℕ} {Γ : Type} [Field Γ] [Finite Γ]
  {t u : 𝔊} {K D P Y W F J J₀ C : Subgroup 𝔊} {φ : ↥K →* SL(2, Γ)}
  (c : E2Ctx f Γ t u K D P Y W F J J₀ C φ)

include c

theorem A_isSylowOf_K : IsSylowOf 2 (P ⊓ K) K :=
  c.P_isSylowOf_N.inf_of_le_normalizer c.K_le_N c.N_le_normalizer_K

theorem card_A : Nat.card ↥(P ⊓ K) = Nat.card D * (2 ^ f) ^ 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := c.A_isSylowOf_K
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hS
  obtain ⟨hle, hp, hdvd⟩ := hS
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hp
  have h1 := Subgroup.relIndex_mul_card (P ⊓ K) K
  rw [inf_eq_left.mpr hle, ha, c.card_K, c.card_SL, c.card_D] at h1
  set m : ℕ := ((2 ^ f) ^ 3) ^ 2 - 1 with hm
  have hmodd : Odd m := by
    have hQe : Even ((2 ^ f) ^ 3) := by
      rw [← pow_mul]
      exact (Nat.even_pow' (by have := c.two_le; omega)).2 even_two
    have h4 : 4 ≤ ((2 ^ f) ^ 3) ^ 2 := by
      have : 2 ≤ (2 ^ f) ^ 3 := by
        rcases hQe with ⟨r, hr⟩
        have : 0 < (2 ^ f) ^ 3 := by positivity
        omega
      nlinarith
    have : Even (((2 ^ f) ^ 3) ^ 2) := by
      rcases hQe with ⟨r, hr⟩
      exact ⟨2 * r * r, by rw [hr]; ring⟩
    obtain ⟨r, hr⟩ := this
    exact ⟨r - 1, by omega⟩
  have hrodd : Odd ((P ⊓ K).relIndex K) := Nat.odd_iff.2 (by
    rcases Nat.even_or_odd ((P ⊓ K).relIndex K) with he | ho
    · exact absurd (even_iff_two_dvd.1 he) hdvd
    · exact Nat.odd_iff.1 ho)
  have h2 : 2 ^ a * (P ⊓ K).relIndex K = 2 ^ (19 * f) * m := by
    rw [mul_comm, h1]
    have : ((2 ^ f) ^ 16 * ((2 ^ f) ^ 3 * m)) = 2 ^ (19 * f) * m := by
      rw [← pow_mul, ← pow_mul]
      ring
    rw [this]
  have h3 : a = 19 * f := eq_of_pow_mul_eq_pow_mul hrodd hmodd h2
  rw [ha, h3, c.card_D, ← pow_mul, ← pow_mul, ← pow_add]
  ring_nf

end ASylow2

end E2Ctx

section ConjNormalizer

variable {G : Type*} [Group G]

theorem conjg_eq_of_mem_normalizer {X : Subgroup G} {g : G} (hg : g ∈ normalizer (X : Set G)) :
    Xᵍ[g] = X := by
  ext x
  rw [mem_conjg_iff]
  exact (mem_normalizer_iff.1 hg x).symm

theorem mem_normalizer_of_conjg_eq {X : Subgroup G} {g : G} (h : Xᵍ[g] = X) :
    g ∈ normalizer (X : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  rw [← mem_conjg_iff, h]

end ConjNormalizer

namespace E2Ctx

section AFacts

variable {𝔊 : Type*} [Group 𝔊] [Finite 𝔊] {f : ℕ} {Γ : Type} [Field Γ] [Finite Γ]
  {t u : 𝔊} {K D P Y W F J J₀ C : Subgroup 𝔊} {φ : ↥K →* SL(2, Γ)}
  (c : E2Ctx f Γ t u K D P Y W F J J₀ C φ)

include c

theorem D_le_A : D ≤ P ⊓ K := le_inf c.D_le_P c.D_le_K

theorem At_eq : (P ⊓ K)ᵍ[t] = P ⊓ Kᵍ[t] := by
  rw [conjg_inf, c.P_conj]

theorem A_inf_At : (P ⊓ K) ⊓ (P ⊓ K)ᵍ[t] = D := by
  rw [c.At_eq]
  apply le_antisymm
  · intro x hx
    obtain ⟨hxA, hxAt⟩ := mem_inf.1 hx
    rw [← c.K_inf]
    exact mem_inf.2 ⟨(mem_inf.1 hxA).2, (mem_inf.1 hxAt).2⟩
  · exact le_inf c.D_le_A (le_inf c.D_le_P c.D_le_Kt)

theorem A_comm_At : ⁅P ⊓ K, (P ⊓ K)ᵍ[t]⁆ ≤ D :=
  le_trans (commutator_mono inf_le_right (conjg_mono inf_le_right t)) c.comm_le

theorem P_le_normalizer_A : P ≤ normalizer ((P ⊓ K : Subgroup 𝔊) : Set 𝔊) := fun g hg =>
  Common.mem_normalizer_inf (le_normalizer hg) (c.N_le_normalizer_K (c.P_le_N hg))

theorem At_le_normalizer_A : (P ⊓ K)ᵍ[t] ≤ normalizer ((P ⊓ K : Subgroup 𝔊) : Set 𝔊) := by
  intro g hg
  rw [c.At_eq] at hg
  exact c.P_le_normalizer_A (mem_inf.1 hg).1

theorem P_eq_A_sup : P = (P ⊓ K) ⊔ (P ⊓ K)ᵍ[t] := by
  have hle : (P ⊓ K) ⊔ (P ⊓ K)ᵍ[t] ≤ P := by
    refine sup_le inf_le_left ?_
    rw [c.At_eq]
    exact inf_le_left
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  have h := Common.card_sup_mul_card_inf_eq c.At_le_normalizer_A
  rw [c.A_inf_At, card_conjg, c.card_A] at h
  have hDpos : 0 < Nat.card D := Nat.card_pos
  have h2 : Nat.card ↥((P ⊓ K) ⊔ (P ⊓ K)ᵍ[t]) = Nat.card D * (2 ^ f) ^ 6 := by
    apply Nat.eq_of_mul_eq_mul_right hDpos
    rw [h]
    ring
  rw [h2, c.card_P]

end AFacts

end E2Ctx

namespace E2Ctx

section Centralizer

variable {𝔊 : Type*} [Group 𝔊] [Finite 𝔊] {f : ℕ} {Γ : Type} [Field Γ] [Finite Γ]
  {t u : 𝔊} {K D P Y W F J J₀ C : Subgroup 𝔊} {φ : ↥K →* SL(2, Γ)}
  (c : E2Ctx f Γ t u K D P Y W F J J₀ C φ)

include c

theorem mem_D_of_commutators {z : 𝔊} (hz : z ∈ K) (hc : ∀ a ∈ K, z * a * z⁻¹ * a⁻¹ ∈ D) :
    z ∈ D := by
  haveI := c.charTwo
  have hcen : φ ⟨z, hz⟩ ∈ Subgroup.center SL(2, Γ) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := c.φ_surj g
    have h1 : (⟨z * k * z⁻¹ * k⁻¹, by
        exact K.mul_mem (K.mul_mem (K.mul_mem hz k.2) (K.inv_mem hz)) (K.inv_mem k.2)⟩ : ↥K) ∈
        φ.ker := by
      rw [c.φ_ker, Subgroup.mem_subgroupOf]
      exact hc k k.2
    rw [MonoidHom.mem_ker] at h1
    have h2 : φ ⟨z, hz⟩ * φ k * (φ ⟨z, hz⟩)⁻¹ * (φ k)⁻¹ = 1 := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact h1
    calc φ k * φ ⟨z, hz⟩ = (φ ⟨z, hz⟩ * φ k * (φ ⟨z, hz⟩)⁻¹ * (φ k)⁻¹)⁻¹ *
          (φ ⟨z, hz⟩ * φ k) := by group
      _ = φ ⟨z, hz⟩ * φ k := by rw [h2]; simp
  rw [center_sl2_eq_bot_of_charTwo, Subgroup.mem_bot] at hcen
  have : (⟨z, hz⟩ : ↥K) ∈ φ.ker := hcen
  rw [c.φ_ker, Subgroup.mem_subgroupOf] at this
  exact this

theorem mem_D_of_commutators_t {z : 𝔊} (hz : z ∈ Kᵍ[t])
    (hc : ∀ a ∈ Kᵍ[t], z * a * z⁻¹ * a⁻¹ ∈ D) : z ∈ D := by
  have hz' : t * z * t⁻¹ ∈ K := by
    have := mem_conjg_iff.1 hz
    exact this
  have h1 : t * z * t⁻¹ ∈ D := by
    refine c.mem_D_of_commutators hz' fun a ha => ?_
    have haKt : t⁻¹ * a * t ∈ Kᵍ[t] := by
      rw [mem_conjg_iff, show t * (t⁻¹ * a * t) * t⁻¹ = a by group]
      exact ha
    have := hc _ haKt
    have hDt : t * (z * (t⁻¹ * a * t) * z⁻¹ * (t⁻¹ * a * t)⁻¹) * t⁻¹ ∈ D := by
      have hmem : z * (t⁻¹ * a * t) * z⁻¹ * (t⁻¹ * a * t)⁻¹ ∈ Dᵍ[t] := by
        rw [c.D_conj]
        exact this
      exact mem_conjg_iff.1 hmem
    have e : t * (z * (t⁻¹ * a * t) * z⁻¹ * (t⁻¹ * a * t)⁻¹) * t⁻¹ =
        t * z * t⁻¹ * a * (t * z * t⁻¹)⁻¹ * a⁻¹ := by group
    rwa [e] at hDt
  have h2 : z ∈ Dᵍ[t] := mem_conjg_iff.2 h1
  rwa [c.D_conj] at h2

end Centralizer

end E2Ctx

namespace E2Ctx

section StepA

variable {𝔊 : Type*} [Group 𝔊] [Finite 𝔊] {f : ℕ} {Γ : Type} [Field Γ] [Finite Γ]
  {t u : 𝔊} {K D P Y W F J J₀ C : Subgroup 𝔊} {φ : ↥K →* SL(2, Γ)}
  (c : E2Ctx f Γ t u K D P Y W F J J₀ C φ)

include c

theorem t_mem_normalizer_N : t ∈ normalizer ((K ⊔ Kᵍ[t] : Subgroup 𝔊) : Set 𝔊) := by
  apply mem_normalizer_of_conjg_eq
  rw [conjg_sup, c.Kt_conj, sup_comm]

theorem centralizer_D_normalized {n x : 𝔊} (hn : n ∈ K ⊔ Kᵍ[t])
    (hx : ∀ d ∈ D, d * x = x * d) : ∀ d ∈ D, d * (n * x * n⁻¹) = (n * x * n⁻¹) * d := by
  intro d hd
  have hd' : n⁻¹ * d * n ∈ D := by
    have := (mem_normalizer_iff.1 (c.N_le_normalizer_D (inv_mem hn)) d).1 hd
    simpa using this
  have := hx _ hd'
  calc d * (n * x * n⁻¹) = n * ((n⁻¹ * d * n) * x) * n⁻¹ := by group
    _ = n * (x * (n⁻¹ * d * n)) * n⁻¹ := by rw [this]
    _ = (n * x * n⁻¹) * d := by group

theorem N_inf_centralizer_D : (K ⊔ Kᵍ[t]) ⊓ centralizer (D : Set 𝔊) = D := by
  haveI := c.charTwo
  set N := K ⊔ Kᵍ[t] with hN
  set Cc := N ⊓ centralizer (D : Set 𝔊) with hCc
  have hDN : D ≤ N := c.D_le_K.trans le_sup_left
  have hDC : D ≤ Cc := le_inf hDN (fun x hx => mem_centralizer_iff.2 fun y hy => c.D_comm y hy x hx)
  have hmemCc : ∀ x, x ∈ Cc ↔ x ∈ N ∧ ∀ d ∈ D, d * x = x * d := fun x => by
    simp only [hCc, mem_inf, mem_centralizer_iff, SetLike.mem_coe]
  have hCcN : ∀ n ∈ N, ∀ x ∈ Cc, n * x * n⁻¹ ∈ Cc := fun n hn x hx => by
    obtain ⟨hxN, hxc⟩ := (hmemCc x).1 hx
    exact (hmemCc _).2 ⟨mul_mem (mul_mem hn hxN) (inv_mem hn), c.centralizer_D_normalized hn hxc⟩
  have htN : ∀ y ∈ N, t * y * t⁻¹ ∈ N := fun y hy =>
    (mem_normalizer_iff.1 c.t_mem_normalizer_N y).1 hy
  have htD : ∀ d ∈ D, t⁻¹ * d * t ∈ D := fun d hd => by
    have : d ∈ Dᵍ[t] := by rw [c.D_conj]; exact hd
    have h1 := mem_conjg_iff.1 this
    rw [c.t_inv] at h1 ⊢
    exact h1
  have hCct : ∀ x ∈ Cc, t * x * t⁻¹ ∈ Cc := by
    intro x hx
    obtain ⟨hxN, hxc⟩ := (hmemCc x).1 hx
    refine (hmemCc _).2 ⟨htN x hxN, fun d hd => ?_⟩
    have := hxc _ (htD d hd)
    calc d * (t * x * t⁻¹) = t * ((t⁻¹ * d * t) * x) * t⁻¹ := by group
      _ = t * (x * (t⁻¹ * d * t)) * t⁻¹ := by rw [this]
      _ = (t * x * t⁻¹) * d := by group
  have hCct' : ∀ x ∈ Cc, t⁻¹ * x * t ∈ Cc := fun x hx => by
    have h1 := hCct x hx
    rw [c.t_inv] at h1 ⊢
    exact h1
  have hdich : Cc ⊓ K ≤ D ∨ K ≤ Cc := by
    have hnormM : (((Cc ⊓ K).subgroupOf K).map φ).Normal := by
      refine ⟨fun m hm g => ?_⟩
      obtain ⟨y, hy, rfl⟩ := hm
      obtain ⟨k, rfl⟩ := c.φ_surj g
      have hy' : y ∈ (Cc ⊓ K).subgroupOf K := hy
      have hy'' := Subgroup.mem_subgroupOf.1 hy'
      obtain ⟨hyC, hyK⟩ := mem_inf.1 hy''
      refine ⟨k * y * k⁻¹, ?_, by simp⟩
      show k * y * k⁻¹ ∈ (Cc ⊓ K).subgroupOf K
      rw [Subgroup.mem_subgroupOf]
      exact mem_inf.2 ⟨hCcN k (Subgroup.mem_sup_left k.2) y hyC,
        K.mul_mem (K.mul_mem k.2 hyK) (K.inv_mem k.2)⟩
    haveI := hnormM
    haveI := Common.sl2_isSimpleGroup_of_charTwo c.four_le_card_Γ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (((Cc ⊓ K).subgroupOf K).map φ) with hM | hM
    · left
      intro x hx
      obtain ⟨hxC, hxK⟩ := mem_inf.1 hx
      have h1 : φ ⟨x, hxK⟩ ∈ ((Cc ⊓ K).subgroupOf K).map φ :=
        ⟨⟨x, hxK⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
      rw [hM, Subgroup.mem_bot] at h1
      have : (⟨x, hxK⟩ : ↥K) ∈ φ.ker := h1
      rw [c.φ_ker, Subgroup.mem_subgroupOf] at this
      exact this
    · right
      intro x hx
      have h1 : φ ⟨x, hx⟩ ∈ ((Cc ⊓ K).subgroupOf K).map φ := by
        rw [hM]
        exact Subgroup.mem_top _
      obtain ⟨y, hy, hyx⟩ := h1
      have hker : y⁻¹ * ⟨x, hx⟩ ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
      rw [c.φ_ker, Subgroup.mem_subgroupOf] at hker
      have hyC : (y : 𝔊) ∈ Cc := (mem_inf.1 (Subgroup.mem_subgroupOf.1 hy)).1
      have : x = (y : 𝔊) * ((y : 𝔊)⁻¹ * x) := by group
      rw [this]
      exact mul_mem hyC (hDC hker)
  have hCKt_of : Cc ⊓ K ≤ D → Cc ⊓ Kᵍ[t] ≤ D := by
    intro h x hx
    obtain ⟨hxC, hxK⟩ := mem_inf.1 hx
    have h1 : t * x * t⁻¹ ∈ D := h (mem_inf.2 ⟨hCct x hxC, mem_conjg_iff.1 hxK⟩)
    have : x ∈ Dᵍ[t] := mem_conjg_iff.2 h1
    rwa [c.D_conj] at this
  have hCK : Cc ⊓ K ≤ D := by
    rcases hdich with h | h
    · exact h
    exfalso
    have hKt : Kᵍ[t] ≤ Cc := by
      intro x hx
      have h1 : t * x * t⁻¹ ∈ Cc := h (mem_conjg_iff.1 hx)
      have := hCct' _ h1
      rwa [show t⁻¹ * (t * x * t⁻¹) * t = x by group] at this
    have hNC : N ≤ Cc := sup_le h hKt
    have hDY : D ≤ Y := fun d hd => (c.mem_Y d).2 ⟨c.D_le_P hd, fun p hp =>
      mem_centralizer_iff.1 (mem_inf.1 (hNC (c.P_le_N hp))).2 d hd⟩
    have h1 := Subgroup.card_le_of_le hDY
    rw [c.card_D, c.card_Y] at h1
    have h2 : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := c.two_le; omega)
    have h3 : (2 ^ f) ^ 2 < (2 ^ f) ^ 16 := Nat.pow_lt_pow_right h2 (by norm_num)
    omega
  have hCKt : Cc ⊓ Kᵍ[t] ≤ D := hCKt_of hCK
  refine le_antisymm (fun x hx => ?_) hDC
  obtain ⟨hxN, hxc⟩ := (hmemCc x).1 hx
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right K Kᵍ[t] c.K_le_normalizer_Kt
  obtain ⟨k, hk, k', hk', hkk⟩ : ∃ k ∈ K, ∃ k' ∈ Kᵍ[t], k * k' = x := by
    have : x ∈ (K : Set 𝔊) * (Kᵍ[t] : Set 𝔊) := by
      rw [← hmul]
      exact hxN
    exact Set.mem_mul.1 this
  have hDnorm : ∀ n ∈ N, ∀ d ∈ D, n * d * n⁻¹ ∈ D := fun n hn d hd =>
    (mem_normalizer_iff.1 (c.N_le_normalizer_D hn) d).1 hd
  have hKN : K ≤ N := le_sup_left
  have hKtN : Kᵍ[t] ≤ N := le_sup_right
  have hid : ∀ a : 𝔊, x * a * x⁻¹ * a⁻¹ =
      (k * (k' * a * k'⁻¹ * a⁻¹) * k⁻¹) * (k * a * k⁻¹ * a⁻¹) := fun a => by
    rw [← hkk]
    group
  have hxa : ∀ a ∈ K, x * a * x⁻¹ * a⁻¹ ∈ D := fun a ha => by
    apply hCK
    have e : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
    refine mem_inf.2 ⟨?_, ?_⟩
    · rw [e]
      exact mul_mem hx (hCcN a (hKN ha) x⁻¹ (inv_mem hx)) |> fun h => by
        have := hCcN a (hKN ha) x⁻¹ (inv_mem hx)
        exact mul_mem hx this
    · exact K.mul_mem ((mem_normalizer_iff.1 (c.N_le_normalizer_K hxN) a).1 ha) (K.inv_mem ha)
  have hxa' : ∀ a ∈ Kᵍ[t], x * a * x⁻¹ * a⁻¹ ∈ D := fun a ha => by
    apply hCKt
    have e : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
    refine mem_inf.2 ⟨?_, ?_⟩
    · rw [e]
      exact mul_mem hx (hCcN a (hKtN ha) x⁻¹ (inv_mem hx))
    · exact Kᵍ[t].mul_mem ((mem_normalizer_iff.1 (c.N_le_normalizer_Kt hxN) a).1 ha)
        (Kᵍ[t].inv_mem ha)
  have hk_D : k ∈ D := by
    refine c.mem_D_of_commutators hk (fun a ha => ?_)
    have h1 : ⁅k', a⁆ ∈ D := by
      rw [← commutatorElement_inv]
      exact inv_mem (c.comm_le (commutator_mem_commutator ha hk'))
    rw [commutatorElement_def] at h1
    have h2 := hDnorm k (hKN hk) _ h1
    have h3 := hxa a ha
    have : k * a * k⁻¹ * a⁻¹ = (k * (k' * a * k'⁻¹ * a⁻¹) * k⁻¹)⁻¹ * (x * a * x⁻¹ * a⁻¹) := by
      rw [hid a]
      group
    rw [this]
    exact mul_mem (inv_mem h2) h3
  have hk'_D : k' ∈ D := by
    refine c.mem_D_of_commutators_t hk' (fun a ha => ?_)
    have h1 : k * a * k⁻¹ * a⁻¹ ∈ D := by
      have := c.comm_le (commutator_mem_commutator hk ha)
      rwa [commutatorElement_def] at this
    have h3 := hxa' a ha
    have : k' * a * k'⁻¹ * a⁻¹ = k⁻¹ * ((x * a * x⁻¹ * a⁻¹) * (k * a * k⁻¹ * a⁻¹)⁻¹) * k := by
      rw [hid a]
      group
    rw [this]
    have h4 := hDnorm k⁻¹ (inv_mem (hKN hk)) _ (mul_mem h3 (inv_mem h1))
    simpa using h4
  rw [← hkk]
  exact mul_mem hk_D hk'_D

end StepA

end E2Ctx

section PGroupCenter

variable {G : Type*} [Group G] [Finite G]

theorem exists_ne_one_central_of_pgroup {M : Subgroup G} (hM : IsPGroup 2 M) (hne : M ≠ ⊥) :
    ∃ z ∈ M, z ≠ 1 ∧ ∀ m ∈ M, z * m = m * z := by
  haveI : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).2 hne
  have h1 := hM.bot_lt_center
  obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 (bot_lt_iff_ne_bot.1 h1)
  refine ⟨((z : ↥(Subgroup.center ↥M)) : ↥M), ((z : ↥(Subgroup.center ↥M)) : ↥M).2, ?_,
    fun m hm => ?_⟩
  · intro h
    apply hz1
    exact Subtype.ext (Subtype.ext h)
  · exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨m, hm⟩)).symm

end PGroupCenter

namespace E2Ctx

section UFacts

variable {𝔊 : Type*} [Group 𝔊] [Finite 𝔊] {f : ℕ} {Γ : Type} [Field Γ] [Finite Γ]
  {t u : 𝔊} {K D P Y W F J J₀ C : Subgroup 𝔊} {φ : ↥K →* SL(2, Γ)}
  (c : E2Ctx f Γ t u K D P Y W F J J₀ C φ)

include c

theorem u_mem_normalizer_K : u ∈ normalizer (K : Set 𝔊) := c.N_le_normalizer_K c.u_mem_N

theorem Ku_conj : Kᵍ[u] = K := conjg_eq_of_mem_normalizer c.u_mem_normalizer_K

theorem Du_conj : Dᵍ[u] = D := conjg_eq_of_mem_normalizer (c.N_le_normalizer_D c.u_mem_N)

theorem Au_ne : (P ⊓ K)ᵍ[u] ≠ P ⊓ K := by
  intro h
  apply c.u_not_mem_normalizer_P
  apply mem_normalizer_of_conjg_eq
  have e : ((P ⊓ K)ᵍ[t])ᵍ[u] = ((P ⊓ K)ᵍ[u])ᵍ[t] := by
    rw [conjg_conjg, conjg_conjg, c.t_comm_u]
  calc Pᵍ[u] = ((P ⊓ K) ⊔ (P ⊓ K)ᵍ[t])ᵍ[u] := by rw [← c.P_eq_A_sup]
    _ = (P ⊓ K)ᵍ[u] ⊔ ((P ⊓ K)ᵍ[t])ᵍ[u] := conjg_sup _ _ _
    _ = (P ⊓ K) ⊔ (P ⊓ K)ᵍ[t] := by rw [e, h]
    _ = P := c.P_eq_A_sup.symm

theorem D_le_Au : D ≤ (P ⊓ K)ᵍ[u] := by
  have := conjg_mono c.D_le_A u
  rwa [c.Du_conj] at this

theorem Au_le_K : (P ⊓ K)ᵍ[u] ≤ K := by
  have := conjg_mono (inf_le_right : P ⊓ K ≤ K) u
  rwa [c.Ku_conj] at this

theorem K_eq_A_sup_Au_and : (P ⊓ K) ⊔ (P ⊓ K)ᵍ[u] = K ∧ (P ⊓ K) ⊓ (P ⊓ K)ᵍ[u] = D :=
  c.sylow_sup_inf c.D_le_A c.D_le_Au inf_le_right c.Au_le_K c.card_A
    (by rw [card_conjg, c.card_A]) c.Au_ne.symm

theorem K_eq_A_sup_Au : K = (P ⊓ K) ⊔ (P ⊓ K)ᵍ[u] := c.K_eq_A_sup_Au_and.1.symm

theorem A_inf_Au : (P ⊓ K) ⊓ (P ⊓ K)ᵍ[u] = D := c.K_eq_A_sup_Au_and.2

end UFacts

end E2Ctx

section ZcLemmas

variable {G : Type*} [Group G]

theorem mem_zc_iff {X : Subgroup G} {x : G} : x ∈ zc X ↔ x ∈ X ∧ ∀ y ∈ X, y * x = x * y := by
  simp only [zc, mem_inf, mem_centralizer_iff, SetLike.mem_coe]

theorem zc_le (X : Subgroup G) : zc X ≤ X := inf_le_left

end ZcLemmas

namespace E2Ctx

section Step1Pre

variable {𝔊 : Type*} [Group 𝔊] [Finite 𝔊] {f : ℕ} {Γ : Type} [Field Γ] [Finite Γ]
  {t u : 𝔊} {K D P Y W F J J₀ C : Subgroup 𝔊} {φ : ↥K →* SL(2, Γ)}
  (c : E2Ctx f Γ t u K D P Y W F J J₀ C φ)

include c

theorem D_le_At : D ≤ (P ⊓ K)ᵍ[t] := by
  have := conjg_mono c.D_le_A t
  rwa [c.D_conj] at this

theorem zc_A_le_D : zc (P ⊓ K) ≤ D := by
  intro x hx
  obtain ⟨hxA, hxc⟩ := mem_zc_iff.1 hx
  have hxN : x ∈ K ⊔ Kᵍ[t] := c.P_le_N (mem_inf.1 hxA).1
  have hxD : x ∈ centralizer (D : Set 𝔊) :=
    mem_centralizer_iff.2 fun d hd => hxc d (c.D_le_A hd)
  rw [← c.N_inf_centralizer_D]
  exact mem_inf.2 ⟨hxN, hxD⟩

theorem zc_K_eq : zc K = zc (P ⊓ K) ⊓ (zc (P ⊓ K))ᵍ[u] := by
  rw [← zc_conjg]
  ext z
  rw [mem_inf, mem_zc_iff, mem_zc_iff, mem_zc_iff]
  constructor
  · rintro ⟨hzK, hzc⟩
    have hzD : z ∈ D := c.central_le_D hzK (fun k hk => (hzc k hk).symm)
    exact ⟨⟨c.D_le_A hzD, fun y hy => hzc y (mem_inf.1 hy).2⟩,
      c.D_le_Au hzD, fun y hy => hzc y (c.Au_le_K hy)⟩
  · rintro ⟨⟨hzA, hzcA⟩, hzAu, hzcAu⟩
    refine ⟨(inf_le_right : P ⊓ K ≤ K) hzA, fun k hk => ?_⟩
    rw [c.K_eq_A_sup_Au] at hk
    have : k ∈ centralizer ({z} : Set 𝔊) := by
      refine (sup_le (fun a ha => ?_) (fun a ha => ?_) : (P ⊓ K) ⊔ (P ⊓ K)ᵍ[u] ≤ _) hk
      · exact mem_centralizer_singleton_iff.2 (hzcA a ha)
      · exact mem_centralizer_singleton_iff.2 (hzcAu a ha)
    exact mem_centralizer_singleton_iff.1 this

theorem Y_eq : Y = zc (P ⊓ K) ⊓ (zc (P ⊓ K))ᵍ[t] := by
  rw [← zc_conjg]
  ext y
  rw [c.mem_Y, mem_inf, mem_zc_iff, mem_zc_iff]
  constructor
  · rintro ⟨hyP, hyc⟩
    have hyD : y ∈ D := by
      rw [← c.N_inf_centralizer_D]
      exact mem_inf.2 ⟨c.P_le_N hyP, mem_centralizer_iff.2 fun d hd => (hyc d (c.D_le_P hd)).symm⟩
    refine ⟨⟨c.D_le_A hyD, fun a ha => (hyc a (mem_inf.1 ha).1).symm⟩, c.D_le_At hyD,
      fun a ha => ?_⟩
    have haP : a ∈ P := by
      have := (mem_inf.1 (by rw [← c.At_eq]; exact ha : a ∈ P ⊓ Kᵍ[t])).1
      exact this
    exact (hyc a haP).symm
  · rintro ⟨⟨hyA, hyc⟩, hyAt, hyc'⟩
    refine ⟨(inf_le_left : P ⊓ K ≤ P) hyA, fun p hp => ?_⟩
    rw [c.P_eq_A_sup] at hp
    have : p ∈ centralizer ({y} : Set 𝔊) := by
      refine (sup_le (fun a ha => ?_) (fun a ha => ?_) : (P ⊓ K) ⊔ (P ⊓ K)ᵍ[t] ≤ _) hp
      · exact mem_centralizer_singleton_iff.2 (hyc a ha)
      · exact mem_centralizer_singleton_iff.2 (hyc' a ha)
    exact (mem_centralizer_singleton_iff.1 this).symm

theorem D_ne_bot : D ≠ ⊥ := by
  intro h
  have h1 := c.card_D
  rw [h, Subgroup.card_bot] at h1
  have h2 : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := c.two_le; omega)
  have h3 : 1 < (2 ^ f) ^ 16 := Nat.one_lt_pow (by norm_num) h2
  omega

theorem zc_inf_conj_ne_bot : zc (P ⊓ K) ⊓ ((zc (P ⊓ K))ᵍ[u])ᵍ[t] ≠ ⊥ := by
  have hA₂K : ((P ⊓ K)ᵍ[u])ᵍ[t] ≤ Kᵍ[t] := conjg_mono c.Au_le_K t
  have hDA₂ : D ≤ ((P ⊓ K)ᵍ[u])ᵍ[t] := by
    have := conjg_mono (conjg_mono c.D_le_A u) t
    rwa [c.Du_conj, c.D_conj] at this
  have hA₂N : ((P ⊓ K)ᵍ[u])ᵍ[t] ≤ K ⊔ Kᵍ[t] := hA₂K.trans le_sup_right
  have hAN : P ⊓ K ≤ K ⊔ Kᵍ[t] := inf_le_right.trans le_sup_left
  have hnorm : P ⊓ K ≤ normalizer ((((P ⊓ K)ᵍ[u])ᵍ[t] : Subgroup 𝔊) : Set 𝔊) := by
    refine le_normalizer_of_commutator_le (X := ((P ⊓ K)ᵍ[u])ᵍ[t]) (Y := P ⊓ K) ?_
    rw [commutator_comm]
    exact (commutator_mono inf_le_right hA₂K).trans (c.comm_le.trans hDA₂)
  have hAp : IsPGroup 2 (P ⊓ K : Subgroup 𝔊) := c.P_pgroup.to_inf_left
  have hA₂p : IsPGroup 2 (((P ⊓ K)ᵍ[u])ᵍ[t] : Subgroup 𝔊) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hAp
    exact IsPGroup.of_card (n := n) (by rw [card_conjg, card_conjg, hn])
  have hMp := hAp.to_sup_of_normal_right' hA₂p hnorm
  have hMne : (P ⊓ K) ⊔ ((P ⊓ K)ᵍ[u])ᵍ[t] ≠ ⊥ := by
    intro h
    apply c.D_ne_bot
    rw [eq_bot_iff] at h ⊢
    exact (c.D_le_A.trans le_sup_left).trans h
  obtain ⟨z, hzM, hz1, hzc⟩ := exists_ne_one_central_of_pgroup hMp hMne
  have hzN : z ∈ K ⊔ Kᵍ[t] := (sup_le hAN hA₂N) hzM
  have hzD : z ∈ D := by
    rw [← c.N_inf_centralizer_D]
    refine mem_inf.2 ⟨hzN, mem_centralizer_iff.2 fun d hd => ?_⟩
    exact (hzc d (Subgroup.mem_sup_left (c.D_le_A hd))).symm
  intro hbot
  have hzmem : z ∈ zc (P ⊓ K) ⊓ ((zc (P ⊓ K))ᵍ[u])ᵍ[t] := by
    rw [← zc_conjg, ← zc_conjg, mem_inf, mem_zc_iff, mem_zc_iff]
    refine ⟨⟨c.D_le_A hzD, fun a ha => ?_⟩, hDA₂ hzD, fun a ha => ?_⟩
    · exact (hzc a (Subgroup.mem_sup_left ha)).symm
    · exact (hzc a (Subgroup.mem_sup_right ha)).symm
  rw [hbot] at hzmem
  exact hz1 (Subgroup.mem_bot.1 hzmem)

end Step1Pre

end E2Ctx

section Coprime

variable {G : Type*} [Group G] [Finite G]

theorem coprime_of_odd_of_card_two_pow {m : ℕ} {X : Subgroup G} (hm : Odd m)
    (hX : IsPGroup 2 X) : m.Coprime (Nat.card X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hX
  rw [hn]
  refine Nat.Coprime.pow_right n ?_
  refine ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 ?_).symm
  rcases hm with ⟨k, rfl⟩
  omega

theorem exists_fixed_mul_commutator {X S : Subgroup G} (hSX : S ≤ normalizer (X : Set G))
    (hsolv : Group.IsSolvable X) (hcop : (Nat.card S).Coprime (Nat.card X)) {x : G} (hx : x ∈ X) :
    ∃ c ∈ X ⊓ centralizer (S : Set G), ∃ n ∈ ⁅X, S⁆, x = c * n := by
  have hNM : ⁅X, S⁆ ≤ X := by
    rw [commutator_le]
    intro y hy s hs
    have : y * s * y⁻¹ * s⁻¹ = y * (s * y⁻¹ * s⁻¹) := by group
    rw [commutatorElement_def, this]
    exact mul_mem hy ((mem_normalizer_iff.1 (hSX hs) y⁻¹).1 (inv_mem hy))
  exact Common.exists_mem_inf_centralizer_mul_of_coprime hNM
    (Subgroup.normalizer_commutator_ge_left X S) hSX (Subgroup.normalizer_commutator_ge_right X S)
    hsolv hcop hx (fun s hs => by
      have := commutator_mem_commutator (inv_mem hx) hs
      rw [commutatorElement_def] at this
      have e : x⁻¹ * (s * x * s⁻¹) = x⁻¹ * s * x⁻¹⁻¹ * s⁻¹ := by group
      rw [e]
      exact this)

theorem commutator_fixed_eq_one {X S : Subgroup G} (habel : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
    (hSX : S ≤ normalizer (X : Set G)) (hcop : (Nat.card S).Coprime (Nat.card X)) {x : G}
    (hx : x ∈ ⁅S, X⁆) (hfix : ∀ s ∈ S, s * x * s⁻¹ * x⁻¹ = 1) : x = 1 := by
  have h := Common.mem_of_mem_commutator_sup_of_fixed (A := S) (Y := X) (Z := ⊥) bot_le
    (fun y hy y' hy' => by rw [Subgroup.mem_bot]; simp [habel y hy y' hy'])
    hSX (fun s _ => Subgroup.le_normalizer_of_normal (K := S) (H := ⊥) ‹_›) hcop (x := x)
    (mem_sup_left hx)
    (fun s hs => by rw [Subgroup.mem_bot]; exact hfix s hs)
  exact Subgroup.mem_bot.1 h

end Coprime

section ConjNormalizer2

variable {G : Type*} [Group G]

theorem mem_normalizer_conjg_iff {X : Subgroup G} {g h : G} :
    g ∈ normalizer ((Xᵍ[h] : Subgroup G) : Set G) ↔ h * g * h⁻¹ ∈ normalizer (X : Set G) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro H x
    have := H (h⁻¹ * x * h)
    rw [mem_conjg_iff, mem_conjg_iff] at this
    have e1 : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
    have e2 : h * (g * (h⁻¹ * x * h) * g⁻¹) * h⁻¹ = h * g * h⁻¹ * x * (h * g * h⁻¹)⁻¹ := by group
    rwa [e1, e2] at this
  · intro H y
    rw [mem_conjg_iff, mem_conjg_iff]
    have := H (h * y * h⁻¹)
    have e2 : h * (g * y * g⁻¹) * h⁻¹ = h * g * h⁻¹ * (h * y * h⁻¹) * (h * g * h⁻¹)⁻¹ := by group
    rwa [e2]

theorem conjg_pow_two_mul_eq {X : Subgroup G} {g : G} (h : Xᵍ[g * g] = X) (k : ℕ) :
    Xᵍ[g ^ (2 * k)] = X := by
  induction k with
  | zero => simpa using conjg_one X
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add, ← conjg_conjg, ih, pow_two, h]

end ConjNormalizer2

namespace E2Ctx

section NormalSubgroups

variable {𝔊 : Type*} [Group 𝔊] [Finite 𝔊] {f : ℕ} {Γ : Type} [Field Γ] [Finite Γ]
  {t u : 𝔊} {K D P Y W F J J₀ C : Subgroup 𝔊} {φ : ↥K →* SL(2, Γ)}
  (c : E2Ctx f Γ t u K D P Y W F J J₀ C φ)

include c

theorem dichotomy_K {X : Subgroup 𝔊} (hXN : ∀ n ∈ K ⊔ Kᵍ[t], ∀ x ∈ X, n * x * n⁻¹ ∈ X)
    (hDX : D ≤ X) : X ⊓ K ≤ D ∨ K ≤ X := by
  haveI := c.charTwo
  have hnormM : (((X ⊓ K).subgroupOf K).map φ).Normal := by
    refine ⟨fun m hm g => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hm
    obtain ⟨k, rfl⟩ := c.φ_surj g
    have hy' : y ∈ (X ⊓ K).subgroupOf K := hy
    have hy'' := Subgroup.mem_subgroupOf.1 hy'
    obtain ⟨hyC, hyK⟩ := mem_inf.1 hy''
    refine ⟨k * y * k⁻¹, ?_, by simp⟩
    show k * y * k⁻¹ ∈ (X ⊓ K).subgroupOf K
    rw [Subgroup.mem_subgroupOf]
    exact mem_inf.2 ⟨hXN k (Subgroup.mem_sup_left k.2) y hyC,
      K.mul_mem (K.mul_mem k.2 hyK) (K.inv_mem k.2)⟩
  haveI := hnormM
  haveI := Common.sl2_isSimpleGroup_of_charTwo c.four_le_card_Γ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (((X ⊓ K).subgroupOf K).map φ) with hM | hM
  · left
    intro x hx
    obtain ⟨hxC, hxK⟩ := mem_inf.1 hx
    have h1 : φ ⟨x, hxK⟩ ∈ ((X ⊓ K).subgroupOf K).map φ :=
      ⟨⟨x, hxK⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
    rw [hM, Subgroup.mem_bot] at h1
    have : (⟨x, hxK⟩ : ↥K) ∈ φ.ker := h1
    rw [c.φ_ker, Subgroup.mem_subgroupOf] at this
    exact this
  · right
    intro x hx
    have h1 : φ ⟨x, hx⟩ ∈ ((X ⊓ K).subgroupOf K).map φ := by
      rw [hM]
      exact Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := h1
    have hker : y⁻¹ * ⟨x, hx⟩ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
    rw [c.φ_ker, Subgroup.mem_subgroupOf] at hker
    have hyC : (y : 𝔊) ∈ X := (mem_inf.1 (Subgroup.mem_subgroupOf.1 hy)).1
    have : x = (y : 𝔊) * ((y : 𝔊)⁻¹ * x) := by group
    rw [this]
    exact mul_mem hyC (hDX hker)

theorem conjg_t_normalized {X : Subgroup 𝔊} (hXN : ∀ n ∈ K ⊔ Kᵍ[t], ∀ x ∈ X, n * x * n⁻¹ ∈ X) :
    ∀ n ∈ K ⊔ Kᵍ[t], ∀ x ∈ Xᵍ[t], n * x * n⁻¹ ∈ Xᵍ[t] := by
  intro n hn x hx
  rw [mem_conjg_iff] at hx ⊢
  have hn' : t * n * t⁻¹ ∈ K ⊔ Kᵍ[t] := (mem_normalizer_iff.1 c.t_mem_normalizer_N n).1 hn
  have := hXN _ hn' _ hx
  have e : t * (n * x * n⁻¹) * t⁻¹ = (t * n * t⁻¹) * (t * x * t⁻¹) * (t * n * t⁻¹)⁻¹ := by group
  rw [e]
  exact this

theorem dichotomy_Kt {X : Subgroup 𝔊} (hXN : ∀ n ∈ K ⊔ Kᵍ[t], ∀ x ∈ X, n * x * n⁻¹ ∈ X)
    (hDX : D ≤ X) : X ⊓ Kᵍ[t] ≤ D ∨ Kᵍ[t] ≤ X := by
  have hDXt : D ≤ Xᵍ[t] := by
    have := conjg_mono hDX t
    rwa [c.D_conj] at this
  rcases c.dichotomy_K (c.conjg_t_normalized hXN) hDXt with h | h
  · left
    intro x hx
    obtain ⟨hxX, hxK⟩ := mem_inf.1 hx
    have h1 : t * x * t⁻¹ ∈ Xᵍ[t] ⊓ K := by
      refine mem_inf.2 ⟨?_, mem_conjg_iff.1 hxK⟩
      rw [mem_conjg_iff]
      have e : t * (t * x * t⁻¹) * t⁻¹ = x := by
        rw [c.t_inv]
        calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
          _ = x := by rw [c.t_mul_t]; simp
      rw [e]
      exact hxX
    have h2 := h h1
    have : x ∈ Dᵍ[t] := mem_conjg_iff.2 h2
    rwa [c.D_conj] at this
  · right
    intro x hx
    have h1 : t * x * t⁻¹ ∈ Xᵍ[t] := h (mem_conjg_iff.1 hx)
    rw [mem_conjg_iff] at h1
    have e : t * (t * x * t⁻¹) * t⁻¹ = x := by
      rw [c.t_inv]
      calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
        _ = x := by rw [c.t_mul_t]; simp
    rwa [e] at h1

theorem le_D_of_inf_le_D {X : Subgroup 𝔊} (hXN : ∀ n ∈ K ⊔ Kᵍ[t], ∀ x ∈ X, n * x * n⁻¹ ∈ X)
    (hXle : X ≤ K ⊔ Kᵍ[t]) (h1 : X ⊓ K ≤ D) (h2 : X ⊓ Kᵍ[t] ≤ D) : X ≤ D := by
  intro x hx
  have hxN : x ∈ K ⊔ Kᵍ[t] := hXle hx
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right K Kᵍ[t] c.K_le_normalizer_Kt
  obtain ⟨k, hk, k', hk', hkk⟩ : ∃ k ∈ K, ∃ k' ∈ Kᵍ[t], k * k' = x := by
    have : x ∈ (K : Set 𝔊) * (Kᵍ[t] : Set 𝔊) := by
      rw [← hmul]
      exact hxN
    exact Set.mem_mul.1 this
  have hDnorm : ∀ n ∈ K ⊔ Kᵍ[t], ∀ d ∈ D, n * d * n⁻¹ ∈ D := fun n hn d hd =>
    (mem_normalizer_iff.1 (c.N_le_normalizer_D hn) d).1 hd
  have hKN : K ≤ K ⊔ Kᵍ[t] := le_sup_left
  have hKtN : Kᵍ[t] ≤ K ⊔ Kᵍ[t] := le_sup_right
  have hid : ∀ a : 𝔊, x * a * x⁻¹ * a⁻¹ =
      (k * (k' * a * k'⁻¹ * a⁻¹) * k⁻¹) * (k * a * k⁻¹ * a⁻¹) := fun a => by
    rw [← hkk]
    group
  have hxa : ∀ a ∈ K, x * a * x⁻¹ * a⁻¹ ∈ D := fun a ha => by
    apply h1
    have e : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
    refine mem_inf.2 ⟨?_, ?_⟩
    · rw [e]
      exact mul_mem hx (hXN a (hKN ha) x⁻¹ (inv_mem hx))
    · exact K.mul_mem ((mem_normalizer_iff.1 (c.N_le_normalizer_K hxN) a).1 ha) (K.inv_mem ha)
  have hxa' : ∀ a ∈ Kᵍ[t], x * a * x⁻¹ * a⁻¹ ∈ D := fun a ha => by
    apply h2
    have e : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
    refine mem_inf.2 ⟨?_, ?_⟩
    · rw [e]
      exact mul_mem hx (hXN a (hKtN ha) x⁻¹ (inv_mem hx))
    · exact Kᵍ[t].mul_mem ((mem_normalizer_iff.1 (c.N_le_normalizer_Kt hxN) a).1 ha)
        (Kᵍ[t].inv_mem ha)
  have hk_D : k ∈ D := by
    refine c.mem_D_of_commutators hk (fun a ha => ?_)
    have h1' : ⁅k', a⁆ ∈ D := by
      rw [← commutatorElement_inv]
      exact inv_mem (c.comm_le (commutator_mem_commutator ha hk'))
    rw [commutatorElement_def] at h1'
    have h2' := hDnorm k (hKN hk) _ h1'
    have h3 := hxa a ha
    have : k * a * k⁻¹ * a⁻¹ = (k * (k' * a * k'⁻¹ * a⁻¹) * k⁻¹)⁻¹ * (x * a * x⁻¹ * a⁻¹) := by
      rw [hid a]
      group
    rw [this]
    exact mul_mem (inv_mem h2') h3
  have hk'_D : k' ∈ D := by
    refine c.mem_D_of_commutators_t hk' (fun a ha => ?_)
    have h1' : k * a * k⁻¹ * a⁻¹ ∈ D := by
      have := c.comm_le (commutator_mem_commutator hk ha)
      rwa [commutatorElement_def] at this
    have h3 := hxa' a ha
    have : k' * a * k'⁻¹ * a⁻¹ = k⁻¹ * ((x * a * x⁻¹ * a⁻¹) * (k * a * k⁻¹ * a⁻¹)⁻¹) * k := by
      rw [hid a]
      group
    rw [this]
    have h4 := hDnorm k⁻¹ (inv_mem (hKN hk)) _ (mul_mem h3 (inv_mem h1'))
    simpa using h4
  rw [← hkk]
  exact mul_mem hk_D hk'_D

end NormalSubgroups

end E2Ctx

namespace E2Ctx

section JNormalizer

variable {𝔊 : Type*} [Group 𝔊] [Finite 𝔊] {f : ℕ} {Γ : Type} [Field Γ] [Finite Γ]
  {t u : 𝔊} {K D P Y W F J J₀ C : Subgroup 𝔊} {φ : ↥K →* SL(2, Γ)}
  (c : E2Ctx f Γ t u K D P Y W F J J₀ C φ)

include c

theorem card_D_lt_card_K : Nat.card D < Nat.card K := by
  rw [c.card_K]
  have hDpos : 0 < Nat.card D := Nat.card_pos
  have : 1 < Nat.card SL(2, Γ) := by
    rw [c.card_SL]
    have h2 : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := c.two_le; omega)
    have h3 : 1 < (2 ^ f) ^ 3 := Nat.one_lt_pow (by norm_num) h2
    have h4 : 1 < ((2 ^ f) ^ 3) ^ 2 - 1 := by
      have : 4 ≤ ((2 ^ f) ^ 3) ^ 2 := by nlinarith
      omega
    nlinarith
  nlinarith

theorem J_le_normalizer_D : J ≤ normalizer (D : Set 𝔊) := fun j hj => by
  have h := Common.mem_normalizer_sup (c.J_nor_W hj)
    (mem_normalizer_conjg_iff.2 (c.J_nor_W (c.J_conj_u j hj)))
  rwa [← c.D_eq_sup] at h

theorem J_le_normalizer_K : J ≤ normalizer (K : Set 𝔊) := by
  intro j hj
  have hjN := c.J_nor_N hj
  have hjD := c.J_le_normalizer_D hj
  have hNj : (K ⊔ Kᵍ[t])ᵍ[j] = K ⊔ Kᵍ[t] := conjg_eq_of_mem_normalizer hjN
  have hDj : Dᵍ[j] = D := conjg_eq_of_mem_normalizer hjD
  have hKjle : Kᵍ[j] ≤ K ⊔ Kᵍ[t] := by
    have := conjg_mono (c.K_le_N) j
    rwa [hNj] at this
  have hDKj : D ≤ Kᵍ[j] := by
    have := conjg_mono c.D_le_K j
    rwa [hDj] at this
  have hKjN : ∀ n ∈ K ⊔ Kᵍ[t], ∀ x ∈ Kᵍ[j], n * x * n⁻¹ ∈ Kᵍ[j] := by
    intro n hn x hx
    rw [mem_conjg_iff] at hx ⊢
    have hn' : j * n * j⁻¹ ∈ K ⊔ Kᵍ[t] := by
      have := (mem_normalizer_iff.1 hjN n).1 hn
      exact this
    have := (mem_normalizer_iff.1 (c.N_le_normalizer_K hn') _).1 hx
    have e : j * (n * x * n⁻¹) * j⁻¹ = (j * n * j⁻¹) * (j * x * j⁻¹) * (j * n * j⁻¹)⁻¹ := by group
    rw [e]
    exact this
  have hcardKj : Nat.card ↥(Kᵍ[j]) = Nat.card K := card_conjg K j
  have key : Kᵍ[j] = K ∨ Kᵍ[j] = Kᵍ[t] := by
    rcases c.dichotomy_K hKjN hDKj with h1 | h1
    · rcases c.dichotomy_Kt hKjN hDKj with h2 | h2
      · exfalso
        have hle := c.le_D_of_inf_le_D hKjN hKjle h1 h2
        have := Subgroup.card_le_of_le hle
        rw [hcardKj] at this
        exact absurd this (not_le.2 c.card_D_lt_card_K)
      · right
        exact (Subgroup.eq_of_le_of_card_ge h2 (by rw [hcardKj, card_conjg])).symm
    · left
      exact (Subgroup.eq_of_le_of_card_ge h1 hcardKj.le).symm
  rcases key with h | h
  · exact mem_normalizer_of_conjg_eq h
  · exfalso
    have hjt : j * t = t * j := mem_centralizer_singleton_iff.1 (c.J_cen_t hj)
    have hKjj : Kᵍ[j * j] = K := by
      calc Kᵍ[j * j] = (Kᵍ[j])ᵍ[j] := (conjg_conjg K j j).symm
        _ = (Kᵍ[t])ᵍ[j] := by rw [h]
        _ = Kᵍ[t * j] := conjg_conjg K t j
        _ = Kᵍ[j * t] := by rw [hjt]
        _ = (Kᵍ[j])ᵍ[t] := (conjg_conjg K j t).symm
        _ = (Kᵍ[t])ᵍ[t] := by rw [h]
        _ = K := c.Kt_conj
    obtain ⟨k, hk⟩ := Odd.of_dvd_nat c.J_odd (Subgroup.orderOf_dvd_natCard J hj)
    have hpow : j ^ (2 * (k + 1)) = j := by
      rw [show 2 * (k + 1) = orderOf j + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]
    have hKj : Kᵍ[j] = K := by
      have := conjg_pow_two_mul_eq hKjj (k + 1)
      rwa [hpow] at this
    have hKKt : K = Kᵍ[t] := hKj.symm.trans h
    have hDK : D = K := by rw [← c.K_inf, ← hKKt, inf_idem]
    have := c.card_D_lt_card_K
    rw [hDK] at this
    exact lt_irrefl _ this

end JNormalizer

end E2Ctx

section ZcNormalizer

variable {G : Type*} [Group G]

theorem mem_normalizer_zc {X : Subgroup G} {g : G} (hg : g ∈ normalizer (X : Set G)) :
    g ∈ normalizer ((zc X : Subgroup G) : Set G) := by
  apply mem_normalizer_of_conjg_eq
  rw [← zc_conjg, conjg_eq_of_mem_normalizer hg]

theorem isSolvable_of_isPGroup_two [Finite G] {X : Subgroup G} (hX : IsPGroup 2 X) :
    Group.IsSolvable ↥X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hX.isNilpotent
  infer_instance

end ZcNormalizer

namespace E2Ctx

section Step1e

variable {𝔊 : Type*} [Group 𝔊] [Finite 𝔊] {f : ℕ} {Γ : Type} [Field Γ] [Finite Γ]
  {t u : 𝔊} {K D P Y W F J J₀ C : Subgroup 𝔊} {φ : ↥K →* SL(2, Γ)}
  (c : E2Ctx f Γ t u K D P Y W F J J₀ C φ)

include c

theorem Y_le_W : Y ≤ W := fun y hy => (c.mem_W y).2 ⟨((c.mem_Y y).1 hy).1, fun p hp => by
  have := ((c.mem_Y y).1 hy).2 p hp
  rw [this, mul_inv_cancel_right, mul_inv_cancel]
  exact one_mem Y⟩

theorem W_le_F : W ≤ F := fun w hw => (c.mem_F w).2 ⟨((c.mem_W w).1 hw).1, fun p hp =>
  c.Y_le_W (((c.mem_W w).1 hw).2 p hp)⟩

theorem Y_le_D : Y ≤ D := (c.Y_le_W.trans c.W_le_F).trans c.F_le_D

theorem W_le_D : W ≤ D := c.W_le_F.trans c.F_le_D

theorem odd_card_J₀ : Odd (Nat.card J₀) :=
  Odd.of_dvd_nat c.J_odd (Subgroup.card_dvd_of_le c.J₀_le_J)

theorem J_le_normalizer_A : J ≤ normalizer ((P ⊓ K : Subgroup 𝔊) : Set 𝔊) := fun j hj =>
  Common.mem_normalizer_inf (c.J_nor_P hj) (c.J_le_normalizer_K hj)

theorem J_le_normalizer_zcA : J ≤ normalizer ((zc (P ⊓ K) : Subgroup 𝔊) : Set 𝔊) := fun j hj =>
  mem_normalizer_zc (c.J_le_normalizer_A hj)

theorem J₀_normalizes_Wu {j : 𝔊} (hj : j ∈ J₀) : j ∈ normalizer ((Wᵍ[u] : Subgroup 𝔊) : Set 𝔊) :=
  mem_normalizer_conjg_iff.2 (c.J_nor_W (c.J₀_le_J (c.J₀_conj_u j hj)))

theorem centralizer_J₀_D {d : 𝔊} (hd : d ∈ D) (hc : ∀ j ∈ J₀, j * d = d * j) :
    d ∈ Y ⊔ Yᵍ[u] := by
  have hWWu : W ≤ normalizer ((Wᵍ[u] : Subgroup 𝔊) : Set 𝔊) := fun w hw => by
    refine mem_normalizer_fintype fun x hx => ?_
    have hxD : x ∈ D := by
      have : x ∈ Wᵍ[u] := hx
      rw [c.D_eq_sup]
      exact Subgroup.mem_sup_right this
    have : w * x * w⁻¹ = x := by
      rw [c.D_comm w (c.W_le_D hw) x hxD, mul_inv_cancel_right]
    rw [this]
    exact hx
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right W Wᵍ[u] hWWu
  obtain ⟨w, hw, w', hw', hww⟩ : ∃ w ∈ W, ∃ w' ∈ Wᵍ[u], w * w' = d := by
    have : d ∈ (W : Set 𝔊) * (Wᵍ[u] : Set 𝔊) := by
      rw [← hmul, ← c.D_eq_sup]
      exact hd
    exact Set.mem_mul.1 this
  have hw'D : w' ∈ D := by
    rw [c.D_eq_sup]
    exact Subgroup.mem_sup_right hw'
  have hwD : w ∈ D := c.W_le_D hw
  have hfix : ∀ j ∈ J₀, j * w * j⁻¹ = w ∧ j * w' * j⁻¹ = w' := by
    intro j hj
    have h1 : j * w * j⁻¹ ∈ W := (mem_normalizer_iff.1 (c.J_nor_W (c.J₀_le_J hj)) w).1 hw
    have h2 : j * w' * j⁻¹ ∈ Wᵍ[u] := (mem_normalizer_iff.1 (c.J₀_normalizes_Wu hj) w').1 hw'
    have hD1 : j * w * j⁻¹ ∈ D := c.W_le_D h1
    have hD2 : j * w' * j⁻¹ ∈ D := by
      rw [c.D_eq_sup]
      exact Subgroup.mem_sup_right h2
    have hjd : j * (w * w') * j⁻¹ = w * w' := by
      rw [hww, hc j hj, mul_inv_cancel_right]
    have e : j * (w * w') * j⁻¹ = (j * w * j⁻¹) * (j * w' * j⁻¹) := by group
    rw [e] at hjd
    have h3 : w⁻¹ * (j * w * j⁻¹) = w' * (j * w' * j⁻¹)⁻¹ := by
      have h4 : (j * w * j⁻¹) * (j * w' * j⁻¹) = w * w' := hjd
      calc w⁻¹ * (j * w * j⁻¹) = w⁻¹ * ((j * w * j⁻¹) * (j * w' * j⁻¹)) * (j * w' * j⁻¹)⁻¹ := by
            group
        _ = w⁻¹ * (w * w') * (j * w' * j⁻¹)⁻¹ := by rw [h4]
        _ = w' * (j * w' * j⁻¹)⁻¹ := by group
    have h5 : w⁻¹ * (j * w * j⁻¹) ∈ W ⊓ Wᵍ[u] :=
      mem_inf.2 ⟨mul_mem (inv_mem hw) h1, by rw [h3]; exact mul_mem hw' (inv_mem h2)⟩
    rw [c.W_inf, Subgroup.mem_bot] at h5
    have h6 : j * w * j⁻¹ = w := by
      have := mul_left_cancel (a := w⁻¹) (h5.trans (inv_mul_cancel w).symm)
      exact this
    refine ⟨h6, ?_⟩
    rw [h6] at hjd
    exact mul_left_cancel hjd
  have hwY : w ∈ Y := by
    rw [← c.W_inf_cen]
    refine mem_inf.2 ⟨hw, mem_centralizer_iff.2 fun j hj => ?_⟩
    have := (hfix j hj).1
    calc j * w = (j * w * j⁻¹) * j := by group
      _ = w * j := by rw [this]
  have hw'Y : w' ∈ Yᵍ[u] := by
    rw [mem_conjg_iff]
    have hx : u * w' * u⁻¹ ∈ W := mem_conjg_iff.1 hw'
    have : u * w' * u⁻¹ ∈ Y := by
      rw [← c.W_inf_cen]
      refine mem_inf.2 ⟨hx, mem_centralizer_iff.2 fun j hj => ?_⟩
      have hj' : u⁻¹ * j * u ∈ J₀ := by
        have := c.J₀_conj_u j hj
        rw [c.u_inv] at this ⊢
        exact this
      have := (hfix _ hj').2
      calc j * (u * w' * u⁻¹) = u * ((u⁻¹ * j * u) * w' * (u⁻¹ * j * u)⁻¹) * u⁻¹ * j := by group
        _ = u * w' * u⁻¹ * j := by rw [this]
        _ = (u * w' * u⁻¹) * j := rfl
    exact this
  rw [← hww]
  exact mul_mem (Subgroup.mem_sup_left hwY) (Subgroup.mem_sup_right hw'Y)

end Step1e

end E2Ctx

namespace E2Ctx

section Step1ef

variable {𝔊 : Type*} [Group 𝔊] [Finite 𝔊] {f : ℕ} {Γ : Type} [Field Γ] [Finite Γ]
  {t u : 𝔊} {K D P Y W F J J₀ C : Subgroup 𝔊} {φ : ↥K →* SL(2, Γ)}
  (c : E2Ctx f Γ t u K D P Y W F J J₀ C φ)

include c

theorem Y_le_F : Y ≤ F := c.Y_le_W.trans c.W_le_F

theorem isPGroup_zcA : IsPGroup 2 (zc (P ⊓ K) : Subgroup 𝔊) :=
  (c.P_pgroup.to_inf_left (K := K)).to_inf_left

theorem H_inf_Hu_eq_bot (hZ : zc K = ⊥) : zc (P ⊓ K) ⊓ (zc (P ⊓ K))ᵍ[u] = ⊥ := by
  rw [← c.zc_K_eq]
  exact hZ

theorem centralizer_J₀_H (hZ : zc K = ⊥) {h : 𝔊} (hh : h ∈ zc (P ⊓ K))
    (hc : ∀ j ∈ J₀, j * h = h * j) : h ∈ Y := by
  have hHD : zc (P ⊓ K) ≤ D := c.zc_A_le_D
  have hY : Y ≤ zc (P ⊓ K) := by
    rw [c.Y_eq]
    exact inf_le_left
  have hYu : Yᵍ[u] ≤ (zc (P ⊓ K))ᵍ[u] := conjg_mono hY u
  have h1 := c.centralizer_J₀_D (hHD hh) hc
  have hYYu : Y ≤ normalizer ((Yᵍ[u] : Subgroup 𝔊) : Set 𝔊) := fun y hy => by
    refine mem_normalizer_fintype fun x hx => ?_
    have hxD : x ∈ D := by
      have hx' : x ∈ Yᵍ[u] := hx
      have : x ∈ Wᵍ[u] := conjg_mono c.Y_le_W u hx'
      rw [c.D_eq_sup]
      exact Subgroup.mem_sup_right this
    have : y * x * y⁻¹ = x := by
      rw [c.D_comm y (c.Y_le_D hy) x hxD, mul_inv_cancel_right]
    rw [this]
    exact hx
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right Y Yᵍ[u] hYYu
  obtain ⟨y, hy, y', hy', hyy⟩ : ∃ y ∈ Y, ∃ y' ∈ Yᵍ[u], y * y' = h := by
    have : h ∈ (Y : Set 𝔊) * (Yᵍ[u] : Set 𝔊) := by
      rw [← hmul]
      exact h1
    exact Set.mem_mul.1 this
  have hy'1 : y' = 1 := by
    have h2 : y' ∈ zc (P ⊓ K) := by
      have : y' = y⁻¹ * h := by rw [← hyy]; group
      rw [this]
      exact mul_mem (inv_mem (hY hy)) hh
    have h3 : y' ∈ zc (P ⊓ K) ⊓ (zc (P ⊓ K))ᵍ[u] := mem_inf.2 ⟨h2, hYu hy'⟩
    rw [c.H_inf_Hu_eq_bot hZ, Subgroup.mem_bot] at h3
    exact h3
  rw [← hyy, hy'1, mul_one]
  exact hy

theorem H_le_F (hZ : zc K = ⊥) : zc (P ⊓ K) ≤ F := by
  intro h hh
  have hHD : zc (P ⊓ K) ≤ D := c.zc_A_le_D
  have hHJ : J₀ ≤ normalizer ((zc (P ⊓ K) : Subgroup 𝔊) : Set 𝔊) := fun j hj =>
    c.J_le_normalizer_zcA (c.J₀_le_J hj)
  obtain ⟨c₀, hc₀, n, hn, hcn⟩ := exists_fixed_mul_commutator hHJ
    (isSolvable_of_isPGroup_two c.isPGroup_zcA)
    (coprime_of_odd_of_card_two_pow c.odd_card_J₀ c.isPGroup_zcA) hh
  obtain ⟨hc₀H, hc₀c⟩ := mem_inf.1 hc₀
  have hc₀Y : c₀ ∈ Y := c.centralizer_J₀_H hZ hc₀H
    (fun j hj => mem_centralizer_iff.1 hc₀c j hj)
  have hnF : n ∈ F := by
    have : ⁅zc (P ⊓ K), J₀⁆ ≤ F := by
      rw [commutator_le]
      intro x hx j hj
      exact c.D_J₀_le_F x (hHD hx) j hj
    exact this hn
  rw [hcn]
  exact mul_mem (c.Y_le_F hc₀Y) hnF

end Step1ef

end E2Ctx

namespace E2Ctx

section Step1f

variable {𝔊 : Type*} [Group 𝔊] [Finite 𝔊] {f : ℕ} {Γ : Type} [Field Γ] [Finite Γ]
  {t u : 𝔊} {K D P Y W F J J₀ C : Subgroup 𝔊} {φ : ↥K →* SL(2, Γ)}
  (c : E2Ctx f Γ t u K D P Y W F J J₀ C φ)

include c

theorem Y_le_H : Y ≤ zc (P ⊓ K) := by
  rw [c.Y_eq]
  exact inf_le_left

theorem H_le_P : zc (P ⊓ K) ≤ P := (zc_le _).trans inf_le_left

theorem P_le_normalizer_zcA : P ≤ normalizer ((zc (P ⊓ K) : Subgroup 𝔊) : Set 𝔊) := fun p hp =>
  mem_normalizer_zc (c.P_le_normalizer_A hp)

theorem t_conj_mem_Y {x : 𝔊} (hx : x ∈ Y) : t * x * t⁻¹ ∈ Y := by
  have : x ∈ Yᵍ[t] := by rw [c.Y_conj]; exact hx
  exact mem_conjg_iff.1 this

theorem Y_inf_Yut : Y ⊓ (Yᵍ[u])ᵍ[t] = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxY, hxYut⟩ := mem_inf.1 hx
  have h1 : t * x * t⁻¹ ∈ Yᵍ[u] := mem_conjg_iff.1 hxYut
  have h2 : t * x * t⁻¹ ∈ Y := c.t_conj_mem_Y hxY
  have h3 : t * x * t⁻¹ ∈ W ⊓ Wᵍ[u] :=
    mem_inf.2 ⟨c.Y_le_W h2, conjg_mono c.Y_le_W u h1⟩
  rw [c.W_inf, Subgroup.mem_bot] at h3
  have : x = 1 := by
    have h4 : t * x * t⁻¹ = 1 := h3
    calc x = t⁻¹ * (t * x * t⁻¹) * t := by group
      _ = 1 := by rw [h4]; group
  rw [this]
  exact one_mem _

theorem Y_ne_H : Y ≠ zc (P ⊓ K) := by
  intro h
  apply c.zc_inf_conj_ne_bot
  rw [← h]
  exact c.Y_inf_Yut

theorem Y_ne_H_inf_W (hF : zc (P ⊓ K) ≤ F) : zc (P ⊓ K) ⊓ W ≠ Y := by
  intro hYeq
  apply c.Y_ne_H
  have hHW : zc (P ⊓ K) ≤ W := by
    intro h hh
    refine (c.mem_W h).2 ⟨c.H_le_P hh, fun p hp => ?_⟩
    have h1 : h * p * h⁻¹ * p⁻¹ ∈ W := ((c.mem_F h).1 (hF hh)).2 p hp
    have h2 : h * p * h⁻¹ * p⁻¹ ∈ zc (P ⊓ K) := by
      have hp' : p * h⁻¹ * p⁻¹ ∈ zc (P ⊓ K) :=
        (mem_normalizer_iff.1 (c.P_le_normalizer_zcA hp) h⁻¹).1 (inv_mem hh)
      have e : h * p * h⁻¹ * p⁻¹ = h * (p * h⁻¹ * p⁻¹) := by group
      rw [e]
      exact mul_mem hh hp'
    rw [← hYeq]
    exact mem_inf.2 ⟨h2, h1⟩
  have : zc (P ⊓ K) ⊓ W = zc (P ⊓ K) := inf_eq_left.2 hHW
  rw [← hYeq, this]

theorem card_H_inf_W (hZ : zc K = ⊥) : Nat.card ↥(zc (P ⊓ K) ⊓ W) = (2 ^ f) ^ 5 := by
  have hF := c.H_le_F hZ
  have hnorm : J ≤ normalizer ((zc (P ⊓ K) ⊓ W : Subgroup 𝔊) : Set 𝔊) := fun j hj =>
    Common.mem_normalizer_inf (c.J_le_normalizer_zcA hj) (c.J_nor_W hj)
  rcases c.J_inv_W (zc (P ⊓ K) ⊓ W) (le_inf c.Y_le_H c.Y_le_W) inf_le_right hnorm with h | h | h
  · exact absurd h (c.Y_ne_H_inf_W hF)
  · rw [h, c.card_Y]
    ring
  · exfalso
    have hWH : W ≤ zc (P ⊓ K) := by
      rw [← h]
      exact inf_le_left
    have hWHt : W ≤ (zc (P ⊓ K))ᵍ[t] := by
      have := conjg_mono hWH t
      rwa [c.W_conj] at this
    have hWY : W ≤ Y := by
      rw [c.Y_eq]
      exact le_inf hWH hWHt
    have := Subgroup.card_le_of_le hWY
    rw [c.card_W, c.card_Y] at this
    have h2 : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := c.two_le; omega)
    have h3 : (2 ^ f) ^ 2 < (2 ^ f) ^ 8 := Nat.pow_lt_pow_right h2 (by norm_num)
    omega

end Step1f

end E2Ctx

namespace E2Ctx

section Step1g

variable {𝔊 : Type*} [Group 𝔊] [Finite 𝔊] {f : ℕ} {Γ : Type} [Field Γ] [Finite Γ]
  {t u : 𝔊} {K D P Y W F J J₀ C : Subgroup 𝔊} {φ : ↥K →* SL(2, Γ)}
  (c : E2Ctx f Γ t u K D P Y W F J J₀ C φ)

include c

theorem W_le_P : W ≤ P := fun w hw => ((c.mem_W w).1 hw).1

theorem P_le_normalizer_W : P ≤ normalizer (W : Set 𝔊) := by
  intro p hp
  refine mem_normalizer_fintype fun w hw => ?_
  refine (c.mem_W _).2 ⟨mul_mem (mul_mem hp (c.W_le_P hw)) (inv_mem hp), fun q hq => ?_⟩
  have h1 : w * (p⁻¹ * q * p) * w⁻¹ * (p⁻¹ * q * p)⁻¹ ∈ Y :=
    ((c.mem_W w).1 hw).2 _ (mul_mem (mul_mem (inv_mem hp) hq) hp)
  have h2 : p * (w * (p⁻¹ * q * p) * w⁻¹ * (p⁻¹ * q * p)⁻¹) * p⁻¹ ∈ Y := by
    have hpY : ∀ y ∈ Y, p * y * p⁻¹ ∈ Y := fun y hy => by
      have := ((c.mem_Y y).1 hy).2 p hp
      rw [← this]
      simpa using hy
    exact hpY _ h1
  have e : p * (w * (p⁻¹ * q * p) * w⁻¹ * (p⁻¹ * q * p)⁻¹) * p⁻¹ =
      (p * w * p⁻¹) * q * (p * w * p⁻¹)⁻¹ * q⁻¹ := by group
  rwa [e] at h2

theorem Wu_conj_t : (Wᵍ[u])ᵍ[t] = Wᵍ[u] := by
  rw [conjg_conjg, ← c.t_comm_u, ← conjg_conjg, c.W_conj]

theorem conjg_conjg_le_Wu {X : Subgroup 𝔊} (hX : X ≤ W) : (Xᵍ[u])ᵍ[t] ≤ Wᵍ[u] := by
  rw [← c.Wu_conj_t]
  exact conjg_mono (conjg_mono hX u) t

theorem H_not_le_W : ¬ zc (P ⊓ K) ≤ W := by
  intro hHW
  apply c.zc_inf_conj_ne_bot
  rw [eq_bot_iff, ← c.W_inf]
  exact le_inf_iff.2 ⟨inf_le_left.trans hHW, (inf_le_right.trans (c.conjg_conjg_le_Wu hHW))⟩

theorem le_normalizer_of_le_D {X Y : Subgroup 𝔊} (hX : X ≤ D) (hY : Y ≤ D) :
    Y ≤ normalizer (X : Set 𝔊) := fun y hy => by
  refine mem_normalizer_fintype fun x hx => ?_
  have := c.D_comm y (hY hy) x (hX hx)
  have e : y * x * y⁻¹ = x := by rw [this]; group
  rw [e]
  exact hx

theorem Hu_le_D : (zc (P ⊓ K))ᵍ[u] ≤ D := by
  have := conjg_mono c.zc_A_le_D u
  rwa [c.Du_conj] at this

theorem Wu_le_D : Wᵍ[u] ≤ D := by
  rw [c.D_eq_sup]
  exact le_sup_right

theorem card_H (hZ : zc K = ⊥) : Nat.card ↥(zc (P ⊓ K)) = (2 ^ f) ^ 8 := by
  have hF := c.H_le_F hZ
  have hHW := c.card_H_inf_W hZ
  have hnorm : J ≤ normalizer (((zc (P ⊓ K)) ⊔ W : Subgroup 𝔊) : Set 𝔊) := fun j hj =>
    Common.mem_normalizer_sup (c.J_le_normalizer_zcA hj) (c.J_nor_W hj)
  have hcard := Common.card_sup_mul_card_inf_eq (A := zc (P ⊓ K)) (B := W)
    (fun w hw => c.P_le_normalizer_zcA (c.W_le_P hw))
  rw [hHW] at hcard
  have hpos : 0 < (2 ^ f) ^ 5 := by positivity
  have h2 : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := c.two_le; omega)
  rcases c.J_inv_F (zc (P ⊓ K) ⊔ W) le_sup_right (sup_le hF c.W_le_F) hnorm with h | h | h
  · exact absurd (le_sup_left.trans h.le) c.H_not_le_W
  · rw [h, c.card_W] at hcard
    apply Nat.eq_of_mul_eq_mul_right (show 0 < (2 ^ f) ^ 8 by positivity)
    rw [← hcard]
    ring
  · exfalso
    rw [h, c.card_F, c.card_W] at hcard
    have hH11 : Nat.card ↥(zc (P ⊓ K)) = (2 ^ f) ^ 11 := by
      apply Nat.eq_of_mul_eq_mul_right (show 0 < (2 ^ f) ^ 8 by positivity)
      rw [← hcard]
      ring
    have hdisj := c.H_inf_Hu_eq_bot hZ
    have hc2 := Common.card_sup_mul_card_inf_eq (A := zc (P ⊓ K)) (B := (zc (P ⊓ K))ᵍ[u])
      (c.le_normalizer_of_le_D c.zc_A_le_D c.Hu_le_D)
    rw [hdisj, card_conjg, hH11, Subgroup.card_bot, mul_one] at hc2
    have hle : Nat.card ↥(zc (P ⊓ K) ⊔ (zc (P ⊓ K))ᵍ[u]) ≤ Nat.card D :=
      Subgroup.card_le_of_le (sup_le c.zc_A_le_D c.Hu_le_D)
    rw [c.card_D, hc2] at hle
    have : (2 ^ f) ^ 16 < (2 ^ f) ^ 11 * (2 ^ f) ^ 11 := by
      rw [← pow_add]
      exact Nat.pow_lt_pow_right h2 (by norm_num)
    omega

end Step1g

end E2Ctx

namespace E2Ctx

section Step1h

variable {𝔊 : Type*} [Group 𝔊] [Finite 𝔊] {f : ℕ} {Γ : Type} [Field Γ] [Finite Γ]
  {t u : 𝔊} {K D P Y W F J J₀ C : Subgroup 𝔊} {φ : ↥K →* SL(2, Γ)}
  (c : E2Ctx f Γ t u K D P Y W F J J₀ C φ)

include c

theorem Aut_le_Kt : ((P ⊓ K)ᵍ[u])ᵍ[t] ≤ Kᵍ[t] :=
  conjg_mono c.Au_le_K t

theorem D_le_Aut : D ≤ ((P ⊓ K)ᵍ[u])ᵍ[t] := by
  have := conjg_mono c.D_le_Au t
  rwa [c.D_conj] at this

theorem K_le_normalizer_Aut : K ≤ normalizer ((((P ⊓ K)ᵍ[u])ᵍ[t] : Subgroup 𝔊) : Set 𝔊) := by
  apply le_normalizer_of_commutator_le
  refine le_trans (commutator_mono c.Aut_le_Kt le_rfl) ?_
  rw [commutator_comm]
  exact c.comm_le.trans c.D_le_Aut

theorem K_le_normalizer_Hut :
    K ≤ normalizer ((((zc (P ⊓ K))ᵍ[u])ᵍ[t] : Subgroup 𝔊) : Set 𝔊) := by
  have := fun k (hk : k ∈ K) => mem_normalizer_zc (c.K_le_normalizer_Aut hk)
  intro k hk
  have h := this k hk
  rwa [zc_conjg, zc_conjg] at h

theorem Hut_le_D : ((zc (P ⊓ K))ᵍ[u])ᵍ[t] ≤ D := by
  have := conjg_mono c.Hu_le_D t
  rwa [c.D_conj] at this

theorem card_Hut (hZ : zc K = ⊥) : Nat.card ↥(((zc (P ⊓ K))ᵍ[u])ᵍ[t]) = (2 ^ f) ^ 8 := by
  rw [card_conjg, card_conjg, c.card_H hZ]

theorem Q_ne_bot (hZ : zc K = ⊥) : ((zc (P ⊓ K))ᵍ[u])ᵍ[t] ⊓ W ≠ ⊥ := by
  intro hQ
  set H := zc (P ⊓ K) with hH
  set Hut := (Hᵍ[u])ᵍ[t] with hHut
  have h2 : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := c.two_le; omega)
  have hHutD : Hut ≤ D := c.Hut_le_D
  have hHD : H ≤ D := c.zc_A_le_D
  have hcard1 := Common.card_sup_mul_card_inf_eq (A := Hut) (B := W)
    (c.le_normalizer_of_le_D hHutD c.W_le_D)
  rw [hQ, Subgroup.card_bot, mul_one, c.card_Hut hZ, c.card_W] at hcard1
  have hDeq : Hut ⊔ W = D := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hHutD c.W_le_D) ?_
    rw [hcard1, c.card_D]
    exact (by ring : (2 ^ f) ^ 16 = (2 ^ f) ^ 8 * (2 ^ f) ^ 8).le
  have hmul : ((Hut ⊔ W : Subgroup 𝔊) : Set 𝔊) = (Hut : Set 𝔊) * (W : Set 𝔊) :=
    Subgroup.coe_mul_of_left_le_normalizer_right Hut W (c.le_normalizer_of_le_D c.W_le_D hHutD)
  have hcen : ∀ x ∈ F, ∃ h ∈ H ⊓ Hut, ∃ w ∈ W, x = h * w := by
    intro x hx
    have hxD : x ∈ Hut ⊔ W := hDeq ▸ c.F_le_D hx
    have : x ∈ (Hut : Set 𝔊) * (W : Set 𝔊) := by
      rw [← hmul]
      exact hxD
    obtain ⟨h, hh, w, hw, rfl⟩ := Set.mem_mul.1 this
    refine ⟨h, mem_inf.2 ⟨?_, hh⟩, w, hw, rfl⟩
    have hhA : h ∈ P ⊓ K := c.D_le_A (hHutD hh)
    refine (mem_zc_iff).2 ⟨hhA, fun a ha => ?_⟩
    have haP : a ∈ P := (mem_inf.1 ha).1
    have haK : a ∈ K := (mem_inf.1 ha).2
    have hxa : h * w * a * (h * w)⁻¹ * a⁻¹ ∈ W := ((c.mem_F _).1 hx).2 a haP
    have hwa : w * a * w⁻¹ * a⁻¹ ∈ Y := ((c.mem_W w).1 hw).2 a haP
    have haHut : a * h⁻¹ * a⁻¹ ∈ Hut := by
      have := (mem_normalizer_iff.1 (c.K_le_normalizer_Hut haK) h⁻¹).1 (inv_mem hh)
      exact this
    have hw' : w * a * w⁻¹ * a⁻¹ ∈ W := c.Y_le_W hwa
    have hwa' : a * w * a⁻¹ ∈ W := (mem_normalizer_iff.1 (c.P_le_normalizer_W haP) w).1 hw
    have e : h * (a * h⁻¹ * a⁻¹) = (h * w * a * (h * w)⁻¹ * a⁻¹) * (w * a * w⁻¹ * a⁻¹)⁻¹ := by
      have hc1 : (a * h⁻¹ * a⁻¹) * (w * a * w⁻¹ * a⁻¹) = (w * a * w⁻¹ * a⁻¹) * (a * h⁻¹ * a⁻¹) :=
        c.D_comm _ (hHutD haHut) _ (c.W_le_D hw')
      calc h * (a * h⁻¹ * a⁻¹)
          = h * ((a * h⁻¹ * a⁻¹) * (w * a * w⁻¹ * a⁻¹)) * (w * a * w⁻¹ * a⁻¹)⁻¹ := by group
        _ = h * ((w * a * w⁻¹ * a⁻¹) * (a * h⁻¹ * a⁻¹)) * (w * a * w⁻¹ * a⁻¹)⁻¹ := by rw [hc1]
        _ = _ := by group
    have h1 : h * (a * h⁻¹ * a⁻¹) ∈ W := by
      rw [e]
      exact mul_mem hxa (inv_mem hw')
    have h3 : h * (a * h⁻¹ * a⁻¹) ∈ Hut := mul_mem hh haHut
    have h4 : h * (a * h⁻¹ * a⁻¹) ∈ Hut ⊓ W := mem_inf.2 ⟨h3, h1⟩
    rw [hQ, Subgroup.mem_bot] at h4
    have h5 : a * h⁻¹ * a⁻¹ = h⁻¹ := by
      have := congrArg (fun z => h⁻¹ * z) h4
      simpa using this
    have h6 : a * h * a⁻¹ = h := by
      have := congrArg (fun z => z⁻¹) h5
      simpa [mul_assoc] using this
    calc a * h = (a * h * a⁻¹) * a := by group
      _ = h * a := by rw [h6]
  set T := H ⊓ Hut with hT
  have hTD : T ≤ D := inf_le_left.trans hHD
  have hTW : T ⊓ W = ⊥ := by
    rw [eq_bot_iff, ← hQ]
    exact inf_le_inf_right W inf_le_right
  have hc3 := Common.card_sup_mul_card_inf_eq (A := T) (B := W)
    (c.le_normalizer_of_le_D hTD c.W_le_D)
  rw [hTW, Subgroup.card_bot, mul_one, c.card_W] at hc3
  have hFle : F ≤ T ⊔ W := by
    intro x hx
    obtain ⟨h, hh, w, hw, rfl⟩ := hcen x hx
    exact mul_mem (mem_sup_left hh) (mem_sup_right hw)
  have h6 : (2 ^ f) ^ 14 ≤ Nat.card ↥T * (2 ^ f) ^ 8 := by
    have := Subgroup.card_le_of_le hFle
    rwa [c.card_F, hc3] at this
  set X := H ⊓ W with hX
  have hXD : X ≤ D := inf_le_left.trans hHD
  have hXT : X ⊓ T = ⊥ := by
    rw [eq_bot_iff, ← hQ]
    exact le_inf (inf_le_right.trans inf_le_right) (inf_le_left.trans inf_le_right)
  have hc4 := Common.card_sup_mul_card_inf_eq (A := X) (B := T) (c.le_normalizer_of_le_D hXD hTD)
  rw [hXT, Subgroup.card_bot, mul_one, c.card_H_inf_W hZ] at hc4
  have hXTH : X ⊔ T ≤ H := sup_le inf_le_left inf_le_left
  have h7 : Nat.card ↥(X ⊔ T) ≤ (2 ^ f) ^ 8 := by
    have := Subgroup.card_le_of_le hXTH
    rwa [c.card_H hZ] at this
  rw [hc4] at h7
  have h8 : Nat.card ↥T ≤ (2 ^ f) ^ 3 := by
    have : (2 ^ f) ^ 5 * Nat.card ↥T ≤ (2 ^ f) ^ 5 * (2 ^ f) ^ 3 := by
      calc (2 ^ f) ^ 5 * Nat.card ↥T ≤ (2 ^ f) ^ 8 := h7
        _ = (2 ^ f) ^ 5 * (2 ^ f) ^ 3 := by ring
    exact Nat.le_of_mul_le_mul_left this (by positivity)
  have h9 : (2 ^ f) ^ 6 ≤ Nat.card ↥T := by
    have : (2 ^ f) ^ 8 * (2 ^ f) ^ 6 ≤ (2 ^ f) ^ 8 * Nat.card ↥T := by
      calc (2 ^ f) ^ 8 * (2 ^ f) ^ 6 = (2 ^ f) ^ 14 := by ring
        _ ≤ Nat.card ↥T * (2 ^ f) ^ 8 := h6
        _ = (2 ^ f) ^ 8 * Nat.card ↥T := by ring
    exact Nat.le_of_mul_le_mul_left this (by positivity)
  have : (2 ^ f) ^ 3 < (2 ^ f) ^ 6 := Nat.pow_lt_pow_right h2 (by norm_num)
  omega

end Step1h

end E2Ctx

section PGroupNormal

variable {G : Type*} [Group G] [Finite G]

theorem exists_ne_one_commuting_of_normal_pgroup {A Q : Subgroup G} (hA : IsPGroup 2 A)
    (hQA : Q ≤ A) (hN : A ≤ normalizer (Q : Set G)) (hne : Q ≠ ⊥) :
    ∃ z ∈ Q, z ≠ 1 ∧ ∀ a ∈ A, z * a = a * z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥A := hA.isNilpotent
  have hQn : (Q.subgroupOf A).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hQA]
    intro h k hh hk
    exact (mem_normalizer_iff.1 (hN hk) h).1 hh
  haveI := hQn
  have hne' : Q.subgroupOf A ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hQA hx⟩ : ↥A) ∈ Q.subgroupOf A := hx
    rw [h, Subgroup.mem_bot] at this
    have h1 : x = 1 := congrArg Subtype.val this
    rw [h1]
    exact one_mem _
  obtain ⟨z, hz⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne')
  obtain ⟨hzQ, hzC⟩ := mem_inf.1 z.2
  refine ⟨((z : ↥A) : G), Subgroup.mem_subgroupOf.1 hzQ, ?_, fun a ha => ?_⟩
  · intro h1
    apply hz
    apply Subtype.ext
    apply Subtype.ext
    exact h1
  · have := Subgroup.mem_center_iff.1 hzC ⟨a, ha⟩
    exact (congrArg Subtype.val this).symm

end PGroupNormal

section ConjConj

variable {G : Type*} [Group G]

theorem mem_conjg_conjg_iff {X : Subgroup G} {g h x : G} :
    x ∈ (Xᵍ[g])ᵍ[h] ↔ g * (h * x * h⁻¹) * g⁻¹ ∈ X := by
  rw [mem_conjg_iff, mem_conjg_iff]

end ConjConj

namespace E2Ctx

section Step1i

variable {𝔊 : Type*} [Group 𝔊] [Finite 𝔊] {f : ℕ} {Γ : Type} [Field Γ] [Finite Γ]
  {t u : 𝔊} {K D P Y W F J J₀ C : Subgroup 𝔊} {φ : ↥K →* SL(2, Γ)}
  (c : E2Ctx f Γ t u K D P Y W F J J₀ C φ)

include c

theorem P_le_normalizer_Y : P ≤ normalizer (Y : Set 𝔊) := fun p hp => by
  refine mem_normalizer_fintype fun y hy => ?_
  have := ((c.mem_Y y).1 hy).2 p hp
  have e : p * y * p⁻¹ = y := by rw [← this]; group
  rw [e]
  exact hy

theorem J_le_normalizer_Hut :
    J ≤ normalizer ((((zc (P ⊓ K))ᵍ[u])ᵍ[t] : Subgroup 𝔊) : Set 𝔊) := fun j hj => by
  rw [mem_normalizer_conjg_iff, mem_normalizer_conjg_iff]
  have htj : t * j * t⁻¹ = j := by
    have := mem_centralizer_singleton_iff.1 (c.J_cen_t hj)
    rw [← this]
    group
  rw [htj]
  exact c.J_le_normalizer_zcA (c.J_conj_u j hj)

theorem Y_inf_Hut (hZ : zc K = ⊥) : Y ⊓ ((zc (P ⊓ K))ᵍ[u])ᵍ[t] = ⊥ := by
  rw [eq_bot_iff]
  have hYHt : Y ≤ (zc (P ⊓ K))ᵍ[t] := by
    rw [c.Y_eq]
    exact inf_le_right
  calc Y ⊓ ((zc (P ⊓ K))ᵍ[u])ᵍ[t] ≤ (zc (P ⊓ K))ᵍ[t] ⊓ ((zc (P ⊓ K))ᵍ[u])ᵍ[t] :=
        inf_le_inf_right _ hYHt
    _ = (zc (P ⊓ K) ⊓ (zc (P ⊓ K))ᵍ[u])ᵍ[t] := (conjg_inf _ _ t).symm
    _ = ⊥ := by rw [c.H_inf_Hu_eq_bot hZ, Subgroup.map_bot]
    _ ≤ ⊥ := le_rfl

theorem J_inv_card {R : Subgroup 𝔊} (hRW : R ≤ W) (hRY : R ⊓ Y = ⊥) (hR0 : R ≠ ⊥)
    (hRJ : J ≤ normalizer (R : Set 𝔊)) :
    Nat.card R = (2 ^ f) ^ 3 ∨ Y ⊔ R = W := by
  have hcard := Common.card_sup_mul_card_inf_eq (A := Y) (B := R)
    (fun r hr => c.P_le_normalizer_Y (c.W_le_P (hRW hr)))
  rw [inf_comm, hRY, Subgroup.card_bot, mul_one, c.card_Y] at hcard
  have hnorm : J ≤ normalizer ((Y ⊔ R : Subgroup 𝔊) : Set 𝔊) := fun j hj =>
    Common.mem_normalizer_sup (c.J_nor_Y hj) (hRJ hj)
  have hpos : 0 < (2 ^ f) ^ 2 := by positivity
  rcases c.J_inv_W (Y ⊔ R) le_sup_left (sup_le c.Y_le_W hRW) hnorm with h | h | h
  · exfalso
    apply hR0
    rw [eq_bot_iff, ← hRY]
    exact le_inf le_rfl (le_sup_right.trans h.le)
  · left
    rw [h, c.card_Y] at hcard
    exact (Nat.eq_of_mul_eq_mul_left hpos hcard).symm
  · right
    exact h

end Step1i

end E2Ctx

namespace E2Ctx

section Step1i2

variable {𝔊 : Type*} [Group 𝔊] [Finite 𝔊] {f : ℕ} {Γ : Type} [Field Γ] [Finite Γ]
  {t u : 𝔊} {K D P Y W F J J₀ C : Subgroup 𝔊} {φ : ↥K →* SL(2, Γ)}
  (c : E2Ctx f Γ t u K D P Y W F J J₀ C φ)

include c

theorem J_le_normalizer_Q :
    J ≤ normalizer ((((zc (P ⊓ K))ᵍ[u])ᵍ[t] ⊓ W : Subgroup 𝔊) : Set 𝔊) := fun j hj =>
  Common.mem_normalizer_inf (c.J_le_normalizer_Hut hj) (c.J_nor_W hj)

theorem Q_inf_Y (hZ : zc K = ⊥) : (((zc (P ⊓ K))ᵍ[u])ᵍ[t] ⊓ W) ⊓ Y = ⊥ := by
  rw [eq_bot_iff, ← c.Y_inf_Hut hZ]
  exact le_inf inf_le_right (inf_le_left.trans inf_le_left)

theorem Q_sup_Y_ne_W (hZ : zc K = ⊥) :
    ((zc (P ⊓ K))ᵍ[u])ᵍ[t] ⊓ W ⊔ Y ≠ W := by
  intro hW
  have htt := c.t_mul_t
  have huu := c.u_mul_u
  have htu : t * u = u * t := c.t_comm_u
  set H := zc (P ⊓ K) with hH
  set Hut := (Hᵍ[u])ᵍ[t] with hHut
  set Q := Hut ⊓ W with hQ
  have hQJ : J ≤ normalizer (Q : Set 𝔊) := c.J_le_normalizer_Q
  have hQW : Q ≤ W := inf_le_right
  have hQHut : Q ≤ Hut := inf_le_left
  have hmul : ((Q ⊔ Y : Subgroup 𝔊) : Set 𝔊) = (Q : Set 𝔊) * (Y : Set 𝔊) :=
    Subgroup.coe_mul_of_left_le_normalizer_right Q Y
      (fun q hq => c.P_le_normalizer_Y (c.W_le_P (hQW hq)))
  have hcomm : ∀ w ∈ W, ∀ j ∈ J₀, w * j * w⁻¹ * j⁻¹ ∈ Q := by
    intro w hw j hj
    have hwQY : w ∈ ((Q ⊔ Y : Subgroup 𝔊) : Set 𝔊) := by
      rw [hW]
      exact hw
    rw [hmul] at hwQY
    obtain ⟨q, hq, y, hy, rfl⟩ := Set.mem_mul.1 hwQY
    have hyj : j * y = y * j := mem_centralizer_iff.1 (c.J₀_cen_Y hy) j hj
    have hjq : j * q⁻¹ * j⁻¹ ∈ Q :=
      (mem_normalizer_iff.1 (hQJ (c.J₀_le_J hj)) q⁻¹).1 (inv_mem hq)
    have e : q * y * j * (q * y)⁻¹ * j⁻¹ = q * (j * q⁻¹ * j⁻¹) := by
      have h1 : y * j * y⁻¹ = j := by rw [← hyj]; group
      calc q * y * j * (q * y)⁻¹ * j⁻¹ = q * (y * j * y⁻¹) * q⁻¹ * j⁻¹ := by group
        _ = q * j * q⁻¹ * j⁻¹ := by rw [h1]
        _ = q * (j * q⁻¹ * j⁻¹) := by group
    rw [e]
    exact mul_mem hq hjq
  have hcomm_t : ∀ w ∈ W, ∀ j ∈ J₀, t * (w * j * w⁻¹ * j⁻¹) * t⁻¹ ∈ Q := by
    intro w hw j hj
    have htj : t * j * t⁻¹ = j := by
      have := mem_centralizer_singleton_iff.1 (c.J_cen_t (c.J₀_le_J hj))
      rw [← this]
      group
    have hw' : t * w * t⁻¹ ∈ W := by
      rw [← mem_conjg_iff, c.W_conj]
      exact hw
    have h1 := hcomm (t * w * t⁻¹) hw' j hj
    have e : t * (w * j * w⁻¹ * j⁻¹) * t⁻¹ =
        (t * w * t⁻¹) * j * (t * w * t⁻¹)⁻¹ * j⁻¹ := by
      calc t * (w * j * w⁻¹ * j⁻¹) * t⁻¹
          = (t * w * t⁻¹) * (t * j * t⁻¹) * (t * w * t⁻¹)⁻¹ * (t * j * t⁻¹)⁻¹ := by group
        _ = _ := by rw [htj]
    rw [e]
    exact h1
  have hcY : ∀ w ∈ W, ∀ j ∈ J₀, u * (w * j * w⁻¹ * j⁻¹) * u⁻¹ ∈ Y := by
    intro w hw j hj
    have h1 : w * j * w⁻¹ * j⁻¹ ∈ Q := hcomm w hw j hj
    have h2 : t * (w * j * w⁻¹ * j⁻¹) * t⁻¹ ∈ Q := hcomm_t w hw j hj
    have h1' := mem_conjg_conjg_iff.1 (hQHut h1)
    have h2' := mem_conjg_conjg_iff.1 (hQHut h2)
    have e2 : ∀ x : 𝔊, t * (t * x * t⁻¹) * t⁻¹ = x := fun x => by
      calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
        _ = x := by rw [htt]; group
    rw [e2] at h2'
    rw [c.Y_eq]
    refine mem_inf.2 ⟨h2', ?_⟩
    rw [mem_conjg_iff]
    have e3 : ∀ x : 𝔊, t * (u * x * u⁻¹) * t⁻¹ = u * (t * x * t⁻¹) * u⁻¹ := fun x => by
      calc t * (u * x * u⁻¹) * t⁻¹ = (t * u) * x * (t * u)⁻¹ := by group
        _ = (u * t) * x * (u * t)⁻¹ := by rw [htu]
        _ = u * (t * x * t⁻¹) * u⁻¹ := by group
    rw [e3]
    exact h1'
  have hclaim : ∀ w₁ ∈ Wᵍ[u], ∀ j₁ ∈ J₀, w₁ * j₁ * w₁⁻¹ * j₁⁻¹ ∈ Y := by
    intro w₁ hw₁ j₁ hj₁
    have hw : u * w₁ * u⁻¹ ∈ W := mem_conjg_iff.1 hw₁
    have hj : u * j₁ * u⁻¹ ∈ J₀ := c.J₀_conj_u j₁ hj₁
    have h1 := hcY _ hw _ hj
    have e : u * ((u * w₁ * u⁻¹) * (u * j₁ * u⁻¹) * (u * w₁ * u⁻¹)⁻¹ * (u * j₁ * u⁻¹)⁻¹) * u⁻¹ =
        (u * u) * (w₁ * j₁ * w₁⁻¹ * j₁⁻¹) * (u * u)⁻¹ := by group
    rw [e, huu] at h1
    simpa using h1
  have hWuP : Wᵍ[u] ≤ P := c.Wu_le_D.trans c.D_le_P
  have hWu_pg : IsPGroup 2 (Wᵍ[u] : Subgroup 𝔊) := c.P_pgroup.to_le hWuP
  have hcop : (Nat.card J₀).Coprime (Nat.card (Wᵍ[u] : Subgroup 𝔊)) :=
    coprime_of_odd_of_card_two_pow c.odd_card_J₀ hWu_pg
  have hJ₀Wu : J₀ ≤ normalizer ((Wᵍ[u] : Subgroup 𝔊) : Set 𝔊) := fun j hj =>
    c.J₀_normalizes_Wu hj
  have habel : ∀ x ∈ Wᵍ[u], ∀ y ∈ Wᵍ[u], x * y = y * x := fun x hx y hy =>
    c.D_comm x (c.Wu_le_D hx) y (c.Wu_le_D hy)
  have hfixed : ∀ w₁ ∈ Wᵍ[u], ∀ j₁ ∈ J₀, j₁ * w₁ = w₁ * j₁ := by
    intro w₁ hw₁ j₁ hj₁
    have hx : j₁ * w₁ * j₁⁻¹ * w₁⁻¹ ∈ ⁅J₀, Wᵍ[u]⁆ := by
      have := commutator_mem_commutator hj₁ hw₁
      rwa [commutatorElement_def] at this
    have hxY : j₁ * w₁ * j₁⁻¹ * w₁⁻¹ ∈ Y := by
      have := inv_mem (hclaim w₁ hw₁ j₁ hj₁)
      have e : (w₁ * j₁ * w₁⁻¹ * j₁⁻¹)⁻¹ = j₁ * w₁ * j₁⁻¹ * w₁⁻¹ := by group
      rwa [e] at this
    have h1 := commutator_fixed_eq_one habel hJ₀Wu hcop hx (fun s hs => by
      have := mem_centralizer_iff.1 (c.J₀_cen_Y hxY) s hs
      rw [this]
      group)
    calc j₁ * w₁ = (j₁ * w₁ * j₁⁻¹ * w₁⁻¹) * (w₁ * j₁) := by group
      _ = w₁ * j₁ := by rw [h1, one_mul]
  have hWcen : W ≤ centralizer (J₀ : Set 𝔊) := by
    intro w hw
    refine mem_centralizer_iff.2 fun j hj => ?_
    have hw₁ : u * w * u⁻¹ ∈ Wᵍ[u] := by
      rw [mem_conjg_iff]
      have e : u * (u * w * u⁻¹) * u⁻¹ = (u * u) * w * (u * u)⁻¹ := by group
      rw [e, huu]
      simpa using hw
    have hj₁ : u * j * u⁻¹ ∈ J₀ := c.J₀_conj_u j hj
    have h1 := hfixed _ hw₁ _ hj₁
    have e1 : u * j * u⁻¹ * (u * w * u⁻¹) = u * (j * w) * u⁻¹ := by group
    have e2 : u * w * u⁻¹ * (u * j * u⁻¹) = u * (w * j) * u⁻¹ := by group
    rw [e1, e2] at h1
    exact mul_left_cancel (mul_right_cancel h1)
  have hWY : W ≤ Y := by
    intro w hw
    rw [← c.W_inf_cen]
    exact mem_inf.2 ⟨hw, hWcen hw⟩
  have h1 := Subgroup.card_le_of_le hWY
  rw [c.card_W, c.card_Y] at h1
  have h2 : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := c.two_le; omega)
  have h3 : (2 ^ f) ^ 2 < (2 ^ f) ^ 8 := Nat.pow_lt_pow_right h2 (by norm_num)
  omega

theorem card_Q (hZ : zc K = ⊥) :
    Nat.card ↥(((zc (P ⊓ K))ᵍ[u])ᵍ[t] ⊓ W) = (2 ^ f) ^ 3 := by
  rcases c.J_inv_card inf_le_right (c.Q_inf_Y hZ) (c.Q_ne_bot hZ) c.J_le_normalizer_Q with h | h
  · exact h
  · exact absurd (by rw [sup_comm]; exact h) (c.Q_sup_Y_ne_W hZ)

end Step1i2

end E2Ctx

namespace E2Ctx

section Step1i3

variable {𝔊 : Type*} [Group 𝔊] [Finite 𝔊] {f : ℕ} {Γ : Type} [Field Γ] [Finite Γ]
  {t u : 𝔊} {K D P Y W F J J₀ C : Subgroup 𝔊} {φ : ↥K →* SL(2, Γ)}
  (c : E2Ctx f Γ t u K D P Y W F J J₀ C φ)

include c

theorem Q_le_H (hZ : zc K = ⊥) :
    ((zc (P ⊓ K))ᵍ[u])ᵍ[t] ⊓ W ≤ zc (P ⊓ K) := by
  set H := zc (P ⊓ K) with hH
  set Hut := (Hᵍ[u])ᵍ[t] with hHut
  set Q := Hut ⊓ W with hQ
  have hQD : Q ≤ D := inf_le_left.trans c.Hut_le_D
  have hQA : Q ≤ P ⊓ K := hQD.trans c.D_le_A
  have hQW : Q ≤ W := inf_le_right
  have hAQ : P ⊓ K ≤ normalizer (Q : Set 𝔊) := fun a ha =>
    Common.mem_normalizer_inf (c.K_le_normalizer_Hut (mem_inf.1 ha).2)
      (c.P_le_normalizer_W (mem_inf.1 ha).1)
  have hApg : IsPGroup 2 (P ⊓ K : Subgroup 𝔊) := c.P_pgroup.to_inf_left
  obtain ⟨z, hzQ, hz1, hzc⟩ :=
    exists_ne_one_commuting_of_normal_pgroup hApg hQA hAQ (c.Q_ne_bot hZ)
  set R := Q ⊓ H with hR
  have hRne : R ≠ ⊥ := by
    intro h
    have : z ∈ R := mem_inf.2 ⟨hzQ, (mem_zc_iff).2 ⟨hQA hzQ, fun y hy => (hzc y hy).symm⟩⟩
    rw [h, Subgroup.mem_bot] at this
    exact hz1 this
  have hRW : R ≤ W := inf_le_left.trans hQW
  have hRY : R ⊓ Y = ⊥ := by
    rw [eq_bot_iff, ← c.Q_inf_Y hZ]
    exact inf_le_inf_right Y inf_le_left
  have hRJ : J ≤ normalizer (R : Set 𝔊) := fun j hj =>
    Common.mem_normalizer_inf (c.J_le_normalizer_Q hj) (c.J_le_normalizer_zcA hj)
  have hcardQ := c.card_Q hZ
  rcases c.J_inv_card hRW hRY hRne hRJ with h | h
  · have hRQ : R ≤ Q := inf_le_left
    have hRQ' : R = Q := Subgroup.eq_of_le_of_card_ge hRQ (by rw [h, hcardQ])
    rw [← hRQ']
    exact inf_le_right
  · exfalso
    apply c.Q_sup_Y_ne_W hZ
    apply le_antisymm (sup_le hQW c.Y_le_W)
    calc W = Y ⊔ R := h.symm
      _ ≤ Q ⊔ Y := sup_le le_sup_right (inf_le_left.trans le_sup_left)

end Step1i3

end E2Ctx

namespace E2Ctx

section Step1j

variable {𝔊 : Type*} [Group 𝔊] [Finite 𝔊] {f : ℕ} {Γ : Type} [Field Γ] [Finite Γ]
  {t u : 𝔊} {K D P Y W F J J₀ C : Subgroup 𝔊} {φ : ↥K →* SL(2, Γ)}
  (c : E2Ctx f Γ t u K D P Y W F J J₀ C φ)

include c

theorem K_le_normalizer_At : K ≤ normalizer ((((P ⊓ K)ᵍ[t] : Subgroup 𝔊)) : Set 𝔊) := by
  apply le_normalizer_of_commutator_le
  have h1 : (P ⊓ K)ᵍ[t] ≤ Kᵍ[t] := conjg_mono inf_le_right t
  refine le_trans (commutator_mono h1 le_rfl) ?_
  rw [commutator_comm]
  exact c.comm_le.trans c.D_le_At

theorem card_Au : Nat.card ↥((P ⊓ K)ᵍ[u]) = Nat.card D * (2 ^ f) ^ 3 := by
  rw [card_conjg, c.card_A]

theorem Au_isSylowOf_K : IsSylowOf 2 ((P ⊓ K)ᵍ[u]) K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.ABGLocalTools.isSylowOf_of_card c.Au_le_K ?_
  rw [card_conjg]
  exact c.A_isSylowOf_K.card_eq

theorem mem_D_of_normalizer_Au {y : 𝔊} (hyA : y ∈ P ⊓ K)
    (hy : y ∈ normalizer (((P ⊓ K)ᵍ[u] : Subgroup 𝔊) : Set 𝔊)) : y ∈ D := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyP : y ∈ P := (mem_inf.1 hyA).1
  have hyK : y ∈ K := (mem_inf.1 hyA).2
  have hS : IsSylowOf 2 ((P ⊓ K)ᵍ[u]) K := c.Au_isSylowOf_K
  have hpg : IsPGroup 2 (zpowers y ⊔ (P ⊓ K)ᵍ[u] : Subgroup 𝔊) :=
    IsPGroup.to_sup_of_normal_right' (c.P_pgroup.to_le (zpowers_le.2 hyP)) hS.isPGroup
      (zpowers_le.2 hy)
  have hle : zpowers y ⊔ (P ⊓ K)ᵍ[u] ≤ K := sup_le (zpowers_le.2 hyK) hS.le
  have heq := hS.eq_of_le le_sup_right hle hpg
  have hyAu : y ∈ (P ⊓ K)ᵍ[u] := by
    have h : y ∈ zpowers y ⊔ (P ⊓ K)ᵍ[u] := mem_sup_left (mem_zpowers y)
    rwa [heq] at h
  have h3 : y ∈ (P ⊓ K) ⊓ (P ⊓ K)ᵍ[u] := mem_inf.2 ⟨hyA, hyAu⟩
  rw [c.A_inf_Au] at h3
  exact h3

theorem conj_Au_ne {y : 𝔊} (hyA : y ∈ P ⊓ K) (hyD : y ∉ D) :
    ((P ⊓ K)ᵍ[u])ᵍ[y⁻¹] ≠ (P ⊓ K)ᵍ[u] := by
  intro h
  apply hyD
  apply c.mem_D_of_normalizer_Au hyA
  have := inv_mem (mem_normalizer_of_conjg_eq h)
  simpa using this

theorem Au_sup_conj {y : 𝔊} (hyA : y ∈ P ⊓ K) (hyD : y ∉ D) :
    (P ⊓ K)ᵍ[u] ⊔ ((P ⊓ K)ᵍ[u])ᵍ[y⁻¹] = K := by
  have hyK : y ∈ K := (mem_inf.1 hyA).2
  have hyN : y⁻¹ ∈ normalizer (K : Set 𝔊) := inv_mem (c.N_le_normalizer_K (c.K_le_N hyK))
  have hDy : Dᵍ[y⁻¹] = D :=
    conjg_eq_of_mem_normalizer (inv_mem (c.N_le_normalizer_D (c.K_le_N hyK)))
  refine (c.sylow_sup_inf c.D_le_Au (hDy ▸ conjg_mono c.D_le_Au y⁻¹) c.Au_le_K ?_ c.card_Au
    (by rw [card_conjg, c.card_Au]) (c.conj_Au_ne hyA hyD).symm).1
  have := conjg_mono c.Au_le_K y⁻¹
  rwa [conjg_eq_of_mem_normalizer hyN] at this

end Step1j

end E2Ctx

section Counting

variable {G : Type*} [Group G] [Finite G]

theorem card_mul_le_of_conjugates {A D Q Ω : Subgroup G}
    (hΩ : ∀ a ∈ A, ∀ z ∈ Q, a * z * a⁻¹ ∈ Ω)
    (hdisj : ∀ a ∈ A, ∀ a' ∈ A, ∀ z : G, z ≠ 1 → a⁻¹ * z * a ∈ Q → a'⁻¹ * z * a' ∈ Q →
      a⁻¹ * a' ∈ D) :
    Nat.card A * (Nat.card Q - 1) ≤ (Nat.card Ω - 1) * Nat.card D := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hfs : ∀ X : Subgroup G, (Finset.univ.filter (· ∈ X)).card = Nat.card X := fun X => by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hmem : ∀ (X : Subgroup G) (x : G), x ∈ Finset.univ.filter (· ∈ X) ↔ x ∈ X := fun X x => by
    simp
  set r : G → G → Prop := fun a z => a⁻¹ * z * a ∈ Q with hr
  have key := Finset.card_mul_le_card_mul (s := Finset.univ.filter (· ∈ A))
    (t := (Finset.univ.filter (· ∈ Ω)).erase 1) r (m := Nat.card Q - 1) (n := Nat.card D) ?_ ?_
  · rw [Finset.card_erase_of_mem ((hmem Ω 1).2 (one_mem Ω)), hfs, hfs] at key
    exact key
  ·
    intro a ha
    have haA : a ∈ A := (hmem A a).1 ha
    have h1 : ((Finset.univ.filter (· ∈ Q)).erase 1).card ≤
        (((Finset.univ.filter (· ∈ Ω)).erase 1).filter (r a)).card := by
      apply Finset.card_le_card_of_injOn (fun z => a * z * a⁻¹)
      · intro z hz
        simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, hmem,
          Set.mem_singleton_iff] at hz
        simp only [Finset.coe_filter, Finset.mem_erase, hmem, Set.mem_setOf_eq, hr]
        have e : a⁻¹ * (a * z * a⁻¹) * a = z := by group
        refine ⟨⟨?_, hΩ a haA z hz.1⟩, ?_⟩
        · intro h
          apply hz.2
          have := congrArg (fun x => a⁻¹ * x * a) h
          simp only [e] at this
          simpa using this
        · rw [e]
          exact hz.1
      · intro z _ z' _ h
        have h' : a * z * a⁻¹ = a * z' * a⁻¹ := h
        exact mul_left_cancel (mul_right_cancel h')
    rw [Finset.card_erase_of_mem ((hmem Q 1).2 (one_mem Q)), hfs] at h1
    exact h1
  ·
    intro z hz
    have hz1 : z ≠ 1 := (Finset.mem_erase.1 hz).1
    by_cases hne : ((Finset.univ.filter (· ∈ A)).filter (fun a => r a z)).Nonempty
    · obtain ⟨a₀, ha₀⟩ := hne
      have ha₀' := Finset.mem_filter.1 ha₀
      have h1 : ((Finset.univ.filter (· ∈ A)).filter (fun a => r a z)).card ≤
          (Finset.univ.filter (· ∈ D)).card := by
        apply Finset.card_le_card_of_injOn (fun a => a₀⁻¹ * a)
        · intro a ha
          have ha' := Finset.mem_filter.1 (Finset.mem_coe.1 ha)
          rw [Finset.mem_coe, hmem]
          exact hdisj a₀ ((hmem A a₀).1 ha₀'.1) a ((hmem A a).1 ha'.1) z hz1 ha₀'.2 ha'.2
        · intro a _ a' _ h
          exact mul_left_cancel h
      rw [hfs] at h1
      exact h1
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      simp only [Finset.bipartiteBelow, hne, Finset.card_empty]
      exact Nat.zero_le _

end Counting

namespace E2Ctx

section Step1j2

variable {𝔊 : Type*} [Group 𝔊] [Finite 𝔊] {f : ℕ} {Γ : Type} [Field Γ] [Finite Γ]
  {t u : 𝔊} {K D P Y W F J J₀ C : Subgroup 𝔊} {φ : ↥K →* SL(2, Γ)}
  (c : E2Ctx f Γ t u K D P Y W F J J₀ C φ)

include c

theorem Q_conj_t : (((zc (P ⊓ K))ᵍ[u])ᵍ[t] ⊓ W)ᵍ[t] = (zc (P ⊓ K))ᵍ[u] ⊓ W := by
  rw [conjg_inf, c.W_conj, map_conj_inv_map_conj_inv c.t_mul_t]

theorem card_Q₁ (hZ : zc K = ⊥) : Nat.card ↥((zc (P ⊓ K))ᵍ[u] ⊓ W) = (2 ^ f) ^ 3 := by
  rw [← c.Q_conj_t, card_conjg]
  exact c.card_Q hZ

theorem Q₁_le_Ht (hZ : zc K = ⊥) : (zc (P ⊓ K))ᵍ[u] ⊓ W ≤ (zc (P ⊓ K))ᵍ[t] := by
  rw [← c.Q_conj_t]
  exact conjg_mono (c.Q_le_H hZ) t

theorem key_disjoint (hZ : zc K = ⊥) {a a' z : 𝔊} (ha : a ∈ P ⊓ K) (ha' : a' ∈ P ⊓ K)
    (hz1 : z ≠ 1) (hq : a⁻¹ * z * a ∈ (zc (P ⊓ K))ᵍ[u] ⊓ W)
    (hq' : a'⁻¹ * z * a' ∈ (zc (P ⊓ K))ᵍ[u] ⊓ W) : a⁻¹ * a' ∈ D := by
  by_contra hyD
  set y := a⁻¹ * a' with hy
  have hyA : y ∈ P ⊓ K := mul_mem (inv_mem ha) ha'
  set q₁ := a⁻¹ * z * a with hq₁
  set q₂ := a'⁻¹ * z * a' with hq₂
  have hq₂y : q₂ = y⁻¹ * q₁ * y := by
    simp only [hq₂, hq₁, hy]
    group
  have hzcAu : zc ((P ⊓ K)ᵍ[u]) = (zc (P ⊓ K))ᵍ[u] := zc_conjg _ _
  have h1 : q₁ ∈ zc ((P ⊓ K)ᵍ[u]) := by
    rw [hzcAu]
    exact (mem_inf.1 hq).1
  have h2 : q₂ ∈ zc ((P ⊓ K)ᵍ[u]) := by
    rw [hzcAu]
    exact (mem_inf.1 hq').1
  obtain ⟨h1A, h1c⟩ := mem_zc_iff.1 h1
  obtain ⟨h2A, h2c⟩ := mem_zc_iff.1 h2
  have hc1 : (P ⊓ K)ᵍ[u] ≤ centralizer ({q₁} : Set 𝔊) := fun b hb =>
    mem_centralizer_singleton_iff.2 (h1c b hb)
  have hc2 : ((P ⊓ K)ᵍ[u])ᵍ[y⁻¹] ≤ centralizer ({q₁} : Set 𝔊) := by
    intro b₂ hb₂
    rw [mem_conjg_iff] at hb₂
    have hb : y⁻¹ * b₂ * y ∈ (P ⊓ K)ᵍ[u] := by simpa using hb₂
    have h3 := h2c _ hb
    rw [hq₂y] at h3
    refine mem_centralizer_singleton_iff.2 ?_
    have e : b₂ * q₁ = y * ((y⁻¹ * b₂ * y) * (y⁻¹ * q₁ * y)) * y⁻¹ := by group
    have e' : q₁ * b₂ = y * ((y⁻¹ * q₁ * y) * (y⁻¹ * b₂ * y)) * y⁻¹ := by group
    rw [e, e', h3]
  have hsup := c.Au_sup_conj hyA hyD
  have hcK : K ≤ centralizer ({q₁} : Set 𝔊) := by
    rw [← hsup]
    exact sup_le hc1 hc2
  have hq₁K : q₁ ∈ K := c.Au_le_K h1A
  have hq₁Z : q₁ ∈ zc K :=
    mem_zc_iff.2 ⟨hq₁K, fun k hk => mem_centralizer_singleton_iff.1 (hcK hk)⟩
  rw [hZ, Subgroup.mem_bot] at hq₁Z
  apply hz1
  have hz : z = a * q₁ * a⁻¹ := by
    simp only [hq₁]
    group
  rw [hz, hq₁Z]
  group

end Step1j2

end E2Ctx

namespace E2Ctx

section Step1j3

variable {𝔊 : Type*} [Group 𝔊] [Finite 𝔊] {f : ℕ} {Γ : Type} [Field Γ] [Finite Γ]
  {t u : 𝔊} {K D P Y W F J J₀ C : Subgroup 𝔊} {φ : ↥K →* SL(2, Γ)}
  (c : E2Ctx f Γ t u K D P Y W F J J₀ C φ)

include c

theorem zc_K_ne_bot : zc K ≠ ⊥ := by
  intro hZ
  have hA : ∀ a ∈ P ⊓ K, ∀ z ∈ (zc (P ⊓ K))ᵍ[u] ⊓ W,
      a * z * a⁻¹ ∈ (zc (P ⊓ K))ᵍ[t] ⊓ W := by
    intro a ha z hz
    have haP : a ∈ P := (mem_inf.1 ha).1
    have haK : a ∈ K := (mem_inf.1 ha).2
    have hNHt : a ∈ normalizer (((zc (P ⊓ K))ᵍ[t] : Subgroup 𝔊) : Set 𝔊) := by
      have := mem_normalizer_zc (c.K_le_normalizer_At haK)
      rwa [zc_conjg] at this
    have hz' : z ∈ (zc (P ⊓ K))ᵍ[t] ⊓ W := mem_inf.2 ⟨c.Q₁_le_Ht hZ hz, (mem_inf.1 hz).2⟩
    exact (mem_normalizer_iff.1 (Common.mem_normalizer_inf hNHt (c.P_le_normalizer_W haP)) z).1 hz'
  have hcount := card_mul_le_of_conjugates (A := P ⊓ K) (D := D)
    (Q := (zc (P ⊓ K))ᵍ[u] ⊓ W) (Ω := (zc (P ⊓ K))ᵍ[t] ⊓ W) hA
    (fun a ha a' ha' z hz1 hq hq' => c.key_disjoint hZ ha ha' hz1 hq hq')
  rw [c.card_A, c.card_Q₁ hZ] at hcount
  have hΩ : Nat.card ↥((zc (P ⊓ K))ᵍ[t] ⊓ W) = (2 ^ f) ^ 5 := by
    have : (zc (P ⊓ K) ⊓ W)ᵍ[t] = (zc (P ⊓ K))ᵍ[t] ⊓ W := by rw [conjg_inf, c.W_conj]
    rw [← this, card_conjg]
    exact c.card_H_inf_W hZ
  rw [hΩ] at hcount
  have hDpos : 0 < Nat.card D := Nat.card_pos
  have h3 : (2 ^ f) ^ 3 * ((2 ^ f) ^ 3 - 1) ≤ (2 ^ f) ^ 5 - 1 := by
    have : Nat.card D * ((2 ^ f) ^ 3 * ((2 ^ f) ^ 3 - 1)) ≤ Nat.card D * ((2 ^ f) ^ 5 - 1) := by
      calc Nat.card D * ((2 ^ f) ^ 3 * ((2 ^ f) ^ 3 - 1))
          = Nat.card D * (2 ^ f) ^ 3 * ((2 ^ f) ^ 3 - 1) := by ring
        _ ≤ ((2 ^ f) ^ 5 - 1) * Nat.card D := hcount
        _ = Nat.card D * ((2 ^ f) ^ 5 - 1) := by ring
    exact Nat.le_of_mul_le_mul_left this hDpos
  have ha4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) c.two_le
  set a := 2 ^ f with ha
  have e6 : a ^ 3 * a ^ 3 = a ^ 6 := by ring
  have h56 : 4 * a ^ 5 ≤ a ^ 6 := by
    calc 4 * a ^ 5 ≤ a * a ^ 5 := Nat.mul_le_mul_right _ ha4
      _ = a ^ 6 := by ring
  have h35 : a ^ 3 ≤ a ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h5pos : 1 ≤ a ^ 5 := Nat.one_le_pow _ _ (by omega)
  rw [Nat.mul_sub_one, e6] at h3
  omega

end Step1j3

end E2Ctx

namespace E2Ctx

section Step2a

variable {𝔊 : Type*} [Group 𝔊] [Finite 𝔊] {f : ℕ} {Γ : Type} [Field Γ] [Finite Γ]
  {t u : 𝔊} {K D P Y W F J J₀ C : Subgroup 𝔊} {φ : ↥K →* SL(2, Γ)}
  (c : E2Ctx f Γ t u K D P Y W F J J₀ C φ)

include c

theorem D_le_N : D ≤ K ⊔ Kᵍ[t] := c.D_le_K.trans le_sup_left

theorem zc_N_eq_bot : zc (K ⊔ Kᵍ[t]) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzN, hzc⟩ := mem_zc_iff.1 hz
  have hzD : z ∈ D := by
    rw [← c.N_inf_centralizer_D]
    exact mem_inf.2 ⟨hzN, mem_centralizer_iff.2 fun d hd => (hzc d (c.D_le_N hd))⟩
  have hzY : z ∈ Y := (c.mem_Y z).2 ⟨c.D_le_P hzD, fun p hp => (hzc p (c.P_le_N hp)).symm⟩
  have hzYu : z ∈ Yᵍ[u] := by
    rw [mem_conjg_iff]
    have := hzc u c.u_mem_N
    have e : u * z * u⁻¹ = z := by rw [this]; group
    rw [e]
    exact hzY
  have : z ∈ W ⊓ Wᵍ[u] := mem_inf.2 ⟨c.Y_le_W hzY, conjg_mono c.Y_le_W u hzYu⟩
  rw [c.W_inf] at this
  exact this

theorem zc_Kt_eq : zc (Kᵍ[t]) = (zc K)ᵍ[t] := zc_conjg K t

theorem zc_Kt_conj : (zc (Kᵍ[t]))ᵍ[t] = zc K := by
  rw [c.zc_Kt_eq, map_conj_inv_map_conj_inv c.t_mul_t]

theorem zc_K_le_D : zc K ≤ D := fun z hz =>
  c.central_le_D (mem_zc_iff.1 hz).1 (fun k hk => (mem_zc_iff.1 hz).2 k hk |>.symm)

theorem zc_Kt_le_D : zc (Kᵍ[t]) ≤ D := by
  rw [c.zc_Kt_eq]
  have := conjg_mono c.zc_K_le_D t
  rwa [c.D_conj] at this

theorem zc_inf_zc_Kt : zc K ⊓ zc (Kᵍ[t]) = ⊥ := by
  rw [eq_bot_iff, ← c.zc_N_eq_bot]
  intro z hz
  obtain ⟨h1, h2⟩ := mem_inf.1 hz
  obtain ⟨hzK, hzc1⟩ := mem_zc_iff.1 h1
  obtain ⟨hzKt, hzc2⟩ := mem_zc_iff.1 h2
  refine mem_zc_iff.2 ⟨mem_sup_left hzK, fun n hn => ?_⟩
  have hle : K ⊔ Kᵍ[t] ≤ centralizer ({z} : Set 𝔊) := sup_le
    (fun k hk => mem_centralizer_singleton_iff.2 (hzc1 k hk))
    (fun k hk => mem_centralizer_singleton_iff.2 (hzc2 k hk))
  exact mem_centralizer_singleton_iff.1 (hle hn)

theorem zc_Kt_ne_bot : zc (Kᵍ[t]) ≠ ⊥ := by
  intro h
  apply c.zc_K_ne_bot
  rw [← c.zc_Kt_conj, h, Subgroup.map_bot]

theorem N_le_normalizer_zc_K : K ⊔ Kᵍ[t] ≤ normalizer ((zc K : Subgroup 𝔊) : Set 𝔊) := fun n hn =>
  mem_normalizer_zc (c.N_le_normalizer_K hn)

theorem N_le_normalizer_zc_Kt :
    K ⊔ Kᵍ[t] ≤ normalizer ((zc (Kᵍ[t]) : Subgroup 𝔊) : Set 𝔊) := fun n hn =>
  mem_normalizer_zc (c.N_le_normalizer_Kt hn)

end Step2a

end E2Ctx

namespace E2Ctx

section Step2b

variable {𝔊 : Type*} [Group 𝔊] [Finite 𝔊] {f : ℕ} {Γ : Type} [Field Γ] [Finite Γ]
  {t u : 𝔊} {K D P Y W F J J₀ C : Subgroup 𝔊} {φ : ↥K →* SL(2, Γ)}
  (c : E2Ctx f Γ t u K D P Y W F J J₀ C φ)

include c

theorem t_conj_conj (x : 𝔊) : t * (t * x * t⁻¹) * t⁻¹ = x := by
  calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
    _ = x := by rw [c.t_mul_t]; group

theorem t_conj_mem_zc_K {e : 𝔊} (he : e ∈ zc (Kᵍ[t])) : t * e * t⁻¹ ∈ zc K := by
  rw [← c.zc_Kt_conj, mem_conjg_iff, c.t_conj_conj]
  exact he

theorem t_conj_mem_zc_Kt {e : 𝔊} (he : e ∈ zc K) : t * e * t⁻¹ ∈ zc (Kᵍ[t]) := by
  rw [c.zc_Kt_eq, mem_conjg_iff, c.t_conj_conj]
  exact he

theorem card_zc_Kt : Nat.card ↥(zc (Kᵍ[t])) = (2 ^ f) ^ 8 := by
  set E := zc (Kᵍ[t]) with hE
  set E' := zc K with hE'
  set X := (E ⊔ E') ⊓ centralizer ({t} : Set 𝔊) with hX
  have hED : E ≤ D := c.zc_Kt_le_D
  have hE'D : E' ≤ D := c.zc_K_le_D
  have hEE' : E ⊓ E' = ⊥ := by
    rw [inf_comm]
    exact c.zc_inf_zc_Kt
  have hmul : ((E ⊔ E' : Subgroup 𝔊) : Set 𝔊) = (E : Set 𝔊) * (E' : Set 𝔊) :=
    Subgroup.coe_mul_of_left_le_normalizer_right E E' (c.le_normalizer_of_le_D hE'D hED)
  have htE : ∀ e ∈ E, t * e * t⁻¹ ∈ E' := fun e he => c.t_conj_mem_zc_K he
  have htE' : ∀ e ∈ E', t * e * t⁻¹ ∈ E := fun e he => c.t_conj_mem_zc_Kt he
  have hψmem : ∀ e ∈ E, e * (t * e * t⁻¹) ∈ X := by
    intro e he
    refine mem_inf.2 ⟨mul_mem (mem_sup_left he) (mem_sup_right (htE e he)), ?_⟩
    rw [mem_centralizer_singleton_iff]
    have hcomm := c.D_comm e (hED he) (t * e * t⁻¹) (hE'D (htE e he))
    have h1 : t * (e * (t * e * t⁻¹)) * t⁻¹ = (t * e * t⁻¹) * (t * (t * e * t⁻¹) * t⁻¹) := by
      group
    rw [c.t_conj_conj] at h1
    have h2 : t * (e * (t * e * t⁻¹)) * t⁻¹ = e * (t * e * t⁻¹) := by
      rw [h1]
      exact hcomm.symm
    calc e * (t * e * t⁻¹) * t = (t * (e * (t * e * t⁻¹)) * t⁻¹) * t := by rw [h2]
      _ = t * (e * (t * e * t⁻¹)) := by group
  have hψinj : ∀ e ∈ E, ∀ e₂ ∈ E, e * (t * e * t⁻¹) = e₂ * (t * e₂ * t⁻¹) → e = e₂ := by
    intro e he e₂ he₂ h
    have h1 : e₂⁻¹ * e = (t * e₂ * t⁻¹) * (t * e * t⁻¹)⁻¹ := by
      calc e₂⁻¹ * e = e₂⁻¹ * (e * (t * e * t⁻¹)) * (t * e * t⁻¹)⁻¹ := by group
        _ = e₂⁻¹ * (e₂ * (t * e₂ * t⁻¹)) * (t * e * t⁻¹)⁻¹ := by rw [h]
        _ = (t * e₂ * t⁻¹) * (t * e * t⁻¹)⁻¹ := by group
    have h2 : e₂⁻¹ * e ∈ E ⊓ E' :=
      mem_inf.2 ⟨mul_mem (inv_mem he₂) he, by
        rw [h1]
        exact mul_mem (htE e₂ he₂) (inv_mem (htE e he))⟩
    rw [hEE', Subgroup.mem_bot] at h2
    exact (inv_mul_eq_one.1 h2).symm
  have hψsurj : ∀ g ∈ X, ∃ e ∈ E, g = e * (t * e * t⁻¹) := by
    intro g hg
    obtain ⟨hgEE', hgt⟩ := mem_inf.1 hg
    have hg' : g ∈ (E : Set 𝔊) * (E' : Set 𝔊) := by
      rw [← hmul]
      exact hgEE'
    obtain ⟨e, he, e', he', rfl⟩ := Set.mem_mul.1 hg'
    have hfix : t * (e * e') * t⁻¹ = e * e' := by
      have := mem_centralizer_singleton_iff.1 hgt
      rw [← this]
      group
    have h1 : t * e * t⁻¹ ∈ E' := htE e he
    have h2 : t * e' * t⁻¹ ∈ E := htE' e' he'
    have h3 : t * (e * e') * t⁻¹ = (t * e * t⁻¹) * (t * e' * t⁻¹) := by group
    rw [hfix] at h3
    have hc := c.D_comm (t * e * t⁻¹) (hE'D h1) (t * e' * t⁻¹) (hED h2)
    have h4 : e⁻¹ * (t * e' * t⁻¹) = e' * (t * e * t⁻¹)⁻¹ := by
      calc e⁻¹ * (t * e' * t⁻¹)
          = e⁻¹ * ((t * e' * t⁻¹) * (t * e * t⁻¹)) * (t * e * t⁻¹)⁻¹ := by group
        _ = e⁻¹ * ((t * e * t⁻¹) * (t * e' * t⁻¹)) * (t * e * t⁻¹)⁻¹ := by rw [hc]
        _ = e⁻¹ * (e * e') * (t * e * t⁻¹)⁻¹ := by rw [h3]
        _ = e' * (t * e * t⁻¹)⁻¹ := by group
    have h5 : e⁻¹ * (t * e' * t⁻¹) ∈ E ⊓ E' :=
      mem_inf.2 ⟨mul_mem (inv_mem he) h2, by rw [h4]; exact mul_mem he' (inv_mem h1)⟩
    rw [hEE', Subgroup.mem_bot] at h5
    have h6 : e = t * e' * t⁻¹ := inv_mul_eq_one.1 h5
    have h7 : e' = t * e * t⁻¹ := by
      rw [h6, c.t_conj_conj]
    refine ⟨e, he, ?_⟩
    rw [← h7]
  have hXcard : Nat.card ↥E = Nat.card ↥X := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun e : ↥E => (⟨(e : 𝔊) * (t * (e : 𝔊) * t⁻¹), hψmem e e.2⟩ : ↥X)) ⟨?_, ?_⟩)
    · intro e₁ e₂ h
      apply Subtype.ext
      exact hψinj e₁ e₁.2 e₂ e₂.2 (congrArg Subtype.val h)
    · intro g
      obtain ⟨e, he, hge⟩ := hψsurj g g.2
      exact ⟨⟨e, he⟩, Subtype.ext hge.symm⟩
  have hXD : X ≤ D ⊓ centralizer ({t} : Set 𝔊) := inf_le_inf_right _ (sup_le hED hE'D)
  have hCX : C ≤ normalizer (X : Set 𝔊) := fun g hg =>
    Common.mem_normalizer_inf
      (Common.mem_normalizer_sup (c.N_le_normalizer_zc_Kt (c.C_le_N hg))
        (c.N_le_normalizer_zc_K (c.C_le_N hg)))
      (Subgroup.le_normalizer (c.C_cen_t hg))
  have hXne : X ≠ ⊥ := by
    obtain ⟨e, he, he1⟩ : ∃ e ∈ E, e ≠ 1 := by
      obtain ⟨⟨e, he⟩, h1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 c.zc_Kt_ne_bot
      exact ⟨e, he, fun h => h1 (Subtype.ext h)⟩
    intro hX0
    have h0 := hψmem e he
    rw [hX0, Subgroup.mem_bot] at h0
    have h1 : e ∈ E' := by
      have : e = (t * e * t⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h0
      rw [this]
      exact inv_mem (htE e he)
    have h2 : e ∈ E ⊓ E' := mem_inf.2 ⟨he, h1⟩
    rw [hEE', Subgroup.mem_bot] at h2
    exact he1 h2
  have hXeq : X = D ⊓ centralizer ({t} : Set 𝔊) := (c.C_irr X hXD hCX).resolve_left hXne
  rw [hXcard, hXeq, c.card_D₁]

end Step2b

end E2Ctx

namespace E2Ctx

section Step2c

variable {𝔊 : Type*} [Group 𝔊] [Finite 𝔊] {f : ℕ} {Γ : Type} [Field Γ] [Finite Γ]
  {t u : 𝔊} {K D P Y W F J J₀ C : Subgroup 𝔊} {φ : ↥K →* SL(2, Γ)}
  (c : E2Ctx f Γ t u K D P Y W F J J₀ C φ)

include c

theorem card_zc_K : Nat.card ↥(zc K) = (2 ^ f) ^ 8 := by
  have := c.card_zc_Kt
  rw [c.zc_Kt_eq, card_conjg] at this
  exact this

theorem D_eq_zc_sup : D = zc (Kᵍ[t]) ⊔ zc K := by
  have hle : zc (Kᵍ[t]) ⊔ zc K ≤ D := sup_le c.zc_Kt_le_D c.zc_K_le_D
  have hc := Common.card_sup_mul_card_inf_eq (A := zc (Kᵍ[t])) (B := zc K)
    (c.le_normalizer_of_le_D c.zc_Kt_le_D c.zc_K_le_D)
  rw [inf_comm, c.zc_inf_zc_Kt, Subgroup.card_bot, mul_one, c.card_zc_Kt, c.card_zc_K] at hc
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hc, c.card_D]
  exact (by ring : (2 ^ f) ^ 16 = (2 ^ f) ^ 8 * (2 ^ f) ^ 8).le

theorem comm_K_D_le : ⁅K, D⁆ ≤ zc (Kᵍ[t]) := by
  rw [Subgroup.commutator_le]
  intro k hk d hd
  have hmul : ((zc (Kᵍ[t]) ⊔ zc K : Subgroup 𝔊) : Set 𝔊) =
      (zc (Kᵍ[t]) : Set 𝔊) * (zc K : Set 𝔊) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (c.le_normalizer_of_le_D c.zc_K_le_D c.zc_Kt_le_D)
  have hd' : d ∈ (zc (Kᵍ[t]) : Set 𝔊) * (zc K : Set 𝔊) := by
    rw [← hmul, ← c.D_eq_zc_sup]
    exact hd
  obtain ⟨e, he, e', he', rfl⟩ := Set.mem_mul.1 hd'
  have hke : k * e * k⁻¹ ∈ zc (Kᵍ[t]) :=
    (mem_normalizer_iff.1 (mem_normalizer_zc (c.K_le_normalizer_Kt hk)) e).1 he
  have hk' : k * e' = e' * k := (mem_zc_iff.1 he').2 k hk
  have h1 : k * e' * k⁻¹ = e' := by rw [hk']; group
  have e1 : k * (e * e') * k⁻¹ * (e * e')⁻¹ = (k * e * k⁻¹) * e⁻¹ := by
    calc k * (e * e') * k⁻¹ * (e * e')⁻¹
        = (k * e * k⁻¹) * (k * e' * k⁻¹) * e'⁻¹ * e⁻¹ := by group
      _ = (k * e * k⁻¹) * e' * e'⁻¹ * e⁻¹ := by rw [h1]
      _ = (k * e * k⁻¹) * e⁻¹ := by group
  rw [commutatorElement_def, e1]
  exact mul_mem hke (inv_mem he)

theorem commutator_K_inf_D_le : ⁅K, K⁆ ⊓ D ≤ zc (Kᵍ[t]) :=
  commutator_inf_le_of_sl2_two_pow_quotient (m := 3 * f) (by have := c.two_le; omega)
    c.card_Γ_pow c.zc_Kt_le_D c.comm_K_D_le φ c.φ_surj c.φ_ker

theorem K'_le_K : ⁅K, K⁆ ≤ K := commutator_le_of_le le_rfl le_rfl

theorem N_le_normalizer_K' : K ⊔ Kᵍ[t] ≤ normalizer ((⁅K, K⁆ : Subgroup 𝔊) : Set 𝔊) :=
  fun n hn => by
    apply mem_normalizer_of_conjg_eq
    rw [conjg_commutator, conjg_eq_of_mem_normalizer (c.N_le_normalizer_K hn)]

theorem N_le_normalizer_Kt' :
    K ⊔ Kᵍ[t] ≤ normalizer ((⁅Kᵍ[t], Kᵍ[t]⁆ : Subgroup 𝔊) : Set 𝔊) := fun n hn => by
  apply mem_normalizer_of_conjg_eq
  rw [conjg_commutator, conjg_eq_of_mem_normalizer (c.N_le_normalizer_Kt hn)]

theorem zc_Kt_le_K : zc (Kᵍ[t]) ≤ K := c.zc_Kt_le_D.trans c.D_le_K

theorem zc_K_le_Kt : zc K ≤ Kᵍ[t] := c.zc_K_le_D.trans c.D_le_Kt

theorem B_le_K : ⁅K, K⁆ ⊔ zc (Kᵍ[t]) ≤ K := sup_le c.K'_le_K c.zc_Kt_le_K

theorem Bt_eq : (⁅K, K⁆ ⊔ zc (Kᵍ[t]))ᵍ[t] = ⁅Kᵍ[t], Kᵍ[t]⁆ ⊔ zc K := by
  rw [conjg_sup, conjg_commutator, c.zc_Kt_conj]

theorem Bt_le_Kt : (⁅K, K⁆ ⊔ zc (Kᵍ[t]))ᵍ[t] ≤ Kᵍ[t] := conjg_mono c.B_le_K t

theorem N_le_normalizer_B :
    K ⊔ Kᵍ[t] ≤ normalizer (((⁅K, K⁆ ⊔ zc (Kᵍ[t]) : Subgroup 𝔊)) : Set 𝔊) := fun n hn =>
  Common.mem_normalizer_sup (c.N_le_normalizer_K' hn) (c.N_le_normalizer_zc_Kt hn)

theorem N_le_normalizer_Bt :
    K ⊔ Kᵍ[t] ≤ normalizer (((⁅K, K⁆ ⊔ zc (Kᵍ[t]))ᵍ[t] : Subgroup 𝔊) : Set 𝔊) := fun n hn => by
  rw [c.Bt_eq]
  exact Common.mem_normalizer_sup (c.N_le_normalizer_Kt' hn) (c.N_le_normalizer_zc_K hn)

theorem B_inf_D : (⁅K, K⁆ ⊔ zc (Kᵍ[t])) ⊓ D = zc (Kᵍ[t]) := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right c.zc_Kt_le_D)
  obtain ⟨hxB, hxD⟩ := mem_inf.1 hx
  have hmul : ((⁅K, K⁆ ⊔ zc (Kᵍ[t]) : Subgroup 𝔊) : Set 𝔊) =
      ((⁅K, K⁆ : Subgroup 𝔊) : Set 𝔊) * (zc (Kᵍ[t]) : Set 𝔊) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (fun k hk => mem_normalizer_zc (c.K_le_normalizer_Kt (c.K'_le_K hk)))
  have hx' : x ∈ ((⁅K, K⁆ : Subgroup 𝔊) : Set 𝔊) * (zc (Kᵍ[t]) : Set 𝔊) := by
    rw [← hmul]
    exact hxB
  obtain ⟨k, hk, e, he, rfl⟩ := Set.mem_mul.1 hx'
  have hkD : k ∈ D := by
    have : k = k * e * e⁻¹ := by group
    rw [this]
    exact mul_mem hxD (inv_mem (c.zc_Kt_le_D he))
  have := c.commutator_K_inf_D_le (mem_inf.2 ⟨hk, hkD⟩)
  exact mul_mem this he

theorem Bt_inf_D : (⁅K, K⁆ ⊔ zc (Kᵍ[t]))ᵍ[t] ⊓ D = zc K := by
  have := congrArg (fun X : Subgroup 𝔊 => Xᵍ[t]) c.B_inf_D
  simp only [conjg_inf, c.D_conj, c.zc_Kt_conj] at this
  exact this

theorem B_inf_Bt : (⁅K, K⁆ ⊔ zc (Kᵍ[t])) ⊓ (⁅K, K⁆ ⊔ zc (Kᵍ[t]))ᵍ[t] = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := mem_inf.1 hx
  have hxD : x ∈ D := by
    rw [← c.K_inf]
    exact mem_inf.2 ⟨c.B_le_K hx1, c.Bt_le_Kt hx2⟩
  have h1 : x ∈ zc (Kᵍ[t]) := by
    rw [← c.B_inf_D]
    exact mem_inf.2 ⟨hx1, hxD⟩
  have h2 : x ∈ zc K := by
    rw [← c.Bt_inf_D]
    exact mem_inf.2 ⟨hx2, hxD⟩
  have : x ∈ zc K ⊓ zc (Kᵍ[t]) := mem_inf.2 ⟨h2, h1⟩
  rw [c.zc_inf_zc_Kt] at this
  exact this

theorem comm_B_Bt : ⁅⁅K, K⁆ ⊔ zc (Kᵍ[t]), (⁅K, K⁆ ⊔ zc (Kᵍ[t]))ᵍ[t]⁆ = ⊥ := by
  rw [eq_bot_iff, ← c.B_inf_Bt, Subgroup.commutator_le]
  intro b hb x hx
  rw [commutatorElement_def]
  refine mem_inf.2 ⟨?_, ?_⟩
  · have hbN : x ∈ K ⊔ Kᵍ[t] := mem_sup_right (c.Bt_le_Kt hx)
    have h1 := (mem_normalizer_iff.1 (c.N_le_normalizer_B hbN) b).1 hb
    have h2 := (mem_normalizer_iff.1 (c.N_le_normalizer_B hbN) b⁻¹).1 (inv_mem hb)
    have e : b * x * b⁻¹ * x⁻¹ = b * (x * b⁻¹ * x⁻¹) := by group
    rw [e]
    exact mul_mem hb h2
  · have hbN : b ∈ K ⊔ Kᵍ[t] := mem_sup_left (c.B_le_K hb)
    have h1 := (mem_normalizer_iff.1 (c.N_le_normalizer_Bt hbN) x).1 hx
    exact mul_mem h1 (inv_mem hx)

theorem N_eq_B_sup_Bt :
    K ⊔ Kᵍ[t] = (⁅K, K⁆ ⊔ zc (Kᵍ[t])) ⊔ (⁅K, K⁆ ⊔ zc (Kᵍ[t]))ᵍ[t] := by
  have hBt : (⁅K, K⁆ ⊔ zc (Kᵍ[t]))ᵍ[t] = ⁅Kᵍ[t], Kᵍ[t]⁆ ⊔ zc K := c.Bt_eq
  have hK' : ⁅K, K⁆ ≤ (⁅K, K⁆ ⊔ zc (Kᵍ[t])) ⊔ (⁅K, K⁆ ⊔ zc (Kᵍ[t]))ᵍ[t] :=
    le_sup_left.trans le_sup_left
  have hE : zc (Kᵍ[t]) ≤ (⁅K, K⁆ ⊔ zc (Kᵍ[t])) ⊔ (⁅K, K⁆ ⊔ zc (Kᵍ[t]))ᵍ[t] :=
    le_sup_right.trans le_sup_left
  have hE' : zc K ≤ (⁅K, K⁆ ⊔ zc (Kᵍ[t])) ⊔ (⁅K, K⁆ ⊔ zc (Kᵍ[t]))ᵍ[t] := by
    have : zc K ≤ (⁅K, K⁆ ⊔ zc (Kᵍ[t]))ᵍ[t] := by
      rw [hBt]
      exact le_sup_right
    exact this.trans le_sup_right
  have hK : K ≤ (⁅K, K⁆ ⊔ zc (Kᵍ[t])) ⊔ (⁅K, K⁆ ⊔ zc (Kᵍ[t]))ᵍ[t] := by
    have hD : D ≤ (⁅K, K⁆ ⊔ zc (Kᵍ[t])) ⊔ (⁅K, K⁆ ⊔ zc (Kᵍ[t]))ᵍ[t] := by
      rw [c.D_eq_zc_sup]
      exact sup_le hE hE'
    have h1 : K ≤ ⁅K, K⁆ ⊔ D := c.K_eq_commutator_sup.le
    exact h1.trans (sup_le hK' hD)
  apply le_antisymm
  · refine sup_le hK ?_
    have h2 := conjg_mono hK t
    rw [conjg_sup, map_conj_inv_map_conj_inv c.t_mul_t, sup_comm] at h2
    exact h2
  · exact sup_le_sup c.B_le_K c.Bt_le_Kt

end Step2c

end E2Ctx

section Diagonal

variable {G : Type*} [Group G]

theorem conj_conj_of_mul_self {t : G} (htt : t * t = 1) (x : G) :
    t * (t * x * t⁻¹) * t⁻¹ = x := by
  calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
    _ = x := by rw [htt]; group

theorem conj_mem_conjg {t : G} (htt : t * t = 1) {A : Subgroup G} {a : G} (ha : a ∈ A) :
    t * a * t⁻¹ ∈ Aᵍ[t] := by
  rw [mem_conjg_iff, conj_conj_of_mul_self htt]
  exact ha

theorem conj_mem_of_mem_conjg {t : G} {A : Subgroup G} {a : G} (ha : a ∈ Aᵍ[t]) :
    t * a * t⁻¹ ∈ A :=
  mem_conjg_iff.1 ha

theorem diag_fixed {t : G} (htt : t * t = 1) {A : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ Aᵍ[t], a * b = b * a) {a : G} (ha : a ∈ A) :
    (a * (t * a * t⁻¹)) * t = t * (a * (t * a * t⁻¹)) := by
  have h1 : t * (a * (t * a * t⁻¹)) * t⁻¹ = (t * a * t⁻¹) * (t * (t * a * t⁻¹) * t⁻¹) := by
    group
  rw [conj_conj_of_mul_self htt] at h1
  have h2 : t * (a * (t * a * t⁻¹)) * t⁻¹ = a * (t * a * t⁻¹) := by
    rw [h1]
    exact (hcomm a ha _ (conj_mem_conjg htt ha)).symm
  calc a * (t * a * t⁻¹) * t = (t * (a * (t * a * t⁻¹)) * t⁻¹) * t := by rw [h2]
    _ = t * (a * (t * a * t⁻¹)) := by group

theorem diag_inj {t : G} (htt : t * t = 1) {A : Subgroup G} (hinf : A ⊓ Aᵍ[t] = ⊥) {a a' : G}
    (ha : a ∈ A) (ha' : a' ∈ A) (h : a * (t * a * t⁻¹) = a' * (t * a' * t⁻¹)) : a = a' := by
  have h1 : a'⁻¹ * a = (t * a' * t⁻¹) * (t * a * t⁻¹)⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * (t * a * t⁻¹)) * (t * a * t⁻¹)⁻¹ := by group
      _ = a'⁻¹ * (a' * (t * a' * t⁻¹)) * (t * a * t⁻¹)⁻¹ := by rw [h]
      _ = (t * a' * t⁻¹) * (t * a * t⁻¹)⁻¹ := by group
  have h2 : a'⁻¹ * a ∈ A ⊓ Aᵍ[t] :=
    mem_inf.2 ⟨mul_mem (inv_mem ha') ha, by
      rw [h1]
      exact mul_mem (conj_mem_conjg htt ha') (inv_mem (conj_mem_conjg htt ha))⟩
  rw [hinf, Subgroup.mem_bot] at h2
  exact (inv_mul_eq_one.1 h2).symm

theorem diag_surj {t : G} (htt : t * t = 1) {A : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ b ∈ Aᵍ[t], a * b = b * a) (hinf : A ⊓ Aᵍ[t] = ⊥) {g : G}
    (hg : g ∈ (A : Set G) * (Aᵍ[t] : Set G)) (hgt : g * t = t * g) :
    ∃ a ∈ A, g = a * (t * a * t⁻¹) := by
  obtain ⟨e, he, e', he', rfl⟩ := Set.mem_mul.1 hg
  have hfix : t * (e * e') * t⁻¹ = e * e' := by
    rw [← hgt]
    group
  have h1 : t * e * t⁻¹ ∈ Aᵍ[t] := conj_mem_conjg htt he
  have h2 : t * e' * t⁻¹ ∈ A := conj_mem_of_mem_conjg he'
  have h3 : t * (e * e') * t⁻¹ = (t * e * t⁻¹) * (t * e' * t⁻¹) := by group
  rw [hfix] at h3
  have hc := hcomm (t * e' * t⁻¹) h2 (t * e * t⁻¹) h1
  have h4 : e⁻¹ * (t * e' * t⁻¹) = e' * (t * e * t⁻¹)⁻¹ := by
    calc e⁻¹ * (t * e' * t⁻¹)
        = e⁻¹ * ((t * e' * t⁻¹) * (t * e * t⁻¹)) * (t * e * t⁻¹)⁻¹ := by group
      _ = e⁻¹ * ((t * e * t⁻¹) * (t * e' * t⁻¹)) * (t * e * t⁻¹)⁻¹ := by rw [← hc]
      _ = e⁻¹ * (e * e') * (t * e * t⁻¹)⁻¹ := by rw [h3]
      _ = e' * (t * e * t⁻¹)⁻¹ := by group
  have h5 : e⁻¹ * (t * e' * t⁻¹) ∈ A ⊓ Aᵍ[t] :=
    mem_inf.2 ⟨mul_mem (inv_mem he) h2, by rw [h4]; exact mul_mem he' (inv_mem h1)⟩
  rw [hinf, Subgroup.mem_bot] at h5
  have h6 : e = t * e' * t⁻¹ := inv_mul_eq_one.1 h5
  have h7 : e' = t * e * t⁻¹ := by
    rw [h6, conj_conj_of_mul_self htt]
  refine ⟨e, he, ?_⟩
  rw [← h7]

end Diagonal

namespace E2Ctx

section Step2d

variable {𝔊 : Type*} [Group 𝔊] [Finite 𝔊] {f : ℕ} {Γ : Type} [Field Γ] [Finite Γ]
  {t u : 𝔊} {K D P Y W F J J₀ C : Subgroup 𝔊} {φ : ↥K →* SL(2, Γ)}
  (c : E2Ctx f Γ t u K D P Y W F J J₀ C φ)

include c

theorem card_B : Nat.card ↥(⁅K, K⁆ ⊔ zc (Kᵍ[t])) = Nat.card SL(2, Γ) * (2 ^ f) ^ 8 := by
  have hK : D ⊔ (⁅K, K⁆ ⊔ zc (Kᵍ[t])) = K := by
    apply le_antisymm (sup_le c.D_le_K c.B_le_K)
    calc K = ⁅K, K⁆ ⊔ D := c.K_eq_commutator_sup
      _ ≤ D ⊔ (⁅K, K⁆ ⊔ zc (Kᵍ[t])) := sup_le (le_sup_left.trans le_sup_right) le_sup_left
  have h := Common.card_sup_mul_card_inf_eq (A := D) (B := ⁅K, K⁆ ⊔ zc (Kᵍ[t]))
    (fun b hb => c.N_le_normalizer_D (mem_sup_left (c.B_le_K hb)))
  rw [hK, inf_comm, c.B_inf_D, c.card_K, c.card_zc_Kt] at h
  have hpos : 0 < Nat.card D := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [← h]
  ring

theorem B_comm_Bt : ∀ b ∈ ⁅K, K⁆ ⊔ zc (Kᵍ[t]), ∀ x ∈ (⁅K, K⁆ ⊔ zc (Kᵍ[t]))ᵍ[t],
    b * x = x * b := by
  intro b hb x hx
  have h := Subgroup.commutator_mem_commutator hb hx
  rw [c.comm_B_Bt, Subgroup.mem_bot, commutatorElement_def] at h
  have h1 : b * x * b⁻¹ = x := mul_inv_eq_one.1 h
  calc b * x = (b * x * b⁻¹) * b := by group
    _ = x * b := by rw [h1]

theorem C_eq_Cn : C = (K ⊔ Kᵍ[t]) ⊓ centralizer ({t} : Set 𝔊) := by
  have hBN : ∀ b ∈ ⁅K, K⁆ ⊔ zc (Kᵍ[t]), b ∈ K ⊔ Kᵍ[t] := fun b hb => mem_sup_left (c.B_le_K hb)
  have hBtN : ∀ x ∈ (⁅K, K⁆ ⊔ zc (Kᵍ[t]))ᵍ[t], x ∈ K ⊔ Kᵍ[t] := fun x hx =>
    mem_sup_right (c.Bt_le_Kt hx)
  have hmem : ∀ b ∈ ⁅K, K⁆ ⊔ zc (Kᵍ[t]),
      b * (t * b * t⁻¹) ∈ (K ⊔ Kᵍ[t]) ⊓ centralizer ({t} : Set 𝔊) := by
    intro b hb
    refine mem_inf.2 ⟨mul_mem (hBN b hb) (hBtN _ (conj_mem_conjg c.t_mul_t hb)), ?_⟩
    rw [mem_centralizer_singleton_iff]
    exact diag_fixed c.t_mul_t c.B_comm_Bt hb
  have hmul : ((K ⊔ Kᵍ[t] : Subgroup 𝔊) : Set 𝔊) =
      ((⁅K, K⁆ ⊔ zc (Kᵍ[t]) : Subgroup 𝔊) : Set 𝔊) *
        (((⁅K, K⁆ ⊔ zc (Kᵍ[t]))ᵍ[t] : Subgroup 𝔊) : Set 𝔊) := by
    rw [c.N_eq_B_sup_Bt]
    exact Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (fun b hb => c.N_le_normalizer_Bt (hBN b hb))
  have hcard : Nat.card ↥(⁅K, K⁆ ⊔ zc (Kᵍ[t])) =
      Nat.card ↥((K ⊔ Kᵍ[t]) ⊓ centralizer ({t} : Set 𝔊)) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun b : ↥(⁅K, K⁆ ⊔ zc (Kᵍ[t])) =>
        (⟨(b : 𝔊) * (t * (b : 𝔊) * t⁻¹), hmem b b.2⟩ :
          ↥((K ⊔ Kᵍ[t]) ⊓ centralizer ({t} : Set 𝔊)))) ⟨?_, ?_⟩)
    · intro b₁ b₂ h
      apply Subtype.ext
      exact diag_inj c.t_mul_t c.B_inf_Bt b₁.2 b₂.2 (congrArg Subtype.val h)
    · intro g
      obtain ⟨hgN, hgt⟩ := mem_inf.1 g.2
      have hg' : (g : 𝔊) ∈ ((⁅K, K⁆ ⊔ zc (Kᵍ[t]) : Subgroup 𝔊) : Set 𝔊) *
          (((⁅K, K⁆ ⊔ zc (Kᵍ[t]))ᵍ[t] : Subgroup 𝔊) : Set 𝔊) := by
        rw [← hmul]
        exact hgN
      obtain ⟨b, hb, hgb⟩ := diag_surj c.t_mul_t c.B_comm_Bt c.B_inf_Bt hg'
        (mem_centralizer_singleton_iff.1 hgt)
      exact ⟨⟨b, hb⟩, Subtype.ext hgb.symm⟩
  refine Subgroup.eq_of_le_of_card_ge (le_inf c.C_le_N c.C_cen_t) ?_
  rw [← hcard, c.card_B, c.card_C]

theorem B_mulEquiv_C : Nonempty (↥(⁅K, K⁆ ⊔ zc (Kᵍ[t])) ≃* ↥C) := by
  have hBN : ∀ b ∈ ⁅K, K⁆ ⊔ zc (Kᵍ[t]), b ∈ K ⊔ Kᵍ[t] := fun b hb => mem_sup_left (c.B_le_K hb)
  have hBtN : ∀ x ∈ (⁅K, K⁆ ⊔ zc (Kᵍ[t]))ᵍ[t], x ∈ K ⊔ Kᵍ[t] := fun x hx =>
    mem_sup_right (c.Bt_le_Kt hx)
  have hmem : ∀ b ∈ ⁅K, K⁆ ⊔ zc (Kᵍ[t]), b * (t * b * t⁻¹) ∈ C := by
    intro b hb
    rw [c.C_eq_Cn]
    refine mem_inf.2 ⟨mul_mem (hBN b hb) (hBtN _ (conj_mem_conjg c.t_mul_t hb)), ?_⟩
    rw [mem_centralizer_singleton_iff]
    exact diag_fixed c.t_mul_t c.B_comm_Bt hb
  have hmul : ((K ⊔ Kᵍ[t] : Subgroup 𝔊) : Set 𝔊) =
      ((⁅K, K⁆ ⊔ zc (Kᵍ[t]) : Subgroup 𝔊) : Set 𝔊) *
        (((⁅K, K⁆ ⊔ zc (Kᵍ[t]))ᵍ[t] : Subgroup 𝔊) : Set 𝔊) := by
    rw [c.N_eq_B_sup_Bt]
    exact Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (fun b hb => c.N_le_normalizer_Bt (hBN b hb))
  let δ : ↥(⁅K, K⁆ ⊔ zc (Kᵍ[t])) →* ↥C :=
    MonoidHom.mk' (fun b => ⟨(b : 𝔊) * (t * (b : 𝔊) * t⁻¹), hmem b b.2⟩) (by
      intro a b
      apply Subtype.ext
      have h1 := c.B_comm_Bt b b.2 (t * (a : 𝔊) * t⁻¹) (conj_mem_conjg c.t_mul_t a.2)
      show ((a * b : ↥(⁅K, K⁆ ⊔ zc (Kᵍ[t]))) : 𝔊) *
          (t * ((a * b : ↥(⁅K, K⁆ ⊔ zc (Kᵍ[t]))) : 𝔊) * t⁻¹) =
        ((a : 𝔊) * (t * (a : 𝔊) * t⁻¹)) * ((b : 𝔊) * (t * (b : 𝔊) * t⁻¹))
      simp only [Subgroup.coe_mul]
      calc (a : 𝔊) * b * (t * (a * b) * t⁻¹)
          = a * (b * (t * a * t⁻¹)) * (t * b * t⁻¹) := by group
        _ = a * ((t * a * t⁻¹) * b) * (t * b * t⁻¹) := by rw [h1]
        _ = _ := by group)
  refine ⟨MulEquiv.ofBijective δ ⟨?_, ?_⟩⟩
  · intro b₁ b₂ h
    apply Subtype.ext
    exact diag_inj c.t_mul_t c.B_inf_Bt b₁.2 b₂.2 (congrArg Subtype.val h)
  · intro g
    have hg : (g : 𝔊) ∈ (K ⊔ Kᵍ[t]) ⊓ centralizer ({t} : Set 𝔊) :=
      (le_inf c.C_le_N c.C_cen_t : C ≤ _) g.2
    obtain ⟨hgN, hgt⟩ := mem_inf.1 hg
    have hg' : (g : 𝔊) ∈ ((⁅K, K⁆ ⊔ zc (Kᵍ[t]) : Subgroup 𝔊) : Set 𝔊) *
        (((⁅K, K⁆ ⊔ zc (Kᵍ[t]))ᵍ[t] : Subgroup 𝔊) : Set 𝔊) := by
      rw [← hmul]
      exact hgN
    obtain ⟨b, hb, hgb⟩ := diag_surj c.t_mul_t c.B_comm_Bt c.B_inf_Bt hg'
      (mem_centralizer_singleton_iff.1 hgt)
    exact ⟨⟨b, hb⟩, Subtype.ext hgb.symm⟩

theorem B_perfect : ⁅⁅K, K⁆ ⊔ zc (Kᵍ[t]), ⁅K, K⁆ ⊔ zc (Kᵍ[t])⁆ = ⁅K, K⁆ ⊔ zc (Kᵍ[t]) := by
  obtain ⟨e⟩ := c.B_mulEquiv_C
  haveI hC : Group.IsPerfect ↥C := Subgroup.isPerfect_iff.mpr c.C_perfect
  haveI : Group.IsPerfect ↥(⁅K, K⁆ ⊔ zc (Kᵍ[t])) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Subgroup.isPerfect_iff.1 inferInstance

end Step2d

end E2Ctx

namespace E2Ctx

section Step2e

variable {𝔊 : Type*} [Group 𝔊] [Finite 𝔊] {f : ℕ} {Γ : Type} [Field Γ] [Finite Γ]
  {t u : 𝔊} {K D P Y W F J J₀ C : Subgroup 𝔊} {φ : ↥K →* SL(2, Γ)}
  (c : E2Ctx f Γ t u K D P Y W F J J₀ C φ)

include c

theorem B_comm_le_K' :
    ⁅⁅K, K⁆ ⊔ zc (Kᵍ[t]), ⁅K, K⁆ ⊔ zc (Kᵍ[t])⁆ ≤ ⁅K, K⁆ := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hmul : ((⁅K, K⁆ ⊔ zc (Kᵍ[t]) : Subgroup 𝔊) : Set 𝔊) =
      ((⁅K, K⁆ : Subgroup 𝔊) : Set 𝔊) * (zc (Kᵍ[t]) : Set 𝔊) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (fun k hk => mem_normalizer_zc (c.K_le_normalizer_Kt (c.K'_le_K hk)))
  have hx' : x ∈ ((⁅K, K⁆ : Subgroup 𝔊) : Set 𝔊) * (zc (Kᵍ[t]) : Set 𝔊) := by
    rw [← hmul]
    exact hx
  have hy' : y ∈ ((⁅K, K⁆ : Subgroup 𝔊) : Set 𝔊) * (zc (Kᵍ[t]) : Set 𝔊) := by
    rw [← hmul]
    exact hy
  obtain ⟨k₁, hk₁, e₁, he₁, rfl⟩ := Set.mem_mul.1 hx'
  obtain ⟨k₂, hk₂, e₂, he₂, rfl⟩ := Set.mem_mul.1 hy'
  have hcomm : e₁ * e₂ = e₂ * e₁ :=
    c.D_comm e₁ (c.zc_Kt_le_D he₁) e₂ (c.zc_Kt_le_D he₂)
  have hn₁ : e₁ * k₂ * e₁⁻¹ ∈ ⁅K, K⁆ :=
    (mem_normalizer_iff.1 (c.N_le_normalizer_K' (mem_sup_left (c.zc_Kt_le_K he₁))) k₂).1 hk₂
  have hn₂ : e₂ * k₁ * e₂⁻¹ ∈ ⁅K, K⁆ :=
    (mem_normalizer_iff.1 (c.N_le_normalizer_K' (mem_sup_left (c.zc_Kt_le_K he₂))) k₁).1 hk₁
  rw [commutatorElement_def]
  have key : k₁ * e₁ * (k₂ * e₂) * (k₁ * e₁)⁻¹ * (k₂ * e₂)⁻¹ =
      (k₁ * (e₁ * k₂ * e₁⁻¹)) * (k₂ * (e₂ * k₁ * e₂⁻¹))⁻¹ := by
    calc k₁ * e₁ * (k₂ * e₂) * (k₁ * e₁)⁻¹ * (k₂ * e₂)⁻¹
        = (k₁ * (e₁ * k₂ * e₁⁻¹) * (e₁ * e₂)) * (k₂ * (e₂ * k₁ * e₂⁻¹) * (e₂ * e₁))⁻¹ := by
          group
      _ = (k₁ * (e₁ * k₂ * e₁⁻¹) * (e₂ * e₁)) * (k₂ * (e₂ * k₁ * e₂⁻¹) * (e₂ * e₁))⁻¹ := by
          rw [hcomm]
      _ = (k₁ * (e₁ * k₂ * e₁⁻¹)) * (k₂ * (e₂ * k₁ * e₂⁻¹))⁻¹ := by group
  rw [key]
  exact mul_mem (mul_mem hk₁ hn₁) (inv_mem (mul_mem hk₂ hn₂))

theorem B_eq_K' : ⁅K, K⁆ ⊔ zc (Kᵍ[t]) = ⁅K, K⁆ := by
  refine le_antisymm ?_ le_sup_left
  calc ⁅K, K⁆ ⊔ zc (Kᵍ[t]) = ⁅⁅K, K⁆ ⊔ zc (Kᵍ[t]), ⁅K, K⁆ ⊔ zc (Kᵍ[t])⁆ := c.B_perfect.symm
    _ ≤ ⁅K, K⁆ := c.B_comm_le_K'

theorem zc_Kt_le_K' : zc (Kᵍ[t]) ≤ ⁅K, K⁆ := le_sup_right.trans c.B_eq_K'.le

theorem K'_inf_D : ⁅K, K⁆ ⊓ D = zc (Kᵍ[t]) := by
  have := c.B_inf_D
  rwa [c.B_eq_K'] at this

theorem N_eq_K'_sup : K ⊔ Kᵍ[t] = ⁅K, K⁆ ⊔ (⁅K, K⁆)ᵍ[t] := by
  have := c.N_eq_B_sup_Bt
  rwa [c.B_eq_K'] at this

theorem K'_inf_K't : ⁅K, K⁆ ⊓ (⁅K, K⁆)ᵍ[t] = ⊥ := by
  have := c.B_inf_Bt
  rwa [c.B_eq_K'] at this

theorem comm_K'_K't : ⁅⁅K, K⁆, (⁅K, K⁆)ᵍ[t]⁆ = ⊥ := by
  have := c.comm_B_Bt
  rwa [c.B_eq_K'] at this

theorem K'_mulEquiv_C : Nonempty (↥(⁅K, K⁆) ≃* ↥C) := by
  have := c.B_mulEquiv_C
  rwa [c.B_eq_K'] at this

end Step2e

theorem E2_abstract {𝔊 : Type*} [Group 𝔊] [Finite 𝔊] {f : ℕ} {Γ : Type} [Field Γ] [Finite Γ]
    {t u : 𝔊} {K D P Y W F J J₀ C : Subgroup 𝔊} {φ : ↥K →* SL(2, Γ)}
    (c : E2Ctx f Γ t u K D P Y W F J J₀ C φ) :
    (K ⊔ Kᵍ[t] = ⁅K, K⁆ ⊔ (⁅K, K⁆)ᵍ[t] ∧ ⁅K, K⁆ ⊓ (⁅K, K⁆)ᵍ[t] = ⊥ ∧
      ⁅⁅K, K⁆, (⁅K, K⁆)ᵍ[t]⁆ = ⊥ ∧ Nonempty (↥(⁅K, K⁆) ≃* ↥C)) ∧
    (D = zc (Kᵍ[t]) ⊔ (zc (Kᵍ[t]))ᵍ[t] ∧ zc (Kᵍ[t]) ⊓ (zc (Kᵍ[t]))ᵍ[t] = ⊥ ∧
      Nat.card ↥(zc (Kᵍ[t])) = (2 ^ f) ^ 8 ∧ ⁅K, K⁆ ⊓ D = zc (Kᵍ[t]) ∧ K = ⁅K, K⁆ ⊔ D) := by
  refine ⟨⟨c.N_eq_K'_sup, c.K'_inf_K't, c.comm_K'_K't, c.K'_mulEquiv_C⟩, ?_, ?_, c.card_zc_Kt,
    c.K'_inf_D, c.K_eq_commutator_sup⟩
  · rw [c.zc_Kt_conj]
    exact c.D_eq_zc_sup
  · rw [c.zc_Kt_conj, inf_comm]
    exact c.zc_inf_zc_Kt

end E2Ctx

section BarGlue

variable {G : Type*} [Group G] {A : Subgroup G}

open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient in
theorem mem_bar_iff' {X : Subgroup G} (x : normalizer (A : Set G)) :
    proj A x ∈ bar A X ↔ ∃ a ∈ A, (x : G) * a ∈ X := by
  constructor
  · rintro ⟨y, hy, e⟩
    have h1 := proj_eq_proj_iff.1 e.symm
    refine ⟨(x : G)⁻¹ * y, h1, ?_⟩
    have := mem_subgroupOf.1 hy
    simpa using this
  · rintro ⟨a, ha, hxa⟩
    refine ⟨⟨x * a, mul_mem x.2 (le_normalizer ha)⟩, mem_subgroupOf.2 hxa, ?_⟩
    rw [proj_eq_proj_iff]
    have : ((x : G) * a)⁻¹ * x = a⁻¹ := by group
    show ((x : G) * a)⁻¹ * x ∈ A
    rw [this]
    exact inv_mem ha

open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient in
theorem bar_conjg {X : Subgroup G} {g : G} (hg : g ∈ normalizer (A : Set G)) :
    bar A (Xᵍ[g]) = (bar A X)ᵍ[proj A ⟨g, hg⟩] := by
  ext y'
  obtain ⟨y, rfl⟩ := proj_surjective y'
  rw [mem_bar_iff', mem_conjg_iff, ← map_inv, ← map_mul, ← map_mul, mem_bar_iff']
  constructor
  · rintro ⟨a, ha, h⟩
    rw [mem_conjg_iff] at h
    refine ⟨g * a * g⁻¹, (mem_normalizer_iff.1 hg a).1 ha, ?_⟩
    simp only [coe_mul, coe_inv]
    have e : g * y * g⁻¹ * (g * a * g⁻¹) = g * ((y : G) * a) * g⁻¹ := by group
    rw [e]
    exact h
  · rintro ⟨a', ha', h⟩
    refine ⟨g⁻¹ * a' * g, ?_, ?_⟩
    · have := (mem_normalizer_iff.1 (inv_mem hg) a').1 ha'
      simpa using this
    · rw [mem_conjg_iff]
      simp only [coe_mul, coe_inv] at h
      have e : g * ((y : G) * (g⁻¹ * a' * g)) * g⁻¹ = g * y * g⁻¹ * a' := by group
      rw [e]
      exact h

open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient in
theorem bar_sup {X Y : Subgroup G} (hX : X ≤ normalizer (A : Set G))
    (hY : Y ≤ normalizer (A : Set G)) : bar A (X ⊔ Y) = bar A X ⊔ bar A Y := by
  unfold bar
  rw [Subgroup.subgroupOf_sup hX hY, Subgroup.map_sup]

open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient in
theorem eq_of_bar_eq {X Y : Subgroup G} (hAX : A ≤ X) (hXN : X ≤ normalizer (A : Set G))
    (hAY : A ≤ Y) (hYN : Y ≤ normalizer (A : Set G)) (h : bar A X = bar A Y) : X = Y := by
  rw [← lift_bar hAX hXN, ← lift_bar hAY hYN, h]

open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient in
theorem card_bar_mul' [Finite G] {X : Subgroup G} (hXN : X ≤ normalizer (A : Set G)) :
    Nat.card (bar A X) * Nat.card ↥(A ⊓ X) = Nat.card X := by
  have h1 := card_bar_mul (X := A ⊔ X) le_sup_left (sup_le le_normalizer hXN)
  have h2 : bar A (A ⊔ X) = bar A X := ProductN1HatAux.bar_sup_left hXN
  rw [h2] at h1
  have h3 := Common.card_sup_mul_card_inf_eq (A := A) (B := X) hXN
  have hpos : 0 < Nat.card A := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc Nat.card A * (Nat.card (bar A X) * Nat.card ↥(A ⊓ X))
      = (Nat.card (bar A X) * Nat.card A) * Nat.card ↥(A ⊓ X) := by ring
    _ = Nat.card ↥(A ⊔ X) * Nat.card ↥(A ⊓ X) := by rw [h1]
    _ = Nat.card A * Nat.card X := h3

open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient in
theorem exists_bar_hom {X Z : Subgroup G} (hAZ : A ≤ Z) (hZX : Z ≤ X)
    (hXN : X ≤ normalizer (A : Set G)) {T : Type*} [Group T] {φ : ↥X →* T}
    (hφ : Function.Surjective φ) (hker : φ.ker = Z.subgroupOf X) :
    ∃ φ' : ↥(bar A X) →* T, Function.Surjective φ' ∧
      φ'.ker = (bar A Z).subgroupOf (bar A X) := by
  have hAX : A ≤ X := hAZ.trans hZX
  let π : ↥X →* ↥(bar A X) :=
    ((proj A).comp (Subgroup.inclusion hXN)).codRestrict (bar A X) (fun x => proj_mem_bar x.2)
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨z, hz, hzy⟩ := y.2
    exact ⟨⟨z.1, mem_subgroupOf.1 hz⟩, Subtype.ext hzy⟩
  have hπker : ∀ x, π x = 1 ↔ (x : G) ∈ A := fun x => by
    have : π x = 1 ↔ proj A (Subgroup.inclusion hXN x) = 1 := by
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    rw [this]
    exact proj_eq_one_iff
  have hle : π.ker ≤ φ.ker := by
    intro x hx
    rw [hker, mem_subgroupOf]
    exact hAZ ((hπker x).1 (MonoidHom.mem_ker.1 hx))
  set φ' : ↥(bar A X) →* T := (MonoidHom.liftOfSurjective π hπ) ⟨φ, hle⟩ with hφ'def
  have hcomp : ∀ x : ↥X, φ' (π x) = φ x := fun x => by
    simp [φ']
  refine ⟨φ', ?_, ?_⟩
  · intro s
    obtain ⟨x, rfl⟩ := hφ s
    exact ⟨π x, hcomp x⟩
  · ext y
    obtain ⟨x, rfl⟩ := hπ y
    rw [MonoidHom.mem_ker, hcomp, Subgroup.mem_subgroupOf]
    have h1 : ((π x : ↥(bar A X)) : Bar A) = proj A (Subgroup.inclusion hXN x) := rfl
    rw [h1, mem_bar_iff hAZ, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    rfl

end BarGlue

section GlueData

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem series_le (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaV₁ d t ≤ yamadaY₂ d t ∧ yamadaY₂ d t ≤ yamadaW₃ d t ∧ yamadaW₃ d t ≤ yamadaF₄ d t ∧
      yamadaF₄ d t ≤ yamadaP d t := by
  obtain ⟨hZ1, hZ2, hZ3, hZ4⟩ := S5_upperCentralSeries_P h d hlay
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hZ1, ← hZ2]
    exact Subgroup.map_mono (Subgroup.upperCentralSeries_mono _ (by norm_num))
  · rw [← hZ2, ← hZ3]
    exact Subgroup.map_mono (Subgroup.upperCentralSeries_mono _ (by norm_num))
  · rw [← hZ3, ← hZ4]
    exact Subgroup.map_mono (Subgroup.upperCentralSeries_mono _ (by norm_num))
  · rw [← hZ4]
    exact Subgroup.map_subtype_le _

theorem F₄_le_D₅ (d : TrialityD4Data L (2 ^ f)) : yamadaF₄ d t ≤ yamadaD₅ d t :=
  Setup.yamadaF₄_le_yamadaD₅_PA d

theorem P_le_normalizer_V₁ (d : TrialityD4Data L (2 ^ f)) :
    yamadaP d t ≤ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) :=
  fun x hx => centralizer_le_normalizer _ (yamadaP_le_centralizer_yamadaV₁ d t hx)

theorem normalizer_D₅_le_normalizer_V₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    normalizer ((yamadaD₅ d t : Subgroup G) : Set G) ≤
      normalizer ((yamadaV₁ d t : Subgroup G) : Set G) := fun g hg => by
  have hy := h.l6Hyps d hlay
  have h525 : ⁅yamadaD₅ d t, yamadaD₅ d t⁆ = yamadaV₁ d t :=
    (h.yamada_5_25 d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593 hy.h5101 hy.h5102 hy.h59e
      hy.h520 hy.h5221 hy.h521).1
  have := Setup.normalizer_le_normalizer_commutator_C8 (yamadaD₅ d t) hg
  rwa [h525] at this

theorem nOneBar_normal (d : TrialityD4Data L (2 ^ f)) (t : G) : (nOneBar d t).Normal := by
  haveI hN : (xBar d t).Normal := Subgroup.normalClosure_normal
  constructor
  intro x hx g
  obtain ⟨y, hy, rfl⟩ := hx
  let σ : ↥(xBar d t) ≃* ↥(xBar d t) := (MulAut.conjNormal g : MulAut ↥(xBar d t))
  have hchar : (CFSG.perfectResidual ↥(xBar d t)).Characteristic := inferInstance
  have key : ∀ y : ↥(xBar d t), y ∈ CFSG.perfectResidual ↥(xBar d t) ↔
      σ y ∈ CFSG.perfectResidual ↥(xBar d t) := fun y => by
    have := Subgroup.ext_iff.1 (hchar.fixed σ) y
    rw [Subgroup.mem_comap] at this
    exact this.symm
  refine ⟨σ y, (key y).1 hy, ?_⟩
  simp [σ]

theorem kBar_le_nOneBar (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) : kBar d t ≤ nOneBar d t := by
  obtain ⟨-, -, ⟨⟨e⟩, -⟩, -⟩ := D1_centralizer_tbar h d hp
  have hSL : Group.IsPerfect SL(2, d.Γ) := by
    refine CFSG.ClassicalInvolution.sl2_isPerfect ?_
    rw [d.card_Γ]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hp.two_le
      _ ≤ (2 ^ f) ^ 3 := Nat.le_self_pow (by norm_num) _
  have hperf : Group.IsPerfect ↥(kBar d t) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidualOf _ _ hperf
    subset_normalClosure

theorem pBar_le_nOneBar (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) : pBar d t ≤ nOneBar d t := by
  have hn := nOneBar_normal d t
  have hk : kBar d t ≤ nOneBar d t := kBar_le_nOneBar h d hp
  have hj : jSixBar d t ≤ nOneBar d t := (ProductN1HatAux.jSixBar_le_kBar d).trans hk
  calc pBar d t = ⁅pBar d t, jSixBar d t⁆ := ProductN1HatAux.pBar_eq_commutator h d hp
    _ ≤ nOneBar d t := by
      rw [commutator_le]
      intro x _ y hy
      rw [commutatorElement_def]
      exact mul_mem (hn.conj_mem y (hj hy) x) (inv_mem (hj hy))

theorem P_le_nOne (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    yamadaP d t ≤ nOne d t := by
  intro x hx
  have hxN : x ∈ normalizer (yamadaD₅ d t : Set G) :=
    (h.yamadaP_le_normalizer_yamadaD₅ d hp.layer) hx
  exact NormalizerQuotient.mem_lift_of_proj_mem (x := ⟨x, hxN⟩)
    (pBar_le_nOneBar h d hp (NormalizerQuotient.proj_mem_bar hx))

theorem V₁_le_D₅ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaV₁ d t ≤ yamadaD₅ d t :=
  (series_le h d hlay).1.trans ((series_le h d hlay).2.1.trans
    ((series_le h d hlay).2.2.1.trans (F₄_le_D₅ d)))

theorem normalizer_P_le_series (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {g : G} (hg : g ∈ normalizer ((yamadaP d t : Subgroup G) : Set G)) :
    g ∈ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) ∧
      g ∈ normalizer ((yamadaY₂ d t : Subgroup G) : Set G) ∧
      g ∈ normalizer ((yamadaW₃ d t : Subgroup G) : Set G) ∧
      g ∈ normalizer ((yamadaF₄ d t : Subgroup G) : Set G) := by
  obtain ⟨hZ1, hZ2, hZ3, hZ4⟩ := S5_upperCentralSeries_P h d hlay
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := mem_normalizer_map_upperCentralSeries hg 1
    rwa [hZ1] at this
  · have := mem_normalizer_map_upperCentralSeries hg 2
    rwa [hZ2] at this
  · have := mem_normalizer_map_upperCentralSeries hg 3
    rwa [hZ3] at this
  · have := mem_normalizer_map_upperCentralSeries hg 4
    rwa [hZ4] at this

theorem K₁_le_nOne {d : TrialityD4Data L (2 ^ f)} {K₁ : Subgroup G} (hK₁ : IsN1Factor d t K₁) :
    K₁ ≤ nOne d t := hK₁.sup_eq ▸ le_sup_left

theorem K₁t_le_nOne {d : TrialityD4Data L (2 ^ f)} {K₁ : Subgroup G} (hK₁ : IsN1Factor d t K₁) :
    K₁ᵍ[t] ≤ nOne d t := hK₁.sup_eq ▸ le_sup_right

theorem nOne_le_normalizer_D₅ (d : TrialityD4Data L (2 ^ f)) :
    nOne d t ≤ normalizer ((yamadaD₅ d t : Subgroup G) : Set G) :=
  NormalizerQuotient.lift_le_normalizer _

theorem normalizer_D₅_le_normalizer_nOne (d : TrialityD4Data L (2 ^ f)) :
    normalizer ((yamadaD₅ d t : Subgroup G) : Set G) ≤
      normalizer ((nOne d t : Subgroup G) : Set G) := fun g hg => by
  refine mem_normalizer_fintype fun x hx => ?_
  obtain ⟨hxN, hx'⟩ := NormalizerQuotient.mem_lift_iff.1 hx
  have hgxg : g * x * g⁻¹ ∈ normalizer ((yamadaD₅ d t : Subgroup G) : Set G) :=
    mul_mem (mul_mem hg hxN) (inv_mem hg)
  refine NormalizerQuotient.mem_lift_iff.2 ⟨hgxg, ?_⟩
  have e : NormalizerQuotient.proj (yamadaD₅ d t) ⟨g * x * g⁻¹, hgxg⟩ =
      NormalizerQuotient.proj (yamadaD₅ d t) ⟨g, hg⟩ *
        NormalizerQuotient.proj (yamadaD₅ d t) ⟨x, hxN⟩ *
          (NormalizerQuotient.proj (yamadaD₅ d t) ⟨g, hg⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [e]
  exact (nOneBar_normal d t).conj_mem _ hx' _

theorem V₁_le_K₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d)
    {K₁ : Subgroup G} (hK₁ : IsN1Factor d t K₁) : yamadaV₁ d t ≤ K₁ :=
  (V₁_le_D₅ h d hlay).trans hK₁.D₅_le

theorem K₁_le_normalizer_V₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {K₁ : Subgroup G} (hK₁ : IsN1Factor d t K₁) :
    K₁ ≤ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) := fun x hx =>
  normalizer_D₅_le_normalizer_V₁ h d hlay (nOne_le_normalizer_D₅ d (K₁_le_nOne hK₁ hx))

theorem K₁t_le_normalizer_V₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {K₁ : Subgroup G} (hK₁ : IsN1Factor d t K₁) :
    K₁ᵍ[t] ≤ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) := fun x hx =>
  normalizer_D₅_le_normalizer_V₁ h d hlay (nOne_le_normalizer_D₅ d (K₁t_le_nOne hK₁ hx))

theorem cLV_le_normalizer_D₅ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    cLV d ≤ normalizer ((yamadaD₅ d t : Subgroup G) : Set G) := by
  rintro _ ⟨l, hl, rfl⟩
  exact (h.coe_mem_normalizer_yamadaD₅_C9 d (h.yamada_5_6_1 d hlay)
    (Subgroup.centralizer_le_normalizer _ hl)).2.2

theorem cLV_le_normalizer_V₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    cLV d ≤ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) := by
  rintro _ ⟨l, hl, rfl⟩
  exact (h.coe_mem_normalizer_yamadaD₅_C9 d (h.yamada_5_6_1 d hlay)
    (Subgroup.centralizer_le_normalizer _ hl)).2.1

theorem cLV_le_nOne (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d) :
    cLV d ≤ nOne d t := by
  intro x hx
  exact NormalizerQuotient.mem_lift_of_proj_mem (x := ⟨x, cLV_le_normalizer_D₅ h d hp.layer hx⟩)
    (kBar_le_nOneBar h d hp (NormalizerQuotient.proj_mem_bar hx))

theorem uG_mem_cLV (d : TrialityD4Data L (2 ^ f)) : uG d ∈ cLV d := by
  refine ⟨d.u, ?_, rfl⟩
  rw [d.centralizer_V_eq]
  exact mem_sup_right d.u_mem_leviShort

theorem uG_mem_normalizer_V₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : uG d ∈ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) :=
  cLV_le_normalizer_V₁ h d hlay (uG_mem_cLV d)

theorem uG_not_mem_normalizer_P (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hp : ProductHyp h d) :
    uG d ∉ normalizer ((yamadaP d t : Subgroup G) : Set G) := by
  intro hu
  have hS := (T4_series_free h d hp).2.2.2.2.2.2.1
  apply d.u_not_mem_B
  rw [← d.normalizer_S]
  refine mem_normalizer_fintype fun s hs => ?_
  have hsP : ((s : L) : G) ∈ yamadaP d t ⊓ centralizer ({t} : Set G) := by
    rw [hS]
    exact ⟨s, hs, rfl⟩
  have h1 : uG d * ((s : L) : G) * (uG d)⁻¹ ∈ yamadaP d t :=
    (mem_normalizer_iff.1 hu _).1 hsP.1
  have h2 : uG d * ((s : L) : G) * (uG d)⁻¹ ∈ centralizer ({t} : Set G) := by
    have hL : ∀ l : L, (l : G) ∈ centralizer ({t} : Set G) := fun l => h.L_le_centralizer l.2
    exact mul_mem (mul_mem (hL d.u) (hL s)) (inv_mem (hL d.u))
  have h3 : uG d * ((s : L) : G) * (uG d)⁻¹ ∈ d.S.map L.subtype := by
    rw [← hS]
    exact ⟨h1, h2⟩
  obtain ⟨s', hs', hs'e⟩ := h3
  have : s' = d.u * s * d.u⁻¹ := Subtype.ext (by simpa using hs'e)
  rw [← this]
  exact hs'

end GlueData



section BarSeries

variable {G : Type*} [Group G] {A P Z Z' : Subgroup G}

theorem bar_self : NormalizerQuotient.bar A A = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨y, hy, rfl⟩
  rw [Subgroup.mem_bot]
  exact NormalizerQuotient.proj_eq_one_iff.2 (mem_subgroupOf.1 hy)

theorem bar_mem_series (hAZ : A ≤ Z) (hAZ' : A ≤ Z') (hAP : A ≤ P)
    (hPN : P ≤ normalizer (A : Set G)) (hZ'P : Z' ≤ P)
    (hiff : ∀ x ∈ P, x ∈ Z' ↔ ∀ p ∈ P, x * p * x⁻¹ * p⁻¹ ∈ Z) :
    ∀ x : NormalizerQuotient.Bar A, x ∈ NormalizerQuotient.bar A Z' ↔
      x ∈ NormalizerQuotient.bar A P ∧ ∀ p ∈ NormalizerQuotient.bar A P,
        x * p * x⁻¹ * p⁻¹ ∈ NormalizerQuotient.bar A Z := by
  intro x
  obtain ⟨x', rfl⟩ := NormalizerQuotient.proj_surjective x
  rw [NormalizerQuotient.mem_bar_iff hAZ', NormalizerQuotient.mem_bar_iff hAP]
  constructor
  · intro hx
    refine ⟨hZ'P hx, fun p hp => ?_⟩
    obtain ⟨p', rfl⟩ := NormalizerQuotient.proj_surjective p
    rw [NormalizerQuotient.mem_bar_iff hAP] at hp
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, NormalizerQuotient.mem_bar_iff hAZ]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using (hiff x' (hZ'P hx)).1 hx p' hp
  · rintro ⟨hxP, hall⟩
    refine (hiff x' hxP).2 fun p hp => ?_
    have h1 := hall (NormalizerQuotient.proj A ⟨p, hPN hp⟩)
      (NormalizerQuotient.proj_mem_bar hp)
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
      NormalizerQuotient.mem_bar_iff hAZ] at h1
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h1

theorem comm_eq_one_iff {M : Type*} [Group M] {x p : M} :
    x * p * x⁻¹ * p⁻¹ = 1 ↔ x * p = p * x := by
  constructor
  · intro h
    calc x * p = (x * p * x⁻¹ * p⁻¹) * (p * x) := by group
      _ = p * x := by rw [h, one_mul]
  · intro h
    rw [h]
    group

end BarSeries


section SectionJ

variable {𝔊 : Type*} [Group 𝔊] [Finite 𝔊]

theorem section_J_inv {t : 𝔊} {W Y U J : Subgroup 𝔊} {m : ℕ}
    (htt : t * t = 1) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hWs : ∀ x ∈ W, x * x = 1)
    (hYW : Y ≤ W) (hWt : Wᵍ[t] = W) (hYt : Yᵍ[t] = Y)
    (hJt : J ≤ centralizer ({t} : Set 𝔊)) (hJW : J ≤ normalizer (W : Set 𝔊))
    (hJY : J ≤ normalizer (Y : Set 𝔊)) (hYU : Y ≤ U) (hUW : U ≤ W)
    (hU : ∀ x ∈ W, x ∈ U ↔ t * x * t⁻¹ * x⁻¹ ∈ Y)
    (hUcard : Nat.card U = Nat.card Y * m) (hfree : Nat.card W * Nat.card Y = Nat.card U ^ 2)
    (hirr : ∀ Z : Subgroup 𝔊, Y ≤ Z → Z ≤ U → J ≤ normalizer (Z : Set 𝔊) → Z = Y ∨ Z = U) :
    ∀ X : Subgroup 𝔊, Y ≤ X → X ≤ W → J ≤ normalizer (X : Set 𝔊) →
      X = Y ∨ Nat.card X = Nat.card Y * m ∨ X = W := by
  intro X hYX hXW hJX
  have hWt' : ∀ x ∈ W, t * x * t⁻¹ ∈ W := fun x hx => by
    have : x ∈ Wᵍ[t] := by rw [hWt]; exact hx
    exact mem_conjg_iff.1 this
  have hYt' : ∀ y ∈ Y, t * y * t⁻¹ ∈ Y := fun y hy => by
    have : y ∈ Yᵍ[t] := by rw [hYt]; exact hy
    exact mem_conjg_iff.1 this
  have hJc : ∀ j ∈ J, j * t = t * j := fun j hj => mem_centralizer_singleton_iff.1 (hJt hj)
  let νh : ↥W →* ↥W := MonoidHom.mk' (fun x => ⟨(x : 𝔊) * (t * (x : 𝔊) * t⁻¹),
    mul_mem x.2 (hWt' x x.2)⟩) (by
      intro a b
      apply Subtype.ext
      have h1 := hWc (b : 𝔊) b.2 (t * (a : 𝔊) * t⁻¹) (hWt' a a.2)
      show ((a : 𝔊) * b) * (t * ((a : 𝔊) * b) * t⁻¹) =
        ((a : 𝔊) * (t * (a : 𝔊) * t⁻¹)) * ((b : 𝔊) * (t * (b : 𝔊) * t⁻¹))
      calc ((a : 𝔊) * b) * (t * ((a : 𝔊) * b) * t⁻¹)
          = a * (b * (t * a * t⁻¹)) * (t * b * t⁻¹) := by group
        _ = a * ((t * a * t⁻¹) * b) * (t * b * t⁻¹) := by rw [h1]
        _ = _ := by group)
  have hνx : ∀ x : ↥W, ((νh x : ↥W) : 𝔊) = (x : 𝔊) * (t * (x : 𝔊) * t⁻¹) := fun x => rfl
  have hYn : (Y.subgroupOf W).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    have := hWc (g : 𝔊) g.2 n n.2
    have e : (g : 𝔊) * n * (g : 𝔊)⁻¹ = n := by rw [this]; group
    simpa [e] using hn⟩
  let φ : ↥W →* (↥W ⧸ Y.subgroupOf W) := (QuotientGroup.mk' (Y.subgroupOf W)).comp νh
  have hkerφ : φ.ker = U.subgroupOf W := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    show (QuotientGroup.mk' (Y.subgroupOf W)) (νh x) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf, hνx, hU x x.2]
    have hxx := hWs x x.2
    have hc := hWc (x : 𝔊) x.2 (t * (x : 𝔊) * t⁻¹) (hWt' x x.2)
    have hxi : (x : 𝔊)⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
    constructor
    · intro hy
      have e : t * (x : 𝔊) * t⁻¹ * (x : 𝔊)⁻¹ = (x : 𝔊) * (t * (x : 𝔊) * t⁻¹) := by
        rw [hxi]; exact hc.symm
      rw [e]
      exact hy
    · intro hy
      have e : t * (x : 𝔊) * t⁻¹ * (x : 𝔊)⁻¹ = (x : 𝔊) * (t * (x : 𝔊) * t⁻¹) := by
        rw [hxi]; exact hc.symm
      rw [← e]
      exact hy
  set X' := X.subgroupOf W with hX'
  have hcardX' : Nat.card X' = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXW).toEquiv
  have hc1 := card_map_mul_card_inf_ker φ X'
  have hX'ker : X' ⊓ φ.ker = (X ⊓ U).subgroupOf W := by
    rw [hkerφ]
    ext x
    simp only [Subgroup.mem_inf, mem_subgroupOf, hX']
  have hcard1 : Nat.card ↥(X' ⊓ φ.ker) = Nat.card ↥(X ⊓ U) := by
    rw [hX'ker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hXW)).toEquiv
  set S := X'.map νh with hS
  have hmap : X'.map φ = S.map (QuotientGroup.mk' (Y.subgroupOf W)) := by
    rw [hS, Subgroup.map_map]
  have hc2 := card_map_mul_card_inf_ker (QuotientGroup.mk' (Y.subgroupOf W)) (S ⊔ Y.subgroupOf W)
  rw [QuotientGroup.ker_mk', inf_eq_right.2 le_sup_right] at hc2
  have hmap2 : (S ⊔ Y.subgroupOf W).map (QuotientGroup.mk' (Y.subgroupOf W)) =
      S.map (QuotientGroup.mk' (Y.subgroupOf W)) := by
    have hY'bot : (Y.subgroupOf W).map (QuotientGroup.mk' (Y.subgroupOf W)) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [Subgroup.map_sup, hY'bot, sup_bot_eq]
  rw [hmap2] at hc2
  set Nu : Subgroup 𝔊 := S.map W.subtype with hNu
  set X₂ : Subgroup 𝔊 := (S ⊔ Y.subgroupOf W).map W.subtype with hX₂
  have hX₂eq : X₂ = Nu ⊔ Y := by
    rw [hX₂, Subgroup.map_sup, hNu, Subgroup.map_subgroupOf_eq_of_le hYW]
  have hcardX₂ : Nat.card X₂ = Nat.card ↥(S ⊔ Y.subgroupOf W) :=
    Subgroup.card_map_of_injective W.subtype_injective
  have hcardY' : Nat.card (Y.subgroupOf W) = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYW).toEquiv
  have hmem_Nu : ∀ z, z ∈ Nu ↔ ∃ x ∈ X, z = x * (t * x * t⁻¹) := by
    intro z
    constructor
    · rintro ⟨w, ⟨x', hx', rfl⟩, rfl⟩
      exact ⟨x', mem_subgroupOf.1 hx', rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨νh ⟨x, hXW hx⟩, ⟨⟨x, hXW hx⟩, mem_subgroupOf.2 hx, rfl⟩, rfl⟩
  have hNuU : Nu ≤ U := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := (hmem_Nu z).1 hz
    have hxW := hXW hx
    have hνW : x * (t * x * t⁻¹) ∈ W := mul_mem hxW (hWt' x hxW)
    rw [hU _ hνW]
    have hc := hWc x hxW (t * x * t⁻¹) (hWt' x hxW)
    have e : t * (x * (t * x * t⁻¹)) * t⁻¹ * (x * (t * x * t⁻¹))⁻¹ = 1 := by
      calc t * (x * (t * x * t⁻¹)) * t⁻¹ * (x * (t * x * t⁻¹))⁻¹
          = (t * x * t⁻¹) * (t * (t * x * t⁻¹) * t⁻¹) * (x * (t * x * t⁻¹))⁻¹ := by group
        _ = (t * x * t⁻¹) * x * (x * (t * x * t⁻¹))⁻¹ := by rw [conj_conj_of_mul_self htt]
        _ = (x * (t * x * t⁻¹)) * (x * (t * x * t⁻¹))⁻¹ := by rw [hc]
        _ = 1 := by group
    rw [e]
    exact one_mem Y
  have hX₂U : X₂ ≤ U := by
    rw [hX₂eq]
    exact sup_le hNuU hYU
  have hYX₂ : Y ≤ X₂ := by
    rw [hX₂eq]
    exact le_sup_right
  have hjt : ∀ j ∈ J, ∀ x : 𝔊, t * (j * x * j⁻¹) * t⁻¹ = j * (t * x * t⁻¹) * j⁻¹ := by
    intro j hj x
    have hj1 := hJc j hj
    calc t * (j * x * j⁻¹) * t⁻¹ = (t * j) * x * (t * j)⁻¹ := by group
      _ = (j * t) * x * (j * t)⁻¹ := by rw [hj1]
      _ = j * (t * x * t⁻¹) * j⁻¹ := by group
  have hJNu : J ≤ normalizer (Nu : Set 𝔊) := fun j hj => by
    refine mem_normalizer_fintype fun z hz => ?_
    obtain ⟨x, hx, rfl⟩ := (hmem_Nu z).1 hz
    refine (hmem_Nu _).2 ⟨j * x * j⁻¹, (mem_normalizer_iff.1 (hJX hj) x).1 hx, ?_⟩
    have e : j * (x * (t * x * t⁻¹)) * j⁻¹ = (j * x * j⁻¹) * (t * (j * x * j⁻¹) * t⁻¹) := by
      rw [hjt j hj x]
      group
    exact e
  have hJX₂ : J ≤ normalizer (X₂ : Set 𝔊) := by
    rw [hX₂eq]
    exact fun j hj => Common.mem_normalizer_sup (hJNu hj) (hJY hj)
  have hJU : J ≤ normalizer (U : Set 𝔊) := fun j hj => by
    refine mem_normalizer_fintype fun x hx => ?_
    rw [SetLike.mem_coe] at hx ⊢
    have hxW : x ∈ W := hUW hx
    have hjxW : j * x * j⁻¹ ∈ W := (mem_normalizer_iff.1 (hJW hj) x).1 hxW
    rw [hU _ hjxW]
    have hxY := (hU x hxW).1 hx
    have e : t * (j * x * j⁻¹) * t⁻¹ * (j * x * j⁻¹)⁻¹ = j * (t * x * t⁻¹ * x⁻¹) * j⁻¹ := by
      rw [hjt j hj x]
      group
    rw [e]
    exact (mem_normalizer_iff.1 (hJY hj) _).1 hxY
  have hJX₁ : J ≤ normalizer ((X ⊓ U : Subgroup 𝔊) : Set 𝔊) := fun j hj =>
    Common.mem_normalizer_inf (hJX hj) (hJU hj)
  have hb : 0 < Nat.card Y := Nat.card_pos
  have hkey : Nat.card X * Nat.card Y = Nat.card ↥(X ⊓ U) * Nat.card X₂ := by
    have h1 : Nat.card ↥(X'.map φ) * Nat.card ↥(X ⊓ U) = Nat.card X := by
      rw [← hcard1, ← hcardX']
      exact hc1
    have h2 : Nat.card ↥(S.map (QuotientGroup.mk' (Y.subgroupOf W))) * Nat.card Y =
        Nat.card X₂ := by
      rw [hcardX₂, ← hcardY']
      exact hc2
    rw [hmap] at h1
    calc Nat.card X * Nat.card Y
        = (Nat.card ↥(S.map (QuotientGroup.mk' (Y.subgroupOf W))) * Nat.card ↥(X ⊓ U)) *
            Nat.card Y := by rw [h1]
      _ = Nat.card ↥(X ⊓ U) * (Nat.card ↥(S.map (QuotientGroup.mk' (Y.subgroupOf W))) *
            Nat.card Y) := by ring
      _ = Nat.card ↥(X ⊓ U) * Nat.card X₂ := by rw [h2]
  have hX₁ : Y ≤ X ⊓ U := le_inf hYX hYU
  rcases hirr _ hX₁ inf_le_right hJX₁ with h1 | h1 <;>
    rcases hirr _ hYX₂ hX₂U hJX₂ with h2 | h2
  · left
    rw [h1, h2] at hkey
    have : Nat.card X = Nat.card Y := Nat.eq_of_mul_eq_mul_right hb hkey
    exact (Subgroup.eq_of_le_of_card_ge hYX this.le).symm
  · right
    left
    rw [h1, h2] at hkey
    have : Nat.card X * Nat.card Y = Nat.card U * Nat.card Y := by rw [hkey, mul_comm]
    rw [Nat.eq_of_mul_eq_mul_right hb this, hUcard]
  · right
    left
    rw [h1, h2] at hkey
    rw [Nat.eq_of_mul_eq_mul_right hb hkey, hUcard]
  · right
    right
    rw [h1, h2] at hkey
    have : Nat.card X * Nat.card Y = Nat.card W * Nat.card Y := by rw [hkey, hfree, pow_two]
    have := Nat.eq_of_mul_eq_mul_right hb this
    exact Subgroup.eq_of_le_of_card_ge hXW this.ge

end SectionJ


section LevelIrr

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem W_irr {T : Subgroup X} (hYT : d.Y ≤ T) (hTW : T ≤ d.W)
    (hJT : d.J ≤ normalizer (T : Set X)) : T = d.Y ∨ T = d.W := by
  by_cases hTY : T ≤ d.Y
  · exact Or.inl (le_antisymm hTY hYT)
  · right
    obtain ⟨w, hwT, hwY⟩ := Set.not_subset.1 hTY
    obtain ⟨a, n, hn, hw⟩ := d.mem_W_iff.1 (hTW hwT)
    have hx4 : d.x₄ a ∈ T := by
      have : d.x₄ a = w * n⁻¹ := by rw [← hw]; group
      rw [this]
      exact mul_mem hwT (inv_mem (hYT hn))
    have ha1 : d.x₄ a ≠ 1 := fun h => hwY (by rw [← hw, h, one_mul]; exact hn)
    have hall : ∀ b, d.x₄ b ∈ T := by
      intro b
      by_cases hb : d.x₄ b = 1
      · rw [hb]
        exact one_mem T
      · obtain ⟨j, ⟨hjJ₂, hj⟩, -⟩ := d.yamada_three_five_five.2.2.1.2 (d.x₄ a) (d.x₄_mem_U₄ a)
          ha1 (d.x₄ b) (d.x₄_mem_U₄ b) hb
        have hJ₂J : d.J₂ ≤ d.J := inf_le_left
        have hjJ : j ∈ d.J := hJ₂J hjJ₂
        have := (mem_normalizer_iff.1 (hJT hjJ) _).1 hx4
        rwa [hj] at this
    refine le_antisymm hTW (fun g hg => ?_)
    obtain ⟨b, n', hn', rfl⟩ := d.mem_W_iff.1 hg
    exact mul_mem (hall b) (hYT hn')

theorem F_irr {T : Subgroup X} (hWT : d.W ≤ T) (hTF : T ≤ d.F)
    (hJT : d.J ≤ normalizer (T : Set X)) : T = d.W ∨ T = d.F := by
  by_cases hTW : T ≤ d.W
  · exact Or.inl (le_antisymm hTW hWT)
  · right
    obtain ⟨w, hwT, hwW⟩ := Set.not_subset.1 hTW
    obtain ⟨a, n, hn, hw⟩ := d.mem_F_iff.1 (hTF hwT)
    have hx3 : d.x₃ a ∈ T := by
      have : d.x₃ a = w * n⁻¹ := by rw [← hw]; group
      rw [this]
      exact mul_mem hwT (inv_mem (hWT hn))
    have ha1 : d.x₃ a ≠ 1 := fun h => hwW (by rw [← hw, h, one_mul]; exact hn)
    have hall : ∀ b, d.x₃ b ∈ T := by
      intro b
      by_cases hb : d.x₃ b = 1
      · rw [hb]
        exact one_mem T
      · obtain ⟨j, ⟨hjJ₂, hj⟩, -⟩ := d.yamada_three_five_five.2.1.2 (d.x₃ a) (d.x₃_mem_U₃ a)
          ha1 (d.x₃ b) (d.x₃_mem_U₃ b) hb
        have hJ₂J : d.J₂ ≤ d.J := inf_le_left
        have hjJ : j ∈ d.J := hJ₂J hjJ₂
        have := (mem_normalizer_iff.1 (hJT hjJ) _).1 hx3
        rwa [hj] at this
    refine le_antisymm hTF (fun g hg => ?_)
    obtain ⟨b, n', hn', rfl⟩ := d.mem_F_iff.1 hg
    exact mul_mem (hall b) (hWT hn')

end LevelIrr


section ConjLeNormalizer

variable {G : Type*} [Group G]

theorem conjg_le_normalizer {A X : Subgroup G} {g : G} (hg : g ∈ normalizer (A : Set G))
    (hX : X ≤ normalizer (A : Set G)) : Xᵍ[g] ≤ normalizer (A : Set G) := by
  intro x hx
  have h1 : g * x * g⁻¹ ∈ normalizer (A : Set G) := hX (mem_conjg_iff.1 hx)
  have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
  rw [e]
  exact mul_mem (mul_mem (inv_mem hg) h1) hg


end ConjLeNormalizer

section LiftGlue

variable {G : Type*} [Group G] [Finite G] {A : Subgroup G}

open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient in
theorem lift_sup' (Y₁ Y₂ : Subgroup (Bar A)) : lift (Y₁ ⊔ Y₂) = lift Y₁ ⊔ lift Y₂ := by
  apply eq_of_bar_eq (le_lift _) (lift_le_normalizer _) (le_sup_of_le_left (le_lift _))
    (sup_le (lift_le_normalizer _) (lift_le_normalizer _))
  rw [bar_lift, bar_sup (lift_le_normalizer _) (lift_le_normalizer _), bar_lift, bar_lift]

open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient in
theorem lift_inf' (Y₁ Y₂ : Subgroup (Bar A)) : lift (Y₁ ⊓ Y₂) = lift Y₁ ⊓ lift Y₂ := by
  apply eq_of_bar_eq (le_lift _) (lift_le_normalizer _) (le_inf (le_lift _) (le_lift _))
    (inf_le_left.trans (lift_le_normalizer _))
  rw [bar_lift, ProductN1HatAux.bar_inf (le_lift _) (le_lift _), bar_lift, bar_lift]

open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient in
theorem lift_conjg' (Y : Subgroup (Bar A)) {g : G} (hg : g ∈ normalizer (A : Set G)) :
    lift (Yᵍ[proj A ⟨g, hg⟩]) = (lift Y)ᵍ[g] := by
  have hA : A ≤ (lift Y)ᵍ[g] := by
    calc A = Aᵍ[g] := (conjg_eq_of_mem_normalizer hg).symm
      _ ≤ (lift Y)ᵍ[g] := conjg_mono (le_lift Y) g
  apply eq_of_bar_eq (le_lift _) (lift_le_normalizer _) hA
    (conjg_le_normalizer hg (lift_le_normalizer Y))
  rw [bar_lift, bar_conjg hg, bar_lift]

open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient in
theorem lift_bot' : lift (⊥ : Subgroup (Bar A)) = A := by
  ext g
  rw [mem_lift_iff]
  constructor
  · rintro ⟨hg, h1⟩
    rw [Subgroup.mem_bot] at h1
    exact proj_eq_one_iff.1 h1
  · intro hg
    exact ⟨le_normalizer hg, by rw [Subgroup.mem_bot]; exact proj_eq_one_iff.2 hg⟩

noncomputable def barHom {X : Subgroup G} (hXN : X ≤ normalizer (A : Set G)) :
    ↥X →* ↥(NormalizerQuotient.bar A X) :=
  ((NormalizerQuotient.proj A).comp (Subgroup.inclusion hXN)).codRestrict
    (NormalizerQuotient.bar A X) (fun x => NormalizerQuotient.proj_mem_bar x.2)

theorem barHom_surjective {X : Subgroup G} (hXN : X ≤ normalizer (A : Set G)) :
    Function.Surjective (barHom hXN) := by
  intro y
  obtain ⟨z, hz, hzy⟩ := y.2
  exact ⟨⟨z.1, mem_subgroupOf.1 hz⟩, Subtype.ext hzy⟩

theorem ker_barHom {X : Subgroup G} (hXN : X ≤ normalizer (A : Set G)) :
    (barHom hXN).ker = A.subgroupOf X := by
  ext x
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  constructor
  · intro h
    have : NormalizerQuotient.proj A (Subgroup.inclusion hXN x) = 1 := congrArg Subtype.val h
    exact NormalizerQuotient.proj_eq_one_iff.1 this
  · intro h
    exact Subtype.ext (NormalizerQuotient.proj_eq_one_iff.2 h)

noncomputable def barEquiv {X : Subgroup G} (hXN : X ≤ normalizer (A : Set G))
    [(A.subgroupOf X).Normal] : (↥X ⧸ A.subgroupOf X) ≃* ↥(NormalizerQuotient.bar A X) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_barHom hXN).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (barHom hXN) (barHom_surjective hXN))

theorem centerMod_eq_lift_zc {X : Subgroup G} :
    centerMod A X = NormalizerQuotient.lift (zc (NormalizerQuotient.bar A X)) := by
  unfold centerMod upperCenterMod
  rw [Subgroup.upperCentralSeries_one]
  congr 1
  ext x
  simp only [zc, Subgroup.mem_map, Subgroup.mem_inf, SetLike.mem_coe, mem_centralizer_iff,
    Subgroup.coe_subtype, Subgroup.mem_center_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, fun z hz => congrArg Subtype.val (hy ⟨z, hz⟩)⟩
  · rintro ⟨hx, hc⟩
    exact ⟨⟨x, hx⟩, fun w => Subtype.ext (hc w w.2), rfl⟩

end LiftGlue


section PCoreGlue

variable {G : Type*} [Group G]

theorem pCoreOf_eq_of_quotient {B E : Subgroup G} {T : Type*} [Group T] [IsSimpleGroup T]
    (hT : ¬ IsPGroup 2 T) (φ : ↥B →* T) (hφ : Function.Surjective φ)
    (hker : φ.ker = E.subgroupOf B) (hE2 : IsPGroup 2 E) (hEB : E ≤ B) :
    pCoreOf 2 B = E := by
  apply le_antisymm
  · have hP := CFSG.pCore_normal (p := 2) (G := ↥B)
    have hP2 : IsPGroup 2 (CFSG.pCore 2 ↥B) := CFSG.pCore_isPGroup (p := 2) (G := ↥B)
    have hN : ((CFSG.pCore 2 ↥B).map φ).Normal := Subgroup.Normal.map hP φ hφ
    haveI := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥B).map φ) with h | h
    · have hle : CFSG.pCore 2 ↥B ≤ φ.ker := (Subgroup.map_eq_bot_iff _).1 h
      rw [hker] at hle
      rintro _ ⟨x, hx, rfl⟩
      exact mem_subgroupOf.1 (hle hx)
    · exfalso
      apply hT
      have h3 := hP2.map φ
      rw [h] at h3
      exact h3.of_equiv (Subgroup.topEquiv : ↥(⊤ : Subgroup T) ≃* T)
  · have hEn : (E.subgroupOf B).Normal := hker ▸ MonoidHom.normal_ker φ
    have hE2' : IsPGroup 2 (E.subgroupOf B) := hE2.comap_subtype
    have hle : E.subgroupOf B ≤ CFSG.pCore 2 ↥B := le_sSup ⟨hEn, hE2'⟩
    intro x hx
    have : (⟨x, hEB hx⟩ : ↥B) ∈ E.subgroupOf B := hx
    exact ⟨⟨x, hEB hx⟩, hle this, rfl⟩

end PCoreGlue

section SL2NotPGroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ}

theorem not_isPGroup_sl2 (d : TrialityD4Data L (2 ^ f)) (hf : 2 ≤ f) :
    ¬ IsPGroup 2 SL(2, d.Γ) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 h
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, d.card_Γ] at hn
  set Q : ℕ := (2 ^ f) ^ 3 with hQ
  have hQe : Even Q := by
    rw [hQ]
    exact (Nat.even_pow' (by omega)).2 ((Nat.even_pow' (by omega)).2 even_two)
  have hQ4 : 4 ≤ Q := by
    rw [hQ]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ (2 ^ f) ^ 3 := Nat.le_self_pow (by norm_num) _
  have hodd : Odd (Q ^ 2 - 1) :=
    Nat.Even.sub_odd (Nat.one_le_pow _ _ (by omega)) (hQe.pow_of_ne_zero (by norm_num)) odd_one
  have hdvd : Q ^ 2 - 1 ∣ 2 ^ n := ⟨Q, by rw [← hn]; ring⟩
  have hcop : Nat.Coprime (Q ^ 2 - 1) (2 ^ n) :=
    Nat.Coprime.pow_right n ((Nat.coprime_two_right.2 hodd))
  have h1 : Q ^ 2 - 1 = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
  have : 16 ≤ Q ^ 2 := by nlinarith
  omega

end SL2NotPGroup

section Fields

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))

local notation "𝔟[" X "]" => NormalizerQuotient.bar (yamadaV₁ d t) X
local notation "𝔭" => NormalizerQuotient.proj (yamadaV₁ d t)

@[expose] noncomputable def tB : NormalizerQuotient.Bar (yamadaV₁ d t) :=
  NormalizerQuotient.proj (yamadaV₁ d t) ⟨t, h.t_mem_normalizer_yamadaV₁ d⟩

@[expose] noncomputable def uB (hlay : h.LayerHyp d) : NormalizerQuotient.Bar (yamadaV₁ d t) :=
  NormalizerQuotient.proj (yamadaV₁ d t) ⟨uG d, uG_mem_normalizer_V₁ h d hlay⟩

theorem J_le_normalizer_V₁ (hlay : h.LayerHyp d) :
    d.J.map L.subtype ≤ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) := by
  rintro _ ⟨j, hj, rfl⟩
  exact (normalizer_P_le_series h d hlay (J_le_normalizer_P h d hlay hj)).1

theorem jZeroG_le_J : jZeroG d ≤ d.J.map L.subtype := map_mono d.J₀_le_J

theorem tB_mul_tB : tB h d * tB h d = 1 := by
  unfold tB
  rw [← map_mul]
  have : (⟨t, h.t_mem_normalizer_yamadaV₁ d⟩ * ⟨t, h.t_mem_normalizer_yamadaV₁ d⟩ :
      normalizer ((yamadaV₁ d t : Subgroup G) : Set G)) = 1 := Subtype.ext h.t_mul_t
  rw [this, map_one]

theorem uB_mul_uB (hlay : h.LayerHyp d) : uB h d hlay * uB h d hlay = 1 := by
  unfold uB
  rw [← map_mul]
  have : (⟨uG d, uG_mem_normalizer_V₁ h d hlay⟩ * ⟨uG d, uG_mem_normalizer_V₁ h d hlay⟩ :
      normalizer ((yamadaV₁ d t : Subgroup G) : Set G)) = 1 := by
    apply Subtype.ext
    show uG d * uG d = 1
    have := congrArg (fun x : L => (x : G)) d.u_mul_self
    simpa using this
  rw [this, map_one]

theorem tB_comm_uB (hlay : h.LayerHyp d) : tB h d * uB h d hlay = uB h d hlay * tB h d := by
  unfold tB uB
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  show t * uG d = uG d * t
  exact (mem_centralizer_singleton_iff.1 (h.L_le_centralizer d.u.2)).symm


variable {K₁ : Subgroup G}

theorem bar_conjg_t (X : Subgroup G) :
    𝔟[Xᵍ[t]] = (𝔟[X])ᵍ[tB h d] :=
  bar_conjg (h.t_mem_normalizer_yamadaV₁ d)

theorem bar_conjg_u (hlay : h.LayerHyp d) (X : Subgroup G) :
    𝔟[Xᵍ[uG d]] = (𝔟[X])ᵍ[uB h d hlay] :=
  bar_conjg (uG_mem_normalizer_V₁ h d hlay)

theorem e2f_K_inf (hp : ProductHyp h d) (hK₁ : IsN1Factor d t K₁) :
    𝔟[K₁] ⊓ (𝔟[K₁])ᵍ[tB h d] = 𝔟[yamadaD₅ d t] := by
  have hlay := hp.layer
  rw [← bar_conjg_t h d, ← ProductN1HatAux.bar_inf (V₁_le_K₁ h d hlay hK₁) ?_, hK₁.inf_eq]
  exact (V₁_le_D₅ h d hlay).trans (hK₁.inf_eq ▸ inf_le_right)

theorem e2f_comm_le (hp : ProductHyp h d) (hK₁ : IsN1Factor d t K₁) :
    ⁅𝔟[K₁], (𝔟[K₁])ᵍ[tB h d]⁆ ≤ 𝔟[yamadaD₅ d t] := by
  have hlay := hp.layer
  rw [← bar_conjg_t h d, ← ProductN1HatAux.bar_commutator (K₁_le_normalizer_V₁ h d hlay hK₁)
    (K₁t_le_normalizer_V₁ h d hlay hK₁)]
  exact NormalizerQuotient.bar_mono hK₁.comm_le

theorem e2f_phi (hp : ProductHyp h d) (hK₁ : IsN1Factor d t K₁) :
    ∃ φ' : ↥(𝔟[K₁]) →* SL(2, d.Γ), Function.Surjective φ' ∧
      φ'.ker = (𝔟[yamadaD₅ d t]).subgroupOf (𝔟[K₁]) := by
  obtain ⟨φ, hφ, hker⟩ := hK₁.iso
  exact exists_bar_hom (V₁_le_D₅ h d hp.layer) hK₁.D₅_le (K₁_le_normalizer_V₁ h d hp.layer hK₁)
    hφ hker

theorem e2f_D_comm (hp : ProductHyp h d) :
    ∀ x ∈ 𝔟[yamadaD₅ d t], ∀ y ∈ 𝔟[yamadaD₅ d t], x * y = y * x := by
  have hlay := hp.layer
  intro x hx y hy
  obtain ⟨x', rfl⟩ := NormalizerQuotient.proj_surjective x
  obtain ⟨y', rfl⟩ := NormalizerQuotient.proj_surjective y
  have hx' : (x' : G) ∈ yamadaD₅ d t := (NormalizerQuotient.mem_bar_iff (V₁_le_D₅ h d hlay) x').1 hx
  have hy' : (y' : G) ∈ yamadaD₅ d t := (NormalizerQuotient.mem_bar_iff (V₁_le_D₅ h d hlay) y').1 hy
  exact (commutator_mem_iff_proj y'.2 x'.2).2
    (h.commutator_mem_yamadaV₁_of_mem_yamadaD₅_PA d hlay hy' hx')

theorem e2f_D_sq (hp : ProductHyp h d) : ∀ x ∈ 𝔟[yamadaD₅ d t], x * x = 1 := by
  have hlay := hp.layer
  intro x hx
  obtain ⟨x', rfl⟩ := NormalizerQuotient.proj_surjective x
  have hx' : (x' : G) ∈ yamadaD₅ d t := (NormalizerQuotient.mem_bar_iff (V₁_le_D₅ h d hlay) x').1 hx
  rw [← map_mul, NormalizerQuotient.proj_eq_one_iff]
  exact h.mul_self_mem_yamadaV₁_of_mem_yamadaD₅_PA d hlay hx'

theorem e2f_P_le_N (hp : ProductHyp h d) (hK₁ : IsN1Factor d t K₁) :
    𝔟[yamadaP d t] ≤ 𝔟[K₁] ⊔ (𝔟[K₁])ᵍ[tB h d] := by
  have hlay := hp.layer
  rw [← bar_conjg_t h d, ← bar_sup (K₁_le_normalizer_V₁ h d hlay hK₁)
    (K₁t_le_normalizer_V₁ h d hlay hK₁), ← hK₁.sup_eq]
  exact NormalizerQuotient.bar_mono (P_le_nOne h d hp)

theorem e2f_P_conj (hp : ProductHyp h d) : (𝔟[yamadaP d t])ᵍ[tB h d] = 𝔟[yamadaP d t] := by
  rw [← bar_conjg_t h d, conjg_eq_of_mem_normalizer (h.t_mem_normalizer_yamadaP d hp.layer)]

theorem e2f_Y_conj (hp : ProductHyp h d) : (𝔟[yamadaY₂ d t])ᵍ[tB h d] = 𝔟[yamadaY₂ d t] := by
  rw [← bar_conjg_t h d, conjg_eq_of_mem_normalizer (h.t_mem_normalizer_yamadaY₂ d)]

theorem e2f_W_conj (hp : ProductHyp h d) : (𝔟[yamadaW₃ d t])ᵍ[tB h d] = 𝔟[yamadaW₃ d t] := by
  rw [← bar_conjg_t h d, conjg_eq_of_mem_normalizer
    (normalizer_P_le_series h d hp.layer (h.t_mem_normalizer_yamadaP d hp.layer)).2.2.1]


theorem card_V₁' (hlay : h.LayerHyp d) : Nat.card (yamadaV₁ d t) = (2 ^ f) ^ 2 :=
  (h.yamada_5_6_2 d hlay).2.1

theorem card_bar_pow (hlay : h.LayerHyp d) {X : Subgroup G} (hAX : yamadaV₁ d t ≤ X)
    (hXN : X ≤ normalizer ((yamadaV₁ d t : Subgroup G) : Set G)) {k : ℕ}
    (hk : Nat.card X = (2 ^ f) ^ (k + 2)) : Nat.card (𝔟[X]) = (2 ^ f) ^ k := by
  have h1 := NormalizerQuotient.card_bar_mul hAX hXN
  rw [hk, card_V₁' h d hlay] at h1
  have hpos : 0 < (2 ^ f) ^ 2 := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1]
  ring

theorem mem_series_succ_iff {P Xn Xn1 : Subgroup G} {n : ℕ}
    (hn : (Subgroup.upperCentralSeries ↥P n).map P.subtype = Xn)
    (hn1 : (Subgroup.upperCentralSeries ↥P (n + 1)).map P.subtype = Xn1) :
    ∀ x ∈ P, x ∈ Xn1 ↔ ∀ p ∈ P, x * p * x⁻¹ * p⁻¹ ∈ Xn := by
  intro x hx
  have hmemn : ∀ y : ↥P, y ∈ Subgroup.upperCentralSeries ↥P n ↔ (y : G) ∈ Xn := fun y => by
    rw [← hn]
    exact (Subgroup.mem_map_iff_mem P.subtype_injective).symm
  have hmemn1 : ∀ y : ↥P, y ∈ Subgroup.upperCentralSeries ↥P (n + 1) ↔ (y : G) ∈ Xn1 := fun y => by
    rw [← hn1]
    exact (Subgroup.mem_map_iff_mem P.subtype_injective).symm
  have key : x ∈ Xn1 ↔ ∀ y : ↥P, ⁅(⟨x, hx⟩ : ↥P), y⁆ ∈ Subgroup.upperCentralSeries ↥P n := by
    rw [← Subgroup.mem_upperCentralSeries_succ_iff]
    exact (hmemn1 ⟨x, hx⟩).symm
  rw [key]
  constructor
  · intro hall p hp
    have := (hmemn _).1 (hall ⟨p, hp⟩)
    simpa [commutatorElement_def] using this
  · intro hall y
    apply (hmemn _).2
    have := hall y y.2
    simpa [commutatorElement_def] using this


theorem series_mem_iff (hlay : h.LayerHyp d) :
    (∀ x ∈ yamadaP d t, x ∈ yamadaY₂ d t ↔ ∀ p ∈ yamadaP d t, x * p * x⁻¹ * p⁻¹ ∈ yamadaV₁ d t) ∧
    (∀ x ∈ yamadaP d t, x ∈ yamadaW₃ d t ↔ ∀ p ∈ yamadaP d t, x * p * x⁻¹ * p⁻¹ ∈ yamadaY₂ d t) ∧
    (∀ x ∈ yamadaP d t, x ∈ yamadaF₄ d t ↔
      ∀ p ∈ yamadaP d t, x * p * x⁻¹ * p⁻¹ ∈ yamadaW₃ d t) := by
  obtain ⟨hZ1, hZ2, hZ3, hZ4⟩ := S5_upperCentralSeries_P h d hlay
  exact ⟨mem_series_succ_iff hZ1 hZ2, mem_series_succ_iff hZ2 hZ3, mem_series_succ_iff hZ3 hZ4⟩

theorem e2f_mem_Y (hlay : h.LayerHyp d) : ∀ x : NormalizerQuotient.Bar (yamadaV₁ d t),
    x ∈ 𝔟[yamadaY₂ d t] ↔ x ∈ 𝔟[yamadaP d t] ∧ ∀ p ∈ 𝔟[yamadaP d t], x * p = p * x := by
  have hs := series_le h d hlay
  have := bar_mem_series (A := yamadaV₁ d t) (Z := yamadaV₁ d t) le_rfl hs.1
    (hs.1.trans (hs.2.1.trans (hs.2.2.1.trans hs.2.2.2)))
    (P_le_normalizer_V₁ d) (hs.2.1.trans (hs.2.2.1.trans hs.2.2.2)) (series_mem_iff h d hlay).1
  intro x
  rw [this x, bar_self]
  simp only [Subgroup.mem_bot, comm_eq_one_iff]

theorem e2f_mem_W (hlay : h.LayerHyp d) : ∀ x : NormalizerQuotient.Bar (yamadaV₁ d t),
    x ∈ 𝔟[yamadaW₃ d t] ↔ x ∈ 𝔟[yamadaP d t] ∧
      ∀ p ∈ 𝔟[yamadaP d t], x * p * x⁻¹ * p⁻¹ ∈ 𝔟[yamadaY₂ d t] := by
  have hs := series_le h d hlay
  exact bar_mem_series (hs.1) (hs.1.trans hs.2.1)
    (hs.1.trans (hs.2.1.trans (hs.2.2.1.trans hs.2.2.2)))
    (P_le_normalizer_V₁ d) (hs.2.2.1.trans hs.2.2.2) (series_mem_iff h d hlay).2.1

theorem e2f_mem_F (hlay : h.LayerHyp d) : ∀ x : NormalizerQuotient.Bar (yamadaV₁ d t),
    x ∈ 𝔟[yamadaF₄ d t] ↔ x ∈ 𝔟[yamadaP d t] ∧
      ∀ p ∈ 𝔟[yamadaP d t], x * p * x⁻¹ * p⁻¹ ∈ 𝔟[yamadaW₃ d t] := by
  have hs := series_le h d hlay
  exact bar_mem_series (hs.1.trans hs.2.1) (hs.1.trans (hs.2.1.trans hs.2.2.1))
    (hs.1.trans (hs.2.1.trans (hs.2.2.1.trans hs.2.2.2)))
    (P_le_normalizer_V₁ d) hs.2.2.2 (series_mem_iff h d hlay).2.2


theorem uG_inv_eq (d : TrialityD4Data L (2 ^ f)) : (uG d)⁻¹ = uG d := by
  apply inv_eq_of_mul_eq_one_right
  have := congrArg (fun x : L => (x : G)) d.u_mul_self
  simpa using this

theorem D₅_eq_sup_W₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaD₅ d t = yamadaW₃ d t ⊔ (yamadaW₃ d t)ᵍ[uG d] ∧
      yamadaW₃ d t ⊓ (yamadaW₃ d t)ᵍ[uG d] = yamadaV₁ d t := by
  have hy := h.l6Hyps d hlay
  obtain ⟨-, -, -, h1, h2, -, -⟩ := h.yamada_5_25 d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592
    hy.h593 hy.h5101 hy.h5102 hy.h59e hy.h520 hy.h5221 hy.h521
  have e : (yamadaW₃ d t)ᵍ[uG d] =
      (yamadaW₃ d t).map (MulAut.conj ((d.u : L) : G)).toMonoidHom := by
    rw [uG_inv_eq d]
  rw [e]
  exact ⟨h1, h2⟩

theorem e2f_F_le_D : 𝔟[yamadaF₄ d t] ≤ 𝔟[yamadaD₅ d t] :=
  NormalizerQuotient.bar_mono (F₄_le_D₅ d)

theorem e2f_card_D (hp : ProductHyp h d) : Nat.card (𝔟[yamadaD₅ d t]) = (2 ^ f) ^ 16 :=
  card_bar_pow h d hp.layer (V₁_le_D₅ h d hp.layer)
    (fun x hx => P_le_normalizer_V₁ d (yamadaD₅_le_yamadaP d t hx))
    (T4_series_free h d hp).2.2.2.2.2.2.2.1

theorem e2f_card_P' (hp : ProductHyp h d) : Nat.card (𝔟[yamadaP d t]) = (2 ^ f) ^ 22 := by
  have hs := series_le h d hp.layer
  exact card_bar_pow h d hp.layer (hs.1.trans (hs.2.1.trans (hs.2.2.1.trans hs.2.2.2)))
    (P_le_normalizer_V₁ d) (T4_series_free h d hp).2.2.2.2.2.2.2.2.2.1

theorem e2f_card_P (hp : ProductHyp h d) :
    Nat.card (𝔟[yamadaP d t]) = Nat.card (𝔟[yamadaD₅ d t]) * (2 ^ f) ^ 6 := by
  rw [e2f_card_P' h d hp, e2f_card_D h d hp]
  ring

theorem e2f_card_Y (hp : ProductHyp h d) : Nat.card (𝔟[yamadaY₂ d t]) = (2 ^ f) ^ 2 := by
  have hs := series_le h d hp.layer
  exact card_bar_pow h d hp.layer hs.1
    (fun x hx => P_le_normalizer_V₁ d ((hs.2.1.trans (hs.2.2.1.trans hs.2.2.2)) hx))
    (h.yamada_5_9_2 d hp.layer).2.1

theorem e2f_card_W (hp : ProductHyp h d) : Nat.card (𝔟[yamadaW₃ d t]) = (2 ^ f) ^ 8 := by
  have hs := series_le h d hp.layer
  exact card_bar_pow h d hp.layer (hs.1.trans hs.2.1)
    (fun x hx => P_le_normalizer_V₁ d ((hs.2.2.1.trans hs.2.2.2) hx))
    (h.yamada_5_21 d hp.layer).2.2

theorem e2f_card_F (hp : ProductHyp h d) : Nat.card (𝔟[yamadaF₄ d t]) = (2 ^ f) ^ 14 := by
  have hs := series_le h d hp.layer
  exact card_bar_pow h d hp.layer (hs.1.trans (hs.2.1.trans hs.2.2.1))
    (fun x hx => P_le_normalizer_V₁ d (hs.2.2.2 hx))
    (h.card_yamadaF₄ d hp.layer)

theorem e2f_u_mem_N (hp : ProductHyp h d) (hK₁ : IsN1Factor d t K₁) :
    uB h d hp.layer ∈ 𝔟[K₁] ⊔ (𝔟[K₁])ᵍ[tB h d] := by
  have hlay := hp.layer
  rw [← bar_conjg_t h d, ← bar_sup (K₁_le_normalizer_V₁ h d hlay hK₁)
    (K₁t_le_normalizer_V₁ h d hlay hK₁), ← hK₁.sup_eq]
  exact (NormalizerQuotient.mem_bar_iff ((V₁_le_K₁ h d hlay hK₁).trans (K₁_le_nOne hK₁)) _).2
    (cLV_le_nOne h d hp (uG_mem_cLV d))

theorem e2f_u_not_mem (hp : ProductHyp h d) :
    uB h d hp.layer ∉ normalizer ((𝔟[yamadaP d t] : Subgroup _) : Set _) := by
  have hlay := hp.layer
  intro hu
  apply uG_not_mem_normalizer_P h d hp
  refine mem_normalizer_fintype fun x hx => ?_
  have hxN := P_le_normalizer_V₁ d hx
  have h1 : 𝔭 ⟨x, hxN⟩ ∈ 𝔟[yamadaP d t] := NormalizerQuotient.proj_mem_bar hx
  have h2 := (mem_normalizer_iff.1 hu _).1 h1
  have huN := uG_mem_normalizer_V₁ h d hlay
  have hxu : uG d * x * (uG d)⁻¹ ∈ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) :=
    mul_mem (mul_mem huN hxN) (inv_mem huN)
  have e : uB h d hlay * 𝔭 ⟨x, hxN⟩ * (uB h d hlay)⁻¹ = 𝔭 ⟨uG d * x * (uG d)⁻¹, hxu⟩ := by
    unfold uB
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [e] at h2
  have hs := series_le h d hlay
  have hVP : yamadaV₁ d t ≤ yamadaP d t := hs.1.trans (hs.2.1.trans (hs.2.2.1.trans hs.2.2.2))
  exact (NormalizerQuotient.mem_bar_iff hVP _).1 h2


theorem W₃_le_normalizer_V₁ (hlay : h.LayerHyp d) :
    yamadaW₃ d t ≤ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) := fun x hx =>
  P_le_normalizer_V₁ d ((series_le h d hlay).2.2.1.trans (series_le h d hlay).2.2.2 hx)

theorem e2f_D_eq_sup (hlay : h.LayerHyp d) :
    𝔟[yamadaD₅ d t] = 𝔟[yamadaW₃ d t] ⊔ (𝔟[yamadaW₃ d t])ᵍ[uB h d hlay] := by
  rw [← bar_conjg_u h d hlay, ← bar_sup (W₃_le_normalizer_V₁ h d hlay)
    (conjg_le_normalizer (uG_mem_normalizer_V₁ h d hlay) (W₃_le_normalizer_V₁ h d hlay)),
    ← (D₅_eq_sup_W₃ h d hlay).1]

theorem e2f_W_inf (hlay : h.LayerHyp d) :
    𝔟[yamadaW₃ d t] ⊓ (𝔟[yamadaW₃ d t])ᵍ[uB h d hlay] = ⊥ := by
  have hV : yamadaV₁ d t ≤ yamadaW₃ d t := (series_le h d hlay).1.trans (series_le h d hlay).2.1
  have hVu : yamadaV₁ d t ≤ (yamadaW₃ d t)ᵍ[uG d] := by
    rw [← (D₅_eq_sup_W₃ h d hlay).2]
    exact inf_le_right
  rw [← bar_conjg_u h d hlay, ← ProductN1HatAux.bar_inf hV hVu, (D₅_eq_sup_W₃ h d hlay).2,
    bar_self]

theorem J_le_normalizer_P' (hlay : h.LayerHyp d) :
    d.J.map L.subtype ≤ normalizer ((yamadaP d t : Subgroup G) : Set G) := by
  rintro _ ⟨j, hj, rfl⟩
  exact J_le_normalizer_P h d hlay hj

theorem e2f_J_odd (hlay : h.LayerHyp d) : Odd (Nat.card (𝔟[d.J.map L.subtype])) := by
  have hJN := J_le_normalizer_V₁ h d hlay
  have h1 := card_bar_mul' hJN
  have hJodd : Odd (Nat.card (d.J.map L.subtype)) := by
    rw [Subgroup.card_map_of_injective L.subtype_injective, d.card_J]
    have he : Even (2 ^ f) := d.even_q
    have ha : Odd (2 ^ f - 1) := Nat.Even.sub_odd Nat.one_le_two_pow he odd_one
    have hb : Odd ((2 ^ f) ^ 3 - 1) :=
      Nat.Even.sub_odd (Nat.one_le_pow _ _ (by positivity)) (he.pow_of_ne_zero (by norm_num))
        odd_one
    exact ha.mul hb
  rw [← h1] at hJodd
  exact (Nat.odd_mul.1 hJodd).1

theorem e2f_J_cen_t : 𝔟[d.J.map L.subtype] ≤ centralizer ({tB h d} : Set _) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [mem_centralizer_singleton_iff]
  obtain ⟨j, hj, hjy⟩ := mem_subgroupOf.1 hy
  have hc : (y : G) * t = t * y := by
    rw [← hjy]
    exact mem_centralizer_singleton_iff.1 (h.L_le_centralizer j.2)
  unfold tB
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hc

theorem e2f_J_nor_N (hp : ProductHyp h d) (hK₁ : IsN1Factor d t K₁) :
    𝔟[d.J.map L.subtype] ≤ normalizer ((𝔟[K₁] ⊔ (𝔟[K₁])ᵍ[tB h d] : Subgroup _) : Set _) := by
  have hlay := hp.layer
  rw [← bar_conjg_t h d, ← bar_sup (K₁_le_normalizer_V₁ h d hlay hK₁)
    (K₁t_le_normalizer_V₁ h d hlay hK₁), ← hK₁.sup_eq]
  refine NormalizerQuotient.bar_le_normalizer_bar
    ((V₁_le_K₁ h d hlay hK₁).trans (K₁_le_nOne hK₁)) ?_
  intro x hx
  exact normalizer_D₅_le_normalizer_nOne d ((E1_core h d hp).2.2 (J_le_normalizer_P' h d hlay hx))

theorem e2f_J_nor_P (hlay : h.LayerHyp d) :
    𝔟[d.J.map L.subtype] ≤ normalizer ((𝔟[yamadaP d t] : Subgroup _) : Set _) :=
  NormalizerQuotient.bar_le_normalizer_bar
    ((series_le h d hlay).1.trans ((series_le h d hlay).2.1.trans
      ((series_le h d hlay).2.2.1.trans (series_le h d hlay).2.2.2)))
    (J_le_normalizer_P' h d hlay)

theorem e2f_J_nor_Y (hlay : h.LayerHyp d) :
    𝔟[d.J.map L.subtype] ≤ normalizer ((𝔟[yamadaY₂ d t] : Subgroup _) : Set _) :=
  NormalizerQuotient.bar_le_normalizer_bar (series_le h d hlay).1
    (fun x hx => (normalizer_P_le_series h d hlay (J_le_normalizer_P' h d hlay hx)).2.1)

theorem e2f_J_nor_W (hlay : h.LayerHyp d) :
    𝔟[d.J.map L.subtype] ≤ normalizer ((𝔟[yamadaW₃ d t] : Subgroup _) : Set _) :=
  NormalizerQuotient.bar_le_normalizer_bar ((series_le h d hlay).1.trans (series_le h d hlay).2.1)
    (fun x hx => (normalizer_P_le_series h d hlay (J_le_normalizer_P' h d hlay hx)).2.2.1)

theorem e2f_J_nor_F (hlay : h.LayerHyp d) :
    𝔟[d.J.map L.subtype] ≤ normalizer ((𝔟[yamadaF₄ d t] : Subgroup _) : Set _) :=
  NormalizerQuotient.bar_le_normalizer_bar
    ((series_le h d hlay).1.trans ((series_le h d hlay).2.1.trans (series_le h d hlay).2.2.1))
    (fun x hx => (normalizer_P_le_series h d hlay (J_le_normalizer_P' h d hlay hx)).2.2.2)

theorem e2f_J₀_le_J : 𝔟[jZeroG d] ≤ 𝔟[d.J.map L.subtype] :=
  NormalizerQuotient.bar_mono (jZeroG_le_J d)

theorem e2f_J_conj_u (hlay : h.LayerHyp d) :
    ∀ j ∈ 𝔟[d.J.map L.subtype], uB h d hlay * j * (uB h d hlay)⁻¹ ∈ 𝔟[d.J.map L.subtype] := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨j, hj, hjy⟩ := mem_subgroupOf.1 hy
  have hu : uG d * (y : G) * (uG d)⁻¹ ∈ d.J.map L.subtype :=
    ⟨d.u * j * d.u⁻¹, d.conj_mem_J d.u_mem_weyl hj, by rw [← hjy]; simp [uG]⟩
  have huN := uG_mem_normalizer_V₁ h d hlay
  have hN : uG d * (y : G) * (uG d)⁻¹ ∈ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) :=
    mul_mem (mul_mem huN y.2) (inv_mem huN)
  refine ⟨⟨_, hN⟩, mem_subgroupOf.2 hu, ?_⟩
  unfold uB
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem e2f_J₀_conj_u (hlay : h.LayerHyp d) :
    ∀ j ∈ 𝔟[jZeroG d], uB h d hlay * j * (uB h d hlay)⁻¹ ∈ 𝔟[jZeroG d] := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨j, hj, hjy⟩ := mem_subgroupOf.1 hy
  have hu : uG d * (y : G) * (uG d)⁻¹ ∈ jZeroG d :=
    ⟨d.u * j * d.u⁻¹, (mem_normalizer_iff.1 d.u_mem_normalizer_J₀ j).1 hj,
      by rw [← hjy]; simp [uG]⟩
  have huN := uG_mem_normalizer_V₁ h d hlay
  have hN : uG d * (y : G) * (uG d)⁻¹ ∈ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) :=
    mul_mem (mul_mem huN y.2) (inv_mem huN)
  refine ⟨⟨_, hN⟩, mem_subgroupOf.2 hu, ?_⟩
  unfold uB
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl


theorem jZeroG_le_normalizer_V₁ (hlay : h.LayerHyp d) :
    jZeroG d ≤ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) :=
  (jZeroG_le_J d).trans (J_le_normalizer_V₁ h d hlay)

theorem e2f_J₀_cen_Y (hp : ProductHyp h d) :
    𝔟[yamadaY₂ d t] ≤ centralizer ((𝔟[jZeroG d] : Subgroup _) : Set _) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨j, hj, rfl⟩
  have hyc : (y : G) ∈ centralizer ((jZeroG d : Subgroup G) : Set G) :=
    (T5_J₀ h d hp).1 (mem_subgroupOf.1 hy)
  have := mem_centralizer_iff.1 hyc j (mem_subgroupOf.1 hj)
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext this

theorem e2f_W_inf_cen (hp : ProductHyp h d) :
    𝔟[yamadaW₃ d t] ⊓ centralizer ((𝔟[jZeroG d] : Subgroup _) : Set _) = 𝔟[yamadaY₂ d t] := by
  have hlay := hp.layer
  have hs := series_le h d hlay
  refine le_antisymm ?_ (le_inf (NormalizerQuotient.bar_mono hs.2.1) (e2f_J₀_cen_Y h d hp))
  intro x hx
  obtain ⟨hxW, hxc⟩ := mem_inf.1 hx
  obtain ⟨x', rfl⟩ := NormalizerQuotient.proj_surjective x
  have hVW : yamadaV₁ d t ≤ yamadaW₃ d t := hs.1.trans hs.2.1
  have hx'W : (x' : G) ∈ yamadaW₃ d t := (NormalizerQuotient.mem_bar_iff hVW x').1 hxW
  have hY₂N : (x' : G) ∈ normalizer ((yamadaY₂ d t : Subgroup G) : Set G) :=
    (normalizer_P_le_series h d hlay (le_normalizer (hs.2.2.1.trans hs.2.2.2 hx'W))).2.1
  have hmem : (x' : G) ∈ yamadaW₃ d t ⊓ centralizerMod (yamadaY₂ d t) (jZeroG d) := by
    refine mem_inf.2 ⟨hx'W, ?_⟩
    rw [mem_centralizerMod_iff]
    refine ⟨hY₂N, fun b hb hbN => ?_⟩
    have hbV : b ∈ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) :=
      jZeroG_le_normalizer_V₁ h d hlay hb
    have h1 := mem_centralizer_iff.1 hxc (𝔭 ⟨b, hbV⟩) (NormalizerQuotient.proj_mem_bar hb)
    have h2 := (commutator_mem_iff_proj x'.2 hbV).1 h1
    exact hs.1 h2
  rw [(T5_J₀ h d hp).2.1] at hmem
  exact (NormalizerQuotient.mem_bar_iff hs.1 x').2 hmem

theorem e2f_D_J₀_le_F (hp : ProductHyp h d) :
    ∀ x ∈ 𝔟[yamadaD₅ d t], ∀ j ∈ 𝔟[jZeroG d], x * j * x⁻¹ * j⁻¹ ∈ 𝔟[yamadaF₄ d t] := by
  have hlay := hp.layer
  have hs := series_le h d hlay
  intro x hx _ ⟨j', hj', hjj⟩
  obtain ⟨x', rfl⟩ := NormalizerQuotient.proj_surjective x
  subst hjj
  have hx' : (x' : G) ∈ yamadaD₅ d t :=
    (NormalizerQuotient.mem_bar_iff (V₁_le_D₅ h d hlay) x').1 hx
  have hj : (j' : G) ∈ jZeroG d := mem_subgroupOf.1 hj'
  have hjF : (j' : G) ∈ normalizer ((yamadaF₄ d t : Subgroup G) : Set G) :=
    (normalizer_P_le_series h d hlay (J_le_normalizer_P' h d hlay (jZeroG_le_J d hj))).2.2.2
  have h1 := ((mem_centralizerMod_iff.1 ((T5_J₀ h d hp).2.2.2.2.2.1 hx')).2 j' hj hjF)
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
    NormalizerQuotient.mem_bar_iff (hs.1.trans (hs.2.1.trans hs.2.2.1))]
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h1


theorem mem_normalizer_lift {Z : Subgroup (NormalizerQuotient.Bar (yamadaV₁ d t))} {g : G}
    (hg : g ∈ normalizer ((yamadaV₁ d t : Subgroup G) : Set G))
    (hZ : 𝔭 ⟨g, hg⟩ ∈ normalizer (Z : Set (NormalizerQuotient.Bar (yamadaV₁ d t)))) :
    g ∈ normalizer ((NormalizerQuotient.lift Z : Subgroup G) : Set G) := by
  refine mem_normalizer_fintype fun z hz => ?_
  rw [SetLike.mem_coe] at hz ⊢
  obtain ⟨hzN, hzZ⟩ := NormalizerQuotient.mem_lift_iff.1 hz
  have hgz : g * z * g⁻¹ ∈ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) :=
    mul_mem (mul_mem hg hzN) (inv_mem hg)
  refine NormalizerQuotient.mem_lift_iff.2 ⟨hgz, ?_⟩
  have e : 𝔭 ⟨g * z * g⁻¹, hgz⟩ = 𝔭 ⟨g, hg⟩ * 𝔭 ⟨z, hzN⟩ * (𝔭 ⟨g, hg⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [e]
  exact (mem_normalizer_iff.1 hZ _).1 hzZ

theorem free_card {A B : Subgroup G} (hF : FreeLifted t A B)
    (hcA : Nat.card A = Nat.card B * ((2 ^ f) ^ 3) ^ 2)
    (htt : t * t = 1) (htB : t ∈ normalizer (B : Set G)) :
    Nat.card ↥((A ⊓ centralizerMod B (zpowers t) : Subgroup G)) = Nat.card B * (2 ^ f) ^ 3 := by
  have hBA : B ≤ A := hF.1.le
  have hBX : B ≤ A ⊓ centralizerMod B (zpowers t) :=
    ProductToolboxAux.Core.le_inf_centralizerMod_zpowers hF.1 htt htB
  have h1 := Subgroup.relIndex_mul_card (H := B) (K := A)
  rw [inf_of_le_left hBA, hcA] at h1
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have h2 : B.relIndex A = ((2 ^ f) ^ 3) ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_right hBpos
    rw [h1]
    ring
  have h3 : B.relIndex (A ⊓ centralizerMod B (zpowers t)) = (2 ^ f) ^ 3 := by
    have := hF.2.1
    rw [IsFreeSection, h2] at this
    exact (Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) this).symm
  have h4 := Subgroup.relIndex_mul_card (H := B) (K := A ⊓ centralizerMod B (zpowers t))
  rw [inf_of_le_left hBX, h3] at h4
  rw [← h4]
  ring


theorem W₃_le_D₅ (hlay : h.LayerHyp d) : yamadaW₃ d t ≤ yamadaD₅ d t :=
  (series_le h d hlay).2.2.1.trans (F₄_le_D₅ d)

theorem F₄_le_normalizer_V₁ (hlay : h.LayerHyp d) :
    yamadaF₄ d t ≤ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) := fun x hx =>
  P_le_normalizer_V₁ d ((series_le h d hlay).2.2.2 hx)

theorem F₄_conj (hp : ProductHyp h d) : (𝔟[yamadaF₄ d t])ᵍ[tB h d] = 𝔟[yamadaF₄ d t] := by
  rw [← bar_conjg_t h d, conjg_eq_of_mem_normalizer (h.t_mem_normalizer_yamadaF₄ d hp.layer)]

@[expose] noncomputable def xtW (d : TrialityD4Data L (2 ^ f)) (t : G) : Subgroup G :=
  d.W.map L.subtype ⊔ yamadaY₂ d t

@[expose] noncomputable def xtF (d : TrialityD4Data L (2 ^ f)) (t : G) : Subgroup G :=
  d.F.map L.subtype ⊔ yamadaW₃ d t

theorem xtW_eq (hp : ProductHyp h d) :
    yamadaW₃ d t ⊓ centralizerMod (yamadaY₂ d t) (zpowers t) = xtW d t := by
  obtain ⟨-, -, hW₃C, -, -, -, -, -, -, -, -, -, f3, -⟩ := T4_series_free h d hp
  rw [f3.2.2, hW₃C]
  rfl

theorem xtF_eq (hp : ProductHyp h d) :
    yamadaF₄ d t ⊓ centralizerMod (yamadaW₃ d t) (zpowers t) = xtF d t := by
  obtain ⟨-, -, -, hF₄C, -, -, -, -, -, -, -, -, -, f4, -⟩ := T4_series_free h d hp
  rw [f4.2.2, hF₄C]
  rfl

theorem WL_le_W₃ (hp : ProductHyp h d) : d.W.map L.subtype ≤ yamadaW₃ d t := by
  obtain ⟨-, -, hW₃C, -⟩ := T4_series_free h d hp
  rw [← hW₃C]
  exact inf_le_left

theorem FL_le_F₄ (hp : ProductHyp h d) : d.F.map L.subtype ≤ yamadaF₄ d t := by
  obtain ⟨-, -, -, hF₄C, -⟩ := T4_series_free h d hp
  rw [← hF₄C]
  exact inf_le_left

theorem xtW_bounds (hp : ProductHyp h d) : yamadaY₂ d t ≤ xtW d t ∧ xtW d t ≤ yamadaW₃ d t :=
  ⟨le_sup_right, sup_le (WL_le_W₃ h d hp) (series_le h d hp.layer).2.1⟩

theorem xtF_bounds (hp : ProductHyp h d) : yamadaW₃ d t ≤ xtF d t ∧ xtF d t ≤ yamadaF₄ d t :=
  ⟨le_sup_right, sup_le (FL_le_F₄ h d hp) (series_le h d hp.layer).2.2.1⟩

theorem card_xtW (hp : ProductHyp h d) :
    Nat.card (xtW d t) = Nat.card (yamadaY₂ d t) * (2 ^ f) ^ 3 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, f3, -⟩ := T4_series_free h d hp
  rw [← xtW_eq h d hp]
  refine free_card f3 ?_ h.t_mul_t (h.t_mem_normalizer_yamadaY₂ d)
  rw [(h.yamada_5_21 d hp.layer).2.2, (h.yamada_5_9_2 d hp.layer).2.1]
  ring

theorem card_xtF (hp : ProductHyp h d) :
    Nat.card (xtF d t) = Nat.card (yamadaW₃ d t) * (2 ^ f) ^ 3 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, f4, -⟩ := T4_series_free h d hp
  rw [← xtF_eq h d hp]
  refine free_card f4 ?_ h.t_mul_t
    (normalizer_P_le_series h d hp.layer (h.t_mem_normalizer_yamadaP d hp.layer)).2.2.1
  rw [h.card_yamadaF₄ d hp.layer, (h.yamada_5_21 d hp.layer).2.2]
  ring


theorem barU_W (hp : ProductHyp h d) :
    ∀ x ∈ 𝔟[yamadaW₃ d t], x ∈ 𝔟[xtW d t] ↔
      tB h d * x * (tB h d)⁻¹ * x⁻¹ ∈ 𝔟[yamadaY₂ d t] := by
  have hlay := hp.layer
  have hs := series_le h d hlay
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, f3, -⟩ := T4_series_free h d hp
  have hVY : yamadaV₁ d t ≤ yamadaY₂ d t := hs.1
  have hVW : yamadaV₁ d t ≤ yamadaW₃ d t := hs.1.trans hs.2.1
  have htY : t ∈ normalizer ((yamadaY₂ d t : Subgroup G) : Set G) :=
    h.t_mem_normalizer_yamadaY₂ d
  have htN : t ∈ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) :=
    h.t_mem_normalizer_yamadaV₁ d
  intro x hx
  obtain ⟨x', rfl⟩ := NormalizerQuotient.proj_surjective x
  have hx'W : (x' : G) ∈ yamadaW₃ d t := (NormalizerQuotient.mem_bar_iff hVW x').1 hx
  have hx'Y : (x' : G) ∈ normalizer ((yamadaY₂ d t : Subgroup G) : Set G) :=
    (normalizer_P_le_series h d hlay (le_normalizer (hs.2.2.1.trans hs.2.2.2 hx'W))).2.1
  rw [NormalizerQuotient.mem_bar_iff (hVY.trans (xtW_bounds h d hp).1) x']
  have hcN : t * (x' : G) * t⁻¹ * (x' : G)⁻¹ ∈ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) :=
    mul_mem (mul_mem (mul_mem htN x'.2) (inv_mem htN)) (inv_mem x'.2)
  have hcomm : tB h d * 𝔭 x' * (tB h d)⁻¹ * (𝔭 x')⁻¹ =
      𝔭 ⟨t * (x' : G) * t⁻¹ * (x' : G)⁻¹, hcN⟩ := by
    unfold tB
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  rw [hcomm, NormalizerQuotient.mem_bar_iff hVY, ← xtW_eq h d hp,
    ProductToolboxAux.Core.mem_inf_centralizerMod_zpowers_iff f3.1 h.t_mul_t htY]
  constructor
  · rintro ⟨-, h1⟩
    have h2 := (mem_normalizer_iff.1 hx'Y _).1 h1
    have e : (x' : G) * ((x' : G)⁻¹ * (t * x' * t⁻¹)) * (x' : G)⁻¹ =
        t * (x' : G) * t⁻¹ * (x' : G)⁻¹ := by
      group
    rw [e] at h2
    exact h2
  · intro h1
    refine ⟨hx'W, ?_⟩
    have h1' : t * (x' : G) * t⁻¹ * (x' : G)⁻¹ ∈ yamadaY₂ d t := h1
    have h2 := (mem_normalizer_iff.1 (inv_mem hx'Y) _).1 h1'
    have e : (x' : G)⁻¹ * (t * (x' : G) * t⁻¹ * (x' : G)⁻¹) * (x' : G)⁻¹⁻¹ =
        (x' : G)⁻¹ * (t * x' * t⁻¹) := by
      group
    rw [e] at h2
    exact h2


theorem P_le_normalizer_Y₂ (hlay : h.LayerHyp d) :
    yamadaP d t ≤ normalizer ((yamadaY₂ d t : Subgroup G) : Set G) := fun x hx =>
  (normalizer_P_le_series h d hlay (le_normalizer hx)).2.1

theorem barIrr_W (hp : ProductHyp h d) :
    ∀ Z : Subgroup (NormalizerQuotient.Bar (yamadaV₁ d t)), 𝔟[yamadaY₂ d t] ≤ Z →
      Z ≤ 𝔟[xtW d t] → 𝔟[d.J.map L.subtype] ≤ normalizer (Z : Set _) →
      Z = 𝔟[yamadaY₂ d t] ∨ Z = 𝔟[xtW d t] := by
  have hlay := hp.layer
  have hs := series_le h d hlay
  have hY₂C := (T4_series_free h d hp).2.1
  intro Z hYZ hZU hJZ
  have hVY := hs.1
  have hP₂ : yamadaP d t ≤ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) :=
    P_le_normalizer_V₁ d
  have hY₂N : yamadaY₂ d t ≤ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) := fun x hx =>
    hP₂ ((hs.2.1.trans (hs.2.2.1.trans hs.2.2.2)) hx)
  have hXtN : xtW d t ≤ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) := fun x hx =>
    W₃_le_normalizer_V₁ h d hlay ((xtW_bounds h d hp).2 hx)
  have h1 : yamadaY₂ d t ≤ NormalizerQuotient.lift Z := by
    have := NormalizerQuotient.lift_mono hYZ
    rwa [NormalizerQuotient.lift_bar hVY hY₂N] at this
  have h2 : NormalizerQuotient.lift Z ≤ xtW d t := by
    have := NormalizerQuotient.lift_mono hZU
    rwa [NormalizerQuotient.lift_bar (hVY.trans (xtW_bounds h d hp).1) hXtN] at this
  have hJ : d.J.map L.subtype ≤ normalizer ((NormalizerQuotient.lift Z : Subgroup G) : Set G) := by
    rintro _ ⟨j, hj, rfl⟩
    exact mem_normalizer_lift d (J_le_normalizer_V₁ h d hlay ⟨j, hj, rfl⟩)
      (hJZ (NormalizerQuotient.proj_mem_bar ⟨j, hj, rfl⟩))
  let TL : Subgroup L := (NormalizerQuotient.lift Z ⊓ d.W.map L.subtype).comap L.subtype
  have hmemTL : ∀ x : L, x ∈ TL ↔ (x : G) ∈ NormalizerQuotient.lift Z ∧ x ∈ d.W := fun x => by
    simp only [TL, Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.coe_subtype]
    exact and_congr_right fun _ => Subgroup.mem_map_iff_mem L.subtype_injective
  have hYLY : ∀ y ∈ d.Y, (y : G) ∈ yamadaY₂ d t := fun y hy => by
    have : (y : G) ∈ yamadaY₂ d t ⊓ centralizer ({t} : Set G) := by
      rw [hY₂C]
      exact ⟨y, hy, rfl⟩
    exact this.1
  have hYTL : d.Y ≤ TL := fun y hy => (hmemTL y).2 ⟨h1 (hYLY y hy), d.Y_le_W hy⟩
  have hTLW : TL ≤ d.W := fun x hx => ((hmemTL x).1 hx).2
  have hJTL : d.J ≤ normalizer (TL : Set L) := by
    intro j hj
    refine mem_normalizer_fintype fun x hx => ?_
    rw [SetLike.mem_coe] at hx ⊢
    have hx' := (hmemTL x).1 hx
    refine (hmemTL _).2 ⟨?_, (mem_normalizer_iff.1 (d.J_le_normalizer_W hj) x).1 hx'.2⟩
    have := (mem_normalizer_iff.1 (hJ ⟨j, hj, rfl⟩) (x : G)).1 hx'.1
    simpa using this
  have hWLN : d.W.map L.subtype ≤ normalizer ((yamadaY₂ d t : Subgroup G) : Set G) := fun x hx =>
    P_le_normalizer_Y₂ h d hlay ((hs.2.2.1.trans hs.2.2.2) (WL_le_W₃ h d hp hx))
  rcases W_irr d hYTL hTLW hJTL with hT | hT
  · left
    have hZY : NormalizerQuotient.lift Z ≤ yamadaY₂ d t := by
      intro z hz
      have hzX : z ∈ xtW d t := h2 hz
      have hmem : z ∈ ((d.W.map L.subtype : Subgroup G) : Set G) * (yamadaY₂ d t : Set G) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hWLN]
        exact hzX
      obtain ⟨w, hw, y, hy, rfl⟩ := Set.mem_mul.1 hmem
      obtain ⟨wL, hwL, rfl⟩ := hw
      have hwZ : (wL : G) ∈ NormalizerQuotient.lift Z := by
        have : (wL : G) = (wL : G) * y * y⁻¹ := by group
        rw [this]
        exact mul_mem hz (inv_mem (h1 hy))
      have hwT : wL ∈ TL := (hmemTL wL).2 ⟨hwZ, hwL⟩
      rw [hT] at hwT
      exact mul_mem (hYLY wL hwT) hy
    calc Z = 𝔟[NormalizerQuotient.lift Z] := (NormalizerQuotient.bar_lift Z).symm
      _ = 𝔟[yamadaY₂ d t] := by rw [le_antisymm hZY h1]
  · right
    have hZX : xtW d t ≤ NormalizerQuotient.lift Z := by
      refine sup_le (fun w hw => ?_) h1
      obtain ⟨wL, hwL, rfl⟩ := hw
      have : wL ∈ TL := by rw [hT]; exact hwL
      exact ((hmemTL wL).1 this).1
    calc Z = 𝔟[NormalizerQuotient.lift Z] := (NormalizerQuotient.bar_lift Z).symm
      _ = 𝔟[xtW d t] := by rw [le_antisymm h2 hZX]


theorem card_bar_q (hlay : h.LayerHyp d) {Z : Subgroup G} (hVZ : yamadaV₁ d t ≤ Z)
    (hZN : Z ≤ normalizer ((yamadaV₁ d t : Subgroup G) : Set G)) :
    Nat.card (𝔟[Z]) * (2 ^ f) ^ 2 = Nat.card Z := by
  have := NormalizerQuotient.card_bar_mul hVZ hZN
  rwa [card_V₁' h d hlay] at this

theorem e2f_J_inv_W (hp : ProductHyp h d) :
    ∀ X : Subgroup (NormalizerQuotient.Bar (yamadaV₁ d t)), 𝔟[yamadaY₂ d t] ≤ X →
      X ≤ 𝔟[yamadaW₃ d t] → 𝔟[d.J.map L.subtype] ≤ normalizer (X : Set _) →
      X = 𝔟[yamadaY₂ d t] ∨ Nat.card X = Nat.card (𝔟[yamadaY₂ d t]) * (2 ^ f) ^ 3 ∨
        X = 𝔟[yamadaW₃ d t] := by
  have hlay := hp.layer
  have hs := series_le h d hlay
  have hVY : yamadaV₁ d t ≤ yamadaY₂ d t := hs.1
  have hY₂N : yamadaY₂ d t ≤ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) := fun x hx =>
    P_le_normalizer_V₁ d ((hs.2.1.trans (hs.2.2.1.trans hs.2.2.2)) hx)
  have hXtN : xtW d t ≤ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) := fun x hx =>
    W₃_le_normalizer_V₁ h d hlay ((xtW_bounds h d hp).2 hx)
  have hbarXt : Nat.card (𝔟[xtW d t]) = Nat.card (𝔟[yamadaY₂ d t]) * (2 ^ f) ^ 3 := by
    have h1 := card_bar_q h d hlay (hVY.trans (xtW_bounds h d hp).1) hXtN
    have h2 := card_bar_q h d hlay hVY hY₂N
    have hpos : 0 < (2 ^ f) ^ 2 := by positivity
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1, card_xtW h d hp, ← h2]
    ring
  have hbarW := e2f_card_W h d hp
  have hbarY := e2f_card_Y h d hp
  exact section_J_inv (t := tB h d) (W := 𝔟[yamadaW₃ d t]) (Y := 𝔟[yamadaY₂ d t])
    (U := 𝔟[xtW d t]) (J := 𝔟[d.J.map L.subtype]) (m := (2 ^ f) ^ 3)
    (tB_mul_tB h d)
    (fun x hx y hy => e2f_D_comm h d hp x (NormalizerQuotient.bar_mono (W₃_le_D₅ h d hlay) hx) y
      (NormalizerQuotient.bar_mono (W₃_le_D₅ h d hlay) hy))
    (fun x hx => e2f_D_sq h d hp x (NormalizerQuotient.bar_mono (W₃_le_D₅ h d hlay) hx))
    (NormalizerQuotient.bar_mono hs.2.1) (e2f_W_conj h d hp) (e2f_Y_conj h d hp)
    (e2f_J_cen_t h d) (e2f_J_nor_W h d hlay) (e2f_J_nor_Y h d hlay)
    (NormalizerQuotient.bar_mono (xtW_bounds h d hp).1)
    (NormalizerQuotient.bar_mono (xtW_bounds h d hp).2) (barU_W h d hp) hbarXt
    (by rw [hbarW, hbarXt, hbarY]; ring) (barIrr_W h d hp)


theorem P_le_normalizer_W₃ (hlay : h.LayerHyp d) :
    yamadaP d t ≤ normalizer ((yamadaW₃ d t : Subgroup G) : Set G) := fun x hx =>
  (normalizer_P_le_series h d hlay (le_normalizer hx)).2.2.1

theorem barU_F (hp : ProductHyp h d) :
    ∀ x ∈ 𝔟[yamadaF₄ d t], x ∈ 𝔟[xtF d t] ↔
      tB h d * x * (tB h d)⁻¹ * x⁻¹ ∈ 𝔟[yamadaW₃ d t] := by
  have hlay := hp.layer
  have hs := series_le h d hlay
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, f4, -⟩ := T4_series_free h d hp
  have hVW : yamadaV₁ d t ≤ yamadaW₃ d t := hs.1.trans hs.2.1
  have hVF : yamadaV₁ d t ≤ yamadaF₄ d t := hs.1.trans (hs.2.1.trans hs.2.2.1)
  have htW : t ∈ normalizer ((yamadaW₃ d t : Subgroup G) : Set G) :=
    (normalizer_P_le_series h d hlay (h.t_mem_normalizer_yamadaP d hlay)).2.2.1
  have htN : t ∈ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) :=
    h.t_mem_normalizer_yamadaV₁ d
  intro x hx
  obtain ⟨x', rfl⟩ := NormalizerQuotient.proj_surjective x
  have hx'F : (x' : G) ∈ yamadaF₄ d t := (NormalizerQuotient.mem_bar_iff hVF x').1 hx
  have hx'W : (x' : G) ∈ normalizer ((yamadaW₃ d t : Subgroup G) : Set G) :=
    P_le_normalizer_W₃ h d hlay (hs.2.2.2 hx'F)
  rw [NormalizerQuotient.mem_bar_iff (hVW.trans (xtF_bounds h d hp).1) x']
  have hcN : t * (x' : G) * t⁻¹ * (x' : G)⁻¹ ∈ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) :=
    mul_mem (mul_mem (mul_mem htN x'.2) (inv_mem htN)) (inv_mem x'.2)
  have hcomm : tB h d * 𝔭 x' * (tB h d)⁻¹ * (𝔭 x')⁻¹ =
      𝔭 ⟨t * (x' : G) * t⁻¹ * (x' : G)⁻¹, hcN⟩ := by
    unfold tB
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  rw [hcomm, NormalizerQuotient.mem_bar_iff hVW, ← xtF_eq h d hp,
    ProductToolboxAux.Core.mem_inf_centralizerMod_zpowers_iff f4.1 h.t_mul_t htW]
  constructor
  · rintro ⟨-, h1⟩
    have h2 := (mem_normalizer_iff.1 hx'W _).1 h1
    have e : (x' : G) * ((x' : G)⁻¹ * (t * x' * t⁻¹)) * (x' : G)⁻¹ =
        t * (x' : G) * t⁻¹ * (x' : G)⁻¹ := by
      group
    rw [e] at h2
    exact h2
  · intro h1
    refine ⟨hx'F, ?_⟩
    have h1' : t * (x' : G) * t⁻¹ * (x' : G)⁻¹ ∈ yamadaW₃ d t := h1
    have h2 := (mem_normalizer_iff.1 (inv_mem hx'W) _).1 h1'
    have e : (x' : G)⁻¹ * (t * (x' : G) * t⁻¹ * (x' : G)⁻¹) * (x' : G)⁻¹⁻¹ =
        (x' : G)⁻¹ * (t * x' * t⁻¹) := by
      group
    rw [e] at h2
    exact h2

theorem barIrr_F (hp : ProductHyp h d) :
    ∀ Z : Subgroup (NormalizerQuotient.Bar (yamadaV₁ d t)), 𝔟[yamadaW₃ d t] ≤ Z →
      Z ≤ 𝔟[xtF d t] → 𝔟[d.J.map L.subtype] ≤ normalizer (Z : Set _) →
      Z = 𝔟[yamadaW₃ d t] ∨ Z = 𝔟[xtF d t] := by
  have hlay := hp.layer
  have hs := series_le h d hlay
  have hF₄C := (T4_series_free h d hp).2.2.2.1
  have hW₃C := (T4_series_free h d hp).2.2.1
  intro Z hWZ hZU hJZ
  have hVW : yamadaV₁ d t ≤ yamadaW₃ d t := hs.1.trans hs.2.1
  have hW₃N : yamadaW₃ d t ≤ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) :=
    W₃_le_normalizer_V₁ h d hlay
  have hXtN : xtF d t ≤ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) := fun x hx =>
    F₄_le_normalizer_V₁ h d hlay ((xtF_bounds h d hp).2 hx)
  have h1 : yamadaW₃ d t ≤ NormalizerQuotient.lift Z := by
    have := NormalizerQuotient.lift_mono hWZ
    rwa [NormalizerQuotient.lift_bar hVW hW₃N] at this
  have h2 : NormalizerQuotient.lift Z ≤ xtF d t := by
    have := NormalizerQuotient.lift_mono hZU
    rwa [NormalizerQuotient.lift_bar (hVW.trans (xtF_bounds h d hp).1) hXtN] at this
  have hJ : d.J.map L.subtype ≤ normalizer ((NormalizerQuotient.lift Z : Subgroup G) : Set G) := by
    rintro _ ⟨j, hj, rfl⟩
    exact mem_normalizer_lift d (J_le_normalizer_V₁ h d hlay ⟨j, hj, rfl⟩)
      (hJZ (NormalizerQuotient.proj_mem_bar ⟨j, hj, rfl⟩))
  let TL : Subgroup L := (NormalizerQuotient.lift Z ⊓ d.F.map L.subtype).comap L.subtype
  have hmemTL : ∀ x : L, x ∈ TL ↔ (x : G) ∈ NormalizerQuotient.lift Z ∧ x ∈ d.F := fun x => by
    simp only [TL, Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.coe_subtype]
    exact and_congr_right fun _ => Subgroup.mem_map_iff_mem L.subtype_injective
  have hWLW : ∀ w ∈ d.W, (w : G) ∈ yamadaW₃ d t := fun w hw => WL_le_W₃ h d hp ⟨w, hw, rfl⟩
  have hWTL : d.W ≤ TL := fun w hw => (hmemTL w).2 ⟨h1 (hWLW w hw), d.W_le_F hw⟩
  have hTLF : TL ≤ d.F := fun x hx => ((hmemTL x).1 hx).2
  have hJTL : d.J ≤ normalizer (TL : Set L) := by
    intro j hj
    refine mem_normalizer_fintype fun x hx => ?_
    rw [SetLike.mem_coe] at hx ⊢
    have hx' := (hmemTL x).1 hx
    refine (hmemTL _).2 ⟨?_, (mem_normalizer_iff.1 (d.J_le_normalizer_F hj) x).1 hx'.2⟩
    have := (mem_normalizer_iff.1 (hJ ⟨j, hj, rfl⟩) (x : G)).1 hx'.1
    simpa using this
  have hFLN : d.F.map L.subtype ≤ normalizer ((yamadaW₃ d t : Subgroup G) : Set G) := fun x hx =>
    P_le_normalizer_W₃ h d hlay (hs.2.2.2 (FL_le_F₄ h d hp hx))
  rcases F_irr d hWTL hTLF hJTL with hT | hT
  · left
    have hZW : NormalizerQuotient.lift Z ≤ yamadaW₃ d t := by
      intro z hz
      have hzX : z ∈ xtF d t := h2 hz
      have hmem : z ∈ ((d.F.map L.subtype : Subgroup G) : Set G) * (yamadaW₃ d t : Set G) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hFLN]
        exact hzX
      obtain ⟨w, hw, y, hy, rfl⟩ := Set.mem_mul.1 hmem
      obtain ⟨wL, hwL, rfl⟩ := hw
      have hwZ : (wL : G) ∈ NormalizerQuotient.lift Z := by
        have : (wL : G) = (wL : G) * y * y⁻¹ := by group
        rw [this]
        exact mul_mem hz (inv_mem (h1 hy))
      have hwT : wL ∈ TL := (hmemTL wL).2 ⟨hwZ, hwL⟩
      rw [hT] at hwT
      exact mul_mem (hWLW wL hwT) hy
    calc Z = 𝔟[NormalizerQuotient.lift Z] := (NormalizerQuotient.bar_lift Z).symm
      _ = 𝔟[yamadaW₃ d t] := by rw [le_antisymm hZW h1]
  · right
    have hZX : xtF d t ≤ NormalizerQuotient.lift Z := by
      refine sup_le (fun w hw => ?_) h1
      obtain ⟨wL, hwL, rfl⟩ := hw
      have : wL ∈ TL := by rw [hT]; exact hwL
      exact ((hmemTL wL).1 this).1
    calc Z = 𝔟[NormalizerQuotient.lift Z] := (NormalizerQuotient.bar_lift Z).symm
      _ = 𝔟[xtF d t] := by rw [le_antisymm h2 hZX]

theorem e2f_J_inv_F (hp : ProductHyp h d) :
    ∀ X : Subgroup (NormalizerQuotient.Bar (yamadaV₁ d t)), 𝔟[yamadaW₃ d t] ≤ X →
      X ≤ 𝔟[yamadaF₄ d t] → 𝔟[d.J.map L.subtype] ≤ normalizer (X : Set _) →
      X = 𝔟[yamadaW₃ d t] ∨ Nat.card X = Nat.card (𝔟[yamadaW₃ d t]) * (2 ^ f) ^ 3 ∨
        X = 𝔟[yamadaF₄ d t] := by
  have hlay := hp.layer
  have hs := series_le h d hlay
  have hVW : yamadaV₁ d t ≤ yamadaW₃ d t := hs.1.trans hs.2.1
  have hW₃N : yamadaW₃ d t ≤ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) :=
    W₃_le_normalizer_V₁ h d hlay
  have hXtN : xtF d t ≤ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) := fun x hx =>
    F₄_le_normalizer_V₁ h d hlay ((xtF_bounds h d hp).2 hx)
  have hbarXt : Nat.card (𝔟[xtF d t]) = Nat.card (𝔟[yamadaW₃ d t]) * (2 ^ f) ^ 3 := by
    have h1 := card_bar_q h d hlay (hVW.trans (xtF_bounds h d hp).1) hXtN
    have h2 := card_bar_q h d hlay hVW hW₃N
    have hpos : 0 < (2 ^ f) ^ 2 := by positivity
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1, card_xtF h d hp, ← h2]
    ring
  have hbarW := e2f_card_W h d hp
  have hbarF := e2f_card_F h d hp
  have hF₄D : yamadaF₄ d t ≤ yamadaD₅ d t := F₄_le_D₅ d
  exact section_J_inv (t := tB h d) (W := 𝔟[yamadaF₄ d t]) (Y := 𝔟[yamadaW₃ d t])
    (U := 𝔟[xtF d t]) (J := 𝔟[d.J.map L.subtype]) (m := (2 ^ f) ^ 3)
    (tB_mul_tB h d)
    (fun x hx y hy => e2f_D_comm h d hp x (NormalizerQuotient.bar_mono hF₄D hx) y
      (NormalizerQuotient.bar_mono hF₄D hy))
    (fun x hx => e2f_D_sq h d hp x (NormalizerQuotient.bar_mono hF₄D hx))
    (NormalizerQuotient.bar_mono hs.2.2.1) (F₄_conj h d hp) (e2f_W_conj h d hp)
    (e2f_J_cen_t h d) (e2f_J_nor_F h d hlay) (e2f_J_nor_W h d hlay)
    (NormalizerQuotient.bar_mono (xtF_bounds h d hp).1)
    (NormalizerQuotient.bar_mono (xtF_bounds h d hp).2) (barU_F h d hp) hbarXt
    (by rw [hbarF, hbarXt, hbarW]; ring) (barIrr_F h d hp)


theorem e2f_W_fixed_not_le_Y (hp : ProductHyp h d) :
    ¬ (𝔟[yamadaW₃ d t] ⊓ centralizer ({tB h d} : Set _) ≤ 𝔟[yamadaY₂ d t]) := by
  intro h0
  have hlay := hp.layer
  have hs := series_le h d hlay
  have hT4 := T4_series_free h d hp
  have hWle : d.W.map L.subtype ≤ yamadaY₂ d t ⊓ centralizer ({t} : Set G) := by
    intro x hx
    have hxW : x ∈ yamadaW₃ d t ⊓ centralizer ({t} : Set G) := by
      rw [hT4.2.2.1]
      exact hx
    obtain ⟨hxW, hxC⟩ := mem_inf.1 hxW
    have hxN := W₃_le_normalizer_V₁ h d hlay hxW
    have h1 : 𝔭 ⟨x, hxN⟩ ∈ 𝔟[yamadaW₃ d t] ⊓ centralizer ({tB h d} : Set _) := by
      refine mem_inf.2 ⟨NormalizerQuotient.proj_mem_bar hxW, ?_⟩
      rw [mem_centralizer_singleton_iff]
      unfold tB
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_singleton_iff.1 hxC)
    have h2 := h0 h1
    exact mem_inf.2 ⟨(NormalizerQuotient.mem_bar_iff hs.1 _).1 h2, hxC⟩
  have hcard := Subgroup.card_le_of_le hWle
  rw [hT4.2.1, Subgroup.card_map_of_injective L.subtype_injective, d.card_W,
    Subgroup.card_map_of_injective L.subtype_injective, d.card_Y] at hcard
  have h2 : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := hp.two_le; omega)
  have : (2 ^ f) ^ 2 < (2 ^ f) ^ 5 := Nat.pow_lt_pow_right h2 (by norm_num)
  omega

theorem e2f_C_le_N (hp : ProductHyp h d) (hK₁ : IsN1Factor d t K₁) :
    𝔟[cLV d] ≤ 𝔟[K₁] ⊔ (𝔟[K₁])ᵍ[tB h d] := by
  have hlay := hp.layer
  rw [← bar_conjg_t h d, ← bar_sup (K₁_le_normalizer_V₁ h d hlay hK₁)
    (K₁t_le_normalizer_V₁ h d hlay hK₁), ← hK₁.sup_eq]
  exact NormalizerQuotient.bar_mono (cLV_le_nOne h d hp)

theorem e2f_C_cen_t : 𝔟[cLV d] ≤ centralizer ({tB h d} : Set _) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [mem_centralizer_singleton_iff]
  obtain ⟨l, hl, hly⟩ := mem_subgroupOf.1 hy
  have hc : (y : G) * t = t * y := by
    rw [← hly]
    exact mem_centralizer_singleton_iff.1 (h.L_le_centralizer l.2)
  unfold tB
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hc

theorem e2f_C_perfect (hlay : h.LayerHyp d) : ⁅𝔟[cLV d], 𝔟[cLV d]⁆ = 𝔟[cLV d] := by
  rw [← ProductN1HatAux.bar_commutator (cLV_le_normalizer_V₁ h d hlay)
    (cLV_le_normalizer_V₁ h d hlay), cLV_perfect d]


theorem DL_le_D₅ (hp : ProductHyp h d) : d.D.map L.subtype ≤ yamadaD₅ d t := by
  rw [← (T4_series_free h d hp).2.2.2.2.1]
  exact inf_le_left

theorem DL_le_cLV : d.D.map L.subtype ≤ cLV d :=
  Subgroup.map_mono (d.D_le_S.trans d.S_le_centralizer_V)

theorem DL_le_normalizer_V₁ (hlay : h.LayerHyp d) :
    d.D.map L.subtype ≤ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) :=
  (DL_le_cLV d).trans (cLV_le_normalizer_V₁ h d hlay)

theorem D₅_le_normalizer_V₁ (d : TrialityD4Data L (2 ^ f)) :
    yamadaD₅ d t ≤ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) := fun x hx =>
  P_le_normalizer_V₁ d (yamadaD₅_le_yamadaP d t hx)

theorem D1_eq (hp : ProductHyp h d) :
    𝔟[yamadaD₅ d t] ⊓ centralizer ({tB h d} : Set _) = 𝔟[d.D.map L.subtype] := by
  have hlay := hp.layer
  have hT4 := T4_series_free h d hp
  have hVD : yamadaV₁ d t ≤ yamadaD₅ d t := V₁_le_D₅ h d hlay
  have hDLD := DL_le_D₅ h d hp
  have hDLN := DL_le_normalizer_V₁ h d hlay
  have htN : t ∈ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) :=
    h.t_mem_normalizer_yamadaV₁ d
  apply le_antisymm
  · intro x hx
    obtain ⟨hxD, hxc⟩ := mem_inf.1 hx
    obtain ⟨x', rfl⟩ := NormalizerQuotient.proj_surjective x
    have hx'D : (x' : G) ∈ yamadaD₅ d t := (NormalizerQuotient.mem_bar_iff hVD x').1 hxD
    rw [mem_centralizer_singleton_iff] at hxc
    have hcomm := (commutator_mem_iff_proj htN x'.2).1 (by unfold tB at hxc; exact hxc)
    have hcoc : (x' : G)⁻¹ * (t * x' * t⁻¹) ∈ yamadaV₁ d t := by
      have h1 := (mem_normalizer_iff.1 (inv_mem x'.2) _).1 hcomm
      have e : (x' : G)⁻¹ * (t * x' * t⁻¹ * (x' : G)⁻¹) * (x' : G)⁻¹⁻¹ =
          (x' : G)⁻¹ * (t * x' * t⁻¹) := by group
      rwa [e] at h1
    have hH1 : H1Zero t (yamadaV₁ d t) :=
      ProductToolboxAux.h1Zero_of_freeLifted h.t_mul_t htN
        (ProductToolboxAux.P04.t_mem_normalizer_bot t) (ProductToolboxAux.h1Zero_bot t)
        (hT4.2.2.2.2.2.2.2.2.2.2.1)
    have hmem := T2_lift h.t_mul_t hVD (fun x hx => D₅_le_normalizer_V₁ d hx)
      (h.t_mem_normalizer_yamadaD₅_C9 d) htN hH1 x' hx'D hcoc
    rw [hT4.2.2.2.2.1] at hmem
    have hmul : ((d.D.map L.subtype ⊔ yamadaV₁ d t : Subgroup G) : Set G) =
        ((d.D.map L.subtype : Subgroup G) : Set G) * (yamadaV₁ d t : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ (fun x hx => hDLN hx)
    have hmem' : (x' : G) ∈
        ((d.D.map L.subtype : Subgroup G) : Set G) * (yamadaV₁ d t : Set G) := by
      rw [← hmul]
      exact hmem
    obtain ⟨c, hc, v, hv, hcv⟩ := Set.mem_mul.1 hmem'
    refine (mem_bar_iff' x').2 ⟨v⁻¹, inv_mem hv, ?_⟩
    have : (x' : G) * v⁻¹ = c := by rw [← hcv]; group
    rw [this]
    exact hc
  · rintro _ ⟨y, hy, rfl⟩
    have hyDL : (y : G) ∈ d.D.map L.subtype := mem_subgroupOf.1 hy
    have hyD : (y : G) ∈ yamadaD₅ d t := hDLD hyDL
    have hyC : (y : G) ∈ centralizer ({t} : Set G) := by
      have : (y : G) ∈ yamadaD₅ d t ⊓ centralizer ({t} : Set G) := by
        rw [hT4.2.2.2.2.1]
        exact hyDL
      exact this.2
    refine mem_inf.2 ⟨NormalizerQuotient.proj_mem_bar hyD, ?_⟩
    rw [mem_centralizer_singleton_iff]
    unfold tB
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 hyC)

theorem e2f_D₁_le_C (hp : ProductHyp h d) :
    𝔟[yamadaD₅ d t] ⊓ centralizer ({tB h d} : Set _) ≤ 𝔟[cLV d] := by
  rw [D1_eq h d hp]
  exact NormalizerQuotient.bar_mono (DL_le_cLV d)

theorem V₁_inf_DL (hp : ProductHyp h d) :
    yamadaV₁ d t ⊓ d.D.map L.subtype = d.V.map L.subtype := by
  have hT4 := T4_series_free h d hp
  apply le_antisymm
  · intro x hx
    obtain ⟨hxV, hxD⟩ := mem_inf.1 hx
    have hxC : x ∈ centralizer ({t} : Set G) := by
      have : x ∈ yamadaD₅ d t ⊓ centralizer ({t} : Set G) := by
        rw [hT4.2.2.2.2.1]
        exact hxD
      exact this.2
    have : x ∈ yamadaV₁ d t ⊓ centralizer ({t} : Set G) := mem_inf.2 ⟨hxV, hxC⟩
    rwa [hT4.1] at this
  · intro x hx
    have hxV : x ∈ yamadaV₁ d t ⊓ centralizer ({t} : Set G) := by
      rw [hT4.1]
      exact hx
    obtain ⟨xl, hxl, rfl⟩ := hx
    exact mem_inf.2 ⟨hxV.1, ⟨xl, d.F_le_D (d.W_le_F (d.Y_le_W (d.V_le_Y hxl))), rfl⟩⟩

theorem e2f_card_D₁ (hp : ProductHyp h d) :
    Nat.card ↥(𝔟[yamadaD₅ d t] ⊓ centralizer ({tB h d} : Set _)) = (2 ^ f) ^ 8 := by
  have hlay := hp.layer
  rw [D1_eq h d hp]
  have h1 := card_bar_mul' (A := yamadaV₁ d t) (DL_le_normalizer_V₁ h d hlay)
  rw [V₁_inf_DL h d hp, Subgroup.card_map_of_injective L.subtype_injective, d.card_V,
    Subgroup.card_map_of_injective L.subtype_injective, d.card_D] at h1
  have hpos : 0 < 2 ^ f := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1]
  ring


theorem VL_le_V₁ (hp : ProductHyp h d) : d.V.map L.subtype ≤ yamadaV₁ d t := by
  rw [← (T4_series_free h d hp).1]
  exact inf_le_left

theorem e2f_C_irr (hp : ProductHyp h d) :
    ∀ X : Subgroup (NormalizerQuotient.Bar (yamadaV₁ d t)),
      X ≤ 𝔟[yamadaD₅ d t] ⊓ centralizer ({tB h d} : Set _) → 𝔟[cLV d] ≤ normalizer (X : Set _) →
      X = ⊥ ∨ X = 𝔟[yamadaD₅ d t] ⊓ centralizer ({tB h d} : Set _) := by
  have hlay := hp.layer
  intro X hX hCX
  rw [D1_eq h d hp] at hX ⊢
  have hDLN := DL_le_normalizer_V₁ h d hlay
  have hbarsup : 𝔟[yamadaV₁ d t ⊔ d.D.map L.subtype] = 𝔟[d.D.map L.subtype] :=
    ProductN1HatAux.bar_sup_left hDLN
  have hlift : NormalizerQuotient.lift (𝔟[d.D.map L.subtype]) =
      yamadaV₁ d t ⊔ d.D.map L.subtype := by
    rw [← hbarsup]
    exact NormalizerQuotient.lift_bar le_sup_left (sup_le le_normalizer hDLN)
  have hVX : yamadaV₁ d t ≤ NormalizerQuotient.lift X := NormalizerQuotient.le_lift X
  have hXD : NormalizerQuotient.lift X ≤ yamadaV₁ d t ⊔ d.D.map L.subtype := by
    have := NormalizerQuotient.lift_mono hX
    rwa [hlift] at this
  have hcN : ∀ g ∈ cLV d, g ∈ normalizer ((NormalizerQuotient.lift X : Subgroup G) : Set G) :=
    fun g hg => mem_normalizer_lift d (cLV_le_normalizer_V₁ h d hlay hg)
      (hCX (NormalizerQuotient.proj_mem_bar hg))
  let TL : Subgroup L := (NormalizerQuotient.lift X ⊓ d.D.map L.subtype).comap L.subtype
  have hmemTL : ∀ x : L, x ∈ TL ↔ (x : G) ∈ NormalizerQuotient.lift X ∧ x ∈ d.D := fun x => by
    simp only [TL, Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.coe_subtype]
    exact and_congr_right fun _ => Subgroup.mem_map_iff_mem L.subtype_injective
  have hVTL : d.V ≤ TL := fun v hv => (hmemTL v).2
    ⟨hVX (VL_le_V₁ h d hp ⟨v, hv, rfl⟩), d.F_le_D (d.W_le_F (d.Y_le_W (d.V_le_Y hv)))⟩
  have hTLD : TL ≤ d.D := fun x hx => ((hmemTL x).1 hx).2
  have hLSN : d.leviShort ≤ normalizer (TL : Set L) := by
    intro g hg
    refine mem_normalizer_fintype fun x hx => ?_
    rw [SetLike.mem_coe] at hx ⊢
    have hx' := (hmemTL x).1 hx
    have hgc : (g : G) ∈ cLV d := ⟨g, by rw [d.centralizer_V_eq]; exact mem_sup_right hg, rfl⟩
    refine (hmemTL _).2 ⟨?_, ?_⟩
    · have := (mem_normalizer_iff.1 (hcN _ hgc) (x : G)).1 hx'.1
      simpa using this
    · have hgD : g ∈ normalizer (d.D : Set L) := by
        rw [← d.normalizer_V_eq_normalizer_D]
        exact d.leviShort_le_normalizer_V hg
      exact (mem_normalizer_iff.1 hgD x).1 hx'.2
  have hDLmem : ∀ c ∈ d.D.map L.subtype, ∃ cL : L, cL ∈ d.D ∧ (cL : G) = c := fun c hc => by
    obtain ⟨cL, hcL, hcLc⟩ := hc
    exact ⟨cL, hcL, hcLc⟩
  rcases d.yamada_three_ten.1 TL hVTL hTLD hLSN with hT | hT
  · left
    have hXV : NormalizerQuotient.lift X ≤ yamadaV₁ d t := by
      intro z hz
      have hmem : z ∈ ((yamadaV₁ d t : Subgroup G) : Set G) *
          ((d.D.map L.subtype : Subgroup G) : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hDLN]
        exact hXD hz
      obtain ⟨v, hv, c, hc, rfl⟩ := Set.mem_mul.1 hmem
      obtain ⟨cL, hcL, rfl⟩ := hDLmem c hc
      have hcX : (cL : G) ∈ NormalizerQuotient.lift X := by
        have : (cL : G) = v⁻¹ * (v * (cL : G)) := by group
        rw [this]
        exact mul_mem (inv_mem (hVX hv)) hz
      have hcT : cL ∈ TL := (hmemTL cL).2 ⟨hcX, hcL⟩
      rw [hT] at hcT
      exact mul_mem hv (VL_le_V₁ h d hp ⟨cL, hcT, rfl⟩)
    calc X = 𝔟[NormalizerQuotient.lift X] := (NormalizerQuotient.bar_lift X).symm
      _ = 𝔟[yamadaV₁ d t] := by rw [le_antisymm hXV hVX]
      _ = ⊥ := bar_self
  · right
    have hDX : d.D.map L.subtype ≤ NormalizerQuotient.lift X := by
      intro c hc
      obtain ⟨cL, hcL, rfl⟩ := hDLmem c hc
      have : cL ∈ TL := by rw [hT]; exact hcL
      exact ((hmemTL cL).1 this).1
    calc X = 𝔟[NormalizerQuotient.lift X] := (NormalizerQuotient.bar_lift X).symm
      _ = 𝔟[yamadaV₁ d t ⊔ d.D.map L.subtype] := by
        rw [le_antisymm hXD (sup_le hVX hDX)]
      _ = 𝔟[d.D.map L.subtype] := hbarsup

theorem V₁_inf_cLV (hp : ProductHyp h d) :
    yamadaV₁ d t ⊓ cLV d = d.V.map L.subtype := by
  have hT4 := T4_series_free h d hp
  apply le_antisymm
  · intro x hx
    obtain ⟨hxV, hxc⟩ := mem_inf.1 hx
    have hxC : x ∈ centralizer ({t} : Set G) := by
      obtain ⟨l, -, rfl⟩ := hxc
      exact h.L_le_centralizer l.2
    have : x ∈ yamadaV₁ d t ⊓ centralizer ({t} : Set G) := mem_inf.2 ⟨hxV, hxC⟩
    rwa [hT4.1] at this
  · intro x hx
    obtain ⟨xl, hxl, rfl⟩ := hx
    refine mem_inf.2 ⟨VL_le_V₁ h d hp ⟨xl, hxl, rfl⟩, ?_⟩
    exact DL_le_cLV d ⟨xl, d.F_le_D (d.W_le_F (d.Y_le_W (d.V_le_Y hxl))), rfl⟩

theorem e2f_card_C (hp : ProductHyp h d) :
    Nat.card (𝔟[cLV d]) = Nat.card SL(2, d.Γ) * (2 ^ f) ^ 8 := by
  have hlay := hp.layer
  have h1 := card_bar_mul' (A := yamadaV₁ d t) (cLV_le_normalizer_V₁ h d hlay)
  rw [V₁_inf_cLV h d hp, Subgroup.card_map_of_injective L.subtype_injective, d.card_V] at h1
  have hcLV : Nat.card (cLV d) = (2 ^ f) ^ 9 * ((2 ^ f) ^ 3 * ((2 ^ f) ^ 6 - 1)) := by
    unfold cLV
    rw [Subgroup.card_map_of_injective L.subtype_injective, d.centralizer_V_eq]
    have h2 := Common.card_sup_mul_card_inf_eq (A := d.D) (B := d.leviShort)
      (by rw [← d.normalizer_V_eq_normalizer_D]; exact d.leviShort_le_normalizer_V)
    rw [d.D_inf_leviShort, Subgroup.card_bot, mul_one, d.card_D, d.card_leviShort] at h2
    exact h2
  have hSL : Nat.card SL(2, d.Γ) = (2 ^ f) ^ 3 * (((2 ^ f) ^ 3) ^ 2 - 1) := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, d.card_Γ]
  rw [hcLV] at h1
  have hpos : 0 < 2 ^ f := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1, hSL, ← pow_mul]
  ring


theorem e2f_P_pgroup (hp : ProductHyp h d) : IsPGroup 2 (𝔟[yamadaP d t]) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine IsPGroup.of_card (n := 22 * f) ?_
  rw [e2f_card_P' h d hp, ← pow_mul, mul_comm]

theorem e2Ctx (hp : ProductHyp h d) (hK₁ : IsN1Factor d t K₁) :
    ∃ φ : ↥(𝔟[K₁]) →* SL(2, d.Γ),
      E2Ctx f d.Γ (tB h d) (uB h d hp.layer) (𝔟[K₁]) (𝔟[yamadaD₅ d t]) (𝔟[yamadaP d t])
        (𝔟[yamadaY₂ d t]) (𝔟[yamadaW₃ d t]) (𝔟[yamadaF₄ d t]) (𝔟[d.J.map L.subtype])
        (𝔟[jZeroG d]) (𝔟[cLV d]) φ := by
  have hlay := hp.layer
  obtain ⟨φ, hφs, hφk⟩ := e2f_phi h d hp hK₁
  refine ⟨φ, ?_⟩
  exact
    { two_le := hp.two_le
      card_Γ := d.card_Γ
      charTwo := inferInstance
      t_mul_t := tB_mul_tB h d
      u_mul_u := uB_mul_uB h d hlay
      t_comm_u := tB_comm_uB h d hlay
      K_inf := e2f_K_inf h d hp hK₁
      comm_le := e2f_comm_le h d hp hK₁
      φ_surj := hφs
      φ_ker := hφk
      D_comm := e2f_D_comm h d hp
      D_sq := e2f_D_sq h d hp
      D_le_P := NormalizerQuotient.bar_mono (yamadaD₅_le_yamadaP d t)
      P_le_N := e2f_P_le_N h d hp hK₁
      P_pgroup := e2f_P_pgroup h d hp
      card_P := e2f_card_P h d hp
      P_conj := e2f_P_conj h d hp
      mem_Y := e2f_mem_Y h d hlay
      mem_W := e2f_mem_W h d hlay
      mem_F := e2f_mem_F h d hlay
      F_le_D := e2f_F_le_D d
      card_Y := e2f_card_Y h d hp
      card_W := e2f_card_W h d hp
      card_F := e2f_card_F h d hp
      card_D := e2f_card_D h d hp
      Y_conj := e2f_Y_conj h d hp
      W_conj := e2f_W_conj h d hp
      u_mem_N := e2f_u_mem_N h d hp hK₁
      u_not_mem_normalizer_P := e2f_u_not_mem h d hp
      D_eq_sup := e2f_D_eq_sup h d hlay
      W_inf := e2f_W_inf h d hlay
      J_odd := e2f_J_odd h d hlay
      J_cen_t := e2f_J_cen_t h d
      J_nor_N := e2f_J_nor_N h d hp hK₁
      J_nor_P := e2f_J_nor_P h d hlay
      J_nor_Y := e2f_J_nor_Y h d hlay
      J_nor_W := e2f_J_nor_W h d hlay
      J_nor_F := e2f_J_nor_F h d hlay
      J₀_le_J := e2f_J₀_le_J d
      J_conj_u := e2f_J_conj_u h d hlay
      J₀_conj_u := e2f_J₀_conj_u h d hlay
      J₀_cen_Y := e2f_J₀_cen_Y h d hp
      W_inf_cen := e2f_W_inf_cen h d hp
      D_J₀_le_F := e2f_D_J₀_le_F h d hp
      W_fixed_not_le_Y := e2f_W_fixed_not_le_Y h d hp
      J_inv_W := e2f_J_inv_W h d hp
      J_inv_F := e2f_J_inv_F h d hp
      C_le_N := e2f_C_le_N h d hp hK₁
      C_cen_t := e2f_C_cen_t h d
      C_perfect := e2f_C_perfect h d hlay
      D₁_le_C := e2f_D₁_le_C h d hp
      card_D₁ := e2f_card_D₁ h d hp
      C_irr := e2f_C_irr h d hp
      card_C := e2f_card_C h d hp }

end Fields


section Export

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) {K₁ : Subgroup G}

local notation "𝔟[" X "]" => NormalizerQuotient.bar (yamadaV₁ d t) X
local notation "𝔭" => NormalizerQuotient.proj (yamadaV₁ d t)

theorem V₁_le_K₁' (hp : ProductHyp h d) (hK₁ : IsN1Factor d t K₁) :
    yamadaV₁ d t ≤ ⁅K₁, K₁⁆ := by
  have hy := h.l6Hyps d hp.layer
  have h525 : ⁅yamadaD₅ d t, yamadaD₅ d t⁆ = yamadaV₁ d t :=
    (h.yamada_5_25 d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593 hy.h5101 hy.h5102 hy.h59e
      hy.h520 hy.h5221 hy.h521).1
  rw [← h525]
  exact commutator_mono hK₁.D₅_le hK₁.D₅_le

theorem e2_core (hp : ProductHyp h d) (hK₁ : IsN1Factor d t K₁) :
    (nOne d t = ⁅K₁, K₁⁆ ⊔ (⁅K₁, K₁⁆)ᵍ[t] ∧ ⁅K₁, K₁⁆ ⊓ (⁅K₁, K₁⁆)ᵍ[t] = yamadaV₁ d t ∧
      ⁅⁅K₁, K₁⁆, (⁅K₁, K₁⁆)ᵍ[t]⁆ ≤ yamadaV₁ d t ∧
      SectionIso ⁅K₁, K₁⁆ (yamadaV₁ d t) (cLV d) (d.V.map L.subtype)) ∧
    (yamadaD₅ d t = centerMod (yamadaV₁ d t) (K₁ᵍ[t]) ⊔
        (centerMod (yamadaV₁ d t) (K₁ᵍ[t]))ᵍ[t] ∧
      centerMod (yamadaV₁ d t) (K₁ᵍ[t]) ⊓ (centerMod (yamadaV₁ d t) (K₁ᵍ[t]))ᵍ[t] =
        yamadaV₁ d t ∧
      (yamadaV₁ d t).relIndex (centerMod (yamadaV₁ d t) (K₁ᵍ[t])) = (2 ^ f) ^ 8 ∧
      centerMod (yamadaV₁ d t) (K₁ᵍ[t]) = pCoreOf 2 ⁅K₁, K₁⁆) := by
  have hlay := hp.layer
  obtain ⟨φ, hctx⟩ := e2Ctx h d hp hK₁
  obtain ⟨⟨hA1, hA2, hA3, ⟨eqv⟩⟩, hB1, hB2, hB3, hB4, hB5⟩ := hctx.E2_abstract
  have htN : t ∈ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) :=
    h.t_mem_normalizer_yamadaV₁ d
  have hVK : yamadaV₁ d t ≤ K₁ := V₁_le_K₁ h d hlay hK₁
  have hK₁N := K₁_le_normalizer_V₁ h d hlay hK₁
  have hK₁tN := K₁t_le_normalizer_V₁ h d hlay hK₁
  have hVK' := V₁_le_K₁' h d hp hK₁
  have hK'K : ⁅K₁, K₁⁆ ≤ K₁ := commutator_le_of_le le_rfl le_rfl
  have hK'N : ⁅K₁, K₁⁆ ≤ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) := hK'K.trans hK₁N
  have hK'tN : (⁅K₁, K₁⁆)ᵍ[t] ≤ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) :=
    (conjg_mono hK'K t).trans hK₁tN
  have hVK't : yamadaV₁ d t ≤ (⁅K₁, K₁⁆)ᵍ[t] := by
    calc yamadaV₁ d t = (yamadaV₁ d t)ᵍ[t] := (conjg_eq_of_mem_normalizer htN).symm
      _ ≤ (⁅K₁, K₁⁆)ᵍ[t] := conjg_mono hVK' t
  have bK' : 𝔟[⁅K₁, K₁⁆] = ⁅𝔟[K₁], 𝔟[K₁]⁆ := ProductN1HatAux.bar_commutator hK₁N hK₁N
  have bKt : 𝔟[K₁ᵍ[t]] = (𝔟[K₁])ᵍ[tB h d] := bar_conjg_t h d K₁
  have bK't : 𝔟[(⁅K₁, K₁⁆)ᵍ[t]] = (⁅𝔟[K₁], 𝔟[K₁]⁆)ᵍ[tB h d] := by rw [bar_conjg_t h d, bK']
  have hnOneN : nOne d t ≤ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) := fun x hx =>
    normalizer_D₅_le_normalizer_V₁ h d hlay (nOne_le_normalizer_D₅ d hx)
  have hnOne : 𝔟[nOne d t] = 𝔟[K₁] ⊔ (𝔟[K₁])ᵍ[tB h d] := by
    rw [hK₁.sup_eq, bar_sup hK₁N hK₁tN, bKt]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  ·
    apply eq_of_bar_eq (hVK.trans (K₁_le_nOne hK₁)) hnOneN (le_sup_of_le_left hVK')
      (sup_le hK'N hK'tN)
    rw [hnOne, bar_sup hK'N hK'tN, bK', bK't]
    exact hA1
  ·
    apply eq_of_bar_eq (le_inf hVK' hVK't) (inf_le_left.trans hK'N) le_rfl le_normalizer
    rw [ProductN1HatAux.bar_inf hVK' hVK't, bK', bK't, hA2, bar_self]
  ·
    intro x hx
    have hxN : x ∈ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) :=
      (commutator_le_of_le hK'N hK'tN) hx
    have h1 : 𝔭 ⟨x, hxN⟩ ∈ 𝔟[⁅⁅K₁, K₁⁆, (⁅K₁, K₁⁆)ᵍ[t]⁆] := NormalizerQuotient.proj_mem_bar hx
    rw [ProductN1HatAux.bar_commutator hK'N hK'tN, bK', bK't, hA3, Subgroup.mem_bot] at h1
    exact NormalizerQuotient.proj_eq_one_iff.1 h1
  ·
    have hcN := cLV_le_normalizer_V₁ h d hlay
    have hVLc : d.V.map L.subtype ≤ cLV d := by
      rw [← V₁_inf_cLV h d hp]
      exact inf_le_right
    have hn1 : ((yamadaV₁ d t).subgroupOf ⁅K₁, K₁⁆).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hVK').2 hK'N
    have hVLcN : cLV d ≤ normalizer ((d.V.map L.subtype : Subgroup G) : Set G) := by
      rintro _ ⟨l, hl, rfl⟩
      have hl' : l ∈ normalizer (d.V : Set L) := Subgroup.centralizer_le_normalizer _ hl
      refine mem_normalizer_fintype fun x hx => ?_
      rw [SetLike.mem_coe] at hx ⊢
      obtain ⟨v, hv, rfl⟩ := hx
      exact ⟨l * v * l⁻¹, (mem_normalizer_iff.1 hl' v).1 hv, by simp⟩
    have hn2 : ((d.V.map L.subtype).subgroupOf (cLV d)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hVLc).2 hVLcN
    refine ⟨hn1, hn2, ?_⟩
    haveI := hn1
    haveI : ((yamadaV₁ d t).subgroupOf (cLV d)).Normal := ker_barHom hcN ▸ MonoidHom.normal_ker _
    have eK := barEquiv (A := yamadaV₁ d t) hK'N
    have hVc : (yamadaV₁ d t).subgroupOf (cLV d) = (d.V.map L.subtype).subgroupOf (cLV d) := by
      rw [← Subgroup.inf_subgroupOf_right (yamadaV₁ d t) (cLV d), V₁_inf_cLV h d hp]
    have eC : (↥(cLV d) ⧸ (d.V.map L.subtype).subgroupOf (cLV d)) ≃* ↥(𝔟[cLV d]) :=
      (QuotientGroup.quotientMulEquivOfEq hVc.symm).trans (barEquiv (A := yamadaV₁ d t) hcN)
    exact ⟨eK.trans ((MulEquiv.subgroupCongr bK').trans (eqv.trans eC.symm))⟩
  · set E : Subgroup (NormalizerQuotient.Bar (yamadaV₁ d t)) := zc ((𝔟[K₁])ᵍ[tB h d]) with hE
    have hEq : centerMod (yamadaV₁ d t) (K₁ᵍ[t]) = NormalizerQuotient.lift E := by
      rw [centerMod_eq_lift_zc, bKt]
    have hVEt : yamadaV₁ d t ≤ centerMod (yamadaV₁ d t) (K₁ᵍ[t]) := by
      rw [hEq]
      exact NormalizerQuotient.le_lift E
    have hEtN : centerMod (yamadaV₁ d t) (K₁ᵍ[t]) ≤
        normalizer ((yamadaV₁ d t : Subgroup G) : Set G) := by
      rw [hEq]
      exact NormalizerQuotient.lift_le_normalizer E
    have hbarEt : 𝔟[centerMod (yamadaV₁ d t) (K₁ᵍ[t])] = E := by
      rw [hEq, NormalizerQuotient.bar_lift]
    have hVEtt : yamadaV₁ d t ≤ (centerMod (yamadaV₁ d t) (K₁ᵍ[t]))ᵍ[t] := by
      calc yamadaV₁ d t = (yamadaV₁ d t)ᵍ[t] := (conjg_eq_of_mem_normalizer htN).symm
        _ ≤ _ := conjg_mono hVEt t
    have hEttN := conjg_le_normalizer htN hEtN
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply eq_of_bar_eq (V₁_le_D₅ h d hlay) (fun x hx => D₅_le_normalizer_V₁ d hx)
        (le_sup_of_le_left hVEt) (sup_le hEtN hEttN)
      rw [bar_sup hEtN hEttN, bar_conjg_t h d, hbarEt]
      exact hB1
    · apply eq_of_bar_eq (le_inf hVEt hVEtt) (inf_le_left.trans hEtN) le_rfl le_normalizer
      rw [ProductN1HatAux.bar_inf hVEt hVEtt, bar_conjg_t h d, hbarEt, hB2, bar_self]
    · have h1 := Subgroup.relIndex_mul_card (H := yamadaV₁ d t)
        (K := centerMod (yamadaV₁ d t) (K₁ᵍ[t]))
      rw [inf_of_le_left hVEt] at h1
      have h2 := NormalizerQuotient.card_bar_mul hVEt hEtN
      rw [hbarEt, hB3] at h2
      have hpos : 0 < Nat.card (yamadaV₁ d t) := Nat.card_pos
      apply Nat.eq_of_mul_eq_mul_right hpos
      rw [h1, ← h2]
    ·
      symm
      have hVD : yamadaV₁ d t ≤ yamadaD₅ d t := V₁_le_D₅ h d hlay
      have hD₅N : yamadaD₅ d t ≤ normalizer ((yamadaV₁ d t : Subgroup G) : Set G) := fun x hx =>
        D₅_le_normalizer_V₁ d hx
      have hBE : ⁅K₁, K₁⁆ ⊓ yamadaD₅ d t = centerMod (yamadaV₁ d t) (K₁ᵍ[t]) := by
        apply eq_of_bar_eq (le_inf hVK' hVD) (inf_le_left.trans hK'N) hVEt hEtN
        rw [ProductN1HatAux.bar_inf hVK' hVD, bK', hbarEt]
        exact hB4
      have hKeq : K₁ = ⁅K₁, K₁⁆ ⊔ yamadaD₅ d t := by
        apply eq_of_bar_eq hVK hK₁N (le_sup_of_le_left hVK') (sup_le hK'N hD₅N)
        rw [bar_sup hK'N hD₅N, bK']
        exact hB5
      have hEB : centerMod (yamadaV₁ d t) (K₁ᵍ[t]) ≤ ⁅K₁, K₁⁆ := hBE ▸ inf_le_left
      have hED : centerMod (yamadaV₁ d t) (K₁ᵍ[t]) ≤ yamadaD₅ d t := hBE ▸ inf_le_right
      have hf4 : 4 ≤ Nat.card d.Γ := by
        rw [d.card_Γ]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hp.two_le
          _ ≤ (2 ^ f) ^ 3 := Nat.le_self_pow (by norm_num) _
      haveI : IsSimpleGroup SL(2, d.Γ) := sl2_isSimpleGroup_of_charTwo hf4
      have hT : ¬ IsPGroup 2 SL(2, d.Γ) := not_isPGroup_sl2 d hp.two_le
      obtain ⟨φ₁, hφ₁, hker₁⟩ := hK₁.iso
      have hK₁K' : K₁ ≤ normalizer ((⁅K₁, K₁⁆ : Subgroup G) : Set G) := fun x hx =>
        Setup.normalizer_le_normalizer_commutator_C8 K₁ (le_normalizer hx)
      let ψ : ↥⁅K₁, K₁⁆ →* SL(2, d.Γ) := φ₁.comp (Subgroup.inclusion hK'K)
      have hψ : Function.Surjective ψ := by
        intro s
        obtain ⟨k, hk⟩ := hφ₁ s
        have hkmem : (k : G) ∈ ((⁅K₁, K₁⁆ : Subgroup G) : Set G) * (yamadaD₅ d t : Set G) := by
          rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _
            (fun x hx => hK₁K' (hK₁.D₅_le hx))]
          rw [← hKeq]
          exact k.2
        obtain ⟨b, hb, δ, hδ, hbδ⟩ := Set.mem_mul.1 hkmem
        refine ⟨⟨b, hb⟩, ?_⟩
        have hδK : δ ∈ K₁ := hK₁.D₅_le hδ
        have h1 : φ₁ ⟨δ, hδK⟩ = 1 := by
          have : (⟨δ, hδK⟩ : ↥K₁) ∈ φ₁.ker := by
            rw [hker₁]
            exact mem_subgroupOf.2 hδ
          exact this
        have hk' : k = ⟨b, hK'K hb⟩ * ⟨δ, hδK⟩ := Subtype.ext hbδ.symm
        show φ₁ ⟨b, hK'K hb⟩ = s
        rw [← hk, hk', map_mul, h1, mul_one]
      have hψk : ψ.ker = (centerMod (yamadaV₁ d t) (K₁ᵍ[t])).subgroupOf ⁅K₁, K₁⁆ := by
        ext x
        rw [MonoidHom.mem_ker, mem_subgroupOf, ← hBE]
        show φ₁ (Subgroup.inclusion hK'K x) = 1 ↔ _
        rw [← MonoidHom.mem_ker, hker₁, mem_subgroupOf, Subgroup.mem_inf]
        exact ⟨fun h1 => ⟨x.2, h1⟩, fun h1 => h1.2⟩
      have hP2 : IsPGroup 2 (yamadaP d t) := by
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        refine IsPGroup.of_card (n := 24 * f) ?_
        rw [(T4_series_free h d hp).2.2.2.2.2.2.2.2.2.1, ← pow_mul, mul_comm]
      have hE2 : IsPGroup 2 (centerMod (yamadaV₁ d t) (K₁ᵍ[t])) :=
        hP2.to_le (hED.trans (yamadaD₅_le_yamadaP d t))
      exact pCoreOf_eq_of_quotient hT ψ hψ hψk hE2 hEB

end Export

end ProductN1Aux

section Statements

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

theorem E1_char_D5 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K₁ : Subgroup G} (hK₁ : IsN1Factor d t K₁) :
    yamadaP d t ⊓ centralizerMod (yamadaV₁ d t) (yamadaW₃ d t) = yamadaD₅ d t ∧
      ((yamadaD₅ d t).subgroupOf (yamadaP d t)).Characteristic ∧
      normalizer ((yamadaP d t : Subgroup G) : Set G) ≤
        normalizer ((yamadaD₅ d t : Subgroup G) : Set G) :=
  ProductN1Aux.E1_core h d hp

theorem E2_decomposition (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K₁ : Subgroup G} (hK₁ : IsN1Factor d t K₁) :
    (nOne d t = ⁅K₁, K₁⁆ ⊔ (⁅K₁, K₁⁆)ᵍ[t] ∧ ⁅K₁, K₁⁆ ⊓ (⁅K₁, K₁⁆)ᵍ[t] = yamadaV₁ d t ∧
      ⁅⁅K₁, K₁⁆, (⁅K₁, K₁⁆)ᵍ[t]⁆ ≤ yamadaV₁ d t ∧
      SectionIso ⁅K₁, K₁⁆ (yamadaV₁ d t) (cLV d) (d.V.map L.subtype)) ∧
    (yamadaD₅ d t = centerMod (yamadaV₁ d t) (K₁ᵍ[t]) ⊔ (centerMod (yamadaV₁ d t) (K₁ᵍ[t]))ᵍ[t] ∧
      centerMod (yamadaV₁ d t) (K₁ᵍ[t]) ⊓ (centerMod (yamadaV₁ d t) (K₁ᵍ[t]))ᵍ[t] =
        yamadaV₁ d t ∧
      (yamadaV₁ d t).relIndex (centerMod (yamadaV₁ d t) (K₁ᵍ[t])) = (2 ^ f) ^ 8 ∧
      centerMod (yamadaV₁ d t) (K₁ᵍ[t]) = pCoreOf 2 ⁅K₁, K₁⁆) :=
  ProductN1Aux.e2_core h d hp hK₁

theorem E3_commutators (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hp : ProductHyp h d)
    {K₁ : Subgroup G} (hK₁ : IsN1Factor d t K₁) :
    (yamadaV₁ d t ≤ ⁅K₁, K₁⁆ ∧ yamadaV₁ d t ≤ zc (nOne d t)) ∧
    (nOne d t = ⁅K₁, K₁⁆ ⊔ (⁅K₁, K₁⁆)ᵍ[t] ∧ ⁅⁅K₁, K₁⁆, (⁅K₁, K₁⁆)ᵍ[t]⁆ ≤ yamadaV₁ d t ∧
      ⁅K₁, K₁⁆ = ⁅⁅K₁, K₁⁆, ⁅K₁, K₁⁆⁆ ⊔ yamadaV₁ d t ∧
      ⁅⁅⁅K₁, K₁⁆, ⁅K₁, K₁⁆⁆, (⁅⁅K₁, K₁⁆, ⁅K₁, K₁⁆⁆)ᵍ[t]⁆ = ⊥) := by
  have hlay := hp.layer
  have hy := h.l6Hyps d hlay
  obtain ⟨⟨hN, hinf, hcomm, hsec⟩, -⟩ := E2_decomposition h d hp hK₁
  have hV₁K' : yamadaV₁ d t ≤ ⁅K₁, K₁⁆ := hinf ▸ inf_le_left
  have hK₁N : K₁ ≤ nOne d t := hK₁.sup_eq ▸ le_sup_left
  have hK₁tN : K₁ᵍ[t] ≤ nOne d t := hK₁.sup_eq ▸ le_sup_right
  have hNN : nOne d t ≤ normalizer (yamadaD₅ d t : Set G) :=
    NormalizerQuotient.lift_le_normalizer _
  have h525 : ⁅yamadaD₅ d t, yamadaD₅ d t⁆ = yamadaV₁ d t :=
    (h.yamada_5_25 d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593 hy.h5101 hy.h5102 hy.h59e
      hy.h520 hy.h5221 hy.h521).1
  have hNV : normalizer (yamadaD₅ d t : Set G) ≤ normalizer (yamadaV₁ d t : Set G) :=
    fun g hg => by
      have := Setup.normalizer_le_normalizer_commutator_C8 (yamadaD₅ d t) hg
      rwa [h525] at this
  obtain ⟨φ, hφ, hker⟩ := hK₁.iso
  have hK₁cen : K₁ ≤ centralizer (yamadaV₁ d t : Set G) := by
    have hf2 := hp.two_le
    refine ProductN1Aux.le_centralizer_of_sl2_quotient (m := f * 3) (d := f * 2) ?_ (by omega)
      (by omega)
      (fun x hx => hNV (hNN (hK₁N hx))) (inf_le_right : yamadaD₅ d t ≤ _) φ hφ hker ?_ (by omega)
    · rw [d.card_Γ, ← pow_mul]
    · rw [hy.h562.2.1, ← pow_mul]
  have hK₁tcen : K₁ᵍ[t] ≤ centralizer (yamadaV₁ d t : Set G) := by
    rintro _ ⟨k, hk, rfl⟩
    have htV₁ : t ∈ normalizer (yamadaV₁ d t : Set G) := h.t_mem_normalizer_yamadaV₁ d
    rw [mem_centralizer_iff]
    intro v hv
    have hv' : t * v * t⁻¹ ∈ yamadaV₁ d t := (mem_normalizer_iff.1 htV₁ v).1 hv
    have := mem_centralizer_iff.1 (hK₁cen hk) _ hv'
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc v * (t⁻¹ * k * t) = t⁻¹ * ((t * v * t⁻¹) * k) * t := by group
      _ = t⁻¹ * (k * (t * v * t⁻¹)) * t := by rw [this]
      _ = (t⁻¹ * k * t) * v := by group
  have hV₁cenN : yamadaV₁ d t ≤ centralizer ((nOne d t : Subgroup G) : Set G) := by
    intro v hv
    rw [mem_centralizer_iff]
    intro x hx
    have hxsup : x ∈ K₁ ⊔ K₁ᵍ[t] := hK₁.sup_eq ▸ hx
    have hle : K₁ ⊔ K₁ᵍ[t] ≤ centralizer ({v} : Set G) :=
      sup_le (fun k hk => mem_centralizer_singleton_iff.2
        (mem_centralizer_iff.1 (hK₁cen hk) v hv).symm)
        (fun k hk => mem_centralizer_singleton_iff.2
        (mem_centralizer_iff.1 (hK₁tcen hk) v hv).symm)
    exact mem_centralizer_singleton_iff.1 (hle hxsup)
  have hK'N : ⁅K₁, K₁⁆ ≤ nOne d t := commutator_le_of_le hK₁N hK₁N
  have hV₁N : yamadaV₁ d t ≤ nOne d t := hV₁K'.trans hK'N
  have hK'tN : (⁅K₁, K₁⁆)ᵍ[t] ≤ nOne d t :=
    (Subgroup.map_mono (commutator_le_of_le le_rfl le_rfl)).trans hK₁tN
  refine ⟨⟨hV₁K', le_inf hV₁N hV₁cenN⟩, hN, hcomm, ?_, ?_⟩
  ·
    obtain ⟨hn1, hn2, ⟨e⟩⟩ := hsec
    haveI := hn1
    have hcLV : Group.IsPerfect ↥(cLV d) := Subgroup.isPerfect_iff.mpr (ProductN1Aux.cLV_perfect d)
    haveI := hcLV
    have hq : Group.IsPerfect (↥(cLV d) ⧸ (d.V.map L.subtype).subgroupOf (cLV d)) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    haveI := hq
    have hq' : Group.IsPerfect (↥⁅K₁, K₁⁆ ⧸ (yamadaV₁ d t).subgroupOf ⁅K₁, K₁⁆) :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact ProductN1Aux.eq_commutator_sup_of_perfect_quotient hV₁K' hq'
  · rw [Subgroup.map_commutator]
    exact ProductN1Aux.commutator_commutator_eq_bot_of_central hK'N hK'tN hcomm hV₁cenN

end Statements

end CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
