module

public import CFSG.GH74.GLS.SP.Local.SPLOrdG3
public import CFSG.GH74.GLS.SP.Local.SPLCtStage
public import CFSG.GH74.GLS.SP.Local.SPLCtS2C
public import CFSG.GH74.GLS.SP.Local.SPLCtSD

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

section Ct0

variable {G : Type} [Group G] [Finite G] (D : SPLNot1 G)

@[expose] def SPLNot1.ext3 (D : SPLNot1 G) : SPLNot3 G :=
  { toSPLNot2 := { toSPLNot1 := D, A := ⊥, I := ⊥, x := 1 }, X₁ := ⊥, X₁' := ⊥, Y₁ := ⊥, a := 1 }

@[expose] noncomputable def SPLNot1.dg (D : SPLNot1 G) (hs : SPLSetup D.toSPLNot0) : ↥D.K₁ →* G :=
  diagHom D.ext3 hs

omit [Finite G] in
theorem zpow_z_cases' (hs : SPLSetup D.toSPLNot0) (j : ℤ) : D.z ^ j = 1 ∨ D.z ^ j = D.z :=
  zpow_z_cases D.ext3 hs j

omit [Finite G] in
theorem t_mul_t' (hs : SPLSetup D.toSPLNot0) : D.t * D.t = 1 := t_mul_t D.ext3 hs

omit [Finite G] in
theorem z_mul_z' (hs : SPLSetup D.toSPLNot0) : D.z * D.z = 1 := z_mul_z D.ext3 hs

theorem z_comm_t' (hs : SPLSetup D.toSPLNot0) : D.z * D.t = D.t * D.z := z_comm_t D.ext3 hs

theorem t_conj_K₁' (hs : SPLSetup D.toSPLNot0) : ∀ x ∈ D.K₁, D.t * x * D.t⁻¹ ∈ D.K₂ :=
  t_conj_K₁ D.ext3 hs

theorem t_conj_K₂' (hs : SPLSetup D.toSPLNot0) : ∀ x ∈ D.K₂, D.t * x * D.t⁻¹ ∈ D.K₁ :=
  t_conj_K₂ D.ext3 hs

omit [Finite G] in
theorem z_mem_K₁' (hs : SPLSetup D.toSPLNot0) : D.z ∈ D.K₁ := z_mem_K₁ (D := D.toSPLNot0) hs

omit [Finite G] in
theorem z_mem_K₂' (hs : SPLSetup D.toSPLNot0) : D.z ∈ D.K₂ := z_mem_K₂ (D := D.toSPLNot0) hs

omit [Finite G] in
theorem z_mem_K' (hs : SPLSetup D.toSPLNot0) : D.z ∈ D.K := Subgroup.mem_sup_left (z_mem_K₁' D hs)

omit [Finite G] in
theorem z_ne_one' (hs : SPLSetup D.toSPLNot0) : D.z ≠ 1 := z_ne_one D.ext3 hs

theorem dg_apply (hs : SPLSetup D.toSPLNot0) (k : ↥D.K₁) :
    D.dg hs k = (k : G) * (D.t * k * D.t⁻¹) := rfl

theorem dg_ker_iff (hs : SPLSetup D.toSPLNot0) (k : ↥D.K₁) :
    D.dg hs k = 1 ↔ (k : G) ∈ zpowers D.z := by
  constructor
  · intro hk
    exact mem_zpowers_of_mem_ker_diagHom D.ext3 hs (k := k) hk
  · intro hk
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hk
    rcases zpow_z_cases' D hs j with h | h
    · have : k = 1 := Subtype.ext (by rw [← hj, h]; rfl)
      rw [this, map_one]
    · have : k = ⟨D.z, z_mem_K₁' D hs⟩ := Subtype.ext (by rw [← hj, h])
      rw [this]
      exact diagHom_z D.ext3 hs

theorem dg_range_le (hs : SPLSetup D.toSPLNot0) : (D.dg hs).range ≤ D.Ct ⊓ D.K :=
  diagHom_range_le D.ext3 hs

theorem CK_eq (hs : SPLSetup D.toSPLNot0) : D.Ct ⊓ D.K = (D.dg hs).range ⊔ zpowers D.z := by
  have htt := t_mul_t' D hs
  apply le_antisymm
  · rintro κ ⟨hκC, hκK⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hs.comps.comm hκK
    have hct : D.t * (a * b) = (a * b) * D.t := (mem_centralizer_singleton_iff.mp hκC).symm
    have ha'' : D.t * a * D.t⁻¹ ∈ D.K₂ := t_conj_K₁' D hs a ha
    have hb'' : D.t * b * D.t⁻¹ ∈ D.K₁ := t_conj_K₂' D hs b hb
    have hmain : (D.t * a * D.t⁻¹) * (D.t * b * D.t⁻¹) = a * b := by
      have : D.t * (a * b) * D.t⁻¹ = a * b := by rw [hct]; group
      rw [← this]; group
    have hc1 : (D.t * a * D.t⁻¹) * a = a * (D.t * a * D.t⁻¹) := (hs.comps.comm a ha _ ha'').symm
    have hc3 : (D.t * b * D.t⁻¹) * (D.t * a * D.t⁻¹) = (D.t * a * D.t⁻¹) * (D.t * b * D.t⁻¹) :=
      hs.comps.comm _ hb'' _ ha''
    have hw1 : a⁻¹ * (D.t * b * D.t⁻¹) ∈ D.K₁ := D.K₁.mul_mem (D.K₁.inv_mem ha) hb''
    have hw2 : a⁻¹ * (D.t * b * D.t⁻¹) = ((D.t * a * D.t⁻¹) * b⁻¹)⁻¹ := by
      have e1 : a⁻¹ * (D.t * b * D.t⁻¹) * ((D.t * a * D.t⁻¹) * b⁻¹) = 1 := by
        calc a⁻¹ * (D.t * b * D.t⁻¹) * ((D.t * a * D.t⁻¹) * b⁻¹)
            = a⁻¹ * ((D.t * b * D.t⁻¹) * (D.t * a * D.t⁻¹)) * b⁻¹ := by group
          _ = a⁻¹ * ((D.t * a * D.t⁻¹) * (D.t * b * D.t⁻¹)) * b⁻¹ := by rw [hc3]
          _ = a⁻¹ * (a * b) * b⁻¹ := by rw [hmain]
          _ = 1 := by group
      exact eq_inv_of_mul_eq_one_left e1
    have hw3 : a⁻¹ * (D.t * b * D.t⁻¹) ∈ D.K₂ := by
      rw [hw2]
      exact D.K₂.inv_mem (D.K₂.mul_mem ha'' (D.K₂.inv_mem hb))
    have hwz : a⁻¹ * (D.t * b * D.t⁻¹) ∈ zpowers D.z := by
      rw [← hs.comps.inf_eq]; exact ⟨hw1, hw3⟩
    have hab : a * b = (a * (D.t * a * D.t⁻¹)) * (a⁻¹ * (D.t * b * D.t⁻¹)) := by
      calc a * b = (D.t * a * D.t⁻¹) * (D.t * b * D.t⁻¹) := hmain.symm
        _ = (a * (D.t * a * D.t⁻¹) * a⁻¹) * (D.t * b * D.t⁻¹) := by
            have : a * (D.t * a * D.t⁻¹) * a⁻¹ = D.t * a * D.t⁻¹ := by
              rw [← hc1]; group
            rw [this]
        _ = (a * (D.t * a * D.t⁻¹)) * (a⁻¹ * (D.t * b * D.t⁻¹)) := by group
    rw [hab]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨⟨a, ha⟩, rfl⟩) (Subgroup.mem_sup_right hwz)
  · refine sup_le (dg_range_le D hs) ?_
    rw [zpowers_le]
    exact ⟨mem_centralizer_singleton_iff.mpr (z_comm_t' D hs), z_mem_K' D hs⟩

theorem dg_range_inf_Z (hs : SPLSetup D.toSPLNot0) : (D.dg hs).range ⊓ zpowers D.z = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨⟨k, rfl⟩, hz⟩
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hz
  rcases zpow_z_cases' D hs j with h | h
  · rw [← hj, h]; exact one_mem _
  · exfalso
    have h1 : D.dg hs k = D.z := by rw [← hj, h]
    have h2 : (k : G) * (D.t * k * D.t⁻¹) = D.z := h1
    have hkK₂ : (k : G) ∈ D.K₂ := by
      have : (k : G) = D.z * (D.t * k * D.t⁻¹)⁻¹ := by
        rw [← h2]; group
      rw [this]
      exact D.K₂.mul_mem (z_mem_K₂' D hs) (D.K₂.inv_mem (t_conj_K₁' D hs k k.2))
    have hkz : (k : G) ∈ zpowers D.z := by rw [← hs.comps.inf_eq]; exact ⟨k.2, hkK₂⟩
    have h3 : D.dg hs k = 1 := (dg_ker_iff D hs k).mpr hkz
    exact z_ne_one' D hs (by rw [← h1, h3])

omit [Finite G] in
theorem spl_commutator_mul_of_central {K : Type*} [Group K] {r₁ r₂ w₁ w₂ : K}
    (h1 : Commute w₁ r₂) (h2 : Commute w₂ r₁) (h3 : Commute w₁ w₂) :
    ⁅r₁ * w₁, r₂ * w₂⁆ = ⁅r₁, r₂⁆ := by
  have h2' : Commute w₂ r₁⁻¹ := h2.inv_right
  calc ⁅r₁ * w₁, r₂ * w₂⁆
      = r₁ * (w₁ * r₂) * w₂ * w₁⁻¹ * r₁⁻¹ * w₂⁻¹ * r₂⁻¹ := by
        simp only [commutatorElement_def, mul_inv_rev]; group
    _ = r₁ * (r₂ * w₁) * w₂ * w₁⁻¹ * r₁⁻¹ * w₂⁻¹ * r₂⁻¹ := by rw [h1.eq]
    _ = r₁ * r₂ * (w₁ * w₂ * w₁⁻¹) * r₁⁻¹ * w₂⁻¹ * r₂⁻¹ := by group
    _ = r₁ * r₂ * w₂ * r₁⁻¹ * w₂⁻¹ * r₂⁻¹ := by
        rw [h3.eq]; group
    _ = r₁ * r₂ * (w₂ * r₁⁻¹) * w₂⁻¹ * r₂⁻¹ := by group
    _ = r₁ * r₂ * (r₁⁻¹ * w₂) * w₂⁻¹ * r₂⁻¹ := by rw [h2'.eq]
    _ = ⁅r₁, r₂⁆ := by simp only [commutatorElement_def]; group

omit [Finite G] in
theorem z_central_in_K (hs : SPLSetup D.toSPLNot0) {w : G} (hw : w ∈ zpowers D.z) :
    ∀ x ∈ D.K, w * x = x * w := by
  intro x hx
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hw
  exact (Commute.zpow_left (show Commute D.z x from z_cen_K D.ext3 hs x hx) j).eq

theorem Ict_eq (hs : SPLSetup D.toSPLNot0) : D.Ict = (D.dg hs).range := by
  have hperf : ⁅(⊤ : Subgroup ↥D.K₁), (⊤ : Subgroup ↥D.K₁)⁆ = ⊤ := by
    have := hs.comps.quasi₁.1
    rw [← commutator_def]
    exact this.commutator_eq_top
  have hrangeK : ∀ r ∈ (D.dg hs).range, r ∈ D.K := fun r hr => (dg_range_le D hs hr).2
  have hcommr : ⁅(D.dg hs).range, (D.dg hs).range⁆ ≤ (D.dg hs).range := by
    rw [commutator_le]
    intro x hx y hy
    obtain ⟨k₁, rfl⟩ := hx
    obtain ⟨k₂, rfl⟩ := hy
    exact ⟨⁅k₁, k₂⁆, by simp [map_commutatorElement]⟩
  unfold SPLNot1.Ict
  rw [CK_eq D hs]
  apply le_antisymm
  · rw [commutator_le]
    intro g hg h hh
    have hc : ∀ a ∈ (D.dg hs).range, ∀ b ∈ zpowers D.z, a * b = b * a := fun a ha b hb =>
      (z_central_in_K D hs hb a (hrangeK a ha)).symm
    obtain ⟨r₁, hr₁, w₁, hw₁, rfl⟩ := mem_sup_of_commute hc hg
    obtain ⟨r₂, hr₂, w₂, hw₂, rfl⟩ := mem_sup_of_commute hc hh
    have hw₂K : w₂ ∈ D.K := by
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hw₂
      exact Subgroup.zpow_mem _ (z_mem_K' D hs) _
    rw [spl_commutator_mul_of_central (z_central_in_K D hs hw₁ r₂ (hrangeK r₂ hr₂))
      (z_central_in_K D hs hw₂ r₁ (hrangeK r₁ hr₁))
      (z_central_in_K D hs hw₁ w₂ hw₂K)]
    exact hcommr (Subgroup.commutator_mem_commutator hr₁ hr₂)
  · have hrange : (D.dg hs).range = ⁅(D.dg hs).range, (D.dg hs).range⁆ := by
      rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hperf]
    calc (D.dg hs).range = ⁅(D.dg hs).range, (D.dg hs).range⁆ := hrange
      _ ≤ ⁅(D.dg hs).range ⊔ zpowers D.z, (D.dg hs).range ⊔ zpowers D.z⁆ :=
        commutator_mono le_sup_left le_sup_left

theorem Ict_le (hs : SPLSetup D.toSPLNot0) : D.Ict ≤ D.Ct ⊓ D.K := by
  rw [Ict_eq D hs]; exact dg_range_le D hs

theorem Ict_le_K (hs : SPLSetup D.toSPLNot0) : D.Ict ≤ D.K := (Ict_le D hs).trans inf_le_right

theorem Ict_le_Ct (hs : SPLSetup D.toSPLNot0) : D.Ict ≤ D.Ct := (Ict_le D hs).trans inf_le_left

theorem Ict_perfect (hs : SPLSetup D.toSPLNot0) : ⁅D.Ict, D.Ict⁆ = D.Ict := by
  rw [Ict_eq D hs]; exact diagHom_range_perfect D.ext3 hs

theorem Ict_inf_z (hs : SPLSetup D.toSPLNot0) : D.Ict ⊓ zpowers D.z = ⊥ := by
  rw [Ict_eq D hs]; exact dg_range_inf_Z D hs

theorem Ict_isL2 (hs : SPLSetup D.toSPLNot0) : IVK.IsL2 ↥D.Ict (fun r => r = D.q) := by
  obtain ⟨F, hF, hfin, hq, ⟨e⟩⟩ := hs.comps.sl₁
  refine ⟨F, hF, hfin, hq, ⟨?_⟩⟩
  let μ : ↥D.K₁ →* IVK.L2 F := (IVK.L2.mk F).comp e.toMonoidHom
  have hμ : Function.Surjective μ := (QuotientGroup.mk'_surjective _).comp e.surjective
  have hcenter : center (StatedSL 2 F) = (StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F) := by
    rw [← map_center_eq_statedScalars 2 F]
    exact (Subgroup.map_center_eq (specialLinearGroupEquivStatedSL 2 F)).symm
  have hker : (D.dg hs).ker = μ.ker := by
    ext k
    have hc : k ∈ center ↥D.K₁ ↔ (k : G) ∈ zpowers D.z := mem_center_K₁_iff D.ext3 hs k
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, dg_ker_iff D hs, ← hc,
      ← mem_center_equiv_iff e, hcenter]
    exact (QuotientGroup.eq_one_iff (e k)).symm
  exact (MulEquiv.subgroupCongr (Ict_eq D hs)).trans
    ((QuotientGroup.quotientKerEquivRange (D.dg hs)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivOfSurjective μ hμ)))

omit [Finite G] in
theorem F_cen_S₁ : ∀ f ∈ D.F, ∀ s ∈ D.S₁, f * s = s * f := by
  intro f hf s hsS
  have h : f ∈ centralizer (D.S₁ : Set G) := TwoThin.pPrimeCoreOf_le _ hf
  exact (mem_centralizer_iff.mp h s hsS).symm

omit [Finite G] in
theorem mem_F₀_iff (f : G) : f ∈ D.F₀ ↔ f ∈ D.F ∧ f * D.t = D.t * f :=
  ⟨fun h => ⟨h.1, mem_centralizer_singleton_iff.mp h.2⟩,
    fun h => ⟨h.1, mem_centralizer_singleton_iff.mpr h.2⟩⟩

theorem t_mem_normalizer_F (hs : SPLSetup D.toSPLNot0) : D.t ∈ normalizer (D.F : Set G) := by
  have htt := t_mul_t' D hs
  rw [mem_normalizer_iff]
  intro f
  constructor
  · intro hf
    exact t_normalizes_F hs f hf
  · intro hf
    have h := t_normalizes_F hs _ hf
    have e : D.t * (D.t * f * D.t⁻¹) * D.t⁻¹ = f := by
      calc D.t * (D.t * f * D.t⁻¹) * D.t⁻¹ = (D.t * D.t) * f * (D.t * D.t)⁻¹ := by group
        _ = f := by rw [htt]; group
    rwa [e] at h

omit [Finite G] in
theorem zpow_t_comm {τ : G} (hτ : τ ∈ zpowers D.t) :
    τ * D.t = D.t * τ := by
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hτ
  exact ((Commute.refl D.t).zpow_left j).eq

theorem CCt_decomp (hs : SPLSetup D.toSPLNot0) {c : G} (hc : c ∈ D.C ⊓ D.Ct) :
    ∃ κ ∈ D.Ct ⊓ D.K, ∃ τ ∈ zpowers D.t, ∃ y ∈ D.F₀, c = κ * τ * y := by
  obtain ⟨hcC, hcCt⟩ := hc
  have hct : c * D.t = D.t * c := mem_centralizer_singleton_iff.mp hcCt
  obtain ⟨k, hk, s, hsS, y, hyF, rfl⟩ := hs.gen c hcC
  have hsKt : s ∈ D.K ⊔ zpowers D.t := S_le_Kt D.ext3 hs hsS
  obtain ⟨κ', hκ', τ, hτ, rfl⟩ := mem_sup_of_le_normalizer (t_le_normalizer_K D.ext3 hs) hsKt
  have hκK : k * κ' ∈ D.K := D.K.mul_mem hk hκ'
  have hτt : τ * D.t = D.t * τ := zpow_t_comm D hτ
  have hτN : τ ∈ normalizer (D.F : Set G) :=
    (Subgroup.zpowers_le.mpr (t_mem_normalizer_F D hs)) hτ
  have hy' : D.t * y * D.t⁻¹ ∈ D.F := t_normalizes_F hs y hyF
  have hτ' : D.t * τ * D.t⁻¹ = τ := by
    calc D.t * τ * D.t⁻¹ = (τ * D.t) * D.t⁻¹ := by rw [hτt]
      _ = τ := by group
  have hKt : (k * κ') ⁻¹ * (D.t * (k * κ') * D.t⁻¹) = τ * (y * (D.t * y * D.t⁻¹)⁻¹) * τ⁻¹ := by
    have h1 : (D.t * (k * κ') * D.t⁻¹) * τ * (D.t * y * D.t⁻¹) = (k * κ') * τ * y := by
      calc (D.t * (k * κ') * D.t⁻¹) * τ * (D.t * y * D.t⁻¹)
          = (D.t * (k * κ') * D.t⁻¹) * (D.t * τ * D.t⁻¹) * (D.t * y * D.t⁻¹) := by rw [hτ']
        _ = D.t * ((k * κ') * τ * y) * D.t⁻¹ := by group
        _ = D.t * (D.t⁻¹ * ((k * κ') * τ * y) * D.t) * D.t⁻¹ := by
            have : (k * κ') * τ * y = D.t⁻¹ * (D.t * ((k * κ') * τ * y)) := by group
            have h2 : D.t * ((k * κ') * τ * y) = ((k * κ') * τ * y) * D.t := by
              have := hct
              calc D.t * ((k * κ') * τ * y) = D.t * (k * (κ' * τ) * y) := by group
                _ = (k * (κ' * τ) * y) * D.t := this.symm
                _ = ((k * κ') * τ * y) * D.t := by group
            rw [h2]; group
        _ = (k * κ') * τ * y := by group
    calc (k * κ')⁻¹ * (D.t * (k * κ') * D.t⁻¹)
        = (k * κ')⁻¹ * ((D.t * (k * κ') * D.t⁻¹) * τ * (D.t * y * D.t⁻¹)) *
            (D.t * y * D.t⁻¹)⁻¹ * τ⁻¹ := by group
      _ = (k * κ')⁻¹ * ((k * κ') * τ * y) * (D.t * y * D.t⁻¹)⁻¹ * τ⁻¹ := by rw [h1]
      _ = τ * (y * (D.t * y * D.t⁻¹)⁻¹) * τ⁻¹ := by group
  have hL : (k * κ')⁻¹ * (D.t * (k * κ') * D.t⁻¹) ∈ D.K :=
    D.K.mul_mem (D.K.inv_mem hκK) (t_normalizes_K hs _ hκK)
  have hR : τ * (y * (D.t * y * D.t⁻¹)⁻¹) * τ⁻¹ ∈ D.F :=
    (mem_normalizer_iff.mp hτN _).mp (D.F.mul_mem hyF (D.F.inv_mem hy'))
  have h0 : (k * κ')⁻¹ * (D.t * (k * κ') * D.t⁻¹) = 1 := by
    have hmem : (k * κ')⁻¹ * (D.t * (k * κ') * D.t⁻¹) ∈ D.F ⊓ D.K := ⟨hKt ▸ hR, hL⟩
    rw [F_inf_K_eq hs] at hmem
    exact Subgroup.mem_bot.mp hmem
  have h0' : y * (D.t * y * D.t⁻¹)⁻¹ = 1 := by
    have : τ * (y * (D.t * y * D.t⁻¹)⁻¹) * τ⁻¹ = 1 := hKt ▸ h0
    have h3 : y * (D.t * y * D.t⁻¹)⁻¹ = τ⁻¹ * 1 * τ := by
      calc y * (D.t * y * D.t⁻¹)⁻¹ = τ⁻¹ * (τ * (y * (D.t * y * D.t⁻¹)⁻¹) * τ⁻¹) * τ := by group
        _ = τ⁻¹ * 1 * τ := by rw [this]
    rw [h3]; group
  refine ⟨k * κ', ⟨?_, hκK⟩, τ, hτ, y, ?_, by group⟩
  · apply mem_centralizer_singleton_iff.mpr
    have : D.t * (k * κ') * D.t⁻¹ = k * κ' := by
      calc D.t * (k * κ') * D.t⁻¹ = (k * κ') * ((k * κ')⁻¹ * (D.t * (k * κ') * D.t⁻¹)) := by group
        _ = k * κ' := by rw [h0, mul_one]
    calc (k * κ') * D.t = (D.t * (k * κ') * D.t⁻¹) * D.t := by rw [this]
      _ = D.t * (k * κ') := by group
  · refine (mem_F₀_iff D y).mpr ⟨hyF, ?_⟩
    have : D.t * y * D.t⁻¹ = y := by
      have h4 : y = D.t * y * D.t⁻¹ := by
        calc y = (y * (D.t * y * D.t⁻¹)⁻¹) * (D.t * y * D.t⁻¹) := by group
          _ = D.t * y * D.t⁻¹ := by rw [h0', one_mul]
      exact h4.symm
    calc y * D.t = (D.t * y * D.t⁻¹) * D.t := by rw [this]
      _ = D.t * y := by group

theorem CCt_eq (hs : SPLSetup D.toSPLNot0) :
    D.C ⊓ D.Ct = (zpowers D.z ⊔ zpowers D.t) ⊔ (D.Ict ⊔ D.F₀) := by
  apply le_antisymm
  · intro c hc
    obtain ⟨κ, hκ, τ, hτ, y, hy, rfl⟩ := CCt_decomp D hs hc
    have hκ' : κ ∈ D.Ict ⊔ zpowers D.z := by
      have := hκ; rw [CK_eq D hs, ← Ict_eq D hs] at this; exact this
    have hκJ : κ ∈ (zpowers D.z ⊔ zpowers D.t) ⊔ (D.Ict ⊔ D.F₀) := by
      refine (sup_le ?_ ?_ : D.Ict ⊔ zpowers D.z ≤ _) hκ'
      · exact le_trans le_sup_left le_sup_right
      · exact le_trans le_sup_left le_sup_left
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hκJ
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right hτ)))
      (Subgroup.mem_sup_right (Subgroup.mem_sup_right hy))
  · refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
    · rw [zpowers_le]
      exact ⟨mem_centralizer_singleton_iff.mpr rfl, mem_centralizer_singleton_iff.mpr (z_comm_t' D hs)⟩
    · rw [zpowers_le]
      exact ⟨t_mem_Cz hs, mem_centralizer_singleton_iff.mpr rfl⟩
    · exact le_inf ((Ict_le_K D hs).trans (K_le_C D.ext3 hs)) (Ict_le_Ct D hs)
    · exact le_inf (inf_le_left.trans (F_le_C hs)) inf_le_right

omit [Finite G] in
theorem zpow_t_cases (hs : SPLSetup D.toSPLNot0) (j : ℤ) : D.t ^ j = 1 ∨ D.t ^ j = D.t := by
  have htt := t_mul_t' D hs
  rcases Int.even_or_odd' j with ⟨m, rfl | rfl⟩
  · left; rw [zpow_mul, zpow_two, htt, one_zpow]
  · right
    have h2 : D.t ^ (2 * m) = 1 := by rw [zpow_mul, zpow_two, htt, one_zpow]
    rw [zpow_add_one, h2, one_mul]

omit [Finite G] in
theorem F₀_le_F : D.F₀ ≤ D.F := inf_le_left

theorem F₀_odd : Odd (Nat.card ↥D.F₀) := by
  have h1 : Nat.card ↥D.F₀ ∣ Nat.card ↥D.F := Subgroup.card_dvd_of_le (F₀_le_F D)
  have h2 : Odd (Nat.card ↥D.F) := TwoThin.card_pPrimeCoreOf_odd _
  exact Odd.of_dvd_nat h2 h1

theorem F₀_norm (hs : SPLSetup D.toSPLNot0) :
    ∀ f ∈ D.F₀, ∀ i ∈ D.Ict, f * i * f⁻¹ ∈ D.Ict := by
  intro f hf i hi
  rw [Ict_eq D hs] at hi ⊢
  obtain ⟨k, rfl⟩ := hi
  have hfF : f ∈ D.F := hf.1
  have hft : f * D.t = D.t * f := ((mem_F₀_iff D f).mp hf).2
  have hk : f * (k : G) * f⁻¹ ∈ D.K₁ := F_normalizes_K₁ hs f hfF k k.2
  refine ⟨⟨f * k * f⁻¹, hk⟩, ?_⟩
  show (f * k * f⁻¹) * (D.t * (f * k * f⁻¹) * D.t⁻¹) = f * (k * (D.t * k * D.t⁻¹)) * f⁻¹
  have hc : Commute D.t f := hft.symm
  have h1 : D.t * f = f * D.t := hc.eq
  have h2 : D.t⁻¹ * f⁻¹ = f⁻¹ * D.t⁻¹ := hc.inv_inv.eq
  have : D.t * (f * k * f⁻¹) * D.t⁻¹ = f * (D.t * k * D.t⁻¹) * f⁻¹ := by
    calc D.t * (f * k * f⁻¹) * D.t⁻¹ = (D.t * f) * k * (f⁻¹ * D.t⁻¹) := by group
      _ = (f * D.t) * k * (D.t⁻¹ * f⁻¹) := by rw [h1, ← h2]
      _ = f * (D.t * k * D.t⁻¹) * f⁻¹ := by group
  rw [this]; group

theorem F₀_le_normalizer_I (hs : SPLSetup D.toSPLNot0) : D.F₀ ≤ normalizer (D.Ict : Set G) := by
  intro f hf
  rw [mem_normalizer_iff]
  intro i
  constructor
  · intro hi; exact F₀_norm D hs f hf i hi
  · intro hi
    have h := F₀_norm D hs f⁻¹ (D.F₀.inv_mem hf) _ hi
    have e : f⁻¹ * (f * i * f⁻¹) * f⁻¹⁻¹ = i := by group
    rwa [e] at h

theorem F₀_inf_I (hs : SPLSetup D.toSPLNot0) : D.F₀ ⊓ D.Ict = ⊥ := by
  rw [eq_bot_iff]
  intro x ⟨hxF₀, hxI⟩
  have h : x ∈ D.F ⊓ D.K := ⟨hxF₀.1, Ict_le_K D hs hxI⟩
  rw [F_inf_K_eq hs] at h
  exact h

omit [Finite G] in
theorem K₁_perfect (hs : SPLSetup D.toSPLNot0) : ⁅D.K₁, D.K₁⁆ = D.K₁ := by
  have h : ⁅(⊤ : Subgroup ↥D.K₁), (⊤ : Subgroup ↥D.K₁)⁆ = ⊤ := by
    rw [← commutator_def]; exact hs.comps.quasi₁.1.commutator_eq_top
  have h2 := congrArg (Subgroup.map D.K₁.subtype) h
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
  exact h2

theorem F₀_faith (hs : SPLSetup D.toSPLNot0) :
    ∀ f ∈ D.F₀, (∀ i ∈ D.Ict, f * i = i * f) → f = 1 := by
  intro f hf hcomm
  have hfF : f ∈ D.F := hf.1
  have hft : f * D.t = D.t * f := ((mem_F₀_iff D f).mp hf).2
  have hc : Commute D.t f := hft.symm
  have h1 : D.t * f = f * D.t := hc.eq
  have h2 : D.t⁻¹ * f⁻¹ = f⁻¹ * D.t⁻¹ := hc.inv_inv.eq
  have key : ∀ k ∈ D.K₁, f * k * f⁻¹ * k⁻¹ ∈ zpowers D.z := by
    intro k hk
    have hak : f * k * f⁻¹ ∈ D.K₁ := F_normalizes_K₁ hs f hfF k hk
    have hta : D.t * (f * k * f⁻¹) * D.t⁻¹ = f * (D.t * k * D.t⁻¹) * f⁻¹ := by
      calc D.t * (f * k * f⁻¹) * D.t⁻¹ = (D.t * f) * k * (f⁻¹ * D.t⁻¹) := by group
        _ = (f * D.t) * k * (D.t⁻¹ * f⁻¹) := by rw [h1, ← h2]
        _ = f * (D.t * k * D.t⁻¹) * f⁻¹ := by group
    have hIk : D.dg hs ⟨k, hk⟩ ∈ D.Ict := by
      rw [Ict_eq D hs]; exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    have hI : f * (D.dg hs ⟨k, hk⟩) = (D.dg hs ⟨k, hk⟩) * f := hcomm _ hIk
    have hga : D.dg hs ⟨f * k * f⁻¹, hak⟩ = D.dg hs ⟨k, hk⟩ := by
      calc D.dg hs ⟨f * k * f⁻¹, hak⟩ = f * (D.dg hs ⟨k, hk⟩) * f⁻¹ := by
            show (f * k * f⁻¹) * (D.t * (f * k * f⁻¹) * D.t⁻¹) = f * (k * (D.t * k * D.t⁻¹)) * f⁻¹
            rw [hta]; group
        _ = D.dg hs ⟨k, hk⟩ := by rw [hI]; group
    have h3 : D.dg hs (⟨f * k * f⁻¹, hak⟩ * (⟨k, hk⟩ : ↥D.K₁)⁻¹) = 1 := by
      rw [map_mul, map_inv, hga, mul_inv_cancel]
    exact (dg_ker_iff D hs _).mp h3
  have hzc : ∀ (j : ℤ) (x : G), x ∈ D.K → D.z ^ j * x = x * D.z ^ j := fun j x hx =>
    z_central_in_K D hs (zpow_mem (mem_zpowers D.z) j) x hx
  have hK₁ : ∀ k ∈ D.K₁, k * f = f * k := by
    have hcomm' : ⁅D.K₁, D.K₁⁆ ≤ centralizer ({f} : Set G) := by
      rw [commutator_le]
      intro a ha b hb
      rw [mem_centralizer_singleton_iff]
      have haK : a ∈ D.K := Subgroup.mem_sup_left ha
      have hbK : b ∈ D.K := Subgroup.mem_sup_left hb
      obtain ⟨j₁, hj₁⟩ := mem_zpowers_iff.mp (key a ha)
      obtain ⟨j₂, hj₂⟩ := mem_zpowers_iff.mp (key b hb)
      have ha' : f * a * f⁻¹ = a * D.z ^ j₁ := by
        calc f * a * f⁻¹ = (f * a * f⁻¹ * a⁻¹) * a := by group
          _ = D.z ^ j₁ * a := by rw [← hj₁]
          _ = a * D.z ^ j₁ := hzc j₁ a haK
      have hb' : f * b * f⁻¹ = b * D.z ^ j₂ := by
        calc f * b * f⁻¹ = (f * b * f⁻¹ * b⁻¹) * b := by group
          _ = D.z ^ j₂ * b := by rw [← hj₂]
          _ = b * D.z ^ j₂ := hzc j₂ b hbK
      have hzz : D.z ^ j₁ * D.z ^ j₂ = D.z ^ j₂ * D.z ^ j₁ := by
        rw [← zpow_add, ← zpow_add, add_comm]
      have hcf : f * ⁅a, b⁆ * f⁻¹ = ⁅a, b⁆ := by
        have e : f * ⁅a, b⁆ * f⁻¹ = ⁅f * a * f⁻¹, f * b * f⁻¹⁆ := by
          simp only [commutatorElement_def]; group
        rw [e, ha', hb']
        exact spl_commutator_mul_of_central (hzc j₁ b hbK) (hzc j₂ a haK) hzz
      calc ⁅a, b⁆ * f = (f * ⁅a, b⁆ * f⁻¹) * f := by rw [hcf]
        _ = f * ⁅a, b⁆ := by group
    intro k hk
    have hk' : k ∈ centralizer ({f} : Set G) := hcomm' (by rw [K₁_perfect D hs]; exact hk)
    exact mem_centralizer_singleton_iff.mp hk'
  have hK₂ : ∀ x ∈ D.K₂, x * f = f * x := by
    intro x hx
    have htt := t_mul_t' D hs
    have hk : D.t * x * D.t⁻¹ ∈ D.K₁ := t_conj_K₂' D hs x hx
    have hfk := hK₁ _ hk
    have hxe : D.t * (D.t * x * D.t⁻¹) * D.t⁻¹ = x := by
      calc D.t * (D.t * x * D.t⁻¹) * D.t⁻¹ = (D.t * D.t) * x * (D.t * D.t)⁻¹ := by group
        _ = x := by rw [htt]; group
    calc x * f = (D.t * (D.t * x * D.t⁻¹) * D.t⁻¹) * f := by rw [hxe]
      _ = D.t * ((D.t * x * D.t⁻¹) * (D.t⁻¹ * f)) := by group
      _ = D.t * ((D.t * x * D.t⁻¹) * (f * D.t⁻¹)) := by rw [hc.inv_left.eq]
      _ = D.t * (((D.t * x * D.t⁻¹) * f) * D.t⁻¹) := by group
      _ = D.t * ((f * (D.t * x * D.t⁻¹)) * D.t⁻¹) := by rw [hfk]
      _ = (D.t * f) * (D.t * x * D.t⁻¹) * D.t⁻¹ := by group
      _ = (f * D.t) * (D.t * x * D.t⁻¹) * D.t⁻¹ := by rw [h1]
      _ = f * (D.t * (D.t * x * D.t⁻¹) * D.t⁻¹) := by group
      _ = f * x := by rw [hxe]
  have hK : ∀ k ∈ D.K, f * k = k * f := by
    intro k hk
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hs.comps.comm hk
    calc f * (a * b) = (f * a) * b := by group
      _ = (a * f) * b := by rw [(hK₁ a ha).symm]
      _ = a * (f * b) := by group
      _ = a * (b * f) := by rw [(hK₂ b hb).symm]
      _ = a * b * f := by group
  exact eq_one_of_mem_F_cen_K hs hfF hK

theorem v2_of_two_mod_four (m : ℕ) (h : m % 4 = 2) : m.factorization 2 = 1 := by
  obtain ⟨k, hk⟩ : ∃ k, m = 2 * k := ⟨m / 2, by omega⟩
  have hk0 : k ≠ 0 := by omega
  have h1 : (2 * k).factorization 2 = 1 + k.factorization 2 := by
    rw [Nat.factorization_mul (by norm_num) hk0]
    simp [Nat.Prime.factorization_self Nat.prime_two]
  have h2 : k.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by omega)
  rw [hk, h1, h2]

theorem v2_pair (q : ℕ) (hq : q % 2 = 1) (h5 : 5 ≤ q) :
    (q ^ 2 - 1).factorization 2 = (if q % 4 = 1 then q - 1 else q + 1).factorization 2 + 1 := by
  have hsq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have h1 : 1 ≤ q := by omega
    zify [h1, Nat.one_le_pow 2 q (by omega)]
    ring_nf
  have hne1 : q - 1 ≠ 0 := by omega
  have hne2 : q + 1 ≠ 0 := by omega
  rw [hsq, Nat.factorization_mul hne1 hne2]
  simp only [Finsupp.add_apply]
  split_ifs with h
  · rw [v2_of_two_mod_four (q + 1) (by omega)]
  · rw [v2_of_two_mod_four (q - 1) (by omega)]; omega

omit [Finite G] in
theorem v2_q_sq_sub_one_eq_n (hs : SPLSetup D.toSPLNot0) : (D.q ^ 2 - 1).factorization 2 = D.n := by
  have h := v2_pair D.q (Nat.odd_iff.mp hs.odd_q) hs.q_ge
  unfold SPLNot0.n SPLNot0.d
  exact h

theorem I_simple (hs : SPLSetup D.toSPLNot0) : IsSimpleGroup ↥D.Ict := by
  obtain ⟨F, hF, hfin, hq, ⟨e⟩⟩ := Ict_isL2 D hs
  have h4 : 4 ≤ Nat.card F := by
    have hq' : Nat.card F = D.q := hq
    have := hs.q_ge; omega
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  exact (e.trans (IVK.L2.equivPSL F)).isSimpleGroup

omit [Finite G] in
theorem exists_eps (hs : SPLSetup D.toSPLNot0) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ((D.q : ℤ) ≡ ε [ZMOD 4]) ∧
      (((2 * (D.d / 2) : ℕ) : ℤ) = (D.q : ℤ) - ε) := by
  have hodd := hs.odd_q
  have h4 := four_dvd_d D.toSPLNot0 hodd
  obtain ⟨k, hk⟩ := hodd
  by_cases h : D.q % 4 = 1
  · refine ⟨1, Or.inl rfl, ?_, ?_⟩
    · show (D.q : ℤ) % 4 = 1 % 4
      omega
    · have hd : D.d = D.q - 1 := by unfold SPLNot0.d; simp [h]
      rw [hd] at h4 ⊢
      have := hs.q_ge
      omega
  · refine ⟨-1, Or.inr rfl, ?_, ?_⟩
    · show (D.q : ℤ) % 4 = (-1) % 4
      omega
    · have hd : D.d = D.q + 1 := by unfold SPLNot0.d; simp [h]
      rw [hd] at h4 ⊢
      omega

theorem L2facts (hs : SPLSetup D.toSPLNot0) :
    2 * Nat.card ↥D.Ict = D.q * (D.q ^ 2 - 1) ∧
    (∀ u v : ↥D.Ict, orderOf u = 2 → orderOf v = 2 → ∃ g : ↥D.Ict, g * u * g⁻¹ = v) ∧
    (∀ u : ↥D.Ict, orderOf u = 2 →
      Nonempty (↥(centralizer ({u} : Set ↥D.Ict)) ≃* DihedralGroup (D.d / 2))) := by
  obtain ⟨ε, hε1, hε, hδ⟩ := exists_eps D hs
  exact L2_involution_facts (Ict_isL2 D hs) hs.q_ge hs.odd_q hε1 hε hδ

theorem card_K₁_eq_two_mul (hs : SPLSetup D.toSPLNot0) : Nat.card ↥D.K₁ = 2 * Nat.card ↥D.Ict := by
  rw [(L2facts D hs).1]; exact card_K₁ (D := D.toSPLNot0) hs

theorem I_even (hs : SPLSetup D.toSPLNot0) : Even (Nat.card ↥D.Ict) := by
  have h := (L2facts D hs).1
  obtain ⟨m, hm⟩ := Nat.eight_dvd_sq_sub_one_of_odd hs.odd_q
  rw [hm] at h
  exact ⟨2 * D.q * m, by nlinarith⟩

theorem inf_I_eq_bot (hs : SPLSetup D.toSPLNot0) {N : Subgroup G}
    (hnorm : ∀ j ∈ D.Ict, ∀ x ∈ N, j * x * j⁻¹ ∈ N) (hodd : Odd (Nat.card ↥N)) :
    N ⊓ D.Ict = ⊥ := by
  have hsimple := I_simple D hs
  have hN : ((N ⊓ D.Ict).subgroupOf D.Ict).Normal := by
    refine ⟨fun a ha j => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    refine ⟨?_, ?_⟩
    · have := hnorm j j.2 a ha.1
      simpa using this
    · have := D.Ict.mul_mem (D.Ict.mul_mem j.2 ha.2) (D.Ict.inv_mem j.2)
      simpa using this
  have := hsimple
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ D.Ict).subgroupOf D.Ict) with h | h
  · rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx.2⟩ : ↥D.Ict) ∈ (N ⊓ D.Ict).subgroupOf D.Ict := hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  · exfalso
    have hIN : D.Ict ≤ N := by
      intro x hx
      have : (⟨x, hx⟩ : ↥D.Ict) ∈ (N ⊓ D.Ict).subgroupOf D.Ict := by rw [h]; exact Subgroup.mem_top _
      exact this.1
    have h1 : Nat.card ↥D.Ict ∣ Nat.card ↥N := Subgroup.card_dvd_of_le hIN
    have h2 : 2 ∣ Nat.card ↥N := (even_iff_two_dvd.mp (I_even D hs)).trans h1
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

theorem F_inf_Kt' (hs : SPLSetup D.toSPLNot0) {f : G} (hf : f ∈ D.F) (hf' : f ∈ D.K ⊔ zpowers D.t) :
    f = 1 := by
  have h0 : D.F ⊓ (D.K ⊔ zpowers D.t) = ⊥ := F_inf_Kt D.ext3 hs
  have h : f ∈ D.F ⊓ (D.K ⊔ zpowers D.t) := ⟨hf, hf'⟩
  rw [h0] at h
  exact Subgroup.mem_bot.mp h

theorem V_inf_IF₀ (hs : SPLSetup D.toSPLNot0) {v : G} (hv : v ∈ zpowers D.z ⊔ zpowers D.t)
    (hv' : v ∈ D.Ict ⊔ D.F₀) : v = 1 := by
  have hzt : ∀ a ∈ zpowers D.z, ∀ b ∈ zpowers D.t, a * b = b * a := by
    intro a ha b hb
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp ha
    obtain ⟨l, rfl⟩ := mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow (show Commute D.z D.t from z_comm_t' D hs) j l).eq
  obtain ⟨ζ, hζ, τ, hτ, rfl⟩ := mem_sup_of_commute hzt hv
  obtain ⟨i', hi', f', hf', hv_eq⟩ := mem_sup_of_le_normalizer (F₀_le_normalizer_I D hs) hv'
  obtain ⟨jz, rfl⟩ := mem_zpowers_iff.mp hζ
  obtain ⟨jt, rfl⟩ := mem_zpowers_iff.mp hτ
  have hi'K : i' ∈ D.K := Ict_le_K D hs hi'
  have hzK : D.z ∈ D.K := z_mem_K' D hs
  have htK : D.t ∉ D.K := t_not_mem_K D.ext3 hs
  rcases zpow_z_cases' D hs jz with hz1 | hz1 <;> rcases zpow_t_cases D hs jt with ht1 | ht1
  · rw [hz1, ht1, one_mul]
  ·
    exfalso
    rw [hz1, ht1, one_mul] at hv_eq
    have hf1 : f' = 1 := by
      refine F_inf_Kt' D hs hf'.1 ?_
      have : f' = i'⁻¹ * D.t := by rw [hv_eq]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (D.K.inv_mem hi'K))
        (Subgroup.mem_sup_right (mem_zpowers _))
    rw [hf1, mul_one] at hv_eq
    exact htK (hv_eq ▸ hi'K)
  ·
    exfalso
    rw [hz1, ht1, mul_one] at hv_eq
    have hf1 : f' = 1 := by
      have hfK : f' ∈ D.F ⊓ D.K := by
        refine ⟨hf'.1, ?_⟩
        have : f' = i'⁻¹ * D.z := by rw [hv_eq]; group
        rw [this]; exact D.K.mul_mem (D.K.inv_mem hi'K) hzK
      rw [F_inf_K_eq hs] at hfK
      exact Subgroup.mem_bot.mp hfK
    rw [hf1, mul_one] at hv_eq
    have : D.z ∈ D.Ict ⊓ zpowers D.z := ⟨hv_eq ▸ hi', mem_zpowers _⟩
    rw [Ict_inf_z D hs] at this
    exact z_ne_one' D hs (Subgroup.mem_bot.mp this)
  ·
    exfalso
    rw [hz1, ht1] at hv_eq
    have hf1 : f' = 1 := by
      refine F_inf_Kt' D hs hf'.1 ?_
      have : f' = i'⁻¹ * D.z * D.t := by
        calc f' = i'⁻¹ * (i' * f') := by group
          _ = i'⁻¹ * (D.z * D.t) := by rw [hv_eq]
          _ = i'⁻¹ * D.z * D.t := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (D.K.mul_mem (D.K.inv_mem hi'K) hzK))
        (Subgroup.mem_sup_right (mem_zpowers _))
    rw [hf1, mul_one] at hv_eq
    apply htK
    have hzi : D.z * D.t = i' := hv_eq
    have : D.t = D.z⁻¹ * i' := by rw [← hzi]; group
    rw [this]
    exact D.K.mul_mem (D.K.inv_mem hzK) hi'K

theorem T₁_exists (hs : SPLSetup D.toSPLNot0) : ∃ T₁ : Subgroup G, T₁ ≤ D.Ict ⊓ D.S₁ ∧
    IsPGroup 2 T₁ ∧ (∀ P : Subgroup G, P ≤ D.Ict → IsPGroup 2 P → T₁ ≤ P → P = T₁) ∧
    Nat.card ↥T₁ = 2 ^ (D.n - 1) ∧
    T₁ = (((D.S : Subgroup G) ⊓ D.K₁).subgroupOf D.K₁).map (D.dg hs) := by
  have htt := t_mul_t' D hs
  set Q : Subgroup G := (D.S : Subgroup G) ⊓ D.K₁ with hQ
  have hQK₁ : Q ≤ D.K₁ := inf_le_right
  set Q' : Subgroup ↥D.K₁ := Q.subgroupOf D.K₁ with hQ'
  set g := D.dg hs with hg
  set R' : Subgroup ↥g.range := Q'.map g.rangeRestrict with hR'
  set T₁ : Subgroup G := Q'.map g with hT₁
  have hzS : zpowers D.z ≤ (D.S : Subgroup G) := by rw [zpowers_le]; exact hs.syl.z_mem
  have hT₁eq : T₁ = R'.map g.range.subtype := by
    rw [hR', Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict]
  have hT₁I : T₁ ≤ D.Ict := by
    rw [Ict_eq D hs]; exact Subgroup.map_le_range g Q'
  have hT₁S : T₁ ≤ D.S₁ := by
    rintro x ⟨q, hq, rfl⟩
    have hqS : (q : G) ∈ (D.S : Subgroup G) := hq.1
    have htS : D.t ∈ (D.S : Subgroup G) := hs.syl.t_mem
    refine ⟨?_, ?_⟩
    · show (q : G) * (D.t * q * D.t⁻¹) ∈ (D.S : Subgroup G)
      exact Subgroup.mul_mem _ hqS (Subgroup.mul_mem _ (Subgroup.mul_mem _ htS hqS) (Subgroup.inv_mem _ htS))
    · show (q : G) * (D.t * q * D.t⁻¹) ∈ D.K
      have hqK : (q : G) ∈ D.K := Subgroup.mem_sup_left q.2
      exact Subgroup.mul_mem _ hqK (t_normalizes_K hs _ hqK)
  have hp : IsPGroup 2 ↥T₁ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hQp : IsPGroup 2 ↥Q := IsPGroup.to_le D.S.isPGroup' inf_le_left
    exact (IsPGroup.comap_subtype hQp (K := D.K₁)).map g
  have hindex : R'.index = Q'.index := by
    refine Subgroup.index_map_eq Q' (MonoidHom.rangeRestrict_surjective g) ?_
    rw [MonoidHom.ker_rangeRestrict]
    intro k hk
    have hkz : (k : G) ∈ zpowers D.z := (dg_ker_iff D hs k).mp hk
    exact ⟨hzS hkz, k.2⟩
  have hcardT : Nat.card ↥T₁ = Nat.card ↥R' := by
    rw [hT₁eq]; exact Subgroup.card_subtype g.range R'
  have h1 : Nat.card ↥R' * R'.index = Nat.card ↥g.range := Subgroup.card_mul_index R'
  have h2 : Nat.card ↥Q' * Q'.index = Nat.card ↥D.K₁ := Subgroup.card_mul_index Q'
  have hrange : Nat.card ↥g.range = Nat.card ↥D.Ict :=
    Nat.card_congr (MulEquiv.subgroupCongr (Ict_eq D hs).symm).toEquiv
  have hQc : Nat.card ↥Q' = Nat.card ↥Q := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK₁).toEquiv
  have hK₁ := card_K₁_eq_two_mul D hs
  have hidx : 0 < Q'.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have hRQ : 2 * Nat.card ↥R' = Nat.card ↥Q := by
    have : 2 * Nat.card ↥R' * Q'.index = Nat.card ↥Q * Q'.index := by
      calc 2 * Nat.card ↥R' * Q'.index = 2 * (Nat.card ↥R' * R'.index) := by rw [hindex]; ring
        _ = 2 * Nat.card ↥g.range := by rw [h1]
        _ = Nat.card ↥D.K₁ := by rw [hrange, hK₁]
        _ = Nat.card ↥Q * Q'.index := by rw [← hQc, h2]
    exact Nat.eq_of_mul_eq_mul_right hidx this
  have hQcard : Nat.card ↥Q = 2 ^ D.n := by
    have hq2 : 25 ≤ D.q ^ 2 := by have := hs.q_ge; nlinarith
    rw [Q₁_card hs, card_K₁ (D := D.toSPLNot0) hs, Nat.factorization_mul (by have := hs.q_ge; omega)
      (by omega)]
    simp only [Finsupp.add_apply]
    have hq0 : D.q.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by
      obtain ⟨k, hk⟩ := hs.odd_q; omega)
    rw [hq0, zero_add, v2_q_sq_sub_one_eq_n D hs]
  have hn3 : 3 ≤ D.n := three_le_n D.toSPLNot0 hs.odd_q hs.q_ge
  have hT₁card : Nat.card ↥T₁ = 2 ^ (D.n - 1) := by
    rw [hcardT]
    have h3 : 2 * Nat.card ↥R' = 2 * 2 ^ (D.n - 1) := by
      rw [hRQ, hQcard]
      obtain ⟨m, hm⟩ : ∃ m, D.n = m + 1 := ⟨D.n - 1, by omega⟩
      rw [hm]; simp [pow_succ]; ring
    omega
  refine ⟨T₁, le_inf hT₁I hT₁S, hp, ?_, hT₁card, rfl⟩
  intro P hPI hPp hT₁P
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · exact (Subgroup.eq_of_le_of_card_ge hT₁P (by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hPp)
      have hPdvd : Nat.card ↥P ∣ Nat.card ↥D.Ict := Subgroup.card_dvd_of_le hPI
      have h2k : 2 ^ (k + 1) ∣ D.q * (D.q ^ 2 - 1) := by
        rw [← (L2facts D hs).1, pow_succ']
        exact Nat.mul_dvd_mul_left 2 (hk ▸ hPdvd)
      have hcop : Nat.Coprime (2 ^ (k + 1)) D.q := by
        apply Nat.Coprime.pow_left
        exact (Nat.coprime_two_left.mpr hs.odd_q)
      have h3 : 2 ^ (k + 1) ∣ D.q ^ 2 - 1 := hcop.dvd_of_dvd_mul_left h2k
      have hne : D.q ^ 2 - 1 ≠ 0 := by
        have : 25 ≤ D.q ^ 2 := by have := hs.q_ge; nlinarith
        omega
      have h4 : k + 1 ≤ (D.q ^ 2 - 1).factorization 2 :=
        (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp h3
      rw [v2_q_sq_sub_one_eq_n D hs] at h4
      rw [hk, hT₁card]
      exact Nat.pow_le_pow_right (by norm_num) (by omega))).symm.le
  · exact hT₁P

theorem C_I_T₁_le (hs : SPLSetup D.toSPLNot0) {T₁ : Subgroup G} (hT₁I : T₁ ≤ D.Ict)
    (hp : IsPGroup 2 T₁) (hmax : ∀ P : Subgroup G, P ≤ D.Ict → IsPGroup 2 P → T₁ ≤ P → P = T₁) :
    ∀ i ∈ D.Ict, (∀ a ∈ T₁, i * a = a * i) → i ∈ T₁ := by
  intro i hi hc
  have hp' : IsPGroup 2 ↥(T₁.subgroupOf D.Ict) := IsPGroup.comap_subtype hp
  have hmax' : ∀ P : Subgroup ↥D.Ict, IsPGroup 2 ↥P → T₁.subgroupOf D.Ict ≤ P →
      P = T₁.subgroupOf D.Ict := by
    intro P hP hle
    have hP2 : IsPGroup 2 ↥(P.map D.Ict.subtype) := hP.map _
    have hle' : T₁ ≤ P.map D.Ict.subtype := by
      intro x hx
      exact ⟨⟨x, hT₁I hx⟩, hle hx, rfl⟩
    have hPI : P.map D.Ict.subtype ≤ D.Ict := Subgroup.map_subtype_le P
    have heq := hmax _ hPI hP2 hle'
    apply le_antisymm
    · intro x hx
      have : (x : G) ∈ P.map D.Ict.subtype := ⟨x, hx, rfl⟩
      rw [heq] at this
      exact this
    · exact hle
  have := L2_sylow_self_cent (Ict_isL2 D hs) hs.q_ge hs.odd_q (T₁.subgroupOf D.Ict) hp' hmax'
    ⟨i, hi⟩ (fun a ha => Subtype.ext (hc a ha))
  exact this

theorem Ict_comm_zpow_t (hs : SPLSetup D.toSPLNot0) {i : G} (hi : i ∈ D.Ict) {τ : G}
    (hτ : τ ∈ zpowers D.t) : i * τ = τ * i := by
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hτ
  have : i * D.t = D.t * i := mem_centralizer_singleton_iff.mp (Ict_le_Ct D hs hi)
  exact (Commute.zpow_right (show Commute i D.t from this) j).eq

omit [Finite G] in
theorem F₀_comm_zpow_z (hs : SPLSetup D.toSPLNot0) {y : G} (hy : y ∈ D.F₀) {ζ : G}
    (hζ : ζ ∈ zpowers D.z) : y * ζ = ζ * y := by
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hζ
  have : y * D.z = D.z * y := F_cen_S₁ D y hy.1 D.z (z_mem_S₁ (D := D.toSPLNot0) hs)
  exact (Commute.zpow_right (show Commute y D.z from this) j).eq

omit [Finite G] in
theorem F₀_comm_zpow_t {y : G} (hy : y ∈ D.F₀) {τ : G}
    (hτ : τ ∈ zpowers D.t) : y * τ = τ * y := by
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hτ
  have : y * D.t = D.t * y := ((mem_F₀_iff D y).mp hy).2
  exact (Commute.zpow_right (show Commute y D.t from this) j).eq

theorem Ict_le_CCt (hs : SPLSetup D.toSPLNot0) : D.Ict ≤ D.C ⊓ D.Ct :=
  le_inf ((Ict_le_K D hs).trans (K_le_C D.ext3 hs)) (Ict_le_Ct D hs)

theorem O2_CCt (hs : SPLSetup D.toSPLNot0) : ∀ N : Subgroup G, N ≤ D.C ⊓ D.Ct →
    (∀ g ∈ D.C ⊓ D.Ct, ∀ n ∈ N, g * n * g⁻¹ ∈ N) → Odd (Nat.card ↥N) → N = ⊥ := by
  intro N hNX hNnorm hNodd
  obtain ⟨T₁, hT₁le, hT₁p, hT₁max, -, -⟩ := T₁_exists D hs
  have hT₁I : T₁ ≤ D.Ict := hT₁le.trans inf_le_left
  have hT₁S : T₁ ≤ D.S₁ := hT₁le.trans inf_le_right
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  have hnX : n ∈ D.C ⊓ D.Ct := hNX hn
  obtain ⟨κ, hκ, τ, hτ, y, hy, hn_eq⟩ := CCt_decomp D hs hnX
  have hκ' : κ ∈ D.Ict ⊔ zpowers D.z := by
    have := hκ; rw [CK_eq D hs, ← Ict_eq D hs] at this; exact this
  have hzcomm : ∀ a ∈ D.Ict, ∀ b ∈ zpowers D.z, a * b = b * a := fun a ha b hb =>
    (z_central_in_K D hs hb a (Ict_le_K D hs ha)).symm
  obtain ⟨i, hi, ζ, hζ, hκeq⟩ := mem_sup_of_commute hzcomm hκ'
  have hiζ : i * ζ = ζ * i := hzcomm i hi ζ hζ
  have hiτ : i * τ = τ * i := Ict_comm_zpow_t D hs hi hτ
  have hyζ : y * ζ = ζ * y := F₀_comm_zpow_z D hs hy hζ
  have hyτ : y * τ = τ * y := F₀_comm_zpow_t D hy hτ
  have hζτ : ζ * τ = τ * ζ := by
    obtain ⟨a, rfl⟩ := mem_zpowers_iff.mp hζ
    obtain ⟨b, rfl⟩ := mem_zpowers_iff.mp hτ
    exact (Commute.zpow_zpow (show Commute D.z D.t from z_comm_t' D hs) a b).eq
  have hζ2 : ζ * ζ = 1 := by
    obtain ⟨a, rfl⟩ := mem_zpowers_iff.mp hζ
    rcases zpow_z_cases' D hs a with h | h <;> rw [h]
    · simp
    · exact z_mul_z' D hs
  have hτ2 : τ * τ = 1 := by
    obtain ⟨a, rfl⟩ := mem_zpowers_iff.mp hτ
    rcases zpow_t_cases D hs a with h | h <;> rw [h]
    · simp
    · exact t_mul_t' D hs
  have hvv : (ζ * τ) * (ζ * τ) = 1 := by
    calc ζ * τ * (ζ * τ) = ζ * (τ * ζ) * τ := by group
      _ = ζ * (ζ * τ) * τ := by rw [← hζτ]
      _ = (ζ * ζ) * (τ * τ) := by group
      _ = 1 := by rw [hζ2, hτ2, one_mul]
  have hiζτ : i * ζ * τ = ζ * τ * i := by
    calc i * ζ * τ = (i * ζ) * τ := rfl
      _ = (ζ * i) * τ := by rw [hiζ]
      _ = ζ * (i * τ) := by group
      _ = ζ * (τ * i) := by rw [hiτ]
      _ = ζ * τ * i := by group
  have hnvw : n = (ζ * τ) * (i * y) := by
    calc n = κ * τ * y := hn_eq
      _ = i * ζ * τ * y := by rw [hκeq]
      _ = (i * ζ * τ) * y := rfl
      _ = (ζ * τ * i) * y := by rw [hiζτ]
      _ = (ζ * τ) * (i * y) := by group
  have hvw : Commute (ζ * τ) (i * y) := by
    show ζ * τ * (i * y) = (i * y) * (ζ * τ)
    have h1 : ζ * (i * y) = (i * y) * ζ := by
      calc ζ * (i * y) = (ζ * i) * y := by group
        _ = (i * ζ) * y := by rw [hiζ]
        _ = i * (ζ * y) := by group
        _ = i * (y * ζ) := by rw [hyζ]
        _ = (i * y) * ζ := by group
    have h2 : τ * (i * y) = (i * y) * τ := by
      calc τ * (i * y) = (τ * i) * y := by group
        _ = (i * τ) * y := by rw [hiτ]
        _ = i * (τ * y) := by group
        _ = i * (y * τ) := by rw [hyτ]
        _ = (i * y) * τ := by group
    calc ζ * τ * (i * y) = ζ * (τ * (i * y)) := by group
      _ = ζ * ((i * y) * τ) := by rw [h2]
      _ = (ζ * (i * y)) * τ := by group
      _ = ((i * y) * ζ) * τ := by rw [h1]
      _ = (i * y) * (ζ * τ) := by group
  have hmodd : Odd (orderOf n) := by
    have : orderOf n ∣ Nat.card ↥N := by
      have := orderOf_dvd_natCard (⟨n, hn⟩ : ↥N)
      rwa [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat hNodd this
  have hnm : n ^ orderOf n = 1 := pow_orderOf_eq_one n
  have hwI : i * y ∈ D.Ict ⊔ D.F₀ :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hi) (Subgroup.mem_sup_right hy)
  have hv1 : ζ * τ = 1 := by
    have hvm : (ζ * τ) ^ orderOf n = ζ * τ := by
      obtain ⟨m, hm⟩ := hmodd
      rw [hm, pow_succ, pow_mul, pow_two, hvv, one_pow, one_mul]
    have h3 : (ζ * τ) * (i * y) ^ orderOf n = 1 := by
      have : ((ζ * τ) * (i * y)) ^ orderOf n = (ζ * τ) ^ orderOf n * (i * y) ^ orderOf n :=
        hvw.mul_pow _
      rw [← hnvw, hnm, hvm] at this
      exact this.symm
    have h4 : ζ * τ = ((i * y) ^ orderOf n)⁻¹ := eq_inv_of_mul_eq_one_left h3
    have hvV : ζ * τ ∈ zpowers D.z ⊔ zpowers D.t :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left hζ) (Subgroup.mem_sup_right hτ)
    refine V_inf_IF₀ D hs hvV ?_
    rw [h4]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hwI _)
  have hnw : n = i * y := by rw [hnvw, hv1, one_mul]
  have hIX := Ict_le_CCt D hs
  have hnormI : ∀ j ∈ D.Ict, ∀ x ∈ N, j * x * j⁻¹ ∈ N := fun j hj x hx => hNnorm j (hIX hj) x hx
  have hNI : N ⊓ D.Ict = ⊥ := inf_I_eq_bot D hs hnormI hNodd
  have hcI : ∀ j ∈ D.Ict, n * j = j * n := by
    intro j hj
    have hnjn : n * j * n⁻¹ ∈ D.Ict := by
      rw [hnw]
      have h1 : y * j * y⁻¹ ∈ D.Ict := F₀_norm D hs y hy j hj
      have : i * y * j * (i * y)⁻¹ = i * (y * j * y⁻¹) * i⁻¹ := by group
      rw [this]
      exact D.Ict.mul_mem (D.Ict.mul_mem hi h1) (D.Ict.inv_mem hi)
    have hc1 : n * j * n⁻¹ * j⁻¹ ∈ N := by
      have : n * j * n⁻¹ * j⁻¹ = n * (j * n⁻¹ * j⁻¹) := by group
      rw [this]
      exact N.mul_mem hn (hNnorm j (hIX hj) n⁻¹ (N.inv_mem hn))
    have hc2 : n * j * n⁻¹ * j⁻¹ ∈ D.Ict := D.Ict.mul_mem hnjn (D.Ict.inv_mem hj)
    have hc3 : n * j * n⁻¹ * j⁻¹ ∈ N ⊓ D.Ict := ⟨hc1, hc2⟩
    rw [hNI, Subgroup.mem_bot] at hc3
    calc n * j = (n * j * n⁻¹ * j⁻¹) * (j * n) := by group
      _ = j * n := by rw [hc3, one_mul]
  have hyT₁ : ∀ a ∈ T₁, y * a = a * y := fun a ha => F_cen_S₁ D y hy.1 a (hT₁S ha)
  have hiT₁ : i ∈ T₁ := by
    refine C_I_T₁_le D hs hT₁I hT₁p hT₁max i hi ?_
    intro a ha
    have h1 := hcI a (hT₁I ha)
    rw [hnw] at h1
    have h2 : i * y * a = i * a * y := by
      calc i * y * a = i * (y * a) := by group
        _ = i * (a * y) := by rw [hyT₁ a ha]
        _ = i * a * y := by group
    have h3 : a * (i * y) = a * i * y := by group
    rw [h2, h3] at h1
    exact mul_right_cancel h1
  have hiy : i * y = y * i := (hyT₁ i hiT₁).symm
  have hi1 : i = 1 := by
    have hcomm' : Commute i y := hiy
    have h1 : i ^ orderOf n * y ^ orderOf n = 1 := by
      rw [← hcomm'.mul_pow]
      have : (i * y) = n := hnw.symm
      rw [this]; exact hnm
    have h2 : i ^ orderOf n = (y ^ orderOf n)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : i ^ orderOf n ∈ D.F₀ ⊓ D.Ict := by
      refine ⟨?_, Subgroup.pow_mem _ hi _⟩
      rw [h2]; exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hy _)
    rw [F₀_inf_I D hs, Subgroup.mem_bot] at h3
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp hT₁p) (⟨i, hiT₁⟩ : ↥T₁)
    rw [Subgroup.orderOf_mk] at ha
    have hdvd : orderOf i ∣ orderOf n := orderOf_dvd_of_pow_eq_one h3
    have hcop : Nat.Coprime (orderOf i) (orderOf n) := by
      rw [ha]; exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hmodd)
    have h5 : orderOf i = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
    exact orderOf_eq_one_iff.mp h5
  have hy1 : y = 1 := by
    refine F₀_faith D hs y hy ?_
    intro j hj
    have h1 := hcI j hj
    rw [hnw, hi1, one_mul] at h1
    exact h1
  rw [hnw, hi1, hy1, one_mul]

theorem Ict_quasisimple (hs : SPLSetup D.toSPLNot0) : IsQuasisimple ↥D.Ict := by
  have hq : IsQuasisimple ↥D.K₁ := hs.comps.quasi₁
  have hker : (D.dg hs).rangeRestrict.ker ≤ center ↥D.K₁ := by
    rw [MonoidHom.ker_rangeRestrict]
    intro k hk
    have hkz : (k : G) ∈ zpowers D.z := (dg_ker_iff D hs k).mp hk
    exact (mem_center_K₁_iff D.ext3 hs k).mpr hkz
  have h1 : IsQuasisimple ↥(D.dg hs).range :=
    CFSG.LocalCores.isQuasisimple_of_surjective hq (D.dg hs).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _) hker
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupCongr (Ict_eq D hs).symm) h1

theorem isPCompIn_of_normal_quasisimple {X K : Subgroup G} (hKX : K ≤ X)
    (hn : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hq : IsQuasisimple ↥K)
    (hc : ∀ N : Subgroup G, N ≤ X → (∀ g ∈ X, ∀ n ∈ N, g * n * g⁻¹ ∈ N) →
      Odd (Nat.card ↥N) → N = ⊥) : IsPCompIn 2 X K := by
  refine ⟨hKX, ?_⟩
  have hO : pPrimeCoreOf 2 X = ⊥ :=
    hc _ (TwoThin.pPrimeCoreOf_le X) (fun g hg n hn' => TwoThin.pPrimeCoreOf_normalized X hg hn')
      (TwoThin.card_pPrimeCoreOf_odd X)
  have hO' : pPrimeCore 2 ↥X = ⊥ := by
    have : (pPrimeCore 2 ↥X).map X.subtype = ⊥ := hO
    exact (Subgroup.map_eq_bot_iff_of_injective (pPrimeCore 2 ↥X) X.subtype_injective).mp this
  have hinj : Function.Injective (QuotientGroup.mk' (pPrimeCore 2 ↥X)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hO']
  have hL : (K.subgroupOf X).Normal := ⟨fun a ha g => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using hn g g.2 a ha⟩
  let e : ↥K ≃* ↥(K.subgroupOf X) := (Subgroup.subgroupOfEquivOfLe hKX).symm
  let e2 : ↥(K.subgroupOf X) ≃* ↥((K.subgroupOf X).map (QuotientGroup.mk' (pPrimeCore 2 ↥X))) :=
    Subgroup.equivMapOfInjective _ _ hinj
  refine ⟨(K.subgroupOf X).map (QuotientGroup.mk' (pPrimeCore 2 ↥X)), ⟨?_, ?_⟩, hL.isSubnormal, rfl, ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (e.trans e2) hq
  · exact Subgroup.IsSubnormal.map (QuotientGroup.mk'_surjective _) hL.isSubnormal
  · intro J hJ _ hmap
    have := Subgroup.map_injective hinj hmap
    exact hJ.ne this

theorem zpow_z_cen_I (hs : SPLSetup D.toSPLNot0) {ζ : G} (hζ : ζ ∈ zpowers D.z) {j : G}
    (hj : j ∈ D.Ict) : ζ * j * ζ⁻¹ = j := by
  have h1 : ζ * j = j * ζ := z_central_in_K D hs hζ j (Ict_le_K D hs hj)
  rw [h1]; group

theorem zpow_t_cen_I (hs : SPLSetup D.toSPLNot0) {τ : G} (hτ : τ ∈ zpowers D.t) {j : G}
    (hj : j ∈ D.Ict) : τ * j * τ⁻¹ = j := by
  have h1 : τ * j = j * τ := (Ict_comm_zpow_t D hs hj hτ).symm
  rw [h1]; group

theorem CCt_normalizes_I (hs : SPLSetup D.toSPLNot0) :
    ∀ x ∈ D.C ⊓ D.Ct, ∀ k ∈ D.Ict, x * k * x⁻¹ ∈ D.Ict := by
  intro x hx k hk
  obtain ⟨κ, hκ, τ, hτ, y, hy, rfl⟩ := CCt_decomp D hs hx
  have hκ' : κ ∈ D.Ict ⊔ zpowers D.z := by
    have := hκ; rw [CK_eq D hs, ← Ict_eq D hs] at this; exact this
  have hzcomm : ∀ a ∈ D.Ict, ∀ b ∈ zpowers D.z, a * b = b * a := fun a ha b hb =>
    (z_central_in_K D hs hb a (Ict_le_K D hs ha)).symm
  obtain ⟨i, hi, ζ, hζ, rfl⟩ := mem_sup_of_commute hzcomm hκ'
  have h1 : y * k * y⁻¹ ∈ D.Ict := F₀_norm D hs y hy k hk
  have h2 : τ * (y * k * y⁻¹) * τ⁻¹ = y * k * y⁻¹ := zpow_t_cen_I D hs hτ h1
  have h3 : ζ * (y * k * y⁻¹) * ζ⁻¹ = y * k * y⁻¹ := zpow_z_cen_I D hs hζ h1
  have e : (i * ζ * τ * y) * k * (i * ζ * τ * y)⁻¹ =
      i * (ζ * (τ * (y * k * y⁻¹) * τ⁻¹) * ζ⁻¹) * i⁻¹ := by group
  rw [e, h2, h3]
  exact D.Ict.mul_mem (D.Ict.mul_mem hi h1) (D.Ict.inv_mem hi)

theorem I_comp (hs : SPLSetup D.toSPLNot0) : IsPCompIn 2 (D.C ⊓ D.Ct) D.Ict :=
  isPCompIn_of_normal_quasisimple (Ict_le_CCt D hs) (CCt_normalizes_I D hs) (Ict_quasisimple D hs)
    (O2_CCt D hs)

omit [Finite G] in
theorem Act_le_Ct : D.Act ≤ D.Ct := TwoThin.pPrimeCoreOf_le D.Ct

omit [Finite G] in
theorem Act_normal : ∀ c ∈ D.Ct, ∀ a ∈ D.Act, c * a * c⁻¹ ∈ D.Act := fun _ hc _ ha =>
  TwoThin.pPrimeCoreOf_normalized D.Ct hc ha

theorem Act_odd : Odd (Nat.card ↥D.Act) := TwoThin.card_pPrimeCoreOf_odd D.Ct

theorem Act_inf_Ict (hs : SPLSetup D.toSPLNot0) : D.Act ⊓ D.Ict = ⊥ :=
  inf_I_eq_bot D hs (fun j hj x hx => Act_normal D j (Ict_le_Ct D hs hj) x hx) (Act_odd D)

omit [Finite G] in
theorem fpf_inj_aux (z x y : G) (h : x⁻¹ * (z * x * z⁻¹) = y⁻¹ * (z * y * z⁻¹)) :
    z * (y * x⁻¹) * z⁻¹ = y * x⁻¹ := by
  calc z * (y * x⁻¹) * z⁻¹ = (z * y * z⁻¹) * (z * x * z⁻¹)⁻¹ := by group
    _ = y * (y⁻¹ * (z * y * z⁻¹)) * (z * x * z⁻¹)⁻¹ := by group
    _ = y * (x⁻¹ * (z * x * z⁻¹)) * (z * x * z⁻¹)⁻¹ := by rw [← h]
    _ = y * x⁻¹ := by group

omit [Finite G] in
theorem fpf_inv_aux (z y : G) (hz : z * z = 1) :
    z * (y⁻¹ * (z * y * z⁻¹)) * z⁻¹ = (y⁻¹ * (z * y * z⁻¹))⁻¹ := by
  calc z * (y⁻¹ * (z * y * z⁻¹)) * z⁻¹ = (z * y⁻¹ * z⁻¹) * ((z * z) * y * (z * z)⁻¹) := by group
    _ = (z * y⁻¹ * z⁻¹) * y := by rw [hz]; group
    _ = (y⁻¹ * (z * y * z⁻¹))⁻¹ := by group

theorem fpf_inverts (A : Subgroup G) (z : G) (hz : z * z = 1)
    (hA : ∀ a ∈ A, z * a * z⁻¹ ∈ A) (hfix : ∀ a ∈ A, z * a * z⁻¹ = a → a = 1) :
    ∀ a ∈ A, z * a * z⁻¹ = a⁻¹ := by
  let f : ↥A → ↥A := fun a => ⟨(a : G)⁻¹ * (z * a * z⁻¹), A.mul_mem (A.inv_mem a.2) (hA a a.2)⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have h : (a : G)⁻¹ * (z * a * z⁻¹) = (b : G)⁻¹ * (z * b * z⁻¹) := congrArg Subtype.val hab
    have h2 := fpf_inj_aux z (a : G) (b : G) h
    have h3 : (b : G) * (a : G)⁻¹ = 1 := hfix _ (A.mul_mem b.2 (A.inv_mem a.2)) h2
    exact Subtype.ext (mul_inv_eq_one.mp h3).symm
  have hsurj := Finite.injective_iff_surjective.mp hinj
  intro a ha
  obtain ⟨b, hb⟩ := hsurj ⟨a, ha⟩
  have hab : a = (b : G)⁻¹ * (z * b * z⁻¹) := (congrArg Subtype.val hb).symm
  rw [hab]
  exact fpf_inv_aux z (b : G) hz

omit [Finite G] in
theorem comm_of_inverts (A : Subgroup G) (z : G)
    (hinv : ∀ a ∈ A, z * a * z⁻¹ = a⁻¹) : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
  intro a ha b hb
  have h1 := hinv (a * b) (A.mul_mem ha hb)
  have h2 : z * (a * b) * z⁻¹ = (z * a * z⁻¹) * (z * b * z⁻¹) := by group
  rw [h2, hinv a ha, hinv b hb, mul_inv_rev] at h1
  have h3 : (a⁻¹ * b⁻¹)⁻¹ = (b⁻¹ * a⁻¹)⁻¹ := by rw [h1]
  simpa using h3.symm

theorem CA_z_trivial (hs : SPLSetup D.toSPLNot0) :
    ∀ a ∈ D.Act, D.z * a * D.z⁻¹ = a → a = 1 := by
  intro a ha hza
  have hN : D.Act ⊓ D.C = ⊥ := by
    refine O2_CCt D hs (D.Act ⊓ D.C) ?_ ?_ ?_
    · exact fun x hx => ⟨hx.2, Act_le_Ct D hx.1⟩
    · intro g hg n hn
      refine ⟨Act_normal D g hg.2 n hn.1, ?_⟩
      show g * n * g⁻¹ ∈ centralizer ({D.z} : Set G)
      rw [mem_centralizer_singleton_iff]
      have hgz : g * D.z = D.z * g := mem_centralizer_singleton_iff.mp hg.1
      have hnz : n * D.z = D.z * n := mem_centralizer_singleton_iff.mp hn.2
      calc g * n * g⁻¹ * D.z = g * n * (g⁻¹ * D.z) := by group
        _ = g * n * (D.z * g⁻¹) := by
            have : g⁻¹ * D.z = D.z * g⁻¹ := (show Commute g D.z from hgz).inv_left.eq
            rw [this]
        _ = g * (n * D.z) * g⁻¹ := by group
        _ = g * (D.z * n) * g⁻¹ := by rw [hnz]
        _ = D.z * (g * n * g⁻¹) := by
            calc g * (D.z * n) * g⁻¹ = (g * D.z) * n * g⁻¹ := by group
              _ = (D.z * g) * n * g⁻¹ := by rw [hgz]
              _ = D.z * (g * n * g⁻¹) := by group
    · exact Odd.of_dvd_nat (Act_odd D) (Subgroup.card_dvd_of_le inf_le_left)
  have ha' : a ∈ D.Act ⊓ D.C := by
    refine ⟨ha, ?_⟩
    show a ∈ centralizer ({D.z} : Set G)
    rw [mem_centralizer_singleton_iff]
    calc a * D.z = (D.z * a * D.z⁻¹) * D.z := by rw [hza]
      _ = D.z * a := by group
  rw [hN] at ha'
  exact Subgroup.mem_bot.mp ha'

theorem Act_inv (hs : SPLSetup D.toSPLNot0) : ∀ a ∈ D.Act, D.z * a * D.z⁻¹ = a⁻¹ :=
  fpf_inverts D.Act D.z (z_mul_z' D hs)
    (fun a ha => Act_normal D D.z (mem_centralizer_singleton_iff.mpr (z_comm_t' D hs)) a ha)
    (CA_z_trivial D hs)

theorem Act_comm (hs : SPLSetup D.toSPLNot0) : ∀ a ∈ D.Act, ∀ b ∈ D.Act, a * b = b * a :=
  comm_of_inverts D.Act D.z (Act_inv D hs)

omit [Finite G] in
theorem T₁_subgroupOf {T₁ : Subgroup G} (hT₁I : T₁ ≤ D.Ict) (hp : IsPGroup 2 T₁)
    (hmax : ∀ P : Subgroup G, P ≤ D.Ict → IsPGroup 2 P → T₁ ≤ P → P = T₁) :
    IsPGroup 2 ↥(T₁.subgroupOf D.Ict) ∧
    ∀ P : Subgroup ↥D.Ict, IsPGroup 2 ↥P → T₁.subgroupOf D.Ict ≤ P → P = T₁.subgroupOf D.Ict := by
  refine ⟨IsPGroup.comap_subtype hp, ?_⟩
  intro P hP hle
  have hP2 : IsPGroup 2 ↥(P.map D.Ict.subtype) := hP.map _
  have hle' : T₁ ≤ P.map D.Ict.subtype := by
    intro x hx
    exact ⟨⟨x, hT₁I hx⟩, hle hx, rfl⟩
  have hPI : P.map D.Ict.subtype ≤ D.Ict := Subgroup.map_subtype_le P
  have heq := hmax _ hPI hP2 hle'
  apply le_antisymm
  · intro x hx
    have : (x : G) ∈ P.map D.Ict.subtype := ⟨x, hx, rfl⟩
    rw [heq] at this
    exact this
  · exact hle

theorem T₁_dihedral (hs : SPLSetup D.toSPLNot0) {T₁ : Subgroup G} (hT₁I : T₁ ≤ D.Ict)
    (hp : IsPGroup 2 T₁) (hmax : ∀ P : Subgroup G, P ≤ D.Ict → IsPGroup 2 P → T₁ ≤ P → P = T₁)
    (hcard : Nat.card ↥T₁ = 2 ^ (D.n - 1)) : IVK.IsDihedralOrder ↥T₁ (2 ^ (D.n - 1)) := by
  obtain ⟨hp', hmax'⟩ := T₁_subgroupOf D hT₁I hp hmax
  obtain ⟨m, k, hm, hk2, ⟨φ⟩⟩ := L2_sylow_dihedral (Ict_isL2 D hs) hs.q_ge hs.odd_q
    (T₁.subgroupOf D.Ict) hp' hmax'
  let ψ : ↥T₁ ≃* DihedralGroup k := (Subgroup.subgroupOfEquivOfLe hT₁I).symm.trans φ
  have hc : Nat.card ↥T₁ = 2 * k := by
    rw [Nat.card_congr ψ.toEquiv, DihedralGroup.nat_card]
  exact ⟨k, by omega, hk2, ⟨ψ⟩⟩

theorem splCt0 (hs : SPLSetup D.toSPLNot0) : SPLCt0 D where
  I_le_K := Ict_le_K D hs
  I_le_Ct := Ict_le_Ct D hs
  I_L2 := Ict_isL2 D hs
  I_perf := Ict_perfect D hs
  I_inf_z := Ict_inf_z D hs
  CK := by rw [CK_eq D hs, ← Ict_eq D hs]
  CCt := CCt_eq D hs
  F₀_norm := F₀_norm D hs
  F₀_inf := F₀_inf_I D hs
  F₀_faith := F₀_faith D hs
  F₀_odd := F₀_odd D
  F_cen := F_cen_S₁ D
  O2 := O2_CCt D hs
  I_comp := I_comp D hs
  T₁ex := by
    obtain ⟨T₁, hle, hp, hmax, hcard, -⟩ := T₁_exists D hs
    exact ⟨T₁, hle, hp, hmax, T₁_dihedral D hs (hle.trans inf_le_left) hp hmax hcard⟩
  A_odd := Act_odd D
  A_normal := Act_normal D
  A_comm := Act_comm D hs
  A_inv := Act_inv D hs
  AI_inf := Act_inf_Ict D hs

end Ct0

end CFSG.GH74.GLS.SP.Local
