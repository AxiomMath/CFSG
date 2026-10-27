module

public import CFSG.GH74.GLS.SP.Local.SPLR2Defs
public import CFSG.GH74.GLS.SP.Local.SPLCoordStage
public import CFSG.GH74.GLS.SP.Local.SPLM2b

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

section R2C

variable {G : Type} [Group G]

theorem r2c_X₂_card (D : SPLNot3 G) (h3 : SPL3X D) : Nat.card ↥D.X₂ = D.q := by
  show Nat.card ↥(conjBy D.t D.X₁) = D.q
  rw [card_conjBy]; exact h3.X₁_card

theorem r2c_X₃_card (D : SPLNot3 G) (h3 : SPL3X D) : Nat.card ↥D.X₃ = D.q := by
  show Nat.card ↥(conjBy D.a D.Y₁) = D.q
  rw [card_conjBy]; exact h3.Y₁_card

theorem r2c_X₄_card (D : SPLNot3 G) (h3 : SPL3X D) : Nat.card ↥D.X₄ = D.q := by
  show Nat.card ↥(conjBy D.w₁ D.X₃) = D.q
  rw [card_conjBy]; exact r2c_X₃_card D h3

theorem r2c_X₂_eab (D : SPLNot3 G) (h3 : SPL3X D) : IsEAb D.p D.X₂ := isEAb_conjBy h3.X₁_eab D.t

theorem r2c_X₃_eab (D : SPLNot3 G) (h3 : SPL3X D) : IsEAb D.p D.X₃ := isEAb_conjBy h3.Y₁_eab D.a

theorem r2c_X₄_eab (D : SPLNot3 G) (h3 : SPL3X D) : IsEAb D.p D.X₄ :=
  isEAb_conjBy (r2c_X₃_eab D h3) D.w₁

theorem r2c_odd_p [Finite G] (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0) : Odd D.p :=
  hs.prime.odd_of_ne_two hs.p_ne_two

theorem r2c_eq_one_of_cen_inv {p : ℕ} (hodd : Odd p) {c z : G} (hc : c ^ p = 1)
    (h1 : z * c * z⁻¹ = c) (h2 : z * c * z⁻¹ = c⁻¹) : c = 1 :=
  eq_one_of_inv_eq_self hodd hc (h1.symm.trans h2).symm

theorem r2c_z_cen_X₂ [Finite G] (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) :
    ∀ y ∈ D.X₂, D.z * y * D.z⁻¹ = y := by
  intro y hy
  have hyK : y ∈ D.K := le_sup_right (a := D.K₁) (b := D.K₂) (X₂_le_K₂ D hs h3 hy)
  rw [← z_comm_K D hs hyK]
  group

theorem r2c_z_inv_X₄ [Finite G] (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0)
    (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3X D) (hA : SPL3Aa D) :
    ∀ x ∈ D.X₄, D.z * x * D.z⁻¹ = x⁻¹ := by
  intro x hx
  have hx' : D.w₁ * x * D.w₁⁻¹ ∈ D.X₃ := mem_conjBy_iff.mp hx
  have h := z_inv_X₃ D hs h3 hA _ hx'
  have hw : D.w₁ * D.z = D.z * D.w₁ := w₁_comm_z D hs h1
  have e1 : D.z * (D.w₁ * x * D.w₁⁻¹) * D.z⁻¹ = D.w₁ * (D.z * x * D.z⁻¹) * D.w₁⁻¹ := by
    calc D.z * (D.w₁ * x * D.w₁⁻¹) * D.z⁻¹ = (D.z * D.w₁) * x * (D.z * D.w₁)⁻¹ := by group
      _ = (D.w₁ * D.z) * x * (D.w₁ * D.z)⁻¹ := by rw [hw]
      _ = _ := by group
  rw [e1] at h
  have h2 : D.w₁ * (D.z * x * D.z⁻¹) * D.w₁⁻¹ = D.w₁ * x⁻¹ * D.w₁⁻¹ := by rw [h]; group
  calc D.z * x * D.z⁻¹ = D.w₁⁻¹ * (D.w₁ * (D.z * x * D.z⁻¹) * D.w₁⁻¹) * D.w₁ := by group
    _ = D.w₁⁻¹ * (D.w₁ * x⁻¹ * D.w₁⁻¹) * D.w₁ := by rw [h2]
    _ = x⁻¹ := by group

theorem r2c_mem_C₂_iff (D : SPLNot3 G) {g : G} : g ∈ D.C₂ ↔ ∀ y ∈ D.X₂, y * g = g * y :=
  Subgroup.mem_centralizer_iff

theorem r2c_X₂_cen_C₂ (D : SPLNot3 G) : ∀ y ∈ D.X₂, ∀ g ∈ D.C₂, y * g = g * y :=
  fun y hy _ hg => (r2c_mem_C₂_iff D).1 hg y hy

theorem r2c_V₂_le_C₂ (D : SPLNot3 G) : D.V₂ ≤ D.C₂ := TwoThin.pPrimeCoreOf_le D.C₂

theorem r2c_X₂_cen_V₂ (D : SPLNot3 G) : ∀ y ∈ D.X₂, ∀ g ∈ D.V₂, y * g = g * y :=
  fun y hy g hg => r2c_X₂_cen_C₂ D y hy g (r2c_V₂_le_C₂ D hg)

theorem r2c_K₁_cen_X₂ (D : SPLNot3 G) (hRA : R2A D) :
    ∀ k ∈ D.K₁, ∀ y ∈ D.X₂, k * y = y * k :=
  fun k hk y hy => (r2c_X₂_cen_C₂ D y hy k (hRA.K₁_le_C₂ hk)).symm

theorem r2c_z_not_mem_V₂ [Finite G] (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0) (hRA : R2A D) :
    D.z ∉ D.V₂ := by
  intro hz
  have h1 : orderOf D.z ∣ Nat.card ↥D.V₂ := Subgroup.orderOf_dvd_natCard D.V₂ hz
  rw [hs.syl.z_inv] at h1
  exact (Nat.not_even_iff_odd.mpr hRA.V₂_odd) (even_iff_two_dvd.mpr h1)

theorem r2c_V₂_inf_K₁ [Finite G] (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0) (hRA : R2A D) :
    D.V₂ ⊓ D.K₁ = ⊥ := by
  have hN : (D.V₂.subgroupOf D.K₁).Normal :=
    ⟨fun n hn g => by
      show ((g * n * g⁻¹ : ↥D.K₁) : G) ∈ D.V₂
      simpa using hRA.V₂_norm g (hRA.K₁_le_C₂ g.2) n hn⟩
  have hz := r2c_z_not_mem_V₂ D hs hRA
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hs.comps.quasi₁
      (D.V₂.subgroupOf D.K₁) with hle | htop
  · rw [eq_bot_iff]
    rintro x ⟨hxV, hxK⟩
    have hxc : (⟨x, hxK⟩ : ↥D.K₁) ∈ center ↥D.K₁ := hle hxV
    have hxz : x ∈ zpowers D.z := (mem_center_K₁_iff D hs ⟨x, hxK⟩).mp hxc
    rcases eq_one_or_z hs hxz with h | h
    · rw [h]; exact Subgroup.one_mem _
    · exact absurd (h ▸ hxV) hz
  · exfalso
    have hzK : (⟨D.z, z_mem_K₁ hs⟩ : ↥D.K₁) ∈ D.V₂.subgroupOf D.K₁ := by rw [htop]; trivial
    exact hz hzK

theorem r2c_M₂_cen (D : SPLNot3 G) : ∀ g ∈ D.M₂, ∀ h ∈ D.C₂, g * h * g⁻¹ ∈ D.C₂ := by
  intro g hg h hh
  rw [r2c_mem_C₂_iff] at hh ⊢
  intro y hy
  have hy' : g⁻¹ * y * g ∈ D.X₂ := by
    have := (mem_normalizer_iff.mp (D.M₂.inv_mem hg) y).mp hy
    simpa using this
  have := hh _ hy'
  calc y * (g * h * g⁻¹) = g * ((g⁻¹ * y * g) * h) * g⁻¹ := by group
    _ = g * (h * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
    _ = (g * h * g⁻¹) * y := by group

theorem r2c_M₂_norm_C₂ (D : SPLNot3 G) : D.M₂ ≤ normalizer (D.C₂ : Set G) := fun g hg =>
  normalizer_of_both (r2c_M₂_cen D g hg) (fun h hh => by
    simpa using r2c_M₂_cen D g⁻¹ (D.M₂.inv_mem hg) h hh)

theorem r2c_M₂_norm_V₂ (D : SPLNot3 G) : D.M₂ ≤ normalizer (D.V₂ : Set G) := fun _ hg =>
  TwoThin.mem_normalizer_pPrimeCoreOf (r2c_M₂_norm_C₂ D hg)

theorem r2c_H_V₂ [Finite G] (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1)
    (h3 : SPL3X D) : Normalizes D.H D.V₂ := by
  have hHM : D.H ≤ D.M₂ := le_normalizer_of_normalizes (H_X₂ D hs h1 h3)
  intro h hh v hv
  exact (mem_normalizer_iff.mp (r2c_M₂_norm_V₂ D (hHM hh)) v).mp hv

theorem r2c_F_V₂ [Finite G] (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D) :
    Normalizes D.F D.V₂ := by
  have hFM : D.F ≤ D.M₂ := F_le_M₂ D hs h3
  intro f hf v hv
  exact (mem_normalizer_iff.mp (r2c_M₂_norm_V₂ D (hFM hf)) v).mp hv

theorem r2c_X₁'_X₄ (D : SPLNot3 G) (h3 : SPL3X D)
    (hD1 : ∀ x ∈ D.X, ∀ y ∈ D.X₃, x * y = y * x) :
    ∀ g ∈ D.X₁', ∀ c ∈ D.X₄, g * c = c * g := by
  intro g hg c hc
  rw [h3.X₁'_eq, mem_conjBy_iff] at hg
  have hc' : D.w₁ * c * D.w₁⁻¹ ∈ D.X₃ := mem_conjBy_iff.mp hc
  have h := hD1 _ ((le_sup_left : D.X₁ ≤ D.X₁ ⊔ D.X₂) hg) _ hc'
  have e1 : D.w₁ * g * D.w₁⁻¹ * (D.w₁ * c * D.w₁⁻¹) = D.w₁ * (g * c) * D.w₁⁻¹ := by group
  have e2 : D.w₁ * c * D.w₁⁻¹ * (D.w₁ * g * D.w₁⁻¹) = D.w₁ * (c * g) * D.w₁⁻¹ := by group
  rw [e1, e2] at h
  exact mul_left_cancel (mul_right_cancel h)

theorem r2c_cen_K₁ (D : SPLNot3 G) (h3 : SPL3X D) {c : G} (hc1 : ∀ g ∈ D.X₁, g * c = c * g)
    (hc2 : ∀ g ∈ D.X₁', g * c = c * g) : ∀ g ∈ D.K₁, g * c = c * g := by
  have hle : D.K₁ ≤ centralizer ({c} : Set G) := by
    rw [h3.K₁_eq]
    exact sup_le (fun g hg => mem_centralizer_singleton_iff.mpr (hc1 g hg))
      (fun g hg => mem_centralizer_singleton_iff.mpr (hc2 g hg))
  exact fun g hg => mem_centralizer_singleton_iff.mp (hle hg)

theorem r2c_key [Finite G] (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1)
    (h3 : SPL3X D) (hA : SPL3Aa D) (hD1 : ∀ x ∈ D.X, ∀ y ∈ D.X₃, x * y = y * x) {c : G}
    (hc : c ∈ D.X₄) (hcen : ∀ g ∈ D.X₁, g * c = c * g) : c = 1 := by
  have hK := r2c_cen_K₁ D h3 hcen (fun g hg => r2c_X₁'_X₄ D h3 hD1 g hg c hc)
  have hz : D.z * c = c * D.z := hK D.z (z_mem_K₁ hs)
  refine r2c_eq_one_of_cen_inv (r2c_odd_p D hs) ((r2c_X₄_eab D h3).2 c hc) ?_
    (r2c_z_inv_X₄ D hs h1 h3 hA c hc)
  rw [hz]; group

theorem r2c_X₂_inf_X₃ [Finite G] (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D)
    (hA : SPL3Aa D) : D.X₂ ⊓ D.X₃ = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx2, hx3⟩
  rw [Subgroup.mem_bot]
  exact r2c_eq_one_of_cen_inv (r2c_odd_p D hs) ((r2c_X₃_eab D h3).2 x hx3)
    (r2c_z_cen_X₂ D hs h3 x hx2) (z_inv_X₃ D hs h3 hA x hx3)

theorem r2c_X₃_X₄ [Finite G] (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1)
    (h3 : SPL3X D) (hA : SPL3Aa D) (hRA : R2A D)
    (hD1 : ∀ x ∈ D.X, ∀ y ∈ D.X₃, x * y = y * x) {b c : G} (hb : b ∈ D.X₃) (hc : c ∈ D.X₄)
    (hx : b * c⁻¹ ∈ D.X₂) : b = 1 ∧ c = 1 := by
  have hc1 : c = 1 := by
    refine r2c_key D hs h1 h3 hA hD1 hc (fun g hg => ?_)
    have hgb : Commute g b := hD1 g ((le_sup_left : D.X₁ ≤ D.X₁ ⊔ D.X₂) hg) b hb
    have hgx : Commute g (b * c⁻¹) := r2c_K₁_cen_X₂ D hRA g (h3.X₁_le hg) _ hx
    have h3' : Commute g ((b * c⁻¹)⁻¹ * b) := hgx.inv_right.mul_right hgb
    have e : (b * c⁻¹)⁻¹ * b = c := by group
    rw [e] at h3'
    exact h3'
  refine ⟨?_, hc1⟩
  rw [hc1, inv_one, mul_one] at hx
  have : b ∈ D.X₂ ⊓ D.X₃ := ⟨hx, hb⟩
  rw [r2c_X₂_inf_X₃ D hs h3 hA] at this
  exact this

theorem r2c_norm_of_X₂_le (D : SPLNot3 G) (hRA : R2A D) {N : Subgroup G} (hN : D.X₂ ≤ N)
    (hNV : N ≤ D.V₂) : ∀ g ∈ D.V₂, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
  intro g hg n hn
  have h1 : ⁅g, n⁆ ∈ D.X₂ := hRA.V₂_class2 g hg n (hNV hn)
  have h2 : g * n * g⁻¹ = ⁅g, n⁆ * n := by rw [commutatorElement_def]; group
  rw [h2]
  exact N.mul_mem (hN h1) hn

theorem r2c_le_normalizer (D : SPLNot3 G) (hRA : R2A D) {N B : Subgroup G} (hN : D.X₂ ≤ N)
    (hNV : N ≤ D.V₂) (hB : B ≤ D.V₂) : B ≤ normalizer (N : Set G) := fun g hg =>
  normalizer_of_both (r2c_norm_of_X₂_le D hRA hN hNV g (hB hg)) (fun n hn => by
    simpa using r2c_norm_of_X₂_le D hRA hN hNV g⁻¹ (D.V₂.inv_mem (hB hg)) n hn)

theorem r2c_X₃_le_normalizer (D : SPLNot3 G) (hRA : R2A D) (hRB : R2B D) :
    D.X₃ ≤ normalizer (D.X₂ : Set G) :=
  r2c_le_normalizer D hRA le_rfl hRA.X₂_le_V₂ hRB.X₃_le_V₂

theorem r2c_X₄_le_normalizer (D : SPLNot3 G) (hRA : R2A D) (hRB : R2B D) :
    D.X₄ ≤ normalizer ((D.X₂ ⊔ D.X₃ : Subgroup G) : Set G) :=
  r2c_le_normalizer D hRA le_sup_left (sup_le hRA.X₂_le_V₂ hRB.X₃_le_V₂) hRB.X₄_le_V₂

theorem r2c_card_X₂_sup_X₃ [Finite G] (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D)
    (hA : SPL3Aa D) (hRA : R2A D) (hRB : R2B D) : Nat.card ↥(D.X₂ ⊔ D.X₃) = D.q ^ 2 := by
  have h := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer
    (r2c_X₃_le_normalizer D hRA hRB)
  rw [r2c_X₂_inf_X₃ D hs h3 hA, Subgroup.card_bot, r2c_X₂_card D h3, r2c_X₃_card D h3,
    mul_one] at h
  rw [h]; ring

theorem r2c_card_R₂ [Finite G] (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0)
    (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3X D) (hA : SPL3Aa D) (hRA : R2A D) (hRB : R2B D)
    (hD1 : ∀ x ∈ D.X, ∀ y ∈ D.X₃, x * y = y * x) : Nat.card ↥D.R₂ = D.q ^ 3 := by
  have h := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer
    (r2c_X₄_le_normalizer D hRA hRB)
  have hinf : (D.X₂ ⊔ D.X₃) ⊓ D.X₄ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx23, hx4⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute
      (fun a ha b hb => r2c_X₂_cen_V₂ D a ha b (hRB.X₃_le_V₂ hb)) hx23
    have hb1 : b * (a * b)⁻¹ ∈ D.X₂ := by
      have e : b * (a * b)⁻¹ = a⁻¹ := by group
      rw [e]; exact D.X₂.inv_mem ha
    obtain ⟨-, hc⟩ := r2c_X₃_X₄ D hs h1 h3 hA hRA hD1 hb hx4 hb1
    rw [hc]; exact Subgroup.one_mem _
  rw [hinf, Subgroup.card_bot, mul_one, r2c_card_X₂_sup_X₃ D hs h3 hA hRA hRB,
    r2c_X₄_card D h3] at h
  show Nat.card ↥(D.X₂ ⊔ D.X₃ ⊔ D.X₄) = _
  rw [h]; ring

theorem r2c_R₂_prod (D : SPLNot3 G) (hRA : R2A D) (hRB : R2B D) :
    (D.R₂ : Set G) = (D.X₂ : Set G) * (D.X₃ : Set G) * (D.X₄ : Set G) := by
  show ((D.X₂ ⊔ D.X₃ ⊔ D.X₄ : Subgroup G) : Set G) = _
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (r2c_X₄_le_normalizer D hRA hRB),
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ (r2c_X₃_le_normalizer D hRA hRB)]

theorem r2c_R₂_le_V₂ (D : SPLNot3 G) (hRA : R2A D) (hRB : R2B D) : D.R₂ ≤ D.V₂ :=
  sup_le (sup_le hRA.X₂_le_V₂ hRB.X₃_le_V₂) hRB.X₄_le_V₂

theorem r2c_C₂_le_normalizer_V₂ (D : SPLNot3 G) (hRA : R2A D) :
    D.C₂ ≤ normalizer (D.V₂ : Set G) := fun g hg =>
  normalizer_of_both (hRA.V₂_norm g hg) (fun v hv => by
    simpa using hRA.V₂_norm g⁻¹ (D.C₂.inv_mem hg) v hv)

theorem r2c_F_inf_C₂ [Finite G] (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0)
    (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3X D)
    (hCX : D.C₂ ⊓ centralizer ({D.z} : Set G) = D.X₂ ⊔ D.K₁) : D.F ⊓ D.C₂ = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxF, hxC₂⟩
  have hxC : x ∈ centralizer ({D.z} : Set G) := F_le_C hs hxF
  have hx : x ∈ D.X₂ ⊔ D.K₁ := by rw [← hCX]; exact ⟨hxC₂, hxC⟩
  have hxK : x ∈ D.K := (sup_le (le_trans (X₂_le_K₂ D hs h3) le_sup_right)
    (le_sup_left : D.K₁ ≤ D.K₁ ⊔ D.K₂)) hx
  have : x ∈ D.F ⊓ D.K := ⟨hxF, hxK⟩
  rw [h1.F_inf_K] at this
  exact this

theorem r2c_card_V₂_le [Finite G] (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0)
    (h1 : SPL2Set D.toSPLNot1) (ho : SPL2Ord D.toSPLNot0) (h3 : SPL3X D) (hRA : R2A D)
    (hRB : R2B D) (hCX : D.C₂ ⊓ centralizer ({D.z} : Set G) = D.X₂ ⊔ D.K₁) :
    Nat.card ↥D.V₂ ≤ D.q ^ 3 := by
  have : Fact D.p.Prime := ⟨hs.prime⟩
  obtain ⟨k, -, hqk⟩ := hs.q_pow
  obtain ⟨PF⟩ : Nonempty (Sylow D.p ↥D.F) := inferInstance
  set P₀ : Subgroup G := (PF : Subgroup ↥D.F).map D.F.subtype with hP₀
  have hP₀F : P₀ ≤ D.F := Subgroup.map_subtype_le _
  have hP₀card : Nat.card ↥P₀ = D.p ^ (Nat.card ↥D.F).factorization D.p := by
    rw [hP₀, Subgroup.card_map_of_injective D.F.subtype_injective]
    exact Sylow.card_eq_multiplicity PF
  have hX₁V : D.X₁ ≤ normalizer (D.V₂ : Set G) := fun x hx =>
    r2c_C₂_le_normalizer_V₂ D hRA (hRA.K₁_le_C₂ (h3.X₁_le hx))
  have hinf1 : D.V₂ ⊓ D.X₁ = ⊥ := by
    rw [eq_bot_iff]
    exact (inf_le_inf_left D.V₂ h3.X₁_le).trans (r2c_V₂_inf_K₁ D hs hRA).le
  have hc1 := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer hX₁V
  rw [hinf1, Subgroup.card_bot, mul_one, h3.X₁_card] at hc1
  have hFQ₁ : Normalizes D.F (D.V₂ ⊔ D.X₁) := normalizes_sup (r2c_F_V₂ D hs h3) h3.F_X₁
  have hP₀N : P₀ ≤ normalizer ((D.V₂ ⊔ D.X₁ : Subgroup G) : Set G) := fun g hg =>
    le_normalizer_of_normalizes hFQ₁ (hP₀F hg)
  have hQ₁C : D.V₂ ⊔ D.X₁ ≤ D.C₂ :=
    sup_le (r2c_V₂_le_C₂ D) (h3.X₁_le.trans hRA.K₁_le_C₂)
  have hinf2 : (D.V₂ ⊔ D.X₁) ⊓ P₀ = ⊥ := by
    rw [eq_bot_iff]
    have : (D.V₂ ⊔ D.X₁) ⊓ P₀ ≤ D.F ⊓ D.C₂ := fun x hx => ⟨hP₀F hx.2, hQ₁C hx.1⟩
    exact this.trans (r2c_F_inf_C₂ D hs h1 h3 hCX).le
  have hc2 := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer hP₀N
  rw [hinf2, Subgroup.card_bot, mul_one, hc1, hP₀card] at hc2
  obtain ⟨a, ha⟩ := hRB.V₂_pgroup.exists_card_eq
  have hQp : IsPGroup D.p ↥(D.V₂ ⊔ D.X₁ ⊔ P₀) := by
    refine IsPGroup.of_card (n := a + k + (Nat.card ↥D.F).factorization D.p) ?_
    rw [hc2, ha, hqk]
    ring
  obtain ⟨T, hQT⟩ := hQp.exists_le_sylow
  have hle := Subgroup.card_le_of_le hQT
  have hT : Nat.card ↥(T : Subgroup G) = D.q ^ 4 * D.p ^ (Nat.card ↥D.F).factorization D.p :=
    ho.card_sylow T
  rw [hc2, hT] at hle
  have hpos : 0 < D.p ^ (Nat.card ↥D.F).factorization D.p := pow_pos hs.prime.pos _
  have hq0 : 0 < D.q := by have := hs.q_ge; omega
  have h4 : Nat.card ↥D.V₂ * D.q ≤ D.q ^ 4 := by
    have : Nat.card ↥D.V₂ * D.q * D.p ^ (Nat.card ↥D.F).factorization D.p ≤
        D.q ^ 4 * D.p ^ (Nat.card ↥D.F).factorization D.p := by simpa using hle
    exact Nat.le_of_mul_le_mul_right this hpos
  have h5 : Nat.card ↥D.V₂ * D.q ≤ D.q ^ 3 * D.q := by rw [← pow_succ]; exact h4
  exact Nat.le_of_mul_le_mul_right h5 hq0

theorem r2c_R₂_eq_V₂ [Finite G] (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0)
    (h1 : SPL2Set D.toSPLNot1) (ho : SPL2Ord D.toSPLNot0) (h3 : SPL3X D) (hA : SPL3Aa D)
    (hRA : R2A D) (hRB : R2B D) (hD1 : ∀ x ∈ D.X, ∀ y ∈ D.X₃, x * y = y * x)
    (hCX : D.C₂ ⊓ centralizer ({D.z} : Set G) = D.X₂ ⊔ D.K₁) : D.R₂ = D.V₂ :=
  Subgroup.eq_of_le_of_card_ge (r2c_R₂_le_V₂ D hRA hRB) (by
    rw [r2c_card_R₂ D hs h1 h3 hA hRA hRB hD1]
    exact r2c_card_V₂_le D hs h1 ho h3 hRA hRB hCX)

theorem r2c_decomp (D : SPLNot3 G) (hRA : R2A D) (hRB : R2B D) (hV : D.R₂ = D.V₂) :
    ∀ v ∈ D.V₂, ∃ a ∈ D.X₂, ∃ b ∈ D.X₃, ∃ c ∈ D.X₄, v = a * b * c := by
  intro v hv
  rw [← hV, ← SetLike.mem_coe, r2c_R₂_prod D hRA hRB] at hv
  obtain ⟨_, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩ := hv
  exact ⟨a, ha, b, hb, c, hc, rfl⟩

theorem r2c_H_le_K [Finite G] (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0)
    (h1 : SPL2Set D.toSPLNot1) : D.H ≤ D.K :=
  sup_le ((H₁_le_K₁ D h1).trans le_sup_left) ((H₂_le_K₂ D hs h1).trans le_sup_right)

theorem r2c_H_X₃ [Finite G] (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1)
    (h3 : SPL3X D) (hA : SPL3Aa D) (hRA : R2A D) (hRB : R2B D)
    (hD1 : ∀ x ∈ D.X, ∀ y ∈ D.X₃, x * y = y * x) (hV : D.R₂ = D.V₂) :
    Normalizes D.H D.X₃ := by
  intro h hh x hx
  have hxV : x ∈ D.V₂ := hRB.X₃_le_V₂ hx
  have hyV : h * x * h⁻¹ ∈ D.V₂ := r2c_H_V₂ D hs h1 h3 h hh x hxV
  have hyX : ∀ g ∈ D.X₁, g * (h * x * h⁻¹) = (h * x * h⁻¹) * g := by
    intro g hg
    have hg' : h⁻¹ * g * h ∈ D.X₁ := by
      have := h3.H_X₁ h⁻¹ (D.H.inv_mem hh) g hg
      simpa using this
    have hc := hD1 _ ((le_sup_left : D.X₁ ≤ D.X₁ ⊔ D.X₂) hg') x hx
    calc g * (h * x * h⁻¹) = h * ((h⁻¹ * g * h) * x) * h⁻¹ := by group
      _ = h * (x * (h⁻¹ * g * h)) * h⁻¹ := by rw [hc]
      _ = (h * x * h⁻¹) * g := by group
  have hzh : h * D.z = D.z * h := z_comm_K D hs (r2c_H_le_K D hs h1 hh)
  have hzy : D.z * (h * x * h⁻¹) * D.z⁻¹ = (h * x * h⁻¹)⁻¹ := by
    have e : D.z * (h * x * h⁻¹) * D.z⁻¹ = h * (D.z * x * D.z⁻¹) * h⁻¹ := by
      calc D.z * (h * x * h⁻¹) * D.z⁻¹ = (D.z * h) * x * (D.z * h)⁻¹ := by group
        _ = (h * D.z) * x * (h * D.z)⁻¹ := by rw [hzh]
        _ = _ := by group
    rw [e, z_inv_X₃ D hs h3 hA x hx]
    group
  obtain ⟨a, ha, b, hb, c, hc, hyabc⟩ := r2c_decomp D hRA hRB hV _ hyV
  have haV : a ∈ D.V₂ := hRA.X₂_le_V₂ ha
  have hbV : b ∈ D.V₂ := hRB.X₃_le_V₂ hb
  have hc1 : c = 1 := by
    refine r2c_key D hs h1 h3 hA hD1 hc (fun g hg => ?_)
    have hga : Commute g a := r2c_K₁_cen_X₂ D hRA g (h3.X₁_le hg) a ha
    have hgb : Commute g b := hD1 g ((le_sup_left : D.X₁ ≤ D.X₁ ⊔ D.X₂) hg) b hb
    have hgy : Commute g (h * x * h⁻¹) := hyX g hg
    rw [hyabc] at hgy
    have h4 : Commute g ((a * b)⁻¹ * (a * b * c)) := (hga.mul_right hgb).inv_right.mul_right hgy
    have e : (a * b)⁻¹ * (a * b * c) = c := by group
    rw [e] at h4
    exact h4
  rw [hc1, mul_one] at hyabc
  rw [hyabc] at hzy
  have hza : D.z * a * D.z⁻¹ = a := r2c_z_cen_X₂ D hs h3 a ha
  have hzb : D.z * b * D.z⁻¹ = b⁻¹ := z_inv_X₃ D hs h3 hA b hb
  have e : D.z * (a * b) * D.z⁻¹ = a * b⁻¹ := by
    calc D.z * (a * b) * D.z⁻¹ = (D.z * a * D.z⁻¹) * (D.z * b * D.z⁻¹) := by group
      _ = a * b⁻¹ := by rw [hza, hzb]
  rw [e] at hzy
  have hab : a * b⁻¹ = b⁻¹ * a := r2c_X₂_cen_V₂ D a ha b⁻¹ (D.V₂.inv_mem hbV)
  have ha2 : a⁻¹ = a := by
    have h5 : b⁻¹ * a = b⁻¹ * a⁻¹ := by
      calc b⁻¹ * a = a * b⁻¹ := hab.symm
        _ = (a * b)⁻¹ := hzy
        _ = b⁻¹ * a⁻¹ := by group
    exact (mul_left_cancel h5).symm
  have ha1 : a = 1 := eq_one_of_inv_eq_self (r2c_odd_p D hs) ((r2c_X₂_eab D h3).2 a ha) ha2
  rw [hyabc, ha1, one_mul]
  exact hb

theorem r2c_odd_mem_of_normal_two_index [Finite G] {C V : Subgroup G} (hV : (V.subgroupOf C).Normal)
    (hVC : V ≤ C) (hk : ∃ k : ℕ, Nat.card ↥C = 2 ^ k * Nat.card ↥V) {u : G} (huC : u ∈ C)
    (hu : Odd (orderOf u)) : u ∈ V := by
  obtain ⟨k, hk⟩ := hk
  have hNcard : Nat.card ↥(V.subgroupOf C) = Nat.card ↥V :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVC).toEquiv
  have hQ : Nat.card (↥C ⧸ V.subgroupOf C) = 2 ^ k := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (V.subgroupOf C)
    rw [hNcard, hk] at h
    have hVpos : 0 < Nat.card ↥V := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_right hVpos h).symm
  let ū : ↥C ⧸ V.subgroupOf C := QuotientGroup.mk ⟨u, huC⟩
  have h1 : orderOf ū ∣ orderOf (⟨u, huC⟩ : ↥C) :=
    orderOf_map_dvd (QuotientGroup.mk' (V.subgroupOf C)) ⟨u, huC⟩
  have h2 : orderOf ū ∣ 2 ^ k := by
    rw [← hQ]; exact orderOf_dvd_natCard ū
  rw [Subgroup.orderOf_mk] at h1
  have hodd : Odd (orderOf ū) := Odd.of_dvd_nat hu h1
  have hcop : Nat.Coprime (orderOf ū) (2 ^ k) := (Nat.coprime_two_right.mpr hodd).pow_right k
  have h3 : orderOf ū = 1 := Nat.Coprime.eq_one_of_dvd hcop h2
  have h4 : ū = 1 := orderOf_eq_one_iff.mp h3
  have h5 : (⟨u, huC⟩ : ↥C) ∈ V.subgroupOf C := (QuotientGroup.eq_one_iff _).mp h4
  exact Subgroup.mem_subgroupOf.mp h5

theorem r2c_exists_sq_root {x : G} (hx : Odd (orderOf x)) : ∃ m : ℕ, x = x ^ m * x ^ m := by
  obtain ⟨m, hm⟩ := hx
  refine ⟨m + 1, ?_⟩
  rw [← pow_add]
  have : (m + 1) + (m + 1) = orderOf x + 1 := by omega
  rw [this, pow_succ, pow_orderOf_eq_one, one_mul]

theorem r2c_orderOf_conj (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  rw [← this]
  rfl

theorem r2c_nonabelian [Finite G] (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0) (h3 : SPL3X D)
    (hA : SPL3Aa D) (hRA : R2A D) (hRB : R2B D) (hD2 : L34Concl D)
    (hVcard : Nat.card ↥D.V₂ = D.q ^ 3) : ∃ u ∈ D.V₂, ∃ v ∈ D.V₂, u * v ≠ v * u := by
  by_contra hcon
  push Not at hcon
  obtain ⟨V, hVC, hVN, hVodd, hVk, hVcomm⟩ := hD2
  have hsq : ∀ v ∈ D.V₂, v * v ∈ D.X₂ ⊔ D.X₃ := by
    intro v hv
    have hvodd : Odd (orderOf v) :=
      Odd.of_dvd_nat hRA.V₂_odd (Subgroup.orderOf_dvd_natCard D.V₂ hv)
    have hu1 : D.a * v * D.a⁻¹ ∈ centralizer (D.Y₁ : Set G) := by
      rw [mem_centralizer_iff]
      intro y hy
      have hy' : D.a⁻¹ * y * D.a ∈ D.X₃ := by
        rw [SPLNot3.X₃, mem_conjBy_iff]
        have e : D.a * (D.a⁻¹ * y * D.a) * D.a⁻¹ = y := by group
        rw [e]; exact hy
      have hc := hcon v hv _ (hRB.X₃_le_V₂ hy')
      calc y * (D.a * v * D.a⁻¹) = D.a * ((D.a⁻¹ * y * D.a) * v) * D.a⁻¹ := by group
        _ = D.a * (v * (D.a⁻¹ * y * D.a)) * D.a⁻¹ := by rw [← hc]
        _ = (D.a * v * D.a⁻¹) * y := by group
    have hu2 : Odd (orderOf (D.a * v * D.a⁻¹)) := by rw [r2c_orderOf_conj]; exact hvodd
    have hu3 : D.a * v * D.a⁻¹ ∈ V := r2c_odd_mem_of_normal_two_index hVN hVC hVk hu1 hu2
    have hcomm : ⁅D.a * v * D.a⁻¹, D.z * D.t⁆ ∈ D.Y₁ := by
      rw [← hVcomm]
      exact Subgroup.commutator_mem_commutator hu3 (Subgroup.mem_zpowers _)
    have hvz : ⁅v, D.z⁆ ∈ D.X₃ := by
      rw [SPLNot3.X₃, mem_conjBy_iff]
      have e : D.a * ⁅v, D.z⁆ * D.a⁻¹ = ⁅D.a * v * D.a⁻¹, D.z * D.t⁆ := by
        rw [← a_z_conj D hs hA, commutatorElement_def, commutatorElement_def]
        group
      rw [e]; exact hcomm
    have hv' : D.z * v⁻¹ * D.z⁻¹ * v⁻¹ ∈ D.X₂ := hRA.z_inv_mod v⁻¹ (D.V₂.inv_mem hv)
    set x₀ := D.z * v⁻¹ * D.z⁻¹ * v⁻¹ with hx₀
    have hx₀v : x₀ * v = D.z * v⁻¹ * D.z⁻¹ := by rw [hx₀]; group
    have hc : x₀ * v = v * x₀ := r2c_X₂_cen_V₂ D x₀ hv' v hv
    have e : v * v = x₀⁻¹ * ⁅v, D.z⁆ := by
      calc v * v = x₀⁻¹ * (x₀ * v) * v := by group
        _ = x₀⁻¹ * (v * x₀) * v := by rw [hc]
        _ = x₀⁻¹ * (v * (x₀ * v)) := by group
        _ = x₀⁻¹ * (v * (D.z * v⁻¹ * D.z⁻¹)) := by rw [hx₀v]
        _ = x₀⁻¹ * ⁅v, D.z⁆ := by rw [commutatorElement_def]; group
    rw [e]
    exact (D.X₂ ⊔ D.X₃).mul_mem (Subgroup.mem_sup_left (D.X₂.inv_mem hv'))
      (Subgroup.mem_sup_right hvz)
  have hle : D.V₂ ≤ D.X₂ ⊔ D.X₃ := by
    intro v hv
    have hvodd : Odd (orderOf v) :=
      Odd.of_dvd_nat hRA.V₂_odd (Subgroup.orderOf_dvd_natCard D.V₂ hv)
    obtain ⟨m, hm⟩ := r2c_exists_sq_root hvodd
    rw [hm]
    exact hsq _ (D.V₂.pow_mem hv m)
  have hcard := Subgroup.card_le_of_le hle
  rw [hVcard, r2c_card_X₂_sup_X₃ D hs h3 hA hRA hRB] at hcard
  have hq : 1 < D.q := by have := hs.q_ge; omega
  have : D.q ^ 2 < D.q ^ 3 := Nat.pow_lt_pow_right hq (by norm_num)
  omega

theorem r2c_irred_X₁_H₁ [Finite G] (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0)
    (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3X D) : IrredUnder (zpowers D.h₁) D.X₁ := by
  obtain ⟨X, hXK, hXc, hXe, hXn, hXne, hKX, htwo, hirr, hcen⟩ :=
    sl2_rootGroups D.K₁ D.q D.p hs.prime hs.comps.sl₁ hs.odd_q hs.q_ge hs.q_pow D.z
      hs.comps.cen₁ D.h₁ D.w₁ h1.h₁_mem h1.w₁_mem h1.h₁_ord h1.w₁_sq h1.w₁_inv h1.nbhd
  have hP : IsPGroup D.p ↥D.X₁ := fun g =>
    ⟨1, by simpa using Subtype.ext (h3.X₁_eab.2 g g.2)⟩
  have hX₁ : D.X₁ = X ∨ D.X₁ = conjBy D.w₁ X :=
    htwo D.X₁ h3.X₁_le hP h3.X₁_card (fun g hg x hx => h3.H_X₁ g (H₁_le_H D hg) x hx)
  rcases hX₁ with h | h
  · rw [h]; exact hirr
  · rw [h]
    exact irredUnder_conjBy D.w₁ hirr (w₁_inv_conj_H₁ D h1)

theorem r2c_irred_X₂ [Finite G] (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0)
    (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3X D) : IrredUnder D.H D.X₂ := by
  refine irredUnder_conjBy D.t ((r2c_irred_X₁_H₁ D hs h1 h3).mono (H₁_le_H D)) ?_
  intro h hh
  have := t_norm_H D hs h1 h hh
  rw [t_inv D hs] at this ⊢
  exact this

theorem r2c_R₂_comm [Finite G] (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0)
    (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3X D) (hRA : R2A D) (hV : D.R₂ = D.V₂)
    (hnab : ∃ u ∈ D.V₂, ∃ v ∈ D.V₂, u * v ≠ v * u) : ⁅D.R₂, D.R₂⁆ = D.X₂ := by
  rw [hV]
  have hle : ⁅D.V₂, D.V₂⁆ ≤ D.X₂ := Subgroup.commutator_le.mpr hRA.V₂_class2
  have hN : Normalizes D.H ⁅D.V₂, D.V₂⁆ :=
    (r2c_H_V₂ D hs h1 h3).commutator (r2c_H_V₂ D hs h1 h3)
  rcases r2c_irred_X₂ D hs h1 h3 _ hle hN with hbot | heq
  · exfalso
    obtain ⟨u, hu, v, hv, huv⟩ := hnab
    apply huv
    have h5 : ⁅u, v⁆ ∈ ⁅D.V₂, D.V₂⁆ := Subgroup.commutator_mem_commutator hu hv
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h5
    exact h5
  · exact heq

theorem r2c_sl2_trans {F : Type} [Field F] {a₀ a₁ : Fin 2 → F} (h₀ : a₀ ≠ 0) (h₁ : a₁ ≠ 0) :
    ∃ M : Matrix.SpecialLinearGroup (Fin 2) F,
      (M : Matrix (Fin 2) (Fin 2) F).mulVec a₀ = a₁ := by
  have key : ∀ v : Fin 2 → F, v ≠ 0 →
      ∃ M : Matrix.SpecialLinearGroup (Fin 2) F,
        (M : Matrix (Fin 2) (Fin 2) F).mulVec (Pi.single 0 1) = v := by
    intro v hv
    by_cases h0 : v 0 = 0
    · have h1 : v 1 ≠ 0 := by
        intro h; apply hv; ext i; fin_cases i <;> simp [h0, h]
      refine ⟨⟨!![0, -(v 1)⁻¹; v 1, 0], ?_⟩, ?_⟩
      · rw [Matrix.det_fin_two_of]; field_simp; ring
      · ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0]
    · refine ⟨⟨!![v 0, 0; v 1, (v 0)⁻¹], ?_⟩, ?_⟩
      · rw [Matrix.det_fin_two_of]; field_simp; ring
      · ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  obtain ⟨M₀, hM₀⟩ := key a₀ h₀
  obtain ⟨M₁, hM₁⟩ := key a₁ h₁
  refine ⟨M₁ * M₀⁻¹, ?_⟩
  have e1 : ((M₀⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec a₀ =
      Pi.single 0 1 := by
    rw [← hM₀, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, e1, hM₁]

theorem r2c_commutator_le (D : SPLNot3 G) (hRA : R2A D) :
    commutator ↥D.V₂ ≤ D.X₂.subgroupOf D.V₂ := by
  rw [commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  show ((⁅g₁, g₂⁆ : ↥D.V₂) : G) ∈ D.X₂
  exact hRA.V₂_class2 g₁ g₁.2 g₂ g₂.2

theorem r2c_z_nontrivial_mod_X₂ [Finite G] (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0)
    (h3 : SPL3X D) (hA : SPL3Aa D) (hRB : R2B D) :
    ∃ r ∈ D.V₂, D.z * r * D.z⁻¹ * r⁻¹ ∉ D.X₂ := by
  obtain ⟨x, hx, hx1⟩ := exists_ne_one_of_two_le D.X₃ (by
    rw [r2c_X₃_card D h3]; have := hs.q_ge; omega)
  refine ⟨x, hRB.X₃_le_V₂ hx, fun hmem => ?_⟩
  have h1' := z_inv_X₃ D hs h3 hA x hx
  have e : D.z * x * D.z⁻¹ * x⁻¹ = x⁻¹ * x⁻¹ := by rw [h1']
  rw [e] at hmem
  have hX₃ : x⁻¹ * x⁻¹ ∈ D.X₃ := D.X₃.mul_mem (D.X₃.inv_mem hx) (D.X₃.inv_mem hx)
  have h12 : x⁻¹ * x⁻¹ ∈ D.X₂ ⊓ D.X₃ := ⟨hmem, hX₃⟩
  rw [r2c_X₂_inf_X₃ D hs h3 hA] at h12
  have h0 : x⁻¹ * x⁻¹ = 1 := Subgroup.mem_bot.mp h12
  have hxx : x * x = 1 := by
    have := congrArg (fun y => y⁻¹) h0
    simpa [mul_inv_rev] using this
  exact hx1 (eq_one_of_inv_eq_self (r2c_odd_p D hs) ((r2c_X₃_eab D h3).2 x hx)
    (inv_eq_of_mul_eq_one_right hxx))

theorem r2c_trans [Finite G] (hNM : NatModStmt) (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0)
    (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3X D) (hA : SPL3Aa D) (hRA : R2A D) (hRB : R2B D)
    (hV : D.R₂ = D.V₂) (hVcard : Nat.card ↥D.V₂ = D.q ^ 3) :
    ∀ c ∈ D.V₂, c ∉ D.X₂ → ∀ u ∈ D.V₂, u ∉ D.X₂ → ∃ k ∈ D.K₁, (k * c * k⁻¹)⁻¹ * u ∈ D.X₂ := by
  classical
  obtain ⟨F, hFfield, hFfin, ε, hFq, hE1, hE2, hE3⟩ :=
    sl2_iso_data D.K₁ D.q D.p hs.prime hs.comps.sl₁ hs.odd_q hs.q_ge hs.q_pow D.h₁ D.w₁ h1.h₁_mem
      h1.w₁_mem h1.h₁_ord h1.w₁_inv D.X₁ h3.X₁_le h3.X₁_card
      (fun g hg x hx => h3.H_X₁ g (H₁_le_H D hg) x hx)
  obtain ⟨k, -, hqk⟩ := hs.q_pow
  have hFq' : Nat.card F = D.p ^ k := hFq.trans hqk
  have hX₂V : D.X₂ ≤ D.V₂ := hRA.X₂_le_V₂
  have hKR : ∀ k ∈ D.K₁, ∀ r ∈ D.V₂, k * r * k⁻¹ ∈ D.V₂ := fun k hk r hr =>
    hRA.V₂_norm k (hRA.K₁_le_C₂ hk) r hr
  have hKX₂ := r2c_K₁_cen_X₂ D hRA
  have hX₂c := r2c_X₂_cen_V₂ D
  have hnorm : (D.X₂.subgroupOf D.V₂).Normal := subgroupOf_normal_of_central D.V₂ D.X₂ hX₂c
  have _hnorm := hnorm
  have hcomm : IsMulCommutative (↥D.V₂ ⧸ D.X₂.subgroupOf D.V₂) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr (r2c_commutator_le D hRA)
  let instCG : CommGroup (↥D.V₂ ⧸ D.X₂.subgroupOf D.V₂) :=
    { (inferInstance : Group (↥D.V₂ ⧸ D.X₂.subgroupOf D.V₂)) with
      mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
  let π : ↥D.V₂ →* (↥D.V₂ ⧸ D.X₂.subgroupOf D.V₂) := QuotientGroup.mk' _
  let ρ := quotAct D.V₂ D.X₂ D.K₁ hKR hKX₂ hnorm
  have hπker : ∀ r : ↥D.V₂, π r = 1 ↔ (r : G) ∈ D.X₂ := fun r => by
    show QuotientGroup.mk r = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    rfl
  have hπsurj : Function.Surjective π := QuotientGroup.mk_surjective
  have hexp : ∀ v : ↥D.V₂ ⧸ D.X₂.subgroupOf D.V₂, v ^ D.p = 1 := by
    intro v
    obtain ⟨⟨r, hr⟩, rfl⟩ := hπsurj v
    obtain ⟨y, hy, a, ha, b, hb, rfl⟩ := r2c_decomp D hRA hRB hV r hr
    have hya : π ⟨y * a * b, hr⟩ = π ⟨a, hRB.X₃_le_V₂ ha⟩ * π ⟨b, hRB.X₄_le_V₂ hb⟩ := by
      have e : (⟨y * a * b, hr⟩ : ↥D.V₂) =
          ⟨y, hX₂V hy⟩ * ⟨a, hRB.X₃_le_V₂ ha⟩ * ⟨b, hRB.X₄_le_V₂ hb⟩ := rfl
      rw [e, map_mul, map_mul, (hπker ⟨y, hX₂V hy⟩).2 hy, one_mul]
    rw [hya, mul_pow, ← map_pow, ← map_pow]
    have ha' : (⟨a, hRB.X₃_le_V₂ ha⟩ : ↥D.V₂) ^ D.p = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact (r2c_X₃_eab D h3).2 a ha)
    have hb' : (⟨b, hRB.X₄_le_V₂ hb⟩ : ↥D.V₂) ^ D.p = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact (r2c_X₄_eab D h3).2 b hb)
    rw [ha', hb']
    simp
  have hVq : Nat.card (↥D.V₂ ⧸ D.X₂.subgroupOf D.V₂) = D.p ^ (2 * k) := by
    have h1' := Subgroup.card_eq_card_quotient_mul_card_subgroup (D.X₂.subgroupOf D.V₂)
    have h2' : Nat.card (D.X₂.subgroupOf D.V₂) = D.q := by
      rw [← r2c_X₂_card D h3]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX₂V).toEquiv
    rw [hVcard, h2'] at h1'
    have hq0 : 0 < D.q := by have := hs.q_ge; omega
    have : Nat.card (↥D.V₂ ⧸ D.X₂.subgroupOf D.V₂) = D.q ^ 2 := by
      apply Nat.eq_of_mul_eq_mul_right hq0
      rw [← h1']; ring
    rw [this, hqk, ← pow_mul, mul_comm]
  have hz := r2c_z_nontrivial_mod_X₂ D hs h3 hA hRB
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    apply Subtype.ext
    rw [Subgroup.coe_one]
    refine kernel_eq_one_of_quasisimple D.K₁ D.V₂ D.X₂ D.z hs.comps.quasi₁ hs.comps.cen₁
      (z_mul_z D hs) hKR ?_ (z_mem_K₁ hs) hz k.2 ?_
    · intro k' hk' y hy
      have : k' * y * k'⁻¹ = y := by rw [hKX₂ k' hk' y hy]; group
      rw [this]; exact hy
    · intro r hr
      have e := congrArg (fun f => f (QuotientGroup.mk ⟨r, hr⟩)) hk
      simp only [MulAut.one_apply] at e
      rw [show ρ k (QuotientGroup.mk ⟨r, hr⟩) =
        QuotientGroup.mk (conjOn D.V₂ D.K₁ hKR k ⟨r, hr⟩) from rfl] at e
      have e2 := (QuotientGroup.eq).mp e
      have e3 : ((k : G) * r * (k : G)⁻¹)⁻¹ * r ∈ D.X₂ := e2
      have e4 : r⁻¹ * ((k : G) * r * (k : G)⁻¹) ∈ D.X₂ := by
        have := D.X₂.inv_mem e3
        simpa [mul_assoc] using this
      have e5 := hX₂c _ e4 r hr
      have h6 : r * (r⁻¹ * ((k : G) * r * (k : G)⁻¹)) =
          (r⁻¹ * ((k : G) * r * (k : G)⁻¹)) * r := e5.symm
      have : (k : G) * r * (k : G)⁻¹ * r⁻¹ = r⁻¹ * ((k : G) * r * (k : G)⁻¹) := by
        calc (k : G) * r * (k : G)⁻¹ * r⁻¹
            = (r * (r⁻¹ * ((k : G) * r * (k : G)⁻¹))) * r⁻¹ := by group
          _ = ((r⁻¹ * ((k : G) * r * (k : G)⁻¹)) * r) * r⁻¹ := by rw [h6]
          _ = _ := by group
      rw [this]; exact e4
  obtain ⟨τ, hτ⟩ := hNM hs.prime hs.p_ne_two hFq' ε hexp hVq ρ hρinj
  intro c hc hcX u hu huX
  have hc1 : π ⟨c, hc⟩ ≠ 1 := fun h => hcX ((hπker _).1 h)
  have hu1 : π ⟨u, hu⟩ ≠ 1 := fun h => huX ((hπker _).1 h)
  have hτc : Multiplicative.toAdd (τ (π ⟨c, hc⟩)) ≠ 0 := by
    intro h
    apply hc1
    apply τ.injective
    rw [map_one]
    exact toAdd_eq_zero.mp h
  have hτu : Multiplicative.toAdd (τ (π ⟨u, hu⟩)) ≠ 0 := by
    intro h
    apply hu1
    apply τ.injective
    rw [map_one]
    exact toAdd_eq_zero.mp h
  obtain ⟨M, hM⟩ := r2c_sl2_trans hτc hτu
  refine ⟨((ε.symm M : ↥D.K₁) : G), (ε.symm M).2, ?_⟩
  have e := hτ (ε.symm M) (π ⟨c, hc⟩)
  rw [MulEquiv.apply_symm_apply, hM] at e
  have e1 : ρ (ε.symm M) (π ⟨c, hc⟩) = π ⟨u, hu⟩ := τ.injective (by rw [e]; simp)
  have e3 := (QuotientGroup.eq).mp e1
  exact Subgroup.mem_subgroupOf.mp e3

theorem r2c_R₂_center [Finite G] (hNM : NatModStmt) (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0)
    (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3X D) (hA : SPL3Aa D) (hRA : R2A D) (hRB : R2B D)
    (hV : D.R₂ = D.V₂) (hVcard : Nat.card ↥D.V₂ = D.q ^ 3)
    (hnab : ∃ u ∈ D.V₂, ∃ v ∈ D.V₂, u * v ≠ v * u) :
    (center ↥D.R₂).map D.R₂.subtype = D.X₂ := by
  have hX₂R : D.X₂ ≤ D.R₂ := le_sup_left.trans le_sup_left
  have hX₂V : D.X₂ ≤ D.V₂ := hRA.X₂_le_V₂
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    by_contra hcX
    have hcX' : (c : G) ∉ D.X₂ := hcX
    have hcV : (c : G) ∈ D.V₂ := by rw [← hV]; exact c.2
    have hcen : ∀ r ∈ D.V₂, (c : G) * r = r * (c : G) := by
      intro r hr
      have := Subgroup.mem_center_iff.mp hc ⟨r, by rw [hV]; exact hr⟩
      exact (congrArg Subtype.val this).symm
    obtain ⟨u₀, hu₀, v₀, hv₀, hne⟩ := hnab
    apply hne
    have hucen : ∀ u ∈ D.V₂, ∀ v ∈ D.V₂, u * v = v * u := by
      intro u hu v hv
      by_cases huX : u ∈ D.X₂
      · exact r2c_X₂_cen_V₂ D u huX v hv
      · obtain ⟨k, hk, hkx⟩ := r2c_trans hNM D hs h1 h3 hA hRA hRB hV hVcard c hcV hcX' u hu huX
        have hu_eq : u = (k * c * k⁻¹) * ((k * c * k⁻¹)⁻¹ * u) := by group
        have hkc : ∀ v ∈ D.V₂, (k * c * k⁻¹) * v = v * (k * c * k⁻¹) := by
          intro v hv
          have hv' : k⁻¹ * v * k ∈ D.V₂ := by
            have := hRA.V₂_norm k⁻¹ (hRA.K₁_le_C₂ (D.K₁.inv_mem hk)) v hv
            simpa using this
          have h := hcen _ hv'
          calc (k * c * k⁻¹) * v = k * (c * (k⁻¹ * v * k)) * k⁻¹ := by group
            _ = k * ((k⁻¹ * v * k) * c) * k⁻¹ := by rw [h]
            _ = v * (k * c * k⁻¹) := by group
        rw [hu_eq]
        calc (k * c * k⁻¹) * ((k * c * k⁻¹)⁻¹ * u) * v
            = (k * c * k⁻¹) * (((k * c * k⁻¹)⁻¹ * u) * v) := by group
          _ = (k * c * k⁻¹) * (v * ((k * c * k⁻¹)⁻¹ * u)) := by
              rw [r2c_X₂_cen_V₂ D _ hkx v hv]
          _ = ((k * c * k⁻¹) * v) * ((k * c * k⁻¹)⁻¹ * u) := by group
          _ = (v * (k * c * k⁻¹)) * ((k * c * k⁻¹)⁻¹ * u) := by rw [hkc v hv]
          _ = v * ((k * c * k⁻¹) * ((k * c * k⁻¹)⁻¹ * u)) := by group
    exact hucen u₀ hu₀ v₀ hv₀
  · intro hx
    refine ⟨⟨x, hX₂R hx⟩, Subgroup.mem_center_iff.mpr (fun g => ?_), rfl⟩
    exact Subtype.ext (r2c_X₂_cen_V₂ D x hx g (by rw [← hV]; exact g.2)).symm

theorem r2C_of_inputs (hNM : NatModStmt) {G : Type} [Group G] [Finite G] (D : SPLNot3 G)
    (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (hc : SPL2Ct D.toSPLNot2)
    (ho : SPL2Ord D.toSPLNot0) (h3 : SPL3X D) (hA : SPL3Aa D) (hRA : R2A D) (hRB : R2B D)
    (hD1 : ∀ x ∈ D.X, ∀ y ∈ D.X₃, x * y = y * x) (hD2 : L34Concl D)
    (hCX : D.C₂ ⊓ centralizer ({D.z} : Set G) = D.X₂ ⊔ D.K₁) : SPL3R2 D := by
  have _ := hc
  have hV := r2c_R₂_eq_V₂ D hs h1 ho h3 hA hRA hRB hD1 hCX
  have hRcard := r2c_card_R₂ D hs h1 h3 hA hRA hRB hD1
  have hVcard : Nat.card ↥D.V₂ = D.q ^ 3 := by rw [← hV]; exact hRcard
  have hnab := r2c_nonabelian D hs h3 hA hRA hRB hD2 hVcard
  exact
    { X₁_X₃ := fun x hx y hy => hD1 x ((le_sup_left : D.X₁ ≤ D.X₁ ⊔ D.X₂) hx) y hy
      R₂_prod := r2c_R₂_prod D hRA hRB
      H_X₃ := r2c_H_X₃ D hs h1 h3 hA hRA hRB hD1 hV
      R₂_normal := by rw [hV]; exact r2c_M₂_norm_V₂ D
      R₂_card := hRcard
      R₂_center := r2c_R₂_center hNM D hs h1 h3 hA hRA hRB hV hVcard hnab
      R₂_comm := r2c_R₂_comm D hs h1 h3 hRA hV hnab }

end R2C

end CFSG.GH74.GLS.SP.Local
