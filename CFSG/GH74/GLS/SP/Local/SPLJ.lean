module

public import CFSG.GH74.GLS.SP.Local.SPLBruhat
public import CFSG.GH74.GLS.SP.Local.SPLRoot2
public import CFSG.GH74.GLS.SP.Local.SPLSet
public import CFSG.GH74.GLS.SP.Local.SPLY1

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

structure SPLAlpha (D : SPLNot3 G) (α : ↥D.K₁ ≃* ↥D.K₁) : Prop where
  inv_X₁ : ∀ x : ↥D.K₁, (x : G) ∈ D.X₁ → (α x : G) = (x : G)⁻¹
  fix_H₁ : ∀ g : ↥D.K₁, (g : G) ∈ zpowers D.h₁ → α g = g
  img_w₁ : ∀ g : ↥D.K₁, (g : G) = D.w₁ → (α g : G) = D.w₁ * D.z
  invol : ∀ k, α (α k) = k

@[expose] noncomputable def theta [Finite G] (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0)
    (α : ↥D.K₁ ≃* ↥D.K₁) : ↥D.K₁ →* G where
  toFun k := (α k : G) * (D.t * (k : G) * D.t⁻¹)
  map_one' := by simp
  map_mul' k k' := by
    have hc : (α k' : G) * (D.t * (k : G) * D.t⁻¹) = (D.t * (k : G) * D.t⁻¹) * (α k' : G) :=
      hs.comps.comm _ (α k').2 _ (t_conj_K₁ D hs _ k.2)
    simp only [map_mul, Subgroup.coe_mul]
    calc (α k : G) * (α k' : G) * (D.t * ((k : G) * (k' : G)) * D.t⁻¹)
        = (α k : G) * ((α k' : G) * (D.t * (k : G) * D.t⁻¹)) * (D.t * (k' : G) * D.t⁻¹) := by
          group
      _ = (α k : G) * ((D.t * (k : G) * D.t⁻¹) * (α k' : G)) * (D.t * (k' : G) * D.t⁻¹) := by
          rw [hc]
      _ = _ := by group

theorem theta_apply [Finite G] (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0) (α : ↥D.K₁ ≃* ↥D.K₁)
    (k : ↥D.K₁) : theta D hs α k = (α k : G) * (D.t * (k : G) * D.t⁻¹) := rfl

theorem theta_mem_K [Finite G] (D : SPLNot3 G) (hs : SPLSetup D.toSPLNot0) (α : ↥D.K₁ ≃* ↥D.K₁)
    (k : ↥D.K₁) : theta D hs α k ∈ D.K := by
  rw [theta_apply]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (α k).2)
    (Subgroup.mem_sup_right (t_conj_K₁ D hs _ k.2))

section ThetaFacts

variable [Finite G] (D : SPLNot3 G) {α : ↥D.K₁ ≃* ↥D.K₁}

omit [Finite G] in
theorem alpha_z (h1 : SPL2Set D.toSPLNot1) (hα : SPLAlpha D α) (g : ↥D.K₁)
    (hg : (g : G) ∈ zpowers D.z) : α g = g :=
  hα.fix_H₁ g ((zpowers_le.mpr (z_mem_H₁ D h1)) hg)

theorem theta_eq_one_iff (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1)
    (hα : SPLAlpha D α) (k : ↥D.K₁) :
    theta D hs α k = 1 ↔ (k : G) ∈ zpowers D.z := by
  rw [theta_apply]
  constructor
  · intro hk
    have h2 : (α k : G) = (D.t * (k : G) * D.t⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hk
    have h3' : (α k : G) ∈ D.K₂ := by
      rw [h2]; exact Subgroup.inv_mem _ (t_conj_K₁ D hs _ k.2)
    have h4 : (α k : G) ∈ D.K₁ ⊓ D.K₂ := ⟨(α k).2, h3'⟩
    rw [hs.comps.inf_eq] at h4
    have h5 : α (α k) = α k := alpha_z D h1 hα (α k) h4
    have h6 : k = α k := by
      have := hα.invol k
      rw [h5] at this
      exact this.symm
    have h7 : (k : G) = (α k : G) := congrArg Subtype.val h6
    rw [h7]; exact h4
  · intro hk
    have hk' : α k = k := alpha_z D h1 hα k hk
    have hz2 := z_mul_z D hs
    have hcomm := t_comm_z D hs
    rcases eq_one_or_z hs hk with h | h
    · rw [hk', h]; simp
    · rw [hk', h]
      have : D.t * D.z * D.t⁻¹ = D.z := by
        calc D.t * D.z * D.t⁻¹ = D.z * D.t * D.t⁻¹ := by rw [hcomm]
          _ = D.z := by group
      rw [this]; exact hz2

omit [Finite G] in
theorem z_not_mem_X₁ (hs : SPLSetup D.toSPLNot0) (h3 : SPL3M2 D) : D.z ∉ D.X₁ := by
  intro hz
  have h := h3.X₁_eab.2 D.z hz
  have h2 : orderOf D.z ∣ D.p := orderOf_dvd_of_pow_eq_one h
  rw [hs.syl.z_inv] at h2
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hs.prime).mp h2
  exact hs.p_ne_two this.symm

theorem X₁_inf_X₂ (hs : SPLSetup D.toSPLNot0) (h3 : SPL3M2 D) :
    D.X₁ ⊓ conjBy D.t D.X₁ = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  have hxK : x ∈ D.K₁ ⊓ D.K₂ := ⟨h3.X₁_le hx1, X₂_le_K₂ D hs h3.toSPL3X hx2⟩
  rw [hs.comps.inf_eq] at hxK
  rcases eq_one_or_z hs hxK with h | h
  · rw [h]; exact Subgroup.one_mem _
  · exact absurd (h ▸ hx1) (z_not_mem_X₁ D hs h3)

theorem mem_Y₁_iff (hs : SPLSetup D.toSPLNot0) (h3 : SPL3M2 D) (hα : SPLAlpha D α) (y : G) :
    y ∈ D.Y₁ ↔ ∃ k : ↥D.K₁, (k : G) ∈ D.X₁ ∧ theta D hs α k = y := by
  have ht := t_mul_t D hs
  have hcomm : ∀ a ∈ D.X₁, ∀ b ∈ conjBy D.t D.X₁, a * b = b * a := fun a ha b hb =>
    hs.comps.comm a (h3.X₁_le ha) b (X₂_le_K₂ D hs h3.toSPL3X hb)
  obtain ⟨φ, hφ, -, -, -⟩ := Y1_spec ht h3.X₁_eab hcomm (X₁_inf_X₂ D hs h3)
  have hY : D.Y₁ = ⁅D.X₁ ⊔ conjBy D.t D.X₁, zpowers D.t⁆ := h3.Y₁_eq
  constructor
  · intro hy
    rw [hY] at hy
    obtain ⟨u, hu⟩ : ∃ u : ↥D.X₁, (φ u : G) = y := by
      obtain ⟨u, hu⟩ := φ.surjective ⟨y, hy⟩
      exact ⟨u, congrArg Subtype.val hu⟩
    have hu' : (u : G)⁻¹ ∈ D.K₁ := Subgroup.inv_mem _ (h3.X₁_le u.2)
    refine ⟨⟨(u : G)⁻¹, hu'⟩, Subgroup.inv_mem _ u.2, ?_⟩
    rw [theta_apply, hα.inv_X₁ _ (Subgroup.inv_mem _ u.2), ← hu, hφ]
    simp
  · rintro ⟨k, hk, rfl⟩
    rw [hY]
    have hk' : (k : G)⁻¹ ∈ D.X₁ := Subgroup.inv_mem _ hk
    have := (φ ⟨(k : G)⁻¹, hk'⟩).2
    have e : (φ ⟨(k : G)⁻¹, hk'⟩ : G) = theta D hs α k := by
      rw [hφ, theta_apply, hα.inv_X₁ _ hk]
      simp
    rw [← e]; exact this

end ThetaFacts

section ThetaFacts2

variable [Finite G] (D : SPLNot3 G) {α : ↥D.K₁ ≃* ↥D.K₁}

theorem mem_H₀_iff (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (hα : SPLAlpha D α)
    (y : G) : y ∈ D.H₀ ↔ ∃ k : ↥D.K₁, (k : G) ∈ zpowers D.h₁ ∧ theta D hs α k = y := by
  have hcomm : Commute D.h₁ D.h₂ := H₁_H₂_comm D hs h1 _ (mem_zpowers _) _ (mem_zpowers _)
  constructor
  · intro hy
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
    have hk : D.h₁ ^ i ∈ D.K₁ := zpow_mem h1.h₁_mem i
    refine ⟨⟨D.h₁ ^ i, hk⟩, mem_zpowers_iff.mpr ⟨i, rfl⟩, ?_⟩
    rw [theta_apply, hα.fix_H₁ _ (mem_zpowers_iff.mpr ⟨i, rfl⟩)]
    show D.h₁ ^ i * (D.t * D.h₁ ^ i * D.t⁻¹) = (D.h₁ * D.h₂) ^ i
    rw [hcomm.mul_zpow]
    congr 1
    unfold SPLNot1.h₂
    rw [conj_zpow]
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hk
    rw [theta_apply, hα.fix_H₁ _ hk, ← hi]
    show D.h₁ ^ i * (D.t * D.h₁ ^ i * D.t⁻¹) ∈ D.H₀
    have : D.h₁ ^ i * (D.t * D.h₁ ^ i * D.t⁻¹) = (D.h₁ * D.h₂) ^ i := by
      rw [hcomm.mul_zpow]
      congr 1
      unfold SPLNot1.h₂
      rw [conj_zpow]
    rw [this]
    exact zpow_mem (mem_zpowers _) i

theorem ker_theta_map (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (hα : SPLAlpha D α) :
    (theta D hs α).ker.map D.K₁.subtype = zpowers D.z := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact (theta_eq_one_iff D hs h1 hα k).mp hk
  · intro hx
    refine ⟨⟨x, ?_⟩, ?_, rfl⟩
    · obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
      exact zpow_mem (z_mem_K₁ hs) i
    · exact (theta_eq_one_iff D hs h1 hα _).mpr hx

theorem card_ker_theta (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (hα : SPLAlpha D α) :
    Nat.card (theta D hs α).ker = 2 := by
  have h := ker_theta_map D hs h1 hα
  have h2 : Nat.card ((theta D hs α).ker.map D.K₁.subtype) = Nat.card (theta D hs α).ker :=
    Subgroup.card_map_of_injective D.K₁.subtype_injective
  rw [← h2, h, Nat.card_zpowers, hs.syl.z_inv]

theorem card_J (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (hα : SPLAlpha D α) :
    Nat.card (theta D hs α).range * 2 = D.q * (D.q ^ 2 - 1) := by
  have h := Subgroup.card_ker_mul_card_range (theta D hs α)
  rw [card_ker_theta D hs h1 hα, card_K₁ hs] at h
  omega

structure SPLK1Facts (D : SPLNot3 G) : Prop where
  norm_X₁ : normalizer (D.X₁ : Set G) ⊓ D.K₁ = D.X₁ ⊔ zpowers D.h₁
  bruhat : ∀ k ∈ D.K₁, k ∈ ((D.X₁ ⊔ zpowers D.h₁ : Subgroup G) : Set G) ∨
    k ∈ ((D.X₁ ⊔ zpowers D.h₁ : Subgroup G) : Set G) * {D.w₁} * (D.X₁ : Set G)
  opp : ∀ y ∈ conjBy D.w₁ D.X₁, y ≠ 1 →
    y ∈ (D.X₁ : Set G) * (zpowers D.h₁ : Set G) * {D.w₁} * (D.X₁ : Set G)

theorem exists_alpha (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    ∃ α : ↥D.K₁ ≃* ↥D.K₁, SPLAlpha D α ∧ SPLK1Facts D := by
  have hXn : ∀ g ∈ zpowers D.h₁, ∀ x ∈ D.X₁, g * x * g⁻¹ ∈ D.X₁ := fun g hg x hx =>
    h3.H_X₁ g (H₁_le_H D hg) x hx
  obtain ⟨⟨α, hinv, hfix, himg, hinvol⟩, hN, hBr, hopp⟩ :=
    sl2_diagAut_bruhat D.K₁ D.q D.p hs.prime hs.comps.sl₁ hs.odd_q hs.q_ge hs.q_pow D.z
      hs.comps.cen₁ D.h₁ D.w₁ h1.h₁_mem h1.w₁_mem h1.h₁_ord h1.w₁_sq h1.w₁_inv h1.nbhd D.X₁
      h3.X₁_le h3.X₁_card hXn
  refine ⟨α, ⟨hinv, hfix, fun g hg => ?_, hinvol⟩, ⟨hN, hBr, hopp⟩⟩
  have : g = ⟨D.w₁, h1.w₁_mem⟩ := Subtype.ext hg
  rw [this]; exact himg

end ThetaFacts2

section JFacts

variable [Finite G] (D : SPLNot3 G) {α : ↥D.K₁ ≃* ↥D.K₁}

omit [Finite G] in
theorem H₁_le_normalizer_X₁ (h3 : SPL3M2 D) : zpowers D.h₁ ≤ normalizer (D.X₁ : Set G) :=
  (H₁_le_H D).trans (le_normalizer_of_normalizes h3.H_X₁)

theorem theta_X₁_sup_mem (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D)
    (hα : SPLAlpha D α) {b : G} (hb : b ∈ ((D.X₁ ⊔ zpowers D.h₁ : Subgroup G) : Set G))
    (hbK : b ∈ D.K₁) : theta D hs α ⟨b, hbK⟩ ∈ ((D.Y₁ ⊔ D.H₀ : Subgroup G) : Set G) := by
  rw [Subgroup.coe_mul_of_right_le_normalizer_left D.X₁ (zpowers D.h₁)
    (H₁_le_normalizer_X₁ D h3)] at hb
  obtain ⟨x, hx, g, hg, rfl⟩ := hb
  have hx' : x ∈ D.K₁ := h3.X₁_le hx
  have hg' : g ∈ D.K₁ := H₁_le_K₁ D h1 hg
  have e : (⟨x * g, hbK⟩ : ↥D.K₁) = ⟨x, hx'⟩ * ⟨g, hg'⟩ := rfl
  rw [e, map_mul]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_left ((mem_Y₁_iff D hs h3 hα _).mpr ⟨⟨x, hx'⟩, hx, rfl⟩))
    (Subgroup.mem_sup_right ((mem_H₀_iff D hs h1 hα _).mpr ⟨⟨g, hg'⟩, hg, rfl⟩))

theorem theta_w₁ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (hα : SPLAlpha D α) :
    theta D hs α ⟨D.w₁, h1.w₁_mem⟩ = D.z * D.w := by
  rw [theta_apply, hα.img_w₁ _ rfl]
  show D.w₁ * D.z * (D.t * D.w₁ * D.t⁻¹) = D.z * (D.w₁ * (D.t * D.w₁ * D.t⁻¹))
  rw [w₁_comm_z D hs h1]
  group

theorem mem_normalizer_of_conj_le {g : G} {A : Subgroup G} (h : ∀ x ∈ A, g * x * g⁻¹ ∈ A) :
    g ∈ normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : A.map (MulAut.conj g).toMonoidHom ≤ A := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using h x hx
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])

end JFacts

section JFacts2

variable [Finite G] (D : SPLNot3 G) {α : ↥D.K₁ ≃* ↥D.K₁}

theorem H₀_normalizes_Y₁ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1)
    (h3 : SPL3M2 D) (hα : SPLAlpha D α) :
    ∀ h ∈ D.H₀, ∀ y ∈ D.Y₁, h * y * h⁻¹ ∈ D.Y₁ := by
  intro h hh y hy
  obtain ⟨kh, hkh, rfl⟩ := (mem_H₀_iff D hs h1 hα h).mp hh
  obtain ⟨ku, hku, rfl⟩ := (mem_Y₁_iff D hs h3 hα y).mp hy
  refine (mem_Y₁_iff D hs h3 hα _).mpr ⟨kh * ku * kh⁻¹, ?_, ?_⟩
  · show (kh : G) * (ku : G) * (kh : G)⁻¹ ∈ D.X₁
    exact h3.H_X₁ _ (H₁_le_H D hkh) _ hku
  · simp [map_mul, map_inv]

theorem theta_opp (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D)
    (hα : SPLAlpha D α) (hK : SPLK1Facts D) :
    ∀ y ∈ conjBy (D.z * D.w) D.Y₁, y ≠ 1 →
      y ∈ ((D.Y₁ ⊔ D.H₀ : Subgroup G) : Set G) * {D.z * D.w} *
        ((D.Y₁ ⊔ D.H₀ : Subgroup G) : Set G) := by
  intro y hy hy1
  rw [mem_conjBy_iff] at hy
  obtain ⟨ku, hku, hθ⟩ := (mem_Y₁_iff D hs h3 hα _).mp hy
  set wk : ↥D.K₁ := ⟨D.w₁, h1.w₁_mem⟩ with hwk
  have hw : theta D hs α wk = D.z * D.w := theta_w₁ D hs h1 hα
  set u' : ↥D.K₁ := wk⁻¹ * ku * wk with hu'
  have hyθ : theta D hs α u' = y := by
    rw [hu', map_mul, map_mul, map_inv, hw, hθ]
    group
  have hmem : (u' : G) ∈ conjBy D.w₁ D.X₁ := by
    rw [mem_conjBy_iff]
    have : D.w₁ * (u' : G) * D.w₁⁻¹ = (ku : G) := by
      show D.w₁ * ((D.w₁)⁻¹ * (ku : G) * D.w₁) * D.w₁⁻¹ = (ku : G)
      group
    rw [this]; exact hku
  have hne : (u' : G) ≠ 1 := by
    intro h
    apply hy1
    have : u' = 1 := Subtype.ext h
    rw [← hyθ, this, map_one]
  obtain ⟨_, ⟨_, ⟨a, ha, g, hg, rfl⟩, w, hw', rfl⟩, x, hx, hax⟩ := hK.opp _ hmem hne
  have hw'' : w = D.w₁ := hw'
  subst hw''
  have ha' : a ∈ D.K₁ := h3.X₁_le ha
  have hg' : g ∈ D.K₁ := H₁_le_K₁ D h1 hg
  have hx' : x ∈ D.K₁ := h3.X₁_le hx
  have e : u' = ⟨a, ha'⟩ * ⟨g, hg'⟩ * wk * ⟨x, hx'⟩ := Subtype.ext hax.symm
  rw [← hyθ, e, map_mul, map_mul, map_mul, hw]
  refine ⟨_, ⟨theta D hs α ⟨a, ha'⟩ * theta D hs α ⟨g, hg'⟩, ?_, D.z * D.w, rfl, rfl⟩,
    theta D hs α ⟨x, hx'⟩, ?_, rfl⟩
  · exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left ((mem_Y₁_iff D hs h3 hα _).mpr ⟨⟨a, ha'⟩, ha, rfl⟩))
      (Subgroup.mem_sup_right ((mem_H₀_iff D hs h1 hα _).mpr ⟨⟨g, hg'⟩, hg, rfl⟩))
  · exact Subgroup.mem_sup_left ((mem_Y₁_iff D hs h3 hα _).mpr ⟨⟨x, hx'⟩, hx, rfl⟩)

theorem theta_bruhat (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D)
    (hα : SPLAlpha D α) (hK : SPLK1Facts D) :
    ∀ x ∈ (theta D hs α).range, x ∈ ((D.Y₁ ⊔ D.H₀ : Subgroup G) : Set G) ∨
      x ∈ ((D.Y₁ ⊔ D.H₀ : Subgroup G) : Set G) * {D.z * D.w} *
        ((D.Y₁ ⊔ D.H₀ : Subgroup G) : Set G) := by
  rintro _ ⟨k, rfl⟩
  have hXH : D.X₁ ⊔ zpowers D.h₁ ≤ D.K₁ := sup_le h3.X₁_le (H₁_le_K₁ D h1)
  rcases hK.bruhat k k.2 with hk | hk
  · left
    exact theta_X₁_sup_mem D hs h1 h3 hα hk k.2
  · right
    obtain ⟨_, ⟨b, hb, w, hw', rfl⟩, x, hx, hbx⟩ := hk
    have hw'' : w = D.w₁ := hw'
    subst hw''
    have hb' : b ∈ D.K₁ := hXH hb
    have hx' : x ∈ D.K₁ := h3.X₁_le hx
    have e : k = ⟨b, hb'⟩ * ⟨D.w₁, h1.w₁_mem⟩ * ⟨x, hx'⟩ := Subtype.ext hbx.symm
    rw [e, map_mul, map_mul, theta_w₁ D hs h1 hα]
    exact ⟨_, ⟨theta D hs α ⟨b, hb'⟩, theta_X₁_sup_mem D hs h1 h3 hα hb hb', D.z * D.w, rfl, rfl⟩,
      theta D hs α ⟨x, hx'⟩, Subgroup.mem_sup_left ((mem_Y₁_iff D hs h3 hα _).mpr ⟨⟨x, hx'⟩, hx, rfl⟩),
      rfl⟩

end JFacts2

section JFacts3

variable [Finite G] (D : SPLNot3 G) {α : ↥D.K₁ ≃* ↥D.K₁}

theorem J_perf (hs : SPLSetup D.toSPLNot0) :
    ⁅(theta D hs α).range, (theta D hs α).range⁆ = (theta D hs α).range := by
  have : Group.IsPerfect ↥D.K₁ := hs.comps.quasi₁.1
  have : Group.IsPerfect ↥(theta D hs α).range := Group.IsPerfect.range _
  exact Subgroup.commutator_eq_self

theorem Y₁_le_J (hs : SPLSetup D.toSPLNot0) (h3 : SPL3M2 D) (hα : SPLAlpha D α) :
    D.Y₁ ≤ (theta D hs α).range := fun y hy => by
  obtain ⟨k, -, rfl⟩ := (mem_Y₁_iff D hs h3 hα y).mp hy
  exact ⟨k, rfl⟩

theorem H₀_le_J (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (hα : SPLAlpha D α) :
    D.H₀ ≤ (theta D hs α).range := fun y hy => by
  obtain ⟨k, -, rfl⟩ := (mem_H₀_iff D hs h1 hα y).mp hy
  exact ⟨k, rfl⟩

theorem relIndex_Y₁_J (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D)
    (hα : SPLAlpha D α) : 2 * D.Y₁.relIndex (theta D hs α).range = D.q ^ 2 - 1 := by
  have h := card_mul_relIndex' (Y₁_le_J D hs h3 hα)
  rw [h3.Y₁_card] at h
  have hJ := card_J D hs h1 hα
  have hq : 0 < D.q := by have := hs.q_ge; omega
  have : D.q * (2 * D.Y₁.relIndex (theta D hs α).range) = D.q * (D.q ^ 2 - 1) := by
    rw [← hJ, ← h]; ring
  exact Nat.eq_of_mul_eq_mul_left hq this

theorem Y₁_sylow (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D)
    (hα : SPLAlpha D α) : ¬ D.p ∣ D.Y₁.relIndex (theta D hs α).range := by
  intro hp
  have h2 := relIndex_Y₁_J D hs h1 h3 hα
  have hpq : D.p ∣ D.q := by
    obtain ⟨k, hk, hkq⟩ := hs.q_pow
    rw [hkq]; exact dvd_pow_self _ (by omega)
  have h3' : D.p ∣ D.q ^ 2 - 1 := by rw [← h2]; exact Dvd.dvd.mul_left hp 2
  have h4 : D.p ∣ D.q ^ 2 := dvd_pow hpq (by norm_num)
  have hge : 1 ≤ D.q ^ 2 := Nat.one_le_pow _ _ (by have := hs.q_ge; omega)
  have h5 : D.p ∣ D.q ^ 2 - (D.q ^ 2 - 1) := Nat.dvd_sub h4 h3'
  have : D.q ^ 2 - (D.q ^ 2 - 1) = 1 := by omega
  rw [this] at h5
  exact hs.prime.one_lt.ne' (Nat.dvd_one.mp h5)

theorem J_notP (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D)
    (hα : SPLAlpha D α) : ¬ IsPGroup D.p ↥(theta D hs α).range := by
  intro hP
  have : Fact D.p.Prime := ⟨hs.prime⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  have hdvd : D.Y₁.relIndex (theta D hs α).range ∣ D.p ^ n := by
    rw [← hn, ← card_mul_relIndex' (Y₁_le_J D hs h3 hα)]
    exact Dvd.intro_left _ rfl
  obtain ⟨m, hm, hr⟩ := (Nat.dvd_prime_pow hs.prime).mp hdvd
  have hm0 : m = 0 := by
    by_contra hne
    apply Y₁_sylow D hs h1 h3 hα
    rw [hr]; exact dvd_pow_self _ hne
  rw [hm0, pow_zero] at hr
  have h2 := relIndex_Y₁_J D hs h1 h3 hα
  rw [hr] at h2
  have h5 := hs.q_ge
  have h25 : 25 ≤ D.q ^ 2 := by nlinarith
  omega

end JFacts3

section JFacts4

variable [Finite G] (D : SPLNot3 G) {α : ↥D.K₁ ≃* ↥D.K₁}

omit [Finite G] in
theorem mem_center_K₁_iff (hs : SPLSetup D.toSPLNot0) (k : ↥D.K₁) :
    k ∈ center ↥D.K₁ ↔ (k : G) ∈ zpowers D.z := by
  rw [← hs.comps.cen₁]
  constructor
  · intro hk; exact ⟨k, hk, rfl⟩
  · rintro ⟨c, hc, hck⟩
    have : c = k := Subtype.ext hck
    rwa [this] at hc

theorem mem_center_equiv_iff {A B : Type} [Group A] [Group B] (e : A ≃* B) (x : A) :
    e x ∈ center B ↔ x ∈ center A := by
  simp only [← SetLike.mem_coe, Subgroup.coe_center]
  exact MulEquivClass.apply_mem_center_iff e

theorem J_isL2 (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (hα : SPLAlpha D α) :
    IVK.IsL2 ↥(theta D hs α).range (fun r => r = D.q) := by
  obtain ⟨F, hF, hfin, hq, ⟨e⟩⟩ := hs.comps.sl₁
  refine ⟨F, hF, hfin, hq, ⟨?_⟩⟩
  let μ : ↥D.K₁ →* IVK.L2 F := (IVK.L2.mk F).comp e.toMonoidHom
  have hμ : Function.Surjective μ := (QuotientGroup.mk'_surjective _).comp e.surjective
  have hcenter : center (StatedSL 2 F) = (StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F) := by
    rw [← map_center_eq_statedScalars 2 F]
    exact (Subgroup.map_center_eq (specialLinearGroupEquivStatedSL 2 F)).symm
  have hker : (theta D hs α).ker = μ.ker := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, theta_eq_one_iff D hs h1 hα,
      ← mem_center_K₁_iff D hs, ← mem_center_equiv_iff e, hcenter]
    exact (QuotientGroup.eq_one_iff (e k)).symm
  exact (QuotientGroup.quotientKerEquivRange (theta D hs α)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivOfSurjective μ hμ))


omit [Finite G] in
theorem z_pow_p (hs : SPLSetup D.toSPLNot0) : D.z ^ D.p = D.z := by
  obtain ⟨m, hm⟩ := hs.prime.odd_of_ne_two hs.p_ne_two
  have hz2 : D.z ^ 2 = 1 := by rw [pow_two]; exact z_mul_z D hs
  rw [hm, pow_succ, pow_mul, hz2, one_pow, one_mul]

theorem NJ_Y₁_eq (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D)
    (hα : SPLAlpha D α) (hK : SPLK1Facts D) :
    normalizer (D.Y₁ : Set G) ⊓ (theta D hs α).range = D.Y₁ ⊔ D.H₀ := by
  apply le_antisymm
  · rintro x ⟨hxN, k, rfl⟩
    have hk : ∀ u ∈ D.X₁, (k : G) * u * (k : G)⁻¹ ∈ D.X₁ := by
      intro u hu
      have hu' : u ∈ D.K₁ := h3.X₁_le hu
      have hyu : theta D hs α ⟨u, hu'⟩ ∈ D.Y₁ :=
        (mem_Y₁_iff D hs h3 hα _).mpr ⟨⟨u, hu'⟩, hu, rfl⟩
      have h1' : theta D hs α (k * ⟨u, hu'⟩ * k⁻¹) ∈ D.Y₁ := by
        rw [map_mul, map_mul, map_inv]
        exact (mem_normalizer_iff.mp hxN _).mp hyu
      obtain ⟨v, hv, hvθ⟩ := (mem_Y₁_iff D hs h3 hα _).mp h1'
      have hker : theta D hs α (v⁻¹ * (k * ⟨u, hu'⟩ * k⁻¹)) = 1 := by
        rw [map_mul, map_inv, hvθ, inv_mul_cancel]
      have hz := (theta_eq_one_iff D hs h1 hα _).mp hker
      have hz' : (v : G)⁻¹ * ((k : G) * u * (k : G)⁻¹) ∈ zpowers D.z := hz
      rcases eq_one_or_z hs hz' with h | h
      · have hc : (k : G) * u * (k : G)⁻¹ = (v : G) := by
          have h' : (v : G)⁻¹ * ((k : G) * u * (k : G)⁻¹) = 1 := h
          calc (k : G) * u * (k : G)⁻¹ = (v : G) * ((v : G)⁻¹ * ((k : G) * u * (k : G)⁻¹)) := by
                group
            _ = (v : G) := by rw [h', mul_one]
        rw [hc]; exact hv
      · exfalso
        have h' : (v : G)⁻¹ * ((k : G) * u * (k : G)⁻¹) = D.z := h
        have hc : (k : G) * u * (k : G)⁻¹ = (v : G) * D.z := by
          calc (k : G) * u * (k : G)⁻¹ = (v : G) * ((v : G)⁻¹ * ((k : G) * u * (k : G)⁻¹)) := by
                group
            _ = (v : G) * D.z := by rw [h']
        have hcp : ((k : G) * u * (k : G)⁻¹) ^ D.p = 1 := by
          rw [conj_pow, h3.X₁_eab.2 u hu]; group
        rw [hc] at hcp
        have hvz : Commute (v : G) D.z := hs.comps.cz₁ v.2
        rw [hvz.mul_pow, h3.X₁_eab.2 v hv, z_pow_p D hs, one_mul] at hcp
        have := hs.syl.z_inv
        rw [hcp, orderOf_one] at this
        omega
    have hkn : (k : G) ∈ normalizer (D.X₁ : Set G) := mem_normalizer_of_conj_le hk
    have hk2 : (k : G) ∈ D.X₁ ⊔ zpowers D.h₁ := by
      rw [← hK.norm_X₁]; exact ⟨hkn, k.2⟩
    exact theta_X₁_sup_mem D hs h1 h3 hα (b := (k : G)) hk2 k.2
  · apply sup_le
    · exact le_inf Subgroup.le_normalizer (Y₁_le_J D hs h3 hα)
    · exact le_inf (le_normalizer_of_normalizes (H₀_normalizes_Y₁ D hs h1 h3 hα))
        (H₀_le_J D hs h1 hα)

theorem NJ_H₀_eq (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (hα : SPLAlpha D α) :
    normalizer (D.H₀ : Set G) ⊓ (theta D hs α).range = D.H₀ ⊔ zpowers (D.z * D.w) := by
  have hw : theta D hs α ⟨D.w₁, h1.w₁_mem⟩ = D.z * D.w := theta_w₁ D hs h1 hα
  apply le_antisymm
  · rintro x ⟨hxN, k, rfl⟩
    have hk : ∀ u ∈ zpowers D.h₁, (k : G) * u * (k : G)⁻¹ ∈ zpowers D.h₁ := by
      intro u hu
      have hu' : u ∈ D.K₁ := H₁_le_K₁ D h1 hu
      have hyu : theta D hs α ⟨u, hu'⟩ ∈ D.H₀ :=
        (mem_H₀_iff D hs h1 hα _).mpr ⟨⟨u, hu'⟩, hu, rfl⟩
      have h1' : theta D hs α (k * ⟨u, hu'⟩ * k⁻¹) ∈ D.H₀ := by
        rw [map_mul, map_mul, map_inv]
        exact (mem_normalizer_iff.mp hxN _).mp hyu
      obtain ⟨v, hv, hvθ⟩ := (mem_H₀_iff D hs h1 hα _).mp h1'
      have hker : theta D hs α (v⁻¹ * (k * ⟨u, hu'⟩ * k⁻¹)) = 1 := by
        rw [map_mul, map_inv, hvθ, inv_mul_cancel]
      have hz := (theta_eq_one_iff D hs h1 hα _).mp hker
      have hz2 : (v : G)⁻¹ * ((k : G) * u * (k : G)⁻¹) ∈ zpowers D.h₁ :=
        (zpowers_le.mpr (z_mem_H₁ D h1)) hz
      have hc : (k : G) * u * (k : G)⁻¹ = (v : G) * ((v : G)⁻¹ * ((k : G) * u * (k : G)⁻¹)) := by
        group
      rw [hc]; exact Subgroup.mul_mem _ hv hz2
    have hkn : (k : G) ∈ normalizer (zpowers D.h₁ : Set G) := mem_normalizer_of_conj_le hk
    have hk2 : (k : G) ∈ D.H₁ ⊔ zpowers D.w₁ := by
      rw [← h1.nbhd]; exact ⟨hkn, k.2⟩
    have hw1norm : zpowers D.w₁ ≤ normalizer (D.H₁ : Set G) :=
      le_sup_right.trans (h1.nbhd ▸ inf_le_left)
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left D.H₁ (zpowers D.w₁)
      hw1norm] at hk2
    obtain ⟨a, ha, b, hb, hab⟩ := hk2
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hb
    have ha' : a ∈ D.K₁ := H₁_le_K₁ D h1 ha
    have e : k = ⟨a, ha'⟩ * (⟨D.w₁, h1.w₁_mem⟩ : ↥D.K₁) ^ i := by
      apply Subtype.ext
      simpa using hab.symm
    rw [e, map_mul, map_zpow, hw]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left ((mem_H₀_iff D hs h1 hα _).mpr ⟨⟨a, ha'⟩, ha, rfl⟩))
      (Subgroup.mem_sup_right (zpow_mem (mem_zpowers _) i))
  · apply sup_le
    · exact le_inf Subgroup.le_normalizer (H₀_le_J D hs h1 hα)
    · rw [zpowers_le]
      refine ⟨?_, ⟨⟨D.w₁, h1.w₁_mem⟩, hw⟩⟩
      apply mem_normalizer_of_conj_le
      intro x hx
      obtain ⟨kx, hkx, rfl⟩ := (mem_H₀_iff D hs h1 hα x).mp hx
      set wk : ↥D.K₁ := ⟨D.w₁, h1.w₁_mem⟩ with hwk
      have e : D.z * D.w * theta D hs α kx * (D.z * D.w)⁻¹ = theta D hs α (wk * kx * wk⁻¹) := by
        rw [map_mul, map_mul, map_inv]
        have hw' : theta D hs α wk = D.z * D.w := hw
        rw [hw']
      rw [e]
      refine (mem_H₀_iff D hs h1 hα _).mpr ⟨wk * kx * wk⁻¹, ?_, rfl⟩
      show D.w₁ * (kx : G) * D.w₁⁻¹ ∈ zpowers D.h₁
      rw [h1.w₁_inv _ hkx]
      exact Subgroup.inv_mem _ hkx


theorem theta_range_eq (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D)
    (hα : SPLAlpha D α) :
    (theta D hs α).range = D.Y₁ ⊔ conjBy (D.z * D.w) D.Y₁ := by
  set wk : ↥D.K₁ := ⟨D.w₁, h1.w₁_mem⟩ with hwk
  have hw : theta D hs α wk = D.z * D.w := theta_w₁ D hs h1 hα
  apply le_antisymm
  · rintro _ ⟨k, rfl⟩
    let L : Subgroup ↥D.K₁ := (D.Y₁ ⊔ conjBy (D.z * D.w) D.Y₁).comap (theta D hs α)
    have hX₁ : D.X₁.subgroupOf D.K₁ ≤ L := by
      intro x hx
      exact Subgroup.mem_sup_left ((mem_Y₁_iff D hs h3 hα _).mpr ⟨x, hx, rfl⟩)
    have hX₁' : D.X₁'.subgroupOf D.K₁ ≤ L := by
      intro x hx
      have hx' : D.w₁ * (x : G) * D.w₁⁻¹ ∈ D.X₁ := by
        have : (x : G) ∈ D.X₁' := hx
        rw [h3.X₁'_eq, mem_conjBy_iff] at this
        exact this
      have hxK : D.w₁ * (x : G) * D.w₁⁻¹ ∈ D.K₁ := h3.X₁_le hx'
      have e : x = wk⁻¹ * ⟨D.w₁ * (x : G) * D.w₁⁻¹, hxK⟩ * wk := by
        apply Subtype.ext
        show (x : G) = D.w₁⁻¹ * (D.w₁ * (x : G) * D.w₁⁻¹) * D.w₁
        group
      show theta D hs α x ∈ D.Y₁ ⊔ conjBy (D.z * D.w) D.Y₁
      rw [e, map_mul, map_mul, map_inv, hw]
      refine Subgroup.mem_sup_right ?_
      rw [mem_conjBy_iff]
      have hy := (mem_Y₁_iff D hs h3 hα _).mpr ⟨⟨D.w₁ * (x : G) * D.w₁⁻¹, hxK⟩, hx', rfl⟩
      have e2 : (D.z * D.w) * ((D.z * D.w)⁻¹ * theta D hs α ⟨D.w₁ * (x : G) * D.w₁⁻¹, hxK⟩ *
          (D.z * D.w)) * (D.z * D.w)⁻¹ = theta D hs α ⟨D.w₁ * (x : G) * D.w₁⁻¹, hxK⟩ := by group
      rw [e2]; exact hy
    have hsup : D.X₁.subgroupOf D.K₁ ⊔ D.X₁'.subgroupOf D.K₁ = ⊤ := by
      rw [← Subgroup.subgroupOf_sup h3.X₁_le h3.X₁'_le, ← h3.K₁_eq]
      exact Subgroup.subgroupOf_self D.K₁
    have hk : k ∈ L := (hsup ▸ (Subgroup.mem_top k) : k ∈ D.X₁.subgroupOf D.K₁ ⊔ D.X₁'.subgroupOf D.K₁)
      |> sup_le hX₁ hX₁'
    exact hk
  · refine sup_le (Y₁_le_J D hs h3 hα) ?_
    intro y hy
    rw [mem_conjBy_iff] at hy
    obtain ⟨ku, hku, hθ⟩ := (mem_Y₁_iff D hs h3 hα _).mp hy
    refine ⟨wk⁻¹ * ku * wk, ?_⟩
    rw [map_mul, map_mul, map_inv, hw, hθ]
    group

theorem exists_J (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    ∃ J : Subgroup G, J ≤ D.K ∧ IVK.IsL2 ↥J (fun r => r = D.q) ∧ D.Y₁ ≤ J ∧
      ¬ D.p ∣ D.Y₁.relIndex J ∧
      normalizer (D.Y₁ : Set G) ⊓ J = D.Y₁ ⊔ D.H₀ ∧
      normalizer (D.H₀ : Set G) ⊓ J = D.H₀ ⊔ zpowers (D.z * D.w) ∧
      SPLJBruhat (⟨D, J⟩ : SPLNot4 G) ∧ J = D.Y₁ ⊔ conjBy (D.z * D.w) D.Y₁ := by
  obtain ⟨α, hα, hK⟩ := exists_alpha D hs h1 h3
  refine ⟨(theta D hs α).range, ?_, J_isL2 D hs h1 hα, Y₁_le_J D hs h3 hα,
    Y₁_sylow D hs h1 h3 hα, NJ_Y₁_eq D hs h1 h3 hα hK, NJ_H₀_eq D hs h1 hα,
    ⟨J_perf D hs, J_notP D hs h1 h3 hα, H₀_normalizes_Y₁ D hs h1 h3 hα,
      theta_bruhat D hs h1 h3 hα hK, theta_opp D hs h1 h3 hα hK⟩,
    theta_range_eq D hs h1 h3 hα⟩
  rintro _ ⟨k, rfl⟩
  exact theta_mem_K D hs α k

end JFacts4

end CFSG.GH74.GLS.SP.Local
