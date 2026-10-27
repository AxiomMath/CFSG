module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryOmegaRegular

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup
open scoped commutatorElement

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section General

variable {G : Type*} [Group G]

theorem commutatorElement_mul_mul_eq_of_commute {g₁ g₂ b₁ b₂ : G} (h12 : b₁ * g₂ = g₂ * b₁)
    (h21 : b₂ * g₁ = g₁ * b₂) (hb : b₁ * b₂ = b₂ * b₁) :
    ⁅g₁ * b₁, g₂ * b₂⁆ = ⁅g₁, g₂⁆ := by
  have c2 : b₂ * g₁⁻¹ = g₁⁻¹ * b₂ := by
    rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← h21, mul_inv_cancel_right]
  calc ⁅g₁ * b₁, g₂ * b₂⁆ = g₁ * (b₁ * g₂) * b₂ * b₁⁻¹ * g₁⁻¹ * b₂⁻¹ * g₂⁻¹ := by
        rw [commutatorElement_def]; group
    _ = g₁ * g₂ * (b₁ * b₂ * b₁⁻¹) * g₁⁻¹ * b₂⁻¹ * g₂⁻¹ := by rw [h12]; group
    _ = g₁ * g₂ * (b₂ * g₁⁻¹) * b₂⁻¹ * g₂⁻¹ := by rw [hb, mul_inv_cancel_right]; group
    _ = g₁ * g₂ * g₁⁻¹ * g₂⁻¹ := by rw [c2]; group
    _ = ⁅g₁, g₂⁆ := (commutatorElement_def _ _).symm

@[expose] noncomputable def u3U (L T R₂ : Subgroup G) (t : G)
    (E : Subgroup (Equiv.Perm (u3Omega L T R₂ t))) : Subgroup G :=
  (E.comap (u3OmegaAction L T R₂ t)).map
    (normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G)).subtype

theorem mem_u3U {L T R₂ : Subgroup G} {t : G} {E : Subgroup (Equiv.Perm (u3Omega L T R₂ t))}
    {x : G} : x ∈ u3U L T R₂ t E ↔
      ∃ hx : x ∈ normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G),
        u3OmegaAction L T R₂ t ⟨x, hx⟩ ∈ E := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hxE⟩
    exact ⟨⟨x, hx⟩, hxE, rfl⟩

theorem u3U_le_normalizer (L T R₂ : Subgroup G) (t : G)
    (E : Subgroup (Equiv.Perm (u3Omega L T R₂ t))) :
    u3U L T R₂ t E ≤ normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G) := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem le_normalizer_u3U {L T R₂ : Subgroup G} {t : G}
    {E : Subgroup (Equiv.Perm (u3Omega L T R₂ t))}
    (hEn : (E.subgroupOf (u3OmegaAction L T R₂ t).range).Normal) :
    normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer (u3U L T R₂ t E : Set G) := by
  set Y := normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G) with hY
  have key : ∀ y ∈ Y, ∀ x ∈ u3U L T R₂ t E, y * x * y⁻¹ ∈ u3U L T R₂ t E := by
    intro y hy x hx
    obtain ⟨hxY, hxE⟩ := mem_u3U.mp hx
    refine mem_u3U.mpr ⟨mul_mem (mul_mem hy hxY) (inv_mem hy), ?_⟩
    have e : (⟨y * x * y⁻¹, mul_mem (mul_mem hy hxY) (inv_mem hy)⟩ : Y) =
        ⟨y, hy⟩ * ⟨x, hxY⟩ * (⟨y, hy⟩ : Y)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    have hn := hEn.conj_mem ⟨u3OmegaAction L T R₂ t ⟨x, hxY⟩, MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩
      (mem_subgroupOf.mpr hxE) ⟨u3OmegaAction L T R₂ t ⟨y, hy⟩, MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩
    rw [mem_subgroupOf] at hn
    simpa using hn
  intro y hy
  refine mem_normalizer_iff.mpr fun x => ⟨key y hy x, fun hx => ?_⟩
  have := key y⁻¹ (inv_mem hy) _ hx
  rwa [show y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x by group] at this

end General

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem exists_conj_mul_t_eq_of_mem_szR (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {x w : G} (hx : x ∈ szR (szT₁ L T) R₂ t)
    (hw : w ∈ szT₁ L T) : ∃ a ∈ szA₁ (szT₁ L T), x * (w * t) * x⁻¹ = a * (w * t) := by
  obtain ⟨-, -, hA₁, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨v, hv, z, hz, rfl⟩ := exists_mul_of_mem_szR hR hx
  obtain ⟨y, hy, r, hr, rfl⟩ := hR.mem_sup_iff.mp hv
  have hz' : z * (w * t) * z⁻¹ = w * t := by
    rcases mem_zpowers_involution_eq_one_or_eq hR.t_sq hz with hz1 | hz1
    · rw [hz1]; group
    · rw [hz1]
      calc t * (w * t) * t⁻¹ = t * w := by group
        _ = w * t := (hR.t_comm w hw).symm
  set ρ := r * t * r⁻¹ * t with hρ
  have hρA : ρ ∈ szA₁ (szT₁ L T) := hR.rho_mem r hr
  have hρw : w * ρ = ρ * w := mem_centralizer_iff.mp (mem_szA₁.mp hρA).2 w hw
  have hr' : r * (w * t) * r⁻¹ = ρ * (w * t) := by
    have hwr : w * r = r * w := hR.commT₁ w hw r hr
    calc r * (w * t) * r⁻¹ = w * (r * t * r⁻¹) := by
          rw [← mul_assoc, ← hwr]; group
      _ = w * (ρ * t) := by rw [hR.conj_t_eq r]
      _ = ρ * (w * t) := by rw [← mul_assoc, hρw, mul_assoc]
  have hyt : y * t = t * y := hR.t_comm y hy
  have hty : t * y⁻¹ = y⁻¹ * t := by
    rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, hyt, mul_inv_cancel_right]
  have hyρ : y * ρ = ρ * y := mem_centralizer_iff.mp (mem_szA₁.mp hρA).2 y hy
  have hc : ⁅y, w⁆ ∈ szA₁ (szT₁ L T) := by
    rw [hA₁]
    exact commutator_mem_commutator hy hw
  refine ⟨ρ * ⁅y, w⁆, mul_mem hρA hc, ?_⟩
  calc y * r * z * (w * t) * (y * r * z)⁻¹ = y * (r * (z * (w * t) * z⁻¹) * r⁻¹) * y⁻¹ := by
        group
    _ = y * ρ * w * (t * y⁻¹) := by rw [hz', hr']; group
    _ = ρ * (y * w * y⁻¹) * t := by rw [hyρ, hty]; group
    _ = ρ * ⁅y, w⁆ * (w * t) := by rw [commutatorElement_def]; group

section Certificates

theorem map_conj_eq_of_mem_szR_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {x : G} (hx : x ∈ szR (szT₁ L T) R₂ t)
    {X : Subgroup G} (hX : X ∈ u3Omega L T R₂ t) : X.map (MulAut.conj x).toMonoidHom = X := by
  obtain ⟨q, rfl⟩ := h.u3Omega_subset_range_of_card_sylow hS2 hR hX
  induction q using QuotientGroup.induction_on with | H w => ?_
  have hxN : x ∈ normalizer (R₂ : Set G) :=
    (sup_le (sup_le hR.T₁_le_normalizer Subgroup.le_normalizer)
      (zpowers_le.mpr hR.t_mem_normalizer) : szR (szT₁ L T) R₂ t ≤ normalizer (R₂ : Set G)) hx
  rw [u3OmegaPoint_mk, map_conj_sup_zpowers hxN]
  obtain ⟨a, ha, hxa⟩ := h.exists_conj_mul_t_eq_of_mem_szR hS2 hR hx w.2
  rw [hxa]
  have haw : (w : G) * a = a * w := mem_centralizer_iff.mp (mem_szA₁.mp ha).2 w w.2
  have hcomm : a * ((w : G) * t) = (w : G) * t * a := by
    rw [← mul_assoc, ← haw, mul_assoc, hR.szA₁_comm_t ha, ← mul_assoc]
  rw [hcomm, sup_zpowers_mul_eq (hR.le ha)]

theorem u3Omega_eq_range_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hΩ : (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2) :
    u3Omega L T R₂ t = Set.range (u3OmegaPoint L T R₂ t hR.le h.mem_centralizer_szT₁) := by
  refine Set.eq_of_subset_of_ncard_le (h.u3Omega_subset_range_of_card_sylow hS2 hR) ?_
    (Set.finite_range _)
  rw [hΩ, Set.ncard_range_of_injective (h.u3OmegaPoint_injective_of_card_sylow hS2 hR),
    h.card_quotient_szA₁_of_card_sylow hS2]

theorem mem_szR_of_forall_map_conj_eq_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hΩ : (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2) {y : G}
    (hy : y ∈ normalizer (szR (szT₁ L T) R₂ t : Set G))
    (hfix : ∀ X ∈ u3Omega L T R₂ t, X.map (MulAut.conj y).toMonoidHom = X) :
    y ∈ szR (szT₁ L T) R₂ t := by
  obtain ⟨-, -, -, hNR₁⟩ := h.char_of_card_sylow hS2 hR
  obtain ⟨-, -, -, -, -, hTH⟩ := h.s₁_facts_of_card_sylow hS2 hR
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨-, -, hA₁, -⟩ := h.facts_of_card_sylow hS2
  have hyH : y ∈ normalizer ((szT₁ L T ⊔ R₂ : Subgroup G) : Set G) := (mem_inf.mp (hNR₁ hy)).1
  have hyR₂ : y ∈ normalizer (R₂ : Set G) := (mem_inf.mp (hNR₁ hy)).2
  have hyA₁ := h.normalizer_sup_le_normalizer_szA₁_of_card_sylow hS2 hR hyH
  have h0 := hfix _ (sup_zpowers_mem_u3Omega L T R₂ t)
  rw [map_conj_sup_zpowers hyR₂] at h0
  have hyt : y * t * y⁻¹ ∈ R₂ ⊔ zpowers t := by
    rw [← h0]
    exact mem_sup_right (mem_zpowers _)
  have hyA : y ∈ normalizer (szA L T t : Set G) :=
    h.mem_normalizer_szA_of_conj_mem_of_card_sylow hS2 hR hc hy hyA₁ hyt
  have hzN : zpowers t ≤ normalizer (R₂ : Set G) := zpowers_le.mpr hR.t_mem_normalizer
  have hyt' : y * t * y⁻¹ ∈ ((R₂ ⊔ zpowers t : Subgroup G) : Set G) := hyt
  rw [coe_mul_of_right_le_normalizer_left _ _ hzN] at hyt'
  obtain ⟨b, hb, z, hz, hbz⟩ := Set.mem_mul.mp hyt'
  have hbt : y * t * y⁻¹ = b * t := by
    rcases mem_zpowers_involution_eq_one_or_eq hR.t_sq hz with hz1 | hz1
    · exfalso
      rw [hz1, mul_one] at hbz
      have h1 : y⁻¹ * (y * t * y⁻¹) * y ∈ szT₁ L T ⊔ R₂ :=
        (mem_normalizer_iff''.mp hyH _).mp (hbz ▸ mem_sup_right hb)
      rw [show y⁻¹ * (y * t * y⁻¹) * y = t by group] at h1
      exact h.not_mem_szT₁_of_card_sylow hS2 (hTH ⟨htT, h1⟩)
    · rw [← hbz, hz1]
  have hbA : b ∈ szA₁ (szT₁ L T) := by
    refine hR.mem_szA_of_sq_eq_one hc hb ?_
    rw [← hbt, show (y * t * y⁻¹) ^ 2 = y * t ^ 2 * y⁻¹ by rw [sq, sq]; group, hR.t_sq,
      mul_one, mul_inv_cancel]
  obtain ⟨r, hr, hrb⟩ := hR.rho_onto b hbA
  have hrt : r * t * r⁻¹ = y * t * y⁻¹ := by
    rw [hbt, ← hrb]
    exact hR.conj_t_eq r
  set m := r⁻¹ * y with hm
  have hmt : m * t = t * m := by
    have h1 : m * t * m⁻¹ = t := by
      calc m * t * m⁻¹ = r⁻¹ * (y * t * y⁻¹) * r := by rw [hm]; group
        _ = r⁻¹ * (r * t * r⁻¹) * r := by rw [hrt]
        _ = t := by group
    calc m * t = m * t * m⁻¹ * m := by group
      _ = t * m := by rw [h1]
  have hrR₁ := le_u3R₁_of_u3R2 hR hr
  have hmA : m ∈ normalizer (szA L T t : Set G) :=
    mul_mem (inv_mem (u3R₁_le_normalizer L T t (mem_inf.mp hrR₁).1)) hyA
  have hmT : m ∈ normalizer (szT₁ L T : Set G) := h.normalizer_szA_le_of_card_sylow hS2 hmA
  have hmR₂ : m ∈ normalizer (R₂ : Set G) :=
    mul_mem (inv_mem (Subgroup.le_normalizer hr)) hyR₂
  have hΩeq := h.u3Omega_eq_range_of_card_sylow hS2 hR hΩ
  have hmw : ∀ w ∈ szT₁ L T, w⁻¹ * (m * w * m⁻¹) ∈ szA₁ (szT₁ L T) := by
    intro w hw
    have hX : R₂ ⊔ zpowers (w * t) ∈ u3Omega L T R₂ t := by
      rw [hΩeq]
      exact ⟨QuotientGroup.mk ⟨w, hw⟩, rfl⟩
    have h2 := h.map_conj_eq_of_mem_szR_of_card_sylow hS2 hR (le_szR_mid _ _ _ (inv_mem hr)) hX
    have h3 : (R₂ ⊔ zpowers (w * t)).map (MulAut.conj m).toMonoidHom = R₂ ⊔ zpowers (w * t) := by
      have e : (MulAut.conj m).toMonoidHom =
          (MulAut.conj r⁻¹).toMonoidHom.comp (MulAut.conj y).toMonoidHom := by
        ext x
        simp [hm, MulAut.conj_apply, mul_assoc]
      rw [e, ← Subgroup.map_map, hfix _ hX, h2]
    rw [map_conj_sup_zpowers hmR₂] at h3
    have hmwT : m * w * m⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp hmT w).mp hw
    have h4 : u3OmegaPoint L T R₂ t hR.le h.mem_centralizer_szT₁
          (QuotientGroup.mk ⟨m * w * m⁻¹, hmwT⟩) =
        u3OmegaPoint L T R₂ t hR.le h.mem_centralizer_szT₁ (QuotientGroup.mk ⟨w, hw⟩) := by
      rw [u3OmegaPoint_mk, u3OmegaPoint_mk]
      change R₂ ⊔ zpowers (m * w * m⁻¹ * t) = R₂ ⊔ zpowers (w * t)
      rw [← h3, show m * w * m⁻¹ * t = m * (w * t) * m⁻¹ by
        calc m * w * m⁻¹ * t = m * w * m⁻¹ * (m * t * m⁻¹) := by rw [hmt, mul_inv_cancel_right]
          _ = m * (w * t) * m⁻¹ := by group]
    have h5 := h.u3OmegaPoint_injective_of_card_sylow hS2 hR h4
    rw [QuotientGroup.eq, mem_subgroupOf] at h5
    have h6 := inv_mem h5
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv] using h6
  have hmA₁ : szA₁ (szT₁ L T) ≤ centralizer ({m} : Set G) := by
    rw [hA₁, commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [mem_centralizer_singleton_iff]
    have hb₁ := hmw g₁ hg₁
    have hb₂ := hmw g₂ hg₂
    have hb₁c := (mem_szA₁.mp hb₁).2
    have hb₂c := (mem_szA₁.mp hb₂).2
    have key : m * ⁅g₁, g₂⁆ * m⁻¹ = ⁅g₁, g₂⁆ := by
      calc m * ⁅g₁, g₂⁆ * m⁻¹ = ⁅m * g₁ * m⁻¹, m * g₂ * m⁻¹⁆ := by
            simp only [commutatorElement_def]; group
        _ = ⁅g₁ * (g₁⁻¹ * (m * g₁ * m⁻¹)), g₂ * (g₂⁻¹ * (m * g₂ * m⁻¹))⁆ := by
            rw [mul_inv_cancel_left, mul_inv_cancel_left]
        _ = ⁅g₁, g₂⁆ := commutatorElement_mul_mul_eq_of_commute
            (mem_centralizer_iff.mp hb₁c g₂ hg₂).symm (mem_centralizer_iff.mp hb₂c g₁ hg₁).symm
            (mem_centralizer_iff.mp hb₁c _ (szA₁_le _ hb₂)).symm
    calc ⁅g₁, g₂⁆ * m = m * ⁅g₁, g₂⁆ * m⁻¹ * m := by rw [key]
      _ = m * ⁅g₁, g₂⁆ := by group
  have hmC : m ∈ centralizer (szA L T t : Set G) := by
    have hle : szA L T t ≤ centralizer ({m} : Set G) :=
      sup_le hmA₁ (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hmt.symm))
    exact mem_centralizer_iff.mpr fun x hx => mem_centralizer_singleton_iff.mp (hle hx)
  have hmS : m ∈ szT₁ L T ⊔ zpowers t := h.mem_sup_of_forall_mem_szA₁_of_card_sylow hS2 hmC hmw
  have hym : y = r * m := by rw [hm]; group
  rw [hym]
  exact mul_mem (le_szR_mid _ _ _ hr) ((sup_le (le_szR_left _ _ _)
    (zpowers_le.mpr (mem_szR_right _ _ _)) : szT₁ L T ⊔ zpowers t ≤ szR (szT₁ L T) R₂ t) hmS)

theorem szR_le_u3U_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (E : Subgroup (Equiv.Perm (u3Omega L T R₂ t))) :
    szR (szT₁ L T) R₂ t ≤ u3U L T R₂ t E := by
  intro x hx
  refine mem_u3U.mpr ⟨Subgroup.le_normalizer hx, ?_⟩
  have h1 : u3OmegaAction L T R₂ t ⟨x, Subgroup.le_normalizer hx⟩ = 1 := by
    refine Equiv.ext fun X => Subtype.ext ?_
    rw [u3OmegaAction_apply, Equiv.Perm.one_apply]
    exact h.map_conj_eq_of_mem_szR_of_card_sylow hS2 hR hx X.2
  rw [h1]
  exact one_mem E

theorem mem_szR_of_mem_u3U_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hΩ : (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2) {E : Subgroup (Equiv.Perm (u3Omega L T R₂ t))}
    (hreg : ∀ a b : u3Omega L T R₂ t, ∃! x : E, (x : Equiv.Perm (u3Omega L T R₂ t)) a = b)
    {u : G} (hu : u ∈ u3U L T R₂ t E)
    (hut : (R₂ ⊔ zpowers t).map (MulAut.conj u).toMonoidHom = R₂ ⊔ zpowers t) :
    u ∈ szR (szT₁ L T) R₂ t := by
  obtain ⟨huY, huE⟩ := mem_u3U.mp hu
  obtain ⟨x, -, hxu⟩ := hreg ⟨R₂ ⊔ zpowers t, sup_zpowers_mem_u3Omega L T R₂ t⟩
    ⟨R₂ ⊔ zpowers t, sup_zpowers_mem_u3Omega L T R₂ t⟩
  have h1 : (⟨u3OmegaAction L T R₂ t ⟨u, huY⟩, huE⟩ : E) = 1 := by
    rw [hxu ⟨_, huE⟩ (Subtype.ext (by rw [u3OmegaAction_apply]; exact hut)), hxu 1 rfl]
  have h2 : u3OmegaAction L T R₂ t ⟨u, huY⟩ = 1 := congrArg Subtype.val h1
  refine h.mem_szR_of_forall_map_conj_eq_of_card_sylow hS2 hR hc hΩ huY fun X hX => ?_
  have h3 := congrArg
    (fun σ : Equiv.Perm (u3Omega L T R₂ t) => ((σ ⟨X, hX⟩ : u3Omega L T R₂ t) : Subgroup G)) h2
  simpa [u3OmegaAction_apply] using h3

theorem exists_mem_u3U_conj_eq_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hΩ : (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2)
    {E : Subgroup (Equiv.Perm (u3Omega L T R₂ t))} (hE : E ≤ (u3OmegaAction L T R₂ t).range)
    (hreg : ∀ a b : u3Omega L T R₂ t, ∃! x : E, (x : Equiv.Perm (u3Omega L T R₂ t)) a = b)
    {w : G} (hw : w ∈ szT₁ L T) :
    ∃ u ∈ u3U L T R₂ t E, ∃ r ∈ R₂, u * t * u⁻¹ = r * w * t := by
  obtain ⟨-, -, -, hNR₁⟩ := h.char_of_card_sylow hS2 hR
  have hΩeq := h.u3Omega_eq_range_of_card_sylow hS2 hR hΩ
  have hX : R₂ ⊔ zpowers (w * t) ∈ u3Omega L T R₂ t := by
    rw [hΩeq]
    exact ⟨QuotientGroup.mk ⟨w, hw⟩, rfl⟩
  obtain ⟨⟨e, heE⟩, he, -⟩ := hreg ⟨R₂ ⊔ zpowers t, sup_zpowers_mem_u3Omega L T R₂ t⟩ ⟨_, hX⟩
  obtain ⟨⟨u, huY⟩, rfl⟩ := hE heE
  refine ⟨u, mem_u3U.mpr ⟨huY, heE⟩, ?_⟩
  have h1 : (R₂ ⊔ zpowers t).map (MulAut.conj u).toMonoidHom = R₂ ⊔ zpowers (w * t) := by
    have := congrArg Subtype.val he
    simpa [u3OmegaAction_apply] using this
  rw [map_conj_sup_zpowers (mem_inf.mp (hNR₁ huY)).2] at h1
  obtain ⟨w', hw', r', hr', hwr⟩ := h.exists_mul_of_mem_normalizer_szR_of_card_sylow hS2 hR huY
  have htr : t⁻¹ * r' * t ∈ R₂ := by
    have := hR.tN r' hr'
    rw [hR.t_inv] at this ⊢
    exact this
  have h2 : u3OmegaPoint L T R₂ t hR.le h.mem_centralizer_szT₁ (QuotientGroup.mk ⟨w', hw'⟩) =
      u3OmegaPoint L T R₂ t hR.le h.mem_centralizer_szT₁ (QuotientGroup.mk ⟨w, hw⟩) := by
    rw [u3OmegaPoint_mk, u3OmegaPoint_mk]
    change R₂ ⊔ zpowers (w' * t) = R₂ ⊔ zpowers (w * t)
    rw [← h1, hwr, show w' * r' * t = w' * t * (t⁻¹ * r' * t) by group, sup_zpowers_mul_eq htr]
  have h3 := h.u3OmegaPoint_injective_of_card_sylow hS2 hR h2
  rw [QuotientGroup.eq, mem_subgroupOf] at h3
  have hb : w⁻¹ * w' ∈ szA₁ (szT₁ L T) := by
    have := inv_mem h3
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv] using this
  refine ⟨(w⁻¹ * w') * r', mul_mem (hR.le hb) hr', ?_⟩
  rw [hwr]
  have hc1 : w * (w⁻¹ * w') = (w⁻¹ * w') * w := mem_centralizer_iff.mp (mem_szA₁.mp hb).2 w hw
  have hc2 : w * r' = r' * w := hR.commT₁ w hw r' hr'
  calc w' * r' * t = w * (w⁻¹ * w') * r' * t := by group
    _ = (w⁻¹ * w') * (w * r') * t := by rw [hc1]; group
    _ = (w⁻¹ * w') * r' * w * t := by rw [hc2]; group

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
