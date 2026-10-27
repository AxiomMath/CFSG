module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryClosureBasic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryNotSylowWeak

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.GH74.Uniqueness.Bender

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

section Certificates

theorem exists_centralizer_bound_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {v : G} (hvT : v ∈ T) (hv2 : v ^ 2 = 1)
    (hvS : v ∉ szT₁ L T ⊔ zpowers t) :
    ∃ C : Subgroup G, szA₁ (szT₁ L T) ≤ C ∧ C ≤ szR (szT₁ L T) R₂ t ∧
      Nat.card C ≤ 2 * (2 ^ f) ^ 3 ∧
      ∀ e ∈ szR (szT₁ L T) R₂ t, e * v * e⁻¹ * v⁻¹ ∈ szA₁ (szT₁ L T) → e ∈ C := by
  obtain ⟨-, hA₁card, -⟩ := h.facts_of_card_sylow hS2
  have hvt : v * t = t * v := mem_centralizer_singleton_iff.mp (h.le hvT)
  obtain ⟨W, hWT₁, hAW, hWcard, hWmem⟩ := h.exists_commutatorAut_of_card_sylow hS2 hvT hv2 hvS
  refine ⟨(W ⊔ R₂) ⊔ zpowers t, ?_, ?_, ?_, ?_⟩
  · exact hAW.trans (le_sup_left.trans le_sup_left)
  · exact sup_le (sup_le (hWT₁.trans (le_szR_left _ _ _)) (le_szR_mid _ _ _))
      (zpowers_le.mpr (mem_szR_right _ _ _))
  · have htW : t ∈ normalizer (W : Set G) :=
      centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun w hw => hR.t_comm w (hWT₁ hw))
    have htN : zpowers t ≤ normalizer ((W ⊔ R₂ : Subgroup G) : Set G) :=
      zpowers_le.mpr (mem_normalizer_sup_of_mem_inf htW hR.t_mem_normalizer)
    have hprod := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer htN
    rw [sup_comm] at hprod
    have hzt : Nat.card (zpowers t) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one (by norm_num) hR.t_sq
    have h2 : Nat.card ((W ⊔ R₂) ⊔ zpowers t : Subgroup G) ≤
        2 * Nat.card (W ⊔ R₂ : Subgroup G) := by
      have hpos : 0 < Nat.card (zpowers t ⊓ (W ⊔ R₂) : Subgroup G) := Nat.card_pos
      calc Nat.card ((W ⊔ R₂) ⊔ zpowers t : Subgroup G) ≤
          Nat.card ((W ⊔ R₂) ⊔ zpowers t : Subgroup G) *
            Nat.card (zpowers t ⊓ (W ⊔ R₂) : Subgroup G) := Nat.le_mul_of_pos_right _ hpos
        _ = Nat.card (zpowers t) * Nat.card (W ⊔ R₂ : Subgroup G) := hprod
        _ ≤ 2 * Nat.card (W ⊔ R₂ : Subgroup G) := Nat.mul_le_mul_right _ hzt
    have hprod2 := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer
      (hWT₁.trans hR.T₁_le_normalizer)
    rw [hWcard, hR.card] at hprod2
    have hWR : 2 ^ f ≤ Nat.card (W ⊓ R₂ : Subgroup G) :=
      hA₁card ▸ card_le_of_le (le_inf hAW hR.le)
    have hq : 0 < 2 ^ f := by positivity
    have h3 : Nat.card (W ⊔ R₂ : Subgroup G) ≤ (2 ^ f) ^ 3 := by
      have h4 : Nat.card (W ⊔ R₂ : Subgroup G) * 2 ^ f ≤ (2 ^ f) ^ 3 * 2 ^ f := by
        calc Nat.card (W ⊔ R₂ : Subgroup G) * 2 ^ f ≤
            Nat.card (W ⊔ R₂ : Subgroup G) * Nat.card (W ⊓ R₂ : Subgroup G) :=
              Nat.mul_le_mul_left _ hWR
          _ = (2 ^ f) ^ 2 * (2 ^ f) ^ 2 := hprod2
          _ = (2 ^ f) ^ 3 * 2 ^ f := by ring
      exact Nat.le_of_mul_le_mul_right h4 hq
    omega
  · intro e heR hev
    obtain ⟨w, hw, z, hz, hwz⟩ := exists_mul_of_mem_szR hR heR
    obtain ⟨y, hy, r, hr, hyr⟩ := hR.mem_sup_iff.mp hw
    have hzv : z * v = v * z := (commute_of_mem_zpowers hz hvt).symm
    have ha := h.mem_szA₁_of_conj_of_card_sylow hS2 hR hvT hv2 hvS (inv_mem hr)
    set a := v * r⁻¹ * v⁻¹ * r⁻¹⁻¹ with hadef
    have har : r * a = a * r := (hR.comm _ hr _ (hR.le ha))
    have hay : y * a = a * y := mem_centralizer_iff.mp (mem_szA₁.mp ha).2 y hy
    have hyv : y * v * y⁻¹ * v⁻¹ ∈ szA₁ (szT₁ L T) := by
      have e2 : e * v * e⁻¹ * v⁻¹ = a * (y * v * y⁻¹ * v⁻¹) := by
        rw [← hwz, ← hyr]
        calc y * r * z * v * (y * r * z)⁻¹ * v⁻¹ = y * r * (z * v) * z⁻¹ * r⁻¹ * y⁻¹ * v⁻¹ := by
              group
          _ = y * r * (v * z) * z⁻¹ * r⁻¹ * y⁻¹ * v⁻¹ := by rw [hzv]
          _ = y * (r * (v * r⁻¹ * v⁻¹ * r⁻¹⁻¹) * r⁻¹) * v * y⁻¹ * v⁻¹ := by group
          _ = y * (r * a * r⁻¹) * v * y⁻¹ * v⁻¹ := by rw [hadef]
          _ = y * (a * r * r⁻¹) * v * y⁻¹ * v⁻¹ := by rw [har]
          _ = (y * a) * v * y⁻¹ * v⁻¹ := by group
          _ = (a * y) * v * y⁻¹ * v⁻¹ := by rw [hay]
          _ = a * (y * v * y⁻¹ * v⁻¹) := by group
      rw [e2] at hev
      have := mul_mem (inv_mem ha) hev
      rwa [inv_mul_cancel_left] at this
    have hyW : y ∈ W := by
      refine hWmem y hy ?_
      set b := y * v * y⁻¹ * v⁻¹ with hbdef
      have hby : y * b = b * y := mem_centralizer_iff.mp (mem_szA₁.mp hyv).2 y hy
      have hb'y : b⁻¹ * y = y * b⁻¹ := by
        calc b⁻¹ * y = b⁻¹ * (y * b) * b⁻¹ := by group
          _ = b⁻¹ * (b * y) * b⁻¹ := by rw [hby]
          _ = y * b⁻¹ := by group
      have e3 : y⁻¹ * (v * y * v⁻¹) = y⁻¹ * b⁻¹ * y := by rw [hbdef]; group
      rw [e3, mul_assoc, hb'y, inv_mul_cancel_left]
      exact inv_mem hyv
    rw [← hwz, ← hyr]
    exact mul_mem (mem_sup_left (mul_mem (mem_sup_left hyW) (mem_sup_right hr))) (mem_sup_right hz)

theorem inv_mul_mem_of_sq_mem_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {v : G} (hvT : v ∈ T) (hv2 : v ^ 2 = 1)
    (hvS : v ∉ szT₁ L T ⊔ zpowers t) {x : G} (hx : x ∈ T ⊔ R₂)
    (hxR : x ∉ szR (szT₁ L T) R₂ t) (hx2 : x ^ 2 ∈ szR (szT₁ L T) R₂ t) :
    v⁻¹ * x ∈ szR (szT₁ L T) R₂ t := by
  obtain ⟨-, hS₁N, -, -, -, -⟩ := h.s₁_facts_of_card_sylow hS2 hR
  obtain ⟨s, hs, r, hr, rfl⟩ := h.exists_mul_of_mem_s₁_of_card_sylow hS2 hR hx
  have hT₁tR₁ : szT₁ L T ⊔ zpowers t ≤ szR (szT₁ L T) R₂ t :=
    sup_le (le_szR_left _ _ _) (zpowers_le.mpr (mem_szR_right _ _ _))
  have hsN : s ∈ normalizer (szR (szT₁ L T) R₂ t : Set G) := hS₁N (mem_sup_left hs)
  have hsS : s ∉ szT₁ L T ⊔ zpowers t := fun h1 => hxR (mul_mem (hT₁tR₁ h1) hr)
  have hs2 : s ^ 2 ∈ szT₁ L T ⊔ zpowers t := by
    refine h.inf_szR_le_of_card_sylow hS2 hR (mem_inf.mpr ⟨pow_mem hs 2, ?_⟩)
    have h1 : s⁻¹ * r * s ∈ szR (szT₁ L T) R₂ t := (mem_normalizer_iff''.mp hsN r).mp hr
    have e : s ^ 2 = (s * r) ^ 2 * ((s⁻¹ * r * s) * r)⁻¹ := by rw [sq, sq]; group
    rw [e]
    exact mul_mem hx2 (inv_mem (mul_mem h1 hr))
  have hsv := h.mul_inv_mem_of_sq_mem_of_card_sylow hS2 hs hvT hs2
    (by rw [hv2]; exact one_mem _) hsS hvS
  have hvN : v ∈ normalizer (szR (szT₁ L T) R₂ t : Set G) := hS₁N (mem_sup_left hvT)
  have h1 : v⁻¹ * (s * v⁻¹) * v ∈ szR (szT₁ L T) R₂ t :=
    (mem_normalizer_iff''.mp hvN _).mp (hT₁tR₁ hsv)
  rw [show v⁻¹ * (s * r) = v⁻¹ * (s * v⁻¹) * v * r by group]
  exact mul_mem h1 hr

theorem strongClosed_of_outer_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {v : G} (hvT : v ∈ T) (hv2 : v ^ 2 = 1)
    (hvS : v ∉ szT₁ L T ⊔ zpowers t)
    (hsyl : ∃ P : Sylow 2 (normalizer (szA₁ (szT₁ L T) : Set G)),
      (P : Subgroup (normalizer (szA₁ (szT₁ L T) : Set G))) =
        (T ⊔ R₂).subgroupOf (normalizer (szA₁ (szT₁ L T) : Set G))) :
    ∀ g ∈ normalizer (szA₁ (szT₁ L T) : Set G), ∀ r ∈ szR (szT₁ L T) R₂ t,
      g⁻¹ * r * g ∈ T ⊔ R₂ → g⁻¹ * r * g ∈ szR (szT₁ L T) R₂ t := by
  obtain ⟨hR₁, hS₁N, hS₁A, hR₁S₁, -, -⟩ := h.s₁_facts_of_card_sylow hS2 hR
  obtain ⟨-, hA₁card, -⟩ := h.facts_of_card_sylow hS2
  obtain ⟨C, hAC, hCR, hCcard, hCv⟩ := h.exists_centralizer_bound_of_card_sylow hS2 hR hvT hv2 hvS
  have hAR : szA₁ (szT₁ L T) ≤ szR (szT₁ L T) R₂ t := (szA₁_le _).trans (le_szR_left _ _ _)
  have hS : IsPGroup 2 ↥(T ⊔ R₂ : Subgroup G) := by
    obtain ⟨P, hP⟩ := hsyl
    have h1 := P.isPGroup'
    rw [hP] at h1
    exact h1.of_equiv (subgroupOfEquivOfLe hS₁A)
  have hf := h.two_le
  refine strongClosed_mod_of_rank (a := 3 * f + 1) (c := 2 * f + 1) hAR hR₁S₁ hS₁A hS₁N hS
    (fun r hr => h.sq_mem_szA₁_of_mem_u3R₁_of_card_sylow hS2 (hR₁ ▸ hr))
    (fun r hr r' hr' => h.comm_mem_szA₁_of_mem_u3R₁_of_card_sylow hS2 (hR₁ ▸ hr) (hR₁ ▸ hr'))
    ?_ (mem_sup_left hvT)
    (fun x hx hxR hx2 => h.inv_mul_mem_of_sq_mem_of_card_sylow hS2 hR hvT hv2 hvS hx hxR hx2)
    hAC hCR ?_ hCv (by omega) hsyl
  · rw [hR₁, h.card_u3R₁_of_card_sylow hS2, hA₁card]
    ring
  · rw [hA₁card]
    calc Nat.card C ≤ 2 * (2 ^ f) ^ 3 := hCcard
      _ = 2 ^ (2 * f + 1) * 2 ^ f := by ring

end Certificates

end U3Start

section Certificates

theorem u3StrongClosureNcycInput : U3StrongClosureNcycInput := by
  intro G _ _ L f t T R₂ h hS2 hR hS v hvT hv2 hvS g hg hx
  obtain ⟨S, hS⟩ := hS
  have hS₁A := (h.s₁_facts_of_card_sylow hS2 hR).2.2.1
  have hsyl : ∃ P : Sylow 2 (normalizer (szA₁ (szT₁ L T) : Set G)),
      (P : Subgroup (normalizer (szA₁ (szT₁ L T) : Set G))) =
        (T ⊔ R₂).subgroupOf (normalizer (szA₁ (szT₁ L T) : Set G)) :=
    ⟨S.subtype (hS.le.trans hS₁A), by rw [Sylow.coe_subtype, hS]⟩
  exact h.strongClosed_of_outer_of_card_sylow hS2 hR hvT hv2 hvS hsyl g hg t
    (mem_szR_right _ _ _) hx

theorem u3StrongClosureInput : U3StrongClosureInput :=
  u3StrongClosureInput_of_ncyc u3StrongClosureNcycInput

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem not_isSylow_S₁_of_starPrime_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hstar : StarPrimeStatement f) :
    ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ R₂ :=
  h.not_isSylow_S₁_of_strong_of_card_sylow hS2 hR hstar u3StrongClosureInput

end U3Start

end Certificates

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

section Certificates43

theorem not_isSylow_S₁_of_starPrime (h : U3Start G L f t T) (hstar : StarPrimeStatement f)
    {R₂ : Subgroup G} (hR : U3R2 G L (szT₁ L T) R₂ t f) :
    ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ R₂ :=
  h.not_isSylow_S₁_of_ncyc hstar hR u3StrongClosureNcycInput

end Certificates43

end U3Start

end CFSG.SeitzReduction.RankOne
