module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryNotSylow

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

@[expose] def u3Omega {G : Type*} [Group G] (L T R₂ : Subgroup G) (t : G) : Set (Subgroup G) :=
  {X | ∃ y ∈ normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G),
    X = (R₂ ⊔ zpowers t).map (MulAut.conj y).toMonoidHom}

section General

variable {G : Type*} [Group G]

theorem sup_zpowers_mul_eq {R : Subgroup G} {a b : G} (hb : b ∈ R) :
    R ⊔ zpowers (a * b) = R ⊔ zpowers a := by
  apply le_antisymm
  · exact sup_le le_sup_left (zpowers_le.mpr (mul_mem (mem_sup_right (mem_zpowers a))
      (mem_sup_left hb)))
  · refine sup_le le_sup_left (zpowers_le.mpr ?_)
    have h1 : a * b * b⁻¹ ∈ R ⊔ zpowers (a * b) :=
      mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left (inv_mem hb))
    rwa [mul_inv_cancel_right] at h1

theorem map_conj_sup_zpowers {R : Subgroup G} {x y : G} (hy : y ∈ normalizer (R : Set G)) :
    (R ⊔ zpowers x).map (MulAut.conj y).toMonoidHom = R ⊔ zpowers (y * x * y⁻¹) := by
  rw [Subgroup.map_sup, SzPartition.map_conj_zpowers]
  congr 1
  exact mem_normalizer_iff_map_conj_eq.mp hy

end General

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

@[expose] noncomputable def u3OmegaPoint (L T R₂ : Subgroup G) (t : G)
    (hA : szA₁ (szT₁ L T) ≤ R₂) (ht : t ∈ centralizer (szT₁ L T : Set G)) :
    ↥(szT₁ L T) ⧸ (szA₁ (szT₁ L T)).subgroupOf (szT₁ L T) → Subgroup G :=
  Quotient.lift (fun w : szT₁ L T => R₂ ⊔ zpowers ((w : G) * t)) fun a b hab => by
    have h1 : a⁻¹ * b ∈ (szA₁ (szT₁ L T)).subgroupOf (szT₁ L T) :=
      QuotientGroup.leftRel_apply.mp hab
    rw [mem_subgroupOf] at h1
    have hc : ((a⁻¹ * b : szT₁ L T) : G) * t = t * ((a⁻¹ * b : szT₁ L T) : G) :=
      mem_centralizer_iff.mp ht _ (a⁻¹ * b).2
    have e : (b : G) * t = (a : G) * t * ((a⁻¹ * b : szT₁ L T) : G) := by
      rw [mul_assoc (a : G) t, ← hc]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    change R₂ ⊔ zpowers ((a : G) * t) = R₂ ⊔ zpowers ((b : G) * t)
    rw [e, sup_zpowers_mul_eq (hA h1)]

omit [Finite G] in
theorem u3OmegaPoint_mk (L T R₂ : Subgroup G) (t : G) (hA : szA₁ (szT₁ L T) ≤ R₂)
    (ht : t ∈ centralizer (szT₁ L T : Set G)) (w : szT₁ L T) :
    u3OmegaPoint L T R₂ t hA ht (QuotientGroup.mk w) = R₂ ⊔ zpowers ((w : G) * t) :=
  rfl

theorem card_quotient_szA₁_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    Nat.card (↥(szT₁ L T) ⧸ (szA₁ (szT₁ L T)).subgroupOf (szT₁ L T)) = (2 ^ f) ^ 2 := by
  obtain ⟨hT₁, hA₁, -⟩ := h.facts_of_card_sylow hS2
  have h1 := ((szA₁ (szT₁ L T)).subgroupOf (szT₁ L T)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (szA₁_le _)).toEquiv, hA₁, hT₁] at h1
  have h2 : 2 ^ f * ((szA₁ (szT₁ L T)).subgroupOf (szT₁ L T)).index = 2 ^ f * (2 ^ f) ^ 2 := by
    rw [h1]; ring
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h2

omit [Finite G] in
theorem sup_zpowers_mem_u3Omega (L T R₂ : Subgroup G) (t : G) :
    R₂ ⊔ zpowers t ∈ u3Omega L T R₂ t :=
  ⟨1, one_mem _, by rw [map_conj_sup_zpowers (one_mem _), one_mul, inv_one, mul_one]⟩

section Certificates


theorem exists_mul_of_mem_normalizer_szR_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) {y : G}
    (hy : y ∈ normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G)) :
    ∃ w ∈ szT₁ L T, ∃ r ∈ R₂, y * t * y⁻¹ = w * r * t := by
  obtain ⟨-, -, -, hNR₁⟩ := h.char_of_card_sylow hS2 hR
  obtain ⟨-, -, -, -, -, hTH⟩ := h.s₁_facts_of_card_sylow hS2 hR
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  have hyH : y ∈ normalizer ((szT₁ L T ⊔ R₂ : Subgroup G) : Set G) := (mem_inf.mp (hNR₁ hy)).1
  have hyt : y * t * y⁻¹ ∈ szR (szT₁ L T) R₂ t :=
    (mem_normalizer_iff.mp hy t).mp (mem_szR_right _ _ _)
  obtain ⟨w', hw', z, hz, hwz⟩ := exists_mul_of_mem_szR hR hyt
  rcases mem_zpowers_involution_eq_one_or_eq hR.t_sq hz with hz1 | hz1
  · exfalso
    rw [hz1, mul_one] at hwz
    have h1 : y⁻¹ * (y * t * y⁻¹) * y ∈ szT₁ L T ⊔ R₂ :=
      (mem_normalizer_iff''.mp hyH _).mp (hwz ▸ hw')
    rw [show y⁻¹ * (y * t * y⁻¹) * y = t by group] at h1
    exact h.not_mem_szT₁_of_card_sylow hS2 (hTH ⟨htT, h1⟩)
  · obtain ⟨w, hw, r, hr, rfl⟩ := hR.mem_sup_iff.mp hw'
    rw [hz1] at hwz
    exact ⟨w, hw, r, hr, hwz.symm⟩

theorem u3Omega_subset_range_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) :
    u3Omega L T R₂ t ⊆ Set.range (u3OmegaPoint L T R₂ t hR.le h.mem_centralizer_szT₁) := by
  obtain ⟨-, -, -, hNR₁⟩ := h.char_of_card_sylow hS2 hR
  rintro X ⟨y, hy, rfl⟩
  obtain ⟨w, hw, r, hr, hwr⟩ := h.exists_mul_of_mem_normalizer_szR_of_card_sylow hS2 hR hy
  refine ⟨QuotientGroup.mk ⟨w, hw⟩, ?_⟩
  rw [u3OmegaPoint_mk, map_conj_sup_zpowers (mem_inf.mp (hNR₁ hy)).2, hwr]
  have htr : t⁻¹ * r * t ∈ R₂ := by
    have := hR.tN r hr
    rw [hR.t_inv] at this ⊢
    exact this
  rw [show w * r * t = w * t * (t⁻¹ * r * t) by group, sup_zpowers_mul_eq htr]

theorem u3OmegaPoint_injective_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) :
    Function.Injective (u3OmegaPoint L T R₂ t hR.le h.mem_centralizer_szT₁) := by
  obtain ⟨-, -, -, -, -, hTH⟩ := h.s₁_facts_of_card_sylow hS2 hR
  obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
  obtain ⟨-, -, -, hsq, -⟩ := h.facts_of_card_sylow hS2
  have htH : t ∉ szT₁ L T ⊔ R₂ := fun h1 => h.not_mem_szT₁_of_card_sylow hS2 (hTH ⟨htT, h1⟩)
  intro a b hab
  induction a using QuotientGroup.induction_on with | H w => ?_
  induction b using QuotientGroup.induction_on with | H w' => ?_
  rw [u3OmegaPoint_mk, u3OmegaPoint_mk] at hab
  have hwt : (w : G) * t = t * w := (hR.t_comm _ w.2)
  have hwN : (w : G) * t ∈ normalizer (R₂ : Set G) :=
    mul_mem (hR.T₁_le_normalizer w.2) hR.t_mem_normalizer
  have hsq2 : ((w : G) * t) ^ 2 ∈ R₂ := by
    have e : ((w : G) * t) ^ 2 = (w : G) ^ 2 := by
      calc ((w : G) * t) ^ 2 = (w : G) * (t * w) * t := by rw [sq]; group
        _ = (w : G) * ((w : G) * t) * t := by rw [← hwt]
        _ = (w : G) ^ 2 * t ^ 2 := by rw [sq, sq]; group
        _ = (w : G) ^ 2 := by rw [hR.t_sq, mul_one]
    rw [e]
    exact hR.le (hsq _ w.2)
  have hmem : (w' : G) * t ∈ R₂ ⊔ zpowers ((w : G) * t) := by
    rw [hab]
    exact mem_sup_right (mem_zpowers _)
  have hmem' : (w' : G) * t ∈ ((R₂ ⊔ zpowers ((w : G) * t) : Subgroup G) : Set G) := hmem
  rw [coe_mul_of_right_le_normalizer_left _ _ (zpowers_le.mpr hwN)] at hmem'
  obtain ⟨r, hr, z, hz, hrz⟩ := Set.mem_mul.mp hmem'
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
  rw [QuotientGroup.eq, mem_subgroupOf]
  rcases Int.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exfalso
    have hz2 : ((w : G) * t) ^ (j + j) ∈ R₂ := by
      rw [← two_mul, zpow_mul]
      exact zpow_mem (by exact_mod_cast hsq2) j
    have h1 : t ∈ szT₁ L T ⊔ R₂ := by
      have h2 : t = (w' : G)⁻¹ * (r * ((w : G) * t) ^ (j + j)) := by rw [hrz]; group
      rw [h2]
      exact mul_mem (mem_sup_left (inv_mem w'.2)) (mem_sup_right (mul_mem hr hz2))
    exact htH h1
  · have hz2 : ((w : G) * t) ^ (2 * j) ∈ R₂ := by
      rw [zpow_mul]
      exact zpow_mem (by exact_mod_cast hsq2) j
    have e : ((w : G) * t) ^ (2 * j + 1) = ((w : G) * t) ^ (2 * j) * ((w : G) * t) := by
      rw [zpow_add_one]
    rw [e] at hrz
    set s := ((w : G) * t) ^ (2 * j) with hs
    have hw' : (w' : G) = r * s * w := by
      have := congrArg (· * t⁻¹) hrz
      simp only [mul_inv_cancel_right] at this
      rw [← this]
      group
    have hrsT : r * s ∈ szT₁ L T := by
      have : r * s = (w' : G) * (w : G)⁻¹ := by rw [hw']; group
      rw [this]
      exact mul_mem w'.2 (inv_mem w.2)
    have hrsA : r * s ∈ szA₁ (szT₁ L T) := by
      rw [← hR.inf]
      exact mem_inf.mpr ⟨hrsT, mul_mem hr hz2⟩
    have hcomm : (w : G)⁻¹ * (r * s) = (r * s) * (w : G)⁻¹ :=
      mem_centralizer_iff.mp (mem_szA₁.mp hrsA).2 _ (inv_mem w.2)
    have e2 : ((w⁻¹ * w' : szT₁ L T) : G) = r * s := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hw', ← mul_assoc, hcomm]
      group
    rw [e2]
    exact hrsA
theorem ncard_u3Omega_le_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) : (u3Omega L T R₂ t).ncard ≤ (2 ^ f) ^ 2 := by
  calc (u3Omega L T R₂ t).ncard ≤
      (Set.range (u3OmegaPoint L T R₂ t hR.le h.mem_centralizer_szT₁)).ncard :=
        Set.ncard_le_ncard (h.u3Omega_subset_range_of_card_sylow hS2 hR) (Set.finite_range _)
    _ = (2 ^ f) ^ 2 := by
      rw [Set.ncard_range_of_injective (h.u3OmegaPoint_injective_of_card_sylow hS2 hR),
        h.card_quotient_szA₁_of_card_sylow hS2]

theorem one_lt_ncard_u3Omega_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f)
    (hmove : ∃ y ∈ normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G),
      y * t * y⁻¹ ∉ R₂ ⊔ zpowers t) : 1 < (u3Omega L T R₂ t).ncard := by
  obtain ⟨-, -, -, hNR₁⟩ := h.char_of_card_sylow hS2 hR
  obtain ⟨y, hy, hyt⟩ := hmove
  have hmem : (R₂ ⊔ zpowers t).map (MulAut.conj y).toMonoidHom ∈ u3Omega L T R₂ t := ⟨y, hy, rfl⟩
  have hne : (R₂ ⊔ zpowers t).map (MulAut.conj y).toMonoidHom ≠ R₂ ⊔ zpowers t := by
    intro heq
    rw [map_conj_sup_zpowers (mem_inf.mp (hNR₁ hy)).2] at heq
    apply hyt
    rw [← heq]
    exact mem_sup_right (mem_zpowers _)
  have hfin : (u3Omega L T R₂ t).Finite :=
    (Set.finite_range (u3OmegaPoint L T R₂ t hR.le h.mem_centralizer_szT₁)).subset
      (h.u3Omega_subset_range_of_card_sylow hS2 hR)
  exact (Set.one_lt_ncard hfin).mpr ⟨_, sup_zpowers_mem_u3Omega L T R₂ t, _, hmem, hne.symm⟩

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
