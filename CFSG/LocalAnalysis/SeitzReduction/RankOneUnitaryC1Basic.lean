module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryOmega

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

@[expose] def U3C1Exclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ : Subgroup G),
    U3Start G L f t T → (∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) →
    U3R2 G L (szT₁ L T) R₂ t f → (∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) → (∃ r ∈ R₂, r ^ 2 ≠ 1) → False

namespace U3R2

variable {G : Type} [Group G] [Finite G] {L T₁ R₂ : Subgroup G} {t : G} {f : ℕ}
  (hR : U3R2 G L T₁ R₂ t f) (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
include hR hinv

theorem rho_eq_sq_of_inv {r : G} (hr : r ∈ R₂) : r * t * r⁻¹ * t = r ^ 2 := by
  have h1 : t * r⁻¹ * t⁻¹ = r := by
    rw [show t * r⁻¹ * t⁻¹ = (t * r * t⁻¹)⁻¹ by group, hinv r hr, inv_inv]
  calc r * t * r⁻¹ * t = r * (t * r⁻¹ * t⁻¹) := by rw [hR.t_inv]; group
    _ = r ^ 2 := by rw [h1, sq]

theorem mem_szA₁_of_sq_eq_one_of_inv {r : G} (hr : r ∈ R₂) (h2 : r ^ 2 = 1) : r ∈ szA₁ T₁ := by
  refine hR.rho_ker r hr ?_
  have h3 := hR.rho_eq_sq_of_inv hinv hr
  rw [h2] at h3
  calc r * t = (r * t * r⁻¹ * t) * t⁻¹ * r := by group
    _ = t * r := by rw [h3, one_mul, hR.t_inv]

theorem exists_sq_eq_of_inv {b : G} (hb : b ∈ szA₁ T₁) : ∃ r ∈ R₂, r ^ 2 = b := by
  obtain ⟨r, hr, hrb⟩ := hR.rho_onto b hb
  exact ⟨r, hr, by rw [← hR.rho_eq_sq_of_inv hinv hr, hrb]⟩

omit hinv in
theorem pow_four_eq_one_of_inv {r : G} (hr : r ∈ R₂) : r ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
  exact hR.sq_A₁ _ (hR.sq_mem r hr)

theorem conj_t_eq_sq_mul_of_inv {r : G} (hr : r ∈ R₂) : r * t * r⁻¹ = r ^ 2 * t := by
  rw [← hR.rho_eq_sq_of_inv hinv hr, mul_assoc (r * t * r⁻¹) t t, ← sq, hR.t_sq, mul_one]

theorem sq_mul_mul_t_of_inv {y r : G} (hy : y ∈ T₁) (hr : r ∈ R₂) :
    (y * r * t) ^ 2 = y ^ 2 := by
  have e1 : t * y = y * t := (hR.t_comm y hy).symm
  have e2 : t * r = r⁻¹ * t := by
    calc t * r = (t * r * t⁻¹) * t := by group
      _ = r⁻¹ * t := by rw [hinv r hr]
  have e3 : r * y = y * r := (hR.commT₁ y hy r hr).symm
  have htt : t * t = 1 := by rw [← sq]; exact hR.t_sq
  calc (y * r * t) ^ 2 = y * r * (t * y) * r * t := by rw [sq]; group
    _ = y * (r * y) * (t * r) * t := by rw [e1]; group
    _ = y * (y * r) * (r⁻¹ * t) * t := by rw [e3, e2]
    _ = y * y * (t * t) := by group
    _ = y ^ 2 := by rw [htt, mul_one, sq]

theorem mul_t_sq_eq_one_of_inv {r : G} (hr : r ∈ R₂) : (r * t) ^ 2 = 1 :=
  (sq_mul_eq_one_iff hR.t_sq).mpr (hinv r hr)

omit [Finite G] hR in
theorem exists_not_comm_t_of_inv (hne : ∃ r ∈ R₂, r ^ 2 ≠ 1) : ∃ r ∈ R₂, t * r ≠ r * t := by
  obtain ⟨r, hr, hr2⟩ := hne
  refine ⟨r, hr, fun hrt => hr2 ?_⟩
  have h1 : t * r * t⁻¹ = r := by rw [hrt, mul_inv_cancel_right]
  have h2 : r⁻¹ = r := by rw [← hinv r hr, h1]
  rw [sq]
  nth_rewrite 1 [← h2]
  exact inv_mul_cancel r

end U3R2

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem t_not_mem_sup_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) : t ∉ szT₁ L T ⊔ R₂ := by
  intro ht
  obtain ⟨y, hy, r, hr, hyr⟩ := hR.mem_sup_iff.mp ht
  have hr' : r = y⁻¹ * t := by rw [← hyr]; group
  have hyt : y * t = t * y := hR.t_comm y hy
  have htt : t * t = 1 := by rw [← sq]; exact hR.t_sq
  have hyt' : y⁻¹ * t = t * y⁻¹ := by
    calc y⁻¹ * t = y⁻¹ * (t * y) * y⁻¹ := by group
      _ = y⁻¹ * (y * t) * y⁻¹ := by rw [hyt]
      _ = t * y⁻¹ := by group
  have hrA : r ∈ szA₁ (szT₁ L T) := by
    refine hR.rho_ker r hr ?_
    calc r * t = y⁻¹ * (t * t) := by rw [hr']; group
      _ = (t * t) * y⁻¹ := by rw [htt, mul_one, one_mul]
      _ = t * (t * y⁻¹) := by group
      _ = t * (y⁻¹ * t) := by rw [hyt']
      _ = t * r := by rw [hr']
  apply h.not_mem_szT₁_of_card_sylow hS2
  rw [← hyr]
  exact mul_mem hy (szA₁_le _ hrA)

theorem exists_mul_t_of_sq_eq_one_of_inv (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) {x : G}
    (hx : x ∈ szR (szT₁ L T) R₂ t) (hxH : x ∉ szT₁ L T ⊔ R₂) (hx2 : x ^ 2 = 1) :
    ∃ r ∈ R₂, x = r * t := by
  obtain ⟨w, hw, z, hz, rfl⟩ := exists_mul_of_mem_szR hR hx
  rcases mem_zpowers_involution_eq_one_or_eq hR.t_sq hz with rfl | rfl
  · exact absurd (by rwa [mul_one]) hxH
  · obtain ⟨y, hy, r, hr, rfl⟩ := hR.mem_sup_iff.mp hw
    obtain ⟨-, -, -, -, hinvT, -⟩ := h.facts_of_card_sylow hS2
    have hy2 : y ^ 2 = 1 := by rw [← hR.sq_mul_mul_t_of_inv hinv hy hr]; exact hx2
    exact ⟨y * r, mul_mem (hR.le (hinvT y hy hy2)) hr, rfl⟩

theorem inf_centralizer_sup_zpowers_of_inv {R₂ : Subgroup G} (hR : U3R2 G L (szT₁ L T) R₂ t f)
    (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) (hne : ∃ r ∈ R₂, r ^ 2 ≠ 1) :
    szR (szT₁ L T) R₂ t ⊓ centralizer ((R₂ ⊔ zpowers t : Subgroup G) : Set G) = szT₁ L T := by
  apply le_antisymm
  · rintro x ⟨hx, hxC⟩
    have hxt : t * x = x * t := mem_centralizer_iff.mp hxC t (mem_sup_right (mem_zpowers t))
    obtain ⟨w, hw, z, hz, rfl⟩ := exists_mul_of_mem_szR hR hx
    obtain ⟨y, hy, r, hr, rfl⟩ := hR.mem_sup_iff.mp hw
    rcases mem_zpowers_involution_eq_one_or_eq hR.t_sq hz with hz1 | hz1
    · rw [hz1, mul_one] at hxt ⊢
      have hyt : y * t = t * y := hR.t_comm y hy
      have hrt : r * t = t * r := by
        calc r * t = y⁻¹ * (t * (y * r)) := by rw [hxt]; group
          _ = y⁻¹ * (t * y) * r := by group
          _ = y⁻¹ * (y * t) * r := by rw [hyt]
          _ = t * r := by group
      exact mul_mem hy (szA₁_le _ (hR.rho_ker r hr hrt))
    · exfalso
      obtain ⟨r', hr', hr't⟩ := U3R2.exists_not_comm_t_of_inv hinv hne
      apply hr't
      have h1 : r' * (y * r * z) = (y * r * z) * r' :=
        mem_centralizer_iff.mp hxC r' (mem_sup_left hr')
      rw [hz1] at h1
      have hyr' : r' * y = y * r' := (hR.commT₁ y hy r' hr').symm
      have hrr' : r' * r = r * r' := hR.comm r' hr' r hr
      have h2 : y * r * (r' * t) = y * r * (t * r') := by
        calc y * r * (r' * t) = r' * (y * r * t) := by
              rw [← mul_assoc, mul_assoc y r r', ← hrr', ← mul_assoc, ← hyr']; group
          _ = y * r * (t * r') := by rw [h1]; group
      exact (mul_left_cancel h2).symm
  · intro x hx
    have hle : R₂ ⊔ zpowers t ≤ centralizer ({x} : Set G) :=
      sup_le (fun r hr => mem_centralizer_singleton_iff.mpr (hR.commT₁ x hx r hr).symm)
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hR.t_comm x hx).symm))
    exact mem_inf.mpr ⟨le_szR_left _ _ _ hx, mem_centralizer_iff.mpr fun g hg =>
      mem_centralizer_singleton_iff.mp (hle hg)⟩

theorem exists_conj_t_eq_of_inv (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) {y : G}
    (hy : y ∈ normalizer (szR (szT₁ L T) R₂ t : Set G)) : ∃ r ∈ R₂, y * t * y⁻¹ = r * t := by
  obtain ⟨-, -, -, hNR₁⟩ := h.char_of_card_sylow hS2 hR
  have hyH : y ∈ normalizer ((szT₁ L T ⊔ R₂ : Subgroup G) : Set G) := (mem_inf.mp (hNR₁ hy)).1
  refine h.exists_mul_t_of_sq_eq_one_of_inv hS2 hR hinv
    ((mem_normalizer_iff.mp hy t).mp (mem_szR_right _ _ _)) (fun h1 => ?_) ?_
  · apply h.t_not_mem_sup_of_card_sylow hS2 hR
    have h2 := (mem_normalizer_iff''.mp hyH _).mp h1
    rwa [show y⁻¹ * (y * t * y⁻¹) * y = t by group] at h2
  · rw [show (y * t * y⁻¹) ^ 2 = y * t ^ 2 * y⁻¹ by rw [sq, sq]; group, hR.t_sq, mul_one,
      mul_inv_cancel]

theorem normalizer_szR_le_normalizer_sup_zpowers_of_inv
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    {R₂ : Subgroup G} (hR : U3R2 G L (szT₁ L T) R₂ t f) (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹) :
    normalizer (szR (szT₁ L T) R₂ t : Set G) ≤
      normalizer ((R₂ ⊔ zpowers t : Subgroup G) : Set G) := by
  obtain ⟨-, -, -, hNR₁⟩ := h.char_of_card_sylow hS2 hR
  have key : ∀ y ∈ normalizer (szR (szT₁ L T) R₂ t : Set G), ∀ x ∈ R₂ ⊔ zpowers t,
      y * x * y⁻¹ ∈ R₂ ⊔ zpowers t := by
    intro y hy x hx
    obtain ⟨r, hr, hyt⟩ := h.exists_conj_t_eq_of_inv hS2 hR hinv hy
    have hyR : y ∈ normalizer (R₂ : Set G) := (mem_inf.mp (hNR₁ hy)).2
    have hle : R₂ ⊔ zpowers t ≤ (R₂ ⊔ zpowers t).comap (MulAut.conj y).toMonoidHom := by
      refine sup_le (fun a ha => ?_) (zpowers_le.mpr ?_)
      · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact mem_sup_left ((mem_normalizer_iff.mp hyR a).mp ha)
      · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hyt]
        exact mul_mem (mem_sup_left hr) (mem_sup_right (mem_zpowers t))
    have := hle hx
    rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  intro y hy
  refine mem_normalizer_iff.mpr fun x => ⟨key y hy x, fun hx => ?_⟩
  have := key y⁻¹ (inv_mem hy) _ hx
  rwa [show y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x by group] at this

theorem normalizer_szR_le_normalizer_szT₁_of_inv
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    {R₂ : Subgroup G} (hR : U3R2 G L (szT₁ L T) R₂ t f) (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hne : ∃ r ∈ R₂, r ^ 2 ≠ 1) :
    normalizer (szR (szT₁ L T) R₂ t : Set G) ≤ normalizer (szT₁ L T : Set G) ∧
      normalizer (szR (szT₁ L T) R₂ t : Set G) ≤ normalizer (szA₁ (szT₁ L T) : Set G) := by
  have hW := h.normalizer_szR_le_normalizer_sup_zpowers_of_inv hS2 hR hinv
  have hC := inf_centralizer_sup_zpowers_of_inv hR hinv hne
  have key : ∀ y ∈ normalizer (szR (szT₁ L T) R₂ t : Set G), ∀ x ∈ szT₁ L T,
      y * x * y⁻¹ ∈ szT₁ L T := by
    intro y hy x hx
    rw [← hC] at hx ⊢
    obtain ⟨hxR, hxC⟩ := mem_inf.mp hx
    refine mem_inf.mpr ⟨(mem_normalizer_iff.mp hy x).mp hxR, mem_centralizer_iff.mpr fun w hw => ?_⟩
    have hw' : y⁻¹ * w * y ∈ R₂ ⊔ zpowers t := (mem_normalizer_iff''.mp (hW hy) w).mp hw
    have h1 := mem_centralizer_iff.mp hxC _ hw'
    calc w * (y * x * y⁻¹) = y * ((y⁻¹ * w * y) * x) * y⁻¹ := by group
      _ = y * (x * (y⁻¹ * w * y)) * y⁻¹ := by rw [h1]
      _ = y * x * y⁻¹ * w := by group
  have hT : normalizer (szR (szT₁ L T) R₂ t : Set G) ≤ normalizer (szT₁ L T : Set G) := by
    intro y hy
    refine mem_normalizer_iff.mpr fun x => ⟨key y hy x, fun hx => ?_⟩
    have := key y⁻¹ (inv_mem hy) _ hx
    rwa [show y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x by group] at this
  exact ⟨hT, hT.trans (normalizer_le_normalizer_inf_centralizer (szT₁ L T))⟩

omit [Finite G] in
theorem mem_normalizer_szA_of_conj_t_mem {y : G}
    (hyA : y ∈ normalizer (szA₁ (szT₁ L T) : Set G)) {b : G} (hb : b ∈ szA₁ (szT₁ L T))
    (hyt : y * t * y⁻¹ = b * t) : y ∈ normalizer (szA L T t : Set G) := by
  have key : ∀ y' ∈ normalizer (szA₁ (szT₁ L T) : Set G), y' * t * y'⁻¹ ∈ szA L T t →
      ∀ x ∈ szA L T t, y' * x * y'⁻¹ ∈ szA L T t := by
    intro y' hy' hy't x hx
    have hle : szA L T t ≤ (szA L T t).comap (MulAut.conj y').toMonoidHom := by
      refine sup_le (fun a ha => ?_) (zpowers_le.mpr ?_)
      · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact mem_sup_left ((mem_normalizer_iff.mp hy' a).mp ha)
      · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact hy't
    have := hle hx
    rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  have hytA : y * t * y⁻¹ ∈ szA L T t := by
    rw [hyt]
    exact mul_mem (mem_sup_left hb) (mem_sup_right (mem_zpowers t))
  have hy't : y⁻¹ * t * y⁻¹⁻¹ ∈ szA L T t := by
    have hb' : y⁻¹ * b * y ∈ szA₁ (szT₁ L T) := (mem_normalizer_iff''.mp hyA b).mp hb
    have e : y⁻¹ * t * y⁻¹⁻¹ = (y⁻¹ * b * y)⁻¹ * t := by
      rw [inv_inv]
      have h1 : t = y⁻¹ * (b * t) * y := by rw [← hyt]; group
      calc y⁻¹ * t * y = (y⁻¹ * b * y)⁻¹ * (y⁻¹ * (b * t) * y) := by group
        _ = (y⁻¹ * b * y)⁻¹ * t := by rw [← h1]
    rw [e]
    exact mul_mem (mem_sup_left (inv_mem hb')) (mem_sup_right (mem_zpowers t))
  refine mem_normalizer_iff.mpr fun x => ⟨key y hyA hytA x, fun hx => ?_⟩
  have := key y⁻¹ (inv_mem hyA) hy't _ hx
  rwa [show y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x by group] at this

section Certificates

theorem exists_normalizer_szR_not_mem_normalizer_szA_of_not_isSylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hnS : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ R₂)
    (hN : normalizer ((T ⊔ R₂ : Subgroup G) : Set G) ≤ normalizer (szA₁ (szT₁ L T) : Set G)) :
    ∃ y ∈ normalizer (szR (szT₁ L T) R₂ t : Set G), y ∈ normalizer (szA₁ (szT₁ L T) : Set G) ∧
      y ∉ normalizer (szA L T t : Set G) := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hS₁N, hS₁A, hR₁S₁, -, -⟩ := h.s₁_facts_of_card_sylow hS2 hR
  obtain ⟨-, -, -, -, -, hsyl⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  set X := normalizer (szA₁ (szT₁ L T) : Set G) with hX
  by_cases hsylA : ∃ P : Sylow 2 X, (P : Subgroup X) = (T ⊔ R₂).subgroupOf X
  · exfalso
    obtain ⟨x, hxN, hxS, P, hP, hSP, hxP⟩ := exists_normalizer_not_mem_of_not_isSylow
      hsyl.isPGroup hnS
    obtain ⟨Q, hQ⟩ := hsylA
    have hsylA' : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊔ R₂) X :=
      ⟨Q, by rw [hQ, subgroupOf_map_subtype, inf_eq_left.mpr hS₁A]⟩
    have heq := hsylA'.eq_of_le (le_sup_left : T ⊔ R₂ ≤ (T ⊔ R₂) ⊔ zpowers x)
      (sup_le hS₁A (zpowers_le.mpr (hN hxN))) (hP.to_le (sup_le hSP (zpowers_le.mpr hxP)))
    apply hxS
    rw [← heq]
    exact mem_sup_right (mem_zpowers x)
  · have hS' : IsPGroup 2 ((T ⊔ R₂).subgroupOf X) :=
      hsyl.isPGroup.of_equiv (subgroupOfEquivOfLe hS₁A).symm
    obtain ⟨z, hz, hzS, P, hP, hSP, hzP⟩ := exists_normalizer_not_mem_of_not_isSylow hS' hsylA
    have hxS : (z : G) ∉ T ⊔ R₂ := fun h1 => hzS (mem_subgroupOf.mpr h1)
    have hxN : (z : G) ∈ normalizer ((T ⊔ R₂ : Subgroup G) : Set G) := by
      refine mem_normalizer_of_forall_inv_mul_mul_mem fun w hw => ?_
      have h1 := (mem_normalizer_iff''.mp hz ⟨w, hS₁A hw⟩).mp (mem_subgroupOf.mpr hw)
      rw [mem_subgroupOf] at h1
      simpa using h1
    have hxR : (z : G) ∈ normalizer (szR (szT₁ L T) R₂ t : Set G) := by
      refine mem_normalizer_of_forall_inv_mul_mul_mem fun r hr => ?_
      refine h.weakClosed_of_card_sylow hS2 hR z z.2 (fun r' hr' => ?_) r hr
      exact (mem_normalizer_iff''.mp hxN _).mp (hR₁S₁ hr')
    refine ⟨z, hxR, z.2, fun hzA => hxS ?_⟩
    have hP' : IsPGroup 2 (P.map X.subtype) := hP.map X.subtype
    have hSP' : T ⊔ R₂ ≤ P.map X.subtype := fun w hw =>
      ⟨⟨w, hS₁A hw⟩, hSP (mem_subgroupOf.mpr hw), rfl⟩
    have hzP' : (z : G) ∈ P.map X.subtype := ⟨z, hzP, rfl⟩
    have heq := hsyl.eq_of_le (le_sup_left : T ⊔ R₂ ≤ (T ⊔ R₂) ⊔ zpowers (z : G))
      (sup_le hsyl.le (zpowers_le.mpr hzA)) (hP'.to_le (sup_le hSP' (zpowers_le.mpr hzP')))
    rw [← heq]
    exact mem_sup_right (mem_zpowers _)

theorem exists_move_of_inv_of_not_isSylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hnS : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T ⊔ R₂)
    (hN : normalizer ((T ⊔ R₂ : Subgroup G) : Set G) ≤ normalizer (szA₁ (szT₁ L T) : Set G)) :
    ∃ y ∈ normalizer (szR (szT₁ L T) R₂ t : Set G), ∃ r ∈ R₂, r ∉ szA₁ (szT₁ L T) ∧
      y * t * y⁻¹ = r * t := by
  obtain ⟨y, hyR, hyA, hyNA⟩ :=
    h.exists_normalizer_szR_not_mem_normalizer_szA_of_not_isSylow hS2 hR hnS hN
  obtain ⟨r, hr, hyt⟩ := h.exists_conj_t_eq_of_inv hS2 hR hinv hyR
  exact ⟨y, hyR, r, hr, fun hrA => hyNA (mem_normalizer_szA_of_conj_t_mem hyA hrA hyt), hyt⟩

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
