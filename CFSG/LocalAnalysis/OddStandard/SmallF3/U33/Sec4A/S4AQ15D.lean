module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AQ15C

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise commutatorElement

section Q15D0

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

private theorem q15_comm_tR_R (h : L41GPh10 t L S x₁ x₂ lam rho) {k r : G}
    (hk : k ∈ l41R t x₁ x₂ rho) (hr : r ∈ l41R t x₁ x₂ rho) :
    ⁅t * k, r⁆ ∈ l41Y t x₁ x₂ rho := by
  obtain ⟨f, hf, hconj⟩ := m13_conj_t_R h.toL41GPh8 hr
  have ht : t⁻¹ = t := m13_t_inv h.hyp
  have hkey : t * r * t = f * r := by simpa [ht] using hconj
  have hkr : k * r * k⁻¹ = r := by
    rw [m13_comm_R h hk hr]
    group
  have heq : ⁅t * k, r⁆ = f := by
    have e1 : (t * k) * r * (t * k)⁻¹ * r⁻¹ = t * (k * r * k⁻¹) * t * r⁻¹ := by
      rw [mul_inv_rev, ht]
      group
    rw [commutatorElement_def, e1, hkr, hkey]
    group
  rw [heq]
  exact m11_fourGrp_le_Y h hf

private theorem q15_comm_tR_tR (h : L41GPh10 t L S x₁ x₂ lam rho) {k₁ k₂ : G}
    (hk₁ : k₁ ∈ l41R t x₁ x₂ rho) (hk₂ : k₂ ∈ l41R t x₁ x₂ rho) :
    ⁅t * k₁, t * k₂⁆ ∈ l41Y t x₁ x₂ rho := by
  obtain ⟨f₁, hf₁, hconj₁⟩ := m13_conj_t_R h.toL41GPh8 hk₁
  obtain ⟨f₂, hf₂, hconj₂⟩ := m13_conj_t_R h.toL41GPh8 hk₂
  have ht : t⁻¹ = t := m13_t_inv h.hyp
  have hkey₁ : t * k₁ * t = f₁ * k₁ := by simpa [ht] using hconj₁
  have hkey₂ : t * k₂ * t = f₂ * k₂ := by simpa [ht] using hconj₂
  have huv : (t * k₁) * (t * k₂) = f₁ * k₁ * k₂ := by
    rw [show (t * k₁) * (t * k₂) = (t * k₁ * t) * k₂ by group, hkey₁]
  have hvu : (t * k₂) * (t * k₁) = f₂ * k₂ * k₁ := by
    rw [show (t * k₂) * (t * k₁) = (t * k₂ * t) * k₁ by group, hkey₂]
  have hcomm : (t * k₁) * (t * k₂) * ((t * k₂) * (t * k₁))⁻¹ = f₁ * f₂⁻¹ := by
    rw [huv, hvu]
    have h1 : k₁ * k₂ * k₁⁻¹ = k₂ := by
      rw [m13_comm_R h hk₁ hk₂]
      group
    have hinv : (f₂ * k₂ * k₁)⁻¹ = k₁⁻¹ * k₂⁻¹ * f₂⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev]
      group
    rw [hinv]
    calc (f₁ * k₁ * k₂) * (k₁⁻¹ * k₂⁻¹ * f₂⁻¹)
        = (f₁ * (k₁ * k₂ * k₁⁻¹)) * (k₂⁻¹ * f₂⁻¹) := by group
      _ = (f₁ * k₂) * (k₂⁻¹ * f₂⁻¹) := by rw [h1]
      _ = f₁ * f₂⁻¹ := by group
  have heq : ⁅t * k₁, t * k₂⁆ = f₁ * f₂⁻¹ := by
    have e1 : (t * k₁) * (t * k₂) * (t * k₁)⁻¹ * (t * k₂)⁻¹
        = (t * k₁) * (t * k₂) * ((t * k₂) * (t * k₁))⁻¹ := by group
    rw [commutatorElement_def, e1, hcomm]
  rw [heq]
  exact m11_fourGrp_le_Y h (Subgroup.mul_mem _ hf₁ (Subgroup.inv_mem _ hf₂))

theorem q15_comm_F_Y (h : L41GPh10 t L S x₁ x₂ lam rho) {f₁ f₂ : G}
    (h₁ : f₁ ∈ l41F t x₁ x₂ rho) (h₂ : f₂ ∈ l41F t x₁ x₂ rho) :
    ⁅f₁, f₂⁆ ∈ l41Y t x₁ x₂ rho := by
  rcases m13_mem_F h.toL41GPh8 h₁ with h₁R | ⟨k₁, hk₁, rfl⟩
  · rcases m13_mem_F h.toL41GPh8 h₂ with h₂R | ⟨k₂, hk₂, rfl⟩
    · rw [commutatorElement_eq_one_iff_mul_comm.mpr (m13_comm_R h h₁R h₂R)]
      exact (l41Y t x₁ x₂ rho).one_mem
    · rw [(commutatorElement_inv (t * k₂) f₁).symm]
      exact Subgroup.inv_mem _ (q15_comm_tR_R h hk₂ h₁R)
  · rcases m13_mem_F h.toL41GPh8 h₂ with h₂R | ⟨k₂, hk₂, rfl⟩
    · exact q15_comm_tR_R h hk₁ h₂R
    · exact q15_comm_tR_tR h hk₁ hk₂

end Q15D0

section Q15D1

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}
variable [((l41Y t x₁ x₂ rho).subgroupOf (l41Q t x₁ x₂ rho)).Normal]

theorem q15_cent_tbar_iff (h : L41GPh10 t L S x₁ x₂ lam rho) (q : ↥(l41Q t x₁ x₂ rho)) :
    (QuotientGroup.mk q : q15T t x₁ x₂ rho) ∈
        centralizer ({q15Tbar h.toL41GPh8} : Set (q15T t x₁ x₂ rho)) ↔
      (q : G) ∈ l41F t x₁ x₂ rho := by
  let N : Subgroup ↥(l41Q t x₁ x₂ rho) :=
    (l41Y t x₁ x₂ rho).subgroupOf (l41Q t x₁ x₂ rho)
  let tQ : ↥(l41Q t x₁ x₂ rho) := ⟨t, q14_t_mem_Q h.toL41GPh8⟩
  have htbar : q15Tbar h.toL41GPh8 = (QuotientGroup.mk' N tQ : ↥(l41Q t x₁ x₂ rho) ⧸ N) := rfl
  have hmk : (QuotientGroup.mk q : q15T t x₁ x₂ rho) = (QuotientGroup.mk' N q : _) := rfl
  rw [Subgroup.mem_centralizer_singleton_iff, hmk, htbar,
    ← commutatorElement_eq_one_iff_mul_comm]
  constructor
  · intro h1
    rw [← map_commutatorElement (QuotientGroup.mk' N)] at h1
    have hmemN : ⁅q, tQ⁆ ∈ N := (QuotientGroup.eq_one_iff ⁅q, tQ⁆).mp h1
    rw [Subgroup.mem_subgroupOf] at hmemN
    have hcoe : ((⁅q, tQ⁆ : ↥(l41Q t x₁ x₂ rho)) : G) = ⁅(q : G), t⁆ :=
      map_commutatorElement (Subgroup.subtype (l41Q t x₁ x₂ rho)) q tQ
    rw [hcoe] at hmemN
    exact (Set.ext_iff.mp (q14_cent_Qbar_t_F h) (q : G)).mp ⟨q.2, hmemN⟩
  · intro hqF
    have hcommY : ⁅(q : G), t⁆ ∈ l41Y t x₁ x₂ rho :=
      ((Set.ext_iff.mp (q14_cent_Qbar_t_F h) (q : G)).mpr hqF).2
    rw [← map_commutatorElement (QuotientGroup.mk' N)]
    apply (QuotientGroup.eq_one_iff ⁅q, tQ⁆).mpr
    rw [Subgroup.mem_subgroupOf]
    have hcoe : ((⁅q, tQ⁆ : ↥(l41Q t x₁ x₂ rho)) : G) = ⁅(q : G), t⁆ :=
      map_commutatorElement (Subgroup.subtype (l41Q t x₁ x₂ rho)) q tQ
    rw [hcoe]
    exact hcommY

theorem q15_cent_tbar_E8 (h : L41GPh10 t L S x₁ x₂ lam rho) :
    Nonempty (↥(centralizer ({q15Tbar h.toL41GPh8} : Set (q15T t x₁ x₂ rho))) ≃*
      CFSG.GH74.GLS.Bg.TwoGroups.E2 3) := by
  let N : Subgroup ↥(l41Q t x₁ x₂ rho) :=
    (l41Y t x₁ x₂ rho).subgroupOf (l41Q t x₁ x₂ rho)
  let F' : Subgroup ↥(l41Q t x₁ x₂ rho) :=
    (l41F t x₁ x₂ rho).subgroupOf (l41Q t x₁ x₂ rho)
  let φ : ↥F' →* q15T t x₁ x₂ rho := (QuotientGroup.mk' N).comp F'.subtype
  have hNF' : N ≤ F' := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (m13_Y_le_R t x₁ x₂ rho).trans le_sup_left hx
  have hFcard : Nat.card ↥F' = 128 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (q14_F_le_Q h.toL41GPh8)).toEquiv,
      m13_card_F h.toL41GPh8]
    norm_num
  have hker : φ.ker = N.subgroupOf F' := by
    ext x
    exact QuotientGroup.eq_one_iff ((x : ↥F') : ↥(l41Q t x₁ x₂ rho))
  have hKcard : Nat.card ↥φ.ker = 16 := by
    rw [hker]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNF').toEquiv]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (q14_Y_le_Q h)).toEquiv, m11_card_Y h]
  have hV : φ.range = centralizer ({q15Tbar h.toL41GPh8} : Set (q15T t x₁ x₂ rho)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      change (QuotientGroup.mk ((x : ↥F') : ↥(l41Q t x₁ x₂ rho)) : q15T t x₁ x₂ rho) ∈
        centralizer ({q15Tbar h.toL41GPh8} : Set (q15T t x₁ x₂ rho))
      rw [q15_cent_tbar_iff h ((x : ↥F') : ↥(l41Q t x₁ x₂ rho))]
      exact x.2
    · intro hy
      obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective y
      have hqV : (QuotientGroup.mk q : q15T t x₁ x₂ rho) ∈
          centralizer ({q15Tbar h.toL41GPh8} : Set (q15T t x₁ x₂ rho)) := by
        rw [hq]; exact hy
      have hqF : (q : G) ∈ l41F t x₁ x₂ rho := (q15_cent_tbar_iff h q).mp hqV
      exact ⟨⟨q, hqF⟩, hq⟩
  refine CFSG.GH74.GLS.Bg.TwoGroups.L26.elemAbelian_equiv
    (V := ↥(centralizer ({q15Tbar h.toL41GPh8} : Set (q15T t x₁ x₂ rho)))) ?_ ?_ 3 ?_
  · intro a b
    obtain ⟨q₁, hq₁⟩ := QuotientGroup.mk_surjective a.1
    obtain ⟨q₂, hq₂⟩ := QuotientGroup.mk_surjective b.1
    have haV : (QuotientGroup.mk q₁ : q15T t x₁ x₂ rho) ∈
        centralizer ({q15Tbar h.toL41GPh8} : Set (q15T t x₁ x₂ rho)) := by
      rw [hq₁]; exact a.2
    have hbV : (QuotientGroup.mk q₂ : q15T t x₁ x₂ rho) ∈
        centralizer ({q15Tbar h.toL41GPh8} : Set (q15T t x₁ x₂ rho)) := by
      rw [hq₂]; exact b.2
    have haF : (q₁ : G) ∈ l41F t x₁ x₂ rho := (q15_cent_tbar_iff h q₁).mp haV
    have hbF : (q₂ : G) ∈ l41F t x₁ x₂ rho := (q15_cent_tbar_iff h q₂).mp hbV
    apply Subtype.ext
    change a.1 * b.1 = b.1 * a.1
    rw [← hq₁, ← hq₂, ← commutatorElement_eq_one_iff_mul_comm]
    change ⁅(QuotientGroup.mk' N q₁ : q15T t x₁ x₂ rho), QuotientGroup.mk' N q₂⁆ = 1
    rw [← map_commutatorElement (QuotientGroup.mk' N)]
    apply (QuotientGroup.eq_one_iff ⁅q₁, q₂⁆).mpr
    rw [Subgroup.mem_subgroupOf]
    have hcoe : ((⁅q₁, q₂⁆ : ↥(l41Q t x₁ x₂ rho)) : G) = ⁅(q₁ : G), (q₂ : G)⁆ :=
      map_commutatorElement (Subgroup.subtype (l41Q t x₁ x₂ rho)) q₁ q₂
    rw [hcoe]
    exact q15_comm_F_Y h haF hbF
  · intro a
    obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective a.1
    have haV : (QuotientGroup.mk q : q15T t x₁ x₂ rho) ∈
        centralizer ({q15Tbar h.toL41GPh8} : Set (q15T t x₁ x₂ rho)) := by
      rw [hq]; exact a.2
    have haF : (q : G) ∈ l41F t x₁ x₂ rho := (q15_cent_tbar_iff h q).mp haV
    apply Subtype.ext
    change a.1 * a.1 = (1 : q15T t x₁ x₂ rho)
    rw [← hq, ← QuotientGroup.mk_mul]
    apply (QuotientGroup.eq_one_iff (q * q)).mpr
    rw [Subgroup.mem_subgroupOf]
    simpa using q14_sq_mem_Y h haF
  · have hcf := Subgroup.card_ker_mul_card_range φ
    rw [hKcard, hFcard] at hcf
    have hrange : Nat.card ↥φ.range = 8 := by omega
    rw [hV] at hrange
    have hpow : (2 : ℕ) ^ 3 = 8 := by norm_num
    rw [hpow]
    exact hrange

end Q15D1

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
