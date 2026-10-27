module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiRTwoElem
public import CFSG.GH74.BNPair.L15Maschke

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis SzPartition

variable {G : Type} [Group G] [Finite G] {K : Type*} [Field K] [Fintype K] [CharP K 2]

namespace SzRSetup

variable {T₁ R : Subgroup G} {t d : G} {a : ℕ} {u v : G → K} {κ : K}
  (h : SzRSetup T₁ R t d a u v κ)
include h

theorem exists_szR2 (h34 : NoStronglyClosedAbelianTwo G) (hodd : Odd (orderOf d)) :
    ∃ R₂ : Subgroup G, SzR2 T₁ R₂ t d ∧ T₁ ⊔ R₂ ⊔ zpowers t = R ∧
      (T₁ ⊔ zpowers t) ⊓ R₂ = szA₁ T₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD : Nat.Coprime 2 (Nat.card (zpowers d)) := by
    rw [Nat.card_zpowers]
    exact Nat.coprime_two_left.mpr hodd
  have hconj : ∀ {H : Subgroup G}, d ∈ normalizer (H : Set G) →
      ∀ g ∈ zpowers d, ∀ x ∈ H, g * x * g⁻¹ ∈ H := by
    intro H hdH g hg x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    exact (mem_normalizer_iff.mp (zpow_mem hdH k) x).mp hx
  obtain ⟨R₂, hAR₂, hR₂R, hdR₂, hsup, hinf⟩ :=
    CFSG.GH74.BNPair.exists_invariant_complement_interval (p := 2) (Q := R) (Φ := szA₁ T₁)
      (D := zpowers d) (T := T₁ ⊔ zpowers t) h.szA₁_le_R
      (fun x hx y hy => h.comm_mem_szA₁ h34 hx hy) (fun x hx => h.sq_mem_szA₁ h34 hx) hD
      (hconj h.d_mem_normalizer_R) (hconj h.d_mem_normalizer_szA₁)
      ((szA₁_le T₁).trans le_sup_left) h.le (hconj h.d_mem_normalizer_T)
  have hdR₂' : d ∈ normalizer (R₂ : Set G) :=
    mem_normalizer_iff.mpr fun x => ⟨fun hx => hdR₂ d (mem_zpowers d) x hx, fun hx => by
      have := hdR₂ d⁻¹ (inv_mem (mem_zpowers d)) _ hx
      simpa [mul_assoc] using this⟩
  have hker : ∀ r ∈ R₂, r * t * r⁻¹ * t⁻¹ = 1 ↔ r ∈ szA₁ T₁ := by
    intro r hr
    rw [h.rho_eq_one_iff (hR₂R hr), ← hinf]
    exact ⟨fun h1 => mem_inf.mpr ⟨h1, hr⟩, fun h1 => (mem_inf.mp h1).1⟩
  have hR₂T : R₂ ≤ normalizer ((T₁ ⊔ zpowers t : Subgroup G) : Set G) :=
    hR₂R.trans h.le_normalizer_T
  refine ⟨R₂, ⟨h.t_sq, fun x hx => mem_centralizer_iff.mp h.t_mem x hx, h.d_comm, hdR₂', ?_,
    hAR₂, ?_, ?_, ?_, ?_, ?_⟩, ?_, hinf⟩
  ·
    exact commute_of_sq_of_equivariant (U := R₂) (A := szA₁ T₁) (d := d)
      (fun r => r * t * r⁻¹ * t⁻¹) (fun u hu b hb => h.commute_szA₁_of_mem (hR₂R hu) hb)
      (fun b hb => h.sq_eq_one_of_mem_szA₁ hb) (fun u hu => h.sq_mem_szA₁ h34 (hR₂R hu))
      (fun u hu => by
        have := hdR₂ d⁻¹ (inv_mem (mem_zpowers d)) u hu
        simpa using this)
      (fun b hb b' hb' hb1 hb'1 =>
        h.coords.exists_pow_conj_eq_szA₁ h.one_le h.card h.gen' hb hb' hb1 hb'1)
      (fun u hu => h.rho_mem u (hR₂R hu)) (fun u hu u' hu' => h.rho_mul (hR₂R hu) (hR₂R hu'))
      hker (fun u _ => by simpa using h.rho_conj 1 u)
  ·
    intro x hx
    rw [← hinf]
    exact mem_inf.mpr ⟨mem_sup_left (mem_inf.mp hx).1, (mem_inf.mp hx).2⟩
  ·
    intro x hx r hr
    exact h.comm_mem_szA₁ h34 (h.le (mem_sup_left hx)) (hR₂R hr)
  ·
    intro r hr
    exact h.rho_mem r (hR₂R hr)
  ·
    intro b hb
    obtain ⟨x, hx, hxe⟩ := h.exists_conj b hb
    have hx' : x ∈ ((T₁ ⊔ zpowers t ⊔ R₂ : Subgroup G) : Set G) := by rw [hsup]; exact hx
    rw [coe_mul_of_right_le_normalizer_left (T₁ ⊔ zpowers t) R₂ hR₂T] at hx'
    obtain ⟨y, hy, r, hr, rfl⟩ := hx'
    refine ⟨r, hr, ?_⟩
    have h1 := h.rho_mul (h.le hy) (hR₂R hr)
    rw [(h.rho_eq_one_iff (h.le hy)).mpr hy, one_mul] at h1
    rw [← h1, hxe, mul_inv_cancel_right]
  ·
    intro r hr h1
    exact (hker r hr).mp h1
  ·
    apply le_antisymm
    · exact sup_le (sup_le (le_sup_left.trans h.le) hR₂R) (le_sup_right.trans h.le)
    · rw [← hsup]
      exact sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
        (le_sup_right.trans le_sup_left)

end SzRSetup

end CFSG.SeitzReduction.RankOne
