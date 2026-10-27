module

public import CFSG.ClassicalInvolution.Asc77.AscR10Plus

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open scoped MatrixGroups commutatorElement

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}




theorem Std20.r_exists_plus_rho [IsSimpleGroup G] (d : Std20 p f K K' J S R R' W V z t)
    (c7 : Concl20_7 S K K' z) (c9 : Concl20_9 S K K' R R' z) (h8 : 8 < Nat.card R) {b : G}
    (hb : FieldInv20 S K K' W z t b) {u : G} {k : ℕ} (hk : 2 ≤ k)
    (hu : Subgroup.zpowers u = K ⊓ W) (huo : orderOf u = 2 ^ (k + 1))
    (hact : ∀ x ∈ K ⊓ W, b * x * b⁻¹ = x ^ ((2 : ℤ) ^ k - 1)) :
    ∃ ρ : G, ρ ∈ K ⊔ K' ∧ ρ ∈ (S : Subgroup G) ∧ ρ * ρ = 1 ∧ ρ ≠ 1 ∧ ρ ≠ z ∧
      b * ρ = ρ * b ∧ FieldInv20 S K K' W z t (b * ρ) ∧
      ∀ x ∈ K ⊓ W, (b * ρ) * x * (b * ρ)⁻¹ = x ^ ((2 : ℤ) ^ k + 1) := by
  obtain ⟨r, hrR, hrW, hbr⟩ := d.r_inverted_elt c9 h8 hb hk hu huo hact
  obtain ⟨s, hsS, hsK, hsb⟩ := d.z_exists_swap c7 c9 h8 hb
  have hbS := hb.mem
  have hb2 := hb.sq
  have hI := d.viol.hzK
  obtain ⟨hr'R', hr't⟩ := d.r_swap_elt hrR hrW hsS hsK
  obtain ⟨hrinv, hr2⟩ := d.w_conj_facts hrR hrW
  have hrt := d.w_conj_t hrR hrW
  have hrz : r * z = z * r := by rw [← hr2, ← mul_assoc]
  have hrK : r ∈ K := d.hR.1 hrR
  have hrS : r ∈ (S : Subgroup G) := d.hRS hrR
  have hKWR : K ⊓ W ≤ R := by
    rw [d.late_R_eq]
    exact inf_le_inf_left K d.hWS
  have hsz : s * z * s⁻¹ = z := d.late_S_act_z hsS
  have hr'2 : (s * r * s⁻¹) * (s * r * s⁻¹) = z := by
    calc (s * r * s⁻¹) * (s * r * s⁻¹) = s * (r * r) * s⁻¹ := by group
      _ = z := by rw [hr2, hsz]
  have hbs : b * s * b⁻¹ = s := by rw [← hsb]; group
  have hbsi : b * s⁻¹ * b⁻¹ = s⁻¹ := by
    have : b * s⁻¹ * b⁻¹ = (b * s * b⁻¹)⁻¹ := by group
    rw [this, hbs]
  have hbr' : b * (s * r * s⁻¹) * b⁻¹ = (s * r * s⁻¹)⁻¹ := by
    calc b * (s * r * s⁻¹) * b⁻¹ = (b * s * b⁻¹) * (b * r * b⁻¹) * (b * s⁻¹ * b⁻¹) := by group
      _ = s * r⁻¹ * s⁻¹ := by rw [hbs, hbr, hbsi]
      _ = (s * r * s⁻¹)⁻¹ := by group
  generalize s * r * s⁻¹ = r' at hr'R' hr't hbr' hr'2
  have hcomm : r * r' = r' * r := d.late_R_R'_comm hrR hr'R'
  have hr'K' : r' ∈ K' := d.hR'.1 hr'R'
  have hρX : r * r' ∈ sec20X (CoreAssembly.conjClass K) z K K' :=
    (sec20X (CoreAssembly.conjClass K) z K K').mul_mem (le_sec20X_left hrK) (le_sec20X_right hr'K')
  have hρinv : (r * r')⁻¹ = r⁻¹ * r'⁻¹ := by rw [hcomm, mul_inv_rev]
  have hρ2 : (r * r') * (r * r') = 1 := by
    calc (r * r') * (r * r') = r * (r' * r) * r' := by group
      _ = r * (r * r') * r' := by rw [← hcomm]
      _ = (r * r) * (r' * r') := by group
      _ = 1 := by rw [hr2, hr'2, hI.sq]
  have hρi : (r * r')⁻¹ = r * r' := inv_eq_of_mul_eq_one_right hρ2
  have hρb : b * (r * r') * b⁻¹ = (r * r')⁻¹ := by
    calc b * (r * r') * b⁻¹ = (b * r * b⁻¹) * (b * r' * b⁻¹) := by group
      _ = (r * r')⁻¹ := by rw [hbr, hbr', hρinv]
  have hbρ : b * (r * r') = (r * r') * b := by
    calc b * (r * r') = (b * (r * r') * b⁻¹) * b := by group
      _ = (r * r') * b := by rw [hρb, hρi]
  have hρt : (r * r') * t * (r * r')⁻¹ = t := by
    have hzzt : z * (z * t) = t := by rw [← mul_assoc, hI.sq, one_mul]
    calc (r * r') * t * (r * r')⁻¹ = r * (r' * t * r'⁻¹) * r⁻¹ := by group
      _ = r * (z * t) * r⁻¹ := by rw [hr't]
      _ = (r * z * r⁻¹) * (r * t * r⁻¹) := by group
      _ = z * (z * t) := by rw [hrt, show r * z * r⁻¹ = z by rw [hrz]; group]
      _ = t := hzzt
  have hbt : b * t * b⁻¹ = t := by rw [hb.comm_t]; group
  have hb't : b * (r * r') * t * (b * (r * r'))⁻¹ = t := by
    calc b * (r * r') * t * (b * (r * r'))⁻¹ = b * ((r * r') * t * (r * r')⁻¹) * b⁻¹ := by group
      _ = b * t * b⁻¹ := by rw [hρt]
      _ = t := hbt
  have hρx : ∀ x ∈ K ⊓ W, (r * r') * x * (r * r')⁻¹ = x⁻¹ := by
    intro x hx
    have hxr' : x * r' = r' * x := d.late_R_R'_comm (hKWR hx) hr'R'
    calc (r * r') * x * (r * r')⁻¹ = r * (r' * x * r'⁻¹) * r⁻¹ := by group
      _ = r * x * r⁻¹ := by rw [← hxr']; group
      _ = x⁻¹ := hrinv x hx
  have hplus : ∀ x ∈ K ⊓ W, b * (r * r') * x * (b * (r * r'))⁻¹ = x ^ ((2 : ℤ) ^ k + 1) := by
    intro x hx
    have hxo : x ^ ((2 : ℤ) ^ (k + 1)) = 1 := by
      rw [← hu] at hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_mul, mul_comm, zpow_mul, show ((2 : ℤ) ^ (k + 1)) = ((2 ^ (k + 1) : ℕ) : ℤ) by
        push_cast; ring, zpow_natCast, ← huo, pow_orderOf_eq_one, one_zpow]
    calc b * (r * r') * x * (b * (r * r'))⁻¹ = b * ((r * r') * x * (r * r')⁻¹) * b⁻¹ := by group
      _ = (b * x * b⁻¹)⁻¹ := by rw [hρx x hx]; group
      _ = (x ^ ((2 : ℤ) ^ k - 1))⁻¹ := by rw [hact x hx]
      _ = x ^ ((2 : ℤ) ^ k + 1) * (x ^ ((2 : ℤ) ^ (k + 1)))⁻¹ := by
          rw [← zpow_neg, ← zpow_neg, ← zpow_add]
          congr 1
          ring
      _ = x ^ ((2 : ℤ) ^ k + 1) := by rw [hxo, inv_one, mul_one]
  have hmem : b * (r * r') ∈ (S : Subgroup G) :=
    (S : Subgroup G).mul_mem hbS ((S : Subgroup G).mul_mem hrS (d.hR'S hr'R'))
  have hsq : b * (r * r') * (b * (r * r')) = 1 := by
    calc b * (r * r') * (b * (r * r')) = (b * (r * r') * b⁻¹) * (b * b) * (r * r') := by group
      _ = 1 := by rw [hρb, hb2, mul_one, inv_mul_cancel]
  have hat : b * (r * r') * t * (b * (r * r'))⁻¹ = t := hb't
  have huKW : u ∈ K ⊓ W := hu ▸ Subgroup.mem_zpowers u
  have hu2 : ¬ u * u = 1 := by
    intro h
    have h1 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [huo] at h1
    have h2 : 2 ^ (k + 1) ≤ 2 := Nat.le_of_dvd (by norm_num) h1
    have h3 : 2 ^ 3 ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := fun k' hk' =>
    d.r10a_X_le_C (le_sec20X_left hk')
  have hρne : ∀ y : G, (y * u * y⁻¹ = u⁻¹) → y ≠ 1 ∧ y ≠ z := by
    intro y hy
    constructor
    · rintro rfl
      apply hu2
      simp only [one_mul, inv_one, mul_one] at hy
      exact mul_eq_one_iff_eq_inv.mpr hy
    · rintro rfl
      apply hu2
      have hzu : y * u = u * y := (Subgroup.mem_centralizer_singleton_iff.mp (hKz huKW.1)).symm
      have : y * u * y⁻¹ = u := by rw [hzu]; group
      rw [this] at hy
      exact mul_eq_one_iff_eq_inv.mpr hy
  have hne := hρne _ (hρx u huKW)
  refine ⟨r * r', Subgroup.mul_mem _ (Subgroup.mem_sup_left hrK) (Subgroup.mem_sup_right hr'K'),
    (S : Subgroup G).mul_mem hrS (d.hR'S hr'R'), hρ2, hne.1, hne.2, hbρ,
    ⟨hmem, hsq, ?_, ?_, ?_, u, k, hk, hu, huo, Or.inl hplus⟩, hplus⟩
  · intro h
    apply hb.not_mem_X
    have := (sec20X (CoreAssembly.conjClass K) z K K').mul_mem h
      ((sec20X (CoreAssembly.conjClass K) z K K').inv_mem hρX)
    rwa [mul_inv_cancel_right] at this
  · calc b * (r * r') * t = b * (r * r') * t * (b * (r * r'))⁻¹ * (b * (r * r')) := by group
      _ = t * (b * (r * r')) := by rw [hb't]
  · exact d.v_conj_t hmem hsq hat hk hu huo (Or.inl hplus)

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
