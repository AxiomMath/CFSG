module

public import CFSG.ClassicalInvolution.Q3.Q3T6D10A
public import CFSG.ClassicalInvolution.Q3.Q3T6D9B
import CFSG.ClassicalInvolution.Asc77.AscT3CLate10BEng

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6D

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem Std20Three.late_W_exp_four (d : Std20Three K K' J S R R' W V z t) (h8 : Nat.card R = 8) :
    ∀ w ∈ W, (w * w) * (w * w) = 1 := by
  obtain ⟨u, r, v, t₀, T, hh⟩ := d.late_exists_hex
  have hTR : Nat.card R = Nat.card T :=
    Sec6Gen.natCard_isSylow2In_eq d.late_hΩ d.late_mem_K d.late_mem_J d.hR hh.hd'.sylow
  have hu4 : orderOf u = 4 := by
    have := hh.hd.card
    omega
  have hv4 : orderOf v = 4 := by
    have := hh.hd'.card
    omega
  have hu4' : u ^ 4 = 1 := by rw [← hu4]; exact pow_orderOf_eq_one u
  have hv4' : v ^ 4 = 1 := by rw [← hv4]; exact pow_orderOf_eq_one v
  intro w hw
  have hWeq : W = Subgroup.zpowers u ⊔ Subgroup.zpowers v := by
    rw [hh.W₀_eq, inf_comm K W, inf_comm J W]
    exact d.late_hW
  have hN : Subgroup.zpowers v ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G) := fun g hg =>
    Subgroup.centralizer_le_normalizer (Subgroup.zpowers u : Set G)
      (Subgroup.mem_centralizer_iff.mpr fun h hh' => by
        have hhW : h ∈ W := Subgroup.zpowers_le.mpr hh.hd.u_memW hh'
        have hgW : g ∈ W := Subgroup.zpowers_le.mpr hh.hd'.u_memW hg
        exact d.late_hWc h hhW g hgW)
  rw [hWeq] at hw
  obtain ⟨a, ha, b, hb, rfl⟩ := Sec6Gen.exists_mul_of_mem_sup_of_le_normalizer hN hw
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hcomm : u ^ i * v ^ j = v ^ j * u ^ i := by
    have := d.late_hWc u hh.hd.u_memW v hh.hd'.u_memW
    exact ((Commute.zpow_zpow (show Commute u v from this) i j).eq)
  have hi : (u ^ i) ^ 4 = 1 := by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]; simp [hu4']
  have hj : (v ^ j) ^ 4 = 1 := by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]; simp [hv4']
  have hc : Commute (u ^ i) (v ^ j) := hcomm
  calc (u ^ i * v ^ j * (u ^ i * v ^ j)) * (u ^ i * v ^ j * (u ^ i * v ^ j))
      = (u ^ i * v ^ j) ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = (u ^ i) ^ 4 * (v ^ j) ^ 4 := hc.mul_pow 4
    _ = 1 := by rw [hi, hj, one_mul]

private theorem Std20Three.late_toG (d : Std20Three K K' J S R R' W V z t) :
    Std20G K K' J S R R' W V z t :=
  { toStd20F :=
      { d with
        hyp := d.late_hΩ
        late_ne_inv := d.late_ne_inv
        late_mnorm := mem_normalizer_of_mem_omegaStarNbr d.late_hΩ d.viol.star d.viol.hzJ
        late_card2 := fun hU hK hR =>
          Q3T6.Gen612.natCard_eq_two_mul_of_mem_USet d.late_hΩ hU hK hR }
    late_hWc := d.late_hWc
    late_t_mem_W := d.late_t_mem_W
    late_z_mem_W := d.late_z_mem_W
    late_hW := d.late_hW
    late_JW := d.late_JW
    late_exists_swap := d.late_exists_swap
    late_swap_data := fun hu huK => d.late_swap_data hu huK }

theorem Std20Three.late_swap_sq_data (d : Std20Three K K' J S R R' W V z t) {σ e : G}
    (hσ : σ ∈ (S : Subgroup G)) (hσK : conjSub σ K = K') (hσ2 : σ * σ ∈ W)
    (heKW : e ∈ K ⊓ W) (he2 : e * e = z) :
    (e * (σ * e * σ⁻¹) = t ∨ e * (σ * e * σ⁻¹) = z * t) ∧ σ * t * σ⁻¹ = t := by
  exact d.late_toG.late_swap_sq_data hσ hσK hσ2 heKW he2

theorem Std20Three.late_swap_sq_sq (d : Std20Three K K' J S R R' W V z t) (h8 : Nat.card R = 8)
    {σ : G} (hσ : σ ∈ (S : Subgroup G)) (hσK : conjSub σ K = K') (hσ2 : σ * σ ∈ W) :
    (σ * σ) * (σ * σ) = 1 := by
  by_contra hne
  refine d.late_no_fixed_four hσ hσK hσ2 hne (d.late_W_exp_four h8 _ hσ2) ?_
  calc σ * (σ * σ) * σ⁻¹ = σ * σ := by group

theorem Std20Three.late_exists_b (d : Std20Three K K' J S R R' W V z t) (h8 : Nat.card R = 8)
    (c3 : Concl20_3 K K' V z)
    (hTX : ∀ g ∈ (S : Subgroup G), conjSub g K = K →
      g ∈ sec20X (CoreAssembly.conjClass K) z K K') :
    ∃ b ∈ (S : Subgroup G), conjSub b K = K' ∧ (b * b = t ∨ b * b = z * t) := by
  obtain ⟨u, hu, huK⟩ := d.late_exists_swap
  have hu2 : conjSub (u * u) K = K := by
    rw [conjSub_mul, huK, (d.late_swap_data hu huK).1]
  obtain ⟨σ, hσ, hσK, hσ2⟩ := d.late_exists_sq_W c3 hu huK
    (hTX _ (Subgroup.mul_mem _ hu hu) hu2)
  obtain ⟨⟨e, heKW, he2⟩, -⟩ := d.late_exists_four_gens
  obtain ⟨ha₀, hσt⟩ := d.late_swap_sq_data hσ hσK hσ2 heKW he2
  have hs4 := d.late_swap_sq_sq h8 hσ hσK hσ2
  have hs₂ : σ * σ = 1 ∨ σ * σ = z ∨ σ * σ = t ∨ σ * σ = z * t :=
    d.late_inv_W _ hσ2 hs4
  rcases hs₂ with h | h | h | h
  ·
    refine ⟨σ * e, Subgroup.mul_mem _ hσ (d.hWS heKW.2), ?_, ?_⟩
    · rw [conjSub_mul, conjSub_eq_self_of_mem heKW.1, hσK]
    · have hb2 : (σ * e) * (σ * e) = (σ * σ) * (e * (σ * e * σ⁻¹)) := by
        have hW1 := d.late_hWc
        have heσW : σ * e * σ⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (d.hWN hσ) e).mp heKW.2
        calc (σ * e) * (σ * e) = (σ * e * σ⁻¹) * (σ * σ) * e := by group
          _ = (σ * σ) * ((σ * e * σ⁻¹) * e) := by rw [hW1 _ heσW _ hσ2]; group
          _ = (σ * σ) * (e * (σ * e * σ⁻¹)) := by rw [hW1 _ heσW _ heKW.2]
      rw [hb2, h, one_mul]
      exact ha₀
  ·
    refine ⟨σ * e, Subgroup.mul_mem _ hσ (d.hWS heKW.2), ?_, ?_⟩
    · rw [conjSub_mul, conjSub_eq_self_of_mem heKW.1, hσK]
    · have hb2 : (σ * e) * (σ * e) = (σ * σ) * (e * (σ * e * σ⁻¹)) := by
        have hW1 := d.late_hWc
        have heσW : σ * e * σ⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (d.hWN hσ) e).mp heKW.2
        calc (σ * e) * (σ * e) = (σ * e * σ⁻¹) * (σ * σ) * e := by group
          _ = (σ * σ) * ((σ * e * σ⁻¹) * e) := by rw [hW1 _ heσW _ hσ2]; group
          _ = (σ * σ) * (e * (σ * e * σ⁻¹)) := by rw [hW1 _ heσW _ heKW.2]
      rw [hb2, h]
      rcases ha₀ with ha | ha
      · right
        rw [ha]
      · left
        rw [ha, ← mul_assoc, d.viol.hzK.sq, one_mul]
  · exact ⟨σ, hσ, hσK, Or.inl h⟩
  · exact ⟨σ, hσ, hσK, Or.inr h⟩

end Std

end CFSG.ClassicalInvolution.Q3.Q3T6D
