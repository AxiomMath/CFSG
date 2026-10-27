module

public import CFSG.ClassicalInvolution.Q3.Q3T6D8A
public import CFSG.ClassicalInvolution.Q3.Q3T6D9C
import CFSG.ClassicalInvolution.Asc77.AscT3CLate10AEng

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

theorem Std20Three.late_exists_m (d : Std20Three K K' J S R R' W V z t) {a₀ : G}
    (h : a₀ = z ∨ a₀ = t ∨ a₀ = z * t) :
    ∃ m ∈ Subgroup.normalizer (W : Set G), m * z * m⁻¹ = a₀ := by
  rcases h with h | h | h
  · exact ⟨1, Subgroup.one_mem _, by rw [h]; group⟩
  · obtain ⟨m, hm, hmz⟩ := d.late_exists_n
    exact ⟨m, hm, by rw [h]; exact hmz⟩
  · obtain ⟨u, r, v, t₀, T, hh⟩ := d.late_exists_hex
    exact ⟨t₀, hh.t₀_normW, by rw [h]; exact hh.htz⟩

theorem Std20Three.late_exists_four_gens (d : Std20Three K K' J S R R' W V z t) :
    (∃ e ∈ K ⊓ W, e * e = z) ∧ ∃ e ∈ K' ⊓ W, e * e = z := by
  obtain ⟨x, r₀, hd⟩ := late_exists_dDataGen d.late_hΩ d.hW d.late_R_mem_D
    d.late_mem_K d.hR d.viol.hzK
  obtain ⟨x', r₀', hd'⟩ := late_exists_dDataGen d.late_hΩ d.hW
    d.late_R'_mem_D d.late_mem_K' d.hR' d.late_hzK'
  exact ⟨late_sq_root_of_dData hd, late_sq_root_of_dData hd'⟩

theorem Std20Three.late_W_four_mem (d : Std20Three K K' J S R R' W V z t) {ξ : G} (hξW : ξ ∈ W)
    (hξ2 : ξ * ξ ≠ 1) (hξ4 : (ξ * ξ) * (ξ * ξ) = 1) :
    ∃ m ∈ Subgroup.normalizer (W : Set G), m * z * m⁻¹ = ξ * ξ ∧
      (ξ ∈ conjSub m K ∨ ξ ∈ conjSub m K') := by
  have ha₀W : ξ * ξ ∈ W := W.mul_mem hξW hξW
  have ha₀' : ξ * ξ = z ∨ ξ * ξ = t ∨ ξ * ξ = z * t := by
    rcases d.late_inv_W _ ha₀W hξ4 with h | h | h | h
    · exact absurd h hξ2
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  obtain ⟨m, hmN, hme⟩ := d.late_exists_m ha₀'
  obtain ⟨hL₁, hL₂, hL₁₂, hL₁i, hL₂i⟩ := d.late_member_data m
  obtain ⟨⟨e, heKW, he2⟩, ⟨e', he'K'W, he'2⟩⟩ := d.late_exists_four_gens
  have hconjm : ∀ w ∈ W, m * w * m⁻¹ ∈ W := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp hmN w).mp hw
  have hb₁2 : (m * e * m⁻¹) * (m * e * m⁻¹) = ξ * ξ := by
    calc (m * e * m⁻¹) * (m * e * m⁻¹) = m * (e * e) * m⁻¹ := by group
      _ = ξ * ξ := by rw [he2]; exact hme
  have hb₂2 : (m * e' * m⁻¹) * (m * e' * m⁻¹) = ξ * ξ := by
    calc (m * e' * m⁻¹) * (m * e' * m⁻¹) = m * (e' * e') * m⁻¹ := by group
      _ = ξ * ξ := by rw [he'2]; exact hme
  have hA₂ : ∀ {w : G}, w ∈ W → IsPGroup 2 ↥(Subgroup.zpowers w) := fun hw =>
    S.isPGroup'.to_le (Subgroup.zpowers_le.mpr (d.hWS hw))
  have hA₄ : ∀ {w : G}, w * w = ξ * ξ → 4 ≤ Nat.card ↥(Subgroup.zpowers w) := fun hw => by
    rw [Nat.card_zpowers, late_orderOf_four hw hξ2 hξ4]
  have hb₁L : m * e * m⁻¹ ∈ conjSub m K := conj_mem_conjSub heKW.1
  have hb₂L : m * e' * m⁻¹ ∈ conjSub m K' := conj_mem_conjSub he'K'W.1
  have hb₁W : m * e * m⁻¹ ∈ W := hconjm e heKW.2
  have hb₂W : m * e' * m⁻¹ ∈ W := hconjm e' he'K'W.2
  have hne : Subgroup.zpowers (m * e * m⁻¹) ≠ Subgroup.zpowers (m * e' * m⁻¹) := by
    intro h
    exact hL₁₂ (Sec6Gen.eq_of_le_of_le d.late_hΩ hL₁ hL₂ (hA₂ hb₁W) (hA₄ hb₁2)
      (Subgroup.zpowers_le.mpr hb₁L) (h ▸ Subgroup.zpowers_le.mpr hb₂L))
  refine ⟨m, hmN, hme, ?_⟩
  rcases d.late_two_lines hξ2 hξ4 hξW hb₁W hb₂W rfl hb₁2 hb₂2 hne with h | h
  · left
    exact (h ▸ Subgroup.zpowers_le.mpr hb₁L : Subgroup.zpowers ξ ≤ conjSub m K)
      (Subgroup.mem_zpowers ξ)
  · right
    exact (h ▸ Subgroup.zpowers_le.mpr hb₂L : Subgroup.zpowers ξ ≤ conjSub m K')
      (Subgroup.mem_zpowers ξ)

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

theorem Std20Three.late_swap_not_N_member (d : Std20Three K K' J S R R' W V z t) {σ m a₀ : G}
    (hσ : σ ∈ (S : Subgroup G)) (hσK : conjSub σ K = K') (hσa : σ * a₀ * σ⁻¹ = a₀)
    (hme : m * z * m⁻¹ = a₀) (ha₀ : a₀ = z ∨ a₀ = t ∨ a₀ = z * t) {L : Subgroup G}
    (hL : L = conjSub m K ∨ L = conjSub m K') (hσL : conjSub σ L = L) : False := by
  exact d.late_toG.late_swap_not_N_member hσ hσK hσa hme ha₀ hL hσL

theorem Std20Three.late_no_fixed_four (d : Std20Three K K' J S R R' W V z t) {σ ξ : G}
    (hσ : σ ∈ (S : Subgroup G)) (hσK : conjSub σ K = K') (hξW : ξ ∈ W) (hξ2 : ξ * ξ ≠ 1)
    (hξ4 : (ξ * ξ) * (ξ * ξ) = 1) (hfix : σ * ξ * σ⁻¹ = ξ) : False := by
  obtain ⟨m, hmN, hme, hL⟩ := d.late_W_four_mem hξW hξ2 hξ4
  have ha₀' : ξ * ξ = z ∨ ξ * ξ = t ∨ ξ * ξ = z * t := by
    rcases d.late_inv_W _ (W.mul_mem hξW hξW) hξ4 with h | h | h | h
    · exact absurd h hξ2
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hσa : σ * (ξ * ξ) * σ⁻¹ = ξ * ξ := by
    calc σ * (ξ * ξ) * σ⁻¹ = (σ * ξ * σ⁻¹) * (σ * ξ * σ⁻¹) := by group
      _ = ξ * ξ := by rw [hfix]
  have hA₂ : IsPGroup 2 ↥(Subgroup.zpowers ξ) :=
    S.isPGroup'.to_le (Subgroup.zpowers_le.mpr (d.hWS hξW))
  have hA₄ : 4 ≤ Nat.card ↥(Subgroup.zpowers ξ) := by
    rw [Nat.card_zpowers, late_orderOf_four rfl hξ2 hξ4]
  have hcom : ∀ w ∈ Subgroup.zpowers ξ, σ * w * σ⁻¹ = w := by
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hc : Commute σ ξ := by
      calc σ * ξ = (σ * ξ * σ⁻¹) * σ := by group
        _ = ξ * σ := by rw [hfix]
    have := (Commute.zpow_right hc k).eq
    rw [this]
    group
  obtain ⟨L, hLeq, hξL⟩ : ∃ L : Subgroup G, (L = conjSub m K ∨ L = conjSub m K') ∧ ξ ∈ L := by
    rcases hL with h | h
    · exact ⟨conjSub m K, Or.inl rfl, h⟩
    · exact ⟨conjSub m K', Or.inr rfl, h⟩
  obtain ⟨hL₁, hL₂, -, -, -⟩ := d.late_member_data m
  have hLΩ : L ∈ CoreAssembly.conjClass K := by
    rcases hLeq with h | h
    · rw [h]; exact hL₁
    · rw [h]; exact hL₂
  have hσL : conjSub σ L = L := by
    refine Sec6Gen.eq_of_le_of_le d.late_hΩ (d.hyp.conjInvariant σ L hLΩ) hLΩ hA₂ hA₄ ?_
      (Subgroup.zpowers_le.mpr hξL)
    intro w hw
    rw [mem_conjSub_iff]
    have h1 : σ⁻¹ * (σ * w * σ⁻¹) * σ = w := by group
    rw [hcom w hw] at h1
    rw [h1]
    exact Subgroup.zpowers_le.mpr hξL hw
  exact d.late_swap_not_N_member hσ hσK hσa hme ha₀' hLeq hσL

end Std

end CFSG.ClassicalInvolution.Q3.Q3T6D
