module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InvCls
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModel
public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec2Aux

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData CFSG.ComponentClassification.GrSLit
open CFSG.ComponentClassification.GrSLit.L34Facts

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {α : ℕ}

theorem Hyp.mem_centralizer_of_mem_zStarIn (h : Hyp G A) {z : G} (hz : z ∈ zStarIn A) :
    z ∈ centralizer (A : Set G) := by
  obtain ⟨z', hz', rfl⟩ := hz
  rw [h.fusionZStar_eq_center] at hz'
  rw [mem_centralizer_iff]
  intro a ha
  have := mem_center_iff.1 hz' ⟨a, ha⟩
  exact congrArg Subtype.val this

theorem Chart4.eq_one_or_q_of_center (c : Chart4 d α)
    (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4) {z : G} (hzS : z ∈ d.S)
    (hzc : z ∈ centralizer (A : Set G)) (hz2 : z * z = 1) : z = 1 ∨ z = d.q := by
  have hzQ : z ∈ d.Q := ⟨d.S_le_X hzS, hzc⟩
  have hzt : z ∈ zpowers c.t := by rw [← c.Q_inf_S_eq hc]; exact ⟨hzQ, hzS⟩
  obtain ⟨n, hn, rfl⟩ := c.exists_pow_t hzt
  have ht4 : c.t ^ 4 = 1 := c.frame.t4
  have hq : d.q = c.t ^ 2 := c.q_eq
  rw [hq]
  interval_cases n
  · left; simp
  · exfalso
    have h2 : c.t * c.t = 1 := by simpa using hz2
    have : c.t ^ 2 = 1 := by rw [pow_two]; exact h2
    have h4 := orderOf_dvd_of_pow_eq_one this
    rw [c.orderOf_t] at h4
    omega
  · right; rfl
  · exfalso
    have h6 : c.t ^ 6 = 1 := by
      have : c.t ^ 3 * c.t ^ 3 = 1 := hz2
      simpa [← pow_add] using this
    have h4 := orderOf_dvd_of_pow_eq_one h6
    rw [c.orderOf_t] at h4
    omega

theorem Chart4.involution_conj_pi (c : Chart4 d α) (h : Hyp G A)
    (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4) {i : G} (hi : i ∈ d.S)
    (hi2 : i * i = 1) (hi1 : i ≠ 1) (hiq : i ≠ d.q) : ∃ a ∈ A, cj i a = c.pi := by
  have hiA : i ∈ A := d.S_le_A hi
  have hpiA : c.pi ∈ A := d.S_le_A c.mem.1
  have hmuA : c.mu ∈ A := d.S_le_A c.mem.2.2.1
  have hpi2 : c.pi * c.pi = 1 := by simpa [pow_two] using c.frame.pi2
  have hiZ : i ∉ zStarIn A := fun hz => by
    rcases c.eq_one_or_q_of_center hc hi (h.mem_centralizer_of_mem_zStarIn hz) hi2 with h1 | h1
    exacts [hi1 h1, hiq h1]
  have hpe : cj c.pi c.mu = c.t ^ 2 * c.pi := c.frame.pi_mu
  have hpiZ : c.pi ∉ zStarIn A := fun hz => by
    have hcomm := mem_centralizer_iff.1 (h.mem_centralizer_of_mem_zStarIn hz) c.mu hmuA
    have h1 : cj c.pi c.mu = c.pi := by
      unfold cj
      rw [mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [h1] at hpe
    have h2 : c.t ^ 2 = 1 := by
      have := congrArg (fun x => x * c.pi⁻¹) hpe
      simpa using this.symm
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [c.orderOf_t] at h3
    omega
  obtain ⟨j, hj⟩ := GrS4.exists_conj_jq_mem_center h.isL34Type hiA hpiA hi2 hpi2 hiZ hpiZ
  obtain ⟨z₀, hz₀S, hz₀A, hz₀⟩ :=
    exists_mem_of_mem_center (isSylowTwoIn_of_isSylowOf d.S_sylow) hj
  set cA : ↥A := j⁻¹ * ⟨i, hiA⟩ * j with hcA
  have hcA2 : cA * cA = 1 := by
    rw [hcA]
    calc j⁻¹ * ⟨i, hiA⟩ * j * (j⁻¹ * ⟨i, hiA⟩ * j) = j⁻¹ * (⟨i, hiA⟩ * ⟨i, hiA⟩) * j := by group
      _ = 1 := by rw [show (⟨i, hiA⟩ : ↥A) * ⟨i, hiA⟩ = 1 from Subtype.ext hi2]; group
  have hjz : jq A cA = jq A ⟨c.pi, hpiA⟩ * jq A ⟨z₀, hz₀A⟩ := by
    rw [hz₀]; group
  have hz₀2 : z₀ * z₀ = 1 := by
    have hz₀S2 : z₀ * z₀ ∈ d.S := mul_mem hz₀S hz₀S
    refine eq_one_of_jq_eq_one d.S_le_A (M1b.S_isPGroup d) hz₀S2 ?_
    have hcen : jq A ⟨z₀, hz₀A⟩ ∈ center (Jhat A) := by rw [hz₀]; exact hj
    have hsq : jq A cA * jq A cA = 1 := by rw [← map_mul, hcA2, map_one]
    have hpp : jq A ⟨c.pi, hpiA⟩ * jq A ⟨c.pi, hpiA⟩ = 1 := by
      rw [← map_mul, show (⟨c.pi, hpiA⟩ : ↥A) * ⟨c.pi, hpiA⟩ = 1 from Subtype.ext hpi2, map_one]
    have hcom : jq A ⟨z₀, hz₀A⟩ * jq A ⟨c.pi, hpiA⟩ = jq A ⟨c.pi, hpiA⟩ * jq A ⟨z₀, hz₀A⟩ :=
      (mem_center_iff.1 hcen _).symm
    rw [hjz] at hsq
    have : jq A ⟨z₀, hz₀A⟩ * jq A ⟨z₀, hz₀A⟩ = 1 := by
      calc jq A ⟨z₀, hz₀A⟩ * jq A ⟨z₀, hz₀A⟩
          = (jq A ⟨c.pi, hpiA⟩ * jq A ⟨c.pi, hpiA⟩) * (jq A ⟨z₀, hz₀A⟩ * jq A ⟨z₀, hz₀A⟩) := by
            rw [hpp, one_mul]
        _ = jq A ⟨c.pi, hpiA⟩ * (jq A ⟨c.pi, hpiA⟩ * jq A ⟨z₀, hz₀A⟩) * jq A ⟨z₀, hz₀A⟩ := by
            group
        _ = jq A ⟨c.pi, hpiA⟩ * (jq A ⟨z₀, hz₀A⟩ * jq A ⟨c.pi, hpiA⟩) * jq A ⟨z₀, hz₀A⟩ := by
            rw [hcom]
        _ = (jq A ⟨c.pi, hpiA⟩ * jq A ⟨z₀, hz₀A⟩) * (jq A ⟨c.pi, hpiA⟩ * jq A ⟨z₀, hz₀A⟩) := by
            group
        _ = 1 := hsq
    rw [show (⟨z₀ * z₀, d.S_le_A hz₀S2⟩ : ↥A) = ⟨z₀, hz₀A⟩ * ⟨z₀, hz₀A⟩ from rfl, map_mul]
    exact this
  have hz₀Z : z₀ ∈ zStarIn A := by
    rw [mem_zStarIn_iff hz₀A, hz₀]
    exact hj
  have hz₀c := h.mem_centralizer_of_mem_zStarIn hz₀Z
  have hpz : c.pi * z₀ = z₀ * c.pi := (mem_centralizer_iff.1 hz₀c c.pi hpiA)
  have hpz2 : (c.pi * z₀) ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    calc c.pi * z₀ * (c.pi * z₀) = c.pi * (z₀ * c.pi) * z₀ := by group
      _ = c.pi * (c.pi * z₀) * z₀ := by rw [hpz]
      _ = (c.pi * c.pi) * (z₀ * z₀) := by group
      _ = 1 := by rw [hpi2, hz₀2, one_mul]
  have hcA2' : ((cA : ↥A) : G) ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    exact congrArg Subtype.val hcA2
  have hmul : c.pi * z₀ ∈ A := mul_mem hpiA (d.S_le_A hz₀S)
  have heq : ((cA : ↥A) : G) = c.pi * z₀ := by
    refine M1b.eq_of_jq_eq_of_pow h cA.2 hmul hcA2' hpz2 ?_
    rw [hjz]
    exact (map_mul (jq A) ⟨c.pi, hpiA⟩ ⟨z₀, hz₀A⟩).symm
  have hcj : cj i (j : G) = c.pi * z₀ := by
    have : ((cA : ↥A) : G) = (j : G)⁻¹ * i * j := by simp [hcA]
    rw [← heq, this]
    rfl
  rcases c.eq_one_or_q_of_center hc hz₀S hz₀c hz₀2 with h1 | h1
  · exact ⟨j, j.2, by rw [hcj, h1, mul_one]⟩
  · refine ⟨(j : G) * c.mu⁻¹, mul_mem j.2 (inv_mem hmuA), ?_⟩
    have e1 : cj i ((j : G) * c.mu⁻¹) = cj (cj i j) c.mu⁻¹ := by unfold cj; group
    have hqc : c.pi * d.q = d.q * c.pi := mem_centralizer_iff.1 d.q_cent c.pi hpiA
    have e2 : c.pi * d.q = cj c.pi c.mu := by
      rw [hpe, ← c.q_eq]
      exact hqc
    rw [e1, hcj, h1, e2]
    unfold cj
    group

theorem Chart4.involution_QS_conj_pi (hα : α ≤ 1) (c : Chart4 d α)
    (h : Hyp G A) (hP : chPresOK = true) (hQ : chPropsOK = true)
    (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4) {i : G} (hi : i ∈ d.QS)
    (hi2 : i * i = 1) (hi1 : i ≠ 1) (hiq : i ≠ d.q) : IsConj i c.pi := by
  obtain ⟨a, -, ha⟩ := c.involution_conj_pi h hc (c.involutions_in_S' hα h hP hQ hc hi hi2) hi2
    hi1 hiq
  exact isConj_iff.2 ⟨a⁻¹, by rw [← ha]; unfold cj; group⟩

end CFSG.OddStandard.ChengHeld
