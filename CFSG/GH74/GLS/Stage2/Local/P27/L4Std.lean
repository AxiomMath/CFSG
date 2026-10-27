module

public import CFSG.GH74.GLS.Stage2.Local.P27.L4Actual
public import CFSG.GH74.GLS.Stage2.Local.P27.L4Gens
public import CFSG.GH74.GLS.Stage2.Local.P27.L4Dec
public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Canon

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.L4

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local.P27.Psp4 CFSG.GH74.GLS.Stage1.Thm3.Sec7.Q
open scoped commutatorElement

variable {G : Type} [Group G] {S P₁ P₂ : Subgroup G} {z t w : G} {a : ℕ}

theorem mul_rr_left (t c p q : G) : c * rr t p q = rr t (c * p) q := by
  simp only [rr, mul_assoc]

namespace DataL4

variable [Finite G] (h : DataL4 S P₁ P₂ z t w a)

include h

theorem one_not_mem_ZcL : (1 : G) ∉ ZcL (P₁ ⊔ P₂) z t w := by
  rintro (((hz | ⟨r, hr, hr1⟩) | ⟨⟨r, hr, hr1⟩, -⟩) | ⟨r, hr, hr1⟩)
  · exact h.z_ne_one hz.symm
  · apply h.t_ne_one
    calc t = r⁻¹ * (r * t * r⁻¹) * r := by group
      _ = 1 := by rw [← hr1]; group
  · apply h.w_not
    have : w = r⁻¹ := by
      calc w = r⁻¹ * (r * w) := by group
        _ = r⁻¹ := by rw [← hr1, mul_one]
    rw [this]; exact inv_mem hr
  · apply h.t_ne_w
    have e : t * w = 1 := by
      calc t * w = r⁻¹ * (r * (t * w) * r⁻¹) * r := by group
        _ = 1 := by rw [← hr1]; group
    calc t = (t * w) * w⁻¹ := by group
      _ = w := by rw [e, one_mul, h.w_inv']

theorem card_R : Nat.card ↥(P₁ ⊔ P₂) = 2 ^ (2 * a - 1) := by
  have hd := h.toPsp4
  let f : ↥P₁ × ↥P₁ →* G :=
    { toFun := fun p => rr t p.1.1 p.2.1
      map_one' := by simp [rr]
      map_mul' := fun p p' => (hd.rr_mul p.2.2 p'.1.2).symm }
  have hrange : f.range = P₁ ⊔ P₂ := by
    ext g
    rw [MonoidHom.mem_range, hd.mem_R_iff]
    constructor
    · rintro ⟨p, rfl⟩; exact ⟨p.1.1, p.1.2, p.2.1, p.2.2, rfl⟩
    · rintro ⟨p, hp, q, hq, rfl⟩; exact ⟨(⟨p, hp⟩, ⟨q, hq⟩), rfl⟩
  let zz : ↥P₁ × ↥P₁ := (⟨z, h.z_mem₁⟩, ⟨z, h.z_mem₁⟩)
  have hzz2 : zz * zz = 1 := by
    ext
    · exact h.z_sq
    · exact h.z_sq
  have hzz1 : zz ≠ 1 := by
    intro e
    have := congrArg (fun p : ↥P₁ × ↥P₁ => (p.1 : G)) e
    exact h.z_ne_one this
  have hker : f.ker = zpowers zz := by
    ext p
    rw [MonoidHom.mem_ker, mem_zpowers_sq_iff hzz2]
    obtain ⟨⟨p₁, hp₁⟩, ⟨p₂, hp₂⟩⟩ := p
    have e : f (⟨p₁, hp₁⟩, ⟨p₂, hp₂⟩) = 1 ↔ rr t p₁ p₂ = rr t 1 1 := by
      show rr t p₁ p₂ = 1 ↔ _
      rw [Data.rr_one]
    rw [e, hd.rr_eq_iff hp₁ hp₂ (one_mem _) (one_mem _)]
    constructor
    · rintro (⟨e1, e2⟩ | ⟨e1, e2⟩)
      · left
        ext
        · exact e1.symm
        · exact e2.symm
      · right
        have e3 : p₁ = z := by
          calc p₁ = z⁻¹ * (z * p₁) := by group
            _ = z := by rw [← e1, mul_one, h.z_inv]
        have e4 : p₂ = z := by
          calc p₂ = z⁻¹ * (z * p₂) := by group
            _ = z := by rw [← e2, mul_one, h.z_inv]
        ext
        · exact e3
        · exact e4
    · rintro (e1 | e1)
      · have e2 : p₁ = 1 := congrArg (fun p : ↥P₁ × ↥P₁ => (p.1 : G)) e1
        have e3 : p₂ = 1 := congrArg (fun p : ↥P₁ × ↥P₁ => (p.2 : G)) e1
        exact Or.inl ⟨e2.symm, e3.symm⟩
      · have e2 : p₁ = z := congrArg (fun p : ↥P₁ × ↥P₁ => (p.1 : G)) e1
        have e3 : p₂ = z := congrArg (fun p : ↥P₁ × ↥P₁ => (p.2 : G)) e1
        refine Or.inr ⟨?_, ?_⟩
        · rw [e2, h.z_sq]
        · rw [e3, h.z_sq]
  have hkerc : Nat.card ↥f.ker = 2 := by
    rw [hker, Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hzz2) hzz1
  have h1 : Nat.card (↥P₁ × ↥P₁) = Nat.card ((↥P₁ × ↥P₁) ⧸ f.ker) * Nat.card ↥f.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h2 : Nat.card ((↥P₁ × ↥P₁) ⧸ f.ker) = Nat.card ↥f.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  rw [Nat.card_prod, h.card_P₁, h2, hkerc, hrange] at h1
  have : 2 ^ a * 2 ^ a = 2 ^ (2 * a - 1) * 2 := by
    rw [← pow_add, ← pow_succ]; congr 1; have := h.three_le; omega
  omega

theorem card_S : Nat.card ↥S = 2 ^ (2 * a + 1) := by
  have h1 := Subgroup.relIndex_mul_card (P₁ ⊔ P₂) S
  rw [h.idx, inf_eq_left.2 h.R_le_S, h.card_R] at h1
  have : 2 ^ (2 * a + 1) = 4 * 2 ^ (2 * a - 1) := by
    rw [show 2 * a + 1 = (2 * a - 1) + 2 by have := h.three_le; omega, pow_add]; norm_num; ring
  omega

theorem exists_std4 : ∃ (c d : G) (M : ℕ), c ∈ P₁ ∧ d ∈ P₁ ∧ 1 ≤ M ∧ 2 * (2 * M) = 2 ^ (a - 1) ∧
    Rel4 c d (t * c * t⁻¹) (t * d * t⁻¹) t w M ∧ z = c ^ (2 * M) ∧
    (∀ x ∈ P₁, ∃ k : ℕ, x = c ^ k ∨ x = c ^ k * d) ∧ w * c * w⁻¹ = c⁻¹ ∧
    w * d * w⁻¹ = z * c⁻¹ * d := by
  have hzc : ∀ x ∈ P₁, x * z = z * x := fun x hx => h.z_cent x (h.P₁_le hx)
  obtain ⟨c, d, hcP, hdP, hqg, hspan, hz, hwc, hwd⟩ := exists_adapted_gens h.P₁_quat h.z_sq
    h.z_ne_one h.z_mem₁ hzc (fun x hx hx2 hx1 => h.unique_invol hx hx2 hx1)
    (h.z_cent w h.w_mem).symm h.w_inv (fun hw => h.w_not (mem_sup_left hw)) h.w_norm h.w_dih
  have ha3 := h.three_le
  have hM : 2 * 2 ^ (a - 3) = 2 ^ (a - 2) := by
    rw [← pow_succ']; congr 1; omega
  have hqg' : QG c d (2 * 2 ^ (a - 3)) := by rw [hM]; exact hqg
  have hM1 : 1 ≤ 2 ^ (a - 3) := Nat.one_le_two_pow
  obtain ⟨hz', hrel⟩ := h.toPsp4.rel_of_gens hcP hdP hM1 hqg' hspan
  refine ⟨c, d, 2 ^ (a - 3), hcP, hdP, hM1, ?_, ?_, hz', hspan, hwc, hwd⟩
  · rw [show 2 * (2 * 2 ^ (a - 3)) = 2 * 2 ^ (a - 2) by rw [hM], ← pow_succ']
    congr 1; omega
  · have hwd' : w * d * w⁻¹ = c ^ (2 * 2 ^ (a - 3)) * c⁻¹ * d := by rw [← hz']; exact hwd
    exact ⟨hrel, h.w_inv, h.tw_comm, hwc, hwd'⟩

theorem eval_four {c d u e y : G} {M : ℕ} (hc : c ∈ P₁) (hd : d ∈ P₁) (hz : z = c ^ (2 * M))
    (hrel : Rel4 c d (t * c * t⁻¹) (t * d * t⁻¹) t w M) (hwc : w * c * w⁻¹ = c⁻¹)
    (hwd : w * d * w⁻¹ = z * c⁻¹ * d) (hu : u = c ^ M * (t * c * t⁻¹) ^ M) (he : e = t * u)
    (hy : y = c * (w * (d * (t * d * t⁻¹)))) :
    e ∈ XcL (P₁ ⊔ P₂) z t w ∧ u * e ∈ ZcL (P₁ ⊔ P₂) z t w ∧ e * y ∈ XcL (P₁ ⊔ P₂) z t w ∧
      u * (e * y) ∈ ZcL (P₁ ⊔ P₂) z t w := by
  have hd0 := h.toPsp4
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : G, c₀ = c ^ M := ⟨_, rfl⟩
  have hc0 : c₀ ∈ P₁ := by rw [hc₀]; exact pow_mem hc M
  have hωd : w * d * w⁻¹ ∈ P₁ := h.w_norm d hd
  have hzc : z * c = c * z := h.z_comm (h.P₁_le hc)
  have hzd : z * d = d * z := h.z_comm (h.P₁_le hd)
  have hzc0 : z * c₀ = c₀ * z := h.z_comm (h.P₁_le hc0)
  have hωc0 : w * c₀ * w⁻¹ = c₀⁻¹ := by rw [hc₀, ← conj_pow, hwc, inv_pow]
  have hc0sq : c₀ * c₀ = z := by rw [hc₀, ← pow_add, ← two_mul, ← hz]
  have hc0inv : c₀⁻¹ = z * c₀ := by rw [hc₀, hrel.aM_inv, ← hz]
  have hdd : d * d = z := by rw [hz]; exact hrel.toRel.qg.bsq
  have hdinv : d⁻¹ = z * d := by
    calc d⁻¹ = (d * d)⁻¹ * d := by group
      _ = z * d := by rw [hdd, h.z_inv]
  have hdc0 : d * c₀ = c₀⁻¹ * d := by
    have := hrel.toRel.qg.b_conj M
    rw [← hc₀] at this
    exact mul_inv_eq_iff_eq_mul.1 this
  have hωωd : w * (w * d * w⁻¹) * w⁻¹ = d := h.ω_ω d
  have hu_rr : u = rr t c₀ c₀ := by
    rw [hu, hc₀]; unfold rr; rw [conj_pow]
  have htu : t * rr t c₀ c₀ = rr t c₀ c₀ * t := hd0.rr_mul_t hc0 hc0
  have he_rr : e = rr t c₀ c₀ * t := by rw [he, hu_rr, htu]
  have hX1 : e ∈ XcL (P₁ ⊔ P₂) z t w := by
    rw [he_rr]; exact (h.rrt_mem_XcL_iff hc0 hc0).2 hc0sq
  have hZ1 : u * e ∈ ZcL (P₁ ⊔ P₂) z t w := by
    have : u * e = rr t z z * t := by
      rw [he_rr, hu_rr, ← mul_assoc, hd0.rr_mul hc0 hc0, hc0sq]
    rw [this]
    exact (h.rrt_mem_ZcL_iff h.z_mem₁ h.z_mem₁).2 h.z_sq
  have hwrr : w * rr t d d = rr t (w * d * w⁻¹) (w * d * w⁻¹) * w := by
    have := h.w_rr d d
    calc w * rr t d d = (w * rr t d d * w⁻¹) * w := by group
      _ = rr t (w * d * w⁻¹) (w * d * w⁻¹) * w := by rw [this]
  have hy_rr : y = rr t (c * (w * d * w⁻¹)) (w * d * w⁻¹) * w := by
    rw [hy]
    have : d * (t * d * t⁻¹) = rr t d d := rfl
    rw [this, hwrr, ← mul_assoc, mul_rr_left]
  have hP : c * (w * d * w⁻¹) ∈ P₁ := mul_mem hc hωd
  have hey : e * y = rr t (c₀ * (w * d * w⁻¹)) (c₀ * (c * (w * d * w⁻¹))) * (t * w) := by
    rw [he, hu_rr, hy_rr]
    calc t * rr t c₀ c₀ * (rr t (c * (w * d * w⁻¹)) (w * d * w⁻¹) * w)
        = t * (rr t c₀ c₀ * rr t (c * (w * d * w⁻¹)) (w * d * w⁻¹)) * w := by simp only [mul_assoc]
      _ = t * rr t (c₀ * (c * (w * d * w⁻¹))) (c₀ * (w * d * w⁻¹)) * w := by
          rw [hd0.rr_mul hc0 hP]
      _ = (t * rr t (c₀ * (c * (w * d * w⁻¹))) (c₀ * (w * d * w⁻¹)) * t⁻¹) * (t * w) := by group
      _ = rr t (c₀ * (w * d * w⁻¹)) (c₀ * (c * (w * d * w⁻¹))) * (t * w) := by
          rw [hd0.σ_rr (mul_mem hc0 hP) (mul_mem hc0 hωd)]
  have hp1 : c₀ * (w * d * w⁻¹) ∈ P₁ := mul_mem hc0 hωd
  have hq1 : c₀ * (c * (w * d * w⁻¹)) ∈ P₁ := mul_mem hc0 hP
  have hωp1 : w * (c₀ * (w * d * w⁻¹)) * w⁻¹ = c₀⁻¹ * d := by
    rw [conj_mul' w, hωc0, hωωd]
  have hq1_eq : c₀ * (c * (w * d * w⁻¹)) = c₀ * z * d := by
    rw [hwd]
    calc c₀ * (c * (z * c⁻¹ * d)) = c₀ * ((c * z) * c⁻¹ * d) := by simp only [mul_assoc]
      _ = c₀ * ((z * c) * c⁻¹ * d) := by rw [hzc]
      _ = c₀ * z * d := by group
  have hX2 : e * y ∈ XcL (P₁ ⊔ P₂) z t w := by
    rw [hey]
    refine (h.rrtw_mem_XcL_iff hp1 hq1).2 ?_
    rw [hωp1, hq1_eq]
    calc c₀ * z * d = z * c₀ * d := by rw [← hzc0]
      _ = c₀⁻¹ * d := by rw [hc0inv]
      _ = d * c₀ := hdc0.symm
      _ = (z * z) * (d * c₀) := by rw [h.z_sq, one_mul]
      _ = z * ((z * d) * c₀) := by simp only [mul_assoc]
      _ = z * (d⁻¹ * c₀) := by rw [hdinv]
      _ = z * (c₀⁻¹ * d)⁻¹ := by rw [mul_inv_rev, inv_inv]
  have huey : u * (e * y) =
      rr t (c₀ * (c₀ * (w * d * w⁻¹))) (c₀ * (c₀ * (c * (w * d * w⁻¹)))) * (t * w) := by
    rw [hey, hu_rr, ← mul_assoc, hd0.rr_mul hc0 hp1]
  have hp2 : c₀ * (c₀ * (w * d * w⁻¹)) = c⁻¹ * d := by
    rw [← mul_assoc, hc0sq, hwd]
    calc z * (z * c⁻¹ * d) = (z * z) * c⁻¹ * d := by simp only [mul_assoc]
      _ = c⁻¹ * d := by rw [h.z_sq, one_mul]
  have hq2 : c₀ * (c₀ * (c * (w * d * w⁻¹))) = d := by
    rw [← mul_assoc, hc0sq, hwd]
    calc z * (c * (z * c⁻¹ * d)) = z * ((c * z) * c⁻¹ * d) := by simp only [mul_assoc]
      _ = z * ((z * c) * c⁻¹ * d) := by rw [hzc]
      _ = (z * z) * d := by group
      _ = d := by rw [h.z_sq, one_mul]
  have hωp2 : w * (c⁻¹ * d) * w⁻¹ = z * d := by
    rw [conj_mul' w, show w * c⁻¹ * w⁻¹ = c by rw [conj_inv' w, hwc, inv_inv], hwd]
    calc c * (z * c⁻¹ * d) = (c * z) * c⁻¹ * d := by simp only [mul_assoc]
      _ = (z * c) * c⁻¹ * d := by rw [hzc]
      _ = z * d := by group
  have hinv2 : (z * d)⁻¹ = d := by
    calc (z * d)⁻¹ = d⁻¹ * z⁻¹ := by rw [mul_inv_rev]
      _ = (z * d) * z := by rw [hdinv, h.z_inv]
      _ = z * (d * z) := by rw [mul_assoc]
      _ = z * (z * d) := by rw [hzd]
      _ = d := by rw [← mul_assoc, h.z_sq, one_mul]
  have hZ2 : u * (e * y) ∈ ZcL (P₁ ⊔ P₂) z t w := by
    rw [huey]
    have hp2m : c₀ * (c₀ * (w * d * w⁻¹)) ∈ P₁ := mul_mem hc0 hp1
    have hq2m : c₀ * (c₀ * (c * (w * d * w⁻¹))) ∈ P₁ := mul_mem hc0 (mul_mem hc0 hP)
    refine (h.rrtw_mem_ZcL_iff hp2m hq2m).2 ?_
    rw [hp2, hq2, hωp2, hinv2]
  exact ⟨hX1, hZ1, hX2, hZ2⟩

omit [Finite G] in
theorem relIndex_cent_two {u g : G} (hn : ∀ s ∈ S, s * u * s⁻¹ = u ∨ s * u * s⁻¹ = u * z)
    (hgS : g ∈ S) (hg : g * u * g⁻¹ = u * z) :
    (S ⊓ centralizer ({u} : Set G)).relIndex S = 2 := by
  have hT : ∀ x ∈ S, x ∈ S ⊓ centralizer ({u} : Set G) ↔ x * u * x⁻¹ = u := by
    intro x hx
    rw [Subgroup.mem_inf, mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
    simp only [hx, true_and]
  have hzconj : ∀ x ∈ S, x * z * x⁻¹ = z := by
    intro x hx
    rw [h.z_cent x hx, mul_assoc, mul_inv_cancel, mul_one]
  have hzne : u * z ≠ u := by
    intro e
    apply h.z_ne_one
    calc z = u⁻¹ * (u * z) := by group
      _ = 1 := by rw [e]; group
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨g, hgS, fun b hb => ?_⟩
  have hbg : (b * g) * u * (b * g)⁻¹ = (b * u * b⁻¹) * z := by
    calc (b * g) * u * (b * g)⁻¹ = b * (g * u * g⁻¹) * b⁻¹ := by group
      _ = b * (u * z) * b⁻¹ := by rw [hg]
      _ = (b * u * b⁻¹) * (b * z * b⁻¹) := by group
      _ = (b * u * b⁻¹) * z := by rw [hzconj b hb]
  rcases hn b hb with h1 | h1
  · refine Or.inr ⟨(hT b hb).2 h1, fun hbg' => ?_⟩
    have := (hT (b * g) (mul_mem hb hgS)).1 hbg'
    rw [hbg, h1] at this
    exact hzne this
  · refine Or.inl ⟨?_, fun hb' => ?_⟩
    · rw [hT (b * g) (mul_mem hb hgS), hbg, h1]
      calc u * z * z = u * (z * z) := by rw [mul_assoc]
        _ = u := by rw [h.z_sq, mul_one]
    · have := (hT b hb).1 hb'
      rw [h1] at this
      exact hzne this

theorem u0_normal {c d : G} {M : ℕ} (hc : c ∈ P₁) (hz : z = c ^ (2 * M))
    (hrel : Rel4 c d (t * c * t⁻¹) (t * d * t⁻¹) t w M)
    (hspan : ∀ x ∈ P₁, ∃ k : ℕ, x = c ^ k ∨ x = c ^ k * d) {u : G}
    (hu : u = c ^ M * (t * c * t⁻¹) ^ M) :
    ∀ s ∈ S, s * u * s⁻¹ = u ∨ s * u * s⁻¹ = u * z := by
  have hd0 := h.toPsp4
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : G, c₀ = c ^ M := ⟨_, rfl⟩
  have hc0 : c₀ ∈ P₁ := by rw [hc₀]; exact pow_mem hc M
  have hu_rr : u = rr t c₀ c₀ := by rw [hu, hc₀]; unfold rr; rw [conj_pow]
  have hc0inv : c₀⁻¹ = z * c₀ := by rw [hc₀, hrel.aM_inv, ← hz]
  have hconj_c0 : ∀ p ∈ P₁, p * c₀ * p⁻¹ = c₀ ∨ p * c₀ * p⁻¹ = z * c₀ := by
    intro p hp
    obtain ⟨k, hk | hk⟩ := hspan p hp
    · left
      rw [hk, hc₀, (Commute.pow_pow_self c k M).eq]; group
    · right
      have hdc : d * c₀ * d⁻¹ = c₀⁻¹ := by
        have := hrel.toRel.qg.b_conj M
        rw [← hc₀] at this
        exact this
      have hcomm : Commute (c ^ k) c₀⁻¹ := by
        rw [hc₀]; exact (Commute.pow_pow_self c k M).inv_right
      rw [hk]
      calc c ^ k * d * c₀ * (c ^ k * d)⁻¹ = c ^ k * (d * c₀ * d⁻¹) * (c ^ k)⁻¹ := by group
        _ = c ^ k * c₀⁻¹ * (c ^ k)⁻¹ := by rw [hdc]
        _ = c₀⁻¹ := by rw [hcomm.eq]; group
        _ = z * c₀ := hc0inv
  have hzu : ∀ g ∈ S, z * g = g * z := fun g hg => h.z_comm hg
  have hρ : ∀ ρ ∈ P₁ ⊔ P₂, ρ * u * ρ⁻¹ = u ∨ ρ * u * ρ⁻¹ = u * z := by
    intro ρ hρ
    obtain ⟨p, hp, q, hq, rfl⟩ := hd0.mem_R_iff.1 hρ
    have hu_S : rr t c₀ c₀ ∈ S := h.rr_mem_S hc0 hc0
    rw [hu_rr, hd0.conj_rr hp hq hc0 hc0]
    have e1 : rr t c₀ (z * c₀) = rr t c₀ c₀ * z := by
      rw [← hd0.z_mul_rr_right hc0, hzu _ hu_S]
    have e2 : rr t (z * c₀) c₀ = rr t c₀ c₀ * z := by
      rw [← Data.z_mul_rr_left, hzu _ hu_S]
    have e3 : rr t (z * c₀) (z * c₀) = rr t c₀ c₀ := by
      rw [← Data.z_mul_rr_left, ← hd0.z_mul_rr_right hc0, ← mul_assoc, h.z_sq, one_mul]
    rcases hconj_c0 p hp with h1 | h1 <;> rcases hconj_c0 q hq with h2 | h2 <;> rw [h1, h2]
    · exact Or.inl rfl
    · exact Or.inr e1
    · exact Or.inr e2
    · exact Or.inl e3
  have ht : t * u = u * t := by rw [hu_rr]; exact hd0.rr_mul_t hc0 hc0
  have hw : w * u = u * w := by
    have := hrel.u_comm_w
    rw [← hu] at this
    exact this.symm
  intro s hs
  obtain ⟨ρ, hρR, τ, hτ, rfl⟩ := h.S_decomp hs
  have hτu : τ * u * τ⁻¹ = u := by
    rw [h.V_comm ht hw hτ]; group
  have e : ρ * τ * u * (ρ * τ)⁻¹ = ρ * u * ρ⁻¹ := by
    calc ρ * τ * u * (ρ * τ)⁻¹ = ρ * (τ * u * τ⁻¹) * ρ⁻¹ := by group
      _ = ρ * u * ρ⁻¹ := by rw [hτu]
  rw [e]
  exact hρ ρ hρR

theorem exists_skel :
    ∃ (u τ x₀ y e : G) (n : ℕ),
      Skel (S ⊓ centralizer ({u} : Set G)) z u τ x₀ y e n (ZcL (P₁ ⊔ P₂) z t w)
        (XcL (P₁ ⊔ P₂) z t w) ∧
      u ∈ P₁ ⊔ P₂ ∧ u * u = 1 ∧ u ≠ 1 ∧ u ≠ z ∧
      (∀ s ∈ S, s * u * s⁻¹ = u ∨ s * u * s⁻¹ = u * z) ∧ n = 2 ^ (a - 1) ∧
      (∃ g ∈ S, g * u * g⁻¹ = u * z) := by
  obtain ⟨c, d, M, hc, hd, hM1, hnM, hrel, hz, hspan, hwc, hwd⟩ := h.exists_std4
  have hd0 := h.toPsp4
  obtain ⟨u, hu⟩ : ∃ u : G, u = c ^ M * (t * c * t⁻¹) ^ M := ⟨_, rfl⟩
  obtain ⟨b0, hb0⟩ : ∃ b0 : G, b0 = d * (t * d * t⁻¹) := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : G, τ = w * b0 := ⟨_, rfl⟩
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : G, x₀ = z * b0 * t := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : G, y = c * (w * b0) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : G, e = t * u := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = 2 * (2 * M) := ⟨_, rfl⟩
  have hnA : n = 2 ^ (a - 1) := by rw [hn]; exact hnM
  have hcore : Core4 z u τ x₀ y e n := by
    have := hrel.core
    rw [← hz] at this
    rw [hn, hτ, hx₀, hy, he, hu, hb0]
    exact this
  have hy' : y = c * (w * (d * (t * d * t⁻¹))) := by rw [hy, hb0]
  have hc0 : c ^ M ∈ P₁ := pow_mem hc M
  have hu_rr : u = rr t (c ^ M) (c ^ M) := by rw [hu]; unfold rr; rw [conj_pow]
  have huR : u ∈ P₁ ⊔ P₂ := by rw [hu_rr]; exact hd0.rr_mem_R hc0 hc0
  have huS : u ∈ S := h.R_mem_S huR
  have hbS : b0 ∈ S := by rw [hb0]; exact mul_mem (h.P₁_le hd) (h.P₂_le (h.swap d hd))
  have hcS : c ∈ S := h.P₁_le hc
  have hτS : τ ∈ S := by rw [hτ]; exact mul_mem h.w_mem hbS
  have hx₀S : x₀ ∈ S := by rw [hx₀]; exact mul_mem (mul_mem h.z_mem hbS) h.t_mem
  have hyS : y ∈ S := by rw [hy]; exact mul_mem hcS (mul_mem h.w_mem hbS)
  have heS : e ∈ S := by rw [he]; exact mul_mem h.t_mem huS
  have huτ : u * τ = τ * u := by rw [hu, hτ, hb0]; exact hrel.u_comm_tau
  have hux₀ : u * x₀ = x₀ * u := by rw [hu, hx₀, hb0, hz]; exact hrel.u_comm_x0
  have huy : u * y = y * u := by rw [hu, hy, hb0]; exact hrel.u_comm_y
  have hue : u * e = e * u := by rw [he, hu]; exact hrel.u_comm_e
  have hmem : ∀ g, g ∈ S → u * g = g * u → g ∈ S ⊓ centralizer ({u} : Set G) := fun g hgS hg =>
    Subgroup.mem_inf.2 ⟨hgS, mem_centralizer_singleton_iff.2 hg.symm⟩
  have hD₁le : zpowers τ ⊔ zpowers x₀ ≤ S ⊓ centralizer ({u} : Set G) :=
    sup_le (zpowers_le.2 (hmem τ hτS huτ)) (zpowers_le.2 (hmem x₀ hx₀S hux₀))
  have hD₂le : zpowers y ⊔ zpowers e ≤ S ⊓ centralizer ({u} : Set G) :=
    sup_le (zpowers_le.2 (hmem y hyS huy)) (zpowers_le.2 (hmem e heS hue))
  have hu_sq : u * u = 1 := by rw [hu]; exact hrel.u_sq
  have hu_ne_one : u ≠ 1 := by rw [hu]; exact hrel.u_ne_one
  have hu_ne_z : u ≠ z := by rw [hu, hz]; exact hrel.u_ne_z
  have hnormal := h.u0_normal hc hz hrel hspan hu
  have hg : d * u * d⁻¹ = u * z := by rw [hu, hz]; exact hrel.b_u
  have hidx := h.relIndex_cent_two hnormal (h.P₁_le hd) hg
  have hnpos : 0 < n := by rw [hn]; omega
  have hcardT : Nat.card ↥(S ⊓ centralizer ({u} : Set G)) = 2 ^ (2 * a) := by
    have h1 := Subgroup.relIndex_mul_card (S ⊓ centralizer ({u} : Set G)) S
    rw [hidx, inf_eq_left.2 inf_le_left, h.card_S] at h1
    have : 2 ^ (2 * a + 1) = 2 * 2 ^ (2 * a) := by rw [pow_succ]; ring
    omega
  have hcomm : ∀ g ∈ zpowers τ ⊔ zpowers x₀, ∀ g' ∈ zpowers y ⊔ zpowers e, g * g' = g' * g :=
    commute_sup_sup hcore.τ_y hcore.τ_e hcore.x₀_y hcore.x₀_e
  have hcardD : Nat.card ↥((zpowers τ ⊔ zpowers x₀) ⊔ (zpowers y ⊔ zpowers e)) = 2 ^ (2 * a) := by
    have : NeZero n := ⟨hnpos.ne'⟩
    rw [card_sup_of_commute hcomm hcore.inter,
      card_dihedral_sup n τ x₀ hcore.τ_ord hcore.x₀_sq hcore.x₀_τ hcore.x₀_not,
      card_dihedral_sup n y e hcore.y_ord hcore.e_sq hcore.e_y hcore.e_not, hnA]
    have ha3 := h.three_le
    rw [show 2 * a = (2 + (a - 1)) + (a - 1) by omega, pow_add, pow_add]; ring
  have hTeq : (zpowers τ ⊔ zpowers x₀) ⊔ (zpowers y ⊔ zpowers e) = S ⊓ centralizer ({u} : Set G) :=
    Subgroup.eq_of_le_of_card_ge (sup_le hD₁le hD₂le) (by rw [hcardT, hcardD])
  have hX := h.eval_four hc hd hz hrel hwc hwd hu he hy'
  refine ⟨u, τ, x₀, y, e, n, ?_, huR, hu_sq, hu_ne_one, hu_ne_z, hnormal, hnA, ⟨d, h.P₁_le hd, hg⟩⟩
  exact
    { core := hcore
      D₁_le := hD₁le
      D₂_le := hD₂le
      T_le := hTeq.ge
      u_cent := fun g hg => (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hg).2).symm
      z_cent := fun g hg => h.z_comm (Subgroup.mem_inf.1 hg).1
      Z_conj := fun g hg x hx => h.ZcL_conj (Subgroup.mem_inf.1 hg).1 hx
      X_conj := fun g hg x hx => h.XcL_conj (Subgroup.mem_inf.1 hg).1 hx
      part := fun x hx hx2 hx1 => h.partition x (Subgroup.mem_inf.1 hx).1 hx2 hx1
      one_Z := h.one_not_mem_ZcL
      z_Z := Or.inl (Or.inl (Or.inl rfl))
      u_X := (h.mem_XcL_R huR).2 ⟨hu_sq, hu_ne_one, hu_ne_z⟩
      uz_X := by
        refine (h.mem_XcL_R (mul_mem huR h.z_mem_R)).2 ⟨?_, ?_, ?_⟩
        · calc u * z * (u * z) = u * (z * u) * z := by simp only [mul_assoc]
            _ = u * (u * z) * z := by rw [h.z_comm huS]
            _ = (u * u) * (z * z) := by simp only [mul_assoc]
            _ = 1 := by rw [hu_sq, h.z_sq, mul_one]
        · intro e1
          apply hu_ne_z
          calc u = (u * z) * z⁻¹ := by group
            _ = z := by rw [e1, one_mul, h.z_inv]
        · intro e1
          apply hu_ne_one
          calc u = (u * z) * z⁻¹ := by group
            _ = 1 := by rw [e1, mul_inv_cancel]
      e_X := hX.1
      ue_Z := hX.2.1
      ey_X := hX.2.2.1
      uey_Z := hX.2.2.2 }

end DataL4

namespace Skel

variable [Finite G] {T : Subgroup G} {z u τ x₀ y e : G} {n : ℕ} {Z X : Set G}
  (hS : Skel T z u τ x₀ y e n Z X)

include hS

theorem center_eq : (center ↥T).map T.subtype = zpowers z ⊔ zpowers u := by
  have hzT := hS.z_mem_T
  have huT := hS.u_mem_T
  have hzm : z ∈ zpowers z ⊔ zpowers u := mem_sup_left (mem_zpowers z)
  have hum : u ∈ zpowers z ⊔ zpowers u := mem_sup_right (mem_zpowers u)
  apply center_map_eq_of_forall
  · exact sup_le (zpowers_le.2 hzT) (zpowers_le.2 huT)
  · intro g hg hcent
    obtain ⟨a', ha', b', hb', rfl⟩ := hS.T_decomp hg
    have ha_cent : ∀ d ∈ zpowers τ ⊔ zpowers x₀, d * a' = a' * d := by
      intro d hd
      have hdT := hS.D₁_le hd
      have h1 := hcent d hdT
      have h2 : d * b' = b' * d := hS.comm_D12 d hd b' hb'
      have : d * a' * b' = a' * d * b' := by
        calc d * a' * b' = d * (a' * b') := by rw [mul_assoc]
          _ = a' * b' * d := h1
          _ = a' * (b' * d) := by rw [mul_assoc]
          _ = a' * (d * b') := by rw [h2]
          _ = a' * d * b' := by rw [mul_assoc]
      exact mul_right_cancel this
    have hb_cent : ∀ d ∈ zpowers y ⊔ zpowers e, d * b' = b' * d := by
      intro d hd
      have hdT := hS.D₂_le hd
      have h1 := hcent d hdT
      have h2 : a' * d = d * a' := hS.comm_D12 a' ha' d hd
      have : a' * (d * b') = a' * (b' * d) := by
        calc a' * (d * b') = (a' * d) * b' := by rw [mul_assoc]
          _ = (d * a') * b' := by rw [h2]
          _ = d * (a' * b') := by rw [mul_assoc]
          _ = (a' * b') * d := h1
          _ = a' * (b' * d) := by rw [mul_assoc]
      exact mul_left_cancel this
    have ha1 := (hS.dih₁.central_iff hS.half_ge ha').1 (fun d hd => ha_cent d hd)
    have hb1 := (hS.dih₂.central_iff hS.half_ge hb').1 (fun d hd => hb_cent d hd)
    have hu_eq : τ ^ (n / 2) = u := hS.core.u_eq.symm
    have huz_eq : y ^ (n / 2) = u * z := hS.core.uz_eq.symm
    have huz : u * z ∈ zpowers z ⊔ zpowers u := mul_mem hum hzm
    rcases ha1 with h1 | h1 <;> rcases hb1 with h2 | h2
    · rw [h1, h2, one_mul]; exact one_mem _
    · rw [h1, h2, one_mul, huz_eq]; exact huz
    · rw [h1, h2, mul_one, hu_eq]; exact hum
    · rw [h1, h2, hu_eq, huz_eq, ← mul_assoc, hS.u_sq, one_mul]; exact hzm
  · intro g hg d hd
    have hle : zpowers z ⊔ zpowers u ≤ centralizer ({d} : Set G) := by
      refine sup_le ?_ ?_ <;> rw [zpowers_le, mem_centralizer_singleton_iff]
      · exact hS.z_cent d hd
      · exact hS.u_cent d hd
    exact (mem_centralizer_singleton_iff.1 (hle hg)).symm

end Skel

theorem l4_exists_std [Finite G] (h : DataL4 S P₁ P₂ z t w a) :
    ∃ u : G, u ∈ P₁ ⊔ P₂ ∧ u * u = 1 ∧ u ≠ 1 ∧ u ≠ z ∧
      (∀ s ∈ S, s * u * s⁻¹ = u ∨ s * u * s⁻¹ = u * z) ∧
      L4Std S z u a (ZcL (P₁ ⊔ P₂) z t w) (XcL (P₁ ⊔ P₂) z t w) := by
  obtain ⟨u, τ, x₀, y, e, n, hS, huR, hu_sq, hu1, huz, hnormal, hn, g, hgS, hg⟩ := h.exists_skel
  refine ⟨u, huR, hu_sq, hu1, huz, hnormal, ?_⟩
  exact
    { u_X := hS.u_X
      uz_X := hS.uz_X
      index := h.relIndex_cent_two hnormal hgS hg
      center := hS.center_eq
      decomp := fun w0 hw0T hw0sq hw0Z hw0z huw0Z hcard U hU_le _ hU_card hU_dih hU_inf hU_cls =>
        hS.decomp h.three_le hn hw0T hw0sq hw0Z hw0z huw0Z hcard hU_le hU_card hU_dih hU_inf hU_cls }

end CFSG.GH74.GLS.Stage2.Local.P27.L4
