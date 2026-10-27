module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenRep

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson

namespace Thompson

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

@[expose] def muStab (Ω : Set (Subgroup G)) (W : Subgroup G) (e : G) : Subgroup ↥(muGroup Ω W) where
  carrier := {q | ∃ n ∈ Subgroup.normalizer (W : Set G),
    (q : NQuot (W ⊔ OCW W)) = piG W n ∧ n * e * n⁻¹ = e}
  one_mem' := ⟨1, Subgroup.one_mem _, by rw [Subgroup.coe_one, piG_one], by group⟩
  mul_mem' := by
    rintro q q' ⟨n, hn, hqn, hne⟩ ⟨n', hn', hq'n', hn'e⟩
    refine ⟨n * n', Subgroup.mul_mem _ hn hn', ?_, ?_⟩
    · rw [Subgroup.coe_mul, hqn, hq'n', piG_mul hn hn']
    · calc n * n' * e * (n * n')⁻¹ = n * (n' * e * n'⁻¹) * n⁻¹ := by group
        _ = e := by rw [hn'e, hne]
  inv_mem' := by
    rintro q ⟨n, hn, hqn, hne⟩
    refine ⟨n⁻¹, Subgroup.inv_mem _ hn, ?_, ?_⟩
    · rw [Subgroup.coe_inv, hqn, piG_inv hn]
    · have h1 : n * e = e * n := by
        rw [mul_inv_eq_iff_eq_mul] at hne
        exact hne
      calc n⁻¹ * e * n⁻¹⁻¹ = n⁻¹ * (e * n) := by group
        _ = n⁻¹ * (n * e) := by rw [h1]
        _ = e := by group

omit [Finite G] in
theorem exists_rep_of_mem_muDelta {q : ↥(muGroup Ω W)} (hq : q ∈ muDelta Ω W) :
    ∃ ρ : Rep Ω W, ρ.img = (q : NQuot (W ⊔ OCW W)) := by
  obtain ⟨R, hR, r, hr, hrW, hxr⟩ := hq
  obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1
  exact ⟨⟨K, R, r, hK, hR, hRK, hr, hrW⟩, hxr.symm⟩

omit [Finite G] in
theorem sq_eq_involution_of_orderOf_four {K : Subgroup G} {z y : G} (hz : IsUniqueInvolution K z)
    (hyK : y ∈ K) (hy4 : orderOf y = 4) : y * y = z := by
  have hy4' : y ^ 4 = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy4] at this
  have hsq : (y * y) * (y * y) = 1 := by
    rw [← hy4']
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have hne : y * y ≠ 1 := by
    intro h
    have h2 : y ^ 2 = 1 := by rw [pow_two]; exact h
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hy4] at this
    omega
  rcases hz.unique (y * y) (K.mul_mem hyK hyK) hsq with h | h
  · exact absurd h hne
  · exact h

namespace Ctx

variable (c : Ctx p f Ω W)
include c

theorem mem_muStab_iff {e : G} (he : e ∈ W) {R : Subgroup G} (hR : R ∈ DSet Ω W) {r : G}
    (hr : r ∈ R) {q : ↥(muGroup Ω W)} (hq : (q : NQuot (W ⊔ OCW W)) = piG W r) :
    q ∈ muStab Ω W e ↔ r * e * r⁻¹ = e := by
  constructor
  · rintro ⟨n, hn, hqn, hne⟩
    have h : piG W r = piG W n := hq.symm.trans hqn
    rw [← conj_eq_of_piG_eq c.hp c.hq c.hΩ c.hW (hR.2 hr) hn h he]
    exact hne
  · intro h
    exact ⟨r, hR.2 hr, hq, h⟩

theorem muDeltaCent_eq_inter {e : G} (he : e ∈ W) :
    muDeltaCent Ω W e = muDelta Ω W ∩ (muStab Ω W e : Set ↥(muGroup Ω W)) := by
  ext q
  constructor
  · rintro ⟨T, ⟨hT, hTe⟩, t, ht, htW, hq⟩
    refine ⟨⟨T, hT, t, ht, htW, hq⟩, (c.mem_muStab_iff he hT ht hq).mpr ?_⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp (hTe ht)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  · rintro ⟨⟨R, hR, r, hr, hrW, hqr⟩, hqs⟩
    have hre := (c.mem_muStab_iff he hR hr hqr).mp hqs
    have hrc : r * e = e * r := by
      rw [mul_inv_eq_iff_eq_mul] at hre
      exact hre
    exact ⟨R, ⟨hR, le_centralizer_of_mem c.hp c.hq c.hΩ c.hW hR hr hrW he hrc⟩, r, hr, hrW, hqr⟩

theorem comm_sq (ρ σ : Rep Ω W) (hne : ρ.K ≠ σ.K) (hnot : σ.K ∉ omegaNbr Ω ρ.K) {y z j : G}
    (hy : y ∈ σ.K ⊓ W) (hz : IsUniqueInvolution ρ.K z) (hj : IsUniqueInvolution σ.K j)
    (hy2 : y * y = j) :
    (ρ.r * y * ρ.r⁻¹ * y⁻¹) * (ρ.r * y * ρ.r⁻¹ * y⁻¹) = z := by
  have hc := c.comm_mem ρ σ hne hy
  set cc := ρ.r * y * ρ.r⁻¹ * y⁻¹ with hcc
  have hconj : ρ.r * y * ρ.r⁻¹ = cc * y := by rw [hcc]; group
  have h1 : (ρ.r * y * ρ.r⁻¹) * (ρ.r * y * ρ.r⁻¹) = z * j := by
    calc (ρ.r * y * ρ.r⁻¹) * (ρ.r * y * ρ.r⁻¹) = ρ.r * (y * y) * ρ.r⁻¹ := by group
      _ = ρ.r * j * ρ.r⁻¹ := by rw [hy2]
      _ = z * j := c.conj_involution ρ σ hne hnot hz hj
  have hab : cc * y = y * cc := c.comm_W cc hc.2 y hy.2
  have h2 : (cc * y) * (cc * y) = cc * cc * (y * y) := by
    calc (cc * y) * (cc * y) = cc * (y * cc) * y := by simp only [mul_assoc]
      _ = cc * (cc * y) * y := by rw [← hab]
      _ = cc * cc * (y * y) := by simp only [mul_assoc]
  rw [hconj, h2, hy2] at h1
  exact mul_right_cancel h1

theorem stab_dichotomy (ρ ρ₁ ρ₂ : Rep Ω W) {w v z z₁ z₂ : G} (hne₁ : ρ.K ≠ ρ₁.K)
    (hne₂ : ρ.K ≠ ρ₂.K) (hnot₁ : ρ₁.K ∉ omegaNbr Ω ρ.K) (hnot₂ : ρ₂.K ∉ omegaNbr Ω ρ.K)
    (hw : w ∈ ρ₁.K ⊓ W) (hv : v ∈ ρ₂.K ⊓ W) (hz : IsUniqueInvolution ρ.K z)
    (hz₁ : IsUniqueInvolution ρ₁.K z₁) (hz₂ : IsUniqueInvolution ρ₂.K z₂) (hw2 : w * w = z₁)
    (hv2 : v * v = z₂) :
    ρ.r * (w * v) * ρ.r⁻¹ = w * v ∨ ρ.r * (w⁻¹ * v) * ρ.r⁻¹ = w⁻¹ * v := by
  have hcw := c.comm_mem ρ ρ₁ hne₁ hw
  have hcv := c.comm_mem ρ ρ₂ hne₂ hv
  have hsw := c.comm_sq ρ ρ₁ hne₁ hnot₁ hw hz hz₁ hw2
  have hsv := c.comm_sq ρ ρ₂ hne₂ hnot₂ hv hz hz₂ hv2
  have ew : ρ.r * w * ρ.r⁻¹ = (ρ.r * w * ρ.r⁻¹ * w⁻¹) * w := by group
  have ev : ρ.r * v * ρ.r⁻¹ = (ρ.r * v * ρ.r⁻¹ * v⁻¹) * v := by group
  have hrw : ρ.r * (w * v) * ρ.r⁻¹ = (ρ.r * w * ρ.r⁻¹) * (ρ.r * v * ρ.r⁻¹) := by group
  have hrw' : ρ.r * (w⁻¹ * v) * ρ.r⁻¹ = (ρ.r * w * ρ.r⁻¹)⁻¹ * (ρ.r * v * ρ.r⁻¹) := by group
  generalize ρ.r * w * ρ.r⁻¹ * w⁻¹ = cw at hcw hsw ew
  generalize ρ.r * v * ρ.r⁻¹ * v⁻¹ = cv at hcv hsv ev
  rw [ew, ev] at hrw hrw'
  rw [hrw, hrw']
  have hab := c.comm_W
  have h1 : cv * cw⁻¹ ∈ ρ.K := ρ.K.mul_mem hcv.1 (ρ.K.inv_mem hcw.1)
  have hcvw : cv * cw = cw * cv := hab cv hcv.2 cw hcw.2
  have hcc : cw⁻¹ * cv = cv * cw⁻¹ := (Commute.inv_left (show Commute cw cv from hcvw.symm)).eq
  have h2 : (cv * cw⁻¹) * (cv * cw⁻¹) = 1 := by
    calc (cv * cw⁻¹) * (cv * cw⁻¹) = cv * (cw⁻¹ * cv) * cw⁻¹ := by simp only [mul_assoc]
      _ = cv * (cv * cw⁻¹) * cw⁻¹ := by rw [hcc]
      _ = (cv * cv) * (cw * cw)⁻¹ := by rw [mul_inv_rev]; simp only [mul_assoc]
      _ = 1 := by rw [hsv, hsw, mul_inv_cancel]
  rcases hz.unique _ h1 h2 with h3 | h3
  ·
    right
    have hcc' : cv = cw := mul_inv_eq_one.mp h3
    rw [hcc']
    calc (cw * w)⁻¹ * (cw * v) = w⁻¹ * cw⁻¹ * (cw * v) := by rw [mul_inv_rev]
      _ = w⁻¹ * v := by group
  ·
    left
    have hcc' : cv * cw = 1 := by
      have e1 : cv = z * cw := by rw [← h3]; group
      rw [e1]
      calc z * cw * cw = z * (cw * cw) := by simp only [mul_assoc]
        _ = z * z := by rw [hsw]
        _ = 1 := hz.sq
    have hwv : w * (cv * v) = cv * (w * v) := by
      have := hab w hw.2 cv hcv.2
      calc w * (cv * v) = (w * cv) * v := by simp only [mul_assoc]
        _ = (cv * w) * v := by rw [this]
        _ = cv * (w * v) := by simp only [mul_assoc]
    calc cw * w * (cv * v) = cw * (w * (cv * v)) := by simp only [mul_assoc]
      _ = cw * (cv * (w * v)) := by rw [hwv]
      _ = (cw * cv) * (w * v) := by simp only [mul_assoc]
      _ = w * v := by rw [← hcvw, hcc', one_mul]

end Ctx

end Thompson

end CFSG.ClassicalInvolution.Asc77
