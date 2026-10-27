module

public import CFSG.ClassicalInvolution.Asc77.AscT3VBase
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscT3CLate10B

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}


theorem Std20.v_no_norm_four (d : Std20 p f K K' J S R R' W V z t) {σ ξ : G}
    (hσ : σ ∈ (S : Subgroup G)) (hσK : conjSub σ K = K') (hξW : ξ ∈ W) (hξ2 : ξ * ξ ≠ 1)
    (hξ4 : (ξ * ξ) * (ξ * ξ) = 1) (hσξ : σ * ξ * σ⁻¹ = ξ ∨ σ * ξ * σ⁻¹ = ξ⁻¹) : False := by
  obtain ⟨m, hmN, hme, hL⟩ := d.late_W_four_mem hξW hξ2 hξ4
  have ha₀' : ξ * ξ = z ∨ ξ * ξ = t ∨ ξ * ξ = z * t := by
    rcases d.late_inv_W _ (W.mul_mem hξW hξW) hξ4 with h | h | h | h
    · exact absurd h hξ2
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hξinv2 : ξ⁻¹ * ξ⁻¹ = ξ * ξ := by
    have h4 : ξ⁻¹ * ξ⁻¹ = (ξ * ξ)⁻¹ := by group
    rw [h4]
    exact inv_eq_of_mul_eq_one_right hξ4
  have hσa : σ * (ξ * ξ) * σ⁻¹ = ξ * ξ := by
    have : σ * (ξ * ξ) * σ⁻¹ = (σ * ξ * σ⁻¹) * (σ * ξ * σ⁻¹) := by group
    rw [this]
    rcases hσξ with h | h
    · rw [h]
    · rw [h, hξinv2]
  have hA₂ : IsPGroup 2 ↥(Subgroup.zpowers ξ) :=
    S.isPGroup'.to_le (Subgroup.zpowers_le.mpr (d.hWS hξW))
  have hA₄ : 4 ≤ Nat.card ↥(Subgroup.zpowers ξ) := by
    rw [Nat.card_zpowers, late_orderOf_four rfl hξ2 hξ4]
  have hnorm : ∀ w ∈ Subgroup.zpowers ξ, σ⁻¹ * w * σ ∈ Subgroup.zpowers ξ := by
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have h1 : σ⁻¹ * ξ * σ = ξ ∨ σ⁻¹ * ξ * σ = ξ⁻¹ := by
      rcases hσξ with h | h
      · left
        have : ξ = σ⁻¹ * (σ * ξ * σ⁻¹) * σ := by group
        rw [h] at this
        exact this.symm
      · right
        have : ξ = σ⁻¹ * (σ * ξ * σ⁻¹) * σ := by group
        rw [h] at this
        have h2 : σ⁻¹ * ξ⁻¹ * σ = ξ := this.symm
        have := congrArg (fun x => x⁻¹) h2
        simpa [mul_assoc] using this
    have hconj : σ⁻¹ * ξ ^ k * σ = (σ⁻¹ * ξ * σ) ^ k := by
      have := conj_zpow (a := σ⁻¹) (b := ξ) (i := k)
      simpa using this.symm
    rw [hconj]
    rcases h1 with h | h
    · rw [h]; exact Subgroup.zpow_mem_zpowers ξ k
    · rw [h]
      exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers ξ)) k
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
    exact Subgroup.zpowers_le.mpr hξL (hnorm w hw)
  exact d.late_swap_not_N_member hσ hσK hσa hme ha₀' hLeq hσL

@[expose] def InZ (z t g : G) : Prop := g = 1 ∨ g = z ∨ g = t ∨ g = z * t

omit [Finite G] [Fact p.Prime] in
theorem inZ_mul {z t g h : G} (hz2 : z * z = 1) (ht2 : t * t = 1) (hzt : z * t = t * z)
    (hg : InZ z t g) (hh : InZ z t h) : InZ z t (g * h) := by
  have e1 : z * (z * t) = t := by rw [← mul_assoc, hz2, one_mul]
  have e2 : t * (z * t) = z := by rw [← mul_assoc, ← hzt, mul_assoc, ht2, mul_one]
  have e3 : (z * t) * z = t := by rw [mul_assoc, ← hzt, ← mul_assoc, hz2, one_mul]
  have e4 : (z * t) * t = z := by rw [mul_assoc, ht2, mul_one]
  have e5 : (z * t) * (z * t) = 1 := by rw [← mul_assoc, e3, ht2]
  have e6 : t * z = z * t := hzt.symm
  rcases hg with h1 | h1 | h1 | h1 <;> rcases hh with h2 | h2 | h2 | h2 <;> rw [h1, h2] <;>
    simp [InZ, hz2, ht2, e1, e2, e3, e4, e5, e6]

theorem Std20.v_A_minus (d : Std20 p f K K' J S R R' W V z t) (h8 : Nat.card R = 8) {σ ε : G}
    (hσ : σ ∈ (S : Subgroup G)) (hσK : conjSub σ K = K') (hεW : ε ∈ W)
    (hinv : σ * ε * σ⁻¹ = ε⁻¹) : InZ z t ε := by
  have h1 : ε * ε = 1 := by
    by_contra h
    exact d.v_no_norm_four hσ hσK hεW h (d.late_W_exp_four h8 ε hεW) (Or.inr hinv)
  exact (by rcases d.late_inv_W ε hεW h1 with h | h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr h)))

theorem Std20.v_beta_eq (d : Std20 p f K K' J S R R' W V z t) (h8 : Nat.card R = 8)
    {s x : G} (hs : s ∈ (S : Subgroup G)) (hsK : conjSub s K = K') (hs2 : s * s = 1)
    (hxW : x ∈ Subgroup.normalizer (W : Set G)) (hxz : x * z * x⁻¹ = z * t)
    (hxt : x * t * x⁻¹ = z) (hxs : ∃ ε ∈ W, x * s * x⁻¹ = s * ε) :
    ∀ ζ : G, InZ z t ζ → ∃ w ∈ W, w * s * w⁻¹ = s * ζ := by
  obtain ⟨ε, hεW, hxsε⟩ := hxs
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hWc := d.late_hWc
  have hz2 : z * z = 1 := d.viol.hzK.sq
  have ht2 : t * t = 1 := d.viol.hzJ.sq
  have hzt : z * t = t * z := d.late_zt_comm
  have hsN : ∀ w ∈ W, s * w * s⁻¹ ∈ W := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp (d.hWN hs) w).mp hw
  have hxN : ∀ w ∈ W, x * w * x⁻¹ ∈ W := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp hxW w).mp hw
  have hβW : ∀ w ∈ W, (s * w * s⁻¹) * w⁻¹ ∈ W := fun w hw =>
    W.mul_mem (hsN w hw) (W.inv_mem hw)
  have hβmul : ∀ w₁ ∈ W, ∀ w₂ ∈ W, (s * (w₁ * w₂) * s⁻¹) * (w₁ * w₂)⁻¹ =
      ((s * w₁ * s⁻¹) * w₁⁻¹) * ((s * w₂ * s⁻¹) * w₂⁻¹) := by
    intro w₁ h₁ w₂ h₂
    have hc : w₁⁻¹ * ((s * w₂ * s⁻¹) * w₂⁻¹) = ((s * w₂ * s⁻¹) * w₂⁻¹) * w₁⁻¹ :=
      hWc _ (W.inv_mem h₁) _ (hβW w₂ h₂)
    calc (s * (w₁ * w₂) * s⁻¹) * (w₁ * w₂)⁻¹
        = (s * w₁ * s⁻¹) * (((s * w₂ * s⁻¹) * w₂⁻¹) * w₁⁻¹) := by group
      _ = (s * w₁ * s⁻¹) * (w₁⁻¹ * ((s * w₂ * s⁻¹) * w₂⁻¹)) := by rw [hc]
      _ = _ := by group
  have hβinv : ∀ w : G, s * ((s * w * s⁻¹) * w⁻¹) * s⁻¹ = ((s * w * s⁻¹) * w⁻¹)⁻¹ := by
    intro w
    calc s * ((s * w * s⁻¹) * w⁻¹) * s⁻¹ = (s * s) * w * s⁻¹ * w⁻¹ * s⁻¹ := by group
      _ = w * s⁻¹ * w⁻¹ * s⁻¹ := by rw [hs2, one_mul]
      _ = w * s * w⁻¹ * s⁻¹ := by nth_rewrite 1 [hsinv]; rfl
      _ = ((s * w * s⁻¹) * w⁻¹)⁻¹ := by group
  have hβZ : ∀ w ∈ W, InZ z t ((s * w * s⁻¹) * w⁻¹) := fun w hw =>
    d.v_A_minus h8 hs hsK (hβW w hw) (hβinv w)
  have hconj : ∀ w : G, w * s * w⁻¹ = s * ((s * w * s⁻¹) * w⁻¹) := by
    intro w
    calc w * s * w⁻¹ = w * s⁻¹ * w⁻¹ := by rw [hsinv]
      _ = (s * s) * w * s⁻¹ * w⁻¹ := by rw [hs2, one_mul]
      _ = s * ((s * w * s⁻¹) * w⁻¹) := by group
  have hβx : ∀ w ∈ W, (s * (x * w * x⁻¹) * s⁻¹) * (x * w * x⁻¹)⁻¹ =
      x * ((s * w * s⁻¹) * w⁻¹) * x⁻¹ := by
    intro w hw
    have hw' : x * w * x⁻¹ ∈ W := hxN w hw
    have hεc : ε * (x * w * x⁻¹) * ε⁻¹ = x * w * x⁻¹ := by
      rw [hWc ε hεW _ hw']
      group
    have h1 : x * ((s * w * s⁻¹) * w⁻¹) * x⁻¹ =
        (x * s * x⁻¹) * (x * w * x⁻¹) * (x * s * x⁻¹)⁻¹ * (x * w * x⁻¹)⁻¹ := by group
    rw [h1, hxsε]
    calc (s * (x * w * x⁻¹) * s⁻¹) * (x * w * x⁻¹)⁻¹
        = s * (ε * (x * w * x⁻¹) * ε⁻¹) * s⁻¹ * (x * w * x⁻¹)⁻¹ := by rw [hεc]
      _ = _ := by group
  obtain ⟨⟨e, heKW, he2⟩, -⟩ := d.late_exists_four_gens
  have heW : e ∈ W := heKW.2
  obtain ⟨hesq, -⟩ := d.late_swap_sq_data hs hsK (by rw [hs2]; exact W.one_mem) heKW he2
  have hb₁ : ((s * e * s⁻¹) * e⁻¹) = t ∨ ((s * e * s⁻¹) * e⁻¹) = z * t := by
    have hinve : e⁻¹ = e * z := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← mul_assoc, he2, hz2]
    have hcomm : (s * e * s⁻¹) * e = e * (s * e * s⁻¹) := hWc _ (hsN e heW) _ heW
    have : ((s * e * s⁻¹) * e⁻¹) = (e * (s * e * s⁻¹)) * z := by
      rw [hinve, ← mul_assoc, hcomm]
    rw [this]
    rcases hesq with h | h
    · right; rw [h, hzt]
    · left; rw [h, mul_assoc, ← hzt, ← mul_assoc, hz2, one_mul]
  set e₂ := x * e * x⁻¹ with he₂
  have he₂W : e₂ ∈ W := hxN e heW
  have hb₂ : ((s * e₂ * s⁻¹) * e₂⁻¹) = x * ((s * e * s⁻¹) * e⁻¹) * x⁻¹ := hβx e heW
  have e3 : (z * t) * z = t := by rw [mul_assoc, ← hzt, ← mul_assoc, hz2, one_mul]
  intro ζ hζ
  suffices h : ∃ w ∈ W, ((s * w * s⁻¹) * w⁻¹) = ζ by
    obtain ⟨w, hw, hwζ⟩ := h
    exact ⟨w, hw, by rw [hconj, hwζ]⟩
  rcases hb₁ with hb | hb
  ·
    have hb₂' : ((s * e₂ * s⁻¹) * e₂⁻¹) = z := by rw [hb₂, hb, hxt]
    rcases hζ with rfl | rfl | rfl | rfl
    · exact ⟨1, W.one_mem, by simp⟩
    · exact ⟨e₂, he₂W, hb₂'⟩
    · exact ⟨e, heW, hb⟩
    · refine ⟨e * e₂, W.mul_mem heW he₂W, ?_⟩
      rw [hβmul e heW e₂ he₂W, hb, hb₂', hzt]
  · have hb₂' : ((s * e₂ * s⁻¹) * e₂⁻¹) = t := by
      rw [hb₂, hb]
      have : x * (z * t) * x⁻¹ = (x * z * x⁻¹) * (x * t * x⁻¹) := by group
      rw [this, hxz, hxt, e3]
    have e4 : (z * t) * t = z := by rw [mul_assoc, ht2, mul_one]
    rcases hζ with rfl | rfl | rfl | rfl
    · exact ⟨1, W.one_mem, by simp⟩
    · refine ⟨e * e₂, W.mul_mem heW he₂W, ?_⟩
      rw [hβmul e heW e₂ he₂W, hb, hb₂', e4]
    · exact ⟨e₂, he₂W, hb₂'⟩
    · exact ⟨e, heW, hb⟩

omit [Finite G] [Fact p.Prime] in
theorem card_inZ {z t : G} (hz1 : z ≠ 1) (ht1 : t ≠ 1) (hzt' : t ≠ z) (hz2 : z * z = 1) :
    Nat.card {ζ : G | InZ z t ζ} = 4 := by
  classical
  have h1 : z * t ≠ 1 := by
    intro h
    apply hzt'
    exact (eq_inv_of_mul_eq_one_right h).trans (inv_eq_of_mul_eq_one_right hz2)
  have h2 : z ≠ z * t := by
    intro h
    have : z * 1 = z * t := by rw [mul_one]; exact h
    exact ht1 (mul_left_cancel this).symm
  have h3 : t ≠ z * t := by
    intro h
    have : 1 * t = z * t := by rw [one_mul]; exact h
    exact hz1 (mul_right_cancel this).symm
  have : {ζ : G | InZ z t ζ} = (({1, z, t, z * t} : Finset G) : Set G) := by
    ext ζ
    simp [InZ]
  rw [this, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair h3]
  · simp [Ne.symm hzt', h2]
  · simp [Ne.symm hz1, Ne.symm ht1, Ne.symm h1]

theorem Std20.v_swap_fixed (d : Std20 p f K K' J S R R' W V z t) (h8 : Nat.card R = 8)
    {s x : G} {e : ℕ} (hs : s ∈ (S : Subgroup G)) (hsK : conjSub s K = K') (hs2 : s * s = 1)
    (hxW : x ∈ Subgroup.normalizer (W : Set G)) (hxz : x * z * x⁻¹ = z * t)
    (hxt : x * t * x⁻¹ = z) (hxs : ∃ ε ∈ W, x * s * x⁻¹ = s * ε) (hx3 : x ^ 3 ^ e = 1) :
    ∃ ζ : G, InZ z t ζ ∧ (∃ w ∈ W, w * s * w⁻¹ = s * ζ) ∧ x * (s * ζ) * x⁻¹ = s * ζ := by
  classical
  have hz2 : z * z = 1 := d.viol.hzK.sq
  have ht2 : t * t = 1 := d.viol.hzJ.sq
  have hzt : z * t = t * z := d.late_zt_comm
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  obtain ⟨ε, hεW, hxsε⟩ := hxs
  have hεZ : InZ z t ε := by
    refine d.v_A_minus h8 hs hsK hεW ?_
    have h1 : (s * ε) * (s * ε) = 1 := by
      rw [← hxsε]
      calc x * s * x⁻¹ * (x * s * x⁻¹) = x * (s * s) * x⁻¹ := by group
        _ = 1 := by rw [hs2]; group
    have h2 : s * ε * s⁻¹ = ε⁻¹ := by
      have h3 : s * ε * s = ε⁻¹ := by
        have : (s * ε) * (s * ε) = (s * ε * s) * ε := by group
        rw [this] at h1
        exact eq_inv_of_mul_eq_one_left h1
      rw [hsinv]; exact h3
    exact h2
  have hx9 : ∀ ζ : G, InZ z t ζ → InZ z t (x * ζ * x⁻¹) := by
    intro ζ hζ
    have e3 : (z * t) * z = t := by rw [mul_assoc, ← hzt, ← mul_assoc, hz2, one_mul]
    rcases hζ with rfl | rfl | rfl | rfl
    · left; group
    · right; right; right; exact hxz
    · right; left; exact hxt
    · right; right; left
      have : x * (z * t) * x⁻¹ = (x * z * x⁻¹) * (x * t * x⁻¹) := by group
      rw [this, hxz, hxt, e3]
  set Ψ : Set G := {y | ∃ ζ : G, InZ z t ζ ∧ y = s * ζ} with hΨ
  have hΨcard : Nat.card Ψ = 4 := by
    have himg : Ψ = (fun ζ => s * ζ) '' {ζ : G | InZ z t ζ} := by
      ext y
      simp only [hΨ, Set.mem_ofPred_eq, Set.mem_image]
      constructor
      · rintro ⟨ζ, hζ, rfl⟩; exact ⟨ζ, hζ, rfl⟩
      · rintro ⟨ζ, hζ, rfl⟩; exact ⟨ζ, hζ, rfl⟩
    rw [himg, Nat.card_image_of_injective (mul_right_injective s)]
    exact card_inZ d.viol.hzK.ne_one d.viol.hzJ.ne_one d.late_ne_inv hz2
  have hstab : ∀ y ∈ Ψ, x * y * x⁻¹ ∈ Ψ := by
    rintro y ⟨ζ, hζ, rfl⟩
    refine ⟨ε * (x * ζ * x⁻¹), inZ_mul hz2 ht2 hzt hεZ (hx9 ζ hζ), ?_⟩
    calc x * (s * ζ) * x⁻¹ = (x * s * x⁻¹) * (x * ζ * x⁻¹) := by group
      _ = s * (ε * (x * ζ * x⁻¹)) := by rw [hxsε, mul_assoc]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, ⟨ζ, hζ, rfl⟩, hy⟩ := T3V.exists_fixed_conj_of_pow (p := 3) (n := e)
    (by rw [hΨcard]; omega) hx3 hstab
  exact ⟨ζ, hζ, d.v_beta_eq h8 hs hsK hs2 hxW hxz hxt ⟨ε, hεW, hxsε⟩ ζ hζ, hy⟩

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII
