module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII2010Late10
public import CFSG.ClassicalInvolution.Asc77.AscT3VHexYEng

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameCore)
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D
open Out
open scoped commutatorElement MatrixGroups Pointwise

section Std


variable {G : Type} [Group G] [Finite G] [FrameCore G] {Ω : Set (Subgroup G)}
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

private theorem Std20Frame.late_toG (d : Std20Frame K K' J S R R' W V z t) :
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

theorem Std20Frame.v_hexY (d : Std20Frame K K' J S R R' W V z t) :
    ∃ X : Subgroup G, X = (J ⊓ Subgroup.normalizer (K : Set G)) ⊔
        (K ⊓ Subgroup.normalizer (J : Set G)) ∧
      X ≤ pairNormalizers K J z t ∧
      pairNormalizers K J z t ≤ Subgroup.normalizer (X : Set G) ∧
      X = oddCoreOf X ⊔ W ∧
      pairNormalizers K J z t ⊓ Subgroup.centralizer (W : Set G) ≤ X ∧
      (∃ r ∈ K ⊓ (S : Subgroup G), ∃ r' ∈ K' ⊓ (S : Subgroup G),
        r ∈ pairNormalizers K J z t ∧ r' ∈ pairNormalizers K J z t ∧ r * t * r⁻¹ = z * t ∧
        (∀ x ∈ W, (r * r') * x * (r * r')⁻¹ = x⁻¹) ∧
        pairNormalizers K J z t ⊓ Subgroup.centralizer
            ((Subgroup.closure {z, t} : Subgroup G) : Set G) = X ⊔ Subgroup.zpowers (r * r')) ∧
      ∃ φ : ↥(pairNormalizers K J z t) →* DihedralGroup 6, Function.Surjective φ ∧
        φ.ker = X.subgroupOf (pairNormalizers K J z t) := by
  exact d.late_toG.v_hexY

theorem Std20Frame.v_Y_odd (d : Std20Frame K K' J S R R' W V z t) {g x : G}
    (hgY : g ∈ Subgroup.normalizer ((pairNormalizers K J z t : Subgroup G) : Set G))
    (hgW : g ∈ Subgroup.normalizer (W : Set G)) (hgz : g * z * g⁻¹ = z)
    (hgt : g * t * g⁻¹ = t) (hxY : x ∈ pairNormalizers K J z t)
    (hxW : x ∈ Subgroup.normalizer (W : Set G)) (hx : Odd (orderOf x)) :
    x⁻¹ * (g * x * g⁻¹) ∈ pairNormalizers K J z t ⊓ Subgroup.centralizer (W : Set G) := by
  obtain ⟨X, -, hXY, hYX, hXeq, hf, ⟨r, hr, r', hr', hrY, hr'Y, hrt, hinv, hcent⟩, φ, hφs,
    hφk⟩ := d.v_hexY
  refine Y_odd_aux φ hφk hXY hYX hXeq hf hrY hr'Y hinv hcent
    (pairNormalizers_le_normalizer K J z t) d.late_hWc ?_
    (fun w hw w2 => d.late_inv_W w hw w2) d.late_z_mem_W d.late_t_mem_W hgY hgW hgz hgt hxY hxW hx
  intro w hw
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨w, d.hWS hw⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem Std20Frame.v_no_norm_four (d : Std20Frame K K' J S R R' W V z t) {σ ξ : G}
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

theorem Std20Frame.v_A_minus (d : Std20Frame K K' J S R R' W V z t) (h8 : Nat.card R = 8) {σ ε : G}
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

theorem Std20Frame.v_beta_eq (d : Std20Frame K K' J S R R' W V z t) (h8 : Nat.card R = 8)
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

theorem Std20Frame.v_swap_fixed (d : Std20Frame K K' J S R R' W V z t) (h8 : Nat.card R = 8)
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

theorem Std20Frame.v_hexg (d : Std20Frame K K' J S R R' W V z t) :
    ∃ g : G, g ∈ pairNormalizers K J z t ∧ g ∈ Subgroup.normalizer (W : Set G) ∧
      g * z * g⁻¹ = z * t ∧ g * t * g⁻¹ = z := by
  obtain ⟨u, r, v, t₀, T, hh⟩ := d.late_exists_hex
  refine ⟨t₀ * r, Subgroup.mul_mem _ hh.t₀_mem_pair hh.r_mem_pair,
    Subgroup.mul_mem _ hh.t₀_normW hh.r_normW, ?_, ?_⟩
  · calc t₀ * r * z * (t₀ * r)⁻¹ = t₀ * (r * z * r⁻¹) * t₀⁻¹ := by group
      _ = t₀ * z * t₀⁻¹ := by rw [hh.hrz]
      _ = z * t := hh.htz
  · calc t₀ * r * t * (t₀ * r)⁻¹ = t₀ * (r * t * r⁻¹) * t₀⁻¹ := by group
      _ = t₀ * (t * z) * t₀⁻¹ := by rw [hh.hrt]
      _ = (t₀ * t * t₀⁻¹) * (t₀ * z * t₀⁻¹) := by group
      _ = t * (z * t) := by rw [hh.ht₀t, hh.htz]
      _ = z := by rw [d.late_zt_comm, ← mul_assoc, d.viol.hzJ.sq, one_mul]

theorem Std20Frame.v_decomp (d : Std20Frame K K' J S R R' W V z t) {c : G}
    (hc : c ∈ pairNormalizers K J z t ⊓ Subgroup.centralizer (W : Set G)) :
    ∃ q ∈ oddCoreOf (pairNormalizers K J z t ⊓ Subgroup.centralizer (W : Set G)),
      ∃ w ∈ W, c = q * w := by
  obtain ⟨X, -, hXY, hYX, hXeq, hf, -, φ, hφs, hφk⟩ := d.v_hexY
  set C₀ : Subgroup G := pairNormalizers K J z t ⊓ Subgroup.centralizer (W : Set G) with hC₀
  have hWX : W ≤ X := hXeq ▸ le_sup_right
  have hXN : X ≤ Subgroup.normalizer (oddCoreOf X : Set G) := fun a ha =>
    mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer ha)
  have hset2 := Subgroup.coe_mul_of_right_le_normalizer_left (oddCoreOf X) W (hWX.trans hXN)
  obtain ⟨q', hq', w, hw, hqw⟩ : c ∈ (oddCoreOf X : Set G) * (W : Set G) := by
    rw [← hset2, ← hXeq]
    exact hf hc
  have hwC : w ∈ C₀ := ⟨hXY (hWX hw), Subgroup.mem_centralizer_iff.mpr fun a ha =>
    d.late_hWc a ha w hw⟩
  have hq'C : q' ∈ C₀ := by
    have : q' = c * w⁻¹ := by rw [← hqw]; group
    rw [this]
    exact C₀.mul_mem hc (C₀.inv_mem hwC)
  have hAC : oddCoreOf X ⊓ C₀ ≤ oddCoreOf C₀ := by
    refine Sec6Gen.le_oddCoreOf_of_normal inf_le_right ?_ ?_
    · intro a ha
      exact late_mem_normalizer_inf
        (mem_normalizer_oddCore_of_mem_normalizer (Subgroup.le_normalizer (hf ha)))
        (Subgroup.le_normalizer ha)
    · exact (oddCoreOf_odd_natCard X).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  exact ⟨q', hAC ⟨hq', hq'C⟩, w, hw, hqw.symm⟩

theorem Std20Frame.v_exists_x (d : Std20Frame K K' J S R R' W V z t) {s : G} (hs2 : s * s = 1)
    (hsY : s ∈ Subgroup.normalizer ((pairNormalizers K J z t : Subgroup G) : Set G))
    (hsW : s ∈ Subgroup.normalizer (W : Set G)) (hsz : s * z * s⁻¹ = z)
    (hst : s * t * s⁻¹ = t) :
    ∃ (x : G) (e : ℕ), x ∈ Subgroup.normalizer (W : Set G) ∧ x * z * x⁻¹ = z * t ∧
      x * t * x⁻¹ = z ∧ (∃ ε ∈ W, x * s * x⁻¹ = s * ε) ∧ x ^ 3 ^ e = 1 := by
  obtain ⟨g, hgY, hgW, hgz, hgt⟩ := d.v_hexg
  have hz2 : z * z = 1 := d.viol.hzK.sq
  have hzt : z * t = t * z := d.late_zt_comm
  obtain ⟨k, e, hk, hge⟩ := T3V.exists_pow_three_part g (isOfFinOrder_of_finite g)
  set x₀ := g ^ k with hx₀
  have hx₀Y : x₀ ∈ pairNormalizers K J z t := Subgroup.pow_mem _ hgY k
  have hx₀W : x₀ ∈ Subgroup.normalizer (W : Set G) := Subgroup.pow_mem _ hgW k
  obtain ⟨hx₀z, hx₀t⟩ := T3V.pow_act_of_mod hz2 hzt hgz hgt hk
  have hx₀odd : Odd (orderOf x₀) := by
    have : orderOf x₀ ∣ 3 ^ e := orderOf_dvd_of_pow_eq_one hge
    exact (Odd.pow (by decide : Odd 3)).of_dvd_nat this
  have hy := d.v_Y_odd hsY hsW hsz hst hx₀Y hx₀W hx₀odd
  obtain ⟨q, hq, w, hw, hyqw⟩ := d.v_decomp hy
  set C₀ : Subgroup G := pairNormalizers K J z t ⊓ Subgroup.centralizer (W : Set G) with hC₀
  set Q : Subgroup G := oddCoreOf C₀ with hQ
  set N : Subgroup G := Subgroup.normalizer (W : Set G) with hN
  have hQC : Q ≤ C₀ := oddCoreOf_le_self C₀
  have hQN : Q ≤ N := hQC.trans (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
  have hWN : W ≤ N := Subgroup.le_normalizer
  have hNC : ∀ {a : G}, a ∈ Subgroup.normalizer ((pairNormalizers K J z t : Subgroup G) : Set G) →
      a ∈ N → a ∈ Subgroup.normalizer (C₀ : Set G) := fun ha haN =>
    late_mem_normalizer_inf ha (T3V.mem_normalizer_centralizer haN)
  have hx₀C : x₀ ∈ Subgroup.normalizer (Q : Set G) :=
    mem_normalizer_oddCore_of_mem_normalizer (hNC (Subgroup.le_normalizer hx₀Y) hx₀W)
  have hsC : s ∈ Subgroup.normalizer (Q : Set G) :=
    mem_normalizer_oddCore_of_mem_normalizer (hNC hsY hsW)
  have hWnorm : (W.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWN).mpr le_rfl
  have hodd : Odd (Nat.card ↥(Q.subgroupOf N)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN).toEquiv]
    exact oddCoreOf_odd_natCard C₀
  have hQW : ∀ a ∈ Q.subgroupOf N, a ∈ W.subgroupOf N → a = 1 := by
    intro a haQ haW
    have haQ' : (a : G) ∈ Q := haQ
    have haW' : (a : G) ∈ W := haW
    have hodd' : Odd (orderOf (a : G)) := odd_orderOf_of_mem_oddCoreOf C₀ haQ'
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨(a : G), d.hWS haW'⟩
    have hk' : (a : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hdvd : orderOf (a : G) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hcop : Nat.Coprime (orderOf (a : G)) (2 ^ k) := hodd'.coprime_two_right.pow_right k
    have h1 : orderOf (a : G) = 1 := hcop.eq_one_of_dvd hdvd
    exact Subtype.ext (orderOf_eq_one_iff.mp h1)
  set x' : ↥N := ⟨x₀, hx₀W⟩ with hx'
  set s' : ↥N := ⟨s, hsW⟩ with hs'
  have hqx : ∀ a ∈ Q.subgroupOf N, x' * a * x'⁻¹ ∈ Q.subgroupOf N := by
    intro a ha
    exact (Subgroup.mem_normalizer_iff.mp hx₀C (a : G)).mp ha
  have hqs : ∀ a ∈ Q.subgroupOf N, s' * a * s'⁻¹ ∈ Q.subgroupOf N := by
    intro a ha
    exact (Subgroup.mem_normalizer_iff.mp hsC (a : G)).mp ha
  have hss : s' * s' = 1 := Subtype.ext hs2
  have hsx : ∃ q₂ ∈ Q.subgroupOf N, ∃ w₂ ∈ W.subgroupOf N, s' * x' * s'⁻¹ = x' * q₂ * w₂ := by
    refine ⟨⟨q, hQN hq⟩, hq, ⟨w, hWN hw⟩, hw, Subtype.ext ?_⟩
    show s * x₀ * s⁻¹ = x₀ * q * w
    have : x₀⁻¹ * (s * x₀ * s⁻¹) = q * w := hyqw
    calc s * x₀ * s⁻¹ = x₀ * (x₀⁻¹ * (s * x₀ * s⁻¹)) := by group
      _ = x₀ * (q * w) := by rw [this]
      _ = x₀ * q * w := by group
  obtain ⟨q₃, hq₃, w₃, hw₃, hfix⟩ := T3V.exists_mod_fixed (W.subgroupOf N) (Q.subgroupOf N)
    hodd hQW hqx hqs hss hsx
  have hfix' : s * ((q₃ : G) * x₀) * s⁻¹ = ((q₃ : G) * x₀) * (w₃ : G) :=
    congrArg Subtype.val hfix
  have hq₃Q : (q₃ : G) ∈ Q := hq₃
  have hq₃c : ∀ c ∈ W, c * (q₃ : G) = (q₃ : G) * c := fun c hc =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hQC hq₃Q)).2 c hc
  have hw₃W : (w₃ : G) ∈ W := hw₃
  have hztW : z * t ∈ W := W.mul_mem d.late_z_mem_W d.late_t_mem_W
  set x₁ : G := (q₃ : G) * x₀ with hx₁
  have hx₁W : x₁ ∈ N := N.mul_mem q₃.2 hx₀W
  have hx₁z : x₁ * z * x₁⁻¹ = z * t := by
    calc x₁ * z * x₁⁻¹ = (q₃ : G) * (x₀ * z * x₀⁻¹) * (q₃ : G)⁻¹ := by rw [hx₁]; group
      _ = (q₃ : G) * (z * t) * (q₃ : G)⁻¹ := by rw [hx₀z]
      _ = z * t := by rw [← hq₃c _ hztW]; group
  have hx₁t : x₁ * t * x₁⁻¹ = z := by
    calc x₁ * t * x₁⁻¹ = (q₃ : G) * (x₀ * t * x₀⁻¹) * (q₃ : G)⁻¹ := by rw [hx₁]; group
      _ = (q₃ : G) * z * (q₃ : G)⁻¹ := by rw [hx₀t]
      _ = z := by rw [← hq₃c _ d.late_z_mem_W]; group
  obtain ⟨k₂, e₂, hk₂, hge₂⟩ := T3V.exists_pow_three_part x₁ (isOfFinOrder_of_finite x₁)
  obtain ⟨hx₂z, hx₂t⟩ := T3V.pow_act_of_mod hz2 hzt hx₁z hx₁t hk₂
  obtain ⟨w', hw', hpow⟩ := T3V.pow_mul_mem hx₁W hw₃W k₂
  have hsx₂ : s * x₁ ^ k₂ * s⁻¹ = x₁ ^ k₂ * w' := by
    rw [← hpow, ← conj_pow, hfix']
  have hinv : s * (x₁ ^ k₂)⁻¹ * s⁻¹ = w'⁻¹ * (x₁ ^ k₂)⁻¹ := by
    have := congrArg (fun a => a⁻¹) hsx₂
    simpa [mul_assoc] using this
  have hx₂N : x₁ ^ k₂ ∈ N := Subgroup.pow_mem _ hx₁W k₂
  have hsi : s⁻¹ ∈ Subgroup.normalizer (W : Set G) := Subgroup.inv_mem _ hsW
  refine ⟨x₁ ^ k₂, e₂, hx₂N, hx₂z, hx₂t, ⟨s⁻¹ * (x₁ ^ k₂ * w'⁻¹ * (x₁ ^ k₂)⁻¹) * s, ?_, ?_⟩,
    hge₂⟩
  · have h1 : x₁ ^ k₂ * w'⁻¹ * (x₁ ^ k₂)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp hx₂N w'⁻¹).mp (W.inv_mem hw')
    have := (Subgroup.mem_normalizer_iff.mp hsi _).mp h1
    simpa [mul_assoc] using this
  · calc x₁ ^ k₂ * s * (x₁ ^ k₂)⁻¹ = x₁ ^ k₂ * (s * (x₁ ^ k₂)⁻¹ * s⁻¹) * s := by group
      _ = x₁ ^ k₂ * (w'⁻¹ * (x₁ ^ k₂)⁻¹) * s := by rw [hinv]
      _ = s * (s⁻¹ * (x₁ ^ k₂ * w'⁻¹ * (x₁ ^ k₂)⁻¹) * s) := by group

theorem Std20Frame.v_swap_Y (d : Std20Frame K K' J S R R' W V z t) {s : G}
    (hs : s ∈ (S : Subgroup G)) (hsK : conjSub s K = K') (hst : s * t * s⁻¹ = t) :
    s ∈ Subgroup.normalizer ((pairNormalizers K J z t : Subgroup G) : Set G) := by
  obtain ⟨u, r, v, t₀, T, hh⟩ := d.late_exists_hex
  set Z : Subgroup G := Subgroup.closure {z, t} with hZ
  set Y : Subgroup G := pairNormalizers K J z t with hY
  set NZ : Subgroup G := Subgroup.normalizer (Z : Set G) with hNZ
  have hz2 : z * z = 1 := d.viol.hzK.sq
  have hzt : z * t = t * z := d.late_zt_comm
  have hsz : s * z * s⁻¹ = z := d.late_S_act_z hs
  have hsZ : s ∈ NZ := by
    refine T3V.mem_normalizer_of_conj_eq (T3V.conj_eq_of_mem_closure ?_)
    intro a ha
    rcases ha with rfl | ha
    · exact hsz
    · rw [Set.mem_singleton_iff] at ha
      subst ha
      exact hst
  have hYN : Y ≤ NZ := pairNormalizers_le_normalizer K J z t
  have hKY : K ⊓ NZ ≤ Y := le_sup_left
  have hJY : J ⊓ NZ ≤ Y := le_sup_right
  have hconj_inf : ∀ {h : G} (A : Subgroup G), h ∈ NZ →
      conjSub h (A ⊓ NZ) = conjSub h A ⊓ NZ := by
    intro h A hh'
    rw [late_conjSub_inf, conjSub_eq_self_of_mem hh']
  have hconj_Y : ∀ {h : G} {A : Subgroup G}, h ∈ Y → A ≤ Y → conjSub h A ≤ Y := by
    intro h A hhY hA
    calc conjSub h A ≤ conjSub h Y := conjSub_mono hA
      _ = Y := conjSub_eq_self_of_mem hhY
  have hgY : t₀ * r ∈ Y := Y.mul_mem hh.t₀_mem_pair hh.r_mem_pair
  have hK'Y : K' ⊓ NZ ≤ Y := by
    have : K' ⊓ NZ = conjSub (t₀ * r) (J ⊓ NZ) := by
      rw [hconj_inf J (hYN hgY), hh.conj_J]
    rw [this]
    exact hconj_Y hgY hJY
  have hmY : r * t₀ ∈ Y := Y.mul_mem hh.r_mem_pair hh.t₀_mem_pair
  have hmt : (r * t₀) * z * (r * t₀)⁻¹ = t := by
    calc (r * t₀) * z * (r * t₀)⁻¹ = r * (t₀ * z * t₀⁻¹) * r⁻¹ := by group
      _ = r * (z * t) * r⁻¹ := by rw [hh.htz]
      _ = (r * z * r⁻¹) * (r * t * r⁻¹) := by group
      _ = z * (t * z) := by rw [hh.hrz, hh.hrt]
      _ = t := by
        rw [← mul_assoc, hzt, mul_assoc, hz2, mul_one]
  have hJsi : IsUniqueInvolution (conjSub s J) t := by
    have := d.viol.hzJ.conj s
    rwa [hst] at this
  have hJsY : conjSub s J ⊓ NZ ≤ Y := by
    rcases d.late_members_of_inv hmt (d.hyp.conjInvariant s J d.late_mem_J) hJsi with h | h
    · rw [h, ← hconj_inf K (hYN hmY)]
      exact hconj_Y hmY hKY
    · rw [h, ← hconj_inf K' (hYN hmY)]
      exact hconj_Y hmY hK'Y
  refine Asc77.T3CII.mem_normalizer_of_conjSub_le ?_
  calc conjSub s Y = conjSub s (K ⊓ NZ) ⊔ conjSub s (J ⊓ NZ) := by
        rw [hY, pairNormalizers, late_conjSub_sup]
    _ = (K' ⊓ NZ) ⊔ (conjSub s J ⊓ NZ) := by
        rw [hconj_inf K hsZ, hconj_inf J hsZ, hsK]
    _ ≤ Y := sup_le hK'Y hJsY

theorem Std20Frame.v_swap_rho (d : Std20Frame K K' J S R R' W V z t) (h8 : Nat.card R = 8) {s : G}
    (hs : s ∈ (S : Subgroup G)) (hsK : conjSub s K = K') (hs2 : s * s = 1) :
    ∃ s₁ ρ : G, (∃ w ∈ W, w * s * w⁻¹ = s₁) ∧ s₁ ∈ (S : Subgroup G) ∧ s₁ * s₁ = 1 ∧
      (∃ ζ : G, InZ z t ζ ∧ s₁ = s * ζ) ∧ ρ * s₁ = s₁ * ρ ∧ Odd (orderOf ρ) ∧
      ρ * z * ρ⁻¹ = z * t ∧ ρ * t * ρ⁻¹ = z := by
  obtain ⟨⟨e, heKW, he2⟩, -⟩ := d.late_exists_four_gens
  obtain ⟨-, hst⟩ := d.late_swap_sq_data hs hsK (by rw [hs2]; exact W.one_mem) heKW he2
  have hsz : s * z * s⁻¹ = z := d.late_S_act_z hs
  obtain ⟨x, e, hxW, hxz, hxt, hxs, hx3⟩ := d.v_exists_x hs2 (d.v_swap_Y hs hsK hst) (d.hWN hs)
    hsz hst
  obtain ⟨ζ, hζ, hW', hfix⟩ := d.v_swap_fixed h8 hs hsK hs2 hxW hxz hxt hxs hx3
  have hz2 : z * z = 1 := d.viol.hzK.sq
  have ht2 : t * t = 1 := d.viol.hzJ.sq
  have hzt : z * t = t * z := d.late_zt_comm
  have hζW : ζ ∈ W := by
    rcases hζ with rfl | rfl | rfl | rfl
    · exact W.one_mem
    · exact d.late_z_mem_W
    · exact d.late_t_mem_W
    · exact W.mul_mem d.late_z_mem_W d.late_t_mem_W
  have hsζ : s * ζ * s⁻¹ = ζ := by
    rcases hζ with rfl | rfl | rfl | rfl
    · group
    · exact hsz
    · exact hst
    · calc s * (z * t) * s⁻¹ = (s * z * s⁻¹) * (s * t * s⁻¹) := by group
        _ = z * t := by rw [hsz, hst]
  have hζ2 : ζ * ζ = 1 := by
    rcases hζ with rfl | rfl | rfl | rfl
    · group
    · exact hz2
    · exact ht2
    · calc z * t * (z * t) = z * (t * z) * t := by group
        _ = z * (z * t) * t := by rw [hzt]
        _ = (z * z) * (t * t) := by group
        _ = 1 := by rw [hz2, ht2, one_mul]
  refine ⟨s * ζ, x, hW', Subgroup.mul_mem _ hs (d.hWS hζW), ?_, ⟨ζ, hζ, rfl⟩, ?_, ?_, hxz, hxt⟩
  · have hc : ζ * s = s * ζ := by
      calc ζ * s = (s * ζ * s⁻¹) * s := by rw [hsζ]
        _ = s * ζ := by group
    calc s * ζ * (s * ζ) = s * (ζ * s) * ζ := by group
      _ = s * (s * ζ) * ζ := by rw [hc]
      _ = (s * s) * (ζ * ζ) := by group
      _ = 1 := by rw [hs2, hζ2, one_mul]
  · calc x * (s * ζ) = (x * (s * ζ) * x⁻¹) * x := by group
      _ = (s * ζ) * x := by rw [hfix]
  · have : orderOf x ∣ 3 ^ e := orderOf_dvd_of_pow_eq_one hx3
    exact (Odd.pow (by decide : Odd 3)).of_dvd_nat this

end Std

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
