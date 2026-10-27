module

public import CFSG.GH74.GLS.Stage4.T2P71BothA
public import CFSG.GH74.GLS.Stage4.T2P71Nat
public import CFSG.GH74.GLS.Stage4.T6SylM

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6.P71

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.IVK.Proofs2
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {N : T2N3 G} {u : G} {p : ℕ}

theorem comm_in_XY (h11b : IVK_11_1b_nat) (h : T6Ctx N u p) {m : ℕ} (hm : N.q₁ = p ^ m)
    (hcard : N.X₂.relIndex (R₂ N p) = p ^ (2 * m)) {Y : Subgroup G} (hYR : Y ≤ R₂ N p)
    (hYC : ∀ y ∈ Y, ∀ x ∈ N.X₁, x * y = y * x) (hYX : ∀ y ∈ Y, y ∈ N.X₂ → y = 1)
    (hYcard : Nat.card ↥Y = N.q₁) :
    ∀ x ∈ N.X₁, ∀ r ∈ R₂ N p, x * r * x⁻¹ * r⁻¹ ∈ N.X₂ ⊔ Y := by
  classical
  obtain ⟨F, iF, fF, φ, c, hF, hinj, hrange, hz, hX, hX', hw, hHK, hadd, hker, hsurj, hconj⟩ :=
    exists_natCoord h11b h hm hcard
  have hc1 : c 1 = 0 := (hker 1 (R₂ N p).one_mem).2 N.X₂.one_mem
  have hcinv : ∀ a ∈ R₂ N p, c a⁻¹ = - c a := by
    intro a ha
    have := hadd a ha a⁻¹ ((R₂ N p).inv_mem ha)
    rw [mul_inv_cancel, hc1] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  have hmemφ : ∀ g : SL2 F, φ g ∈ N.K₁ := fun g => hrange ▸ ⟨g, rfl⟩
  let T := {w : Fin 2 → F // w 1 = 0}
  have hcY : ∀ y ∈ Y, c y 1 = 0 := by
    intro y hy
    have hxm : φ (sl2U 1) ∈ N.X₁ := by
      rw [hX]
      refine ⟨sl2U 1, ?_, rfl⟩
      simp [uSub]
    have h1 := hconj (sl2U 1) y (hYR hy)
    have h2 : φ (sl2U 1) * y * (φ (sl2U 1))⁻¹ = y := by
      have := hYC y hy _ hxm
      rw [this]; group
    rw [h2] at h1
    have h3 := congrFun h1 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h3
  let f : ↥Y → T := fun y => ⟨c y, hcY y y.2⟩
  have hf : Function.Injective f := by
    intro y y' hyy'
    have h1 : c y = c y' := congrArg Subtype.val hyy'
    have h2 : c ((y : G) * (y' : G)⁻¹) = 0 := by
      rw [hadd _ (hYR y.2) _ ((R₂ N p).inv_mem (hYR y'.2)), hcinv _ (hYR y'.2), h1]
      simp
    have h3 : (y : G) * (y' : G)⁻¹ ∈ N.X₂ := (hker _ ((R₂ N p).mul_mem (hYR y.2) ((R₂ N p).inv_mem (hYR y'.2)))).1 h2
    have h4 : (y : G) * (y' : G)⁻¹ = 1 := hYX _ (Y.mul_mem y.2 (Y.inv_mem y'.2)) h3
    apply Subtype.ext
    exact mul_inv_eq_one.1 h4
  have hTcard : Nat.card T = Nat.card F := by
    apply Nat.card_congr
    exact
      { toFun := fun w => w.1 0
        invFun := fun t => ⟨![t, 0], rfl⟩
        left_inv := fun w => by
          apply Subtype.ext
          ext i
          fin_cases i
          · rfl
          · exact w.2.symm
        right_inv := fun t => rfl }
  have hbij : Function.Bijective f := by
    apply Function.Injective.bijective_of_nat_card_le hf
    rw [hTcard, hF, hYcard]
    exact le_of_eq hm.symm
  intro x hx r hr
  have hxr : x * r * x⁻¹ ∈ R₂ N p := by
    have hxK : x ∈ N.K₁ := by
      have hx' := hx
      rw [hX] at hx'
      obtain ⟨g, -, rfl⟩ := hx'
      exact hmemφ g
    exact R₂_norm N p (K₁_le_M₂ h hxK) hr
  have hk : x * r * x⁻¹ * r⁻¹ ∈ R₂ N p := (R₂ N p).mul_mem hxr ((R₂ N p).inv_mem hr)
  have hck : c (x * r * x⁻¹ * r⁻¹) 1 = 0 := by
    rw [hX] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    have h1 := hconj g r hr
    rw [hadd _ hxr _ ((R₂ N p).inv_mem hr), hcinv _ hr, h1]
    have e10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hg.2.2
    have e11 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := hg.2.1
    simp [e10, e11]
  obtain ⟨⟨y, hy⟩, hyk⟩ := hbij.2 ⟨c (x * r * x⁻¹ * r⁻¹), hck⟩
  have hyk' : c y = c (x * r * x⁻¹ * r⁻¹) := congrArg Subtype.val hyk
  have h2 : c (x * r * x⁻¹ * r⁻¹ * y⁻¹) = 0 := by
    rw [hadd _ hk _ ((R₂ N p).inv_mem (hYR hy)), hcinv _ (hYR hy), hyk']
    simp
  have h3 : x * r * x⁻¹ * r⁻¹ * y⁻¹ ∈ N.X₂ :=
    (hker _ ((R₂ N p).mul_mem hk ((R₂ N p).inv_mem (hYR hy)))).1 h2
  have : x * r * x⁻¹ * r⁻¹ = (x * r * x⁻¹ * r⁻¹ * y⁻¹) * y := by group
  rw [this]
  exact Subgroup.mul_mem_sup h3 hy


theorem R₂_norm_E (h11b : IVK_11_1b_nat) (h : T6Ctx N u p) {m : ℕ} (hm : N.q₁ = p ^ m)
    (hcard : N.X₂.relIndex (R₂ N p) = p ^ (2 * m)) {Y : Subgroup G} (hYR : Y ≤ R₂ N p)
    (hYC : ∀ y ∈ Y, ∀ x ∈ N.X₁, x * y = y * x) (hYX : ∀ y ∈ Y, y ∈ N.X₂ → y = 1)
    (hYcard : Nat.card ↥Y = N.q₁) :
    ∀ r ∈ R₂ N p, ∀ e ∈ (N.X₁ ⊔ N.X₂) ⊔ Y, r * e * r⁻¹ ∈ (N.X₁ ⊔ N.X₂) ⊔ Y := by
  intro r hr
  have hcomm := comm_in_XY h11b h hm hcard hYR hYC hYX hYcard
  set E : Subgroup G := (N.X₁ ⊔ N.X₂) ⊔ Y with hE
  have hX₁E : N.X₁ ≤ E := le_sup_left.trans le_sup_left
  have hX₂E : N.X₂ ≤ E := le_sup_right.trans le_sup_left
  have hYE : Y ≤ E := le_sup_right
  have hX₂Y : N.X₂ ⊔ Y ≤ E := sup_le hX₂E hYE
  have hle : E ≤ E.comap (MulAut.conj r).toMonoidHom := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro x hx
      show r * x * r⁻¹ ∈ E
      have h1 := hcomm x⁻¹ (N.X₁.inv_mem hx) r hr
      have e : r * x * r⁻¹ = x * (x⁻¹ * r * x⁻¹⁻¹ * r⁻¹) := by group
      rw [e]
      exact E.mul_mem (hX₁E hx) (hX₂Y h1)
    · intro x hx
      show r * x * r⁻¹ ∈ E
      rw [R₂_cent h r hr x hx]
      exact hX₂E hx
    · intro y hy
      show r * y * r⁻¹ ∈ E
      have h1 : ⁅r, y⁆ ∈ N.X₂ := (R₂_inv_comm h).2 r hr y (hYR hy)
      have e : r * y * r⁻¹ = ⁅r, y⁆ * y := by rw [commutatorElement_def]; group
      rw [e]
      exact E.mul_mem (hX₂E h1) (hYE hy)
  intro e he
  exact hle he

theorem H_norm_E (h : T6Ctx N u p) {Y : Subgroup G} (hYH : ∀ k ∈ N.H, ∀ y ∈ Y, k * y * k⁻¹ ∈ Y) :
    ∀ k ∈ N.H, ∀ e ∈ (N.X₁ ⊔ N.X₂) ⊔ Y, k * e * k⁻¹ ∈ (N.X₁ ⊔ N.X₂) ⊔ Y := by
  intro k hk
  set E : Subgroup G := (N.X₁ ⊔ N.X₂) ⊔ Y with hE
  have hle : E ≤ E.comap (MulAut.conj k).toMonoidHom := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro x hx
      exact (le_sup_left.trans le_sup_left : N.X₁ ≤ E) (h.sec5.loc.H_norm_X₁ k hk x hx)
    · intro x hx
      exact (le_sup_right.trans le_sup_left : N.X₂ ≤ E) (h.sec5.loc.H_norm_X₂ k hk x hx)
    · intro y hy
      exact (le_sup_right : Y ≤ E) (hYH k hk y hy)
  intro e he
  exact hle he


omit [Finite G] in
theorem weyl_step {Z K A A' : Subgroup G} {w w' : G} (hK : K = A ⊔ A') (hw : w ∈ K)
    (hAA' : ∀ x ∈ A', w⁻¹ * x * w ∈ A) (hw' : ∀ x ∈ A, w' * x * w'⁻¹ = x)
    (hZ : ∀ x ∈ A, w * x * w⁻¹ ∈ Z) (hZ' : ∀ x ∈ A, w' * x * w'⁻¹ ∈ Z) : w ∈ Z := by
  have hAZ : A ≤ Z := fun x hx => by
    have := hZ' x hx
    rwa [hw' x hx] at this
  have hA'Z : A' ≤ Z := fun x hx => by
    have h1 := hZ _ (hAA' x hx)
    have e : w * (w⁻¹ * x * w) * w⁻¹ = x := by group
    rwa [e] at h1
  have : K ≤ Z := by rw [hK]; exact sup_le hAZ hA'Z
  exact this hw

theorem final_contra (h : T6Ctx N u p) (hq : N.q₁ = N.q₂) {v g : G} (hv : v = u ∨ v = N.z * u)
    {Y : Subgroup G} (hYX₁ : ∀ y ∈ Y, ∀ x ∈ N.X₁, x * y = y * x)
    (hYX₂ : ∀ y ∈ Y, ∀ x ∈ N.X₂, x * y = y * x) (hYv : ∀ y ∈ Y, y * v = v * y)
    (hYcard : Nat.card ↥Y = N.q₂)
    (hg : ∀ e ∈ (N.X₁ ⊔ N.X₂) ⊔ Y, g * e * g⁻¹ ∈ (N.X₁ ⊔ N.X₂) ⊔ Y) (hgz : g * N.z * g⁻¹ = v) :
    False := by
  obtain ⟨hz2, hu2, hzu, -⟩ := zu_facts h
  obtain ⟨hv₁, hv₂⟩ := v_inv_X h hv
  set T : Subgroup G := N.X₁ ⊔ N.X₂ with hT
  have hcomm := X₁_X₂_comm h
  have hTp : IsPGroup p ↥T := by
    have h0 : IsPGroup p ↥(⊥ : Subgroup G) := IsPGroup.of_card (n := 0) (by simp)
    have := Y_pGroup h (P₀ := ⊥) bot_le h0
    rwa [sup_bot_eq] at this
  have hTcard : Nat.card ↥T = N.q₁ * N.q₂ := by
    have := card_Y h (P₀ := ⊥) bot_le
    rwa [sup_bot_eq, Subgroup.card_bot, mul_one] at this
  have hvT : ∀ t ∈ T, v * t * v⁻¹ = t⁻¹ := by
    intro t ht
    obtain ⟨x, hx, y, hy, rfl⟩ := (mem_sup_iff_of_comm hcomm t).1 ht
    have hxy := hcomm x⁻¹ (N.X₁.inv_mem hx) y⁻¹ (N.X₂.inv_mem hy)
    calc v * (x * y) * v⁻¹ = (v * x * v⁻¹) * (v * y * v⁻¹) := by group
      _ = x⁻¹ * y⁻¹ := by rw [hv₁ x hx, hv₂ y hy]
      _ = y⁻¹ * x⁻¹ := hxy
      _ = (x * y)⁻¹ := by rw [mul_inv_rev]
  have hzT : ∀ t ∈ T, t * N.z = N.z * t := by
    intro t ht
    obtain ⟨x, hx, y, hy, rfl⟩ := (mem_sup_iff_of_comm hcomm t).1 ht
    have h1 := z_cent_X₁ h hx
    have h2 := z_cent_X₂ h hy
    calc x * y * N.z = x * (y * N.z) := by group
      _ = x * (N.z * y) := by rw [h2]
      _ = (x * N.z) * y := by group
      _ = (N.z * x) * y := by rw [h1]
      _ = N.z * (x * y) := by group
  have hTY : ∀ t ∈ T, ∀ y ∈ Y, t * y = y * t := by
    intro t ht y hy
    obtain ⟨x, hx, x₂, hx₂, rfl⟩ := (mem_sup_iff_of_comm hcomm t).1 ht
    calc x * x₂ * y = x * (x₂ * y) := by group
      _ = x * (y * x₂) := by rw [hYX₂ y hy x₂ hx₂]
      _ = (x * y) * x₂ := by group
      _ = (y * x) * x₂ := by rw [hYX₁ y hy x hx]
      _ = y * (x * x₂) := by group
  have hCE : ∀ e ∈ T ⊔ Y, e * v = v * e → e ∈ Y := by
    intro e he hev
    obtain ⟨t, ht, y, hy, rfl⟩ := (mem_sup_iff_of_comm hTY e).1 he
    have h1 : v * (t * y) * v⁻¹ = t⁻¹ * y := by
      calc v * (t * y) * v⁻¹ = (v * t * v⁻¹) * (v * y * v⁻¹) := by group
        _ = t⁻¹ * y := by
          rw [hvT t ht]
          have : v * y * v⁻¹ = y := by
            have := hYv y hy
            calc v * y * v⁻¹ = (y * v) * v⁻¹ := by rw [this]
              _ = y := by group
          rw [this]
    have h2 : v * (t * y) * v⁻¹ = t * y := by
      calc v * (t * y) * v⁻¹ = (v * (t * y)) * v⁻¹ := rfl
        _ = ((t * y) * v) * v⁻¹ := by rw [hev]
        _ = t * y := by group
    have h3 : t⁻¹ = t := mul_right_cancel (h1.symm.trans h2)
    have h4 : t * t = 1 := by
      calc t * t = t * t⁻¹ := by rw [h3]
        _ = 1 := by group
    have h5 : t = 1 := by
      apply sq_eq_one_of_odd _ h4
      exact t6_odd_of_pGroup h.prime h.p_ne_two hTp ht
    rw [h5, one_mul]
    exact hy
  let f : ↥T → ↥Y := fun t => ⟨g * (t : G) * g⁻¹, by
    apply hCE
    · exact hg _ ((le_sup_left : T ≤ T ⊔ Y) t.2)
    · rw [← hgz]
      have := hzT t t.2
      calc g * (t : G) * g⁻¹ * (g * N.z * g⁻¹) = g * ((t : G) * N.z) * g⁻¹ := by group
        _ = g * (N.z * (t : G)) * g⁻¹ := by rw [this]
        _ = (g * N.z * g⁻¹) * (g * (t : G) * g⁻¹) := by group⟩
  have hf : Function.Injective f := by
    intro t t' htt'
    have := congrArg Subtype.val htt'
    simp only [f] at this
    have h2 : g * (t : G) * g⁻¹ = g * (t' : G) * g⁻¹ := this
    have h3 : (t : G) = t' := by
      calc (t : G) = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = g⁻¹ * (g * t' * g⁻¹) * g := by rw [h2]
        _ = t' := by group
    exact Subtype.ext h3
  have hle := Nat.card_le_card_of_injective f hf
  rw [hTcard, hYcard, hq] at hle
  have hq5 : 5 ≤ N.q₁ := h.sec5.loc.q₁_ge
  have hq5' : 5 ≤ N.q₂ := by omega
  have : N.q₂ * N.q₂ ≤ N.q₂ * 1 := by simpa using hle
  have := Nat.le_of_mul_le_mul_left this (by omega)
  omega

end CFSG.GH74.GLS.Stage4.Rest.T6.P71
