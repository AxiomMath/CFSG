module

public import CFSG.GH74.GLS.Stage4.T2Interfaces
public import CFSG.GH74.GLS.Stage4.T2P52
public import CFSG.GH74.GLS.Stage4.T2Borel

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.Stage4.Rest.T2

section Q3

variable {G : Type} [Group G] [Finite G]

theorem t2L_cent_of_q3 (hC3 : T2C3) {K S : Subgroup G} {F : Type} [Field F] [Finite F]
    (hF3 : Nat.card F = 3) (e : ↥K ≃* SL2 F) (hP : IsPGroup 2 ↥((S ⊓ K).subgroupOf K))
    (hPidx : ¬ 2 ∣ ((S ⊓ K).subgroupOf K).index) {f : G} (hfK : ∀ x ∈ K, f * x * f⁻¹ ∈ K)
    (hfS : ∀ s ∈ S, f * s = s * f) : ∀ x ∈ K, f * x * f⁻¹ = x := by
  have hfn : f ∈ normalizer (K : Set G) := Subgroup.mem_normalizer_fintype hfK
  let ρ : MulAut ↥K := Subgroup.normalizerMonoidHom K ⟨f, hfn⟩
  have hρ : ∀ y : ↥K, ((ρ y : ↥K) : G) = f * y * f⁻¹ := fun y => rfl
  have h1 : ρ = 1 := hC3 ↥K F hF3 e _ hP hPidx ρ (by
    intro p hp
    apply Subtype.ext
    rw [hρ]
    have hpS : (p : G) ∈ S := (Subgroup.mem_subgroupOf.1 hp).1
    have := hfS p hpS
    calc f * (p : G) * f⁻¹ = (p : G) * f * f⁻¹ := by rw [this]
      _ = p := by group)
  intro x hx
  have h2 := congrArg (fun r : MulAut ↥K => ((r ⟨x, hx⟩ : ↥K) : G)) h1
  simpa [hρ] using h2

end Q3

section Torus

variable {G : Type} [Group G]

theorem t2L_normX_torus {K H X X' : Subgroup G} {w f : G} {F : Type} [Field F] [Finite F]
    (φ : SL2 F →* G) (hφ : Function.Injective φ) (hrange : φ.range = K)
    (hX : X = (uSub F).map φ) (hX' : X' = (lSub F).map φ) (hw : w = φ (sl2W F))
    (hHK : H ⊓ K = (tSub F).map φ) (h5 : 5 ≤ Nat.card F) (hcardX : Nat.card ↥X = Nat.card F)
    (hodd : Odd (orderOf f)) (hfK : ∀ x ∈ K, f * x * f⁻¹ ∈ K)
    (hfH' : ∀ h ∈ H, f⁻¹ * h * f ∈ H)
    (hHX : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) (hfw : f * w = w * f) :
    (∀ x ∈ X, f * x * f⁻¹ ∈ X) ∧ (∀ x ∈ X', f * x * f⁻¹ ∈ X') := by
  classical
  have hXK : ∀ x ∈ X, x ∈ K := by
    intro x hx
    rw [hX] at hx
    obtain ⟨a, -, rfl⟩ := hx
    rw [← hrange]; exact ⟨a, rfl⟩
  let YG : Subgroup G := X.map (MulAut.conj f).toMonoidHom
  have hYGle : YG ≤ K := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using hfK x (hXK x hx)
  let Y : Subgroup (SL2 F) := YG.comap φ
  have hYcard : Nat.card ↥Y = Nat.card F := by
    have h2 : Y.map φ = YG := by
      rw [Subgroup.map_comap_eq]
      exact inf_eq_right.2 (hrange ▸ hYGle)
    have h1 : Nat.card ↥(Y.map φ) = Nat.card ↥Y := Subgroup.card_map_of_injective hφ
    have h3 : Nat.card ↥YG = Nat.card ↥X :=
      Subgroup.card_map_of_injective (f := (MulAut.conj f).toMonoidHom)
        (fun a b h => (MulAut.conj f).injective h)
    rw [← h1, h2, h3, hcardX]
  have hn : ∀ d ∈ tSub F, ∀ y ∈ Y, d * y * d⁻¹ ∈ Y := by
    intro d hd y hy
    have hdHK : φ d ∈ H ⊓ K := by rw [hHK]; exact ⟨d, hd, rfl⟩
    obtain ⟨x, hx, hxy⟩ := (Subgroup.mem_comap.1 hy)
    have hconj : ((MulAut.conj f).toMonoidHom) x = f * x * f⁻¹ := by simp [MulAut.conj_apply]
    rw [hconj] at hxy
    refine Subgroup.mem_comap.2 ⟨(f⁻¹ * φ d * f) * x * (f⁻¹ * φ d * f)⁻¹, hHX _ (hfH' _ hdHK.1) x hx, ?_⟩
    calc ((MulAut.conj f).toMonoidHom) ((f⁻¹ * φ d * f) * x * (f⁻¹ * φ d * f)⁻¹)
        = f * ((f⁻¹ * φ d * f) * x * (f⁻¹ * φ d * f)⁻¹) * f⁻¹ := by simp [MulAut.conj_apply]
      _ = φ d * (f * x * f⁻¹) * (φ d)⁻¹ := by group
      _ = φ (d * y * d⁻¹) := by rw [hxy, map_mul, map_mul, map_inv]
  have hsylow := t2C_sylow_torus h5 Y hYcard hn
  have hdich : (∀ x ∈ X, f * x * f⁻¹ ∈ X) ∨ (∀ x ∈ X, f * x * f⁻¹ ∈ X') := by
    have key : ∀ x ∈ X, ∃ a ∈ Y, φ a = f * x * f⁻¹ := by
      intro x hx
      have hmem : f * x * f⁻¹ ∈ YG := ⟨x, hx, by simp [MulAut.conj_apply]⟩
      obtain ⟨a, ha⟩ := (hrange ▸ hYGle hmem : f * x * f⁻¹ ∈ φ.range)
      exact ⟨a, Subgroup.mem_comap.2 (by rw [ha]; exact hmem), ha⟩
    rcases hsylow with h | h
    · left
      intro x hx
      obtain ⟨a, ha, hax⟩ := key x hx
      rw [← hax, hX]
      exact ⟨a, h ▸ ha, rfl⟩
    · right
      intro x hx
      obtain ⟨a, ha, hax⟩ := key x hx
      rw [← hax, hX']
      exact ⟨a, h ▸ ha, rfl⟩
  have hfw' : f * w⁻¹ = w⁻¹ * f := by
    calc f * w⁻¹ = w⁻¹ * (w * f) * w⁻¹ := by group
      _ = w⁻¹ * (f * w) * w⁻¹ := by rw [hfw]
      _ = w⁻¹ * f := by group
  have hsw1 : ∀ x ∈ X, w * x * w⁻¹ ∈ X' := by
    intro x hx
    rw [hX] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨c, rfl⟩ := mem_uSub.1 ha
    rw [hw, hX']
    refine ⟨_, sl2L_mem_lSub (-c), ?_⟩
    rw [← t2A_W_conj_U, map_mul, map_mul, map_inv]
  have hsw3 : ∀ x ∈ X', w * x * w⁻¹ ∈ X := by
    intro x hx
    rw [hX'] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨c, rfl⟩ := mem_lSub.1 ha
    rw [hw, hX]
    refine ⟨_, sl2U_mem_uSub (-c), ?_⟩
    rw [← t2A_W_conj_L, map_mul, map_mul, map_inv]
  have hsw2 : ∀ x ∈ X', ∃ y ∈ X, x = w * y * w⁻¹ := by
    intro x hx
    rw [hX'] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨c, rfl⟩ := mem_lSub.1 ha
    refine ⟨φ (sl2U (-c)), ?_, ?_⟩
    · rw [hX]; exact ⟨_, sl2U_mem_uSub (-c), rfl⟩
    · rw [hw, ← map_inv, ← map_mul, ← map_mul, t2A_W_conj_U, neg_neg]
  have hconjw : ∀ y x : G, x = w * y * w⁻¹ → f * x * f⁻¹ = w * (f * y * f⁻¹) * w⁻¹ := by
    intro y x hxy
    rw [hxy]
    calc f * (w * y * w⁻¹) * f⁻¹ = (f * w) * y * (w⁻¹ * f⁻¹) := by group
      _ = (w * f) * y * (f⁻¹ * w⁻¹) := by
          rw [hfw]
          have : w⁻¹ * f⁻¹ = f⁻¹ * w⁻¹ := by
            rw [← mul_inv_rev, ← mul_inv_rev, hfw]
          rw [this]
      _ = w * (f * y * f⁻¹) * w⁻¹ := by group
  rcases hdich with hA | hB
  · exact ⟨hA, fun x hx => by
      obtain ⟨y, hy, rfl⟩ := hsw2 x hx
      rw [hconjw y _ rfl]
      exact hsw1 _ (hA y hy)⟩
  · exfalso
    have hB' : ∀ x ∈ X', f * x * f⁻¹ ∈ X := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hsw2 x hx
      rw [hconjw y _ rfl]
      exact hsw3 _ (hB y hy)
    have hstep : ∀ x ∈ X, (f * f) * x * (f * f)⁻¹ ∈ X := by
      intro x hx
      have e : (f * f) * x * (f * f)⁻¹ = f * (f * x * f⁻¹) * f⁻¹ := by group
      rw [e]
      exact hB' _ (hB x hx)
    have hiter : ∀ j : ℕ, ∀ x ∈ X, (f * f) ^ j * x * ((f * f) ^ j)⁻¹ ∈ X := by
      intro j
      induction j with
      | zero => intro x hx; simpa using hx
      | succ j ih =>
        intro x hx
        have e : (f * f) ^ (j + 1) * x * ((f * f) ^ (j + 1))⁻¹ =
            (f * f) * ((f * f) ^ j * x * ((f * f) ^ j)⁻¹) * (f * f)⁻¹ := by
          rw [pow_succ']; generalize (f * f) ^ j = v; group
        rw [e]
        exact hstep _ (ih x hx)
    obtain ⟨k, hk⟩ := hodd
    have hfpow : (f * f) ^ (k + 1) = f := by
      have h1 : f ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one f
      calc (f * f) ^ (k + 1) = f ^ (2 * k + 1) * f := by
            rw [← pow_two, ← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ]
        _ = f := by rw [h1, one_mul]
    have hfX : ∀ x ∈ X, f * x * f⁻¹ ∈ X := by
      intro x hx
      have := hiter (k + 1) x hx
      rwa [hfpow] at this
    have hone : ∀ x ∈ X, x = 1 := by
      intro x hx
      have h1 := hfX x hx
      have h2 := hB x hx
      rw [hX] at h1; rw [hX'] at h2
      obtain ⟨a, ha, hax⟩ := h1
      obtain ⟨b, hb, hbx⟩ := h2
      have hab : a = b := hφ (hax.trans hbx.symm)
      have : a ∈ uSub F ⊓ lSub F := ⟨ha, hab ▸ hb⟩
      rw [uSub_inf_lSub, Subgroup.mem_bot] at this
      have h3 : f * x * f⁻¹ = 1 := by rw [← hax, this, map_one]
      calc x = f⁻¹ * (f * x * f⁻¹) * f := by group
        _ = 1 := by rw [h3]; group
    have hXbot : X = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact Subgroup.mem_bot.2 (hone x hx)
    have hcard1 : Nat.card ↥X = 1 := Subgroup.card_eq_one.2 hXbot
    omega

end Torus

section Factor

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem t2L_factor {K H X X' : Subgroup G} {w f z : G} {q : ℕ} (hq_odd : Odd q) (hq3 : 3 ≤ q)
    (hcoord : ∃ (F : Type) (_ : Field F) (_ : Finite F) (φ : SL2 F →* G), Nat.card F = q ∧
      Function.Injective φ ∧ φ.range = K ∧ φ (negOne F) = z ∧ X = (uSub F).map φ ∧
      X' = (lSub F).map φ ∧ w = φ (sl2W F) ∧ H ⊓ K = (tSub F).map φ)
    (hcardX : Nat.card ↥X = q) (hodd : Odd (orderOf f)) (hfK : ∀ x ∈ K, f * x * f⁻¹ ∈ K)
    (hfH' : ∀ h ∈ H, f⁻¹ * h * f ∈ H) (hHX : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X)
    (hfw : f * w = w * f) (hcent3 : q = 3 → ∀ x ∈ K, f * x * f⁻¹ = x) :
    (∀ x ∈ X, f * x * f⁻¹ ∈ X) ∧ (∀ x ∈ X', f * x * f⁻¹ ∈ X') := by
  obtain ⟨F, _, _, φ, hcard, hinj, hrange, -, hX, hX', hw, hHK⟩ := hcoord
  by_cases h3 : q = 3
  · have hc := hcent3 h3
    have hXK : ∀ x ∈ X, x ∈ K := by
      intro x hx
      rw [hX] at hx
      obtain ⟨a, -, rfl⟩ := hx
      rw [← hrange]; exact ⟨a, rfl⟩
    have hX'K : ∀ x ∈ X', x ∈ K := by
      intro x hx
      rw [hX'] at hx
      obtain ⟨a, -, rfl⟩ := hx
      rw [← hrange]; exact ⟨a, rfl⟩
    exact ⟨fun x hx => by rw [hc x (hXK x hx)]; exact hx,
      fun x hx => by rw [hc x (hX'K x hx)]; exact hx⟩
  · have h5 : 5 ≤ Nat.card F := by
      obtain ⟨m, hm⟩ := hq_odd
      omega
    exact t2L_normX_torus φ hinj hrange hX hX' hw hHK h5 (by rw [hcard]; exact hcardX) hodd hfK hfH'
      hHX hfw

end Factor

theorem ch6T2FNormX_of (hC3 : T2C3) : Ch6T2FNormX := by
  intro G _ _ Gs _ q₁ q₂ z K₁ K₂ F₁ F₂ _ _ t hSet hRem N u hz hK₁ hK₂ hq₁ hq₂ hLoc hCoord f hodd hfS
  have ctx := t2Ctx_of hSet hRem hLoc hz hK₁ hK₂ hq₁ hq₂
  have hnormH := t2Ctx_normH hSet hRem hLoc hz hK₁ hK₂ hq₁ hq₂ hodd hfS
  subst hz hK₁ hK₂ hq₁ hq₂
  have hfz : f * N.z = N.z * f := hfS N.z hLoc.z_mem_S
  obtain ⟨hfn₁, hfn₂⟩ := t2Ctx_odd_normK ctx hfz hodd
  have hfH : f ∈ normalizer (N.H : Set G) := Subgroup.mem_normalizer_fintype hnormH
  have hfH' : ∀ h ∈ N.H, f⁻¹ * h * f ∈ N.H := fun h hh => by
    simpa using (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hfH) h).1 hh
  obtain ⟨-, hs₂⟩ := t2C_sylow_inf_K hSet hRem ctx.Sctx
  have hP₂ : IsPGroup 2 ↥((N.S ⊓ N.K₂).subgroupOf N.K₂) :=
    (ctx.Sctx.S2.to_le inf_le_left).comap_subtype
  have f₁ := t2L_factor hLoc.q₁_odd (by have := hLoc.q₁_ge; omega) hCoord.coord₁ hLoc.card_X₁ hodd
    hfn₁ hfH' hLoc.H_norm_X₁ (hfS N.w₁ hLoc.w₁_memS)
    (fun h3 => absurd h3 (by have := hLoc.q₁_ge; omega))
  have f₂ := t2L_factor hLoc.q₂_odd hLoc.q₂_ge hCoord.coord₂ hLoc.card_X₂ hodd hfn₂ hfH'
    hLoc.H_norm_X₂ (hfS N.w₂ hLoc.w₂_memS) (fun h3 => by
      obtain ⟨F', _, _, hF'card, ⟨e⟩⟩ := hLoc.iso₂
      exact t2L_cent_of_q3 hC3 (hF'card.trans h3) e hP₂ hs₂ hfn₂ hfS)
  exact ⟨f₁.1, f₁.2, f₂.1, f₂.2⟩

end CFSG.GH74.GLS.Stage4.Rest
