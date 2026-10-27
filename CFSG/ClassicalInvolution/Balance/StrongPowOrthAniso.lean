module

public import CFSG.ClassicalInvolution.Balance.StrongPowOrthPivot
public import CFSG.ClassicalInvolution.Balance.StrongPowOrthDelta

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Orth

open QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOddQuadratic (anisotropic_finrank_le_two)

section Joint

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem two_ne_zero_of_odd_card' {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K)) :
    (2 : K) ≠ 0 := by
  have := Fintype.ofFinite K
  refine Ring.two_ne_zero fun h => ?_
  have h1 : Fintype.card K % 2 = 0 := FiniteField.even_card_of_char_two h
  rw [← Nat.card_eq_fintype_card] at h1
  have h3 := Nat.odd_iff.mp hodd
  omega

@[expose] def jointSub (t₁ t₂ : V ≃ₗ[F] V) (ε δ : F) : Submodule F V :=
  eigenSub t₁ ε ⊓ eigenSub t₂ δ

theorem mem_jointSub {t₁ t₂ : V ≃ₗ[F] V} {ε δ : F} {x : V} :
    x ∈ jointSub t₁ t₂ ε δ ↔ t₁ x = ε • x ∧ t₂ x = δ • x :=
  Iff.rfl

theorem polar_eq_zero_of_joint {t₁ t₂ : V ≃ₗ[F] V}
    (ht₁ : t₁ ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (ht₂ : t₂ ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {ε δ ε' δ' : F}
    (h : ε * ε' ≠ 1 ∨ δ * δ' ≠ 1) {x y : V} (hx : x ∈ jointSub t₁ t₂ ε δ)
    (hy : y ∈ jointSub t₁ t₂ ε' δ') : polar Q x y = 0 := by
  rcases h with h | h
  · exact polar_eq_zero_of_eigen ht₁ hx.1 hy.1 h
  · exact polar_eq_zero_of_eigen ht₂ hx.2 hy.2 h

theorem exists_pair_split (h2 : (2 : F) ≠ 0) {t₁ t₂ : V ≃ₗ[F] V} (ht₂ : t₂ * t₂ = 1)
    (hc : t₁ * t₂ = t₂ * t₁) {ε δ : F} (hδ : δ * δ = 1) {x : V} (hx : t₁ x = ε • x) :
    ∃ x₁ x₂ : V, x = x₁ + x₂ ∧ x₁ ∈ jointSub t₁ t₂ ε δ ∧ x₂ ∈ jointSub t₁ t₂ ε (-δ) := by
  have e2 : ∀ y, t₂ (t₂ y) = y := fun y => by
    have := congrArg (fun g : V ≃ₗ[F] V => g y) ht₂
    simpa using this
  have ec : ∀ y, t₁ (t₂ y) = t₂ (t₁ y) := fun y => by
    have := congrArg (fun g : V ≃ₗ[F] V => g y) hc
    simpa using this
  set a : F := (2 : F)⁻¹ with ha
  have h2a : a * 2 = 1 := inv_mul_cancel₀ h2
  refine ⟨a • (x + δ • t₂ x), a • (x - δ • t₂ x), ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [← smul_add]
    have : x + δ • t₂ x + (x - δ • t₂ x) = (2 : F) • x := by module
    rw [this, smul_smul, h2a, one_smul]
  · rw [SetLike.mem_coe, mem_eigenSub]
    simp only [map_smul, map_add, ec, hx]
    module
  · rw [SetLike.mem_coe, mem_eigenSub]
    simp only [map_smul, map_add, e2]
    match_scalars <;> first | ring1 | linear_combination (-a) * hδ
  · rw [SetLike.mem_coe, mem_eigenSub]
    simp only [map_smul, map_sub, ec, hx]
    module
  · rw [SetLike.mem_coe, mem_eigenSub]
    simp only [map_smul, map_sub, e2]
    match_scalars <;> first | ring1 | linear_combination (-a) * hδ

@[expose] def sg (F : Type) [Field F] (b : Bool) : F := if b then 1 else -1

theorem sg_mul_self (b : Bool) : sg F b * sg F b = 1 := by
  cases b <;> simp [sg]

theorem sg_mul_ne_one (h2 : (2 : F) ≠ 0) {b b' : Bool} (h : b ≠ b') : sg F b * sg F b' ≠ 1 := by
  intro h1
  apply h2
  cases b <;> cases b' <;> simp [sg] at h1 h ⊢ <;> linear_combination -h1

theorem exists_joint_decomp (h2 : (2 : F) ≠ 0) {t₁ t₂ : V ≃ₗ[F] V} (ht₁ : t₁ * t₁ = 1)
    (ht₂ : t₂ * t₂ = 1) (hc : t₁ * t₂ = t₂ * t₁) (v : V) :
    ∃ f : Bool → Bool → V, (∀ b c, f b c ∈ jointSub t₁ t₂ (sg F b) (sg F c)) ∧
      v = f true true + f true false + f false true + f false false := by
  obtain ⟨pp, pm, hv, hpp, hpm⟩ := exists_eigen_split h2 ht₁ (sg_mul_self (F := F) true) v
  have hs : ∀ b, sg F (!b) = -sg F b := fun b => by cases b <;> simp [sg]
  obtain ⟨a₁, a₂, ha, ha₁, ha₂⟩ := exists_pair_split h2 ht₂ hc (sg_mul_self (F := F) true) hpp
  obtain ⟨b₁, b₂, hb, hb₁, hb₂⟩ := exists_pair_split h2 ht₂ hc (sg_mul_self (F := F) true)
    (ε := sg F false) (by rw [hpm]; simp [sg])
  refine ⟨fun b c => if b then (if c then a₁ else a₂) else (if c then b₁ else b₂), ?_, ?_⟩
  · intro b c
    cases b <;> cases c <;> simp [sg] <;> assumption
  · simp only [ite_true]
    rw [hv, ha, hb]
    abel

@[simp] theorem sg_true : sg F true = 1 := by simp [sg]

@[simp] theorem sg_false : sg F false = -1 := by simp [sg]

theorem polarNondegOn_jointSub (h2 : (2 : F) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    {t₁ t₂ : V ≃ₗ[F] V} (h₁ : t₁ ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (h₂ : t₂ ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (ht₁ : t₁ * t₁ = 1) (ht₂ : t₂ * t₂ = 1)
    (hc : t₁ * t₂ = t₂ * t₁) {ε δ : F} (hε : ε * ε = 1) (hδ : δ * δ = 1) :
    PolarNondegOn Q (jointSub t₁ t₂ ε δ) := by
  intro x hx hxW
  apply eq_zero_of_polar_eq_zero hQ
  intro z
  obtain ⟨y₂, hy₁, hy₂, hpair⟩ := exists_joint_component (Q := Q) h2 h₁ h₂ ht₁ ht₂ hc hε hδ z
  rw [← hpair x hx.1 hx.2]
  exact hxW y₂ (mem_jointSub.mpr ⟨hy₁, hy₂⟩)

theorem finrank_jointSub_le_two [Finite F] [FiniteDimensional F V] (h2 : (2 : F) ≠ 0)
    (hodd : Odd (Nat.card F)) (hQ : (polarBilin Q).Nondegenerate) {t₁ t₂ : V ≃ₗ[F] V}
    (h₁ : t₁ ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (h₂ : t₂ ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (ht₁ : t₁ * t₁ = 1) (ht₂ : t₂ * t₂ = 1)
    (hc : t₁ * t₂ = t₂ * t₁) {ε δ : F} (hε : ε * ε = 1) (hδ : δ * δ = 1)
    (hno : ∀ x ∈ jointSub t₁ t₂ ε δ, Q x = 0 → x = 0) :
    Module.finrank F (jointSub t₁ t₂ ε δ) ≤ 2 :=
  anisotropic_finrank_le_two hodd (Q.restrict (jointSub t₁ t₂ ε δ))
    (nondegenerate_polarBilin_restrict (polarNondegOn_jointSub h2 hQ h₁ h₂ ht₁ ht₂ hc hε hδ))
    fun x hx => Subtype.ext (hno x x.2 hx)

theorem finrank_eigenSub_add [FiniteDimensional F V] (h2 : (2 : F) ≠ 0) {t : V ≃ₗ[F] V}
    (ht : t * t = 1) {ε : F} (hε : ε * ε = 1) :
    Module.finrank F (eigenSub t ε) + Module.finrank F (eigenSub t (-ε)) =
      Module.finrank F V := by
  have hε0 : ε ≠ 0 := fun h => by rw [h, mul_zero] at hε; exact zero_ne_one hε
  have hinf : eigenSub t ε ⊓ eigenSub t (-ε) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨h1, h2'⟩ := Submodule.mem_inf.mp hx
    rw [mem_eigenSub] at h1 h2'
    have : (2 * ε) • x = 0 := by
      rw [mul_smul, two_smul]
      calc ε • x + ε • x = t x - (-ε) • x := by rw [h1, neg_smul, sub_neg_eq_add]
        _ = 0 := by rw [h2', sub_self]
    have h0 : x = 0 := (smul_eq_zero.mp this).resolve_left (mul_ne_zero h2 hε0)
    rw [h0]
    exact Submodule.zero_mem _
  have hsup : eigenSub t ε ⊔ eigenSub t (-ε) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨zp, zm, hz, hzp, hzm⟩ := exists_eigen_split h2 ht hε v
    rw [hz]
    exact Submodule.add_mem_sup hzp hzm
  have h := Submodule.finrank_sup_add_finrank_inf_eq (eigenSub t ε) (eigenSub t (-ε))
  rw [hsup, hinf, finrank_top, finrank_bot] at h
  omega

theorem finrank_jointSub_add [FiniteDimensional F V] (h2 : (2 : F) ≠ 0) {t₁ t₂ : V ≃ₗ[F] V}
    (ht₂ : t₂ * t₂ = 1) (hc : t₁ * t₂ = t₂ * t₁) {ε δ : F} (hδ : δ * δ = 1) :
    Module.finrank F (jointSub t₁ t₂ ε δ) + Module.finrank F (jointSub t₁ t₂ ε (-δ)) =
      Module.finrank F (eigenSub t₁ ε) := by
  have hδ0 : δ ≠ 0 := fun h => by rw [h, mul_zero] at hδ; exact zero_ne_one hδ
  have hinf : jointSub t₁ t₂ ε δ ⊓ jointSub t₁ t₂ ε (-δ) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨h1, h2'⟩ := Submodule.mem_inf.mp hx
    have h1' := h1.2
    have h2'' := h2'.2
    have : (2 * δ) • x = 0 := by
      rw [mul_smul, two_smul]
      calc δ • x + δ • x = t₂ x - (-δ) • x := by rw [h1', neg_smul, sub_neg_eq_add]
        _ = 0 := by rw [h2'', sub_self]
    have h0 : x = 0 := (smul_eq_zero.mp this).resolve_left (mul_ne_zero h2 hδ0)
    rw [h0]
    exact Submodule.zero_mem _
  have hsup : jointSub t₁ t₂ ε δ ⊔ jointSub t₁ t₂ ε (-δ) = eigenSub t₁ ε := by
    refine le_antisymm (sup_le inf_le_left inf_le_left) fun x hx => ?_
    obtain ⟨x₁, x₂, hxx, hx₁, hx₂⟩ := exists_pair_split h2 ht₂ hc hδ (mem_eigenSub.mp hx)
    rw [hxx]
    exact Submodule.add_mem_sup hx₁ hx₂
  have h := Submodule.finrank_sup_add_finrank_inf_eq (jointSub t₁ t₂ ε δ)
    (jointSub t₁ t₂ ε (-δ))
  rw [hsup, hinf, finrank_bot] at h
  omega

theorem finrank_sum_jointSub [FiniteDimensional F V] (h2 : (2 : F) ≠ 0) {t₁ t₂ : V ≃ₗ[F] V}
    (ht₁ : t₁ * t₁ = 1) (ht₂ : t₂ * t₂ = 1) (hc : t₁ * t₂ = t₂ * t₁) :
    Module.finrank F V =
      Module.finrank F (jointSub t₁ t₂ (sg F true) (sg F true)) +
      Module.finrank F (jointSub t₁ t₂ (sg F true) (sg F false)) +
      Module.finrank F (jointSub t₁ t₂ (sg F false) (sg F true)) +
      Module.finrank F (jointSub t₁ t₂ (sg F false) (sg F false)) := by
  have h1 := finrank_eigenSub_add h2 ht₁ (sg_mul_self (F := F) true)
  have h2' := finrank_jointSub_add h2 ht₂ hc (ε := (1 : F)) (sg_mul_self (F := F) true)
  have h3 := finrank_jointSub_add h2 ht₂ hc (ε := (-1 : F)) (sg_mul_self (F := F) true)
  have e1 : sg F true = 1 := sg_true
  have e2 : sg F false = -1 := sg_false
  rw [e1] at h1 h2' h3 ⊢
  rw [e2] at ⊢
  omega

theorem sg_mul_eq {b b' c c' : Bool} (h : b ≠ b') (h' : c ≠ c') :
    sg F b' * sg F c' = sg F b * sg F c := by
  cases b <;> cases b' <;> cases c <;> cases c' <;> simp_all

theorem elemOn_mono {S S' : Submodule F V} (h : S ≤ S') : elemOn Q S ≤ elemOn Q S' := by
  rw [elemOn, Subgroup.closure_le]
  rintro _ ⟨u, w, hu, hw, hQ, hB, rfl⟩
  exact Subgroup.subset_closure ⟨u, w, h hu, h hw, hQ, hB, rfl⟩

theorem polarNondegOn_sup {W T : Submodule F V} (hW : PolarNondegOn Q W)
    (hT : PolarNondegOn Q T) (hWT : ∀ w ∈ W, ∀ t ∈ T, polar Q w t = 0) :
    PolarNondegOn Q (W ⊔ T) := by
  intro x hx hxo
  obtain ⟨w, hw, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
  have hTW : ∀ t ∈ T, ∀ y ∈ W, polar Q t y = 0 := fun t ht y hy => by
    rw [polar_comm]
    exact hWT y hy t ht
  have hw0 : w = 0 := hW w hw fun y hy => by
    have := hxo y (Submodule.mem_sup_left hy)
    rwa [polar_add_left, hTW t ht y hy, add_zero] at this
  have ht0 : t = 0 := hT t ht fun y hy => by
    have := hxo y (Submodule.mem_sup_right hy)
    rwa [polar_add_left, hWT w hw y hy, zero_add] at this
  rw [hw0, ht0, add_zero]

end Joint

theorem orthGenAniso : OrthGenAniso := by
  intro F V _ _ _ _ _ Q hQ hodd h5 h7 t₁ t₂ h₁ h₂ ht₁ ht₂ hc hno H hH₁ hH₂ hH₃
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card' hodd
  set Jp : Bool × Bool → Submodule F V := fun σ => jointSub t₁ t₂ (sg F σ.1) (sg F σ.2) with hJp
  have horth : ∀ σ τ : Bool × Bool, σ ≠ τ → ∀ x ∈ Jp σ, ∀ y ∈ Jp τ, polar Q x y = 0 := by
    intro σ τ hστ x hx y hy
    by_cases hb : σ.1 = τ.1
    · have hc' : σ.2 ≠ τ.2 := fun h => hστ (Prod.ext hb h)
      exact polar_eq_zero_of_joint h₁ h₂ (Or.inr (sg_mul_ne_one h2 hc')) hx hy
    · exact polar_eq_zero_of_joint h₁ h₂ (Or.inl (sg_mul_ne_one h2 hb)) hx hy
  have hanis : ∀ σ, ∀ x ∈ Jp σ, Q x = 0 → x = 0 := fun σ x hx hQx =>
    hno x (sg F σ.1) (sg F σ.2) hx.1 hx.2 hQx
  have hreg : ∀ σ, PolarNondegOn Q (Jp σ) := fun σ =>
    polarNondegOn_jointSub h2 hQ h₁ h₂ ht₁ ht₂ hc (sg_mul_self σ.1) (sg_mul_self σ.2)
  have hd : ∀ σ, Module.finrank F (Jp σ) ≤ 2 := fun σ =>
    finrank_jointSub_le_two h2 hodd hQ h₁ h₂ ht₁ ht₂ hc (sg_mul_self σ.1) (sg_mul_self σ.2)
      (hanis σ)
  have hsumdim : Module.finrank F V = Module.finrank F (Jp (true, true)) +
      Module.finrank F (Jp (true, false)) + Module.finrank F (Jp (false, true)) +
      Module.finrank F (Jp (false, false)) := finrank_sum_jointSub h2 ht₁ ht₂ hc
  have hside : ∀ σ τ : Bool × Bool, σ ≠ τ → elemOn Q (Jp σ ⊔ Jp τ) ≤ H := by
    intro σ τ hστ
    by_cases hb : σ.1 = τ.1
    · refine (elemOn_mono ?_).trans (hH₁ (sg F σ.1) (sg_mul_self σ.1))
      refine sup_le inf_le_left fun x hx => ?_
      have : x ∈ eigenSub t₁ (sg F τ.1) := hx.1
      rwa [← hb] at this
    by_cases hc' : σ.2 = τ.2
    · refine (elemOn_mono ?_).trans (hH₂ (sg F σ.2) (sg_mul_self σ.2))
      refine sup_le inf_le_right fun x hx => ?_
      have : x ∈ eigenSub t₂ (sg F τ.2) := hx.2
      rwa [← hc'] at this
    · refine (elemOn_mono ?_).trans (hH₃ (sg F σ.1 * sg F σ.2) ?_)
      · have key : ∀ ρ : Bool × Bool, ∀ x ∈ Jp ρ,
            x ∈ eigenSub (t₁ * t₂) (sg F ρ.1 * sg F ρ.2) := fun ρ x hx => by
          rw [mem_eigenSub, LinearEquiv.mul_apply, hx.2, LinearEquiv.map_smul, hx.1, smul_smul,
            mul_comm]
        refine sup_le (fun x hx => key σ x hx) fun x hx => ?_
        have := key τ x hx
        rwa [sg_mul_eq hb hc'] at this
      · calc sg F σ.1 * sg F σ.2 * (sg F σ.1 * sg F σ.2)
            = (sg F σ.1 * sg F σ.1) * (sg F σ.2 * sg F σ.2) := by ring
          _ = 1 := by rw [sg_mul_self, sg_mul_self, mul_one]
  have hdecomp := exists_joint_decomp h2 ht₁ ht₂ hc
  have pivot : ∀ T W A B : Bool × Bool, T ≠ W → T ≠ A → T ≠ B → W ≠ A → W ≠ B → A ≠ B →
      Module.finrank F (Jp W) = 2 → Module.finrank F (Jp A) = 2 →
      Module.finrank F (Jp B) = 2 → 1 ≤ Module.finrank F (Jp T) →
      (∀ v : V, ∃ w ∈ Jp W, ∃ t ∈ Jp T, ∃ a ∈ Jp A, ∃ b ∈ Jp B, v = w + t + a + b) →
      elementaryGroup Q ≤ H := by
    intro T W A B hTW hTA hTB hWA hWB hAB hW2 hA2 hB2 hT1 hsum
    refine elementaryGroup_le_of_pivot h2 hodd hQ (W := Jp W) (T := Jp T) (A := Jp A)
      (B := Jp B) (horth W T hTW.symm) (horth W A hWA) (horth W B hWB) (horth T A hTA)
      (horth T B hTB) hW2 (hanis W) hA2 (hanis A) hB2 (hanis B) (hanis T) ?_ hsum
      (polarNondegOn_sup (hreg W) (hreg T) (horth W T hTW.symm)) (hside W T hTW.symm)
      (hside W A hWA) (hside W B hWB)
    intro h
    rw [h, finrank_bot] at hT1
    omega
  have hN : 7 ≤ Module.finrank F (Jp (true, true)) + Module.finrank F (Jp (true, false)) +
      Module.finrank F (Jp (false, true)) + Module.finrank F (Jp (false, false)) := by
    rw [← hsumdim]
    exact h7
  have d1 := hd (true, true)
  have d2 := hd (true, false)
  have d3 := hd (false, true)
  have d4 := hd (false, false)
  by_cases c1 : Module.finrank F (Jp (true, true)) < 2
  · refine pivot (true, true) (true, false) (false, true) (false, false) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by omega) (by omega) (by omega)
      (by omega) fun v => ?_
    obtain ⟨f, hf, hv⟩ := hdecomp v
    exact ⟨f true false, hf _ _, f true true, hf _ _, f false true, hf _ _, f false false,
      hf _ _, by rw [hv]; try abel⟩
  by_cases c2 : Module.finrank F (Jp (true, false)) < 2
  · refine pivot (true, false) (true, true) (false, true) (false, false) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
      (by omega) (by omega) fun v => ?_
    obtain ⟨f, hf, hv⟩ := hdecomp v
    exact ⟨f true true, hf _ _, f true false, hf _ _, f false true, hf _ _, f false false,
      hf _ _, by rw [hv]; try abel⟩
  by_cases c3 : Module.finrank F (Jp (false, true)) < 2
  · refine pivot (false, true) (true, true) (true, false) (false, false) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
      (by omega) (by omega) fun v => ?_
    obtain ⟨f, hf, hv⟩ := hdecomp v
    exact ⟨f true true, hf _ _, f false true, hf _ _, f true false, hf _ _, f false false,
      hf _ _, by rw [hv]; try abel⟩
  · refine pivot (false, false) (true, true) (true, false) (false, true) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
      (by omega) (by omega) fun v => ?_
    obtain ⟨f, hf, hv⟩ := hdecomp v
    exact ⟨f true true, hf _ _, f false false, hf _ _, f true false, hf _ _, f false true,
      hf _ _, by rw [hv]; try abel⟩

end CFSG.ClassicalInvolution.Balance.StrongBalance.Orth
