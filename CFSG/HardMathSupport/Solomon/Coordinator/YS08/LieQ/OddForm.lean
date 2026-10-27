module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddFormCore

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits CFSG.LieType.ChevTwo.OppCl

section FormGlue

variable {F : Type} [Field F] [Finite F] {q : ℕ} [Fact q.Prime] [CharP F q] {V : Type}
  [AddCommGroup V] [Module F V] [Finite V] {H : Type} [Group H]

@[expose] def EA1ε (Φ : ReflForm F V) (Sing : V → Prop) (ρ : H →* Module.End F V) (ε : F) : Prop :=
  ∀ x y, Sing x → Φ.β x y = 0 →
    ∃ (c : F) (h : H), ∀ v, ρ h v = v + Φ.β x v • (y + c • x) + (ε * Φ.β y v) • x

@[expose] def EA2ε (Φ : ReflForm F V) (Sing : V → Prop) (ρ : H →* Module.End F V) : Prop :=
  ∀ x : V, Sing x → ∃ (c₀ : F) (h : H), c₀ ≠ 0 ∧ ∀ v, ρ h v = v + (c₀ * Φ.β x v) • x

theorem rigid_of_comm_form (Φ : ReflForm F V) (Sing : V → Prop) (TS : Submodule F V → Prop)
    (ρ : H →* Module.End F V) {ε : F} (hε : ε = 1 ∨ ε = -1) (hσΦ : ∀ c, Φ.σ (Φ.σ c) = c)
    (hdim : 3 ≤ Module.finrank F V) (hTS : ∀ U, TS U → Φ.IsTotallyIsotropic U)
    (hTSsing : ∀ U, TS U → ∀ v ∈ U, Sing v) (hinj : Function.Injective ρ)
    (hE1 : EA1ε Φ Sing ρ ε) (hroute : EA2ε Φ Sing ρ ∨ 6 ≤ Module.finrank F V)
    (X : ℕ → Submodule F V) (m : ℕ) (hX0 : X 0 = ⊥) (hXmono : Monotone X)
    (hXTS : ∀ k, TS (X k)) (hK : flagKernel ρ (isoCompletion Φ X m) ≠ ⊥)
    (r : Equiv.Perm V) (hr : r ∈ semilinGroup F V) (hΦ : SemiIso Φ r) (n : ℕ)
    (hn : Nat.Coprime n q) (hrn : r ^ n = 1)
    (hcomm : ∀ h ∈ flagKernel ρ (isoCompletion Φ X m), ∀ v, r (ρ h v) = ρ h (r v)) :
    ∃ c : F, ∀ v, r v = c • v := by
  classical
  have hXTI : ∀ k, Φ.IsTotallyIsotropic (X k) := fun k => hTS _ (hXTS k)
  have hW0 : X m ≠ ⊥ := by
    intro hbot
    apply hK
    rw [eq_bot_iff]
    intro h hh
    rw [Subgroup.mem_bot]
    apply hinj
    apply LinearMap.ext
    intro v
    have h1 : isoCompletion Φ X m (m + 1) = Φ.perp (X m) := by
      have := isoCompletion_perp (F := Φ) (X := X) (m := m) (k := m) le_rfl
      rwa [show 2 * m + 1 - m = m + 1 by omega] at this
    have hv : v ∈ isoCompletion Φ X m (m + 1) := by
      rw [h1, hbot, Φ.perp_bot]
      trivial
    have := hh.2 m v hv
    rw [isoCompletion_of_le le_rfl, hbot, Submodule.mem_bot, sub_eq_zero] at this
    rw [this, map_one]
    rfl
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exact absurd (h0 ▸ hX0) hW0
    · exact ⟨m - 1, by omega⟩
  obtain ⟨x₀, hx₀, hx₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨v₁, hv₁⟩ : ∃ v, Φ.β x₀ v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx₀0 (Φ.nondeg x₀ hcon)
  obtain ⟨σ, hC⟩ := FormCoreQ.exists_ctx Φ r hr hΦ ⟨x₀, v₁, hv₁⟩
  have hEich : ∀ x ∈ X (k + 1), ∀ y ∈ Φ.perp (X (k + 1)), ∃ c : F, ∃ h ∈ flagKernel ρ
      (isoCompletion Φ X (k + 1)), ∀ v,
        ρ h v = v + Φ.β x v • (y + c • x) + (ε * Φ.β y v) • x := by
    intro x hx y hy
    obtain ⟨c, h, hh⟩ := hE1 x y (hTSsing _ (hXTS (k + 1)) x hx) (hy x hx)
    refine ⟨c, h, ?_, hh⟩
    exact mem_flagKernel_isoCompletion ρ hXmono hXTI (Nat.lt_succ_self k) hx hy
      (a := y + c • x) (add_mem hy (Submodule.smul_mem _ _ (hXTI (k + 1) hx))) ε hh
  have hE : ∀ x ∈ X (k + 1), x ≠ 0 → ∀ y ∈ Φ.perp (X (k + 1)), ∃ c : F, ∀ v,
      r (v + Φ.β x v • (y + c • x) + (ε * Φ.β y v) • x) =
        r v + Φ.β x (r v) • (y + c • x) + (ε * Φ.β y (r v)) • x := by
    intro x hx _ y hy
    obtain ⟨c, h, hh, hρ⟩ := hEich x hx y hy
    refine ⟨c, fun v => ?_⟩
    have := hcomm h hh v
    rwa [hρ, hρ] at this
  have hline : ∀ x ∈ X (k + 1), x ≠ 0 → ∃ c : F, r x = c • x := by
    intro x hx hx0
    obtain ⟨v₀, hv₀⟩ : ∃ v, Φ.β x v = 1 := by
      obtain ⟨v₂, hv₂⟩ : ∃ v, Φ.β x v ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hx0 (Φ.nondeg x hcon)
      exact ⟨(Φ.β x v₂)⁻¹ • v₂, by rw [Φ.smul_right, inv_mul_cancel₀ hv₂]⟩
    rcases hroute with hT | h6
    · obtain ⟨c₀, h, hc₀, hh⟩ := hT x (hTSsing _ (hXTS (k + 1)) x hx)
      have hmem : h ∈ flagKernel ρ (isoCompletion Φ X (k + 1)) := by
        refine mem_flagKernel_isoCompletion ρ hXmono hXTI (Nat.lt_succ_self k) hx
          (hXTI (k + 1) hx) (a := c₀ • x)
          (Submodule.smul_mem _ _ (hXTI (k + 1) hx)) 0 fun w => ?_
        rw [hh, zero_mul, zero_smul, add_zero, smul_smul, mul_comm]
      refine hC.line_of_transvection hv₀ hc₀ fun v => ?_
      have := hcomm h hmem v
      rw [hh, hh] at this
      exact this
    · have hperp := Φ.finrank_perp (X (k + 1))
      have hWperp : X (k + 1) ≤ Φ.perp (X (k + 1)) := hXTI (k + 1)
      have hfr : 3 ≤ Module.finrank F (Φ.perp (X (k + 1))) := by
        have := Submodule.finrank_mono hWperp
        omega
      have hnle1 : ¬ Φ.perp (X (k + 1)) ≤ Submodule.span F {x} := by
        intro hle
        have := Submodule.finrank_mono hle
        rw [finrank_span_singleton hx0] at this
        omega
      obtain ⟨y₁, hy₁P, hy₁⟩ := SetLike.not_le_iff_exists.1 hnle1
      have hnle2 : ¬ Φ.perp (X (k + 1)) ≤ Submodule.span F ({x, y₁} : Set V) := by
        intro hle
        have h1 := Submodule.finrank_mono hle
        have h2 : Module.finrank F (Submodule.span F ({x, y₁} : Set V)) ≤ 2 := by
          have := finrank_span_finset_le_card (R := F) ({x, y₁} : Finset V)
          have h3 : ({x, y₁} : Finset V).card ≤ 2 := Finset.card_le_two
          simp only [Finset.coe_insert, Finset.coe_singleton] at this
          exact le_trans this h3
        omega
      obtain ⟨y₂, hy₂P, hy₂⟩ := SetLike.not_le_iff_exists.1 hnle2
      exact hC.line_of_eichler hε hσΦ hx0 hy₁ hy₂ (hE x hx hx0 y₁ hy₁P) (hE x hx hx0 y₂ hy₂P)
  exact FormCoreQ.rigid_form_core_q Φ hε hσΦ hdim (X (k + 1)) hW0 (hXTI (k + 1)) r hr hΦ n hn hrn
    hline hE


theorem rigidInner_form (Φ : ReflForm F V) (Sing : V → Prop) (TS : Submodule F V → Prop)
    (ρ : H →* Module.End F V) (𝔉 : Subgroup H → ℕ → Submodule F V) {ε : F}
    (hε : ε = 1 ∨ ε = -1) (hσΦ : ∀ c, Φ.σ (Φ.σ c) = c)
    (hdim : 3 ≤ Module.finrank F V) (hTS : ∀ U, TS U → Φ.IsTotallyIsotropic U)
    (hTSsing : ∀ U, TS U → ∀ v ∈ U, Sing v) (hinj : Function.Injective ρ)
    (hE1 : EA1ε Φ Sing ρ ε) (hroute : EA2ε Φ Sing ρ ∨ 6 ≤ Module.finrank F V)
    (hflag : ∀ Q : Subgroup H, IsPGroup q Q → ∃ (X : ℕ → Submodule F V) (m : ℕ), X 0 = ⊥ ∧
      Monotone X ∧ (∀ k, TS (X k)) ∧ 𝔉 Q = isoCompletion Φ X m)
    (hiso : ∀ (x : H) (u v : V), Φ.β (ρ x u) (ρ x v) = Φ.β u v) :
    ∀ Q : Subgroup H, IsPGroup q Q → flagKernel ρ (𝔉 Q) ≠ ⊥ → ∀ x : H,
      Nat.Coprime (orderOf x) q → (∀ k ∈ flagKernel ρ (𝔉 Q), x * k = k * x) →
        ∃ c : F, ∀ v, ρ x v = c • v := by
  intro Q hQ hK x hx hcomm
  obtain ⟨X, m, hX0, hXmono, hXTS, hFQ⟩ := hflag Q hQ
  rw [hFQ] at hK hcomm
  let r : Equiv.Perm V :=
    { toFun := ρ x
      invFun := ρ x⁻¹
      left_inv := fun v => by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      right_inv := fun v => by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] }
  have hrv : ∀ v, r v = ρ x v := fun v => rfl
  have hr : r ∈ semilinGroup F V :=
    ⟨fun u v => by rw [hrv, hrv, hrv]; exact map_add (ρ x) u v, RingEquiv.refl F,
      fun c v => by rw [hrv, hrv]; exact map_smul (ρ x) c v⟩
  have hΦ : SemiIso Φ r := ⟨RingEquiv.refl F, fun u v => by rw [hrv, hrv]; exact hiso x u v⟩
  have hpow : ∀ k : ℕ, ∀ v, (r ^ k) v = (ρ x ^ k) v := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ', Equiv.Perm.mul_apply, ih, hrv, pow_succ', Module.End.mul_apply]
  have hrn : r ^ orderOf x = 1 := by
    refine Equiv.ext fun v => ?_
    rw [hpow, ← map_pow, pow_orderOf_eq_one, map_one]
    rfl
  have hcommV : ∀ h ∈ flagKernel ρ (isoCompletion Φ X m), ∀ v, r (ρ h v) = ρ h (r v) := by
    intro h hh v
    have := congrArg (fun z : H => ρ z v) (hcomm h hh)
    simp only [map_mul, Module.End.mul_apply] at this
    rw [hrv, hrv]
    exact this
  obtain ⟨c, hc⟩ := rigid_of_comm_form Φ Sing TS ρ hε hσΦ hdim hTS hTSsing hinj hE1 hroute X m hX0
    hXmono hXTS hK r hr hΦ (orderOf x) hx hrn hcommV
  exact ⟨c, fun v => by rw [← hrv]; exact hc v⟩

end FormGlue

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
