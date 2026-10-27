module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.FormCore
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Template

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits CFSG.LieType.ChevTwo.OppCl

section Form

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [Finite V] {H : Type} [Group H]

theorem rigidProp_form (Φ : ReflForm F V) (Sing : V → Prop) (TS : Submodule F V → Prop)
    (ρ : H →* Module.End F V) (P : Equiv.Perm V → Prop) (𝔉 : Subgroup H → ℕ → Submodule F V)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hσΦ : ∀ c, Φ.σ (Φ.σ c) = c)
    (hdim : 4 ≤ Module.finrank F V) (hTS : ∀ U, TS U → Φ.IsTotallyIsotropic U)
    (hTSsing : ∀ U, TS U → ∀ v ∈ U, Sing v) (hinj : Function.Injective ρ) (hE1 : EA1 Φ Sing ρ)
    (hroute : EA2 Φ Sing ρ ∨ 6 ≤ Module.finrank F V)
    (hflag : ∀ Q : Subgroup H, IsPGroup 2 Q → ∃ (X : ℕ → Submodule F V) (m : ℕ), X 0 = ⊥ ∧
      Monotone X ∧ (∀ k, TS (X k)) ∧ 𝔉 Q = isoCompletion Φ X m)
    (hP : ∀ r, P r → SemiIso Φ r) : RigidProp P ρ 𝔉 p := by
  classical
  intro Rh hRhs hRhP hRhp _ Q hQ2 hK hcomm r hr
  obtain ⟨X, m, hX0, hXmono, hXTS, hFQ⟩ := hflag Q hQ2
  have hXTI : ∀ k, Φ.IsTotallyIsotropic (X k) := fun k => hTS _ (hXTS k)
  rw [hFQ] at hK hcomm
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
  obtain ⟨σ, hC⟩ := FormCore.exists_ctx Φ r (hRhs hr) (hP r (hRhP r hr)) ⟨x₀, v₁, hv₁⟩
  have hEich : ∀ x ∈ X (k + 1), ∀ y ∈ Φ.perp (X (k + 1)), ∃ c : F, ∃ h ∈ flagKernel ρ
      (isoCompletion Φ X (k + 1)), ∀ v, ρ h v = v + Φ.β x v • (y + c • x) - Φ.β y v • x := by
    intro x hx y hy
    obtain ⟨c, h, hh⟩ := hE1 x y (hTSsing _ (hXTS (k + 1)) x hx) (hy x hx)
    refine ⟨c, h, ?_, hh⟩
    refine mem_flagKernel_isoCompletion ρ hXmono hXTI (Nat.lt_succ_self k) hx hy
      (a := y + c • x) (add_mem hy (Submodule.smul_mem _ _ (hXTI (k + 1) hx))) (-1) fun v => ?_
    rw [hh]
    simp only [neg_one_mul, neg_smul, sub_eq_add_neg]
  have hE : ∀ x ∈ X (k + 1), x ≠ 0 → ∀ y ∈ Φ.perp (X (k + 1)), ∃ c : F, ∀ v,
      r (v + Φ.β x v • (y + c • x) - Φ.β y v • x) =
        r v + Φ.β x (r v) • (y + c • x) - Φ.β y (r v) • x := by
    intro x hx _ y hy
    obtain ⟨c, h, hh, hρ⟩ := hEich x hx y hy
    refine ⟨c, fun v => ?_⟩
    have := hcomm h hh r hr v
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
    · obtain ⟨h, hh⟩ := hT x 1 (hTSsing _ (hXTS (k + 1)) x hx) (by rw [map_one])
      have hmem : h ∈ flagKernel ρ (isoCompletion Φ X (k + 1)) := by
        refine mem_flagKernel_isoCompletion ρ hXmono hXTI (Nat.lt_succ_self k) hx
          (hXTI (k + 1) hx) (a := x) (hXTI (k + 1) hx) 0 fun w => ?_
        rw [hh]
        simp
      refine hC.line_of_transvection hv₀ fun v => ?_
      have := hcomm h hmem r hr v
      rw [hh, hh] at this
      simpa using this
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
      exact hC.line_of_eichler hσΦ hx0 hy₁ hy₂ (hE x hx hx0 y₁ hy₁P) (hE x hx hx0 y₂ hy₂P)
  obtain ⟨j, hj⟩ := hRhp ⟨r, hr⟩
  have hrj : r ^ p ^ j = 1 := by simpa using congrArg Subtype.val hj
  exact FormCore.rigid_form_core Φ hσΦ hdim (X (k + 1)) hW0 (hXTI (k + 1)) r (hRhs hr)
    (hP r (hRhP r hr)) (p ^ j) ((hp.odd_of_ne_two hp2).pow) hrj hline hE

end Form

end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
