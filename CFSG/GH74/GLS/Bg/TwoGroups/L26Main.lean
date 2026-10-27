module

public import CFSG.GH74.GLS.Bg.TwoGroups.L26Case

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace L26

@[expose] def InY' (SL SU : Type) [Group SL] [Group SU] (T : Type) [Group T] : Prop :=
  Nonempty (T ≃* _root_.CFSG.GH74.GLS.Bg.TwoGroups.E2 4) ∨ Nonempty (T ≃* SL) ∨
    Nonempty (T ≃* SU) ∨
    ∃ n : ℕ, 1 ≤ n ∧ Nonempty (T ≃* Multiplicative (ZMod (2 ^ n) × ZMod (2 ^ n)))

@[expose] def K2Prop : Prop :=
  ∀ (T : Type) [Group T] [Finite T], IsPGroup 2 T → ∀ α : MulAut T, α ^ 3 = 1 →
    (∀ g : T, α g = g → g = 1) → ∀ A : Subgroup T, A.Normal → (∀ a ∈ A, α a ∈ A) →
    Nonempty (↥A ≃* Multiplicative (ZMod 4 × ZMod 4)) → Subgroup.centralizer (A : Set T) = A →
    A ≠ ⊤ → Nat.card T = 64

@[expose] def H64Prop (SL SU : Type) [Group SL] [Group SU] : Prop :=
  ∀ (T : Type) [Group T] [Finite T], Nat.card T = 64 → ∀ α : MulAut T, orderOf α = 3 →
    (∀ g : T, α g = g → g = 1) → ∀ A : Subgroup T, A.Normal → (∀ a ∈ A, α a ∈ A) →
    Nonempty (↥A ≃* Multiplicative (ZMod 4 × ZMod 4)) → Subgroup.centralizer (A : Set T) = A →
    InY' SL SU T

variable {T : Type} [Group T] [Finite T] {α t : MulAut T} {E : Subgroup T}

theorem Cfg.main (SL SU : Type) [Group SL] [Group SU] (hSL : SFacts SL) (hSU : SFacts SU)
    (hK2 : K2Prop) (hH64 : H64Prop SL SU) (hK3 : K3Prop) :
    ∀ (n : ℕ) (T : Type) [Group T] [Finite T], Nat.card T = n →
      ∀ (α t : MulAut T) (E : Subgroup T), Cfg T α t E → InY' SL SU T := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T _ _ hn α t E cfg
    by_contra hY
    have hEn : E.Normal := ⟨fun n hn g => by
      have := cfg.Ecen n hn g
      have h : g * n * g⁻¹ = n := by rw [← this]; group
      rw [h]; exact hn⟩
    obtain ⟨A, hA, hEA, hmax⟩ := cfg.exists_maxA
    have hA' := hA
    obtain ⟨hAn, hAc, hAi⟩ := hA
    have hAα : ∀ a ∈ A, α a ∈ A := fun a ha => (hAi a ha).2
    have hCA : Subgroup.centralizer (A : Set T) = A :=
      le_antisymm (cfg.centralizer_le A hA' hmax)
        (fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb => hAc b hb a ha)
    have hno : ∀ V : Subgroup T, (∀ v ∈ V, t v ∈ V) → (∀ a ∈ V, ∀ b ∈ V, a * b = b * a) →
        (∀ a ∈ V, a * a = 1) → Nat.card V = 16 → False := by
      intro V hVt hVc hV2 hV16
      have hVtop := cfg.noV V hVt hVc hV2 hV16
      apply hY
      have hcard : Nat.card T = 2 ^ 4 := by
        rw [← Subgroup.card_top (G := T), ← hVtop, hV16]; norm_num
      obtain ⟨e⟩ := elemAbelian_equiv (V := T)
        (fun a b => hVc a (hVtop ▸ Subgroup.mem_top a) b (hVtop ▸ Subgroup.mem_top b))
        (fun a => hV2 a (hVtop ▸ Subgroup.mem_top a)) 4 hcard
      exact Or.inl ⟨e⟩
    have hΩ := cfg.omega1 A hA' hEA hno
    obtain ⟨k, a, hk1, haA, hord, hθ⟩ :=
      homocyclic cfg.p2 α A E hAc hAα (fun a _ => cfg.hfix a) hEA cfg.Ecard cfg.E2 hΩ
    have hAtop : A ≠ ⊤ := by
      intro hAt
      apply hY
      obtain ⟨θ⟩ := hθ
      exact Or.inr (Or.inr (Or.inr ⟨k, hk1, ⟨(Subgroup.topEquiv.symm.trans
        (MulEquiv.subgroupCongr hAt.symm)).trans θ⟩⟩))
    have hk2 : 2 ≤ k := by
      by_contra h
      have hk : k = 1 := by omega
      subst hk
      obtain ⟨θ⟩ := hθ
      have hcardA : Nat.card A = 4 := by
        rw [Nat.card_congr θ.toEquiv, Nat.card_eq_fintype_card]; decide
      have hEA' : E = A := Subgroup.eq_of_le_of_card_ge hEA (by rw [hcardA, cfg.Ecard])
      apply hAtop
      rw [eq_top_iff]
      intro g _
      have hg : g ∈ Subgroup.centralizer (A : Set T) :=
        Subgroup.mem_centralizer_iff.mpr (fun b hb => cfg.Ecen b (hEA' ▸ hb) g)
      rw [hCA] at hg
      exact hg
    have hα1 : α ≠ 1 := by
      intro h1
      have hn : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by rw [cfg.Ecard]; norm_num)
      obtain ⟨e₀, he₀⟩ := exists_ne (1 : E)
      apply he₀
      apply Subtype.ext
      exact cfg.hfix e₀ (by rw [h1]; rfl)
    rcases Nat.lt_or_ge k 3 with hk3 | hk3
    · have hk : k = 2 := by omega
      subst hk
      obtain ⟨θ⟩ := hθ
      have hθ4 : Nonempty (↥A ≃* Multiplicative (ZMod 4 × ZMod 4)) := ⟨θ⟩
      have h64 : Nat.card T = 64 :=
        hK2 T cfg.p2 α cfg.a3 cfg.hfix A hAn hAα hθ4 hCA hAtop
      exact hY (hH64 T h64 α (orderOf_eq_prime cfg.a3 hα1) cfg.hfix A hAn hAα hθ4 hCA)
    · have hEtop : E ≠ ⊤ := by
        intro h
        apply hAtop
        rw [eq_top_iff]
        exact h ▸ hEA
      obtain ⟨E', cfg', hlt⟩ := cfg.quot hEtop
      have hIH := ih (Nat.card (T ⧸ E)) (by rw [← hn]; exact hlt) (T ⧸ E) rfl _ _ E' cfg'
      rcases hIH with h1 | h2 | h3 | ⟨j, hj, h4⟩
      · obtain ⟨ε⟩ := h1
        have hsq : ∀ x : T ⧸ E, x * x = 1 := by
          intro x
          apply ε.injective
          rw [map_mul, map_one]
          exact (by decide : ∀ c : _root_.CFSG.GH74.GLS.Bg.TwoGroups.E2 4, c * c = 1) _
        have h1 : (QuotientGroup.mk (a * a) : T ⧸ E) = 1 := by
          rw [QuotientGroup.mk_mul]; exact hsq _
        have h2 : a * a ∈ E := (QuotientGroup.eq_one_iff _).mp h1
        have h3 : a ^ 4 = 1 := by
          calc a ^ 4 = (a * a) * (a * a) := by simp [pow_succ, mul_assoc]
            _ = 1 := cfg.E2 _ h2
        have h4 : orderOf a ∣ 4 := orderOf_dvd_of_pow_eq_one h3
        rw [hord] at h4
        have : 2 ^ k ∣ 2 ^ 2 := by simpa using h4
        have := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this
        omega
      · obtain ⟨ε⟩ := h2
        exact cfg.case_S A hAc hAα hEA hCA k hk3 a haA hord hθ (SFacts.of_equiv ε hSL) hK3
      · obtain ⟨ε⟩ := h3
        exact cfg.case_S A hAc hAα hEA hCA k hk3 a haA hord hθ (SFacts.of_equiv ε hSU) hK3
      · obtain ⟨ε⟩ := h4
        have habel := cfg.abelian_case j ε
        have hTA : IsA α t ⊤ :=
          ⟨inferInstance, fun a _ b _ => habel a b,
            fun a _ => ⟨Subgroup.mem_top _, Subgroup.mem_top _⟩⟩
        have := hmax ⊤ hTA le_top
        exact hAtop this.symm

end L26

end CFSG.GH74.GLS.Bg.TwoGroups
