module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainNext

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Matrix Stage1

variable {G : Type*} [Group G]

@[expose] def LevelTwoKill (t : G) (Q P : Subgroup G) : Prop :=
  ∀ A : Subgroup G, Config t Q P 2 A → (∀ x ∈ A, t * x * t⁻¹ = x⁻¹) →
    normalizer ((A ⊔ zpowers t : Subgroup G) : Set G) ≤ A ⊔ (P ⊔ zpowers t) → False

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G}

theorem false_of_config [Finite G] (hG : IsSimpleGroup G)
    (hnab : ∃ x y : G, x * y ≠ y * x) (hS : Setup ε t L U Q P a ψ p) (hE : EndF2 ε)
    (hM3 : HomEndZero ε) (hM4 : HomEndModZero ε) (hF3 : InvFix U Q) (hAb : AbelBound t)
    (hL2 : LevelTwoKill t Q P) :
    ∀ k (A : Subgroup G), Config t Q P k A → False := by
  suffices h : ∀ d k (A : Subgroup G), Nat.card G - 2 ^ (6 * k) = d → Config t Q P k A → False
    from fun k A hC => h _ k A rfl hC
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro k A hd hC
    have hterm : Terminal t P k A → False := by
      intro hT
      by_cases hk : k = 2
      · subst hk
        rcases hT with ⟨hinv, hN⟩ | ⟨hk3, -⟩
        · exact hL2 A hC hinv hN
        · omega
      · exact hC.false_of_terminal_high hS hG hnab hT (by have := hC.two_le; omega) hF3 hAb
    rcases hC.act with hinv | ⟨hk3, hτ⟩
    · rcases hC.dichotomy hS hinv with hα | hβ
      · exact hterm (Or.inl ⟨hinv, hα⟩)
      · have htr : ∀ v : V6, ∃ g ∈ Config.Rsub t Q A, cOf ψ t k g = v := fun v => by
          obtain ⟨g, hg, hgQ, hgv⟩ := hβ v
          exact ⟨g, Config.mem_Rsub.2 ⟨hg, hgQ⟩, hgv⟩
        have hC' := hC.next_level hS hinv hM3 hM4 hE htr
        have hle : 2 ^ (6 * (k + 1)) ≤ Nat.card G := by
          rw [← hC'.level.card_eq]
          exact Subgroup.card_le_card_group _
        have hlt : 2 ^ (6 * k) < 2 ^ (6 * (k + 1)) :=
          Nat.pow_lt_pow_right (by norm_num) (by omega)
        exact ih _ (by omega) (k + 1) _ rfl hC'
    · exact hterm (Or.inr ⟨hk3, hτ⟩)

theorem l9_of [Finite G] (hG : IsSimpleGroup G)
    (hnab : ∃ x y : G, x * y ≠ y * x) (hS : Setup ε t L U Q P a ψ p) (hE : EndF2 ε)
    (hM3 : HomEndZero ε) (hM4 : HomEndModZero ε) (hF3 : InvFix U Q) (hAb : AbelBound t)
    (hL2 : LevelTwoKill t Q P) : L9 t Q := by
  intro W hQW htW hcard hcomm hnorm
  have hW : Premises t Q W := ⟨hQW, htW, hcard, hcomm, hnorm⟩
  rcases hW.sq_eq_one_or_inv hS hE with h | hinv
  · exact h
  · exfalso
    have hL := hW.level_two hS hinv
    have hpw : pw W 2 = Q := by
      have := hL.pw_top hS.rad.card_Q (fun _ hq => hS.rad.Q_mul_self hq) (by norm_num)
      simpa using this
    have hC : Config t Q P 2 W := by
      refine ⟨le_rfl, hL, Or.inl hinv, fun x hx w hw => hW.P_conj_mem hS hx hw, ?_⟩
      rw [hpw, hW.normalizer_E_eq hS]
    exact false_of_config hG hnab hS hE hM3 hM4 hF3 hAb hL2 2 W hC

end CFSG.EvenSmallLie.OmegaEight.Chain
