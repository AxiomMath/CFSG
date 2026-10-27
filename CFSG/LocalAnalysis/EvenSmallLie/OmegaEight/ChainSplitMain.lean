module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitHigh
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitCone
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitNext

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Matrix Stage1 SplitIn

variable {G : Type} [Group G] {ε : Eps} {t : G} {L H₀ U Q P : Subgroup G} {a : G} {ψ : V6 → G}
  {p u : Fin 6 → G} {x₀ : G}

theorem false_of_configX [Finite G]
    (hG : IsSimpleGroup G) (hnab : ∃ x y : G, x * y ≠ y * x)
    (hS : SetupX ε t L H₀ U Q P a ψ p u x₀) (hL2 : LevelTwoKill t Q (P ⊔ zpowers x₀)) :
    ∀ k (A : Subgroup G), Config t Q (P ⊔ zpowers x₀) k A → False := by
  have hE := endF2 ε
  have hM3 := homEndZero hS.rad
  have hM4 := homEndModZero ε
  suffices h : ∀ d k (A : Subgroup G), Nat.card G - 2 ^ (6 * k) = d →
      Config t Q (P ⊔ zpowers x₀) k A → False
    from fun k A hC => h _ k A rfl hC
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro k A hd hC
    have hterm : Terminal t (P ⊔ zpowers x₀) k A → False := by
      intro hT
      by_cases hk : k = 2
      · subst hk
        rcases hT with ⟨hinv, hN⟩ | ⟨hk3, -⟩
        · exact hL2 A hC hinv hN
        · omega
      · exact hC.false_of_terminal_highX hS hG hnab hT (by have := hC.two_le; omega)
    rcases hC.act with hinv | ⟨hk3, hτ⟩
    · rcases hC.trichotomyX hS hinv with hα | hβ | ⟨g, hg, hc, hl⟩
      · exact hterm (Or.inl ⟨hinv, hα⟩)
      · have htr : ∀ v : V6, ∃ g ∈ Config.Rsub t Q A, cOf ψ t k g = v := fun v => by
          obtain ⟨g, hg, hgQ, hgv⟩ := hβ v
          exact ⟨g, Config.mem_Rsub.2 ⟨hg, hgQ⟩, hgv⟩
        have hC' := hC.next_levelX hS hinv hM3 hM4 hE htr
        have hle : 2 ^ (6 * (k + 1)) ≤ Nat.card G := by
          rw [← hC'.level.card_eq]
          exact Subgroup.card_le_card_group _
        have hlt : 2 ^ (6 * k) < 2 ^ (6 * (k + 1)) :=
          Nat.pow_lt_pow_right (by norm_num) (by omega)
        exact ih _ (by omega) (k + 1) _ rfl hC'
      · exact hC.false_of_coneX hS hinv hg hc hl
    · exact hterm (Or.inr ⟨hk3, hτ⟩)

theorem l9X [Finite G]
    (hG : IsSimpleGroup G) (hnab : ∃ x y : G, x * y ≠ y * x)
    (hS : SetupX ε t L H₀ U Q P a ψ p u x₀) (hL2 : LevelTwoKill t Q (P ⊔ zpowers x₀)) :
    L9 t Q := by
  intro W hQW htW hcard hcomm hnorm
  have hW : Premises t Q W := ⟨hQW, htW, hcard, hcomm, hnorm⟩
  rcases hW.sq_eq_one_or_invX hS (endF2 ε) with h | hinv
  · exact h
  · exfalso
    have hL := hW.level_twoX hS hinv
    have hpw : pw W 2 = Q := by
      have := hL.pw_top hS.rad.card_Q (fun _ hq => hS.rad.Q_mul_self hq) (by norm_num)
      simpa using this
    have hC : Config t Q (P ⊔ zpowers x₀) 2 W := by
      refine ⟨le_rfl, hL, Or.inl hinv, fun x hx w hw => hW.K_conj_memX hS hx hw, ?_⟩
      rw [hpw, hW.normalizer_E_eqX hS]
    exact false_of_configX hG hnab hS hL2 2 W hC

end CFSG.EvenSmallLie.OmegaEight.Chain
