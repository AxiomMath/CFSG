module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitTwoZK
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SplitInStage1Main
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitMain

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Matrix Stage1 SplitIn

variable {G : Type} [Group G] {ε : Eps} {t : G} {L H₀ U Q P : Subgroup G} {a : G} {ψ : V6 → G}
  {p u : Fin 6 → G} {x₀ : G}

theorem levelTwoKillX [Finite G]
    (hG : IsSimpleGroup G)
    (hnab : ∃ x y : G, x * y ≠ y * x) (hS : SetupX ε t L H₀ U Q P a ψ p u x₀) :
    LevelTwoKill t Q (P ⊔ zpowers x₀) := by
  intro W hC hinv hN
  have hT : Terminal t (P ⊔ zpowers x₀) 2 W := Or.inl ⟨hinv, hN⟩
  obtain ⟨Φ, hΦ, hw, hrept, ρ, hρ, hρX, hrepU⟩ := hC.exists_coordB hS
  have hpw : pw W (2 ^ (2 - 2)) = W := by simp only [Nat.sub_self, pow_zero, pw_one]
  rw [hpw] at hΦ
  obtain ⟨g, hodd, b, hb, h, hh, hbh, hhQ, hh2⟩ := hC.exists_conj_decompX hS hρ hG hnab hT
  obtain ⟨i, hi, hhi⟩ := hrepU h hh
  have hinvol := hC.isInvol4_of_repX hS hΦ hρ hh hhQ hh2 hhi
  have hlow := hC.card_centralizer_geX hS hodd
  rw [hbh] at hlow
  have hcW : Nat.card (W ⊓ centralizer ({h} : Set G) : Subgroup G) = fix4c (tilGet ε i) := by
    rw [card_fix_B hΦ hhi, card_fix4]
  rcases (inv_facts ε hi hinvol).2 with hz | hab | hcent
  · subst hz
    exact hC.false_of_zX hS hΦ hw hrept hρ hρX hrepU hb hh hh2 hbh hhi hodd
  ·
    have h2 : 2 * Nat.card (W ⊓ centralizer ({h} : Set G) : Subgroup G) ≤ 256 := by
      refine two_mul_card_le' (t := t) (g := g) (fun B hB hB2 hBc => hS.abelBound hB hB2 hBc)
        hS.shape.mul_self (hC.isPGroup_A.to_le inf_le_left)
        (fun x hx y hy => hC.level.comm x hx.1 y hy.1) ?_ ?_
      · intro d hd
        rw [hbh]
        have h1 := hC.level.comm d hd.1 b hb
        have h2 := mem_centralizer_singleton_iff.1 hd.2
        calc d * (b * h) = b * (d * h) := by rw [← mul_assoc, h1, mul_assoc]
          _ = b * h * d := by rw [h2, mul_assoc]
      · exact fun hu => hC.conj_not_mem_AX hS g hu.1
    omega
  ·
    have hup := hC.card_centralizer_leX hS hΦ hrept hρ hrepU hb hhi
    rw [hcW] at hup
    have : fix4c (tilGet ε i) * (2 * centc ε (tilGet ε i)) < 16384 := by
      calc fix4c (tilGet ε i) * (2 * centc ε (tilGet ε i)) =
          2 * fix4c (tilGet ε i) * centc ε (tilGet ε i) := by ring
        _ < 16384 := hcent
    omega

theorem l9Split
    (ε : Eps) : SplitIn.L9Split ε := by
  intro G _ _ t L H₀ U Q P a ψ p u x₀ hH hK _ hI _
  have hS := SetupX.of_inputs hK hI
  have hst : CFSG.EvenSmallLie.StandardSetting G L := by
    cases ε
    · exact hH.1
    · exact hH.1
  exact l9X hst.simple hst.nonab hS (levelTwoKillX hst.simple hst.nonab hS)

end CFSG.EvenSmallLie.OmegaEight.Chain
