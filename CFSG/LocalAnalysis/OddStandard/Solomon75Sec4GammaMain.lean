module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4GammaConn
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4GammaHub
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4GammaTen
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Center

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG CFSG.GH74.GLS AhatData
open scoped commutatorElement

theorem gamma_two_eq_top_of_ne_nine
    {n : ℕ} (hn : 8 ≤ n) (hn9 : n ≠ 9) {K : Type} [Group K] [Finite K]
    (hK : IsDoubleCoverOfAlt K n) (S : Sylow 2 K) :
    properTwoGenCoreGamma (S : Subgroup K) 2 = ⊤ := by
  rcases (by omega : n = 8 ∨ n = 10 ∨ 11 ≤ n) with rfl | rfl | h
  · exact gamma_two_eq_top_eight hK S
  · obtain ⟨S₀, h⟩ := exists_sylow_gamma_eq_top_ten (CoverSetup.ofCover hK)
    exact gamma_eq_top_of_sylow S h
  · obtain ⟨S₀, h⟩ := exists_sylow_gamma_eq_top_of_pairs h (CoverSetup.ofCover hK)
    exact gamma_eq_top_of_sylow S h

theorem gamma_two_nine
    {K : Type} [Group K] [Finite K] (C : CoverSetup 9 K) (S : Sylow 2 K) :
    ∃ i : Fin 9, properTwoGenCoreGamma (S : Subgroup K) 2 =
        (MulAction.stabilizer (Perm (Fin 9)) i).comap C.ρ ∧
      IsDoubleCoverOfAlt ↥((MulAction.stabilizer (Perm (Fin 9)) i).comap C.ρ) 8 :=
  AhatData.exists_point_gamma_eq_stabilizer C S

theorem rank_three_connected {n : ℕ} (hn : 8 ≤ n) {K : Type} [Group K] [Finite K]
    (hK : IsDoubleCoverOfAlt K n) (S : Sylow 2 K) {E E' : Subgroup K}
    (hE : RankThreeVertex (S : Subgroup K) E) (hE' : RankThreeVertex (S : Subgroup K) E') :
    Relation.ReflTransGen (RankThreeAdj (S : Subgroup K)) E E' := by
  obtain ⟨S₀, y₀, hyS₀, hy₀2, hy₀c, hcomm₀⟩ := exists_hub hn (CoverSetup.ofCover hK)
  obtain ⟨g, hg⟩ := exists_sylow_map_conj_eq S₀ S
  have hnorm : ∀ {x : K}, x ∈ center K → g * x * g⁻¹ ∈ center K := fun hx =>
    (inferInstance : (center K).Normal).conj_mem _ hx g
  refine rankThree_connected_of_hub (y := g * y₀ * g⁻¹) hK.2.1 (center_le_sylow hK S) ?_ ?_ ?_
    ?_ hE hE'
  · rw [hg]
    exact ⟨y₀, hyS₀, rfl⟩
  · calc g * y₀ * g⁻¹ * (g * y₀ * g⁻¹) = g * (y₀ * y₀) * g⁻¹ := by group
      _ = 1 := by rw [hy₀2]; group
  · intro hc
    apply hy₀c
    have := hnorm (x := g * y₀ * g⁻¹) hc
    have h2 := (inferInstance : (center K).Normal).conj_mem _ hc g⁻¹
    simpa [mul_assoc] using h2
  · intro s hs
    rw [hg] at hs
    obtain ⟨s₀, hs₀, rfl⟩ := hs
    have h := hnorm (hcomm₀ s₀ hs₀)
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    convert h using 1
    simp only [commutatorElement_def]
    group

end CFSG.OddStandard.Solomon75
