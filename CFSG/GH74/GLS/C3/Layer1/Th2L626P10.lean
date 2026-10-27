module

public import CFSG.GH74.GLS.C3.Layer1.Th2L626P2
public import CFSG.GH74.GLS.C3.Layer1.Th2L626P9
public import CFSG.GH74.GLS.C3.Layer1.Th2L626
public import CFSG.GH74.GLS.C3.Layer1.Th2L626P6

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools

theorem b_lemma626_core_proved
    (I : L626Inputs) : B_lemma626_core := by
  intro G _ _ hG x y K hV hK5 hCx t u J hmax hJ2 _ hnorm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : ∀ c ∈ centralizer ({t} : Set G), c ∈ normalizer (J : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨fun hk => hnorm c hc k hk, fun hk => ?_⟩
    have := hnorm c⁻¹ (inv_mem hc) _ hk
    have e : c⁻¹ * (c * k * c⁻¹) * c⁻¹⁻¹ = k := by group
    rwa [e] at this
  obtain ⟨B, T, cfg⟩ := Cfg626.exists_of_max hmax hN
  by_contra hnt
  have hunb : IsUnbalancingTriple t u J := hmax.1.1
  have hJc : IsPCompIn 2 (centralizer ({t} : Set G)) J := hunb.1.2
  have hR3 : ∀ y : G, orderOf y = 2 → 3 ≤ pRank 2 ↥(centralizer ({y} : Set G)) := fun y hy =>
    TwoThin.rankThreeCentralizers G hG.kproper.1 hG.kproper.2.1
      (by have := hG.pRank_eq_four; omega) y hy
  have hP : IsILo 2 t J := ⟨hunb.1.1, by simpa [oBound] using hR3 t hunb.1.1, hJc⟩
  have hJU2 : InU2 (kBar J) := I.h102 G hG t u J hunb.isLocallyUnbalancing
  have hVN : T ≤ NxK t J := fun c hc => ⟨cfg.hT.le hc, cfg.hN c (cfg.hT.le hc)⟩
  obtain ⟨v, hvQ, hv2, L, hlt, hnontriv⟩ := C3.Layer1.PumpL42.lemma42T hR3 hP cfg.sylow_Q
    cfg.hT.isPGroup hVN cfg.T_le_normalizer_Q
    (fun z hzQ hz2 _ hzT L hlt =>
      cfg.sylow_clause I hG hV hK5 hCx hJ2 hzQ.1 hzQ.2 hz2 hzT hlt) hnt
  by_cases hcomm : ∀ b ∈ B, v * b = b * v
  · have hrk : pRank 2 ↥(centralizer ({v, u} : Set G)) = 4 :=
      pRank_centralizer_pair hG.pRank_eq_four cfg.hB (fun b hb => (hcomm b hb).symm)
        (fun b hb => cfg.B_comm b hb u cfg.huB)
    exact hnontriv
      (trivial_of_commute_unb I hG hV hK5 hCx hunb hv2 hvQ.2 (hcomm u cfg.huB) hrk hlt).1
  · push Not at hcomm
    obtain ⟨y', hy'B, hy'⟩ := hcomm
    have hy'1 : y' ≠ 1 := fun h => hy' (by rw [h]; simp)
    have hy'2 : orderOf y' = 2 :=
      orderOf_eq_prime (by
        rw [sq]
        exact (C3.Layer1.Back.forall_of_isElementaryAbelian cfg.hB.2.1).2 y' hy'B) hy'1
    have hy'T : y' ∈ T := cfg.hBT hy'B
    exact not_nontrivial_of_noncommute I hG hV hK5 hJU2 cfg.sylow_Q hy'2 (hVN hy'T)
      (cfg.T_le_normalizer_Q hy'T) hvQ hv2 hy' hlt hnontriv

end CFSG.GH74.GLS
