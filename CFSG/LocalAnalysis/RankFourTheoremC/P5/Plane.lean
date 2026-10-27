module

public import CFSG.LocalAnalysis.RankFourTheoremC.P5.Lemma43
public import CFSG.LocalAnalysis.RankFourTheoremC.P5.Cor47
public import CFSG.LocalAnalysis.RankFourTheoremC.P5.Cor46
public import CFSG.LocalAnalysis.RankFourTheoremC.P5.Gen49
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Endgame
import CFSG.LocalAnalysis.RankFourTheoremC.Equivalence

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.P5

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankFourTheoremC CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] {P : Sylow p G}
  {M : Subgroup G} {x : G}

theorem normalizer_ne_top_of_two_group (hS : D1Global G) :
    ∀ Y : Subgroup G, Y ≠ ⊥ → IsPGroup 2 Y → normalizer (Y : Set G) ≠ ⊤ := by
  intro Y hY1 hY2 hN
  have hsimple : IsSimpleGroup G := hS.simple
  have hnormal : Y.Normal := Subgroup.normalizer_eq_top_iff.mp hN
  have hYtop : Y = ⊤ := (hsimple.eq_bot_or_eq_top_of_normal Y).resolve_left hY1
  have hG2 : IsPGroup 2 G := by
    rw [hYtop] at hY2
    exact hY2.of_equiv Subgroup.topEquiv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial (Subgroup.center G) := hG2.center_nontrivial
  have hcen : Subgroup.center G = ⊤ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : Subgroup.center G)
      exact absurd (Subtype.ext (by simpa [h] using hz)) hz1
    · exact h
  obtain ⟨a, b, hab⟩ := hS.nonab
  have ha : a ∈ Subgroup.center G := hcen ▸ Subgroup.mem_top a
  exact hab (Subgroup.mem_center_iff.mp ha b).symm

theorem plane_confinement_p (hp5 : 5 ≤ p) (hK : P5KFacts) (hG : P5Global G)
    (hloc : D1Local p P M) (hType : PTypeHyp p P M)
    (h : CFSG.LocalAnalysis.RankFourTheoremC.IsPPoint p P M x) {A : Subgroup G}
    (hAP : A ≤ (P : Subgroup G)) (hAe : IsElemAbelian p A) (hAc : Nat.card A = p ^ 2)
    (hxA : x ∈ A) {H : Subgroup G} (hH : IsTwoLocal H) (hAH : A ≤ H) : H ≤ M := by
  have hp2 : p ≠ 2 := by omega
  have hab := (shape_p hp5 hK hG hloc hType h).abelian
  have hPM : (P : Subgroup G) ≤ M := sylow_le_of_core hloc
  have hx1 : x ≠ 1 := by
    intro h1
    have := h.elem.2.1
    rw [h1, orderOf_one] at this
    exact hp.out.ne_one this.symm
  have hend := Generic49U3.u3_endgame hp2 (hAP.trans hPM) hAe hAc hxA hx1
    (fun X hX2 hXO hXC => eq_bot_of_two_group_inf_centralizer_p hp5 hK hG hloc hType h hX2 hXO hXC)
    (fun F hF hAF => le_of_coprime_normalized_p hp5 hK hG hloc hType hab hAP hAe hAc
      ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hF) hAF)
    (rank3_absorb_p hG hloc hAP hAe hAc)
    (normalizer_ne_top_of_two_group hG.glob)
    (gen49Cover_p hp5 hK hG hloc hType h hAP hAe hAc hxA)
    (fun Y hY2 hYM hAY hYO => normalizer_le_of_plane_p hp5 hK hG hloc hType h hAP hAe hAc hxA hY2
      hYM hAY hYO)
  obtain ⟨Y, hY1, hY2, rfl⟩ := hH
  exact hend Y hY1 hY2 hAH

end CFSG.LocalAnalysis.RankFourTheoremC.P5
