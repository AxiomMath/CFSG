module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NRm3
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NSt1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7S3

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7n_simpleSec_L1 {s : Setting3 G L} {L1 : Subgroup G} (hL1 : IsCompPre s L1) :
    SimpleSec L1 (M3 s) :=
  simpleSec_of_gl3 (A := L1) (M := M3 s) hL1.1 hL1.2.2.2.2.2

theorem y7n_simpleSec_L1t {c : Ctx7 G L} (hH : F33Hyp c.s c.e) {L1 : Subgroup G}
    (hL1 : IsCompPre c.s L1) : SimpleSec (conjSub c.s.t L1) (M3 c.s) := by
  have hconj : SimpleSec (conjSub c.s.t L1) (conjSub c.s.t (M3 c.s)) :=
    (y7n_simpleSec_L1 (s := c.s) hL1).conj c.s.t
  rwa [y7n_t_norm_M3 c.toCtx5 hH] at hconj

theorem y7n_perm_Lam {c : Ctx7 G L} (hH : F33Hyp c.s c.e) (h7 : c.Upto79) {L1 : Subgroup G}
    (hL1 : IsCompPre c.s L1) {x : G} (hx : x ∈ normalizer (K7 c.s : Set G)) :
    (conjSub x ⁅L1, L1⁆ = ⁅L1, L1⁆ ∧
        conjSub x (conjSub c.s.t ⁅L1, L1⁆) = conjSub c.s.t ⁅L1, L1⁆) ∨
      (conjSub x ⁅L1, L1⁆ = conjSub c.s.t ⁅L1, L1⁆ ∧
        conjSub x (conjSub c.s.t ⁅L1, L1⁆) = ⁅L1, L1⁆) := by
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h71, _⟩, _⟩, _⟩, _⟩, h76⟩, _⟩, _⟩, _⟩ := h7
  have hA : SimpleSec L1 (M3 c.s) := y7n_simpleSec_L1 (s := c.s) hL1
  have hB : SimpleSec (conjSub c.s.t L1) (M3 c.s) := y7n_simpleSec_L1t hH hL1
  have hM2 : IsPGroup 2 (M3 c.s) := y7n_M3_pgroup h71 h76
  have hperm := y7n_perm_of_comp (K := K7 c.s) hA hB hL1.2.2.1 hL1.2.2.2.1
    hL1.2.2.2.2.1 hM2 hx
  have hcm_x : conjSub x ⁅L1, L1⁆ = ⁅conjSub x L1, conjSub x L1⁆ :=
    Subgroup.map_commutator L1 L1 (MulAut.conj x).toMonoidHom
  have hcm_t : conjSub c.s.t ⁅L1, L1⁆ = ⁅conjSub c.s.t L1, conjSub c.s.t L1⁆ :=
    Subgroup.map_commutator L1 L1 (MulAut.conj c.s.t).toMonoidHom
  have hcm_xt : conjSub x (conjSub c.s.t ⁅L1, L1⁆) =
      ⁅conjSub x (conjSub c.s.t L1), conjSub x (conjSub c.s.t L1)⁆ := by
    rw [hcm_t]
    exact Subgroup.map_commutator (conjSub c.s.t L1) (conjSub c.s.t L1)
      (MulAut.conj x).toMonoidHom
  rcases hperm with ⟨hxA, hxB⟩ | ⟨hxA, hxB⟩
  · exact Or.inl ⟨by rw [hcm_x, hxA], by rw [hcm_xt, hxB, hcm_t]⟩
  · exact Or.inr ⟨by rw [hcm_x, hxA, hcm_t], by rw [hcm_xt, hxB]⟩

end CFSG.OddStandard.HigherRank.YamadaG23
