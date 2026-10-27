module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Trich
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Tr

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y7a_isSylowIn_map_subtype_three {V : Subgroup G} (P : Sylow 3 ↥V) :
    IsSylowIn 3 V ((P : Subgroup ↥V).map V.subtype) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨Subgroup.map_subtype_le _, P.isPGroup'.map V.subtype, ?_⟩
  have h := Subgroup.relIndex_map_map_of_injective (f := V.subtype)
    (P : Subgroup ↥V) (⊤ : Subgroup ↥V) V.subtype_injective
  rw [Subgroup.map_top V.subtype, Subgroup.range_subtype, Subgroup.relIndex_top_right] at h
  rw [h]
  exact P.not_dvd_index

theorem y7a_dichotomy (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    (∀ w ∈ c.s.fr.A ⊔ C0 c.e, w ∉ c.s.fr.A ⊔ V1 c.e →
        w ∈ y7aO (y7aX c) (V1 c.e) c.s.t) ∨
      (∀ w ∈ y6Um c.s.fr.A (V1 c.e) c.s.fr.z c.s.t, w ∉ y7aO (y7aX c) (V1 c.e) c.s.t) := by
  obtain ⟨P₃, hP₃⟩ : ∃ P₃ : Subgroup G, IsSylowIn 3 (normIn L c.s.fr.A) P₃ :=
    ⟨_, y7a_isSylowIn_map_subtype_three (default : Sylow 3 ↥(normIn L c.s.fr.A))⟩
  have hNLA : P₃ ≤ normIn L c.s.fr.A := hP₃.1
  have hQX : P₃ ≤ y7aX c := fun k hk =>
    y7a_Y_le_X c hH (s5_NLA_le_Y c.toCtx5 hH (hNLA hk))
  have hQt : ∀ k ∈ P₃, k * c.s.t = c.s.t * k := by
    intro k hk
    have hmem : c.s.t ∈ centralizer (L : Set G) := c.s.t_mem
    rw [Subgroup.mem_centralizer_iff] at hmem
    exact hmem k (hNLA hk).1
  have h2c := hH.hLF.fact18.1.2.2 P₃ hP₃
  exact y7a_trichotomy (c.y7acfg hH) inf_le_left inf_le_right hQX hQt h2c.1 h2c.2.1
    (y7a_trans_Up c hH hF)

end CFSG.OddStandard.HigherRank.YamadaG23
