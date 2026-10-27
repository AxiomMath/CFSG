module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Lemma42PSL2
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Lemma42U3
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1Red

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
  {J : Subgroup G}

theorem u3_lemma42 (hS : Setting G) (hClass : GenericComponentClass G)
    (hSpor : GL83GenericListExclusionRedSpor G) (hc : U3Config G p P M x J)
    (hfus : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) ∧ U3LineWC x (P : Subgroup G)) :
    ∀ a ∈ u3U0 P x J, a ∉ Subgroup.zpowers x → Subgroup.centralizer ({a} : Set G) ≤ M := by
  intro a ha hax
  by_contra hbad
  have hgen := u3_bad_isGenericPoint hS hc hfus.1 ha hax hbad
  have hPa := u3_P_le_centralizer_of_mem_U0 hc hfus.1 ha
  haveI : Fact p.Prime := ⟨hc.prime⟩
  obtain ⟨Ja, hJaC, hCJa, hperf, hlt, hmin, hnot, Q, hQ, ψ, hψ, hker, hlist, hFi⟩ :=
    hClass p hc.sigma P M hc.core hc.fail hc.larger a hgen hc.five
  have hP3 := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).2
  have hPnab : ¬ IsMulCommutative (P : Subgroup G) := by
    intro hcomm
    obtain ⟨-, -, hTnab, -⟩ := u3_T_structure hc
    refine hTnab ⟨⟨fun s t => ?_⟩⟩
    have hle : u3T P x J ≤ (P : Subgroup G) := inf_le_left.trans inf_le_left
    have := hcomm.is_comm.comm ⟨s.1, hle s.2⟩ ⟨t.1, hle t.2⟩
    exact Subtype.ext (congrArg (Subtype.val : ↥(P : Subgroup G) → G) this)
  have key : (∃ _ : Fact p.Prime, Nonempty (Q ≃* PSL(2, GaloisField p 2))) ∨ IsU3Pred p Q := by
    rcases hlist with hE | ⟨h5, hSz⟩
    · rcases hE with hpsl | hu | ⟨h5, h⟩ | ⟨h11, h⟩
      · exact Or.inl hpsl
      · exact Or.inr hu
      · exact Or.inl (hSpor p hc.sigma P M hc.core hc.fail hc.larger a hgen hc.five Ja hJaC hCJa
          hperf hlt hmin hnot Q ψ hψ hker (Or.inl ⟨h5, h⟩) hFi)
      · exact Or.inl (hSpor p hc.sigma P M hc.core hc.fail hc.larger a hgen hc.five Ja hJaC hCJa
          hperf hlt hmin hnot Q ψ hψ hker (Or.inr (Or.inl ⟨h11, h⟩)) hFi)
    · exact Or.inl (hSpor p hc.sigma P M hc.core hc.fail hc.larger a hgen hc.five Ja hJaC hCJa
        hperf hlt hmin hnot Q ψ hψ hker (Or.inr (Or.inr ⟨h5, hSz⟩)) hFi)
  rcases key with ⟨_, hpsl⟩ | hu
  · exact u3_psl2_second_false hc.five hP3 hPnab hPa hJaC hCJa ψ hψ hker hpsl
  · exact u3_second_u3_false hc hfus ha hax
      ⟨hc.sigma, hc.core, hc.fail, hc.larger, hgen, hc.five, hJaC, hCJa, hperf, hlt, hmin, hnot,
        ⟨Q, inferInstance, ψ, hψ, hker, hu⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
