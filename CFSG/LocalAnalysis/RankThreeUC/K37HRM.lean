module

public import CFSG.LocalAnalysis.RankThreeUC.K37HRB
import CFSG.Monster.SteinbergMBXGeneratedPerfectCover
public import CFSG.Monster.SteinbergMY443NativeSurjective
public import CFSG.Sporadic.Bridge.MonsterModels

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37H

open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.RankThree.PartOne
open CFSG.Open CFSG.Monster.Generated CFSG.Monster.B CFSG.Monster.Existence CFSG.YGroups.Y443

theorem k37R_coverRankFour_Gmat
    : K37RCoverRankFour ↥Gmat := by
  have hC : K37RCoverRankFour Cbar := k37R_coverRankFour_B.of_mulEquiv phiB
  have hperf : commutator Cbar = ⊤ := by
    obtain ⟨-, -, hs, -⟩ := short_centralizer_generated_quotient_simple
    haveI : IsSimpleGroup Cbar := hs
    exact k37R_commutator_eq_top_of_simple GeneratedPerfectCover.Cbar_exists_ne_comm
  let κ : ↥(Cgen.subgroupOf Gmat) ≃* ↥Cgen := Subgroup.subgroupOfEquivOfLe Cgen_le_Gmat
  let φ₀ : ↥(Cgen.subgroupOf Gmat) →* Cbar := (QuotientGroup.mk' Zstar).comp κ.toMonoidHom
  have hφ₀ : Function.Surjective φ₀ := (QuotientGroup.mk'_surjective Zstar).comp κ.surjective
  have hk : φ₀.ker ≤ Subgroup.center ↥(Cgen.subgroupOf Gmat) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : κ x ∈ Zstar := (QuotientGroup.eq_one_iff _).1 (by simpa [φ₀] using hx)
    have h2 : κ x ∈ Subgroup.center ↥Cgen := Zstar_le_center h1
    rw [Subgroup.mem_center_iff]
    intro g
    apply κ.injective
    simpa using Subgroup.mem_center_iff.1 h2 (κ g)
  exact hC.of_section (M := Cgen.subgroupOf Gmat) hperf φ₀ hφ₀ hk

theorem k37R_coverRankFour_M
    {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (e : T ≃* CFSG.Blueprint.NativeSporadic.M) : K37RCoverRankFour T := by
  have eM : T ≃* MonsterY443Derived :=
    e.trans CFSG.Blueprint.NativeSporadic.MonsterModel.y443DerivedEquivOpen
  have hsimple : IsSimpleGroup MonsterY443Derived := MulEquiv.isSimpleGroup eM.symm
  have hinj : Function.Injective fM := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (fM.ker) with h | h
    · exact h
    · exact absurd h fM_ker_ne_top
  have hsurj : Function.Surjective fM :=
    ((y443_native_surjective_homomorphism).1 fM fM_isFM).1
  exact k37R_coverRankFour_Gmat.of_mulEquiv (eM.trans (MulEquiv.ofBijective fM ⟨hinj, hsurj⟩))

end CFSG.LocalAnalysis.RankThreeUC.S15.K37H
