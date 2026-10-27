module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32NonabPlumbing

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem sz32_hFd (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G) (hNonab : KFactNonabF5)
    (hc : PointConfig IsSz32Type G 5 P M x J) {a c y : G} (hP : Sz32Struct P x J a c y)
    (hL : Sz32Lines P x (a ^ 5)) (hZ : Sz32ZFacts P M x (a ^ 5)) {U : Subgroup G}
    (hU : Sz32Plane P x a c y U)
    (hC : ∀ u ∈ U, u ∉ Subgroup.zpowers x → Subgroup.centralizer ({u} : Set G) ≤ M) :
    ∀ S R₀ : Subgroup G, EndgameData 5 M U S R₀ → ∀ F : Subgroup G,
      IsSylowOf 5 F (Subgroup.normalizer (S : Set G)) → U ≤ F → F ≤ M → CFSG.Open.pRank 5 F ≤ 2 →
        IsMulCommutative F ∧ ∀ g : G, (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ≤ F →
          (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers x := by
  intro S R₀ hE F hFH hUF hFM hrk
  have hinfo := sz32_F_info hc hP hL hZ hU hFH.isPGroup hUF hrk
  refine ⟨?_, hinfo.wc⟩
  by_contra hnab
  exact sz32_nonab_false hS hU0 hNonab hc hU.abs.elem hU.abs.card hU.abs.mem hC hE hFH hUF hFM
    hinfo hnab

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
