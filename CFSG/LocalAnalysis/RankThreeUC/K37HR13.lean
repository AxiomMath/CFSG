module

public import CFSG.LocalAnalysis.RankThreeUC.K37HRGlue
public import CFSG.RankThree.PartTwo.Census.TripleCoverSuz
public import CFSG.LocalAnalysis.RankThreeUC.K37HDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37H

open CFSG.LocalAnalysis.RankThreeUC.S15.K37
open CFSG.RankThree.PartTwo.Sec4.Census (IsThreeCenterCover)
open CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverSuz
open CFSG.Assembly.RankThreeEven (localRank)
open TauCeti

theorem k37R_four_le_localRank_of_suz_cover {G : Type} [Group G]
    [Finite G] {φ : G →* suzX} (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center G)
    (h3 : 3 ∣ Nat.card φ.ker) : 4 ≤ localRank 3 G :=
  CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverLift.succ_le_localRank_of_lift hφ hker
    Nat.prime_three (by norm_num) h3 (E := suzE)
    (fun x hx y hy => commute_of_mem_suzE hφ hker hx hy)
    (fun e he => exists_lift_of_mem_suzE hφ hker he) tX_ne_one tX_sq
    (fun e he => commute_tX he) (r := 3) card_suzE

theorem k37Rest₁₃_holds : K37Rest₁₃ := by
  intro X _ _ K E S hs hO
  exfalso
  obtain ⟨hq, h3, ⟨e⟩⟩ := hO
  have : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2.1
  have : IsSimpleGroup SporadicName.Suz.Group := e.symm.isSimpleGroup
  obtain ⟨eX⟩ := nonempty_mulEquiv_suzX
  let φ : ↥K →* suzX := (e.trans eX).toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hφ : Function.Surjective φ :=
    (e.trans eX).surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center ↥K := by
    ext g
    simp [φ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  exact k37R_false_of_four_le_localRank hs
    (k37R_four_le_localRank_of_suz_cover hφ hker.le (hker ▸ h3))

end CFSG.LocalAnalysis.RankThreeUC.S15.K37H
