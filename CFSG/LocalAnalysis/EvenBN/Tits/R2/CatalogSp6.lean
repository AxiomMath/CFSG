module

public import CFSG.LocalAnalysis.EvenBN.Tits.R2.CatalogDefs
public import CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.RankThree.PartTwo.Census.Carrier.Sp6TwoCertInputs
import CFSG.Certificates.Kernel.Sp6Two.Sound
import Certificates.Data.Kernel.Sp6TwoT
import Certificates.Kernel.Sp6Two.Final
import Certificates.Kernel.Sp6Two.Rec
import Certificates.Kernel.Sp6Two.Idx4
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.GH74.KGroups.U33

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.R2

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_statedScalars statedProjCongr)

theorem nonempty_mulEquiv_H6_of_lieModel {K : Type} [Group K] (h : LieModel K .PSp 3 2 1) :
    Nonempty (K ≃* H6) := by
  have hm : StatedClassicalModel K .PSp 3 2 1 := by
    rcases h with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h
    all_goals exact absurd h0 (by norm_num)
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : F ≃+* ZMod 2 :=
    (CFSG.ClassicalModels.finiteFieldEquivGaloisField F 2 1 one_pos hcard).trans
      (GaloisField.equivZmodP 2).toRingEquiv
  exact ⟨e.trans ((statedProjCongr (glCongr φ)
    (CFSG.ClassicalInvolution.Upgrade.glCongr_statedSp φ 3) (glCongr_statedScalars φ)).trans
      ((QuotientGroup.quotientMulEquivOfEq
        CFSG.RankThree.PartTwo.Census.statedScalars_subgroupOf_sp6).trans
          QuotientGroup.quotientBot))⟩

end CFSG.LocalAnalysis.EvenBN.Tits.R2
