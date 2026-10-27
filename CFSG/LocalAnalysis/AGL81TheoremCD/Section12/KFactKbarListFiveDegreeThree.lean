module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactKbarListFiveTransport
import CFSG.RankThree.PartTwo.Sec10.Item1015Proof
import CFSG.Adapters.LieModelSimple
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KbarListFive

open CFSG.Open CFSG.Blueprint Subgroup
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo

theorem false_of_psl_three_prime {K S : Type} [Group K] [Finite K] [Group S] [Finite S]
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : CFSG.IsQuasisimple K)
    (e : K ⧸ center K ≃* S) (hK : CFSG.LocalAnalysis.RankThreeUC.AGL81C.IsPSLType 3 (ZMod p) K)
    {E : Subgroup (MulAut S)} (hE : IsElemAbelian 3 E) (hc : Nat.card E = 27) : False := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a⟩ := hK
  let b := a.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3
    (ZMod p))
  have hm : StatedClassicalModel K .PSL 3 p 1 :=
    ⟨⟨hp, le_rfl, by norm_num, by simp, by simp⟩,
      ZMod p, inferInstance, inferInstance, by simp, ⟨b⟩⟩
  have : IsSimpleGroup K := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hm
  let ψ : S ≃* projectiveSL 3 (ZMod p) :=
    ((equiv_of_centerQuotient hq e).symm.trans a).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 (ZMod p))
  have hE' := CFSG.SectionRank.isElemAbelian_map hE (MulAut.congr ψ).toMonoidHom
  have h9 := Sec10.Item1015Proof.card_le_nine_of_mulAut_projectiveSL_three hp (by omega)
    (by simp : Nat.card (ZMod p) = p ^ 1) (by norm_num : ¬ 3 ∣ (1 : ℕ))
    (E.map (MulAut.congr ψ).toMonoidHom) hE'
  rw [Subgroup.card_map_of_injective (MulAut.congr ψ).injective, hc] at h9
  omega

theorem false_of_psu_three_prime {K S : Type} [Group K] [Finite K] [Group S] [Finite S]
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : CFSG.IsQuasisimple K)
    (e : K ⧸ center K ≃* S) (hK : StatedClassicalModel K .PSU 3 p 1)
    {E : Subgroup (MulAut S)} (hE : IsElemAbelian 3 E) (hc : Nat.card E = 27) : False := by
  have : IsSimpleGroup K := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hK
  obtain ⟨-, F, instF, instFin, hF, ⟨a⟩⟩ := hK
  let h : UnitaryFieldData p 1 F := ⟨hp, le_rfl, by simpa using hF⟩
  let ψ : S ≃* unitaryPSU h 3 :=
    ((equiv_of_centerQuotient hq e).symm.trans a).trans (unitaryPSUEquiv h (by norm_num)).symm
  have hE' := CFSG.SectionRank.isElemAbelian_map hE (MulAut.congr ψ).toMonoidHom
  have h9 := Sec10.Item1015Proof.card_le_nine_of_mulAut_unitaryPSU
    (h := h) (by omega) (by simpa using (show 2 < p by omega)) (by norm_num : ¬ 3 ∣ (1 : ℕ))
    (E.map (MulAut.congr ψ).toMonoidHom) hE'
  rw [Subgroup.card_map_of_injective (MulAut.congr ψ).injective, hc] at h9
  omega

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KbarListFive

end
