module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3AFix
import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.LocalAnalysis.GLTheoremA.ExcClubList

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem kdClub_of_iso_quasisimple {Y : Type} [Group Y] [Finite Y] {J : Subgroup Y}
    (hQ : CFSG.Open.IsQuasisimple (PQuot 3 J)) {G : Type} [Group G] (eJ : G ≃* J)
    (hG : CFSG.Open.IsQuasisimple G) (hZ : ∀ z ∈ Subgroup.center G, z ^ 2 = 1)
    (hcat : catalogIs (G ⧸ Subgroup.center G) clubIndex) :
    Nat.card (Subgroup.center (PQuot 3 J)) = 1 ∧ catalogIs (PSimple 3 J) clubIndex := by
  have hJq : CFSG.Open.IsQuasisimple ↥J :=
    CFSG.HardMathSupport.Solomon.Coordinator.isQuasisimple_open_of_mulEquiv eJ.symm hG
  have hnt : GLAPPrimeCore 3 ↥J ≠ ⊤ := by
    intro htop
    have e := QuotientGroup.quotientMulEquivOfEq htop
    haveI : Subsingleton (↥J ⧸ (⊤ : Subgroup ↥J)) := QuotientGroup.subsingleton_quotient_top
    have hsub : Subsingleton (PQuot 3 J) := e.toEquiv.subsingleton
    have hntriv : Nontrivial (PQuot 3 J) := by
      have := hQ.2.toNontrivial
      exact (QuotientGroup.mk'_surjective (Subgroup.center (PQuot 3 J))).nontrivial
    exact not_subsingleton _ hsub
  have hZJ : Nat.Coprime 3 (Nat.card (Subgroup.center ↥J)) := by
    have hp : IsPGroup 2 ↥(Subgroup.center ↥J) := by
      intro z
      refine ⟨1, ?_⟩
      have hz := hZ (eJ.symm (z : J)) (by
        have := Subgroup.map_center_eq eJ.symm
        rw [← this]
        exact ⟨_, z.2, rfl⟩)
      apply Subtype.ext
      apply eJ.symm.injective
      simpa [pow_one] using hz
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hP1 : GLAPPrimeCore 3 ↥J = Subgroup.center ↥J :=
    le_antisymm (le_center_of_normal_of_isQuasisimple hJq inferInstance hnt)
      (CFSG.le_pPrimeCore_of_normal_coprime inferInstance hZJ)
  let e1 : PQuot 3 J ≃* ↥J ⧸ Subgroup.center ↥J := QuotientGroup.quotientMulEquivOfEq hP1
  let e2 : (↥J ⧸ Subgroup.center ↥J) ≃* G ⧸ Subgroup.center G :=
    QuotientGroup.congr _ _ eJ.symm (Subgroup.map_center_eq eJ.symm)
  let e12 : PQuot 3 J ≃* G ⧸ Subgroup.center G := e1.trans e2
  have hperf : Group.IsPerfect G := (Group.isPerfect_def).2 hG.1
  have hc : Subgroup.center (PQuot 3 J) = ⊥ := by
    have h1 := Subgroup.map_center_eq e12
    rw [Group.IsPerfect.center_quotient_center_eq_bot G] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e12.injective).1 h1
  refine ⟨by rw [hc]; exact Subgroup.card_bot, ?_⟩
  have e3 : PSimple 3 J ≃* G ⧸ Subgroup.center G :=
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans e12
  exact (catalogIs_congr e3).2 hcat

end CFSG.LocalAnalysis.GLTheoremA
