module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OFactsF1Cent
public import CFSG.LieType.Multipliers.U43
public import Certificates.Certificate442353
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.LieType.Multipliers.U43

theorem x0_centTwoPlus (Q₁ Q₂ : Subgroup X₀)
    (hQ₁ : Nonempty (↥Q₁ ≃* QuaternionGroup 2)) (hQ₂ : Nonempty (↥Q₂ ≃* QuaternionGroup 2))
    (hcomm : ⁅Q₁, Q₂⁆ = ⊥) (hcard : Nat.card ↥(Q₁ ⊔ Q₂) = 32) :
    IsPGroup 2 (Subgroup.centralizer (((Q₁ ⊔ Q₂ : Subgroup X₀)) : Set X₀)) :=
  (IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)).to_le
    (Certificates.certificate442353.1 Q₁ Q₂ hQ₁ hQ₂ hcomm hcard)

theorem u4CentTwoPlus_of_cert : U4CentTwoPlus := by
  intro V _ _ hV Q1 Q2 hQ1 hQ2 hcomm hcard
  obtain ⟨e⟩ := nonempty_mulEquiv_X₀ hV
  let Q1' : Subgroup X₀ := Q1.map e.toMonoidHom
  let Q2' : Subgroup X₀ := Q2.map e.toMonoidHom
  have hQ1' : Nonempty (↥Q1' ≃* QuaternionGroup 2) := by
    obtain ⟨e1⟩ := hQ1
    exact ⟨(e.subgroupMap Q1).symm.trans e1⟩
  have hQ2' : Nonempty (↥Q2' ≃* QuaternionGroup 2) := by
    obtain ⟨e2⟩ := hQ2
    exact ⟨(e.subgroupMap Q2).symm.trans e2⟩
  have hcomm' : ⁅Q1', Q2'⁆ = ⊥ := by
    rw [show Q1' = Q1.map e.toMonoidHom from rfl,
      show Q2' = Q2.map e.toMonoidHom from rfl,
      ← Subgroup.map_commutator, hcomm, Subgroup.map_bot]
  have hcard' : Nat.card ↥(Q1' ⊔ Q2') = 32 := by
    rw [show Q1' = Q1.map e.toMonoidHom from rfl,
      show Q2' = Q2.map e.toMonoidHom from rfl,
      ← Subgroup.map_sup]
    rw [← Nat.card_congr (Subgroup.equivMapOfInjective (Q1 ⊔ Q2) e.toMonoidHom
      e.injective).toEquiv]
    exact hcard
  have hcent := x0_centTwoPlus Q1' Q2' hQ1' hQ2' hcomm' hcard'
  have hQmap : (Q1 ⊔ Q2).map e.toMonoidHom = Q1' ⊔ Q2' := by
    rw [Subgroup.map_sup]
  have hmapLe : (Subgroup.centralizer (((Q1 ⊔ Q2 : Subgroup V)) : Set V)).map e.toMonoidHom ≤
      Subgroup.centralizer (((Q1' ⊔ Q2' : Subgroup X₀)) : Set X₀) := by
    have hmap := Subgroup.map_centralizer_le_centralizer_image
      (((Q1 ⊔ Q2 : Subgroup V)) : Set V) e.toMonoidHom
    have himg : e.toMonoidHom '' (((Q1 ⊔ Q2 : Subgroup V)) : Set V) =
        (((Q1' ⊔ Q2' : Subgroup X₀)) : Set X₀) := by
      change ((((Q1 ⊔ Q2).map e.toMonoidHom : Subgroup X₀) : Set X₀)) =
        (((Q1' ⊔ Q2' : Subgroup X₀)) : Set X₀)
      rw [hQmap]
    rwa [himg] at hmap
  have hmapP : IsPGroup 2 ((Subgroup.centralizer (((Q1 ⊔ Q2 : Subgroup V)) : Set V)).map
      e.toMonoidHom) := hcent.to_le hmapLe
  have hVcent : IsPGroup 2 (Subgroup.centralizer (((Q1 ⊔ Q2 : Subgroup V)) : Set V)) :=
    hmapP.of_equiv (Subgroup.equivMapOfInjective _
      e.toMonoidHom e.injective).symm
  simpa using hVcent

theorem u43CentTwoPlus_of_cert : U43CentTwoPlus :=
  u43CentTwoPlus_of u4CentTwoPlus_of_cert

end CFSG.OddStandard.SmallF3.Omega
