module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.NormalChain

public section

open CFSG.Open

namespace CFSG.PreuniquenessRankFour.Helpers

universe u

theorem maximal_normal_abelian_pSubgroup_centralizer_eq
    {source : Type u} [Group source] [Finite source]
    (prime : ℕ) [Fact prime.Prime] (hsource : IsPGroup prime source)
    (abelian : Subgroup source) [abelian.Normal] (habelian : IsMulCommutative abelian)
    (hmaximal : ∀ extension : Subgroup source, abelian ≤ extension → extension.Normal →
      IsMulCommutative extension → extension = abelian) :
    Subgroup.centralizer (abelian : Set source) = abelian := by
  let centralizer := Subgroup.centralizer (abelian : Set source)
  let : centralizer.Normal := inferInstance
  let quotientMap := QuotientGroup.mk' abelian
  let image := centralizer.map quotientMap
  let : image.Normal := (inferInstance : centralizer.Normal).map quotientMap
    (QuotientGroup.mk'_surjective abelian)
  have hab : abelian ≤ centralizer := by
    let : IsMulCommutative abelian := habelian
    exact Subgroup.le_centralizer _
  by_contra hnotEqual
  have himageNontrivial : image ≠ ⊥ := by
    intro hbot
    have hcontained := centralizer.map_eq_bot_iff.mp hbot
    rw [QuotientGroup.ker_mk'] at hcontained
    exact hnotEqual (le_antisymm hcontained hab)
  obtain ⟨line, hline, _, hlineCard, hlineNormal⟩ :=
    normal_pSubgroup_has_central_prime_line prime (hsource.to_quotient abelian) image himageNontrivial
  let : line.Normal := hlineNormal
  let extension := line.comap quotientMap
  let : extension.Normal := inferInstance
  have habExtension : abelian ≤ extension := by
    intro member hmember
    change quotientMap member ∈ line
    rw [show quotientMap member = 1 from (QuotientGroup.eq_one_iff _).mpr hmember]
    exact line.one_mem
  have hextensionCentral : extension ≤ centralizer := by
    have hbound := Subgroup.comap_mono (f := quotientMap) hline
    have hpreimage : image.comap quotientMap = centralizer := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hab]
    exact hpreimage ▸ hbound
  let hom := quotientMap.subgroupMap extension
  let : IsCyclic line := isCyclic_of_prime_card hlineCard
  let : IsCyclic (extension.map quotientMap) :=
    Subgroup.isCyclic_of_le (Subgroup.map_comap_le quotientMap line)
  have hkernelCentral : hom.ker ≤ Subgroup.center extension := by
    intro member hmember
    have hzero := congrArg (fun value : extension.map quotientMap => (value : source ⧸ abelian)) hmember
    have hmemberAbelian : (member : source) ∈ abelian := (QuotientGroup.eq_one_iff _).mp hzero
    apply Subgroup.mem_center_iff.mpr
    intro other
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hextensionCentral other.property) member hmemberAbelian).symm
  have hextensionAbelian : IsMulCommutative extension :=
    hom.isMulCommutative_of_isCyclic_of_ker_le_center hkernelCentral
  have hequal := hmaximal extension habExtension (inferInstance : extension.Normal) hextensionAbelian
  have hlineBot : line = ⊥ := by
    have hmap : extension.map quotientMap = line :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective abelian) line
    rw [hequal] at hmap
    have hbot : abelian.map quotientMap = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hmap.symm.trans hbot
  rw [hlineBot, Subgroup.card_bot] at hlineCard
  exact (Fact.out : prime.Prime).ne_one hlineCard.symm

theorem exists_maximal_normal_abelian_overgroup
    {source : Type u} [Group source] [Finite source]
    (abelian : Subgroup source) [abelian.Normal] (habelian : IsMulCommutative abelian) :
    ∃ maximal : Subgroup source, abelian ≤ maximal ∧ maximal.Normal ∧ IsMulCommutative maximal ∧
      ∀ extension : Subgroup source, maximal ≤ extension → extension.Normal →
        IsMulCommutative extension → extension = maximal := by
  classical
  let admissible := fun subgroup : Subgroup source => subgroup.Normal ∧ IsMulCommutative subgroup
  obtain ⟨maximal, hcontained, hmaximal⟩ :=
    Finite.exists_le_maximal (show admissible abelian from ⟨inferInstance, habelian⟩)
  refine ⟨maximal, hcontained, hmaximal.1.1, hmaximal.1.2, ?_⟩
  intro extension hextension hnormal hextensionAbelian
  exact le_antisymm (hmaximal.2 ⟨hnormal, hextensionAbelian⟩ hextension) hextension

end CFSG.PreuniquenessRankFour.Helpers
