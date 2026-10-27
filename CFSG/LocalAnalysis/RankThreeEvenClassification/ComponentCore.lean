module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SubnormalCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.QuasisimpleCore

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

inductive NormalChain {G : Type u} [Group G] : Subgroup G → Subgroup G → Prop
  | refl (subgroup : Subgroup G) : NormalChain subgroup subgroup
  | extend {smaller middle larger : Subgroup G} : NormalChain smaller middle →
      middle ≤ larger → (middle.subgroupOf larger).Normal → NormalChain smaller larger

theorem NormalChain.trans {G : Type u} [Group G] {smaller middle larger : Subgroup G}
    (hfirst : NormalChain smaller middle) (hsecond : NormalChain middle larger) :
    NormalChain smaller larger := by
  induction hsecond with
  | refl => exact hfirst
  | extend _ hle hnormal ih => exact NormalChain.extend ih hle hnormal

theorem normalChain_of_subnormal {G : Type u} [Group G] {smaller larger : Subgroup G}
    (hsubnormal : IsSubnormal smaller larger) : NormalChain smaller larger := by
  induction hsubnormal with
  | refl subgroup => exact NormalChain.refl subgroup
  | step hle hnormal _ ih =>
    exact (NormalChain.extend (NormalChain.refl _) hle hnormal).trans ih

theorem NormalChain.le {G : Type u} [Group G] {smaller larger : Subgroup G}
    (hchain : NormalChain smaller larger) : smaller ≤ larger := by
  induction hchain with
  | refl => exact le_rfl
  | extend _ hle _ ih => exact ih.trans hle

theorem quasisimple_centralizes_own_core {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (subgroup : Subgroup G)
    (hquasi : IsQuasisimple subgroup) :
    subgroup ≤ Subgroup.centralizer (pCoreOf prime subgroup : Set G) := by
  intro element helement
  apply Subgroup.mem_centralizer_iff.mpr
  intro other hother
  obtain ⟨preimage, hpreimage, rfl⟩ := Subgroup.mem_map.mp hother
  have hcenter := quasisimple_pCore_le_center subgroup hquasi prime hprime hpreimage
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hcenter ⟨element, helement⟩).symm

theorem perfect_core_centralization_extend {G : Type u} [Group G]
    (prime : ℕ) (perfectSubgroup middle larger : Subgroup G)
    (hperfect : Group.IsPerfect perfectSubgroup) (hperfectLe : perfectSubgroup ≤ middle)
    (hle : middle ≤ larger) (hnormal : (middle.subgroupOf larger).Normal)
    (hcentral : perfectSubgroup ≤ Subgroup.centralizer (pCoreOf prime middle : Set G)) :
    perfectSubgroup ≤ Subgroup.centralizer (pCoreOf prime larger : Set G) := by
  apply perfect_centralizes_of_commutator_central perfectSubgroup (pCoreOf prime larger) hperfect
  have hcoreNormal : ((pCoreOf prime larger).subgroupOf larger).Normal := by
    have heq : (pCoreOf prime larger).subgroupOf larger = pCore prime larger :=
      Subgroup.comap_map_eq_self_of_injective larger.subtype_injective _
    rw [heq]
    exact pCore_normal larger prime
  have hcoreLe := pCoreOf_le prime larger
  have hmiddleNormalizes := (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hnormal
  have hcoreNormalizes := (Subgroup.normal_subgroupOf_iff_le_normalizer hcoreLe).mp hcoreNormal
  let intersection := middle ⊓ pCoreOf prime larger
  have hintersectionLe : intersection ≤ middle := inf_le_left
  have hintersectionNormal : (intersection.subgroupOf middle).Normal := by
    apply (Subgroup.normal_subgroupOf_iff hintersectionLe).mpr
    intro element conjugator helement hconjugator
    exact ⟨middle.mul_mem (middle.mul_mem hconjugator helement.1)
      (middle.inv_mem hconjugator),
      Subgroup.le_normalizer_iff.mp hcoreNormalizes conjugator (hle hconjugator)
        element helement.2⟩
  have hintersectionPGroup : IsPGroup prime intersection :=
    (pCoreOf_isPGroup prime larger).to_inf_right
  have hintersectionCore := normal_pSubgroup_le_pCoreOf prime intersection middle
    hintersectionLe hintersectionNormal hintersectionPGroup
  have hcommutatorMiddle : ⁅middle, pCoreOf prime larger⁆ ≤ middle :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hcoreLe.trans hmiddleNormalizes)
  have hcommutatorCore : ⁅middle, pCoreOf prime larger⁆ ≤ pCoreOf prime larger :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp (hle.trans hcoreNormalizes)
  have hcommutatorLe : ⁅perfectSubgroup, pCoreOf prime larger⁆ ≤ pCoreOf prime middle :=
    (Subgroup.commutator_mono hperfectLe le_rfl).trans
      ((le_inf hcommutatorMiddle hcommutatorCore).trans hintersectionCore)
  exact hcommutatorLe.trans (Subgroup.le_centralizer_iff.mp hcentral)

theorem subnormal_quasisimple_centralizes_pCore {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) {subgroup overgroup : Subgroup G}
    (hsubnormal : IsSubnormal subgroup overgroup) (hquasi : IsQuasisimple subgroup) :
    subgroup ≤ Subgroup.centralizer (pCoreOf prime overgroup : Set G) := by
  have hchain := normalChain_of_subnormal hsubnormal
  clear hsubnormal
  induction hchain with
  | refl => exact quasisimple_centralizes_own_core prime hprime subgroup hquasi
  | extend hsmaller hle hnormal ih =>
    exact perfect_core_centralization_extend prime subgroup _ _ ⟨hquasi.1⟩
      hsmaller.le hle hnormal ih

theorem charTwoType_no_local_component {G : Type u} [Group G] [Finite G]
    (hchar : IsCharTwoType G) (localSubgroup : Subgroup G) (hlocal : IsTwoLocal localSubgroup)
    (subgroup : Subgroup G) : ¬IsComponentOf subgroup localSubgroup := by
  rintro ⟨hle, hsubnormal, hquasi⟩
  have hcentral := subnormal_quasisimple_centralizes_pCore 2 Nat.prime_two hsubnormal hquasi
  have hcore : subgroup ≤ pCoreOf 2 localSubgroup := fun element helement =>
    hchar localSubgroup hlocal ⟨hle helement, hcentral helement⟩
  exact quasisimple_not_isPGroup subgroup hquasi 2 Nat.prime_two
    ((pCoreOf_isPGroup 2 localSubgroup).to_le hcore)

end CFSG.RankThreeEvenClassification.Helpers
