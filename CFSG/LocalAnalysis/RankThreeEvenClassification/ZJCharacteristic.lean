module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThompsonTransport
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ZJNormality
import CFSG.GroupTheory.SylowNaturalCharacteristic

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem thompsonCenterOf_map_equiv {G : Type u} {H : Type v} [Group G] [Group H]
    [Finite G] [Finite H] (equivalence : G ≃* H) (subgroup : Subgroup G) :
    thompsonCenterOf (subgroup.map (equivalence : G →* H)) =
      (thompsonCenterOf subgroup).map (equivalence : G →* H) := by
  have hcenter := thompsonOrderCenter_map_equiv (equivalence.subgroupMap subgroup)
  simp only [MulEquiv.toMonoidHom_eq_coe] at hcenter
  have hmapped := congrArg
    (fun candidate : Subgroup (subgroup.map (equivalence : G →* H)) =>
      candidate.map (subgroup.map (equivalence : G →* H)).subtype) hcenter
  change _ = ((thompsonOrderCenter subgroup).map subgroup.subtype).map (equivalence : G →* H)
  rw [Subgroup.map_map] at hmapped ⊢
  have hcompose : (subgroup.map (equivalence : G →* H)).subtype.comp
      (equivalence.subgroupMap subgroup : subgroup →* subgroup.map (equivalence : G →* H)) =
      (equivalence : G →* H).comp subgroup.subtype := by
    ext member
    rfl
  rw [hcompose] at hmapped
  exact hmapped.symm

theorem thompsonCenterOf_sylow_eq_of_normal {G : Type u} [Group G] [Finite G]
    (prime : ℕ) [Fact prime.Prime] (first second : Sylow prime G)
    [(thompsonCenterOf (first : Subgroup G)).Normal] :
    thompsonCenterOf (second : Subgroup G) = thompsonCenterOf (first : Subgroup G) := by
  obtain ⟨member, heq⟩ := MulAction.exists_smul_eq G first second
  rw [← heq, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  change thompsonCenterOf ((first : Subgroup G).map (MulAut.conj member : G →* G)) = _
  rw [thompsonCenterOf_map_equiv, Subgroup.Normal.map_conj_eq]

theorem thompsonCenterOf_characteristic_of_normal {G : Type u} [Group G] [Finite G]
    (prime : ℕ) [Fact prime.Prime] (sylow : Sylow prime G)
    [(thompsonCenterOf (sylow : Subgroup G)).Normal] :
    (thompsonCenterOf (sylow : Subgroup G)).Characteristic :=
  CFSG.characteristic_of_normal_of_map_mulEquiv (fun subgroup => thompsonCenterOf subgroup)
    (fun equivalence subgroup => (thompsonCenterOf_map_equiv equivalence subgroup).symm) sylow

theorem thompsonCenterOf_characteristic_of_stable_normal_actions {G : Type u}
    [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime) (hodd : Odd prime)
    (sylow : Sylow prime G)
    (hcharacteristic : Subgroup.centralizer (pCore prime G : Set G) ≤ pCore prime G)
    (hstable : StableNormalPrimeActions prime G) :
    (thompsonCenterOf (sylow : Subgroup G)).Characteristic := by
  let : Fact prime.Prime := ⟨hprime⟩
  have : (thompsonCenterOf (sylow : Subgroup G)).Normal :=
    thompsonCenterOf_normal_of_stable_normal_actions prime hprime hodd sylow hcharacteristic hstable
  exact thompsonCenterOf_characteristic_of_normal prime sylow

end CFSG.RankThreeEvenClassification.Helpers
