module

public import CFSG.Open.LocalVocabulary

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem le_pCore_of_normal {G : Type u} [Group G] (prime : ℕ)
    (subgroup : Subgroup G) (hnormal : subgroup.Normal)
    (hpgroup : IsPGroup prime subgroup) : subgroup ≤ pCore prime G :=
  le_sSup ⟨hnormal, hpgroup⟩

theorem pCore_eq_sSup (G : Type u) [Group G] (prime : ℕ) :
    pCore prime G = sSup {subgroup : Subgroup G |
      subgroup.Normal ∧ IsPGroup prime subgroup} :=
  rfl

theorem pCore_normal (G : Type u) [Group G] (prime : ℕ) : (pCore prime G).Normal := by
  rw [pCore_eq_sSup G prime]
  apply Subgroup.sSup_normal
  rintro subgroup ⟨hnormal, _⟩
  exact hnormal

theorem pCore_le_sylow {G : Type u} [Group G] (prime : ℕ) (sylow : Sylow prime G) :
    pCore prime G ≤ sylow := by
  rw [CFSG.pCore_eq_iSup]
  refine iSup_le fun subgroup => iSup_le fun hnormal => iSup_le fun hpgroup => ?_
  have : subgroup.Normal := hnormal
  exact hpgroup.le_sylow_of_normal sylow

theorem pCore_isPGroup (G : Type u) [Group G] (prime : ℕ) :
    IsPGroup prime (pCore prime G) := by
  classical
  let sylow : Sylow prime G := Classical.choice inferInstance
  have hle := pCore_le_sylow prime sylow
  exact sylow.isPGroup'.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)

theorem pCoreOf_le {G : Type u} [Group G] (prime : ℕ) (subgroup : Subgroup G) :
    pCoreOf prime subgroup ≤ subgroup := by
  exact (Subgroup.map_le_range subgroup.subtype (pCore prime subgroup)).trans
    (le_of_eq (Subgroup.range_subtype subgroup))

theorem normal_pSubgroup_le_pCoreOf {G : Type u} [Group G] (prime : ℕ)
    (smaller larger : Subgroup G) (hle : smaller ≤ larger)
    (hnormal : (smaller.subgroupOf larger).Normal) (hpgroup : IsPGroup prime smaller) :
    smaller ≤ pCoreOf prime larger := by
  have hrestriction : IsPGroup prime (smaller.subgroupOf larger) :=
    hpgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hle).symm
  have hcore := le_pCore_of_normal prime (smaller.subgroupOf larger) hnormal hrestriction
  have hmap := Subgroup.map_mono (f := larger.subtype) hcore
  simpa only [Subgroup.map_subgroupOf_eq_of_le hle, pCoreOf] using hmap

theorem twoLocal_has_nontrivial_pCore {G : Type u} [Group G]
    (subgroup : Subgroup G) (hlocal : IsTwoLocal subgroup) : pCoreOf 2 subgroup ≠ ⊥ := by
  obtain ⟨twosubgroup, hnontrivial, hpgroup, heq⟩ := hlocal
  have hle : twosubgroup ≤ subgroup := heq.symm ▸ Subgroup.le_normalizer
  have hnormal : (twosubgroup.subgroupOf subgroup).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (le_of_eq heq)
  have hcore := normal_pSubgroup_le_pCoreOf 2 twosubgroup subgroup hle hnormal hpgroup
  intro hbot
  apply hnontrivial
  apply le_antisymm _ bot_le
  simpa only [hbot] using hcore

theorem charTwoType_local_centralizer {G : Type u} [Group G] (hchar : IsCharTwoType G)
    (subgroup : Subgroup G) (hlocal : IsTwoLocal subgroup) :
    Subgroup.centralizer (pCore 2 subgroup : Set subgroup) ≤ pCore 2 subgroup := by
  intro element hcentral
  have hambient : (element : G) ∈ Subgroup.centralizer (pCoreOf 2 subgroup : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro other hother
    obtain ⟨preimage, hpreimage, rfl⟩ := Subgroup.mem_map.mp hother
    have heq := Subgroup.mem_centralizer_iff.mp hcentral preimage hpreimage
    exact congrArg Subtype.val heq
  have hcore := hchar subgroup hlocal ⟨element.property, hambient⟩
  exact (Subgroup.mem_map_iff_mem subgroup.subtype_injective).mp hcore

theorem charTwoType_local_center_le_core {G : Type u} [Group G] (hchar : IsCharTwoType G)
    (subgroup : Subgroup G) (hlocal : IsTwoLocal subgroup) :
    Subgroup.center subgroup ≤ pCore 2 subgroup := by
  exact (Subgroup.center_le_centralizer (pCore 2 subgroup : Set subgroup)).trans
    (charTwoType_local_centralizer hchar subgroup hlocal)

theorem charTwoType_local_center_isPGroup {G : Type u} [Group G] (hchar : IsCharTwoType G)
    (subgroup : Subgroup G) (hlocal : IsTwoLocal subgroup) :
    IsPGroup 2 (Subgroup.center subgroup) := by
  have hle := charTwoType_local_center_le_core hchar subgroup hlocal
  exact (pCore_isPGroup subgroup 2).of_injective
    (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)

end CFSG.RankThreeEvenClassification.Helpers
