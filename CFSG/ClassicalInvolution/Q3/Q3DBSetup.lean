module

public import CFSG.ClassicalInvolution.Q3.Q3WALoc
public import CFSG.ClassicalInvolution.Balance.FuzzyAdj
public import CFSG.ClassicalInvolution.Uniform.USat

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3DB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Uniform

variable {G : Type} [Group G] [Finite G]

theorem oddCoreIn_centralizer_conj {z : G} (g : G)
    (h : Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥) :
    Balance.oddCoreIn (Subgroup.centralizer ({g * z * g⁻¹} : Set G)) = ⊥ := by
  rw [← map_conj_centralizer_singleton g z]
  have h1 := oddCoreIn_conjSub_eq g (Subgroup.centralizer ({z} : Set G))
  rw [h] at h1
  exact h1.trans (Subgroup.map_bot _)

theorem classicalInvolutionOddCore_eq_bot {L : Subgroup G} {w : G}
    (hL : IsClassicalMember3 L w)
    (h : Balance.oddCoreIn (Subgroup.centralizer ({w} : Set G)) = ⊥) :
    classicalInvolutionOddCore ↥L = ⊥ := by
  have h1 : Balance.oddCoreIn L ≤ Balance.oddCoreIn (Subgroup.centralizer ({w} : Set G)) :=
    Balance.oddCoreIn_le_of_isSubnormal hL.subnormal
  rw [h, le_bot_iff] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp h1

theorem oddCoreIn_locLayer_le {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (x : G) :
    Balance.oddCoreIn (centralizingLayer Ω {x}) ≤
      Balance.oddCoreIn (Subgroup.centralizer ({x} : Set G)) := by
  refine Balance.le_oddCoreIn_of_normalizes ?_ ?_ (Balance.odd_card_oddCoreIn _)
  · refine (Balance.oddCoreIn_le _).trans ?_
    exact iSup₂_le fun L hL => hL.2
  · intro n hn
    exact mem_normalizer_oddCoreIn_centralizingLayer hΩ hn

theorem classicalInvolutionOddCore_locLayer_eq_bot {Ω : Set (Subgroup G)}
    (hΩ : ConjInvariant Ω) {x : G}
    (h : Balance.oddCoreIn (Subgroup.centralizer ({x} : Set G)) = ⊥) :
    classicalInvolutionOddCore ↥(centralizingLayer Ω {x}) = ⊥ := by
  have h1 := oddCoreIn_locLayer_le hΩ x
  rw [h, le_bot_iff] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ (centralizingLayer Ω {x}).subtype_injective).mp h1

theorem localOddCentral_of_oddCentralizerFree {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω)
    {x : G} (h : Balance.oddCoreIn (Subgroup.centralizer ({x} : Set G)) = ⊥) :
    LocalOddCentral Ω {x} := by
  unfold LocalOddCentral
  rw [classicalInvolutionOddCore_locLayer_eq_bot hΩ h]
  exact bot_le

theorem localOddThreeFree3_of_oddCentralizerFree {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω)
    {x : G} (h : Balance.oddCoreIn (Subgroup.centralizer ({x} : Set G)) = ⊥) :
    Q3W.LocalOddThreeFree3 Ω x := by
  unfold Q3W.LocalOddThreeFree3
  rw [classicalInvolutionOddCore_locLayer_eq_bot hΩ h, Subgroup.card_bot]
  omega

theorem exactMembers3_of_oddCentralizerFree {K : Subgroup G} {z : G}
    (hz : IsClassicalMember3 K z)
    (h : Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥) :
    ExactMembers3 (Set.range fun g : G => conjSub g K) := by
  rintro _ ⟨g, rfl⟩
  exact classicalInvolutionOddCore_eq_bot (hz.conj g) (oddCoreIn_centralizer_conj g h)

theorem oddCoreIn_eq_of_intrinsic3 {K : Subgroup G} {z : G} (hz : IsClassicalMember3 K z)
    (hint : Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ K) :
    Balance.oddCoreIn K = Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) :=
  le_antisymm (Balance.oddCoreIn_le_of_isSubnormal hz.subnormal)
    (Balance.le_oddCoreIn_of_normalizes hint
      ((isSubnormal_le hz.subnormal).trans (Balance.normalizer_oddCoreIn _))
      (Balance.odd_card_oddCoreIn _))

theorem oddCentralizerFree_of_exact_intrinsic {K : Subgroup G} {z : G}
    (hz : IsClassicalMember3 K z)
    (hint : Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ K)
    (hex : classicalInvolutionOddCore ↥K = ⊥) :
    Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥ := by
  rw [← oddCoreIn_eq_of_intrinsic3 hz hint]
  show Subgroup.map _ (classicalInvolutionOddCore ↥K) = ⊥
  rw [hex, Subgroup.map_bot]

theorem satU_three_eq_of_oddCentralizerFree {K : Subgroup G} {z : G}
    (h : Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥) :
    satU (.sl2 3 1) K z = K := by
  rw [satU_of_isSolvableType (MemberType.isSolvableType_sl2.mpr (by norm_num)), h, sup_bot_eq]

end CFSG.ClassicalInvolution.Q3.Q3DB
