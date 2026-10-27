module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.AutBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Cat.Harada.SmallGroups
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.EvenSporadicStandard.HSStd.InvCent.Harada

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type*} [Group G]

noncomputable def outerHom (S : Subgroup G) [S.Normal] : G →* Outer ↥S :=
  (QuotientGroup.mk' (inner ↥S)).comp (MulAut.conjNormal (H := S))

theorem mem_ker_outerHom {S : Subgroup G} [S.Normal] (hcent : centralizer (S : Set G) = ⊥)
    {g : G} : g ∈ (outerHom S).ker ↔ g ∈ S := by
  rw [MonoidHom.mem_ker]
  change (QuotientGroup.mk (MulAut.conjNormal (H := S) g) : Outer ↥S) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨s, hs⟩
    have h1 : MulAut.conjNormal (H := S) g = MulAut.conjNormal (H := S) (s : G) := by
      rw [MulAut.conjNormal_val]
      exact hs.symm
    rw [conjNormal_injective_of_centralizer hcent h1]
    exact s.2
  · intro hg
    refine ⟨⟨g, hg⟩, ?_⟩
    rw [← MulAut.conjNormal_val]

theorem derivedSeries_le_of_outer {S : Subgroup G} [S.Normal]
    (hcent : centralizer (S : Set G) = ⊥) (n : ℕ)
    (hn : derivedSeries (outerHom S).range n = ⊥) : derivedSeries G n ≤ S := by
  intro x hx
  have h1 := map_derivedSeries_le_derivedSeries (outerHom S).rangeRestrict n
  rw [hn, le_bot_iff] at h1
  have hx' : (outerHom S).rangeRestrict x ∈ (derivedSeries G n).map (outerHom S).rangeRestrict :=
    ⟨x, hx, rfl⟩
  rw [h1, Subgroup.mem_bot] at hx'
  have h2 : outerHom S x = 1 := by
    have := congrArg Subtype.val hx'
    simpa using this
  exact (mem_ker_outerHom hcent).1 h2

theorem commutator_le_of_card_outer_dvd_four [Finite G] {S : Subgroup G} [S.Normal]
    (hcent : centralizer (S : Set G) = ⊥) (h : Nat.card (Outer ↥S) ∣ 4) :
    commutator G ≤ S := by
  have hd : Nat.card (outerHom S).range ∣ 4 :=
    (Subgroup.card_subgroup_dvd_card _).trans h
  haveI : Finite (outerHom S).range := inferInstance
  haveI := isMulCommutative_of_card_dvd_four hd
  exact derivedSeries_le_of_outer hcent 1 (commutator_eq_bot_of_isMulCommutative)

theorem commutator_commutator_le_of_card_outer_dvd_twelve [Finite G] {S : Subgroup G} [S.Normal]
    (hcent : centralizer (S : Set G) = ⊥) (h : Nat.card (Outer ↥S) ∣ 12) :
    ⁅commutator G, commutator G⁆ ≤ S := by
  have hd : Nat.card (outerHom S).range ∣ 12 :=
    (Subgroup.card_subgroup_dvd_card _).trans h
  haveI : Finite (outerHom S).range := inferInstance
  exact derivedSeries_le_of_outer hcent 2 (derivedSeries_two_eq_bot_of_card_dvd_twelve hd)

theorem commutator_self_eq {S : Subgroup G} (hperf : Group.IsPerfect ↥S) : ⁅S, S⁆ = S := by
  rw [← Subgroup.map_subtype_commutator, hperf.commutator_eq_top, Subgroup.map_top,
    Subgroup.range_subtype]

theorem le_commutator_of_perfect {S : Subgroup G} (hperf : Group.IsPerfect ↥S) :
    S ≤ commutator G := by
  rw [← commutator_self_eq hperf, _root_.commutator_def]
  exact Subgroup.commutator_mono le_top le_top

theorem le_commutator_commutator_of_perfect {S : Subgroup G} (hperf : Group.IsPerfect ↥S) :
    S ≤ ⁅commutator G, commutator G⁆ := by
  rw [← commutator_self_eq hperf]
  exact Subgroup.commutator_mono (le_commutator_of_perfect hperf) (le_commutator_of_perfect hperf)

end CFSG.EvenSporadicStandard.HSStd.InvCent.Harada
