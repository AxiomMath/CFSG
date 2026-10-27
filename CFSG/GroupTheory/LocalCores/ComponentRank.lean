module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.ClassicalInvolution.RouteD.GapsPerfect
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_8
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZComm
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.LocalCores

open Subgroup

variable {X : Type*} [Group X]

section Finite

variable [Finite X]

theorem exists_odd_prime_dvd_card_of_isComponent {C : Subgroup X} (hC : CFSG.IsComponent C) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card C := by
  by_contra h
  push Not at h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect ↥C := hC.1.1
  have : Nontrivial (↥C ⧸ center ↥C) := hC.1.2.1.toNontrivial
  have : Nontrivial ↥C := (QuotientGroup.mk'_surjective (center ↥C)).nontrivial
  have h2 : IsPGroup 2 ↥C := IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd
    Nat.card_pos.ne' fun {d} hd hdn => by_contra fun hd2 => h d hd hd2 hdn)
  have : Group.IsNilpotent ↥C := h2.isNilpotent
  exact Group.IsPerfect.not_isNilpotent ↥C inferInstance

theorem exists_noncentral_of_isComponent {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    {C : Subgroup X} (hC : CFSG.IsComponent C) (hdvd : p ∣ Nat.card C) :
    ∃ e ∈ C, orderOf e = p ∧ ∃ c ∈ C, e * c ≠ c * e := by
  obtain ⟨x, hx, hxc⟩ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_orderOf_eq_prime_not_mem_center
      ((CFSG.isComponent_iff_open C).mp hC).2.2 hp hodd hdvd
  refine ⟨x, x.2, by rw [Subgroup.orderOf_coe, hx], ?_⟩
  rw [Subgroup.mem_center_iff] at hxc
  obtain ⟨g, hg⟩ := not_forall.mp hxc
  exact ⟨g, g.2, fun h => hg (Subtype.ext h.symm)⟩

theorem card_le_pRank_of_isComponent {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (s : Finset (Subgroup X)) (hs : ∀ C ∈ s, CFSG.IsComponent C ∧ p ∣ Nat.card C) :
    s.card ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  have h := CFSG.LocalAnalysis.RankThreeUC.AGL81C.card_le_pRank_of_components hp s fun C hC =>
    ⟨(hs C hC).1, exists_noncentral_of_isComponent hp hodd (hs C hC).1 (hs C hC).2⟩
  rwa [CFSG.SectionRank.pRank_eq_open_pRank_top,
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h

theorem perfect_le_normalizer_of_isComponent {L : Subgroup X} (hLp : ⁅L, L⁆ = L)
    (hp3 : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3)
    {C : Subgroup X} (hC : CFSG.IsComponent C) : L ≤ normalizer (C : Set X) := by
  classical
  have : Fintype (Subgroup X) := Fintype.ofFinite _
  obtain ⟨p, hp, hp2, hpdvd⟩ := exists_odd_prime_dvd_card_of_isComponent hC
  let T : Finset (Subgroup X) :=
    Finset.univ.filter fun D => CFSG.IsComponent D ∧ p ∣ Nat.card D
  have hT : ∀ D ∈ T, CFSG.IsComponent D ∧ p ∣ Nat.card D := fun D hD =>
    (Finset.mem_filter.mp hD).2
  have hcard : T.card ≤ 3 :=
    (card_le_pRank_of_isComponent hp hp2 T hT).trans (hp3 p hp hp2)
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLp
  have hSn : (T : Set (Subgroup X)).ncard ≤ 4 := by
    rw [Set.ncard_coe_finset]
    omega
  have hmemC : C ∈ (T : Set (Subgroup X)) := by
    rw [Finset.mem_coe]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC, hpdvd⟩
  refine CFSG.ClassicalInvolution.RouteD.Gaps.perfect_le_normalizer_of_card_le_four L _
    T.finite_toSet hSn ?_ hmemC
  intro g _ A hA
  have hA' : CFSG.IsComponent A ∧ p ∣ Nat.card A := hT A (Finset.mem_coe.mp hA)
  rw [Finset.mem_coe]
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
  · exact isComponent_map_mulEquiv (MulAut.conj g) hA'.1
  · rw [← Nat.card_congr (A.equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).toEquiv]
    exact hA'.2

end Finite

theorem exists_inner_of_le_normalizer {L C : Subgroup X} (hLp : ⁅L, L⁆ = L)
    (hC : CFSG.IsComponent C)
    (hOut : Group.IsSolvable
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer (↥C ⧸ center ↥C)))
    (hN : L ≤ normalizer (C : Set X)) :
    ∀ l ∈ L, ∃ c ∈ C, ∀ y ∈ C, l * y * l⁻¹ = c * y * c⁻¹ := by
  intro l hl
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLp
  have : Group.IsPerfect ↥C := hC.1.1
  have : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer C) :=
    CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient C
  exact CFSG.ComponentClassification.ComponentInnerActions.perfect_normalizer_action_inner
    L C hN ⟨l, hl⟩

end CFSG.LocalCores
