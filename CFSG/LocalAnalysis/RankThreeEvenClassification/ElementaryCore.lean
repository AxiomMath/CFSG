module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.GeneratedCore

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

theorem isElemAbelian_isPGroup {G : Type u} [Group G] (prime : ℕ)
    (subgroup : Subgroup G) (hab : IsElemAbelian prime subgroup) : IsPGroup prime subgroup := by
  apply IsPGroup.of_exponent_dvd_pow (n := 1)
  rw [pow_one]
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro element
  apply Subtype.ext
  exact hab.2 element element.property

theorem pRank_eq_exponent_of_elementary {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (subgroup : Subgroup G)
    (hab : IsElemAbelian prime subgroup) (exponent : ℕ)
    (hcard : Nat.card subgroup = prime ^ exponent) : pRank prime subgroup = exponent := by
  apply le_antisymm
  · calc
      pRank prime subgroup ≤ Nat.log prime (Nat.card subgroup) :=
        pRank_le_log_card prime hprime subgroup
      _ = exponent := by rw [hcard, Nat.log_pow hprime.one_lt]
  · exact le_csSup (pRank_bddAbove prime hprime subgroup) ⟨subgroup, le_rfl, hab, hcard⟩

theorem commutative_overgroup_le_centralizer {G : Type u} [Group G]
    (overgroup subgroup : Subgroup G) (hcomm : IsMulCommutative overgroup)
    (hle : subgroup ≤ overgroup) : overgroup ≤ Subgroup.centralizer (subgroup : Set G) := by
  intro element helement
  apply Subgroup.mem_centralizer_iff.mpr
  intro other hother
  exact congrArg (fun member : overgroup => (member : G))
    (isMulCommutative_iff.mp hcomm ⟨other, hle hother⟩ ⟨element, helement⟩)

theorem relativeCentralizer_eq_of_commutative {G : Type u} [Group G]
    (overgroup subgroup : Subgroup G) (hcomm : IsMulCommutative overgroup)
    (hle : subgroup ≤ overgroup) : relativeCentralizer overgroup subgroup = overgroup := by
  exact inf_eq_left.mpr (commutative_overgroup_le_centralizer overgroup subgroup hcomm hle)

theorem centralizerProduct_eq_of_commutative {G : Type u} [Group G]
    (overgroup subgroup : Subgroup G) (hcomm : IsMulCommutative overgroup)
    (hle : subgroup ≤ overgroup) : centralizerProduct overgroup subgroup = overgroup := by
  rw [centralizerProduct, relativeCentralizer_eq_of_commutative overgroup subgroup hcomm hle]
  exact sup_eq_right.mpr hle

theorem aschbacherCore_eq_generatedPCore_of_commutative {G : Type u} [Group G] [Finite G]
    (prime threshold : ℕ) (overgroup : Subgroup G) (hcomm : IsMulCommutative overgroup)
    (hrank : 3 ≤ pRank prime overgroup) :
    aschbacherCore prime threshold overgroup = generatedPCore prime threshold overgroup := by
  apply le_antisymm (aschbacherCore_le_generatedPCore prime threshold overgroup)
  apply generatedPCore_le
  intro subgroup hle hsubgroup
  apply normalizer_le_aschbacherCore prime threshold overgroup subgroup hle hsubgroup
  rw [centralizerProduct_eq_of_commutative overgroup subgroup hcomm hle]
  exact hrank

theorem elementary_rank_three_core_eq_full_core {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (threshold : ℕ) (elementary : Subgroup G)
    (hab : IsElemAbelian prime elementary) (hcard : Nat.card elementary = prime ^ 3) :
    aschbacherCore prime threshold elementary = generatedPCore prime threshold elementary := by
  apply aschbacherCore_eq_generatedPCore_of_commutative prime threshold elementary hab.1
  exact le_of_eq (pRank_eq_exponent_of_elementary prime hprime elementary hab 3 hcard).symm

end CFSG.RankThreeEvenClassification.Helpers
