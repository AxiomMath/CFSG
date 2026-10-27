module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2HermSU
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Defs
public import CFSG.GH74.L5U5.IdentUnitary
public import CFSG.ClassicalInvolution.Phan.Phan3AOrder

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary Matrix
  CFSG.ComponentClassification.CatalogueBUnitaryIsometry CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary CFSG.Blueprint

theorem isQuasisimple_su_herm : CFSG.IsQuasisimple (Su F9 3 1 4) :=
  CFSG.GH74.L5U5.isQuasisimple_su natCard_F9 (by norm_num) (by norm_num)

@[expose] noncomputable def centerQuotientSu : Su F9 3 1 4 ⧸ Subgroup.center (Su F9 3 1 4) ≃*
    CFSG.Open.StatedProj (CFSG.Open.StatedSU 4 (3 ^ 1) F9) :=
  CFSG.GH74.L5U5.centerQuotientEquivStatedProjSu (p := 3) (f := 1) natCard_F9
    (by norm_num : 3 ≤ 4) (by decide)

theorem natCard_center_congr {G : Type*} [Group G] {H K : Subgroup G} (h : H = K) :
    Nat.card (Subgroup.center H) = Nat.card (Subgroup.center K) := by
  subst h
  rfl

theorem card_center_su_herm : Nat.card (Subgroup.center (Su F9 3 1 4)) = 4 :=
  (natCard_center_congr (SUid_eq_statedSU natCard_F9 4)).trans
    (CFSG.ClassicalInvolution.Phan.Q3G.card_center_statedSU_four_three natCard_F9)

theorem mem_zpowers_hermNegSU {s : Su F9 3 1 4} :
    s ∈ Subgroup.zpowers hermNegSU ↔ s = 1 ∨ s = hermNegSU := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, orderOf_hermNegSU]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩
    interval_cases a
    · exact Or.inl (pow_zero _)
    · exact Or.inr (pow_one _)
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, pow_zero _⟩
    · exact ⟨1, by norm_num, pow_one _⟩

theorem omega9_ne_one : omega9 ≠ 1 := by
  intro h
  have := congrArg QuadraticAlgebra.im h
  simp [omega9, QuadraticAlgebra.im_omega, QuadraticAlgebra.im_one] at this

theorem omega9_ne_neg_one : omega9 ≠ -1 := by
  intro h
  have := congrArg QuadraticAlgebra.im h
  simp [omega9, QuadraticAlgebra.im_omega, QuadraticAlgebra.im_neg, QuadraticAlgebra.im_one]
    at this

theorem hermOmegaSU_not_mem_zpowers : hermOmegaSU ∉ Subgroup.zpowers hermNegSU := by
  rw [mem_zpowers_hermNegSU]
  rintro (h | h)
  · have h1 := congrArg (fun s => suMat s 0 0) h
    simp [suMat_hermOmegaSU, Matrix.scalar_apply] at h1
    exact omega9_ne_one h1
  · have h1 := congrArg (fun s => suMat s 0 0) h
    simp [suMat_hermOmegaSU, suMat_hermNegSU, Matrix.scalar_apply] at h1
    exact omega9_ne_neg_one h1

theorem isQuasisimple_isTwoU43_of_cover {X : Type} [Group X] (θ : Su F9 3 1 4 →* X)
    (hθ : Function.Surjective θ) (hker : θ.ker = Subgroup.zpowers hermNegSU) :
    CFSG.IsQuasisimple X ∧ IsTwoU43 X := by
  have hq := isQuasisimple_su_herm
  have hker_le : θ.ker ≤ Subgroup.center (Su F9 3 1 4) := by
    rw [hker]
    exact Subgroup.zpowers_le.mpr hermNegSU_mem_center
  have hcardker : Nat.card θ.ker = 2 := by
    rw [hker, Nat.card_zpowers, orderOf_hermNegSU]
  have hnt : ∃ k, θ k ≠ 1 := ⟨hermOmegaSU, fun h => hermOmegaSU_not_mem_zpowers
    (hker ▸ MonoidHom.mem_ker.mpr h)⟩
  have hqX := CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hq hθ hnt
  let e := CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hq hθ hker_le
  refine ⟨hqX, ?_, ?_⟩
  · haveI : Finite X := Finite.of_surjective θ hθ
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (Su F9 3 1 4))
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)
    have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker
    have h4 : Nat.card (Su F9 3 1 4 ⧸ θ.ker) = Nat.card X :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ hθ).toEquiv
    have h5 : Nat.card (Su F9 3 1 4 ⧸ Subgroup.center (Su F9 3 1 4)) =
        Nat.card (X ⧸ Subgroup.center X) := Nat.card_congr e.toEquiv
    have hm : 0 < Nat.card (X ⧸ Subgroup.center X) := Nat.card_pos
    rw [card_center_su_herm, h5] at h1
    rw [h4, hcardker] at h3
    have h6 : Nat.card (X ⧸ Subgroup.center X) * 4 =
        Nat.card (X ⧸ Subgroup.center X) * (2 * Nat.card (Subgroup.center X)) := by
      rw [← h1, h3, h2]
      ring
    have := Nat.eq_of_mul_eq_mul_left hm h6
    omega
  · have hadm : CFSG.Open.StatedLieAdmissible .PSU 4 3 1 :=
      ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩
    exact Or.inl ⟨by decide, hadm, F9, inferInstance, inferInstance, natCard_F9,
      ⟨e.symm.trans centerQuotientSu⟩⟩

end CFSG.OddStandard.SmallF3.Omega
