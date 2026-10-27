module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingIsolated
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingOddQuotient
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineCanonicalRank
public import CFSG.StronglyEmbedded.TheoremSE.BenderLowRank

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine
  (twoRank_le_one_of_not_twoRankAtLeastTwo not_twoRankAtLeastTwo_of_twoRank_le_one)

@[expose] def NormSplit (X : Type*) [Group X] [Finite X] (M : Subgroup X) (x : X) : Prop :=
  twoRank X ≤ 1 ∨ ∃ u : X, u ^ 2 = 1 ∧ u ∈ Subgroup.center X ∧
    Subgroup.zpowers u ⊓ commutator X = ⊥ ∧ Subgroup.zpowers u ⊔ commutator X = ⊤ ∧
    fusionStronglyEmbedded (M.subgroupOf (commutator X)) ∧
    ∀ t ∈ involutionPointClass x, u⁻¹ * t ∈ commutator X

variable {A B : Type*} [Group A] [Group B]

theorem stronglyEmbedded_of_map_odd_kernel [Finite A] (f : A →* B) (hf : Function.Surjective f)
    (hodd : Odd (Nat.card f.ker)) {M : Subgroup A} (hker : f.ker ≤ M)
    (hM : fusionStronglyEmbedded (M.map f)) : fusionStronglyEmbedded M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite B := Finite.of_surjective f hf
  refine ⟨?_, ?_, ?_⟩
  · intro htop
    apply hM.1
    rw [htop, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hf]
  · obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := M.map f) 2
      (even_iff_two_dvd.mp hM.2.1)
    have hyI : IsInvolution (y : B) :=
      isInvolution_of_orderOf ((Subgroup.orderOf_coe y).trans hy)
    obtain ⟨x, hxM, hxI, -⟩ :=
      CFSG.ProperTwoGeneratedCore.involution_lift_in_subgroup_of_odd_kernel f hodd M hyI y.property
    have hxorder : orderOf (⟨x, hxM⟩ : M) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_of_isInvolution hxI
    exact even_iff_two_dvd.mpr (hxorder ▸ orderOf_dvd_natCard _)
  · intro g hg
    have hfg : f g ∉ M.map f := fun h => hg ((mem_map_iff_of_ker_le f hker g).mp h)
    have hodd' := hM.2.2 (f g) hfg
    by_contra hnot
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(M ⊓ M.map (MulAut.conj g⁻¹).toMonoidHom)) 2
      (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hnot))
    have hxI : IsInvolution (x : A) :=
      isInvolution_of_orderOf ((Subgroup.orderOf_coe x).trans hx)
    have hfxI := CFSG.ProperTwoGeneratedCore.involution_image_of_odd_kernel f hodd hxI
    have hmem : f x ∈ M.map f ⊓ (M.map f).map (MulAut.conj (f g)⁻¹).toMonoidHom := by
      obtain ⟨hxM, y, hyM, hyx⟩ := x.property
      refine ⟨⟨x, hxM, rfl⟩, f y, ⟨y, hyM, rfl⟩, ?_⟩
      rw [← hyx]
      simp only [MulEquiv.coe_toMonoidHom, map_inv, MulAut.conj_inv_apply, map_mul]
    have horder : orderOf (⟨f x, hmem⟩ :
        ↥(M.map f ⊓ (M.map f).map (MulAut.conj (f g)⁻¹).toMonoidHom)) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_of_isInvolution hfxI
    exact hodd'.not_two_dvd_nat (horder ▸ orderOf_dvd_natCard _)

theorem twoRank_le_one_of_odd_kernel [Finite A] [Finite B] (f : A →* B)
    (hodd : Odd (Nat.card f.ker)) (hrank : twoRank B ≤ 1) : twoRank A ≤ 1 := by
  apply twoRank_le_one_of_not_twoRankAtLeastTwo
  rintro ⟨E, hEcard, hEsq⟩
  apply not_twoRankAtLeastTwo_of_twoRank_le_one hrank
  refine CFSG.BenderSuzuki.twoRankAtLeastTwo_of_injective (f.comp E.subtype) ?_ ⟨⊤, ?_, ?_⟩
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro e he
    have heq : (e : A) = 1 := eq_one_of_sq_eq_one_of_odd hodd he
      (by simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using
        congrArg Subtype.val (hEsq e))
    exact Subgroup.mem_bot.mpr (Subtype.ext heq)
  · rw [Subgroup.card_top, hEcard]
  · intro x
    exact Subtype.ext (hEsq x.1)

theorem mem_commutator_of_odd_order {Y : Type*} [Group Y] {S : Set Y}
    (hgen : Subgroup.closure S = ⊤) (hS : ∀ s ∈ S, s ^ 2 = 1) {o : Y}
    (ho : Odd (orderOf o)) : o ∈ commutator Y := by
  have hsq : ∀ y : Y, (Abelianization.of y) ^ 2 = 1 := by
    intro y
    have hy : y ∈ Subgroup.closure S := hgen ▸ Subgroup.mem_top y
    induction hy using Subgroup.closure_induction with
    | mem x hx => rw [← map_pow, hS x hx, map_one]
    | one => rw [map_one, one_pow]
    | mul x y _ _ hx hy => rw [map_mul, mul_pow, hx, hy, one_mul]
    | inv x _ hx => rw [map_inv, inv_pow, hx, inv_one]
  rw [← Abelianization.ker_of]
  change Abelianization.of o = 1
  obtain ⟨m, hm⟩ := ho
  have h1 : (Abelianization.of o) ^ (2 * m + 1) = 1 := by
    rw [← map_pow, ← hm, pow_orderOf_eq_one, map_one]
  rw [pow_succ, pow_mul, hsq, one_pow, one_mul] at h1
  exact h1

end CFSG.ComponentClassification.AschbacherStrongEmbedding
