module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface
public import CFSG.RankThree.Literature.FSmithForm
public import CFSG.GroupTheory.ExtraspecialCentralizerInnerAut
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.Monster.B.Short.Extraspecial

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith CFSG.GroupTheory.WeirSylow
open scoped commutatorElement

variable {H : Type} [Group H] {Q : Subgroup H}

theorem IsPlusExtraspecial.finite {m : ℕ} (h : IsPlusExtraspecial m Q) : Finite Q :=
  Nat.finite_of_card_ne_zero (by rw [h.2.1]; positivity)

theorem IsPlusExtraspecial.isExtraspecialPGroup {m : ℕ} (h : IsPlusExtraspecial m Q) :
    IsExtraspecialPGroup 2 Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := h.1
  haveI := h.finite
  exact CFSG.IsExtraspecial.isExtraspecialPGroup

theorem IsPlusExtraspecial.card_abelianization {m : ℕ} (h : IsPlusExtraspecial m Q) :
    Nat.card (Additive (Abelianization Q)) = 2 ^ (2 * m) := by
  have hE := h.isExtraspecialPGroup
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (_root_.commutator Q)
  rw [hE.2.1, hE.2.2.2, h.2.1] at h1
  change Nat.card (Q ⧸ _root_.commutator Q) = 2 ^ (2 * m)
  rw [hE.2.1]
  have h2 : 2 ^ (1 + 2 * m) = 2 ^ (2 * m) * 2 := by rw [add_comm, pow_succ]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) (h1.symm.trans h2)

variable [Module (ZMod 2) (Additive (Abelianization Q))]

theorem IsPlusExtraspecial.finrank_quotient {m : ℕ} (h : IsPlusExtraspecial m Q) :
    finrank (ZMod 2) (Additive (Abelianization Q)) = 2 * m := by
  haveI := h.finite
  haveI : Finite (Additive (Abelianization Q)) := by
    change Finite (Q ⧸ _root_.commutator Q)
    infer_instance
  have h1 := h.card_abelianization
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at h1
  exact Nat.pow_right_injective le_rfl h1

theorem ker_extraspecialConjOrth [hQn : Q.Normal] [Finite Q] (hE : IsExtraspecialPGroup 2 Q)
    (hC : centralizer (Q : Set H) ≤ Q) :
    (extraspecialConjOrth hE hQn).ker = Q := by
  refine le_antisymm (fun g hg => mem_of_extraspecialConjOrth_eq_one hE hQn hC hg) fun g hg => ?_
  rw [MonoidHom.mem_ker]
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
  change Additive.ofMul (Abelianization.of (conjAut hQn g x)) = Additive.ofMul (Abelianization.of x)
  have h : conjAut hQn g x = ⟨g, hg⟩ * x * (⟨g, hg⟩ : Q)⁻¹ :=
    Subtype.ext (by rw [conjAut_apply]; rfl)
  rw [h, ofMul_of_mul, ofMul_of_mul, map_inv, ofMul_inv]
  abel

theorem conjLinEquiv_eq_one_of_mem [hQn : Q.Normal] {g : H} (hg : g ∈ Q) :
    conjLinEquiv hQn g = 1 := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨x, rfl⟩ := exists_ofMul_of v
  change Additive.ofMul (Abelianization.of (conjAut hQn g x)) = Additive.ofMul (Abelianization.of x)
  have h : conjAut hQn g x = ⟨g, hg⟩ * x * (⟨g, hg⟩ : Q)⁻¹ :=
    Subtype.ext (by rw [conjAut_apply]; rfl)
  rw [h, ofMul_of_mul, ofMul_of_mul, map_inv, ofMul_inv]
  abel

omit [Module (ZMod 2) (Additive (Abelianization Q))] in
theorem mem_centerOf_iff (y : Q) : (y : H) ∈ centerOf Q ↔ y ∈ Subgroup.center Q := by
  rw [centerOf, Subgroup.mem_inf, Subgroup.mem_center_iff, mem_centralizer_iff]
  constructor
  · rintro ⟨-, h⟩ z
    exact Subtype.ext (h z z.2)
  · intro h
    exact ⟨y.2, fun z hz => congrArg Subtype.val (h ⟨z, hz⟩)⟩

theorem extraspecialConjOrth_apply_eq_iff [hQn : Q.Normal] [Finite Q]
    (hE : IsExtraspecialPGroup 2 Q) (g : H) (x : Q) :
    ((extraspecialConjOrth hE hQn g : TauCeti.QuadraticMap.orthogonalGroup
        (extraspecialQuadForm hE)) : Additive (Abelianization Q) ≃ₗ[ZMod 2]
        Additive (Abelianization Q)) (Additive.ofMul (Abelianization.of x)) =
      Additive.ofMul (Abelianization.of x) ↔ ⁅g, (x : H)⁆ ∈ centerOf Q := by
  rw [extraspecialConjOrth_apply]
  have hy : ((conjAut hQn g x * x⁻¹ : Q) : H) = ⁅g, (x : H)⁆ := by
    simp [conjAut_apply, commutatorElement_def]
  rw [← hy, mem_centerOf_iff, ← ofMul_of_eq_zero_iff hE, ofMul_of_mul, map_inv, ofMul_inv,
    ← sub_eq_add_neg, sub_eq_zero]

omit [Module (ZMod 2) (Additive (Abelianization Q))] in
theorem le_of_forall_commutator_mem_centerOf [hQn : Q.Normal] [Finite Q]
    (hE : IsExtraspecialPGroup 2 Q) (hC : centralizer (Q : Set H) ≤ Q) {K : Subgroup H}
    (hK : ∀ g ∈ K, ∀ x ∈ Q, ⁅g, x⁆ ∈ centerOf Q) : K ≤ Q := by
  letI := CFSG.GroupTheory.extraspecialQuotientModule hE
  intro g hg
  refine mem_of_extraspecialConjOrth_eq_one hE hQn hC ?_
  refine Subtype.ext (LinearEquiv.ext fun v => ?_)
  obtain ⟨x, rfl⟩ := exists_ofMul_of v
  exact (extraspecialConjOrth_apply_eq_iff hE g x).2 (hK g hg x x.2)

end CFSG.EvenSporadicStandard.HNRecog
