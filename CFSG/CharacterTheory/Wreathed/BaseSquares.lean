module

public import CFSG.CharacterTheory.Wreathed.BaseNormalizerQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Wielandt.SubgroupRectangular

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical IsMulCommutative

universe u v

@[expose] def squareSubgroup (A : Type u) [Group A] : Subgroup A :=
  Subgroup.closure (Set.range (fun a : A => a ^ 2))

theorem squareSubgroup_map_mulEquiv {A : Type u} {B : Type v}
    [Group A] [Group B] (e : A ≃* B) :
    (squareSubgroup A).map e.toMonoidHom = squareSubgroup B := by
  unfold squareSubgroup
  rw [MonoidHom.map_closure]
  congr 1
  ext b
  constructor
  · rintro ⟨a, ⟨x, rfl⟩, rfl⟩
    exact ⟨e x, (map_pow e x 2).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨(e.symm y) ^ 2, ⟨e.symm y, rfl⟩, ?_⟩
    change e ((e.symm y) ^ 2) = y ^ 2
    rw [map_pow, e.apply_symm_apply]

instance squareSubgroup_characteristic (A : Type u) [Group A] :
    (squareSubgroup A).Characteristic :=
  Subgroup.characteristic_iff_map_eq.mpr squareSubgroup_map_mulEquiv

theorem squareSubgroup_eq_pow_range (A : Type u) [Group A] [IsMulCommutative A] :
    squareSubgroup A = (powMonoidHom (α := A) 2).range := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro a ⟨b, rfl⟩
    exact ⟨b, rfl⟩
  · rintro a ⟨b, rfl⟩
    exact Subgroup.subset_closure ⟨b, rfl⟩

theorem frattini_eq_squareSubgroup (A : Type u) [Group A] [Finite A]
    [IsMulCommutative A] (hA : IsPGroup 2 A) :
    frattini A = squareSubgroup A := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (IsPGroup 2 A) := ⟨hA⟩
  rw [squareSubgroup_eq_pow_range]
  exact CFSG.Wielandt.frattini_eq_powMonoidHom_range_of_isPGroup_commutative
    (R := A) (p := 2)

theorem base_frattini_eq_squares (n : ℕ) :
    frattini (baseSubgroup (2 ^ n)) = squareSubgroup (baseSubgroup (2 ^ n)) := by
  let : IsMulCommutative (baseSubgroup (2 ^ n)) := base_is_abelian _
  exact frattini_eq_squareSubgroup _ ((wreath_isPGroup n).to_subgroup _)

@[expose] def squareAutAction (A : Type u) [Group A] :
    MulAut A →* MulAut (A ⧸ squareSubgroup A) where
  toFun a := QuotientGroup.congr _ _ a (squareSubgroup_map_mulEquiv a)
  map_one' := by
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H a => rfl
  map_mul' a b := by
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H x => rfl

theorem squareAutAction_mk (A : Type u) [Group A] (a : MulAut A) (x : A) :
    squareAutAction A a ((QuotientGroup.mk' (squareSubgroup A)) x) =
      (QuotientGroup.mk' (squareSubgroup A)) (a x) := rfl

variable {G : Type u} [Group G]

theorem modelBase_frattini_eq_squares (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) :
    frattini (modelBase S e) = squareSubgroup (modelBase S e) := by
  rw [← frattini_map_mulEquiv (modelBaseEquiv S e), base_frattini_eq_squares,
    squareSubgroup_map_mulEquiv]

@[expose] def modelBaseFrattiniSquareQuotientEquiv (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) :
    baseSubgroup (2 ^ n) ⧸ frattini (baseSubgroup (2 ^ n)) ≃*
      modelBase S e ⧸ squareSubgroup (modelBase S e) :=
  (QuotientGroup.quotientMulEquivOfEq (base_frattini_eq_squares n)).trans
    (QuotientGroup.congr _ _ (modelBaseEquiv S e)
      (squareSubgroup_map_mulEquiv (modelBaseEquiv S e)))

theorem modelBaseFrattiniSquareQuotientEquiv_mk (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (b : baseSubgroup (2 ^ n)) :
    modelBaseFrattiniSquareQuotientEquiv n S e
      ((QuotientGroup.mk' (frattini (baseSubgroup (2 ^ n)))) b) =
        (QuotientGroup.mk' (squareSubgroup (modelBase S e))) (modelBaseEquiv S e b) := by
  rfl

@[expose] def modelBaseSquareAction (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.normalizer (modelBase S e : Set G) →*
      MulAut (modelBase S e ⧸ squareSubgroup (modelBase S e)) :=
  (squareAutAction (modelBase S e)).comp (modelBase S e).normalizerMonoidHom

theorem modelBaseSquareAction_mk (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelBase S e : Set G)) (b : modelBase S e) :
    modelBaseSquareAction n S e g
      ((QuotientGroup.mk' (squareSubgroup (modelBase S e))) b) =
        (QuotientGroup.mk' (squareSubgroup (modelBase S e)))
          ((modelBase S e).normalizerMonoidHom g b) := rfl

theorem modelBaseSquareAction_intertwines (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelBase S e : Set G))
    (q : baseSubgroup (2 ^ n) ⧸ frattini (baseSubgroup (2 ^ n))) :
    modelBaseSquareAction n S e g (modelBaseFrattiniSquareQuotientEquiv n S e q) =
      modelBaseFrattiniSquareQuotientEquiv n S e
        (CFSG.LargeEvenClassification.Helpers.frattiniAutAction
          (baseSubgroup (2 ^ n)) (modelBaseAction S e g) q) := by
  induction q using QuotientGroup.induction_on with
  | H b =>
    change modelBaseSquareAction n S e g
      (modelBaseFrattiniSquareQuotientEquiv n S e
        ((QuotientGroup.mk' (frattini (baseSubgroup (2 ^ n)))) b)) = _
    rw [modelBaseFrattiniSquareQuotientEquiv_mk, modelBaseSquareAction_mk]
    change (QuotientGroup.mk' (squareSubgroup (modelBase S e)))
      ((modelBase S e).normalizerMonoidHom g (modelBaseEquiv S e b)) =
        modelBaseFrattiniSquareQuotientEquiv n S e
          ((QuotientGroup.mk' (frattini (baseSubgroup (2 ^ n)))) (modelBaseAction S e g b))
    rw [modelBaseFrattiniSquareQuotientEquiv_mk]
    congr 1
    exact ((modelBaseEquiv S e).apply_symm_apply
      ((modelBase S e).normalizerMonoidHom g (modelBaseEquiv S e b))).symm

theorem modelBaseSquareAction_eq_congr_frattini (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) :
    modelBaseSquareAction n S e =
      (MulAut.congr (modelBaseFrattiniSquareQuotientEquiv n S e)).toMonoidHom.comp
        ((CFSG.LargeEvenClassification.Helpers.frattiniAutAction
          (baseSubgroup (2 ^ n))).comp (modelBaseAction S e)) := by
  ext g q
  obtain ⟨b, rfl⟩ := (modelBaseFrattiniSquareQuotientEquiv n S e).surjective q
  change modelBaseSquareAction n S e g (modelBaseFrattiniSquareQuotientEquiv n S e b) =
    modelBaseFrattiniSquareQuotientEquiv n S e
      (CFSG.LargeEvenClassification.Helpers.frattiniAutAction
        (baseSubgroup (2 ^ n)) (modelBaseAction S e g)
          ((modelBaseFrattiniSquareQuotientEquiv n S e).symm
            (modelBaseFrattiniSquareQuotientEquiv n S e b)))
  rw [MulEquiv.symm_apply_apply]
  exact modelBaseSquareAction_intertwines n S e g b

theorem modelBaseSquareAction_ker [Finite G] (n : ℕ) (hn : 1 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (modelBaseSquareAction n S e).ker =
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) := by
  rw [modelBaseSquareAction_eq_congr_frattini,
    MonoidHom.ker_comp_of_injective _ _
      (MulAut.congr (modelBaseFrattiniSquareQuotientEquiv n S e)).injective,
    ← modelBaseAction_ker S e]
  ext g
  constructor
  · intro hg
    let a : (modelBaseAction S e).range := ⟨modelBaseAction S e g, ⟨g, rfl⟩⟩
    have ha : a = 1 := modelBaseAction_range_reduction_injective n hn S e
      (show ((CFSG.LargeEvenClassification.Helpers.frattiniAutAction
        (baseSubgroup (2 ^ n))).domRestrict (modelBaseAction S e).range) a =
          ((CFSG.LargeEvenClassification.Helpers.frattiniAutAction
            (baseSubgroup (2 ^ n))).domRestrict (modelBaseAction S e).range) 1 from
              hg.trans (map_one _).symm)
    exact congrArg Subtype.val ha
  · intro hg
    change CFSG.LargeEvenClassification.Helpers.frattiniAutAction
      (baseSubgroup (2 ^ n)) (modelBaseAction S e g) = 1
    rw [show modelBaseAction S e g = 1 from hg, map_one]

@[expose] def modelBaseNormalizerSquareQuotientEquiv [Finite G]
    (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) ≃*
          (modelBaseSquareAction n S e).range :=
  (QuotientGroup.quotientMulEquivOfEq
    (modelBaseSquareAction_ker n hn S e).symm).trans
      (QuotientGroup.quotientKerEquivRange (modelBaseSquareAction n S e))

@[expose] def modelBaseNormalizerSquareQuotientAction [Finite G]
    (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) →*
          MulAut (modelBase S e ⧸ squareSubgroup (modelBase S e)) :=
  (modelBaseSquareAction n S e).range.subtype.comp
    (modelBaseNormalizerSquareQuotientEquiv n hn S e).toMonoidHom

theorem modelBaseNormalizerSquareQuotientAction_injective [Finite G]
    (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Function.Injective (modelBaseNormalizerSquareQuotientAction n hn S e) :=
  (modelBaseSquareAction n S e).range.subtype_injective.comp
    (modelBaseNormalizerSquareQuotientEquiv n hn S e).injective

theorem modelBaseNormalizerSquareQuotientAction_mk [Finite G]
    (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer (modelBase S e : Set G)) :
    modelBaseNormalizerSquareQuotientAction n hn S e
      ((QuotientGroup.mk' ((Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)))) g) =
          modelBaseSquareAction n S e g := rfl

theorem modelBase_square_quotient_card (n : ℕ) (hn : 1 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nat.card (modelBase S e ⧸ squareSubgroup (modelBase S e)) = 4 := by
  rw [← Nat.card_congr (modelBaseFrattiniSquareQuotientEquiv n S e).toEquiv]
  exact base_frattini_quotient_card n hn

end CFSG.Wreathed
