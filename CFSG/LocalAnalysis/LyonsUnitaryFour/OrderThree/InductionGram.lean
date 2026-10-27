module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderThree.OrbitCharacters
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.SylowKernel
public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderThreeComplement

public section

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical

variable {G : Type} [Group G]

section Centralizers

theorem natCard_centralizer_mulEquiv {A : Type*} [Group A] (φ : A ≃* A) (a : A) :
    Nat.card (Subgroup.centralizer {φ a}) = Nat.card (Subgroup.centralizer {a}) := by
  symm
  refine Nat.card_congr (Equiv.subtypeEquiv φ.toEquiv fun y => ?_)
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  change y * a = a * y ↔ φ y * φ a = φ a * φ y
  rw [← map_mul, ← map_mul, φ.injective.eq_iff]

theorem natCard_centralizer_subgroup (S : Subgroup G) (x : S) :
    Nat.card (Subgroup.centralizer {x}) =
      Nat.card ((S ⊓ Subgroup.centralizer {(x : G)} : Subgroup G)) := by
  have hto : ∀ y : Subgroup.centralizer {x},
      (y : S).val ∈ (S ⊓ Subgroup.centralizer {(x : G)} : Subgroup G) := by
    intro y
    refine Subgroup.mem_inf.mpr ⟨(y : S).property, ?_⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp y.property
    exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val this)
  have hinv : ∀ y : (S ⊓ Subgroup.centralizer {(x : G)} : Subgroup G),
      (⟨y.val, (Subgroup.mem_inf.mp y.property).1⟩ : S) ∈ Subgroup.centralizer {x} := by
    intro y
    have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp y.property).2
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext this)
  exact Nat.card_congr
    { toFun := fun y => ⟨(y : S).val, hto y⟩
      invFun := fun y => ⟨⟨y.val, (Subgroup.mem_inf.mp y.property).1⟩, hinv y⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end Centralizers

section ThreeClasses

theorem three_class_sum [Fintype G] {S : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (S : Set G))
    (hgen : ∀ m ∈ Subgroup.normalizer (S : Set G), ∃ j : ℕ, j < 3 ∧ (n ^ j)⁻¹ * m ∈ innerActing S)
    (hfusion : ∀ P : Subgroup G, P ≤ S → ∀ g : G,
      P.map (MulAut.conj g⁻¹).toMonoidHom ≤ S →
      ∃ m ∈ Subgroup.normalizer (S : Set G), ∀ x ∈ P, m⁻¹ * x * m = g⁻¹ * x * g)
    (hsq : ∀ x ∈ S, x ^ 2 = 1 ↔ x ∈ (Subgroup.center S).map S.subtype)
    (hsqmem : ∀ x ∈ S, x ^ 2 ∈ (Subgroup.center S).map S.subtype)
    (hcomm : (Subgroup.center S).map S.subtype = ⁅S, S⁆)
    (hfix : ∀ j : ℕ, 0 < j → j < 3 → ∀ z ∈ (Subgroup.center S).map S.subtype,
      z ≠ 1 → n ^ j * z * (n ^ j)⁻¹ ≠ z)
    (x : S) (hx1 : x ≠ 1) (f : S → ℂ) (hf : ∀ c y : S, f (c * y * c⁻¹) = f y) :
    ∑ y : S, (if IsConj (x : G) (y : G) then
        (Nat.card ((S ⊓ Subgroup.centralizer {(x : G)} : Subgroup G)) : ℂ) else 0) * f y =
      (Nat.card S : ℂ) * ∑ j : Fin 3, f (normalizerConj S (Subgroup.pow_mem _ hn (j : ℕ)) x) := by
  set w : Fin 3 → S := fun j => normalizerConj S (Subgroup.pow_mem _ hn (j : ℕ)) x with hw
  set c := Nat.card ((S ⊓ Subgroup.centralizer {(x : G)} : Subgroup G)) with hc
  have hwG : ∀ j : Fin 3, (w j : G) = (n ^ (j : ℕ))⁻¹ * x * n ^ (j : ℕ) := fun j => rfl
  have hx1' : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hfilter : Finset.univ.filter (fun y : S => IsConj (x : G) (y : G)) =
      (Finset.univ : Finset (Fin 3)).biUnion
        (fun j => Finset.univ.filter (fun y : S => IsConj (w j) y)) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    rw [isConj_iff_exists_pow hn hgen hfusion x.property y.property]
    constructor
    · rintro ⟨j, hj, s, hs, hy⟩
      refine ⟨⟨j, hj⟩, isConj_iff.mpr ⟨⟨s, hs⟩, Subtype.ext ?_⟩⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hwG]
      exact hy.symm
    · rintro ⟨j, hj⟩
      obtain ⟨s, hs⟩ := isConj_iff.mp hj
      refine ⟨j, j.isLt, s, s.property, ?_⟩
      have := congrArg Subtype.val hs
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      rw [← this, hwG]
  have hdisj : ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint
      (fun j => Finset.univ.filter (fun y : S => IsConj (w j) y)) := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_filter]
    intro y _ hiy hjy
    have hij' : IsConj (w i) (w j) := hiy.trans hjy.symm
    obtain ⟨s, hs⟩ := isConj_iff.mp hij'
    have hsG := congrArg Subtype.val hs
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hwG] at hsG
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · exact conj_pow_ne_conj_pow hn hsq hsqmem hcomm hfix x.property hx1' h j.isLt s.property
        hsG.symm
    · apply conj_pow_ne_conj_pow hn hsq hsqmem hcomm hfix x.property hx1' h i.isLt
        (S.inv_mem s.property)
      rw [← hsG]
      group
  have hsplit : ∑ y : S, (if IsConj (x : G) (y : G) then (c : ℂ) else 0) * f y =
      (c : ℂ) * ∑ y ∈ Finset.univ.filter (fun y : S => IsConj (x : G) (y : G)), f y := by
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y _
    split_ifs <;> simp
  rw [hsplit, hfilter, Finset.sum_biUnion hdisj, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hcls : ∑ y ∈ Finset.univ.filter (fun y : S => IsConj (w j) y), f y =
      ((Finset.univ.filter (fun y : S => IsConj (w j) y)).card : ℂ) * f (w j) := by
    rw [Finset.sum_congr rfl (fun y hy => ?_), Finset.sum_const, nsmul_eq_mul]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨c', rfl⟩ := isConj_iff.mp hy
    exact hf c' (w j)
  have hcard := card_conjClassFinset_mul (w j)
  have hcent : Nat.card (Subgroup.centralizer {w j}) = c := by
    rw [hw]
    simp only
    rw [natCard_centralizer_mulEquiv, natCard_centralizer_subgroup]
  rw [hcent] at hcard
  unfold conjClassFinset at hcard
  rw [hcls, ← hcard]
  ring

end ThreeClasses

section ScalarProduct

theorem scalarProduct_eq_sum {A : Type*} [Fintype A] (f g : A → ℂ) :
    CFSG.Section1.scalarProduct A f g = (Nat.card A : ℂ)⁻¹ * ∑ a, f a * star (g a) := by
  simp only [CFSG.Section1.scalarProduct]
  congr
  exact Subsingleton.elim _ _

theorem scalarProduct_finsetSum_left {A ι : Type*} [Finite A] (s : Finset ι) (Φ : ι → A → ℂ)
    (ψ : A → ℂ) :
    CFSG.Section1.scalarProduct A (fun a => ∑ i ∈ s, Φ i a) ψ =
      ∑ i ∈ s, CFSG.Section1.scalarProduct A (Φ i) ψ := by
  simp only [CFSG.Section1.scalarProduct, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]

theorem scalarProduct_finsetSum_right {A ι : Type*} [Finite A] (s : Finset ι) (φ : A → ℂ)
    (Ψ : ι → A → ℂ) :
    CFSG.Section1.scalarProduct A φ (fun a => ∑ i ∈ s, Ψ i a) =
      ∑ i ∈ s, CFSG.Section1.scalarProduct A φ (Ψ i) := by
  simp only [CFSG.Section1.scalarProduct, star_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem scalarProduct_mul_left {A : Type*} [Finite A] (z : ℂ) (φ ψ : A → ℂ) :
    CFSG.Section1.scalarProduct A (fun a => z * φ a) ψ =
      z * CFSG.Section1.scalarProduct A φ ψ := by
  unfold CFSG.Section1.scalarProduct
  rw [mul_left_comm z ((Nat.card A : ℂ)⁻¹)]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem scalarProduct_mul_right {A : Type*} [Finite A] (z : ℂ) (φ ψ : A → ℂ) :
    CFSG.Section1.scalarProduct A φ (fun a => z * ψ a) =
      star z * CFSG.Section1.scalarProduct A φ ψ := by
  unfold CFSG.Section1.scalarProduct
  rw [mul_left_comm (star z) ((Nat.card A : ℂ)⁻¹)]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [star_mul]
  ring

theorem scalarProduct_basis_character {A : Type*} [Group A] [Fintype A]
    (basis : FiniteIrreducibleCharacterBasis A) (a b : basis.index) :
    CFSG.Section1.scalarProduct A (basis.representation a).character
        (basis.representation b).character = if a = b then 1 else 0 := by
  rw [scalarProduct_eq_sum]
  have h := characterPairing_irreducible (basis.representation a) (basis.representation b)
    (basis.irreducible a) (basis.irreducible b)
  unfold characterPairing at h
  have hsum : ∑ g, (basis.representation a).character g *
      star ((basis.representation b).character g) =
      ∑ g, (basis.representation a).character g * (basis.representation b).character g⁻¹ := by
    apply Finset.sum_congr rfl
    intro g _
    rw [← finite_character_conjugate_inverse]
    rfl
  rw [hsum, h]
  by_cases hab : a = b
  · subst hab
    simp
  · rw [ite_eq_right (fun h' => hab (basis.distinct h')), ite_eq_right hab]

theorem character_isClassFunction {A : Type*} [Group A] (data : FiniteComplexRepresentation A) :
    CFSG.Section1.IsClassFunction data.character :=
  fun x g => Representation.char_conj data.representation g x

theorem scalarProduct_inducedCF_character [Fintype G] (S : Subgroup G) (θ : S → ℂ)
    (data : FiniteComplexRepresentation G) :
    CFSG.Section1.scalarProduct G (CFSG.Section1.inducedCF S θ) data.character =
      CFSG.Section1.scalarProduct S θ (fun x => data.character x) :=
  CFSG.Section1.inducedClassFunction_frobenius_general S θ data.character
    (character_isClassFunction data)

end ScalarProduct

section Projection

@[expose] noncomputable def blockInduction [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (B : Finset basis.index) (S : Subgroup G) (θ : S → ℂ) : G → ℂ :=
  fun g => ∑ label ∈ B, CFSG.Section1.scalarProduct G (CFSG.Section1.inducedCF S θ)
      (basis.representation label).character * (basis.representation label).character g

theorem scalarProduct_blockInduction [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (B : Finset basis.index) (S : Subgroup G) (θ η : S → ℂ) :
    CFSG.Section1.scalarProduct G (blockInduction basis B S θ) (blockInduction basis B S η) =
      ∑ label ∈ B, CFSG.Section1.scalarProduct S θ
          (fun x => (basis.representation label).character x) *
        star (CFSG.Section1.scalarProduct S η
          (fun x => (basis.representation label).character x)) := by
  unfold blockInduction
  rw [scalarProduct_finsetSum_left]
  apply Finset.sum_congr rfl
  intro a ha
  rw [scalarProduct_mul_left, scalarProduct_finsetSum_right]
  simp_rw [scalarProduct_mul_right, scalarProduct_basis_character, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq B a, ite_eq_left ha, scalarProduct_inducedCF_character,
    scalarProduct_inducedCF_character]

end Projection

section Gram

theorem blockInduction_gram [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (B : Finset basis.index) {S : Subgroup G} {n : G} (hn : n ∈ Subgroup.normalizer (S : Set G))
    (hker : ∀ x ∈ S, x ≠ 1 → ∀ y ∈ S, ∑ ξ ∈ B, (basis.representation ξ).character x *
      starRingEnd ℂ ((basis.representation ξ).character y) =
        if IsConj x y then (Nat.card ((S ⊓ Subgroup.centralizer {x} : Subgroup G)) : ℂ) else 0)
    (hclass : ∀ x : S, x ≠ 1 → ∀ f : S → ℂ, (∀ c y : S, f (c * y * c⁻¹) = f y) →
      ∑ y : S, (if IsConj (x : G) (y : G) then
        (Nat.card ((S ⊓ Subgroup.centralizer {(x : G)} : Subgroup G)) : ℂ) else 0) * f y =
      (Nat.card S : ℂ) * ∑ j : Fin 3, f (normalizerConj S (Subgroup.pow_mem _ hn (j : ℕ)) x))
    (θ η : S → ℂ) (hθ : θ 1 = 0) (hη : ∀ c y : S, η (c * y * c⁻¹) = η y) :
    CFSG.Section1.scalarProduct G (blockInduction basis B S θ) (blockInduction basis B S η) =
      ∑ j : Fin 3, CFSG.Section1.scalarProduct S θ (conjugateCharacter S (n ^ (j : ℕ)) η) := by
  set s : ℂ := (Nat.card S : ℂ) with hs
  have hs0 : s ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  set w : Fin 3 → S → S := fun j => normalizerConj S (Subgroup.pow_mem _ hn (j : ℕ)) with hw
  have hK : ∀ x : S, x ≠ 1 → ∀ y : S,
      ∑ ξ ∈ B, star ((basis.representation ξ).character x) *
        (basis.representation ξ).character y =
      if IsConj (x : G) (y : G) then
        (Nat.card ((S ⊓ Subgroup.centralizer {(x : G)} : Subgroup G)) : ℂ) else 0 := by
    intro x hx y
    have h := hker x x.property (fun h' => hx (Subtype.ext h')) y y.property
    have h2 : ∑ ξ ∈ B, star ((basis.representation ξ).character x) *
        (basis.representation ξ).character y =
        star (∑ ξ ∈ B, (basis.representation ξ).character x *
          starRingEnd ℂ ((basis.representation ξ).character y)) := by
      rw [star_sum]
      apply Finset.sum_congr rfl
      intro ξ _
      rw [star_mul', starRingEnd_apply, star_star]
    rw [h2, h]
    split_ifs <;> simp
  have hcoef : ∀ ξ : basis.index,
      (s⁻¹ * ∑ x : S, θ x * star ((basis.representation ξ).character x)) *
        star (s⁻¹ * ∑ y : S, η y * star ((basis.representation ξ).character y)) =
      s⁻¹ * s⁻¹ * ∑ x : S, ∑ y : S, θ x * star (η y) *
        (star ((basis.representation ξ).character x) * (basis.representation ξ).character y) := by
    intro ξ
    have hst : star (s⁻¹ * ∑ y : S, η y * star ((basis.representation ξ).character y)) =
        s⁻¹ * ∑ y : S, star (η y) * (basis.representation ξ).character y := by
      rw [star_mul', star_sum, star_inv₀, hs, star_natCast]
      congr 1
      apply Finset.sum_congr rfl
      intro y _
      rw [star_mul', star_star]
    rw [hst]
    rw [show ∀ a b c d : ℂ, (a * b) * (c * d) = a * c * (b * d) from fun a b c d => by ring]
    congr 1
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [scalarProduct_blockInduction]
  simp_rw [scalarProduct_eq_sum]
  rw [Finset.sum_congr rfl (fun ξ _ => hcoef ξ), ← Finset.mul_sum, Finset.sum_comm]
  have hx : ∀ x : S, ∑ ξ ∈ B, ∑ y : S, θ x * star (η y) *
      (star ((basis.representation ξ).character x) * (basis.representation ξ).character y) =
      θ x * (s * ∑ j : Fin 3, star (η (w j x))) := by
    intro x
    by_cases hx1 : x = 1
    · rw [hx1, hθ]
      simp
    · rw [Finset.sum_comm]
      have hrw : ∀ y : S, ∑ ξ ∈ B, θ x * star (η y) *
          (star ((basis.representation ξ).character x) * (basis.representation ξ).character y) =
          θ x * ((if IsConj (x : G) (y : G) then
            (Nat.card ((S ⊓ Subgroup.centralizer {(x : G)} : Subgroup G)) : ℂ) else 0) *
              star (η y)) := by
        intro y
        rw [← hK x hx1 y, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ξ _
        ring
      rw [Finset.sum_congr rfl (fun y _ => hrw y), ← Finset.mul_sum,
        hclass x hx1 (fun y => star (η y)) (fun c y => by rw [hη])]
  rw [Finset.sum_congr rfl (fun x _ => hx x)]
  have hrhs : ∀ j : Fin 3, ∑ x : S, θ x * star (conjugateCharacter S (n ^ (j : ℕ)) η x) =
      ∑ x : S, θ x * star (η (w j x)) := by
    intro j
    rw [conjugateCharacter_eq_comp (Subgroup.pow_mem _ hn (j : ℕ))]
    rfl
  have hfin : ∀ x : S, θ x * (s * ∑ j : Fin 3, star (η (w j x))) =
      s * ∑ j : Fin 3, θ x * star (η (w j x)) := by
    intro x
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hL : s⁻¹ * s⁻¹ * ∑ x : S, θ x * (s * ∑ j : Fin 3, star (η (w j x))) =
      s⁻¹ * ∑ x : S, ∑ j : Fin 3, θ x * star (η (w j x)) := by
    rw [Finset.sum_congr rfl (fun x _ => hfin x), ← Finset.mul_sum]
    field_simp
  have hR : ∑ j : Fin 3, s⁻¹ * ∑ x : S, θ x * star (η (w j x)) =
      s⁻¹ * ∑ x : S, ∑ j : Fin 3, θ x * star (η (w j x)) := by
    rw [← Finset.mul_sum, Finset.sum_comm]
  rw [hL, ← hR]
  apply Finset.sum_congr rfl
  intro j _
  rw [hrhs j]

end Gram

section Integrality

theorem scalarProduct_restrict_integer [Fintype G] (S : Subgroup G) {θ : S → ℂ}
    (hθ : θ ∈ CFSG.BlocksVChar S) (data : FiniteComplexRepresentation.{0, 0} G) :
    ∃ k : ℤ, CFSG.Section1.scalarProduct S θ (fun x => data.character x) = k := by
  have hθ' : θ ∈ virtualCharacters S := by
    rw [CFSG.blocksVChar_eq_virtualCharacters] at hθ
    exact hθ
  have hres : (fun x : S => data.character x) ∈ virtualCharacters S :=
    Submodule.subset_span ⟨inflatedFiniteComplexRepresentation S.subtype data, rfl⟩
  obtain ⟨k, hk⟩ := characterPairing_virtual_integer θ _ hθ' hres
  refine ⟨k, ?_⟩
  rw [← hk, scalarProduct_eq_sum]
  unfold characterPairing
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  exact finite_character_conjugate_inverse data (x : G)

theorem basis_character_mem_blocksIrr {A : Type} [Group A] [Fintype A]
    (basis : FiniteIrreducibleCharacterBasis A) (label : basis.index) :
    (basis.representation label).character ∈ CFSG.BlocksIrr A := by
  rw [CFSG.blocksIrr_eq_irreducible_characters]
  exact ⟨basis.representation label, basis.irreducible label, rfl⟩

theorem blockInduction_mem_blocksVChar [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)
    (B : Finset basis.index) (S : Subgroup G) {θ : S → ℂ} (hθ : θ ∈ CFSG.BlocksVChar S) :
    blockInduction basis B S θ ∈ CFSG.BlocksVChar G := by
  choose k hk using fun ξ => scalarProduct_restrict_integer S hθ (basis.representation ξ)
  have heq : blockInduction basis B S θ = ∑ ξ ∈ B, k ξ • (basis.representation ξ).character := by
    funext g
    rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro ξ _
    rw [Pi.smul_apply, zsmul_eq_mul, scalarProduct_inducedCF_character, hk]
  rw [heq]
  apply AddSubgroup.sum_mem
  intro ξ _
  apply AddSubgroup.zsmul_mem
  exact AddSubgroup.subset_closure (basis_character_mem_blocksIrr basis ξ)

end Integrality

section LocalFacts

theorem unitaryFourSylowShape_of_mulEquiv {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T))) :
    UnitaryFourSylowShape (S : Subgroup G) := by
  obtain ⟨hcard, hcz, hsq, hsqmem, hZ⟩ := unitary_four_sylow_structure hT S U hSU
  have hK : Nat.card (GaloisField 2 4) = 16 := by
    rw [GaloisField.card 2 4 (by norm_num)]
    norm_num
  obtain ⟨φ⟩ := CFSG.RankTwoShapes.nonempty_sylow_equiv_unitaryFourW hT U (GaloisField 2 4) hK
  obtain ⟨e₀⟩ := hSU
  set ψ := e₀.trans φ
  refine ⟨hcard, hcz, hsq, hsqmem, hZ, fun x hx => ?_⟩
  have hψx : ψ x ∉ Subgroup.center (CFSG.RankTwoShapes.unitaryFourW (GaloisField 2 4) hK) := by
    rwa [mem_center_iff_of_mulEquiv ψ x]
  have hfst : CFSG.RankTwoShapes.UnitaryFourW.fst (ψ x) ≠ 0 := by
    intro h0
    apply hψx
    rw [CFSG.RankTwoShapes.UnitaryFourW.center_eq_ker_firstCoord,
      CFSG.RankTwoShapes.UnitaryFourW.mem_ker_firstCoord]
    exact h0
  rw [← CFSG.RankTwoShapes.UnitaryFourW.natCard_centralizer (ψ x) hfst]
  refine Nat.card_congr (Equiv.subtypeEquiv ψ.toEquiv fun y => ?_)
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  change y * x = x * y ↔ ψ y * ψ x = ψ x * ψ y
  rw [← map_mul, ← map_mul, ψ.injective.eq_iff]

theorem lyons_order_three_local_kernel_hypotheses [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T)))
    (hd : (((S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
      (Subgroup.normalizer ((S : Subgroup G) : Set G))).index = 3) :
    (∀ u ∈ (S : Subgroup G), u ≠ 1 →
      ∃ Q : Sylow 2 (Subgroup.centralizer {u}),
        (Q : Subgroup (Subgroup.centralizer {u})) =
          ((S : Subgroup G) ⊓ Subgroup.centralizer {u}).subgroupOf
            (Subgroup.centralizer {u})) ∧
    (∀ u ∈ (S : Subgroup G), u ≠ 1 →
      ∃ (K : Subgroup (Subgroup.centralizer {u})) (_ : K.Normal),
        Nat.Coprime 2 (Nat.card K) ∧ IsPGroup 2 (Subgroup.centralizer {u} ⧸ K)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hsq, -, -, -, -, -, -, -, -, -⟩ :=
    lyons_unitary_four_fusion_and_centralizers hnonab hT S U hSU
  obtain ⟨hcard, -, -, hsqmem, -⟩ := unitary_four_sylow_structure hT S U hSU
  have hcomp := (lyons_order_three_normalizer_involution_complements hnonab hT S U hSU hd).1
  set Sg := (S : Subgroup G) with hSg
  set Z := (Subgroup.center Sg).map Sg.subtype with hZ
  have hsqmem' : ∀ u ∈ Sg, u ^ 2 ∈ Z := by
    intro u hu
    exact ⟨⟨u, hu⟩ ^ 2, hsqmem ⟨u, hu⟩, rfl⟩
  have hcases : ∀ u ∈ Sg, u ≠ 1 → u ∈ Z ∨ orderOf u = 4 := by
    intro u hu hu1
    by_cases h2 : u ^ 2 = 1
    · exact Or.inl ((hsq u hu).mp h2)
    · right
      have h4 : u ^ 2 ^ (1 + 1) = 1 := by
        have h := (hsq (u ^ 2) (Sg.pow_mem hu 2)).mpr (hsqmem' u hu)
        rw [← pow_mul] at h
        simpa using h
      have := orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using h2) h4
      simpa using this
  have hcentral : ∀ u ∈ Z, u ≠ 1 →
      Nat.card (Subgroup.centralizer ({u} : Set G) ⧸
        CFSG.oddCore (Subgroup.centralizer ({u} : Set G))) = 64 ∧
      Sg ≤ Subgroup.centralizer ({u} : Set G) := by
    intro u hu hu1
    obtain ⟨-, -, hbij⟩ := hcomp u hu hu1
    have hSC : Sg ≤ Subgroup.centralizer ({u} : Set G) := by
      intro s hs
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mem_map_center_iff.mp hu).2 s hs
    refine ⟨?_, hSC⟩
    rw [← Nat.card_eq_of_bijective _ hbij,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv, hcard]
  constructor
  · intro u hu hu1
    rcases hcases u hu hu1 with hZu | h4
    · obtain ⟨hquot, hSC⟩ := hcentral u hZu hu1
      set C := Subgroup.centralizer ({u} : Set G) with hC
      set H := (Sg ⊓ C).subgroupOf C with hH
      have hHcard : Nat.card H = 64 := by
        rw [hH, inf_of_le_left hSC, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv,
          hcard]
      have hHp : IsPGroup 2 H := IsPGroup.of_card (n := 6) (by rw [hHcard]; norm_num)
      have hidx : ¬ 2 ∣ H.index := by
        have h1 := Subgroup.card_mul_index H
        have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.oddCore C)
        rw [hquot] at h2
        rw [hHcard, h2] at h1
        have h3 : H.index = Nat.card (CFSG.oddCore C) := by omega
        rw [h3]
        exact Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp (odd_card_oddCore C))
      exact ⟨hHp.toSylow hidx, IsPGroup.toSylow_coe hHp hidx⟩
    · obtain ⟨-, hP, -⟩ := unitary_four_order_four_centralizer_odd_complement hT S U hSU hu h4
      exact hP
  · intro u hu hu1
    refine ⟨CFSG.oddCore _, inferInstance, Nat.coprime_two_left.mpr (odd_card_oddCore _), ?_⟩
    rcases hcases u hu hu1 with hZu | h4
    · obtain ⟨hquot, -⟩ := hcentral u hZu hu1
      exact IsPGroup.of_card (n := 6) (by rw [hquot]; norm_num)
    · obtain ⟨-, -, -, -, -, hidx, -⟩ :=
        unitary_four_order_four_centralizer_odd_complement hT S U hSU hu h4
      exact IsPGroup.of_card (n := 4) (by rw [← Subgroup.index_eq_card, hidx]; norm_num)

end LocalFacts

section Restriction

theorem scalarProduct_blocksIrr {A : Type} [Group A] [Fintype A] {θ θ' : A → ℂ}
    (hθ : θ ∈ CFSG.BlocksIrr A) (hθ' : θ' ∈ CFSG.BlocksIrr A) :
    CFSG.Section1.scalarProduct A θ θ' = if θ = θ' then 1 else 0 := by
  rw [CFSG.blocksIrr_eq_irreducible_characters] at hθ hθ'
  obtain ⟨d, hd, rfl⟩ := hθ
  obtain ⟨d', hd', rfl⟩ := hθ'
  rw [scalarProduct_eq_sum, ← characterPairing_irreducible d d' hd hd']
  unfold characterPairing
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  congr 1
  exact finite_character_conjugate_inverse d' g

theorem scalarProduct_comp_mulEquiv {A : Type*} [Group A] [Fintype A] (φ : A ≃* A)
    (f θ : A → ℂ) (hf : ∀ x, f (φ x) = f x) :
    CFSG.Section1.scalarProduct A f (θ ∘ φ) = CFSG.Section1.scalarProduct A f θ := by
  rw [scalarProduct_eq_sum, scalarProduct_eq_sum]
  congr 1
  rw [← Equiv.sum_comp φ.toEquiv (fun y => f y * star (θ y))]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Function.comp_apply, MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, hf]

theorem sum_irreducible_expansion {A : Type} [Group A] [Fintype A] {ι : Type*} [Fintype ι]
    (Θ : ι → A → ℂ) (hΘinj : Function.Injective Θ) (hΘirr : ∀ t, Θ t ∈ CFSG.BlocksIrr A)
    (hcover : ∀ χ ∈ CFSG.BlocksIrr A, ∃ t, χ = Θ t) {size : ℕ} (θ : Fin size → A → ℂ)
    (hθ : ∀ k, θ k ∈ CFSG.BlocksIrr A) :
    ∃ m : ι → ℕ,
      (∀ t, (m t : ℂ) = CFSG.Section1.scalarProduct A (fun x => ∑ k, θ k x) (Θ t)) ∧
      ∀ x, ∑ k, θ k x = ∑ t, (m t : ℂ) * Θ t x := by
  classical
  choose idx hidx using fun k => hcover (θ k) (hθ k)
  have hiff : ∀ k t, θ k = Θ t ↔ idx k = t := by
    intro k t
    rw [hidx k]
    exact hΘinj.eq_iff
  refine ⟨fun t => (Finset.univ.filter (fun k => idx k = t)).card, fun t => ?_, fun x => ?_⟩
  · rw [CFSG.Section1.scalarProduct_fintype_sum_left]
    simp_rw [scalarProduct_blocksIrr (hθ _) (hΘirr t), hiff]
    rw [Finset.sum_boole]
  · rw [← Finset.sum_fiberwise Finset.univ idx (fun k => θ k x)]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.sum_congr rfl (fun k hk => ?_), Finset.sum_const, nsmul_eq_mul]
    rw [Finset.mem_filter] at hk
    rw [hidx k, hk.2]

@[expose] noncomputable def orbitEnum (S : Subgroup G) (n : G) (lam : Fin 5 → S → ℂ)
    (ψ : S → ℂ) : Option (Option (Fin 5) × Fin 3) → S → ℂ
  | none => 1
  | some (some i, a) => conjugateCharacter S (n ^ (a : ℕ)) (lam i)
  | some (none, a) => conjugateCharacter S (n ^ (a : ℕ)) ψ

theorem one_mem_blocksIrr (A : Type) [Group A] : (1 : A → ℂ) ∈ CFSG.BlocksIrr A := by
  rw [CFSG.blocksIrr_eq_irreducible_characters]
  refine ⟨principalFiniteComplexRepresentation A,
    principalFiniteComplexRepresentation_isIrreducible A, ?_⟩
  rw [principalFiniteComplexRepresentation_character]

theorem conjugateCharacter_ne_one {S : Subgroup G} {m : G}
    (hm : m ∈ Subgroup.normalizer (S : Set G)) {θ : S → ℂ} (hθ : θ ≠ 1) :
    conjugateCharacter S m θ ≠ 1 := by
  intro h
  apply hθ
  have := congrArg (conjugateCharacter S m⁻¹) h
  rwa [conjugateCharacter_mul (inv_mem hm) hm, inv_mul_cancel, conjugateCharacter_one,
    conjugateCharacter_one_fun S _ (inv_mem hm)] at this

theorem scalarProduct_sub_left' {A : Type*} [Finite A] (f g h : A → ℂ) :
    CFSG.Section1.scalarProduct A (f - g) h =
      CFSG.Section1.scalarProduct A f h - CFSG.Section1.scalarProduct A g h := by
  simp only [CFSG.Section1.scalarProduct, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]

theorem scalarProduct_sub_right' {A : Type*} [Finite A] (f g h : A → ℂ) :
    CFSG.Section1.scalarProduct A f (g - h) =
      CFSG.Section1.scalarProduct A f g - CFSG.Section1.scalarProduct A f h := by
  simp only [CFSG.Section1.scalarProduct, Pi.sub_apply, star_sub, mul_sub, Finset.sum_sub_distrib]

theorem scalarProduct_smul_left' {A : Type*} [Finite A] (c : ℂ) (f g : A → ℂ) :
    CFSG.Section1.scalarProduct A (c • f) g = c * CFSG.Section1.scalarProduct A f g :=
  scalarProduct_mul_left c f g

theorem scalarProduct_smul_right' {A : Type*} [Finite A] (c : ℂ) (f g : A → ℂ) :
    CFSG.Section1.scalarProduct A f (c • g) = star c * CFSG.Section1.scalarProduct A f g :=
  scalarProduct_mul_right c f g

section OrbitEnum

variable {S : Subgroup G} {n : G} (hn : n ∈ Subgroup.normalizer (S : Set G))
  {lam : Fin 5 → S → ℂ} {ψ : S → ℂ}
  (hlam : ∀ i, lam i ∈ CFSG.BlocksIrr S ∧ lam i 1 = 1 ∧ lam i ≠ 1)
  (hψ : ψ ∈ CFSG.BlocksIrr S) (hψ4 : ψ 1 = 4)
  (hinjL : ∀ (i i' : Fin 5) (a b : Fin 3), conjugateCharacter S (n ^ (a : ℕ)) (lam i) =
    conjugateCharacter S (n ^ (b : ℕ)) (lam i') → i = i' ∧ a = b)
  (hinjD : ∀ a b : Fin 3, conjugateCharacter S (n ^ (a : ℕ)) ψ =
    conjugateCharacter S (n ^ (b : ℕ)) ψ → a = b)
  (hcover : ∀ χ ∈ CFSG.BlocksIrr S, χ ≠ 1 →
    (∃ (i : Fin 5) (a : Fin 3), χ = conjugateCharacter S (n ^ (a : ℕ)) (lam i)) ∨
      ∃ a : Fin 3, χ = conjugateCharacter S (n ^ (a : ℕ)) ψ)
include hn

include hlam hψ in
theorem orbitEnum_mem (t : Option (Option (Fin 5) × Fin 3)) :
    orbitEnum S n lam ψ t ∈ CFSG.BlocksIrr S := by
  rcases t with _ | ⟨_ | i, a⟩
  · exact one_mem_blocksIrr S
  · exact conjugateCharacter_mem_blocksIrr (Subgroup.pow_mem _ hn _) hψ
  · exact conjugateCharacter_mem_blocksIrr (Subgroup.pow_mem _ hn _) (hlam i).1

include hlam hψ4 hinjL hinjD in
theorem orbitEnum_injective : Function.Injective (orbitEnum S n lam ψ) := by
  have hpow : ∀ a : ℕ, n ^ a ∈ Subgroup.normalizer (S : Set G) :=
    fun a => Subgroup.pow_mem _ hn a
  have hψ1 : ψ ≠ 1 := by
    intro h
    rw [h] at hψ4
    norm_num at hψ4
  have hdegL : ∀ (i : Fin 5) (a : ℕ), conjugateCharacter S (n ^ a) (lam i) 1 = 1 := by
    intro i a
    rw [conjugateCharacter_apply_one (hpow a), (hlam i).2.1]
  have hdegD : ∀ a : ℕ, conjugateCharacter S (n ^ a) ψ 1 = 4 := by
    intro a
    rw [conjugateCharacter_apply_one (hpow a), hψ4]
  rintro (_ | ⟨_ | i, a⟩) (_ | ⟨_ | i', b⟩) h
  · rfl
  · exact absurd h.symm (conjugateCharacter_ne_one (hpow _) hψ1)
  · exact absurd h.symm (conjugateCharacter_ne_one (hpow _) (hlam i').2.2)
  · exact absurd h (conjugateCharacter_ne_one (hpow _) hψ1)
  · rw [hinjD a b h]
  · have := congrFun h 1
    change conjugateCharacter S (n ^ (a : ℕ)) ψ 1 =
      conjugateCharacter S (n ^ (b : ℕ)) (lam i') 1 at this
    rw [hdegD, hdegL] at this
    norm_num at this
  · exact absurd h (conjugateCharacter_ne_one (hpow _) (hlam i).2.2)
  · have := congrFun h 1
    change conjugateCharacter S (n ^ (a : ℕ)) (lam i) 1 =
      conjugateCharacter S (n ^ (b : ℕ)) ψ 1 at this
    rw [hdegD, hdegL] at this
    norm_num at this
  · obtain ⟨rfl, rfl⟩ := hinjL i i' a b h
    rfl

omit hn in
include hcover in
theorem orbitEnum_cover : ∀ χ ∈ CFSG.BlocksIrr S, ∃ t, χ = orbitEnum S n lam ψ t := by
  intro χ hχ
  by_cases h1 : χ = 1
  · exact ⟨none, h1⟩
  · rcases hcover χ hχ h1 with ⟨i, a, h⟩ | ⟨a, h⟩
    · exact ⟨some (some i, a), h⟩
    · exact ⟨some (none, a), h⟩

include hlam hψ hψ4 hinjL hinjD in
theorem scalarProduct_orbitEnum [Fintype G] (t u : Option (Option (Fin 5) × Fin 3)) :
    CFSG.Section1.scalarProduct S (orbitEnum S n lam ψ t) (orbitEnum S n lam ψ u) =
      if t = u then 1 else 0 := by
  rw [scalarProduct_blocksIrr (orbitEnum_mem hn hlam hψ t) (orbitEnum_mem hn hlam hψ u)]
  by_cases h : t = u
  · subst h
    simp
  · rw [ite_eq_right (fun h' => h (orbitEnum_injective hn hlam hψ4 hinjL hinjD h')),
      ite_eq_right h]

include hlam hψ hψ4 hinjL hinjD in
theorem scalarProduct_orbitEnum_sub [Fintype G] (c : ℂ)
    (t u t' u' : Option (Option (Fin 5) × Fin 3)) :
    CFSG.Section1.scalarProduct S (orbitEnum S n lam ψ t - c • orbitEnum S n lam ψ u)
        (orbitEnum S n lam ψ t' - c • orbitEnum S n lam ψ u') =
      (if t = t' then 1 else 0) - star c * (if t = u' then 1 else 0) -
        c * (if u = t' then 1 else 0) + c * star c * (if u = u' then 1 else 0) := by
  rw [scalarProduct_sub_left', scalarProduct_sub_right', scalarProduct_sub_right',
    scalarProduct_smul_right', scalarProduct_smul_left', scalarProduct_smul_left',
    scalarProduct_smul_right']
  simp only [scalarProduct_orbitEnum hn hlam hψ hψ4 hinjL hinjD]
  ring

include hlam hψ hψ4 hinjL hinjD in
theorem scalarProduct_orbitEnum_sub_one [Fintype G]
    (t u t' u' : Option (Option (Fin 5) × Fin 3)) :
    CFSG.Section1.scalarProduct S (orbitEnum S n lam ψ t - orbitEnum S n lam ψ u)
        (orbitEnum S n lam ψ t' - orbitEnum S n lam ψ u') =
      (if t = t' then 1 else 0) - (if t = u' then 1 else 0) -
        (if u = t' then 1 else 0) + (if u = u' then 1 else 0) := by
  rw [scalarProduct_sub_left', scalarProduct_sub_right', scalarProduct_sub_right']
  simp only [scalarProduct_orbitEnum hn hlam hψ hψ4 hinjL hinjD]
  ring

include hlam hψ hψ4 hinjL hinjD in
theorem orbit_norm_values [Fintype G] :
    ∑ a : Fin 3, CFSG.Section1.scalarProduct S (lam 0 - 1)
        (conjugateCharacter S (n ^ (a : ℕ)) (lam 0 - 1)) = 4 ∧
    (∀ i : Fin 5, i ≠ 0 → ∑ a : Fin 3, CFSG.Section1.scalarProduct S (lam i - lam 0)
        (conjugateCharacter S (n ^ (a : ℕ)) (lam i - lam 0)) = 2) ∧
    ∑ a : Fin 3, CFSG.Section1.scalarProduct S (ψ - (4 : ℂ) • lam 0)
        (conjugateCharacter S (n ^ (a : ℕ)) (ψ - (4 : ℂ) • lam 0)) = 17 := by
  have hpow : ∀ a : ℕ, n ^ a ∈ Subgroup.normalizer (S : Set G) :=
    fun a => Subgroup.pow_mem _ hn a
  have hconj_sub : ∀ (a : ℕ) (f g : S → ℂ), conjugateCharacter S (n ^ a) (f - g) =
      conjugateCharacter S (n ^ a) f - conjugateCharacter S (n ^ a) g := by
    intro a f g
    rw [conjugateCharacter_eq_comp (hpow a), conjugateCharacter_eq_comp (hpow a),
      conjugateCharacter_eq_comp (hpow a)]
    rfl
  have hconj_smul : ∀ (a : ℕ) (c : ℂ) (f : S → ℂ), conjugateCharacter S (n ^ a) (c • f) =
      c • conjugateCharacter S (n ^ a) f := by
    intro a c f
    rw [conjugateCharacter_eq_comp (hpow a), conjugateCharacter_eq_comp (hpow a)]
    rfl
  have hE : ∀ (i : Fin 5) (a : Fin 3), conjugateCharacter S (n ^ (a : ℕ)) (lam i) =
      orbitEnum S n lam ψ (some (some i, a)) := fun _ _ => rfl
  have hED : ∀ a : Fin 3, conjugateCharacter S (n ^ (a : ℕ)) ψ =
      orbitEnum S n lam ψ (some (none, a)) := fun _ => rfl
  have hE1 : ∀ a : ℕ, conjugateCharacter S (n ^ a) 1 = orbitEnum S n lam ψ none :=
    fun a => conjugateCharacter_one_fun S _ (hpow a)
  have hL0 : ∀ i, lam i = orbitEnum S n lam ψ (some (some i, 0)) := by
    intro i
    change lam i = conjugateCharacter S (n ^ ((0 : Fin 3) : ℕ)) (lam i)
    rw [Fin.val_zero, pow_zero, conjugateCharacter_one]
  have hD0 : ψ = orbitEnum S n lam ψ (some (none, 0)) := by
    change ψ = conjugateCharacter S (n ^ ((0 : Fin 3) : ℕ)) ψ
    rw [Fin.val_zero, pow_zero, conjugateCharacter_one]
  have h1 : (1 : S → ℂ) = orbitEnum S n lam ψ none := rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [hconj_sub, hE, hE1]
    rw [hL0 0, h1]
    simp only [scalarProduct_orbitEnum_sub_one hn hlam hψ hψ4 hinjL hinjD, Fin.sum_univ_three]
    simp
    norm_num
  · intro i hi
    simp only [hconj_sub, hE]
    rw [hL0 i, hL0 0]
    simp only [scalarProduct_orbitEnum_sub_one hn hlam hψ hψ4 hinjL hinjD, Fin.sum_univ_three]
    simp [hi, Ne.symm hi]
    norm_num
  · have hθψ : ψ - (4 : ℂ) • lam 0 = orbitEnum S n lam ψ (some (none, 0)) -
        (4 : ℂ) • orbitEnum S n lam ψ (some (some 0, 0)) := by
      rw [← hL0 0]
      congr 1
    simp only [hconj_sub, hconj_smul, hE, hED]
    rw [hθψ]
    simp only [scalarProduct_orbitEnum_sub hn hlam hψ hψ4 hinjL hinjD, Fin.sum_univ_three]
    simp
    norm_num

end OrbitEnum

theorem restriction_orbit_pattern [Fintype G] {S : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (S : Set G)) (lam : Fin 5 → S → ℂ) (ψ : S → ℂ)
    (hlam : ∀ i, lam i ∈ CFSG.BlocksIrr S ∧ lam i 1 = 1 ∧ lam i ≠ 1)
    (hψ : ψ ∈ CFSG.BlocksIrr S) (hψ4 : ψ 1 = 4)
    (hinjL : ∀ (i i' : Fin 5) (a b : Fin 3), conjugateCharacter S (n ^ (a : ℕ)) (lam i) =
      conjugateCharacter S (n ^ (b : ℕ)) (lam i') → i = i' ∧ a = b)
    (hinjD : ∀ a b : Fin 3, conjugateCharacter S (n ^ (a : ℕ)) ψ =
      conjugateCharacter S (n ^ (b : ℕ)) ψ → a = b)
    (hcover : ∀ χ ∈ CFSG.BlocksIrr S, χ ≠ 1 →
      (∃ (i : Fin 5) (a : Fin 3), χ = conjugateCharacter S (n ^ (a : ℕ)) (lam i)) ∨
        ∃ a : Fin 3, χ = conjugateCharacter S (n ^ (a : ℕ)) ψ)
    (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    ∃ (a₀ : ℕ) (b : Fin 5 → ℕ) (c : ℕ),
      (∀ x : S, ρ.character x = a₀ + ∑ i, (b i : ℂ) *
          ∑ a : Fin 3, conjugateCharacter S (n ^ (a : ℕ)) (lam i) x +
        c * ∑ a : Fin 3, conjugateCharacter S (n ^ (a : ℕ)) ψ x) ∧
      ρ.character 1 = a₀ + 3 * ∑ i, (b i : ℂ) + 12 * c ∧
      Module.finrank ℂ V = a₀ + 3 * ∑ i, b i + 12 * c := by
  classical
  have hpow : ∀ a : ℕ, n ^ a ∈ Subgroup.normalizer (S : Set G) := fun a => Subgroup.pow_mem _ hn a
  set Θ := orbitEnum S n lam ψ with hΘ
  let data : FiniteComplexRepresentation.{0, 0} S :=
    { vector := V, representation := ρ.comp S.subtype }
  obtain ⟨size, summand, hirr, hsum⟩ :=
    finiteComplexRepresentation_exists_irreducible_character_sum data
  have hsummand : ∀ k, (summand k).character ∈ CFSG.BlocksIrr S := by
    intro k
    rw [CFSG.blocksIrr_eq_irreducible_characters]
    exact ⟨summand k, hirr k, rfl⟩
  obtain ⟨m, hm, hexp⟩ := sum_irreducible_expansion Θ
    (orbitEnum_injective hn hlam hψ4 hinjL hinjD) (orbitEnum_mem hn hlam hψ)
    (orbitEnum_cover hcover) (fun k => (summand k).character) hsummand
  have hres : (fun x : S => ∑ k, (summand k).character x) = fun x : S => ρ.character x := by
    funext x
    rw [← hsum x]
    rfl
  have hinv : ∀ (a : ℕ) (θ : S → ℂ), CFSG.Section1.scalarProduct S (fun x : S => ρ.character x)
      (conjugateCharacter S (n ^ a) θ) =
      CFSG.Section1.scalarProduct S (fun x : S => ρ.character x) θ := by
    intro a θ
    rw [conjugateCharacter_eq_comp (hpow a)]
    apply scalarProduct_comp_mulEquiv
    intro x
    change ρ.character ((n ^ a)⁻¹ * x * n ^ a) = ρ.character x
    have := Representation.char_conj ρ (x : G) (n ^ a)⁻¹
    rwa [inv_inv] at this
  have hmL : ∀ (i : Fin 5) (a : Fin 3), m (some (some i, a)) = m (some (some i, 0)) := by
    intro i a
    have h1 := hm (some (some i, a))
    have h2 := hm (some (some i, 0))
    rw [hres] at h1 h2
    change _ = CFSG.Section1.scalarProduct S _ (conjugateCharacter S (n ^ (a : ℕ)) (lam i)) at h1
    change _ = CFSG.Section1.scalarProduct S _ (conjugateCharacter S (n ^ ((0 : Fin 3) : ℕ))
      (lam i)) at h2
    rw [hinv] at h1 h2
    exact_mod_cast h1.trans h2.symm
  have hmD : ∀ a : Fin 3, m (some (none, a)) = m (some (none, 0)) := by
    intro a
    have h1 := hm (some (none, a))
    have h2 := hm (some (none, 0))
    rw [hres] at h1 h2
    change _ = CFSG.Section1.scalarProduct S _ (conjugateCharacter S (n ^ (a : ℕ)) ψ) at h1
    change _ = CFSG.Section1.scalarProduct S _ (conjugateCharacter S (n ^ ((0 : Fin 3) : ℕ))
      ψ) at h2
    rw [hinv] at h1 h2
    exact_mod_cast h1.trans h2.symm
  have hformula : ∀ x : S, ρ.character x = m none + ∑ i, (m (some (some i, 0)) : ℂ) *
      ∑ a : Fin 3, conjugateCharacter S (n ^ (a : ℕ)) (lam i) x +
      m (some (none, 0)) * ∑ a : Fin 3, conjugateCharacter S (n ^ (a : ℕ)) ψ x := by
    intro x
    have h := hexp x
    rw [show (∑ k, (summand k).character x) = ρ.character x from congrFun hres x] at h
    rw [h, Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_option]
    simp only [Θ, orbitEnum, Pi.one_apply, mul_one]
    simp_rw [hmL, hmD, ← Finset.mul_sum]
    ring
  have hdegC : ρ.character 1 = (m none : ℂ) + 3 * ∑ i, (m (some (some i, 0)) : ℂ) +
      12 * m (some (none, 0)) := by
    have h := hformula 1
    rw [show ((1 : S) : G) = 1 from rfl] at h
    rw [h]
    have hL : ∀ (i : Fin 5) (a : Fin 3), conjugateCharacter S (n ^ (a : ℕ)) (lam i) 1 = 1 := by
      intro i a
      rw [conjugateCharacter_apply_one (hpow _), (hlam i).2.1]
    have hD : ∀ a : Fin 3, conjugateCharacter S (n ^ (a : ℕ)) ψ 1 = 4 := by
      intro a
      rw [conjugateCharacter_apply_one (hpow _), hψ4]
    simp only [hL, hD, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.mul_sum]
    push_cast
    ring_nf
  refine ⟨m none, fun i => m (some (some i, 0)), m (some (none, 0)), hformula, hdegC, ?_⟩
  have h := hdegC
  rw [Representation.char_one] at h
  exact_mod_cast h

end Restriction

section Node

theorem blocksVChar_conj {A : Type} [Group A] {θ : A → ℂ} (hθ : θ ∈ CFSG.BlocksVChar A)
    (c x : A) : θ (c * x * c⁻¹) = θ x := by
  induction hθ using AddSubgroup.closure_induction with
  | mem f hf => exact blocksIrr_conj hf c x
  | zero => rfl
  | add f g _ _ hf hg => simp only [Pi.add_apply, hf, hg]
  | neg f _ hf => simp only [Pi.neg_apply, hf]

theorem lyons_order_three_principal_induction_gram [Fintype G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T)))
    (hd : (((S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
      (Subgroup.normalizer ((S : Subgroup G) : Set G))).index = 3)
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1) :
    ∃ n ∈ Subgroup.normalizer ((S : Subgroup G) : Set G),
    ∃ (lam : Fin 5 → ↥(S : Subgroup G) → ℂ) (ψ : ↥(S : Subgroup G) → ℂ),
      (∀ i, lam i ∈ CFSG.BlocksIrr (S : Subgroup G) ∧ lam i 1 = 1 ∧ lam i ≠ 1) ∧
      ψ ∈ CFSG.BlocksIrr (S : Subgroup G) ∧ ψ 1 = 4 ∧
      (∀ (i : Fin 5) (a : Fin 3),
        conjugateCharacter (S : Subgroup G) (n ^ (a : ℕ)) (lam i) ∈
          CFSG.BlocksIrr (S : Subgroup G) ∧
        conjugateCharacter (S : Subgroup G) (n ^ (a : ℕ)) (lam i) ≠ 1) ∧
      (∀ a : Fin 3, conjugateCharacter (S : Subgroup G) (n ^ (a : ℕ)) ψ ∈
          CFSG.BlocksIrr (S : Subgroup G) ∧
        conjugateCharacter (S : Subgroup G) (n ^ (a : ℕ)) ψ ≠ 1) ∧
      (∀ (i i' : Fin 5) (a b : Fin 3),
        conjugateCharacter (S : Subgroup G) (n ^ (a : ℕ)) (lam i) =
          conjugateCharacter (S : Subgroup G) (n ^ (b : ℕ)) (lam i') → i = i' ∧ a = b) ∧
      (∀ a b : Fin 3, conjugateCharacter (S : Subgroup G) (n ^ (a : ℕ)) ψ =
        conjugateCharacter (S : Subgroup G) (n ^ (b : ℕ)) ψ → a = b) ∧
      (∀ (i : Fin 5) (a b : Fin 3), conjugateCharacter (S : Subgroup G) (n ^ (a : ℕ)) (lam i) ≠
        conjugateCharacter (S : Subgroup G) (n ^ (b : ℕ)) ψ) ∧
      (∀ χ ∈ CFSG.BlocksIrr (S : Subgroup G), χ ≠ 1 →
        (∃ (i : Fin 5) (a : Fin 3), χ = conjugateCharacter (S : Subgroup G) (n ^ (a : ℕ)) (lam i)) ∨
          ∃ a : Fin 3, χ = conjugateCharacter (S : Subgroup G) (n ^ (a : ℕ)) ψ) ∧
      (∀ θ ∈ CFSG.BlocksVChar (S : Subgroup G), ∀ η ∈ CFSG.BlocksVChar (S : Subgroup G),
        θ 1 = 0 →
        CFSG.Section1.scalarProduct G
            (blockInduction basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
              principal) (S : Subgroup G) θ)
            (blockInduction basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
              principal) (S : Subgroup G) η) =
          ∑ a : Fin 3, CFSG.Section1.scalarProduct (S : Subgroup G) θ
            (conjugateCharacter (S : Subgroup G) (n ^ (a : ℕ)) η)) ∧
      CFSG.Section1.scalarProduct G
          (blockInduction basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
            principal) (S : Subgroup G) (lam 0 - 1))
          (blockInduction basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
            principal) (S : Subgroup G) (lam 0 - 1)) = 4 ∧
      (∀ i : Fin 5, i ≠ 0 → CFSG.Section1.scalarProduct G
          (blockInduction basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
            principal) (S : Subgroup G) (lam i - lam 0))
          (blockInduction basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
            principal) (S : Subgroup G) (lam i - lam 0)) = 2) ∧
      CFSG.Section1.scalarProduct G
          (blockInduction basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
            principal) (S : Subgroup G) (ψ - (4 : ℂ) • lam 0))
          (blockInduction basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
            principal) (S : Subgroup G) (ψ - (4 : ℂ) • lam 0)) = 17 ∧
      (∀ θ ∈ CFSG.BlocksVChar (S : Subgroup G),
        blockInduction basis (coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
          (S : Subgroup G) θ ∈ CFSG.BlocksVChar G) ∧
      (∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
        (ρ : Representation ℂ G V), ∃ (a₀ : ℕ) (b : Fin 5 → ℕ) (c : ℕ),
          (∀ x : (S : Subgroup G), ρ.character x = a₀ + ∑ i, (b i : ℂ) *
              ∑ a : Fin 3, conjugateCharacter (S : Subgroup G) (n ^ (a : ℕ)) (lam i) x +
            c * ∑ a : Fin 3, conjugateCharacter (S : Subgroup G) (n ^ (a : ℕ)) ψ x) ∧
          ρ.character 1 = a₀ + 3 * ∑ i, (b i : ℂ) + 12 * c ∧
          Module.finrank ℂ V = a₀ + 3 * ∑ i, b i + 12 * c) ∧
      (∀ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        ∀ g a : G, CFSG.BlocksIsPPart 2 g a → a ≠ 1 →
          (basis.representation label).character g =
            (basis.representation label).character a) ∧
      (∀ z : (S : Subgroup G), z ∈ Subgroup.center (S : Subgroup G) → z ≠ 1 →
        ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
          Complex.normSq ((basis.representation label).character z) = 64) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hcomm, hsq, -, -, -, -, hfusion, -, -, -, -⟩ :=
    lyons_unitary_four_fusion_and_centralizers hnonab hT S U hSU
  obtain ⟨hcard, -, -, hsqmem₀, -⟩ := unitary_four_sylow_structure hT S U hSU
  set Sg := (S : Subgroup G) with hSg
  have hsqmem : ∀ x ∈ Sg, x ^ 2 ∈ (Subgroup.center Sg).map Sg.subtype :=
    fun x hx => ⟨⟨x, hx⟩ ^ 2, hsqmem₀ ⟨x, hx⟩, rfl⟩
  have hshape := unitaryFourSylowShape_of_mulEquiv hT S U hSU
  obtain ⟨n, hn, hgen, h3, hfix⟩ := order_three_normalizer_generator hnonab hT S U hSU hd
  have hfix1 : ∀ z ∈ (Subgroup.center Sg).map Sg.subtype, z ≠ 1 → n * z * n⁻¹ ≠ z := by
    intro z hz hz1
    have := hfix 1 (by norm_num) (by norm_num) z hz hz1
    rwa [pow_one] at this
  obtain ⟨lam, ψ, hlam, hψ, hψ4, hinjL, hinjD, hcover⟩ :=
    order_three_orbit_partition hshape hn h3 hfix1
  obtain ⟨hsylow, hcomplement⟩ := lyons_order_three_local_kernel_hypotheses hnonab hT S U hSU hd
  obtain ⟨hconst, hker⟩ := normal_complement_principal_sylow_kernel basis ideal 2 principal
    hprincipal S hsylow hcomplement
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hB
  have hclass := fun (x : Sg) (hx1 : x ≠ 1) (f : Sg → ℂ) (hf : ∀ c y : Sg, f (c * y * c⁻¹) = f y) =>
    three_class_sum hn hgen hfusion hsq hsqmem hcomm hfix x hx1 f hf
  have hgram : ∀ θ ∈ CFSG.BlocksVChar Sg, ∀ η ∈ CFSG.BlocksVChar Sg, θ 1 = 0 →
      CFSG.Section1.scalarProduct G (blockInduction basis B Sg θ) (blockInduction basis B Sg η) =
        ∑ a : Fin 3, CFSG.Section1.scalarProduct Sg θ (conjugateCharacter Sg (n ^ (a : ℕ)) η) :=
    fun θ _ η hη hθ1 => blockInduction_gram basis B hn hker hclass θ η hθ1
      (blocksVChar_conj hη)
  have hpow : ∀ a : ℕ, n ^ a ∈ Subgroup.normalizer (Sg : Set G) := fun a => Subgroup.pow_mem _ hn a
  have hψ1 : ψ ≠ 1 := by
    intro h
    rw [h] at hψ4
    norm_num at hψ4
  have hirr_vchar : ∀ θ ∈ CFSG.BlocksIrr Sg, θ ∈ CFSG.BlocksVChar Sg :=
    fun θ hθ => AddSubgroup.subset_closure hθ
  obtain ⟨hn1, hn2, hn3⟩ := orbit_norm_values hn hlam hψ hψ4 hinjL hinjD
  refine ⟨n, hn, lam, ψ, hlam, hψ, hψ4, fun i a => ⟨conjugateCharacter_mem_blocksIrr (hpow _)
    (hlam i).1, conjugateCharacter_ne_one (hpow _) (hlam i).2.2⟩,
    fun a => ⟨conjugateCharacter_mem_blocksIrr (hpow _) hψ, conjugateCharacter_ne_one (hpow _) hψ1⟩,
    hinjL, hinjD, ?_, hcover, hgram, ?_, ?_, ?_,
    fun θ hθ => blockInduction_mem_blocksVChar basis B Sg hθ,
    fun V _ _ _ ρ => restriction_orbit_pattern hn lam ψ hlam hψ hψ4 hinjL hinjD hcover V ρ,
    hconst, ?_⟩
  · intro i a b h
    have := congrFun h 1
    rw [conjugateCharacter_apply_one (hpow _), conjugateCharacter_apply_one (hpow _),
      (hlam i).2.1, hψ4] at this
    norm_num at this
  · rw [hgram _ (sub_mem (hirr_vchar _ (hlam 0).1) (hirr_vchar _ (one_mem_blocksIrr Sg)))
      _ (sub_mem (hirr_vchar _ (hlam 0).1) (hirr_vchar _ (one_mem_blocksIrr Sg)))
      (by simp [(hlam 0).2.1])]
    exact hn1
  · intro i hi
    rw [hgram _ (sub_mem (hirr_vchar _ (hlam i).1) (hirr_vchar _ (hlam 0).1))
      _ (sub_mem (hirr_vchar _ (hlam i).1) (hirr_vchar _ (hlam 0).1))
      (by simp [(hlam i).2.1, (hlam 0).2.1])]
    exact hn2 i hi
  · have h4 : (4 : ℂ) • lam 0 = (4 : ℕ) • lam 0 := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]
      norm_num
    have hmem : ψ - (4 : ℂ) • lam 0 ∈ CFSG.BlocksVChar Sg := by
      rw [h4]
      exact sub_mem (hirr_vchar _ hψ) (AddSubgroup.nsmul_mem _ (hirr_vchar _ (hlam 0).1) 4)
    rw [hgram _ hmem _ hmem (by simp [(hlam 0).2.1, hψ4])]
    exact hn3
  · intro z hz hz1
    have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
    have h := hker (z : G) z.property hz1' (z : G) z.property
    rw [ite_eq_left (IsConj.refl _)] at h
    have hSC : Sg ≤ Subgroup.centralizer {(z : G)} := by
      intro s hs
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_center_iff.mp hz ⟨s, hs⟩
      exact congrArg Subtype.val this
    rw [inf_eq_left.mpr hSC, hcard] at h
    have h' : ((∑ label ∈ B, Complex.normSq ((basis.representation label).character z) : ℝ) :
        ℂ) = 64 := by
      rw [Complex.ofReal_sum]
      have h64 : (64 : ℂ) = ((64 : ℕ) : ℂ) := by norm_num
      rw [h64, ← h]
      apply Finset.sum_congr rfl
      intro label _
      rw [← Complex.mul_conj]
    exact_mod_cast h'

end Node

end CFSG.LyonsUnitaryFour
