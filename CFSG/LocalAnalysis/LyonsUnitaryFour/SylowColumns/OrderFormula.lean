module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.ExtendedCentralizer
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.PrincipalSectionKernel
public import CFSG.CharacterTheory.TwoRankLowerBound.PrincipalProjectionTransport

public section

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers CFSG.RankTwoShapes
open scoped BigOperators Classical

variable {G : Type*} [Group G]

section Weights

variable [Fintype G]

@[expose] noncomputable def classInter (H : Subgroup G) (a : G) : Finset H :=
  Finset.univ.filter (fun x : H => IsConj (x : G) a)

@[expose] noncomputable def classWeight (H : Subgroup G) (ψ : H → ℂ) (a : G) : ℂ :=
  (Nat.card H : ℂ)⁻¹ * ∑ x : H, if IsConj (x : G) a then ψ x else 0

theorem sum_classInter (H : Subgroup G) (ψ : H → ℂ) (a : G) :
    ∑ x ∈ classInter H a, ψ x = (Nat.card H : ℂ) * classWeight H ψ a := by
  have hne : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [classWeight, ← mul_assoc, mul_inv_cancel₀ hne, one_mul, classInter, Finset.sum_filter]

theorem classInter_invariant (H : Subgroup G) (a : G) : ConjInvariant (classInter H a) := by
  intro c x
  simp only [classInter, Finset.mem_filter, Finset.mem_univ, true_and]
  have hconj : IsConj ((c * x * c⁻¹ : H) : G) (x : G) := by
    rw [isConj_comm]
    exact isConj_iff.mpr ⟨c, by simp⟩
  constructor
  · intro h
    exact hconj.trans h
  · intro h
    exact hconj.symm.trans h

theorem classInter_mul_self (H : Subgroup G) {a : G} (ha : a * a = 1) :
    ∀ x ∈ classInter H a, x * x = 1 := by
  intro x hx
  simp only [classInter, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  obtain ⟨c, hc⟩ := isConj_iff.mp hx
  apply Subtype.ext
  have hxG : (x : G) = c⁻¹ * a * c := by rw [← hc]; group
  simp only [Subgroup.coe_mul, Subgroup.coe_one]
  rw [hxG]
  calc c⁻¹ * a * c * (c⁻¹ * a * c) = c⁻¹ * (a * a) * c := by group
    _ = 1 := by rw [ha]; group

theorem productCount_classInter (H : Subgroup G) (localBasis : FiniteIrreducibleCharacterBasis H)
    {a b : G} (ha : a * a = 1) (hb : b * b = 1) (y : H) :
    (productCount (classInter H a) (classInter H b) y : ℂ) = (Nat.card H : ℂ) * ∑ label,
      classWeight H (localBasis.representation label).character a *
        classWeight H (localBasis.representation label).character b *
          (localBasis.representation label).character y /
            (localBasis.representation label).character 1 := by
  have hne : (Nat.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  obtain ⟨-, h⟩ := conjugacy_invariant_product_character_formula_involutions localBasis
    (classInter H a) (classInter H b) (classInter_invariant H a) (classInter_invariant H b)
    (classInter_mul_self H ha) (classInter_mul_self H hb) y
  rw [h, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro label _
  rw [sum_classInter, sum_classInter]
  field_simp

theorem productCount_conjClassFinset_eq (H : Subgroup G) {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) (y : H) (hy : extendedCentralizer (y : G) ≤ H) :
    productCount (conjClassFinset a) (conjClassFinset b) (y : G) =
      productCount (classInter H a) (classInter H b) y := by
  have hinvol : ∀ c : G, c * c = 1 → ∀ g ∈ conjClassFinset c, g * g = 1 := by
    intro c hc g hg
    simp only [conjClassFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    obtain ⟨d, rfl⟩ := isConj_iff.mp hg
    calc d * c * d⁻¹ * (d * c * d⁻¹) = d * (c * c) * d⁻¹ := by group
      _ = 1 := by rw [hc]; group
  obtain ⟨-, -, -, -, hloc, -⟩ := involution_product_extended_centralizer_localization (y : G)
    (conjClassFinset a) (conjClassFinset b) (hinvol a ha) (hinvol b hb)
  rw [hloc H hy]
  unfold productCount
  symm
  apply Finset.card_bij (fun p _ => ((p.1 : G), (p.2 : G)))
  · rintro ⟨x₁, x₂⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, classInter, Finset.mem_univ, true_and]
      at hp ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    refine ⟨⟨⟨?_, x₁.property⟩, ⟨?_, x₂.property⟩⟩, ?_⟩
    · simp only [conjClassFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact h1.symm
    · simp only [conjClassFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact h2.symm
    · rw [← h3]
      rfl
  · rintro ⟨x₁, x₂⟩ _ ⟨y₁, y₂⟩ _ h
    simp only [Prod.mk.injEq] at h
    rw [Subtype.ext h.1, Subtype.ext h.2]
  · rintro ⟨g₁, g₂⟩ hg
    simp only [Finset.mem_filter, Finset.mem_product] at hg
    obtain ⟨⟨⟨hg₁, hg₁H⟩, ⟨hg₂, hg₂H⟩⟩, hprod⟩ := hg
    refine ⟨(⟨g₁, hg₁H⟩, ⟨g₂, hg₂H⟩), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product, classInter, Finset.mem_univ, true_and]
    simp only [conjClassFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hg₁ hg₂
    refine ⟨⟨hg₁.symm, hg₂.symm⟩, Subtype.ext ?_⟩
    simpa using hprod

theorem projection_basis_expansion {A : Type*} [Group A] [Fintype A]
    (basis : FiniteIrreducibleCharacterBasis A) (support : Finset basis.index)
    (c : basis.index → ℂ) (x : A) :
    characterSubsetProjection basis support
        (fun g => ∑ l, c l * (basis.representation l).character g) x =
      ∑ l ∈ support, c l * (basis.representation l).character x := by
  rw [characterSubsetProjection_apply']
  apply Finset.sum_congr rfl
  intro m _
  rw [characterPairing_expansion_left]
  simp_rw [characterPairing_irreducible _ _ (basis.irreducible _) (basis.irreducible m),
    basis.distinct.eq_iff]
  simp

end Weights

section Formula

variable [Fintype G]

theorem principal_projection_section_eq (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (H : Subgroup G) (u : H)
    (e : ℕ) (hu : orderOf (u : G) ∣ p ^ e)
    (hCH : Subgroup.centralizer ({(u : G)} : Set G) ≤ H)
    (localBasis : FiniteIrreducibleCharacterBasis H) (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1)
    (F : G → ℂ) (hF : ∀ x c : G, F (c * x * c⁻¹) = F x) (F' : H → ℂ)
    (hF' : ∀ y c : H, F' (c * y * c⁻¹) = F' y)
    (hagree : ∀ w : H, Commute u w → Nat.Coprime p (orderOf w) →
      F ((u * w : H) : G) = F' (u * w))
    (r : H) (hr : (r : G) ∈ Subgroup.centralizer ({(u : G)} : Set G))
    (hrp : Nat.Coprime p (orderOf r)) :
    characterSubsetProjection basis
        (coefficientBlock basis (localizedComplexIntegerRing ideal) principal) F
        ((u * r : H) : G) =
      characterSubsetProjection localBasis
        (coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal) F'
        (u * r) := by
  classical
  set v : G := (u : G)⁻¹ with hv
  set vH : H := u⁻¹ with hvH
  have hvord : orderOf v ∣ p ^ e := by rw [hv, orderOf_inv]; exact hu
  have hvHord : orderOf vH ∣ p ^ e := by
    rw [hvH, orderOf_inv, ← Subgroup.orderOf_coe]
    exact hu
  set C := Subgroup.centralizer (Subgroup.zpowers v : Set G) with hC
  set C' := Subgroup.centralizer (Subgroup.zpowers vH : Set H) with hC'
  have hCH' : ∀ g ∈ C, g ∈ H := by
    intro g hg
    apply hCH
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : Commute v g := commute_of_mem_centralizer_zpowers v ⟨g, hg⟩
    have h2 : Commute (u : G) g := by
      have := hcomm.inv_left
      rwa [hv, inv_inv] at this
    exact h2.eq.symm
  let ι : C' ≃* C :=
    { toFun := fun c => ⟨((c : H) : G), mem_centralizer_zpowers_of_commute
        ((commute_of_mem_centralizer_zpowers vH c).map H.subtype)⟩
      invFun := fun c => ⟨⟨c, hCH' c c.property⟩, mem_centralizer_zpowers_of_commute
        (Subtype.ext (commute_of_mem_centralizer_zpowers v c).eq)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  obtain ⟨basisC⟩ := finiteIrreducibleCharacterBasis_exists (G := C)
  obtain ⟨pC, hpC⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basisC
    (principalFiniteComplexRepresentation _) (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hpC
  obtain ⟨basisC'⟩ := finiteIrreducibleCharacterBasis_exists (G := C')
  obtain ⟨pC', hpC'⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basisC'
    (principalFiniteComplexRepresentation _) (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hpC'
  have hrcomm : Commute (u : G) (r : G) := (Subgroup.mem_centralizer_singleton_iff.mp hr).symm
  have hrcommH : Commute u r := Subtype.ext hrcomm.eq
  have hrC : (r : G)⁻¹ ∈ C := mem_centralizer_zpowers_of_commute hrcomm.inv_inv
  have hrC' : r⁻¹ ∈ C' := mem_centralizer_zpowers_of_commute hrcommH.inv_inv
  set rC : C := ⟨(r : G)⁻¹, hrC⟩ with hrCdef
  set rC' : C' := ⟨r⁻¹, hrC'⟩ with hrC'def
  have hreg : Nat.Coprime p (orderOf rC.val) := by
    change Nat.Coprime p (orderOf ((r : G)⁻¹))
    rw [orderOf_inv, Subgroup.orderOf_coe]
    exact hrp
  have hreg' : Nat.Coprime p (orderOf rC'.val) := by
    change Nat.Coprime p (orderOf r⁻¹)
    rw [orderOf_inv]
    exact hrp
  have hG := principal_local_section_projection basis ideal p principal hprincipal v e hvord
    basisC pC hpC rC hreg F hF
  have hH := principal_local_section_projection localBasis ideal p localPrincipal
    hlocalPrincipal vH e hvHord basisC' pC' hpC' rC' hreg' F' hF'
  set q : C := ((⟨v, element_mem_centralizer_zpowers v⟩ : C) * rC)⁻¹ with hq
  set q' : C' := ((⟨vH, element_mem_centralizer_zpowers vH⟩ : C') * rC')⁻¹ with hq'
  have hqG : (q : G) = ((u * r : H) : G) := by
    change (v * (r : G)⁻¹)⁻¹ = (u : G) * r
    rw [mul_inv_rev, inv_inv, hv, inv_inv]
    exact hrcomm.eq.symm
  have hq'H : (q' : H) = u * r := by
    change (vH * r⁻¹)⁻¹ = u * r
    rw [mul_inv_rev, inv_inv, hvH, inv_inv]
    exact hrcommH.eq.symm
  have hιq : ι.symm q = q' := by
    apply Subtype.ext
    apply Subtype.ext
    change (q : G) = ((q' : H) : G)
    rw [hqG, hq'H]
  set Q := inverseSection p v with hQ
  set fG : C → ℂ := fun m => F m.val with hfG
  set fH : C → ℂ := fun m => F' (ι.symm m : C').val with hfH
  have hagreeC : ∀ m ∈ Q, fG m = fH m := by
    intro m hm
    set w : C := centralizerSelf v * m with hw
    have hwp : Nat.Coprime p (orderOf (w : G)) := by
      rw [Subgroup.orderOf_coe]
      exact hm
    have hmw : (m : G) = (u : G) * (w : G) := by
      change (m : G) = (u : G) * (v * (m : G))
      rw [← mul_assoc, show (u : G) * v = 1 from mul_inv_cancel (u : G), one_mul]
    set wH : H := ⟨(w : G), hCH' w w.property⟩ with hwH
    have hwcomm : Commute u wH := by
      apply Subtype.ext
      have hc : Commute v (w : G) := commute_of_mem_centralizer_zpowers v w
      have h2 : Commute (u : G) (w : G) := by
        have := hc.inv_left
        rwa [hv, inv_inv] at this
      exact h2.eq
    have hwHp : Nat.Coprime p (orderOf wH) := by
      rw [← Subgroup.orderOf_coe]
      exact hwp
    have h := hagree wH hwcomm hwHp
    have he1 : (m : G) = ((u * wH : H) : G) := hmw
    have he2 : ((ι.symm m : C') : H) = u * wH := Subtype.ext hmw
    change F (m : G) = F' ((ι.symm m : C') : H)
    rw [he1, he2]
    exact h
  have hmaskeq : characterFunctionMask Q fG = characterFunctionMask Q fH := by
    funext m
    unfold characterFunctionMask
    by_cases hm : m ∈ Q
    · rw [ite_eq_left hm, ite_eq_left hm, hagreeC m hm]
    · rw [ite_eq_right hm, ite_eq_right hm]
  have hsec := inverseSection_primeSectionUnion p v e hvord
  have hm1 := congrFun (coefficientBlock_section_mask_commute basisC ideal p pC Q hsec fG) q
  have hm2 := congrFun (coefficientBlock_section_mask_commute basisC ideal p pC Q hsec fH) q
  have hqQ : q ∈ Q := inv_mem_inverseSection p v rC (by rw [← Subgroup.orderOf_coe]; exact hreg)
  rw [hmaskeq] at hm1
  have hmm := hm1.symm.trans hm2
  unfold characterFunctionMask at hmm
  rw [ite_eq_left hqQ, ite_eq_left hqQ] at hmm
  have htrans := principal_projection_transport basisC' basisC (localizedComplexIntegerRing ideal)
    ι pC' hpC' pC hpC (fun m' : C' => F' m'.val) (fun x c => by
      change F' ((c * x * c⁻¹ : C') : H) = F' (x : H)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hF' x c) q
  calc characterSubsetProjection basis
        (coefficientBlock basis (localizedComplexIntegerRing ideal) principal) F
        ((u * r : H) : G) =
      characterSubsetProjection basis
        (coefficientBlock basis (localizedComplexIntegerRing ideal) principal) F (q : G) := by
        rw [hqG]
    _ = characterSubsetProjection basisC
        (coefficientBlock basisC (localizedComplexIntegerRing ideal) pC) fG q := hG.symm
    _ = characterSubsetProjection basisC
        (coefficientBlock basisC (localizedComplexIntegerRing ideal) pC) fH q := hmm
    _ = characterSubsetProjection basisC'
        (coefficientBlock basisC' (localizedComplexIntegerRing ideal) pC')
        (fun m' : C' => F' m'.val) (ι.symm q) := htrans
    _ = characterSubsetProjection basisC'
        (coefficientBlock basisC' (localizedComplexIntegerRing ideal) pC')
        (fun m' : C' => F' m'.val) q' := by rw [hιq]
    _ = characterSubsetProjection localBasis
        (coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal) F'
        (q' : H) := hH
    _ = characterSubsetProjection localBasis
        (coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal) F'
        (u * r) := by rw [hq'H]

theorem brauer_principal_order_formula (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) (H : Subgroup G) (u : H) (e : ℕ) (hu : orderOf (u : G) ∣ p ^ e)
    (hEH : extendedCentralizer (u : G) ≤ H) (localBasis : FiniteIrreducibleCharacterBasis H)
    (localPrincipal : localBasis.index)
    (hlocalPrincipal : (localBasis.representation localPrincipal).character = 1) :
    (∀ r : H, (r : G) ∈ Subgroup.centralizer ({(u : G)} : Set G) → Nat.Coprime p (orderOf r) →
      (Nat.card G : ℂ) *
          ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
            (basis.representation label).character a * (basis.representation label).character b *
              (basis.representation label).character ((u * r : H) : G) /
                (basis.representation label).character 1 =
        (Nat.card H : ℂ) * Nat.card (Subgroup.centralizer ({a} : Set G)) *
            Nat.card (Subgroup.centralizer ({b} : Set G)) *
          ∑ label ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal,
            classWeight H (localBasis.representation label).character a *
              classWeight H (localBasis.representation label).character b *
                (localBasis.representation label).character (u * r) /
                  (localBasis.representation label).character 1) ∧
    ∀ ℓ : ({r : H // (r : G) ∈ Subgroup.centralizer ({(u : G)} : Set G) ∧
        Nat.Coprime p (orderOf r)} → ℂ) →ₗ[ℂ] ℂ,
      (Nat.card G : ℂ) *
          ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
            (basis.representation label).character a * (basis.representation label).character b *
              ℓ (fun r => (basis.representation label).character ((u * r.val : H) : G)) /
                (basis.representation label).character 1 =
        (Nat.card H : ℂ) * Nat.card (Subgroup.centralizer ({a} : Set G)) *
            Nat.card (Subgroup.centralizer ({b} : Set G)) *
          ∑ label ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal,
            classWeight H (localBasis.representation label).character a *
              classWeight H (localBasis.representation label).character b *
                ℓ (fun r => (localBasis.representation label).character (u * r.val)) /
                  (localBasis.representation label).character 1 := by
  classical
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hB
  set BH := coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal
    with hBH
  set ca : ℂ := ((Nat.card (Subgroup.centralizer ({a} : Set G)) : ℕ) : ℂ) with hca
  set cb : ℂ := ((Nat.card (Subgroup.centralizer ({b} : Set G)) : ℕ) : ℂ) with hcb
  have hca0 : ca ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hcb0 : cb ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  set FG : G → ℂ := fun x => (productCount (conjClassFinset a) (conjClassFinset b) x : ℂ)
    with hFGdef
  set FH : H → ℂ := fun y => (productCount (classInter H a) (classInter H b) y : ℂ)
    with hFHdef
  set cG : basis.index → ℂ := fun l => (ca * cb)⁻¹ * Nat.card G *
    ((basis.representation l).character a * (basis.representation l).character b /
      (basis.representation l).character 1) with hcG
  set cH : localBasis.index → ℂ := fun l => (Nat.card H : ℂ) *
    (classWeight H (localBasis.representation l).character a *
      classWeight H (localBasis.representation l).character b /
        (localBasis.representation l).character 1) with hcH
  have hFG : FG = fun g => ∑ l, cG l * (basis.representation l).character g := by
    funext g
    have h := involution_classes_product_character_formula basis a b ha hb g
    have h' : FG g = (ca * cb)⁻¹ * ((Nat.card G : ℂ) * ∑ l, (basis.representation l).character a *
        (basis.representation l).character b * (basis.representation l).character g /
          (basis.representation l).character 1) := by
      rw [← h, ← hca, ← hcb]
      field_simp
      rfl
    rw [h', Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [hcG]
    ring
  have hFH : FH = fun y => ∑ l, cH l * (localBasis.representation l).character y := by
    funext y
    change (productCount (classInter H a) (classInter H b) y : ℂ) = _
    rw [productCount_classInter H localBasis ha hb y, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [hcH]
    ring
  have hclassG : ∀ x c : G, FG (c * x * c⁻¹) = FG x := by
    intro x c
    rw [hFG]
    exact Finset.sum_congr rfl fun l _ => by
      rw [show (basis.representation l).character (c * x * c⁻¹) =
        (basis.representation l).character x from Representation.char_conj _ x c]
  have hclassH : ∀ y c : H, FH (c * y * c⁻¹) = FH y := by
    intro y c
    rw [hFH]
    exact Finset.sum_congr rfl fun l _ => by
      rw [show (localBasis.representation l).character (c * y * c⁻¹) =
        (localBasis.representation l).character y from Representation.char_conj _ y c]
  have hPG : ∀ y : G, ca * cb * characterSubsetProjection basis B FG y =
      Nat.card G * ∑ l ∈ B, (basis.representation l).character a *
        (basis.representation l).character b * (basis.representation l).character y /
          (basis.representation l).character 1 := by
    intro y
    rw [hFG, projection_basis_expansion, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [hcG]
    field_simp
  have hPH : ∀ y : H, characterSubsetProjection localBasis BH FH y =
      Nat.card H * ∑ l ∈ BH, classWeight H (localBasis.representation l).character a *
        classWeight H (localBasis.representation l).character b *
          (localBasis.representation l).character y /
            (localBasis.representation l).character 1 := by
    intro y
    rw [hFH, projection_basis_expansion, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [hcH]
    ring
  have hkey : ∀ r : H, (r : G) ∈ Subgroup.centralizer ({(u : G)} : Set G) →
      Nat.Coprime p (orderOf r) →
      characterSubsetProjection basis B FG ((u * r : H) : G) =
        characterSubsetProjection localBasis BH FH (u * r) := by
    intro r hr hrp
    have hCH : Subgroup.centralizer ({(u : G)} : Set G) ≤ H :=
      (centralizer_le_extendedCentralizer _).trans hEH
    refine principal_projection_section_eq basis ideal p principal hprincipal H u e hu hCH
      localBasis localPrincipal hlocalPrincipal FG hclassG FH hclassH (fun w hw hwp => ?_) r hr hrp
    have hwG : Commute (u : G) (w : G) := hw.map H.subtype
    have hwpG : Nat.Coprime p (orderOf (w : G)) := by rw [Subgroup.orderOf_coe]; exact hwp
    obtain ⟨-, -, -, -, -, hext⟩ := involution_product_extended_centralizer_localization
      ((u * w : H) : G) (∅ : Finset G) (∅ : Finset G) (by simp) (by simp)
    have hle : extendedCentralizer ((u * w : H) : G) ≤ H :=
      (hext p (u : G) (w : G) e hu hwG hwpG).trans hEH
    change (productCount (conjClassFinset a) (conjClassFinset b) ((u * w : H) : G) : ℂ) =
      (productCount (classInter H a) (classInter H b) (u * w) : ℂ)
    exact_mod_cast productCount_conjClassFinset_eq H ha hb (u * w) hle
  refine ⟨fun r hr hrp => ?_, fun ℓ => ?_⟩
  · have h1 := hPG ((u * r : H) : G)
    rw [hkey r hr hrp, hPH] at h1
    rw [← h1]
    ring
  · have hfun : (∑ l ∈ B, ((Nat.card G : ℂ) * ((basis.representation l).character a *
          (basis.representation l).character b / (basis.representation l).character 1)) •
          (fun r : {r : H // (r : G) ∈ Subgroup.centralizer ({(u : G)} : Set G) ∧
            Nat.Coprime p (orderOf r)} =>
            (basis.representation l).character ((u * r.val : H) : G))) =
        ∑ l ∈ BH, ((Nat.card H : ℂ) * ca * cb *
          (classWeight H (localBasis.representation l).character a *
            classWeight H (localBasis.representation l).character b /
              (localBasis.representation l).character 1)) •
          (fun r : {r : H // (r : G) ∈ Subgroup.centralizer ({(u : G)} : Set G) ∧
            Nat.Coprime p (orderOf r)} =>
            (localBasis.representation l).character (u * r.val)) := by
      funext r
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have h1 := hPG ((u * r.val : H) : G)
      rw [hkey r.val r.property.1 r.property.2, hPH] at h1
      calc ∑ l ∈ B, (Nat.card G : ℂ) * ((basis.representation l).character a *
            (basis.representation l).character b / (basis.representation l).character 1) *
            (basis.representation l).character ((u * r.val : H) : G) =
          (Nat.card G : ℂ) * ∑ l ∈ B, (basis.representation l).character a *
            (basis.representation l).character b *
              (basis.representation l).character ((u * r.val : H) : G) /
                (basis.representation l).character 1 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro l _
            ring
        _ = ca * cb * ((Nat.card H : ℂ) * ∑ l ∈ BH,
            classWeight H (localBasis.representation l).character a *
              classWeight H (localBasis.representation l).character b *
                (localBasis.representation l).character (u * r.val) /
                  (localBasis.representation l).character 1) := h1.symm
        _ = ∑ l ∈ BH, (Nat.card H : ℂ) * ca * cb *
            (classWeight H (localBasis.representation l).character a *
              classWeight H (localBasis.representation l).character b /
                (localBasis.representation l).character 1) *
            (localBasis.representation l).character (u * r.val) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro l _
            ring
    have h := congrArg ℓ hfun
    rw [map_sum, map_sum] at h
    simp only [map_smul, smul_eq_mul] at h
    calc (Nat.card G : ℂ) * ∑ l ∈ B, (basis.representation l).character a *
          (basis.representation l).character b *
            ℓ (fun r => (basis.representation l).character ((u * r.val : H) : G)) /
              (basis.representation l).character 1 =
        ∑ l ∈ B, (Nat.card G : ℂ) * ((basis.representation l).character a *
          (basis.representation l).character b / (basis.representation l).character 1) *
            ℓ (fun r => (basis.representation l).character ((u * r.val : H) : G)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          ring
      _ = _ := h
      _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          ring

end Formula

end CFSG.LyonsUnitaryFour
