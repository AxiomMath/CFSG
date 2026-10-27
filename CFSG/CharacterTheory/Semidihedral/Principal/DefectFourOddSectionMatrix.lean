module

public import CFSG.CharacterTheory.Semidihedral.Principal.DefectDegreeDivisibility
public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterConjugateInverse
public import CFSG.CharacterTheory.TwoRankLowerBound.BlockSectionMask
public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterProjectionPairing

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

@[expose] noncomputable def oddSectionMatrix {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (χ ψ : basis.index) : ℂ :=
  (4 / Nat.card G) * ∑ x ∈ Finset.univ.filter (fun x : G => Odd (orderOf x)),
    (basis.representation χ).character x * starRingEnd ℂ ((basis.representation ψ).character x)

namespace DefectFourOdd

theorem odd_primeSectionUnion {G : Type*} [Group G] :
    primeSectionUnion 2 {x : G | Odd (orderOf x)} := by
  have hkey : ∀ (u v : G) (e : ℕ), orderOf u ∣ 2 ^ e → Nat.Coprime 2 (orderOf v) →
      Commute u v → (u * v ∈ {x : G | Odd (orderOf x)} ↔ u = 1) := by
    intro u v e hu hv huv
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hu
    have hcop : Nat.Coprime (orderOf u) (orderOf v) := by
      rw [hj]
      exact Nat.Coprime.pow_left j hv
    simp only [Set.mem_ofPred_eq]
    rw [huv.orderOf_mul_eq_mul_orderOf_of_coprime hcop, Nat.odd_mul]
    constructor
    · rintro ⟨hodd, -⟩
      rw [hj] at hodd
      have hj0 : j = 0 := by
        by_contra hne
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hne
        rw [pow_succ] at hodd
        exact (Nat.not_even_iff_odd.mpr hodd) (even_two.mul_left _)
      rw [hj0, pow_zero] at hj
      exact orderOf_eq_one_iff.mp hj
    · rintro rfl
      exact ⟨by rw [orderOf_one]; exact odd_one, Nat.coprime_two_left.mp hv⟩
  intro u₁ u₂ v₁ v₂ e₁ e₂ hu₁ hu₂ hv₁ hv₂ hc₁ hc₂ hconj
  rw [hkey u₁ v₁ e₁ hu₁ hv₁ hc₁, hkey u₂ v₂ e₂ hu₂ hv₂ hc₂]
  constructor
  · rintro rfl
    exact isConj_one_right.mp hconj
  · rintro rfl
    exact isConj_one_left.mp hconj

variable {G : Type*} [Group G] [Fintype G]

theorem oddSectionMatrix_eq_pairing (basis : FiniteIrreducibleCharacterBasis G)
    (χ ψ : basis.index) :
    oddSectionMatrix basis χ ψ = 4 * characterPairing
      (characterFunctionMask {x : G | Odd (orderOf x)} (basis.representation χ).character)
      (basis.representation ψ).character := by
  unfold oddSectionMatrix characterPairing characterFunctionMask
  rw [Finset.sum_filter, div_eq_mul_inv, mul_assoc]
  congr 2
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Set.mem_ofPred_eq]
  split_ifs
  · rw [finite_character_conjugate_inverse]
  · rw [zero_mul]

theorem pairing_mask_odd_self_adjoint (f g : G → ℂ) :
    characterPairing (characterFunctionMask {x : G | Odd (orderOf x)} f) g =
      characterPairing f (characterFunctionMask {x : G | Odd (orderOf x)} g) := by
  unfold characterPairing characterFunctionMask
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Set.mem_ofPred_eq, orderOf_inv]
  split_ifs <;> simp

theorem oddSectionMatrix_sq (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (label : basis.index) (χ ψ : basis.index)
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label) :
    ∑ ρ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
        oddSectionMatrix basis χ ρ * oddSectionMatrix basis ρ ψ =
      4 * oddSectionMatrix basis χ ψ := by
  have hmem : characterFunctionMask {x : G | Odd (orderOf x)} (basis.representation χ).character ∈
      coefficientCharacterSpace basis
        (coefficientBlock basis (localizedComplexIntegerRing ideal) label) :=
    coefficientBlock_section_mask_mem basis ideal 2 label _ odd_primeSectionUnion _
      (Submodule.subset_span ⟨χ, hχ, rfl⟩)
  have hidem : characterFunctionMask {x : G | Odd (orderOf x)}
      (characterFunctionMask {x : G | Odd (orderOf x)} (basis.representation χ).character) =
        characterFunctionMask {x : G | Odd (orderOf x)} (basis.representation χ).character := by
    funext x
    simp only [characterFunctionMask]
    split_ifs <;> rfl
  have hproj := characterSubsetProjection_pairing_left basis
    (coefficientBlock basis (localizedComplexIntegerRing ideal) label)
    (characterFunctionMask {x : G | Odd (orderOf x)} (basis.representation χ).character)
    (characterFunctionMask {x : G | Odd (orderOf x)} (basis.representation ψ).character)
  rw [characterSubsetProjection_identity basis _ _ hmem, ← pairing_mask_odd_self_adjoint,
    hidem] at hproj
  simp only [oddSectionMatrix_eq_pairing]
  rw [hproj, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [pairing_mask_odd_self_adjoint (basis.representation ρ).character]
  ring

theorem oddSectionMatrix_swap (basis : FiniteIrreducibleCharacterBasis G) (χ ψ : basis.index) :
    oddSectionMatrix basis ψ χ = starRingEnd ℂ (oddSectionMatrix basis χ ψ) := by
  unfold oddSectionMatrix
  rw [map_mul, map_sum, map_div₀, map_ofNat, map_natCast]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, Complex.conj_conj, mul_comm]

theorem sum_filter_eq_sum_conjClasses (p : G → Prop) [DecidablePred p]
    (hp : ∀ x y : G, IsConj x y → (p x ↔ p y)) (f : G → ℂ)
    (hf : ∀ x y : G, IsConj x y → f x = f y) :
    ∑ x ∈ Finset.univ.filter p, f x =
      ∑ K ∈ (Finset.univ.filter p).image ConjClasses.mk,
        ((Subgroup.centralizer ({Classical.choose (ConjClasses.exists_rep K)} : Set G)).index :
          ℂ) * f (Classical.choose (ConjClasses.exists_rep K)) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := ConjClasses.mk)
    (t := (Finset.univ.filter p).image ConjClasses.mk) (fun x hx => Finset.mem_image_of_mem _ hx)]
  refine Finset.sum_congr rfl fun K hK => ?_
  obtain ⟨x₀, hx₀, hK0⟩ := Finset.mem_image.mp hK
  have hg : ConjClasses.mk (Classical.choose (ConjClasses.exists_rep K)) = K :=
    Classical.choose_spec (ConjClasses.exists_rep K)
  have hfiber : (Finset.univ.filter p).filter (fun x => ConjClasses.mk x = K) =
      (ConjClasses.mk (Classical.choose (ConjClasses.exists_rep K))).carrier.toFinset := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset,
      ConjClasses.mem_carrier_iff_mk_eq, hg]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨(hp x₀ x ?_).mp (Finset.mem_filter.mp hx₀).2, h⟩
      exact ConjClasses.mk_eq_mk_iff_isConj.mp (hK0.trans h.symm)
  rw [hfiber, Finset.sum_congr rfl fun x hx => hf x _ (ConjClasses.mk_eq_mk_iff_isConj.mp
    ((ConjClasses.mem_carrier_iff_mk_eq).mp (Set.mem_toFinset.mp hx))), Finset.sum_const,
    nsmul_eq_mul, Set.toFinset_card, ← Nat.card_eq_fintype_card,
    CFSG.LyonsUnitaryFour.card_conjClass_eq_index]

theorem sum_odd_eq_degree_mul_classSum (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsPrime] (χ ψ : basis.index) :
    ∑ x ∈ Finset.univ.filter (fun x : G => Odd (orderOf x)),
        (basis.representation χ).character x *
          starRingEnd ℂ ((basis.representation ψ).character x) =
      (basis.representation χ).character 1 *
        ∑ K ∈ (Finset.univ.filter (fun x : G => Odd (orderOf x))).image ConjClasses.mk,
          (localCentralCharacterHom basis ideal χ
            (centralConjugacyClassSum (localizedComplexIntegerRing ideal) K) : ℂ) *
          (basis.representation ψ).character (Classical.choose (ConjClasses.exists_rep K))⁻¹ := by
  rw [sum_filter_eq_sum_conjClasses (fun x : G => Odd (orderOf x))
    (fun x y h => by
      obtain ⟨c, rfl⟩ := isConj_iff.mp h
      have hc := (MulAut.conj c).orderOf_eq x
      rw [MulAut.conj_apply] at hc
      rw [hc])
    (fun x => (basis.representation χ).character x *
      starRingEnd ℂ ((basis.representation ψ).character x))
    (fun x y h => by
      obtain ⟨c, rfl⟩ := isConj_iff.mp h
      simp only [Representation.char_conj])]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun K _ => ?_
  have hg : ConjClasses.mk (Classical.choose (ConjClasses.exists_rep K)) = K :=
    Classical.choose_spec (ConjClasses.exists_rep K)
  have hscalar : (localCentralCharacterHom basis ideal χ
      (centralConjugacyClassSum (localizedComplexIntegerRing ideal) K) : ℂ) =
      ((Subgroup.centralizer ({Classical.choose (ConjClasses.exists_rep K)} : Set G)).index :
        ℂ) * (basis.representation χ).character (Classical.choose (ConjClasses.exists_rep K)) /
          (basis.representation χ).character 1 := by
    rw [localCentralCharacterHom_coe]
    conv_lhs => rw [← hg]
    exact CFSG.Wreathed.centralCharacterScalar_conjugacyClassSum_mk basis _ χ
  have h1 := irreducible_character_degree_ne_zero (basis.representation χ) (basis.irreducible χ)
  rw [hscalar, finite_character_conjugate_inverse]
  field_simp

end DefectFourOdd

open DefectFourOdd

variable {G : Type*} [Group G] [Fintype G]

theorem defect_order_four_odd_section_matrix_bounds_block
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (label : basis.index)
    (D : Subgroup G) (hD : coefficientBlockDefect basis ideal 2 label D) (hD4 : Nat.card D = 4) :
    (∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
      ∀ ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
        ∑ ρ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
            oddSectionMatrix basis χ ρ * oddSectionMatrix basis ρ ψ =
          4 * oddSectionMatrix basis χ ψ) ∧
    ((∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
      ∀ ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
        ∃ z : ℤ, oddSectionMatrix basis χ ψ = z) →
      (∃ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
        ∃ ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
          ∃ z : ℤ, Odd z ∧ oddSectionMatrix basis χ ψ = z) →
      (coefficientBlock basis (localizedComplexIntegerRing ideal) label).card ≤ 4) := by
  refine ⟨fun χ hχ ψ _ => oddSectionMatrix_sq basis ideal label χ ψ hχ, ?_⟩
  intro hint hodd
  choose! z hz using hint
  obtain ⟨-, -, hdeg⟩ := block_class_defect_witness_character_degree_dvd basis ideal 2 label D hD
  obtain ⟨ha2, hdiv⟩ := hdeg 2 (by rw [hD4]; norm_num)
  obtain ⟨N, hN⟩ := pow_padicValNat_dvd (p := 2) (n := Nat.card G)
  have hNodd : ¬ 2 ∣ N := by
    rintro ⟨M, rfl⟩
    apply pow_succ_padicValNat_not_dvd (p := 2) (Nat.card_pos (α := G)).ne'
    refine ⟨M, ?_⟩
    rw [pow_succ]
    conv_lhs => rw [hN]
    ring
  have hd : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
      ∃ dχ : ℕ, 0 < dχ ∧ Module.finrank ℂ (basis.representation χ).vector =
        2 ^ (padicValNat 2 (Nat.card G) - 2) * dχ := by
    intro χ hχ
    obtain ⟨dχ, hdχ⟩ := hdiv χ hχ
    refine ⟨dχ, Nat.pos_of_ne_zero fun h0 => ?_, hdχ⟩
    apply irreducible_character_degree_ne_zero (basis.representation χ) (basis.irreducible χ)
    rw [FiniteComplexRepresentation.character, Representation.char_one, hdχ, h0, mul_zero,
      Nat.cast_zero]
  choose! d hdpos hdeq using hd
  generalize padicValNat 2 (Nat.card G) = a at hN ha2 hdeq
  have hval : ∀ (ψ : basis.index) (K : ConjClasses G),
      (basis.representation ψ).character (Classical.choose (ConjClasses.exists_rep K))⁻¹ ∈
        localizedComplexIntegerRing ideal := fun ψ K =>
    complexAlgebraicInteger_mem_localized_ring ideal
      (algebraicCharacterValue (basis.representation ψ) _)
  obtain ⟨S, hS⟩ : ∃ S : basis.index → basis.index → localizedComplexIntegerRing ideal,
      S = fun χ ψ => ∑ K ∈ (Finset.univ.filter (fun x : G => Odd (orderOf x))).image
        ConjClasses.mk, localCentralCharacterHom basis ideal χ
          (centralConjugacyClassSum (localizedComplexIntegerRing ideal) K) * ⟨_, hval ψ K⟩ :=
    ⟨_, rfl⟩
  have hScoe : ∀ χ ψ, (S χ ψ : ℂ) =
      ∑ K ∈ (Finset.univ.filter (fun x : G => Odd (orderOf x))).image ConjClasses.mk,
        (localCentralCharacterHom basis ideal χ
          (centralConjugacyClassSum (localizedComplexIntegerRing ideal) K) : ℂ) *
        (basis.representation ψ).character (Classical.choose (ConjClasses.exists_rep K))⁻¹ := by
    intro χ ψ
    rw [hS]
    push_cast
    rfl
  have hSres : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label, ∀ ψ,
      localizedComplexIntegerResidue ideal (S χ ψ) =
        localizedComplexIntegerResidue ideal (S label ψ) := by
    intro χ hχ ψ
    have hsame : centralCharacterResidueHom basis ideal label =
        centralCharacterResidueHom basis ideal χ :=
      (sameCoefficientBlock_iff_centralCharacterResidueHom_eq basis ideal label χ).mp
        ((coefficientBlock_mem_iff _ _ _ _).mp hχ)
    rw [hS]
    simp only [map_sum, map_mul]
    refine Finset.sum_congr rfl fun K _ => ?_
    congr 1
    exact (congrFun (congrArg DFunLike.coe hsame) _).symm
  have hrel : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
      ∀ ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
        ((N : ℂ) * z χ ψ) = (d χ : ℂ) * (S χ ψ : ℂ) := by
    intro χ hχ ψ hψ
    have h := hz χ hχ ψ hψ
    unfold oddSectionMatrix at h
    rw [sum_odd_eq_degree_mul_classSum basis ideal χ ψ, ← hScoe,
      FiniteComplexRepresentation.character,
      Representation.char_one, hdeq χ hχ, hN] at h
    have h2a : (2 : ℂ) ^ a = 2 ^ (a - 2) * 4 := by
      rw [show (4 : ℂ) = 2 ^ 2 by norm_num, ← pow_add, Nat.sub_add_cancel ha2]
    have hN0 : (N : ℂ) ≠ 0 := by
      have : N ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hN
        exact (Nat.card_pos (α := G)).ne' hN
      exact_mod_cast this
    push_cast at h
    rw [h2a] at h
    rw [← h]
    field_simp
  have hrelres : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
      ∀ ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
        (((N : ℤ) * z χ ψ : ℤ) : ComplexAlgebraicIntegers ⧸ ideal) =
          (d χ : ComplexAlgebraicIntegers ⧸ ideal) *
            localizedComplexIntegerResidue ideal (S χ ψ) := by
    intro χ hχ ψ hψ
    have hR : (((N : ℤ) * z χ ψ : ℤ) : localizedComplexIntegerRing ideal) =
        (d χ : localizedComplexIntegerRing ideal) * S χ ψ := by
      apply Subtype.ext
      push_cast
      exact hrel χ hχ ψ hψ
    have h := congrArg (localizedComplexIntegerResidue ideal) hR
    rwa [map_mul, map_intCast, map_natCast] at h
  have hpar : ∀ n : ℤ, (n : ComplexAlgebraicIntegers ⧸ ideal) = 0 ↔ (2 : ℤ) ∣ n := fun n =>
    CharP.intCast_eq_zero_iff _ 2 n
  have hsymm : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
      ∀ ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
        z ψ χ = z χ ψ := by
    intro χ hχ ψ hψ
    have h := oddSectionMatrix_swap basis χ ψ
    rw [hz ψ hψ χ hχ, hz χ hχ ψ hψ, map_intCast] at h
    exact_mod_cast h
  obtain ⟨ρ, hρ, ψ₀, hψ₀, w, hw, hwz⟩ := hodd
  have hzw : z ρ ψ₀ = w := by
    have h := (hz ρ hρ ψ₀ hψ₀).symm.trans hwz
    exact_mod_cast h
  have hN2 : ¬ (2 : ℤ) ∣ (N : ℤ) := by exact_mod_cast hNodd
  have hNw : ¬ (2 : ℤ) ∣ (N : ℤ) * z ρ ψ₀ := by
    rw [hzw]
    intro h2
    rcases Int.prime_two.dvd_mul.mp h2 with h | h
    · exact hN2 h
    · exact (Int.not_even_iff_odd.mpr hw) (even_iff_two_dvd.mpr h)
  have hdρ : (d ρ : ComplexAlgebraicIntegers ⧸ ideal) ≠ 0 := by
    intro h0
    apply hNw
    rw [← hpar, hrelres ρ hρ ψ₀ hψ₀, h0, zero_mul]
  have hσ : localizedComplexIntegerResidue ideal (S label ρ) ≠ 0 := by
    intro h0
    apply hNw
    rw [← hsymm ρ hρ ψ₀ hψ₀, ← hpar, hrelres ψ₀ hψ₀ ρ hρ, hSres ψ₀ hψ₀ ρ, h0, mul_zero]
  have hcol : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
      z χ ρ ≠ 0 := by
    intro χ hχ h0
    have h := hrel χ hχ ρ hρ
    rw [h0, Int.cast_zero, mul_zero] at h
    have hd0 : (d χ : ℂ) ≠ 0 := by exact_mod_cast (hdpos χ hχ).ne'
    have hS0 : S χ ρ = 0 := by
      apply Subtype.ext
      rcases mul_eq_zero.mp h.symm with h1 | h1
      · exact absurd h1 hd0
      · exact h1
    apply hσ
    rw [← hSres χ hχ ρ, hS0, map_zero]
  have haodd : Odd (z ρ ρ) := by
    have h := hrelres ρ hρ ρ hρ
    rw [hSres ρ hρ ρ] at h
    have hne : ((((N : ℤ) * z ρ ρ : ℤ)) : ComplexAlgebraicIntegers ⧸ ideal) ≠ 0 := by
      rw [h]
      exact mul_ne_zero hdρ hσ
    rw [Ne, hpar] at hne
    rcases Int.even_or_odd (z ρ ρ) with he | ho
    · exact absurd (dvd_mul_of_dvd_right (even_iff_two_dvd.mp he) _) hne
    · exact ho
  have hsq := oddSectionMatrix_sq basis ideal label ρ ρ hρ
  have hsqZ : ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
      z χ ρ ^ 2 = 4 * z ρ ρ := by
    have h : ((∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) label,
        z χ ρ ^ 2 : ℤ) : ℂ) = ((4 * z ρ ρ : ℤ) : ℂ) := by
      push_cast
      rw [← hz ρ hρ ρ hρ, ← hsq]
      refine Finset.sum_congr rfl fun χ hχ => ?_
      rw [hz ρ hρ χ hχ, hz χ hχ ρ hρ, ← hsymm ρ hρ χ hχ]
      ring
    exact_mod_cast h
  have hsplit := Finset.add_sum_erase (coefficientBlock basis (localizedComplexIntegerRing ideal)
    label) (fun χ => z χ ρ ^ 2) hρ
  have hlow : ((coefficientBlock basis (localizedComplexIntegerRing ideal) label).erase ρ).card •
      (1 : ℤ) ≤ ∑ χ ∈ (coefficientBlock basis (localizedComplexIntegerRing ideal) label).erase ρ,
        z χ ρ ^ 2 := by
    apply Finset.card_nsmul_le_sum
    intro χ hχ
    have h := hcol χ (Finset.mem_of_mem_erase hχ)
    have : 0 < z χ ρ ^ 2 := by positivity
    omega
  rw [Finset.card_erase_of_mem hρ, nsmul_eq_mul, mul_one] at hlow
  have hB1 : 1 ≤ (coefficientBlock basis (localizedComplexIntegerRing ideal) label).card :=
    Finset.card_pos.mpr ⟨ρ, hρ⟩
  have hineq : z ρ ρ ^ 2 +
      (((coefficientBlock basis (localizedComplexIntegerRing ideal) label).card - 1 : ℕ) : ℤ) ≤
        4 * z ρ ρ := by
    rw [hsqZ] at hsplit
    linarith
  rw [Nat.cast_sub hB1, Nat.cast_one] at hineq
  obtain ⟨k, hk⟩ := haodd
  rw [hk] at hineq
  have hfinal : ((coefficientBlock basis (localizedComplexIntegerRing ideal) label).card : ℤ) ≤
      4 := by
    rcases le_or_gt k 0 with hk0 | hk0
    · nlinarith [mul_nonneg (neg_nonneg.mpr hk0) (by linarith : (0 : ℤ) ≤ 1 - k)]
    · nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ k) (by linarith : (0 : ℤ) ≤ k - 1)]
  exact_mod_cast hfinal

end CFSG.Semidihedral.Principal
