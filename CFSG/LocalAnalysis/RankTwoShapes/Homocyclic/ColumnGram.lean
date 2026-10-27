module

public import CFSG.LocalAnalysis.RankTwoShapes.Homocyclic.Local
public import CFSG.LocalAnalysis.RankTwoShapes.Homocyclic.CentralizerNorm

public section

namespace CFSG.RankTwoShapes

open CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical

section Characters

variable {G : Type} [Group G] {n : ℕ} {S : Subgroup G} (e : S ≃* HomocyclicGroup n)

theorem homocyclicCoord_mul (s t : S) :
    homocyclicCoord e (s * t) = homocyclicCoord e s + homocyclicCoord e t := by
  unfold homocyclicCoord
  rw [map_mul]
  rfl

theorem homocyclicCoord_one : homocyclicCoord e 1 = 0 := by
  unfold homocyclicCoord
  rw [map_one]
  rfl

theorem homocyclicCoord_inv (s : S) : homocyclicCoord e s⁻¹ = -homocyclicCoord e s := by
  have h := homocyclicCoord_mul e s⁻¹ s
  rw [inv_mul_cancel, homocyclicCoord_one] at h
  exact (neg_eq_of_add_eq_zero_left h.symm).symm

theorem homocyclicCoord_embed (v : HomocyclicVector n) :
    homocyclicCoord e ⟨homocyclicEmbed e v, homocyclicEmbed_mem e v⟩ = v := by
  apply homocyclicEmbed_injective e
  rw [homocyclicEmbed_coord]

@[expose] noncomputable def homocyclicEquiv : HomocyclicVector n ≃ S where
  toFun v := ⟨homocyclicEmbed e v, homocyclicEmbed_mem e v⟩
  invFun := homocyclicCoord e
  left_inv v := homocyclicCoord_embed e v
  right_inv s := Subtype.ext (homocyclicEmbed_coord e s)

include e in
theorem card_homocyclic_eq_card_vector :
    Nat.card S = Fintype.card (HomocyclicVector n) := by
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (homocyclicEquiv e).symm

@[expose] noncomputable def homocyclicCharHom (ψ : AddChar (HomocyclicVector n) ℂ) : S →* ℂ where
  toFun s := ψ (homocyclicCoord e s)
  map_one' := by rw [homocyclicCoord_one, AddChar.map_zero_eq_one]
  map_mul' s t := by rw [homocyclicCoord_mul, AddChar.map_add_eq_mul]

theorem homocyclicChar_mem_virtualCharacters (ψ : AddChar (HomocyclicVector n) ℂ) :
    (fun s : S => ψ (homocyclicCoord e s)) ∈ virtualCharacters S := by
  let data : FiniteComplexRepresentation.{0, 0} S :=
    { vector := ℂ, representation := scalarHomRepresentation (homocyclicCharHom e ψ) }
  have h := character_mem_virtualCharacters data
  have hchar : data.character = fun s : S => ψ (homocyclicCoord e s) := by
    change (scalarHomRepresentation (homocyclicCharHom e ψ)).character = _
    rw [scalarHomRepresentation_character]
    rfl
  rw [hchar] at h
  exact h

theorem one_mem_virtualCharacters' : (fun _ : S => (1 : ℂ)) ∈ virtualCharacters S := by
  have h := character_mem_virtualCharacters (principalFiniteComplexRepresentation S)
  rw [principalFiniteComplexRepresentation_character] at h
  exact h

variable [Fintype G]

@[expose] noncomputable def homocyclicColumn (basis : FiniteIrreducibleCharacterBasis G)
    (ψ : AddChar (HomocyclicVector n) ℂ) (label : basis.index) : ℂ :=
  characterPairing (fun s : S => (basis.representation label).character s.val)
    (fun s => ψ (homocyclicCoord e s) - 1)

@[expose] noncomputable def homocyclicMultiplicity (basis : FiniteIrreducibleCharacterBasis G)
    (ψ : AddChar (HomocyclicVector n) ℂ) (label : basis.index) : ℂ :=
  characterPairing (fun s : S => (basis.representation label).character s.val)
    (fun s => ψ (homocyclicCoord e s))

theorem characterPairing_homocyclic_eq (f : G → ℂ) (h : HomocyclicVector n → ℂ) :
    characterPairing (fun s : S => f s.val) (fun s => h (homocyclicCoord e s)) =
      (Fintype.card (HomocyclicVector n) : ℂ)⁻¹ *
        ∑ v, f (homocyclicEmbed e v) * h (-v) := by
  unfold characterPairing
  rw [card_homocyclic_eq_card_vector e, ← Equiv.sum_comp (homocyclicEquiv e)]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  change f (homocyclicEmbed e v) * h (homocyclicCoord e
    (⟨homocyclicEmbed e v, homocyclicEmbed_mem e v⟩ : S)⁻¹) = _
  rw [homocyclicCoord_inv, homocyclicCoord_embed]

theorem homocyclicColumn_eq (basis : FiniteIrreducibleCharacterBasis G)
    (ψ : AddChar (HomocyclicVector n) ℂ) (label : basis.index) :
    homocyclicColumn e basis ψ label = (Fintype.card (HomocyclicVector n) : ℂ)⁻¹ *
      ∑ v, (basis.representation label).character (homocyclicEmbed e v) * (ψ (-v) - 1) :=
  characterPairing_homocyclic_eq e _ (fun v => ψ v - 1)

theorem homocyclicMultiplicity_eq (basis : FiniteIrreducibleCharacterBasis G)
    (ψ : AddChar (HomocyclicVector n) ℂ) (label : basis.index) :
    homocyclicMultiplicity e basis ψ label = (Fintype.card (HomocyclicVector n) : ℂ)⁻¹ *
      ∑ v, (basis.representation label).character (homocyclicEmbed e v) * ψ (-v) :=
  characterPairing_homocyclic_eq e _ (fun v => ψ v)

theorem homocyclicColumn_eq_sub (basis : FiniteIrreducibleCharacterBasis G)
    (ψ : AddChar (HomocyclicVector n) ℂ) (label : basis.index) :
    homocyclicColumn e basis ψ label =
      homocyclicMultiplicity e basis ψ label - homocyclicMultiplicity e basis 0 label := by
  rw [homocyclicColumn_eq, homocyclicMultiplicity_eq, homocyclicMultiplicity_eq, ← mul_sub,
    ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  rw [AddChar.zero_apply]
  ring

theorem homocyclicColumn_integer (basis : FiniteIrreducibleCharacterBasis G)
    (ψ : AddChar (HomocyclicVector n) ℂ) (label : basis.index) :
    ∃ z : ℤ, homocyclicColumn e basis ψ label = z := by
  apply characterPairing_virtual_integer
  · exact character_mem_virtualCharacters
      (inflatedFiniteComplexRepresentation S.subtype (basis.representation label))
  · exact Submodule.sub_mem _ (homocyclicChar_mem_virtualCharacters e ψ)
      (one_mem_virtualCharacters' (S := S))

theorem homocyclicMultiplicity_integer (basis : FiniteIrreducibleCharacterBasis G)
    (ψ : AddChar (HomocyclicVector n) ℂ) (label : basis.index) :
    ∃ z : ℤ, homocyclicMultiplicity e basis ψ label = z := by
  apply characterPairing_virtual_integer
  · exact character_mem_virtualCharacters
      (inflatedFiniteComplexRepresentation S.subtype (basis.representation label))
  · exact homocyclicChar_mem_virtualCharacters e ψ

theorem addChar_sum_neg_eq_zero (ψ : AddChar (HomocyclicVector n) ℂ) (hψ : ψ ≠ 0) :
    ∑ v, ψ (-v) = 0 := by
  rw [← Equiv.sum_comp (Equiv.neg _)]
  simp only [Equiv.neg_apply, neg_neg]
  exact AddChar.sum_eq_zero_iff_ne_zero.mpr hψ

theorem homocyclicColumn_principal (basis : FiniteIrreducibleCharacterBasis G)
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (ψ : AddChar (HomocyclicVector n) ℂ) (hψ : ψ ≠ 0) :
    homocyclicColumn e basis ψ principal = -1 := by
  rw [homocyclicColumn_eq, hprincipal]
  simp only [Pi.one_apply, one_mul, Finset.sum_sub_distrib, addChar_sum_neg_eq_zero ψ hψ,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, zero_sub]
  have hne : (Fintype.card (HomocyclicVector n) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

theorem homocyclic_restriction_fourier (basis : FiniteIrreducibleCharacterBasis G)
    (label : basis.index) (v : HomocyclicVector n) :
    (basis.representation label).character (homocyclicEmbed e v) =
      ∑ φ : AddChar (HomocyclicVector n) ℂ, homocyclicMultiplicity e basis φ label * φ v := by
  simp_rw [homocyclicMultiplicity_eq, mul_assoc, ← Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hinner : ∀ w : HomocyclicVector n,
      ∑ φ : AddChar (HomocyclicVector n) ℂ,
        (basis.representation label).character (homocyclicEmbed e w) * φ (-w) * φ v =
      (basis.representation label).character (homocyclicEmbed e w) *
        (if v - w = 0 then (Fintype.card (HomocyclicVector n) : ℂ) else 0) := by
    intro w
    rw [← AddChar.sum_apply_eq_ite (v - w), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro φ _
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  simp_rw [hinner]
  rw [Finset.sum_eq_single v]
  · rw [sub_self, ite_eq_left rfl]
    have hne : (Fintype.card (HomocyclicVector n) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    field_simp
  · intro w _ hw
    rw [ite_eq_right (sub_ne_zero.mpr (Ne.symm hw)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ v) h

end Characters

section Kernel

variable {G : Type} [Group G] [Fintype G] {n : ℕ} (S : Sylow 2 G)
  (e : (S : Subgroup G) ≃* HomocyclicGroup n)
  (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
  [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
  (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)

omit [Fintype G] in
theorem sylow_two_orderOf_dvd (s : G) (hs : s ∈ (S : Subgroup G)) : ∃ k : ℕ, orderOf s ∣ 2 ^ k := by
  obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
  refine ⟨k, orderOf_dvd_of_pow_eq_one ?_⟩
  have := congrArg Subtype.val hk
  simpa using this

theorem homocyclic_block_kernel_nonconj {s t : G} (hs : s ∈ (S : Subgroup G))
    (ht : t ∈ (S : Subgroup G)) (hst : ¬ IsConj s t) :
    ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation label).character s * (basis.representation label).character t⁻¹ =
        0 := by
  obtain ⟨k, hk⟩ := sylow_two_orderOf_dvd S s hs
  obtain ⟨k', hk'⟩ := sylow_two_orderOf_dvd S t ht
  have h := coefficientBlock_section_column_orthogonality basis ideal 2 principal s t 1 1 k k'
    hk hk' (by simp) (by simp) (Commute.one_right s) (Commute.one_right t) hst
  simpa using h

include e in
theorem homocyclic_block_kernel_conj (hn : 1 ≤ n)
    (hprincipal : (basis.representation principal).character = 1) {s t : G}
    (hs : s ∈ (S : Subgroup G)) (hs1 : s ≠ 1) (hst : IsConj s t) :
    ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation label).character s * (basis.representation label).character t⁻¹ =
        Nat.card S := by
  have hinv : ∀ label, (basis.representation label).character t⁻¹ =
      starRingEnd ℂ ((basis.representation label).character s) := by
    intro label
    rw [finite_character_conjugate_inverse]
    obtain ⟨c, rfl⟩ := isConj_iff.mp hst
    rw [show (c * s * c⁻¹)⁻¹ = c * s⁻¹ * c⁻¹ by group]
    exact Representation.char_conj _ s⁻¹ c
  simp_rw [hinv]
  obtain ⟨k, hk⟩ := sylow_two_orderOf_dvd S s hs
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists
    (G := Subgroup.centralizer (Subgroup.zpowers s : Set G))
  obtain ⟨localPrincipal, hlocalPrincipal⟩ :=
    finiteIrreducibleCharacterBasis_contains_irreducible localBasis
      (principalFiniteComplexRepresentation _)
      (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  obtain ⟨K, hKn, hKcop, hKp, hKcard⟩ := homocyclic_centralizer_zpowers_complement S e hn hs hs1
  obtain ⟨h1, h2, -⟩ := principal_primary_column_centralizer_norm_of_normal_complement basis
    ideal 2 principal hprincipal s k hk localBasis localPrincipal hlocalPrincipal K hKcop hKp
  rw [h1, h2, hKcard]

end Kernel

section Gram

variable {G : Type} [Group G] [Fintype G] {n : ℕ}

theorem addChar_shifted_pairing (ψ φ : AddChar (HomocyclicVector n) ℂ) (hψ : ψ ≠ 0)
    (hφ : φ ≠ 0) :
    (Fintype.card (HomocyclicVector n) : ℂ)⁻¹ * ∑ v, (ψ (-v) - 1) * (φ v - 1) =
      (if φ = ψ then 1 else 0) + 1 := by
  have hexpand : ∀ v, (ψ (-v) - 1) * (φ v - 1) = (φ * ψ⁻¹) v - ψ (-v) - φ v + 1 := by
    intro v
    rw [AddChar.mul_apply, AddChar.inv_apply]
    ring
  have hne : (Fintype.card (HomocyclicVector n) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hiff : φ * ψ⁻¹ = 0 ↔ φ = ψ := by
    rw [← mul_inv_eq_one (a := φ) (b := ψ)]
    rfl
  have hsum : ∑ v, (ψ (-v) - 1) * (φ v - 1) =
      (if φ = ψ then (Fintype.card (HomocyclicVector n) : ℂ) else 0) +
        (Fintype.card (HomocyclicVector n) : ℂ) := by
    simp_rw [hexpand]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      addChar_sum_neg_eq_zero ψ hψ, AddChar.sum_eq_zero_iff_ne_zero.mpr hφ, AddChar.sum_eq_ite]
    simp only [hiff, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, sub_zero]
  rw [hsum]
  split_ifs
  · field_simp
  · field_simp
    ring

theorem sum_ite_three {α : Type*} [Fintype α] [DecidableEq α] (x y z : α) (hxy : x ≠ y)
    (hxz : x ≠ z) (hyz : y ≠ z) (f : α → ℂ) (c : ℂ) :
    ∑ w, f w * (if w = x ∨ w = y ∨ w = z then c else 0) = c * (f x + f y + f z) := by
  have h : ∀ w, f w * (if w = x ∨ w = y ∨ w = z then c else 0) =
      if w ∈ ({x, y, z} : Finset α) then c * f w else 0 := by
    intro w
    simp only [Finset.mem_insert, Finset.mem_singleton]
    split_ifs <;> ring
  simp_rw [h]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_insert (by simp [hxy, hxz]),
    Finset.sum_insert (by simp [hyz]), Finset.sum_singleton]
  ring

theorem sum_product_expansion {ι α : Type*} [Fintype α] (B : Finset ι) (F H : ι → α → ℂ)
    (a b : α → ℂ) (c : ℂ) :
    ∑ χ ∈ B, (c * ∑ v, F χ v * a v) * (c * ∑ w, H χ w * b w) =
      c * c * ∑ v, ∑ w, a v * b w * ∑ χ ∈ B, F χ v * H χ w := by
  calc ∑ χ ∈ B, (c * ∑ v, F χ v * a v) * (c * ∑ w, H χ w * b w)
      = ∑ χ ∈ B, c * c * ∑ v, ∑ w, a v * b w * (F χ v * H χ w) := by
        apply Finset.sum_congr rfl
        intro χ _
        rw [mul_mul_mul_comm, Finset.sum_mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro v _
        apply Finset.sum_congr rfl
        intro w _
        ring
    _ = c * c * ∑ χ ∈ B, ∑ v, ∑ w, a v * b w * (F χ v * H χ w) := by rw [Finset.mul_sum]
    _ = c * c * ∑ v, ∑ w, ∑ χ ∈ B, a v * b w * (F χ v * H χ w) := by
        congr 1
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro v _
        rw [Finset.sum_comm]
    _ = c * c * ∑ v, ∑ w, a v * b w * ∑ χ ∈ B, F χ v * H χ w := by
        congr 1
        apply Finset.sum_congr rfl
        intro v _
        apply Finset.sum_congr rfl
        intro w _
        rw [Finset.mul_sum]

variable (S : Sylow 2 G) (e : (S : Subgroup G) ≃* HomocyclicGroup n)
  (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
  [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
  (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)

theorem homocyclicColumn_eq_inv (ψ : AddChar (HomocyclicVector n) ℂ) (label : basis.index) :
    homocyclicColumn e basis ψ label = (Fintype.card (HomocyclicVector n) : ℂ)⁻¹ *
      ∑ w, (basis.representation label).character (homocyclicEmbed e w)⁻¹ * (ψ w - 1) := by
  rw [homocyclicColumn_eq]
  congr 1
  rw [← Equiv.sum_comp (Equiv.neg _)]
  apply Finset.sum_congr rfl
  intro w _
  simp only [Equiv.neg_apply, neg_neg, homocyclicEmbed_neg]

theorem homocyclicColumn_gram (hn : 1 ≤ n)
    (hprincipal : (basis.representation principal).character = 1) {g₀ : G}
    (hg₀ : g₀ ∈ Subgroup.normalizer ((S : Subgroup G) : Set G))
    (hg₀C : g₀ ∉ Subgroup.centralizer ((S : Subgroup G) : Set G))
    (ψ φ : AddChar (HomocyclicVector n) ℂ) (hψ : ψ ≠ 0) (hφ : φ ≠ 0) :
    ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        homocyclicColumn e basis ψ label * homocyclicColumn e basis φ label =
      3 + ((if φ = ψ then 1 else 0) +
        (if φ.compAddMonoidHom (homocyclicConj e g₀ hg₀) = ψ then 1 else 0) +
        (if φ.compAddMonoidHom ((homocyclicConj e g₀ hg₀).comp (homocyclicConj e g₀ hg₀)) = ψ
          then 1 else 0)) := by
  set T := homocyclicConj e g₀ hg₀
  set q : ℂ := (Fintype.card (HomocyclicVector n) : ℂ)
  have hq : q ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hqS : (Nat.card S : ℂ) = q := by
    rw [card_homocyclic_eq_card_vector e]
  simp_rw [homocyclicColumn_eq e basis ψ, homocyclicColumn_eq_inv S e basis φ]
  rw [sum_product_expansion]
  have hkernel : ∀ v w : HomocyclicVector n, v ≠ 0 →
      ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation label).character (homocyclicEmbed e v) *
          (basis.representation label).character (homocyclicEmbed e w)⁻¹ =
      if w = v ∨ w = T v ∨ w = T (T v) then q else 0 := by
    intro v w hv
    have hv1 : homocyclicEmbed e v ≠ 1 := fun h => hv ((homocyclicEmbed_eq_one_iff e v).mp h)
    have hiff : IsConj (homocyclicEmbed e v) (homocyclicEmbed e w) ↔
        (w = v ∨ w = T v ∨ w = T (T v)) := by
      rw [homocyclic_isConj_iff S e hn hg₀ hg₀C (homocyclicEmbed_mem e v)
        (homocyclicEmbed_mem e w), ← homocyclicEmbed_conj e g₀ hg₀ v,
        ← homocyclicEmbed_conj e g₀ hg₀ (homocyclicConj e g₀ hg₀ v),
        (homocyclicEmbed_injective e).eq_iff, (homocyclicEmbed_injective e).eq_iff,
        (homocyclicEmbed_injective e).eq_iff]
    by_cases hc : IsConj (homocyclicEmbed e v) (homocyclicEmbed e w)
    · rw [ite_eq_left (hiff.mp hc), homocyclic_block_kernel_conj S e ideal basis principal hn
        hprincipal (homocyclicEmbed_mem e v) hv1 hc, hqS]
    · rw [ite_eq_right (fun h => hc (hiff.mpr h)), homocyclic_block_kernel_nonconj S ideal basis
        principal (homocyclicEmbed_mem e v) (homocyclicEmbed_mem e w) hc]
  have hTv : ∀ v, homocyclicEmbed e (T v) = g₀ * homocyclicEmbed e v * g₀⁻¹ :=
    fun v => homocyclicEmbed_conj e g₀ hg₀ v
  have hdistinct : ∀ v : HomocyclicVector n, v ≠ 0 → v ≠ T v ∧ v ≠ T (T v) ∧ T v ≠ T (T v) := by
    intro v hv
    have hv1 : homocyclicEmbed e v ≠ 1 := fun h => hv ((homocyclicEmbed_eq_one_iff e v).mp h)
    obtain ⟨h1, h2, h3⟩ := homocyclic_orbit_distinct S e hn hg₀ hg₀C (homocyclicEmbed_mem e v) hv1
    refine ⟨fun h => h1 ?_, fun h => h3 ?_, fun h => h2 ?_⟩
    · rw [← hTv, ← h]
    · rw [← hTv, ← hTv, ← h]
    · rw [← hTv, ← hTv]
      exact congrArg _ h
  have hinner : ∀ v : HomocyclicVector n,
      ∑ w, (ψ (-v) - 1) * (φ w - 1) *
        ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
          (basis.representation label).character (homocyclicEmbed e v) *
            (basis.representation label).character (homocyclicEmbed e w)⁻¹ =
      q * ((ψ (-v) - 1) * ((φ v - 1) + (φ (T v) - 1) + (φ (T (T v)) - 1))) := by
    intro v
    by_cases hv : v = 0
    · subst hv
      simp
    · simp_rw [hkernel v _ hv, mul_assoc]
      rw [← Finset.mul_sum]
      obtain ⟨h1, h2, h3⟩ := hdistinct v hv
      rw [sum_ite_three v (T v) (T (T v)) h1 h2 h3 (fun w => φ w - 1) q]
      ring
  simp_rw [hinner]
  rw [← Finset.mul_sum]
  have hsplit : ∑ v, (ψ (-v) - 1) * ((φ v - 1) + (φ (T v) - 1) + (φ (T (T v)) - 1)) =
      ∑ v, (ψ (-v) - 1) * (φ v - 1) +
      ∑ v, (ψ (-v) - 1) * ((φ.compAddMonoidHom T) v - 1) +
      ∑ v, (ψ (-v) - 1) * ((φ.compAddMonoidHom (T.comp T)) v - 1) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    simp only [AddChar.compAddMonoidHom_apply, AddMonoidHom.coe_comp, Function.comp_apply]
    ring
  rw [hsplit]
  have hT : Function.Surjective T := by
    obtain ⟨m, hm, hiter⟩ := homocyclicConj_odd_iterate S e g₀ hg₀
    exact (Finite.injective_iff_surjective.mp (iterate_odd_injective (⇑T) hm hiter))
  have hcompne : ∀ (U : HomocyclicVector n →+ HomocyclicVector n), Function.Surjective U →
      φ.compAddMonoidHom U ≠ 0 := by
    intro U hU h0
    apply hφ
    ext w
    obtain ⟨u, rfl⟩ := hU w
    have := congrArg (fun χ : AddChar (HomocyclicVector n) ℂ => χ u) h0
    simpa using this
  have hTT : Function.Surjective (T.comp T) := hT.comp hT
  have e1 := addChar_shifted_pairing ψ φ hψ hφ
  have e2 := addChar_shifted_pairing ψ (φ.compAddMonoidHom T) hψ (hcompne T hT)
  have e3 := addChar_shifted_pairing ψ (φ.compAddMonoidHom (T.comp T)) hψ (hcompne _ hTT)
  have hcalc : q⁻¹ * q⁻¹ * (q * (∑ v, (ψ (-v) - 1) * (φ v - 1) +
      ∑ v, (ψ (-v) - 1) * ((φ.compAddMonoidHom T) v - 1) +
      ∑ v, (ψ (-v) - 1) * ((φ.compAddMonoidHom (T.comp T)) v - 1))) =
      q⁻¹ * ∑ v, (ψ (-v) - 1) * (φ v - 1) +
      q⁻¹ * ∑ v, (ψ (-v) - 1) * ((φ.compAddMonoidHom T) v - 1) +
      q⁻¹ * ∑ v, (ψ (-v) - 1) * ((φ.compAddMonoidHom (T.comp T)) v - 1) := by
    field_simp
  rw [hcalc, e1, e2, e3]
  ring

end Gram

section Orbits

variable {G : Type} [Group G] {n : ℕ} {S : Subgroup G} (e : S ≃* HomocyclicGroup n)

theorem homocyclicConj_one (v : HomocyclicVector n) :
    homocyclicConj e 1 (Subgroup.one_mem _) v = v := by
  apply homocyclicEmbed_injective e
  rw [homocyclicEmbed_conj]
  group

theorem homocyclicConj_mul' {g h : G} (hg : g ∈ Subgroup.normalizer (S : Set G))
    (hh : h ∈ Subgroup.normalizer (S : Set G)) (v : HomocyclicVector n) :
    homocyclicConj e (g * h) (Subgroup.mul_mem _ hg hh) v =
      homocyclicConj e g hg (homocyclicConj e h hh v) := by
  apply homocyclicEmbed_injective e
  simp only [homocyclicEmbed_conj]
  group

theorem homocyclicConj_inv_cancel {g : G} (hg : g ∈ Subgroup.normalizer (S : Set G))
    (v : HomocyclicVector n) :
    homocyclicConj e g hg (homocyclicConj e g⁻¹ (Subgroup.inv_mem _ hg) v) = v := by
  apply homocyclicEmbed_injective e
  simp only [homocyclicEmbed_conj]
  group

@[expose] def HomocyclicOrbitRel (φ ψ : AddChar (HomocyclicVector n) ℂ) : Prop :=
  ∃ g, ∃ hg : g ∈ Subgroup.normalizer (S : Set G), ψ = φ.compAddMonoidHom (homocyclicConj e g hg)

theorem homocyclicOrbitRel_refl (φ : AddChar (HomocyclicVector n) ℂ) :
    HomocyclicOrbitRel e φ φ :=
  ⟨1, Subgroup.one_mem _, by ext v; simp [homocyclicConj_one]⟩

theorem homocyclicOrbitRel_symm {φ ψ : AddChar (HomocyclicVector n) ℂ}
    (h : HomocyclicOrbitRel e φ ψ) : HomocyclicOrbitRel e ψ φ := by
  obtain ⟨g, hg, rfl⟩ := h
  refine ⟨g⁻¹, Subgroup.inv_mem _ hg, ?_⟩
  ext v
  simp [homocyclicConj_inv_cancel]

theorem homocyclicOrbitRel_trans {φ ψ χ : AddChar (HomocyclicVector n) ℂ}
    (h1 : HomocyclicOrbitRel e φ ψ) (h2 : HomocyclicOrbitRel e ψ χ) :
    HomocyclicOrbitRel e φ χ := by
  obtain ⟨g, hg, rfl⟩ := h1
  obtain ⟨h, hh, rfl⟩ := h2
  refine ⟨g * h, Subgroup.mul_mem _ hg hh, ?_⟩
  ext v
  simp only [AddChar.compAddMonoidHom_apply]
  rw [homocyclicConj_mul' e hg hh v]

theorem addChar_comp_eq_self_eq_zero (U : HomocyclicVector n →+ HomocyclicVector n)
    (hU : ∀ v, U v = v → v = 0) (φ : AddChar (HomocyclicVector n) ℂ)
    (hφ : φ.compAddMonoidHom U = φ) : φ = 0 := by
  have hinj : Function.Injective (fun v => U v - v) := by
    intro a b hab
    have h : U (a - b) = a - b := by
      simp only at hab
      rw [map_sub]
      linear_combination (norm := abel_nf) hab
    exact sub_eq_zero.mp (hU _ h)
  have hsurj := Finite.injective_iff_surjective.mp hinj
  ext w
  obtain ⟨u, rfl⟩ := hsurj w
  change φ (U u - u) = (0 : AddChar (HomocyclicVector n) ℂ) (U u - u)
  have hu : φ (U u) = φ u := by
    rw [← AddChar.compAddMonoidHom_apply, hφ]
  rw [AddChar.zero_apply, sub_eq_add_neg, AddChar.map_add_eq_mul, hu, ← AddChar.map_add_eq_mul,
    add_neg_cancel, AddChar.map_zero_eq_one]

end Orbits

section OrbitStructure

variable {G : Type} [Group G] [Finite G] {n : ℕ} (S : Sylow 2 G)
  (e : (S : Subgroup G) ≃* HomocyclicGroup n)

include e in
theorem homocyclicConj_fixed_point_free (hn : 1 ≤ n) {g₀ : G}
    (hg₀ : g₀ ∈ Subgroup.normalizer ((S : Subgroup G) : Set G))
    (hg₀C : g₀ ∉ Subgroup.centralizer ((S : Subgroup G) : Set G)) :
    (∀ v, homocyclicConj e g₀ hg₀ v = v → v = 0) ∧
    (∀ v, homocyclicConj e g₀ hg₀ (homocyclicConj e g₀ hg₀ v) = v → v = 0) ∧
    (∀ v, homocyclicConj e g₀ hg₀ (homocyclicConj e g₀ hg₀ (homocyclicConj e g₀ hg₀ v)) = v) := by
  obtain ⟨m, hm, hT⟩ := homocyclicConj_odd_iterate S e g₀ hg₀
  have hTne : ∃ v, homocyclicConj e g₀ hg₀ v ≠ v := by
    by_contra hall
    push Not at hall
    exact hg₀C ((homocyclicConj_eq_id_iff e g₀ hg₀).mp hall)
  obtain ⟨hfpf, hcube⟩ := vector_odd_endomorphism_cube hn _ hm hT hTne
  have h1 : ∀ v, homocyclicConj e g₀ hg₀ v = v → v = 0 := by
    intro v hv
    by_contra hv0
    exact hfpf v hv0 hv
  refine ⟨h1, fun v hv => h1 v (iterate_odd_fixed _ hm hT v hv), hcube⟩

include e in
theorem homocyclicConj_trichotomy (hn : 1 ≤ n) {g₀ : G}
    (hg₀ : g₀ ∈ Subgroup.normalizer ((S : Subgroup G) : Set G))
    (hg₀C : g₀ ∉ Subgroup.centralizer ((S : Subgroup G) : Set G)) {g : G}
    (hg : g ∈ Subgroup.normalizer ((S : Subgroup G) : Set G)) :
    (∀ v, homocyclicConj e g hg v = v) ∨
    (∀ v, homocyclicConj e g hg v = homocyclicConj e g₀ hg₀ v) ∨
    (∀ v, homocyclicConj e g hg v = homocyclicConj e g₀ hg₀ (homocyclicConj e g₀ hg₀ v)) := by
  have hcomm : ∀ c ∈ Subgroup.centralizer ((S : Subgroup G) : Set G), ∀ v,
      c * homocyclicEmbed e v * c⁻¹ = homocyclicEmbed e v := by
    intro c hc v
    rw [← Subgroup.mem_centralizer_iff.mp hc _ (homocyclicEmbed_mem e v)]
    group
  rcases homocyclic_normalizer_trichotomy S e hn hg₀ hg₀C hg with h0 | h1 | h2
  · left
    exact (homocyclicConj_eq_id_iff e g hg).mpr h0
  · right; left
    intro v
    apply homocyclicEmbed_injective e
    rw [homocyclicEmbed_conj, homocyclicEmbed_conj]
    calc g * homocyclicEmbed e v * g⁻¹ =
        g₀ * ((g₀⁻¹ * g) * homocyclicEmbed e v * (g₀⁻¹ * g)⁻¹) * g₀⁻¹ := by group
      _ = g₀ * homocyclicEmbed e v * g₀⁻¹ := by rw [hcomm _ h1]
  · right; right
    intro v
    apply homocyclicEmbed_injective e
    rw [homocyclicEmbed_conj, homocyclicEmbed_conj, homocyclicEmbed_conj]
    calc g * homocyclicEmbed e v * g⁻¹ =
        g₀ * (g₀ * ((g₀⁻¹ * (g₀⁻¹ * g)) * homocyclicEmbed e v * (g₀⁻¹ * (g₀⁻¹ * g))⁻¹) * g₀⁻¹) *
          g₀⁻¹ := by group
      _ = g₀ * (g₀ * homocyclicEmbed e v * g₀⁻¹) * g₀⁻¹ := by rw [hcomm _ h2]

include e in
theorem homocyclicOrbitRel_iff (hn : 1 ≤ n) {g₀ : G}
    (hg₀ : g₀ ∈ Subgroup.normalizer ((S : Subgroup G) : Set G))
    (hg₀C : g₀ ∉ Subgroup.centralizer ((S : Subgroup G) : Set G))
    (φ ψ : AddChar (HomocyclicVector n) ℂ) :
    HomocyclicOrbitRel e φ ψ ↔ (φ = ψ ∨ φ.compAddMonoidHom (homocyclicConj e g₀ hg₀) = ψ ∨
      φ.compAddMonoidHom ((homocyclicConj e g₀ hg₀).comp (homocyclicConj e g₀ hg₀)) = ψ) := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    rcases homocyclicConj_trichotomy S e hn hg₀ hg₀C hg with h0 | h1 | h2
    · left
      ext v
      simp [h0]
    · right; left
      ext v
      simp [h1]
    · right; right
      ext v
      simp [h2]
  · rintro (rfl | rfl | rfl)
    · exact homocyclicOrbitRel_refl e φ
    · exact ⟨g₀, hg₀, rfl⟩
    · refine ⟨g₀ * g₀, Subgroup.mul_mem _ hg₀ hg₀, ?_⟩
      ext v
      simp only [AddChar.compAddMonoidHom_apply, AddMonoidHom.coe_comp, Function.comp_apply]
      rw [homocyclicConj_mul' e hg₀ hg₀ v]

end OrbitStructure

section Invariance

variable {G : Type} [Group G] [Fintype G] {n : ℕ} {S : Subgroup G} (e : S ≃* HomocyclicGroup n)
  (basis : FiniteIrreducibleCharacterBasis G)

theorem homocyclicMultiplicity_comp_conj (φ : AddChar (HomocyclicVector n) ℂ) {g : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) (label : basis.index) :
    homocyclicMultiplicity e basis (φ.compAddMonoidHom (homocyclicConj e g hg)) label =
      homocyclicMultiplicity e basis φ label := by
  rw [homocyclicMultiplicity_eq, homocyclicMultiplicity_eq]
  congr 1
  have hbij : Function.Bijective (homocyclicConj e g hg) := by
    constructor
    · intro a b hab
      have := congrArg (homocyclicConj e g⁻¹ (Subgroup.inv_mem _ hg)) hab
      apply homocyclicEmbed_injective e
      have h1 := congrArg (homocyclicEmbed e) this
      simp only [homocyclicEmbed_conj] at h1
      simpa [mul_assoc] using h1
    · intro v
      refine ⟨homocyclicConj e g⁻¹ (Subgroup.inv_mem _ hg) v, ?_⟩
      exact homocyclicConj_inv_cancel e hg v
  rw [← hbij.sum_comp (fun v => (basis.representation label).character (homocyclicEmbed e v) *
    φ (-v))]
  apply Finset.sum_congr rfl
  intro v _
  simp only [AddChar.compAddMonoidHom_apply, map_neg, homocyclicEmbed_conj]
  congr 1
  exact (Representation.char_conj (basis.representation label).representation
    (homocyclicEmbed e v) g).symm

theorem homocyclicColumn_comp_conj (φ : AddChar (HomocyclicVector n) ℂ) {g : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) (label : basis.index) :
    homocyclicColumn e basis (φ.compAddMonoidHom (homocyclicConj e g hg)) label =
      homocyclicColumn e basis φ label := by
  rw [homocyclicColumn_eq_sub, homocyclicColumn_eq_sub, homocyclicMultiplicity_comp_conj]

theorem homocyclicColumn_orbit (φ ψ : AddChar (HomocyclicVector n) ℂ)
    (h : HomocyclicOrbitRel e φ ψ) (label : basis.index) :
    homocyclicColumn e basis ψ label = homocyclicColumn e basis φ label := by
  obtain ⟨g, hg, rfl⟩ := h
  exact homocyclicColumn_comp_conj e basis φ hg label

theorem homocyclicMultiplicity_orbit (φ ψ : AddChar (HomocyclicVector n) ℂ)
    (h : HomocyclicOrbitRel e φ ψ) (label : basis.index) :
    homocyclicMultiplicity e basis ψ label = homocyclicMultiplicity e basis φ label := by
  obtain ⟨g, hg, rfl⟩ := h
  exact homocyclicMultiplicity_comp_conj e basis φ hg label

end Invariance

section Iterates

variable {n : ℕ}

@[expose] def addCharIter (U : HomocyclicVector n →+ HomocyclicVector n)
    (φ : AddChar (HomocyclicVector n) ℂ) : ℕ → AddChar (HomocyclicVector n) ℂ
  | 0 => φ
  | k + 1 => (addCharIter U φ k).compAddMonoidHom U

theorem addCharIter_apply (U : HomocyclicVector n →+ HomocyclicVector n)
    (φ : AddChar (HomocyclicVector n) ℂ) (k : ℕ) (v : HomocyclicVector n) :
    addCharIter U φ k v = φ ((⇑U)^[k] v) := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
    change addCharIter U φ k (U v) = _
    rw [ih, Function.iterate_succ_apply]

theorem addCharIter_add (U : HomocyclicVector n →+ HomocyclicVector n)
    (φ : AddChar (HomocyclicVector n) ℂ) (a b : ℕ) :
    addCharIter U (addCharIter U φ a) b = addCharIter U φ (a + b) := by
  ext v
  rw [addCharIter_apply, addCharIter_apply, addCharIter_apply, Function.iterate_add_apply]

end Iterates

section Node

variable {G : Type} [Group G] [Fintype G] {n : ℕ} (S : Sylow 2 G)
  (e : (S : Subgroup G) ≃* HomocyclicGroup n)
  (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
  [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
  (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)

theorem homocyclicColumn_degree_sum (ψ : AddChar (HomocyclicVector n) ℂ) :
    ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      homocyclicColumn e basis ψ label * (basis.representation label).character 1 = 0 := by
  simp_rw [homocyclicColumn_eq e basis ψ]
  have hswap : ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (Fintype.card (HomocyclicVector n) : ℂ)⁻¹ *
        (∑ v, (basis.representation label).character (homocyclicEmbed e v) * (ψ (-v) - 1)) *
          (basis.representation label).character 1 =
      (Fintype.card (HomocyclicVector n) : ℂ)⁻¹ * ∑ v, (ψ (-v) - 1) *
        ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
          (basis.representation label).character (homocyclicEmbed e v) *
            (basis.representation label).character 1⁻¹ := by
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro label _
    rw [inv_one]
    ring
  rw [hswap]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro v _
  by_cases hv : v = 0
  · subst hv
    rw [neg_zero, AddChar.map_zero_eq_one, sub_self, zero_mul]
  · have hv1 : ¬ IsConj (homocyclicEmbed e v) 1 := fun h =>
      hv ((homocyclicEmbed_eq_one_iff e v).mp (isConj_one_left.mp h))
    rw [homocyclic_block_kernel_nonconj S ideal basis principal (homocyclicEmbed_mem e v)
      (Subgroup.one_mem _) hv1, mul_zero]

theorem addChar_comp_ne_zero (U : HomocyclicVector n →+ HomocyclicVector n)
    (hU : Function.Surjective U) (φ : AddChar (HomocyclicVector n) ℂ) (hφ : φ ≠ 0) :
    φ.compAddMonoidHom U ≠ 0 := by
  intro h0
  apply hφ
  ext w
  obtain ⟨u, rfl⟩ := hU w
  have := congrArg (fun χ : AddChar (HomocyclicVector n) ℂ => χ u) h0
  simpa using this

omit [Fintype G] in
include e in
theorem homocyclicConj_surjective {g : G} (hg : g ∈ Subgroup.normalizer ((S : Subgroup G) : Set G))
    [Finite G] : Function.Surjective (homocyclicConj e g hg) := by
  obtain ⟨m, hm, hiter⟩ := homocyclicConj_odd_iterate S e g hg
  exact Finite.injective_iff_surjective.mp (iterate_odd_injective _ hm hiter)

include e in
theorem homocyclic_orbit_indicator (hn : 1 ≤ n) {g₀ : G}
    (hg₀ : g₀ ∈ Subgroup.normalizer ((S : Subgroup G) : Set G))
    (hg₀C : g₀ ∉ Subgroup.centralizer ((S : Subgroup G) : Set G))
    (ψ φ : AddChar (HomocyclicVector n) ℂ) (hψ : ψ ≠ 0) :
    ((if φ = ψ then (1 : ℂ) else 0) +
        (if φ.compAddMonoidHom (homocyclicConj e g₀ hg₀) = ψ then 1 else 0) +
        (if φ.compAddMonoidHom ((homocyclicConj e g₀ hg₀).comp (homocyclicConj e g₀ hg₀)) = ψ
          then 1 else 0)) =
      if HomocyclicOrbitRel e φ ψ then 1 else 0 := by
  rw [homocyclicOrbitRel_iff S e hn hg₀ hg₀C]
  obtain ⟨hfpf1, hfpf2, -⟩ := homocyclicConj_fixed_point_free S e hn hg₀ hg₀C
  set T := homocyclicConj e g₀ hg₀
  have hTT : ∀ v, (T.comp T) v = v → v = 0 := fun v hv => hfpf2 v hv
  have hcompT : ∀ χ : AddChar (HomocyclicVector n) ℂ,
      χ.compAddMonoidHom (T.comp T) = (χ.compAddMonoidHom T).compAddMonoidHom T := by
    intro χ
    ext v
    rfl
  have h01 : ¬ (φ = ψ ∧ φ.compAddMonoidHom T = ψ) := by
    rintro ⟨rfl, h⟩
    exact hψ (addChar_comp_eq_self_eq_zero T hfpf1 φ h)
  have h02 : ¬ (φ = ψ ∧ φ.compAddMonoidHom (T.comp T) = ψ) := by
    rintro ⟨rfl, h⟩
    exact hψ (addChar_comp_eq_self_eq_zero _ hTT φ h)
  have h12 : ¬ (φ.compAddMonoidHom T = ψ ∧ φ.compAddMonoidHom (T.comp T) = ψ) := by
    rintro ⟨h1, h2⟩
    rw [hcompT, h1] at h2
    exact hψ (addChar_comp_eq_self_eq_zero T hfpf1 ψ h2)
  by_cases hA : φ = ψ
  · have hB : ¬ φ.compAddMonoidHom T = ψ := fun h => h01 ⟨hA, h⟩
    have hC : ¬ φ.compAddMonoidHom (T.comp T) = ψ := fun h => h02 ⟨hA, h⟩
    rw [ite_eq_left hA, ite_eq_right hB, ite_eq_right hC, ite_eq_left (Or.inl hA)]
    ring
  · by_cases hB : φ.compAddMonoidHom T = ψ
    · have hC : ¬ φ.compAddMonoidHom (T.comp T) = ψ := fun h => h12 ⟨hB, h⟩
      rw [ite_eq_right hA, ite_eq_left hB, ite_eq_right hC, ite_eq_left (Or.inr (Or.inl hB))]
      ring
    · by_cases hC : φ.compAddMonoidHom (T.comp T) = ψ
      · rw [ite_eq_right hA, ite_eq_right hB, ite_eq_left hC,
          ite_eq_left (Or.inr (Or.inr hC))]
        ring
      · rw [ite_eq_right hA, ite_eq_right hB, ite_eq_right hC,
          ite_eq_right (by rintro (h | h | h) <;> contradiction)]
        ring

include e in
theorem homocyclicColumn_gram_orbit (hn : 1 ≤ n)
    (hNC : Subgroup.normalizer ((S : Subgroup G) : Set G) ≠
      Subgroup.centralizer ((S : Subgroup G) : Set G))
    (hprincipal : (basis.representation principal).character = 1)
    (ψ φ : AddChar (HomocyclicVector n) ℂ) (hψ : ψ ≠ 0) (hφ : φ ≠ 0) :
    ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        homocyclicColumn e basis ψ label * homocyclicColumn e basis φ label =
      3 + if HomocyclicOrbitRel e φ ψ then 1 else 0 := by
  obtain ⟨g₀, hg₀, hg₀C⟩ := exists_normalizer_not_centralizer (S : Subgroup G) hNC
  rw [homocyclicColumn_gram S e ideal basis principal hn hprincipal hg₀ hg₀C ψ φ hψ hφ,
    homocyclic_orbit_indicator S e hn hg₀ hg₀C ψ φ hψ]

omit [Fintype G] in
include e in
theorem exists_homocyclic_orbit_representatives :
    ∃ (ι : Type) (_ : Fintype ι) (ψ : ι → AddChar (HomocyclicVector n) ℂ),
      (∀ i, ψ i ≠ 0) ∧ (∀ i j, HomocyclicOrbitRel e (ψ i) (ψ j) → i = j) ∧
      (∀ φ, φ ≠ 0 → ∃ i, HomocyclicOrbitRel e (ψ i) φ) := by
  let X := {φ : AddChar (HomocyclicVector n) ℂ // φ ≠ 0}
  let r : Setoid X :=
    { r := fun a b => HomocyclicOrbitRel e a.1 b.1
      iseqv := ⟨fun a => homocyclicOrbitRel_refl e a.1,
        fun h => homocyclicOrbitRel_symm e h, fun h1 h2 => homocyclicOrbitRel_trans e h1 h2⟩ }
  refine ⟨Quotient r, inferInstance, fun q => q.out.1, fun q => q.out.2, ?_, ?_⟩
  · intro q q' h
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    exact Quotient.sound h
  · intro φ hφ
    refine ⟨Quotient.mk r ⟨φ, hφ⟩, ?_⟩
    exact Quotient.mk_out (s := r) (⟨φ, hφ⟩ : X)

omit [Fintype G] in
include e in
theorem homocyclic_orbit_representatives_card [Finite G] (hn : 1 ≤ n)
    (hNC : Subgroup.normalizer ((S : Subgroup G) : Set G) ≠
      Subgroup.centralizer ((S : Subgroup G) : Set G))
    {ι : Type*} [Fintype ι] (ψ : ι → AddChar (HomocyclicVector n) ℂ) (hψ0 : ∀ i, ψ i ≠ 0)
    (hpair : ∀ i j, HomocyclicOrbitRel e (ψ i) (ψ j) → i = j)
    (hcover : ∀ φ, φ ≠ 0 → ∃ i, HomocyclicOrbitRel e (ψ i) φ) :
    3 * Fintype.card ι + 1 = Nat.card S := by
  obtain ⟨g₀, hg₀, hg₀C⟩ := exists_normalizer_not_centralizer (S : Subgroup G) hNC
  obtain ⟨hfpf1, hfpf2, hcube⟩ := homocyclicConj_fixed_point_free S e hn hg₀ hg₀C
  have hT : Function.Surjective (homocyclicConj e g₀ hg₀) := homocyclicConj_surjective S e hg₀
  set T := homocyclicConj e g₀ hg₀
  have hiterT : ∀ k : ℕ, Function.Surjective (⇑T)^[k] := fun k => hT.iterate k
  have hrelpow : ∀ (φ : AddChar (HomocyclicVector n) ℂ) (k : ℕ),
      HomocyclicOrbitRel e φ (addCharIter T φ k) := by
    intro φ k
    induction k with
    | zero => exact homocyclicOrbitRel_refl e φ
    | succ k ih => exact homocyclicOrbitRel_trans e ih ⟨g₀, hg₀, rfl⟩
  have hne0 : ∀ (φ : AddChar (HomocyclicVector n) ℂ), φ ≠ 0 → ∀ k, addCharIter T φ k ≠ 0 := by
    intro φ hφ k h0
    apply hφ
    ext w
    obtain ⟨u, rfl⟩ := hiterT k w
    have := congrArg (fun χ : AddChar (HomocyclicVector n) ℂ => χ u) h0
    simpa [addCharIter_apply] using this
  have hthree : ∀ φ : AddChar (HomocyclicVector n) ℂ, addCharIter T φ 3 = φ := by
    intro φ
    ext v
    rw [addCharIter_apply]
    exact congrArg φ (hcube v)
  have hfix1 : ∀ χ : AddChar (HomocyclicVector n) ℂ, χ ≠ 0 → addCharIter T χ 1 ≠ χ := by
    intro χ hχ h
    apply hχ
    exact addChar_comp_eq_self_eq_zero T hfpf1 χ h
  have hfix2 : ∀ χ : AddChar (HomocyclicVector n) ℂ, χ ≠ 0 → addCharIter T χ 2 ≠ χ := by
    intro χ hχ h
    apply hχ
    apply addChar_comp_eq_self_eq_zero (T.comp T) (fun v hv => hfpf2 v hv) χ
    have hcomp : χ.compAddMonoidHom (T.comp T) = addCharIter T χ 2 := by
      ext v
      rfl
    rw [hcomp]
    exact h
  have hexp : ∀ (χ : AddChar (HomocyclicVector n) ℂ), χ ≠ 0 → ∀ k l : ℕ, k < l → l < 3 →
      addCharIter T χ k ≠ addCharIter T χ l := by
    intro χ hχ k l hkl hl h
    have h' := congrArg (fun φ => addCharIter T φ (3 - k)) h
    simp only [addCharIter_add] at h'
    rw [show k + (3 - k) = 3 by omega, hthree,
      show l + (3 - k) = 3 + (l - k) by omega, ← addCharIter_add, hthree] at h'
    have hd : l - k = 1 ∨ l - k = 2 := by omega
    rcases hd with hd | hd
    · rw [hd] at h'
      exact hfix1 χ hχ h'.symm
    · rw [hd] at h'
      exact hfix2 χ hχ h'.symm
  let X := {φ : AddChar (HomocyclicVector n) ℂ // φ ≠ 0}
  let F : ι × Fin 3 → X := fun p => ⟨addCharIter T (ψ p.1) (p.2 : ℕ), hne0 _ (hψ0 p.1) _⟩
  have hbij : Function.Bijective F := by
    constructor
    · rintro ⟨i, k⟩ ⟨j, l⟩ hkl
      have hval : addCharIter T (ψ i) (k : ℕ) = addCharIter T (ψ j) (l : ℕ) :=
        congrArg Subtype.val hkl
      have hij : i = j := by
        apply hpair
        have h1 := hrelpow (ψ i) k
        have h2 := hrelpow (ψ j) l
        rw [hval] at h1
        exact homocyclicOrbitRel_trans e h1 (homocyclicOrbitRel_symm e h2)
      subst hij
      have hkl' : (k : ℕ) = l := by
        by_contra hne
        rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
        · exact hexp (ψ i) (hψ0 i) k l hlt l.isLt hval
        · exact hexp (ψ i) (hψ0 i) l k hlt k.isLt hval.symm
      rw [Fin.ext hkl']
    · rintro ⟨φ, hφ⟩
      obtain ⟨i, hi⟩ := hcover φ hφ
      rw [homocyclicOrbitRel_iff S e hn hg₀ hg₀C] at hi
      rcases hi with rfl | rfl | rfl
      · exact ⟨(i, 0), rfl⟩
      · exact ⟨(i, 1), rfl⟩
      · refine ⟨(i, 2), Subtype.ext ?_⟩
        ext v
        rfl
  have hcard := Fintype.card_of_bijective hbij
  rw [Fintype.card_prod, Fintype.card_fin] at hcard
  have hX : Fintype.card X = Fintype.card (AddChar (HomocyclicVector n) ℂ) - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  rw [hX, AddChar.card_eq] at hcard
  rw [card_homocyclic_eq_card_vector e]
  have hpos : 0 < Fintype.card (HomocyclicVector n) := Fintype.card_pos
  omega

theorem homocyclic_principal_restriction_column_gram (hn : 1 ≤ n)
    (hNC : Subgroup.normalizer ((S : Subgroup G) : Set G) ≠
      Subgroup.centralizer ((S : Subgroup G) : Set G))
    (hprincipal : (basis.representation principal).character = 1) :
    Nat.card (Subgroup.normalizer ((S : Subgroup G) : Set G) ⧸
      (Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
        (Subgroup.normalizer ((S : Subgroup G) : Set G))) = 3 ∧
    (∀ g (hg : g ∈ Subgroup.normalizer ((S : Subgroup G) : Set G)),
      g ∉ Subgroup.centralizer ((S : Subgroup G) : Set G) →
        ∀ ψ : AddChar (HomocyclicVector n) ℂ, ψ ≠ 0 →
          ψ.compAddMonoidHom (homocyclicConj e g hg) ≠ ψ) ∧
    (∀ ψ label, ∃ z : ℤ, homocyclicColumn e basis ψ label = z) ∧
    (∀ ψ : AddChar (HomocyclicVector n) ℂ, ψ ≠ 0 → homocyclicColumn e basis ψ principal = -1) ∧
    (∀ ψ : AddChar (HomocyclicVector n) ℂ,
      ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        homocyclicColumn e basis ψ label * (basis.representation label).character 1 = 0) ∧
    (∀ ψ φ : AddChar (HomocyclicVector n) ℂ, ψ ≠ 0 → φ ≠ 0 →
      ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        homocyclicColumn e basis ψ label * homocyclicColumn e basis φ label =
          3 + if HomocyclicOrbitRel e φ ψ then 1 else 0) ∧
    (∀ (r : ℕ) (ψ : Fin r → AddChar (HomocyclicVector n) ℂ), (∀ i, ψ i ≠ 0) →
      (∀ i j, HomocyclicOrbitRel e (ψ i) (ψ j) → i = j) →
      (∀ φ, φ ≠ 0 → ∃ i, HomocyclicOrbitRel e (ψ i) φ) →
      r = (Nat.card S - 1) / 3 ∧
      ∀ i j, ∑ label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        homocyclicColumn e basis (ψ i) label * homocyclicColumn e basis (ψ j) label =
          3 + if i = j then 1 else 0) := by
  obtain ⟨g₀, hg₀, hg₀C⟩ := exists_normalizer_not_centralizer (S : Subgroup G) hNC
  have hgram := homocyclicColumn_gram_orbit S e ideal basis principal hn hNC hprincipal
  refine ⟨homocyclic_card_normalizer_quotient S e hn hg₀ hg₀C, ?_,
    homocyclicColumn_integer e basis, homocyclicColumn_principal e basis principal hprincipal,
    homocyclicColumn_degree_sum S e ideal basis principal, hgram, ?_⟩
  · intro g hg hgC ψ hψ h
    have hfpf := (homocyclicConj_fixed_point_free S e hn hg hgC).1
    exact hψ (addChar_comp_eq_self_eq_zero _ hfpf ψ h)
  · intro r ψ hψ0 hpair hcover
    refine ⟨?_, ?_⟩
    · have h := homocyclic_orbit_representatives_card S e hn hNC ψ hψ0 hpair hcover
      rw [Fintype.card_fin] at h
      omega
    · intro i j
      rw [hgram (ψ i) (ψ j) (hψ0 i) (hψ0 j)]
      by_cases hij : i = j
      · subst hij
        rw [ite_eq_left (homocyclicOrbitRel_refl e _), ite_eq_left rfl]
      · rw [ite_eq_right (fun h => hij (hpair j i h).symm), ite_eq_right hij]

end Node

end CFSG.RankTwoShapes
