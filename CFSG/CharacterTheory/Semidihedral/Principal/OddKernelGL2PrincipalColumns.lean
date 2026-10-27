module

public import CFSG.CharacterTheory.Semidihedral.Principal.GL2ThreePrincipalBlock
public import CFSG.CharacterTheory.Semidihedral.Principal.SectionPrincipalTransport
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.PrincipalSectionKernel
public import CFSG.CharacterTheory.TwoRankLowerBound.CentralInvolutionSectionMask
public import CFSG.CharacterTheory.Semidihedral.Principal.GL2ColumnsSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.NormalKernelBlockInflation

public section

open scoped Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers GL2ThreeCharacters

namespace GL2PrincipalColumns

theorem block_combinatorics (E : Fin 8 → Fin 8 → Prop) (hsymm : ∀ j k, E j k → E k j)
    (htrans : ∀ i j k, E i j → E j k → E i k) (hrefl : ∀ k, E k k)
    (f : Fin 8 → ℂ) (hf : ∀ k, f k ≠ 0) (hf0 : f 0 = 1) {ε ε₁ ε₂ ε₃ : ℂ} (hε : ε ≠ 0)
    (hε₁ : ε₁ ≠ 0) (hε₂ : ε₂ ≠ 0) (hε₃ : ε₃ ≠ 0) (I : Fin 8 → Fin 8 → ℂ)
    (hI1 : ∀ k m, E k m → I k m = f k) (hI0 : ∀ k m, ¬ E k m → I k m = 0)
    (R1 : ∀ m, I 0 m + ε * (I 1 m - I 2 m) = 0) (R2 : ∀ m, ε * (I 1 m - I 3 m) = 0)
    (R3 : ∀ m, ε * (I 3 m - I 4 m) = 0) (R4 : ∀ m, ε * I 2 m + ε₁ * I 5 m + ε₂ * I 6 m = 0)
    (R5 : ∀ m, ε * I 1 m + ε₁ * I 5 m + ε₃ * I 7 m = 0) :
    ∀ k, E k 0 := by
  have hout : ∀ j k m, E j k → ¬ E m k → ¬ E j m := fun j k m hjk hmk hjm =>
    hmk (htrans m j k (hsymm j m hjm) hjk)
  have h12 : E 1 0 ∧ E 2 0 := by
    by_cases h1 : E 1 0 <;> by_cases h2 : E 2 0
    · exact ⟨h1, h2⟩
    · exfalso
      have e := R1 2
      rw [hI0 0 2 (fun h => h2 (hsymm 0 2 h)), hI0 1 2 (hout 1 0 2 h1 h2), hI1 2 2 (hrefl 2)]
        at e
      have : ε * f 2 = 0 := by linear_combination -e
      exact mul_ne_zero hε (hf 2) this
    · exfalso
      have e := R1 1
      rw [hI0 0 1 (fun h => h1 (hsymm 0 1 h)), hI1 1 1 (hrefl 1), hI0 2 1 (hout 2 0 1 h2 h1)]
        at e
      have : ε * f 1 = 0 := by linear_combination e
      exact mul_ne_zero hε (hf 1) this
    · exfalso
      have e := R1 0
      rw [hI1 0 0 (hrefl 0), hI0 1 0 h1, hI0 2 0 h2, hf0] at e
      norm_num at e
  obtain ⟨h1, h2⟩ := h12
  have h3 : E 3 0 := by
    by_contra h3
    have e := R2 0
    rw [hI1 1 0 h1, hI0 3 0 h3] at e
    have : ε * f 1 = 0 := by linear_combination e
    exact mul_ne_zero hε (hf 1) this
  have h4 : E 4 0 := by
    by_contra h4
    have e := R3 0
    rw [hI1 3 0 h3, hI0 4 0 h4] at e
    have : ε * f 3 = 0 := by linear_combination e
    exact mul_ne_zero hε (hf 3) this
  have h56 : E 5 0 ∧ E 6 0 := by
    by_cases h5 : E 5 0 <;> by_cases h6 : E 6 0
    · exact ⟨h5, h6⟩
    · exfalso
      have e := R4 6
      rw [hI0 2 6 (hout 2 0 6 h2 h6), hI0 5 6 (hout 5 0 6 h5 h6), hI1 6 6 (hrefl 6)] at e
      have : ε₂ * f 6 = 0 := by linear_combination e
      exact mul_ne_zero hε₂ (hf 6) this
    · exfalso
      have e := R4 5
      rw [hI0 2 5 (hout 2 0 5 h2 h5), hI1 5 5 (hrefl 5), hI0 6 5 (hout 6 0 5 h6 h5)] at e
      have : ε₁ * f 5 = 0 := by linear_combination e
      exact mul_ne_zero hε₁ (hf 5) this
    · exfalso
      have e := R4 0
      rw [hI1 2 0 h2, hI0 5 0 h5, hI0 6 0 h6] at e
      have : ε * f 2 = 0 := by linear_combination e
      exact mul_ne_zero hε (hf 2) this
  obtain ⟨h5, h6⟩ := h56
  have h7 : E 7 0 := by
    by_contra h7
    have e := R5 7
    rw [hI0 1 7 (hout 1 0 7 h1 h7), hI0 5 7 (hout 5 0 7 h5 h7), hI1 7 7 (hrefl 7)] at e
    have : ε₃ * f 7 = 0 := by linear_combination e
    exact mul_ne_zero hε₃ (hf 7) this
  intro k
  fin_cases k
  exacts [hrefl 0, h1, h2, h3, h4, h5, h6, h7]

variable {G : Type} [Group G] [Fintype G]

theorem blockProjection_one_eq_zero (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (m : basis.index) (f : G → ℂ)
    (hf : ∀ g : G, Odd (orderOf g) → f g = 0) :
    characterSubsetProjection basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) m) f 1 = 0 := by
  have hmask : characterFunctionMask {g : G | Odd (orderOf g)} f = 0 := by
    funext g
    simp only [characterFunctionMask, Pi.zero_apply]
    split_ifs with hg
    · exact hf g hg
    · rfl
  have h := coefficientBlock_section_mask_commute basis ideal 2 m {g : G | Odd (orderOf g)}
    oddOrderElements_primeSectionUnion f
  rw [hmask, map_zero] at h
  have h1 := congrFun h 1
  simp only [characterFunctionMask, Pi.zero_apply, Set.mem_ofPred_eq, orderOf_one, odd_one,
    ite_true] at h1
  exact h1.symm

theorem principal_block_centralizer_iff (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] {t : G}
    (π : Subgroup.centralizer ({t} : Set G) →* G23) (hπ : Function.Surjective π)
    (hN : Odd (Nat.card π.ker)) {a p b : G23} (ha : orderOf a = 8) (hp : orderOf p = 3)
    (hb : orderOf b = 2) (hbz : b ∉ Subgroup.center G23)
    (basisC : FiniteIrreducibleCharacterBasis (Subgroup.centralizer ({t} : Set G)))
    (principalC : basisC.index) (hprincipalC : (basisC.representation principalC).character = 1)
    (basisH : FiniteIrreducibleCharacterBasis G23) (principalH : basisH.index)
    (hprincipalH : (basisH.representation principalH).character = 1) (lab : basisC.index) :
    lab ∈ coefficientBlock basisC (localizedComplexIntegerRing ideal) principalC ↔
      ∃ θ : basisH.index,
        (basisC.representation lab).character = (basisH.representation θ).character ∘ π := by
  have hN2 : ¬ 2 ∣ Nat.card π.ker := fun h =>
    (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h)
  have h := (normal_prime_kernel_principal_block_inflation_of_surjective π hπ basisC ideal 2 hN2
    basisH principalC hprincipalC principalH hprincipalH).1 lab
  have hall := (GL2_three_all_ordinary_characters_principal_two_block basisH ideal principalH
    hprincipalH a p b ha hp hb hbz).1
  rw [h]
  constructor
  · rintro ⟨θ, -, hθ⟩
    exact ⟨θ, hθ⟩
  · rintro ⟨θ, hθ⟩
    exact ⟨θ, by rw [hall]; exact Finset.mem_univ _, hθ⟩

theorem principal_section_formula (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (basis : FiniteIrreducibleCharacterBasis G)
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    {t : G} (π : Subgroup.centralizer ({t} : Set G) →* G23) (hπ : Function.Surjective π)
    (hN : Odd (Nat.card π.ker)) {a p b : G23} (ha : orderOf a = 8) (hp : orderOf p = 3)
    (hb : orderOf b = 2) (hbz : b ∉ Subgroup.center G23) (j : basis.index)
    (hj : j ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal) :
    ∃ F : G23 → ℂ, (∀ x : Subgroup.centralizer ({t} : Set G),
        (x : G) ∈ centralInvolutionSection t → (basis.representation j).character x = F (π x)) ∧
      ∃ X Y : ℤ, F (-1) = X + 2 * Y ∧ F (-1 * p) = X - Y := by
  obtain ⟨basisC⟩ :=
    finiteIrreducibleCharacterBasis_exists (G := Subgroup.centralizer ({t} : Set G))
  obtain ⟨principalC, hprincipalC⟩ := finiteIrreducibleCharacterBasis_exists_principal_label basisC
  obtain ⟨basisH⟩ := finiteIrreducibleCharacterBasis_exists (G := G23)
  obtain ⟨principalH, hprincipalH⟩ := finiteIrreducibleCharacterBasis_exists_principal_label basisH
  have hiff := principal_block_centralizer_iff ideal π hπ hN ha hp hb hbz basisC principalC
    hprincipalC basisH principalH hprincipalH
  have : Nonempty basisH.index := ⟨principalH⟩
  choose! θ hθ using fun lab
    (hlab : lab ∈ coefficientBlock basisC (localizedComplexIntegerRing ideal) principalC) =>
    (hiff lab).mp hlab
  let res : FiniteComplexRepresentation (Subgroup.centralizer ({t} : Set G)) :=
    inflatedFiniteComplexRepresentation (Subgroup.centralizer ({t} : Set G)).subtype
      (basis.representation j)
  choose m hm using characterPairing_basis_natural basisC res
  refine ⟨fun h => ∑ lab ∈ coefficientBlock basisC (localizedComplexIntegerRing ideal) principalC,
    (m lab : ℂ) * (basisH.representation (θ lab)).character h, ?_, ?_⟩
  · intro x hx
    have h1 := characterSubsetProjection_character basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) principal) j hj
    have h2 := principalProjection_eq_on_centralInvolutionSection ideal t basis principal
      hprincipal basisC principalC hprincipalC (basis.representation j).character
      (fun g c => Representation.char_conj _ g c) x hx
    rw [h1] at h2
    rw [h2]
    show (∑ lab ∈ coefficientBlock basisC (localizedComplexIntegerRing ideal) principalC,
      characterPairing (fun y : Subgroup.centralizer ({t} : Set G) =>
        (basis.representation j).character y) (basisC.representation lab).character •
        (basisC.representation lab).character) x = _
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun lab hlab => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    have hres : res.character =
        fun y : Subgroup.centralizer ({t} : Set G) => (basis.representation j).character y := rfl
    rw [← hres, hm lab, hθ lab hlab]
    rfl
  · choose x y hxy using GL2Columns.label_coords basisH ha hp hb hbz
    refine ⟨∑ lab ∈ coefficientBlock basisC (localizedComplexIntegerRing ideal) principalC,
      (m lab : ℤ) * x (θ lab),
      ∑ lab ∈ coefficientBlock basisC (localizedComplexIntegerRing ideal) principalC,
      (m lab : ℤ) * y (θ lab), ?_, ?_⟩
    · push_cast
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun lab _ => by rw [(hxy _).1]; ring
    · push_cast
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun lab _ => by rw [(hxy _).2]; ring

theorem principal_section_kernel_centralizer (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) {t : G} (ht : orderOf t = 2)
    (basisC : FiniteIrreducibleCharacterBasis (Subgroup.centralizer ({t} : Set G)))
    (principalC : basisC.index) (hprincipalC : (basisC.representation principalC).character = 1)
    (x y : Subgroup.centralizer ({t} : Set G))
    (hx : ∃ r : Subgroup.centralizer ({t} : Set G), (x : G) = t * r ∧ Odd (orderOf r))
    (hy : ∃ r : Subgroup.centralizer ({t} : Set G), (y : G) = t * r ∧ Odd (orderOf r)) :
    ∑ j ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation j).character x *
          starRingEnd ℂ ((basis.representation j).character y) =
      ∑ lab ∈ coefficientBlock basisC (localizedComplexIntegerRing ideal) principalC,
        (basisC.representation lab).character x *
          starRingEnd ℂ ((basisC.representation lab).character y) := by
  have hK : Subgroup.centralizer ({t} : Set G) =
      Subgroup.centralizer (Subgroup.zpowers t : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  suffices key : ∀ K : Subgroup G, K = Subgroup.centralizer (Subgroup.zpowers t : Set G) →
      ∀ (localBasis : FiniteIrreducibleCharacterBasis K) (localPrincipal : localBasis.index),
      (localBasis.representation localPrincipal).character = 1 → ∀ x y : K,
      (∃ r : K, (x : G) = t * r ∧ Odd (orderOf r)) →
      (∃ r : K, (y : G) = t * r ∧ Odd (orderOf r)) →
      ∑ j ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
          (basis.representation j).character x *
            starRingEnd ℂ ((basis.representation j).character y) =
        ∑ lab ∈ coefficientBlock localBasis (localizedComplexIntegerRing ideal) localPrincipal,
          (localBasis.representation lab).character x *
            starRingEnd ℂ ((localBasis.representation lab).character y) from
    key _ hK basisC principalC hprincipalC x y hx hy
  intro K hK'
  subst hK'
  intro localBasis localPrincipal hlocalPrincipal x y hx hy
  obtain ⟨rx, hrx, hrxo⟩ := hx
  obtain ⟨ry, hry, hryo⟩ := hy
  exact CFSG.LyonsUnitaryFour.brauer_principal_section_kernel basis ideal 2 principal hprincipal
    t 1 (by rw [ht]; norm_num) localBasis localPrincipal hlocalPrincipal x y
    ⟨rx, Subtype.ext hrx, Nat.coprime_two_left.mpr hrxo⟩
    ⟨ry, Subtype.ext hry, Nat.coprime_two_left.mpr hryo⟩

theorem principal_column_kernel (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (basis : FiniteIrreducibleCharacterBasis G)
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    {t : G} (ht : orderOf t = 2) (π : Subgroup.centralizer ({t} : Set G) →* G23)
    (hπ : Function.Surjective π) (hN : Odd (Nat.card π.ker)) {a p b : G23}
    (ha : orderOf a = 8) (hp : orderOf p = 3) (hb : orderOf b = 2)
    (hbz : b ∉ Subgroup.center G23) (x y : Subgroup.centralizer ({t} : Set G))
    (hx : ∃ r : Subgroup.centralizer ({t} : Set G), (x : G) = t * r ∧ Odd (orderOf r))
    (hy : ∃ r : Subgroup.centralizer ({t} : Set G), (y : G) = t * r ∧ Odd (orderOf r)) :
    ∑ j ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation j).character x *
          starRingEnd ℂ ((basis.representation j).character y) =
      CFSG.Wreathed.conjugatorCount (π y) (π x) := by
  obtain ⟨basisC⟩ :=
    finiteIrreducibleCharacterBasis_exists (G := Subgroup.centralizer ({t} : Set G))
  obtain ⟨principalC, hprincipalC⟩ := finiteIrreducibleCharacterBasis_exists_principal_label basisC
  obtain ⟨basisH⟩ := finiteIrreducibleCharacterBasis_exists (G := G23)
  obtain ⟨principalH, hprincipalH⟩ := finiteIrreducibleCharacterBasis_exists_principal_label basisH
  have hiff := principal_block_centralizer_iff ideal π hπ hN ha hp hb hbz basisC principalC
    hprincipalC basisH principalH hprincipalH
  have : Nonempty basisH.index := ⟨principalH⟩
  choose! θ hθ using fun lab
    (hlab : lab ∈ coefficientBlock basisC (localizedComplexIntegerRing ideal) principalC) =>
    (hiff lab).mp hlab
  rw [principal_section_kernel_centralizer ideal basis principal hprincipal ht basisC principalC
    hprincipalC x y hx hy, ← CFSG.Wreathed.complete_complex_character_column_sum basisH]
  apply Finset.sum_nbij θ
  · intro lab _
    exact Finset.mem_univ _
  · intro a' ha' b' hb' hab
    apply basisC.distinct
    show (basisC.representation a').character = (basisC.representation b').character
    rw [hθ a' ha', hθ b' hb', hab]
  · intro θ0 _
    obtain ⟨lab, hlab⟩ := exists_inflated_label π hπ basisC basisH θ0
    have hmem : lab ∈ coefficientBlock basisC (localizedComplexIntegerRing ideal) principalC :=
      (hiff lab).mpr ⟨θ0, hlab⟩
    refine ⟨lab, hmem, ?_⟩
    apply basisH.distinct
    show (basisH.representation (θ lab)).character = (basisH.representation θ0).character
    apply hπ.injective_comp_right
    show (basisH.representation (θ lab)).character ∘ π =
      (basisH.representation θ0).character ∘ π
    rw [← hθ lab hmem, hlab]
  · intro lab hlab
    rw [hθ lab hlab]
    rfl

theorem GL2_conjugatorCounts {a p b : G23} (ha : orderOf a = 8) (hp : orderOf p = 3)
    (hb : orderOf b = 2) (hbz : b ∉ Subgroup.center G23) :
    CFSG.Wreathed.conjugatorCount (-1 : G23) (-1) = 48 ∧
      CFSG.Wreathed.conjugatorCount (-1 * p : G23) (-1 * p) = 6 ∧
      CFSG.Wreathed.conjugatorCount (-1 * p : G23) (-1) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · have htop : Subgroup.centralizer ({-1} : Set G23) = ⊤ := by
      ext g
      simp only [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_top, iff_true]
      exact GL2OddKernel.neg_one_mul_comm g
    rw [CFSG.Wreathed.conjugatorCount_self, htop, Subgroup.card_top, card_G23]
    norm_num
  · rw [CFSG.Wreathed.conjugatorCount_self, GL2Columns.card_centralizer_neg_one_mul ha hp hb hbz]
    norm_num
  · unfold CFSG.Wreathed.conjugatorCount
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [ite_eq_right]
    intro hg
    have h1 : g * p * g⁻¹ = 1 := by
      have e : g * (-1 * p) * g⁻¹ = -1 * (g * p * g⁻¹) := by
        rw [← mul_assoc g, GL2OddKernel.neg_one_mul_comm g, mul_assoc, mul_assoc, mul_assoc]
      rw [e] at hg
      have := congrArg (fun x => (-1 : G23)⁻¹ * x) hg
      simpa using this
    rw [conj_eq_one_iff] at h1
    rw [h1, orderOf_one] at hp
    norm_num at hp

end GL2PrincipalColumns

theorem odd_kernel_GL2_principal_character_columns_and_exhaustion {G : Type} [Group G]
    [Fintype G] (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (basis : FiniteIrreducibleCharacterBasis G)
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (t : G) (ht : orderOf t = 2)
    (π : Subgroup.centralizer ({t} : Set G) →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (hπ : Function.Surjective π) (hN : Odd (Nat.card π.ker))
    (hπt : π ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ = -1)
    (a p b : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) (ha : orderOf a = 8)
    (hp : orderOf p = 3) (hb : orderOf b = 2)
    (hbz : b ∉ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)))
    (φ : Fin 8 → Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) → ℂ)
    (hφirr : ∀ i, φ i ∈ CFSG.BlocksIrr (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)))
    (hφ : let ξ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 8)
      let ω : ℂ := ξ + ξ ^ 3
      let rep : Fin 8 → Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
        ![1, -1, a ^ 2, p, -1 * p, b, a, a⁻¹]
      let table : Fin 8 → Fin 8 → ℂ := ![![1, 1, 1, 1, 1, 1, 1, 1],
        ![1, 1, 1, 1, 1, -1, -1, -1], ![2, 2, 2, -1, -1, 0, 0, 0], ![3, 3, -1, 0, 0, -1, 1, 1],
        ![3, 3, -1, 0, 0, 1, -1, -1], ![4, -4, 0, 1, -1, 0, 0, 0], ![2, -2, 0, -1, 1, 0, ω, -ω],
        ![2, -2, 0, -1, 1, 0, -ω, ω]]
      ∀ i j, φ i (rep j) = table i j) :
    let C := Subgroup.centralizer ({t} : Set G)
    let N := π.ker
    let Φ : Fin 5 → Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) → ℂ :=
      ![φ 0 + φ 2 - φ 4, φ 2 - φ 6, φ 6 - φ 7, φ 1 + φ 4 - φ 5, φ 1 + φ 2 - φ 3]
    let β : Fin 5 → G → ℂ := fun i => inducedFunction C (fun c => Φ i (π c))
    let B₀ : Set (G → ℂ) := (fun l => (basis.representation l).character) ''
      (coefficientBlock basis (localizedComplexIntegerRing ideal) principal : Set basis.index)
    let identities : CFSG.BlocksIrr G → CFSG.BlocksIrr G → CFSG.BlocksIrr G →
        CFSG.BlocksIrr G → CFSG.BlocksIrr G → CFSG.BlocksIrr G → CFSG.BlocksIrr G →
        ℤ → ℤ → ℤ → ℤ → Prop := fun χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ ε ε₁ ε₂ ε₃ =>
      [χ₁, χ₂, χ₃, χ₄, χ₅, χ₆, χ₇].Nodup ∧
      (χ₁ : G → ℂ) ≠ 1 ∧ (χ₂ : G → ℂ) ≠ 1 ∧ (χ₃ : G → ℂ) ≠ 1 ∧ (χ₄ : G → ℂ) ≠ 1 ∧
      (χ₅ : G → ℂ) ≠ 1 ∧ (χ₆ : G → ℂ) ≠ 1 ∧ (χ₇ : G → ℂ) ≠ 1 ∧
      (ε = 1 ∨ ε = -1) ∧ (ε₁ = 1 ∨ ε₁ = -1) ∧ (ε₂ = 1 ∨ ε₂ = -1) ∧ (ε₃ = 1 ∨ ε₃ = -1) ∧
      β 0 = 1 + (ε : ℂ) • ((χ₁ : G → ℂ) - χ₂) ∧
      β 1 = (ε : ℂ) • ((χ₁ : G → ℂ) - χ₃) ∧
      β 2 = (ε : ℂ) • ((χ₃ : G → ℂ) - χ₄) ∧
      β 3 = (ε : ℂ) • (χ₂ : G → ℂ) + (ε₁ : ℂ) • (χ₅ : G → ℂ) + (ε₂ : ℂ) • (χ₆ : G → ℂ) ∧
      β 4 = (ε : ℂ) • (χ₁ : G → ℂ) + (ε₁ : ℂ) • (χ₅ : G → ℂ) + (ε₃ : ℂ) • (χ₇ : G → ℂ)
    (∃ (χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ : CFSG.BlocksIrr G) (ε ε₁ ε₂ ε₃ : ℤ),
      identities χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ ε ε₁ ε₂ ε₃) ∧
    ∀ (χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ : CFSG.BlocksIrr G) (ε ε₁ ε₂ ε₃ : ℤ),
      identities χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ ε ε₁ ε₂ ε₃ →
      ((χ₁ : G → ℂ) ∈ B₀ ∧ (χ₂ : G → ℂ) ∈ B₀ ∧ (χ₃ : G → ℂ) ∈ B₀ ∧ (χ₄ : G → ℂ) ∈ B₀ ∧
        (χ₅ : G → ℂ) ∈ B₀ ∧ (χ₆ : G → ℂ) ∈ B₀ ∧ (χ₇ : G → ℂ) ∈ B₀) ∧
      (∀ q : C, π q = p → Odd (orderOf q) ∧ ∀ n : N,
        ![(χ₁ : G → ℂ) (t * ((n : C) : G)), (χ₂ : G → ℂ) (t * ((n : C) : G)),
            (χ₃ : G → ℂ) (t * ((n : C) : G)), (χ₄ : G → ℂ) (t * ((n : C) : G)),
            (χ₅ : G → ℂ) (t * ((n : C) : G)), (χ₆ : G → ℂ) (t * ((n : C) : G)),
            (χ₇ : G → ℂ) (t * ((n : C) : G))] =
          ![2 * (ε : ℂ), 3 * ε, -2 * ε, -2 * ε, (ε₁ : ℂ), 4 * ε₂, -3 * ε₃] ∧
        ![(χ₁ : G → ℂ) (t * (q : G) * ((n : C) : G)), (χ₂ : G → ℂ) (t * (q : G) * ((n : C) : G)),
            (χ₃ : G → ℂ) (t * (q : G) * ((n : C) : G)),
            (χ₄ : G → ℂ) (t * (q : G) * ((n : C) : G)),
            (χ₅ : G → ℂ) (t * (q : G) * ((n : C) : G)),
            (χ₆ : G → ℂ) (t * (q : G) * ((n : C) : G)),
            (χ₇ : G → ℂ) (t * (q : G) * ((n : C) : G))] =
          ![-(ε : ℂ), 0, ε, ε, (ε₁ : ℂ), ε₂, 0]) ∧
      (∀ ψ ∈ B₀, ψ ≠ 1 → ψ ≠ (χ₁ : G → ℂ) → ψ ≠ (χ₂ : G → ℂ) → ψ ≠ (χ₃ : G → ℂ) →
        ψ ≠ (χ₄ : G → ℂ) → ψ ≠ (χ₅ : G → ℂ) → ψ ≠ (χ₆ : G → ℂ) → ψ ≠ (χ₇ : G → ℂ) →
        ∀ q : C, π q = p → ∀ n : N,
          ψ (t * ((n : C) : G)) = 0 ∧ ψ (t * (q : G) * ((n : C) : G)) = 0) ∧
      (Odd C.index → B₀ = {1, (χ₁ : G → ℂ), (χ₂ : G → ℂ), (χ₃ : G → ℂ), (χ₄ : G → ℂ),
        (χ₅ : G → ℂ), (χ₆ : G → ℂ), (χ₇ : G → ℂ)}) := by
  intro C N Φ β B₀ identities
  have hφ' : ∀ i j, φ i (GL2OddKernel.rep a p b j) =
      (tableA i j : ℂ) + (tableB i j : ℂ) * omega8 := by
    intro i j
    have h : φ i (GL2OddKernel.rep a p b j) = GL2OddKernel.charTable
        (Complex.exp (2 * Real.pi * Complex.I / 8) +
          Complex.exp (2 * Real.pi * Complex.I / 8) ^ 3) i j := hφ i j
    rw [h, GL2OddKernel.charTable_eq, GL2OddKernel.exp_eq_xi]
  have hπt' : π (GL2OddKernel.tC t) = -1 := hπt
  have hall := odd_kernel_GL2_centralizer_produces_actual_characters t ht π hπ hN hπt a p b ha
    hp hb hbz φ hφirr hφ
  refine ⟨?_, ?_⟩
  · obtain ⟨χ₁, χ₂, χ₃, χ₄, χ₅, χ₆, χ₇, ε, ε₁, ε₂, ε₃, hnd, h1, h2, h3, h4, h5, h6, h7, hε, hε₁,
      hε₂, hε₃, hβ0, hβ1, hβ2, hβ3, hβ4, -, -⟩ := hall
    exact ⟨χ₁, χ₂, χ₃, χ₄, χ₅, χ₆, χ₇, ε, ε₁, ε₂, ε₃, hnd, h1, h2, h3, h4, h5, h6, h7, hε,
      hε₁, hε₂, hε₃, hβ0, hβ1, hβ2, hβ3, hβ4⟩
  intro χ₁ χ₂ χ₃ χ₄ χ₅ χ₆ χ₇ ε ε₁ ε₂ ε₃ hsol
  obtain ⟨hnd, h1, h2, h3, h4, h5, h6, h7, hε, hε₁, hε₂, hε₃, hβ0, hβ1, hβ2, hβ3, hβ4⟩ := hsol
  have hβodd : ∀ i : Fin 5, ∀ g : G, Odd (orderOf g) → β i g = 0 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h,
      -⟩ := hall
    exact h
  let c : Fin 8 → G → ℂ := ![1, χ₁, χ₂, χ₃, χ₄, χ₅, χ₆, χ₇]
  have hcirr : ∀ k, c k ∈ CFSG.BlocksIrr G := by
    intro k
    fin_cases k
    exacts [principal_mem_blocksIrr G, χ₁.2, χ₂.2, χ₃.2, χ₄.2, χ₅.2, χ₆.2, χ₇.2]
  have hcinj : Function.Injective c :=
    GL2Columns.injective_of_nodup hnd h1 h2 h3 h4 h5 h6 h7
  choose l hl using fun k => GL2Columns.exists_label_of_mem_blocksIrr basis (hcirr k)
  have hlinj : Function.Injective l := fun i j h => hcinj (by rw [← hl i, ← hl j, h])
  have hl0 : l 0 = principal := by
    apply basis.distinct
    show (basis.representation (l 0)).character = (basis.representation principal).character
    rw [hl 0, hprincipal]
    rfl
  have hsign : ∀ s : ℤ, (s = 1 ∨ s = -1) → (s : ℂ) ≠ 0 := by
    rintro s (rfl | rfl) <;> norm_num
  have hmemB : ∀ k, l k ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal := by
    have key := GL2PrincipalColumns.block_combinatorics
      (fun j m => l j ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) (l m))
      (fun j k h => by
        show l k ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) (l j)
        rw [coefficientBlock_eq_of_mem basis _ h]
        exact coefficientBlock_self_mem basis _ (l k))
      (fun i j k hij hjk => by
        show l i ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) (l k)
        rw [← coefficientBlock_eq_of_mem basis _ hjk]
        exact hij)
      (fun k => coefficientBlock_self_mem basis _ (l k))
      (fun k => (basis.representation (l k)).character 1)
      (fun k => irreducible_character_degree_ne_zero (basis.representation (l k))
        (basis.irreducible (l k)))
      (by show (basis.representation (l 0)).character 1 = 1; rw [hl 0]; rfl)
      (hsign ε hε) (hsign ε₁ hε₁) (hsign ε₂ hε₂) (hsign ε₃ hε₃)
      (fun k m => characterSubsetProjection basis
        (coefficientBlock basis (localizedComplexIntegerRing ideal) (l m))
        (basis.representation (l k)).character 1)
      (fun k m h => by
        show characterSubsetProjection basis _ (basis.representation (l k)).character 1 = _
        rw [characterSubsetProjection_character basis _ (l k) h])
      (fun k m h => by
        show characterSubsetProjection basis _ (basis.representation (l k)).character 1 = 0
        rw [characterSubsetProjection_character_not_mem basis _ (l k) h]
        rfl)
      (fun m => by
        have h := GL2PrincipalColumns.blockProjection_one_eq_zero basis ideal (l m) (β 0)
          (hβodd 0)
        have e : β 0 = (basis.representation (l 0)).character + (ε : ℂ) •
            ((basis.representation (l 1)).character - (basis.representation (l 2)).character) := by
          rw [hl 0, hl 1, hl 2]
          exact hβ0
        rw [e, map_add, map_smul, map_sub] at h
        simpa only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] using h)
      (fun m => by
        have h := GL2PrincipalColumns.blockProjection_one_eq_zero basis ideal (l m) (β 1)
          (hβodd 1)
        have e : β 1 = (ε : ℂ) •
            ((basis.representation (l 1)).character - (basis.representation (l 3)).character) := by
          rw [hl 1, hl 3]
          exact hβ1
        rw [e, map_smul, map_sub] at h
        simpa only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] using h)
      (fun m => by
        have h := GL2PrincipalColumns.blockProjection_one_eq_zero basis ideal (l m) (β 2)
          (hβodd 2)
        have e : β 2 = (ε : ℂ) •
            ((basis.representation (l 3)).character - (basis.representation (l 4)).character) := by
          rw [hl 3, hl 4]
          exact hβ2
        rw [e, map_smul, map_sub] at h
        simpa only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] using h)
      (fun m => by
        have h := GL2PrincipalColumns.blockProjection_one_eq_zero basis ideal (l m) (β 3)
          (hβodd 3)
        have e : β 3 = (ε : ℂ) • (basis.representation (l 2)).character +
            (ε₁ : ℂ) • (basis.representation (l 5)).character +
            (ε₂ : ℂ) • (basis.representation (l 6)).character := by
          rw [hl 2, hl 5, hl 6]
          exact hβ3
        rw [e, map_add, map_add, map_smul, map_smul, map_smul] at h
        simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h)
      (fun m => by
        have h := GL2PrincipalColumns.blockProjection_one_eq_zero basis ideal (l m) (β 4)
          (hβodd 4)
        have e : β 4 = (ε : ℂ) • (basis.representation (l 1)).character +
            (ε₁ : ℂ) • (basis.representation (l 5)).character +
            (ε₃ : ℂ) • (basis.representation (l 7)).character := by
          rw [hl 1, hl 5, hl 7]
          exact hβ4
        rw [e, map_add, map_add, map_smul, map_smul, map_smul] at h
        simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h)
    intro k
    have hk := key k
    rw [hl0] at hk
    exact hk
  have hsec : ∀ j ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ∃ F : G23 → ℂ, (∀ x : Subgroup.centralizer ({t} : Set G),
        (x : G) ∈ centralInvolutionSection t → (basis.representation j).character x = F (π x)) ∧
      ∃ X Y : ℤ, F (-1) = X + 2 * Y ∧ F (-1 * p) = X - Y := fun j hj =>
    GL2PrincipalColumns.principal_section_formula ideal basis principal hprincipal π hπ hN ha hp
      hb hbz j hj
  choose! F hF X Y hXY using hsec
  have hNodd : ∀ n : N, Odd (orderOf ((n : C) : G)) := fun n => by
    rw [Subgroup.orderOf_coe]
    exact hN.of_dvd_nat (π.ker.orderOf_dvd_natCard n.2)
  have htn : ∀ j ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ∀ n : N, (basis.representation j).character (t * ((n : C) : G)) =
        (basis.representation j).character t := by
    intro j hj n
    have hx : ((GL2OddKernel.tC t * (n : C) : C) : G) ∈ centralInvolutionSection t :=
      GL2Columns.t_mul_mem_section ht (n : C).2 (hNodd n)
    have hπx : π (GL2OddKernel.tC t * (n : C)) = -1 := by
      rw [map_mul, hπt', MonoidHom.mem_ker.mp n.2, mul_one]
    have e1 := hF j hj _ hx
    have e2 := hF j hj (GL2OddKernel.tC t) (GL2Columns.self_mem_section ht)
    rw [hπx] at e1
    rw [hπt'] at e2
    exact e1.trans e2.symm
  have htqn : ∀ j ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ∀ q : C, π q = p → ∀ n : N,
        (basis.representation j).character (t * (q : G) * ((n : C) : G)) =
          (basis.representation j).character (t * (q : G)) := by
    intro j hj q hq n
    have hqn : Odd (orderOf (q * (n : C))) := GL2Columns.odd_orderOf_of_map_eq π hN hp _
      (by rw [map_mul, hq, MonoidHom.mem_ker.mp n.2, mul_one])
    have hqodd := GL2Columns.odd_orderOf_of_map_eq π hN hp q hq
    have hx : ((GL2OddKernel.tC t * (q * (n : C)) : C) : G) ∈ centralInvolutionSection t :=
      GL2Columns.t_mul_mem_section ht (q * (n : C)).2 (by rwa [Subgroup.orderOf_coe])
    have hx' : ((GL2OddKernel.tC t * q : C) : G) ∈ centralInvolutionSection t :=
      GL2Columns.t_mul_mem_section ht q.2 (by rwa [Subgroup.orderOf_coe])
    have hπx : π (GL2OddKernel.tC t * (q * (n : C))) = -1 * p := by
      rw [map_mul, map_mul, hπt', hq, MonoidHom.mem_ker.mp n.2, mul_one]
    have hπx' : π (GL2OddKernel.tC t * q) = -1 * p := by rw [map_mul, hπt', hq]
    have e1 := hF j hj _ hx
    have e2 := hF j hj _ hx'
    rw [hπx] at e1
    rw [hπx'] at e2
    calc (basis.representation j).character (t * (q : G) * ((n : C) : G))
        = (basis.representation j).character
            ((GL2OddKernel.tC t * (q * (n : C)) : C) : G) := by
          simp only [Subgroup.coe_mul, mul_assoc]
          rfl
      _ = (basis.representation j).character (t * (q : G)) := e1.trans e2.symm
  have hengine : ∀ q : C, π q = p →
      (c 1 t = 2 * ε ∧ c 1 (t * q) = -ε) ∧ (c 2 t = 3 * ε ∧ c 2 (t * q) = 0) ∧
      (c 3 t = -2 * ε ∧ c 3 (t * q) = ε) ∧ (c 4 t = -2 * ε ∧ c 4 (t * q) = ε) ∧
      (c 5 t = ε₁ ∧ c 5 (t * q) = ε₁) ∧ (c 6 t = 4 * ε₂ ∧ c 6 (t * q) = ε₂) ∧
      (c 7 t = -3 * ε₃ ∧ c 7 (t * q) = 0) ∧
      ∀ i ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (∀ k, l k ≠ i) → (basis.representation i).character t = 0 ∧
          (basis.representation i).character (t * q) = 0 := by
    intro q hq
    have hqodd := GL2Columns.odd_orderOf_of_map_eq π hN hp q hq
    have hx' : ((GL2OddKernel.tC t * q : C) : G) ∈ centralInvolutionSection t :=
      GL2Columns.t_mul_mem_section ht q.2 (by rwa [Subgroup.orderOf_coe])
    have hπx' : π (GL2OddKernel.tC t * q) = -1 * p := by rw [map_mul, hπt', hq]
    have hvt : ∀ i ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation i).character t = X i + 2 * Y i := by
      intro i hi
      have e := hF i hi (GL2OddKernel.tC t) (GL2Columns.self_mem_section ht)
      rw [hπt', (hXY i hi).1] at e
      exact e
    have hvq : ∀ i ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation i).character (t * q) = X i - Y i := by
      intro i hi
      have e := hF i hi _ hx'
      rw [hπx', (hXY i hi).2] at e
      exact e
    have hcoord : ∀ i ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        ∃ x y : ℤ, (basis.representation i).character t = x + 2 * y ∧
          (basis.representation i).character (t * q) = x - y :=
      fun i hi => ⟨X i, Y i, hvt i hi, hvq i hi⟩
    have hxt : ∃ r : C, ((GL2OddKernel.tC t : C) : G) = t * r ∧ Odd (orderOf r) :=
      ⟨1, by simp [GL2OddKernel.tC], by simp⟩
    have hxq : ∃ r : C, ((GL2OddKernel.tC t * q : C) : G) = t * r ∧ Odd (orderOf r) :=
      ⟨q, rfl, hqodd⟩
    obtain ⟨c11, c22, c21⟩ := GL2PrincipalColumns.GL2_conjugatorCounts ha hp hb hbz
    have htt : ∑ i ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation i).character t ^ 2 = 48 := by
      have h := GL2PrincipalColumns.principal_column_kernel ideal basis principal hprincipal ht π
        hπ hN ha hp hb hbz _ _ hxt hxt
      rw [hπt', c11] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i hi => ?_
      show _ = (basis.representation i).character t *
        starRingEnd ℂ ((basis.representation i).character t)
      rw [hvt i hi, map_add, map_mul, map_intCast, map_intCast, map_ofNat]
      ring
    have hqq : ∑ i ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation i).character (t * q) ^ 2 = 6 := by
      have h := GL2PrincipalColumns.principal_column_kernel ideal basis principal hprincipal ht π
        hπ hN ha hp hb hbz _ _ hxq hxq
      rw [hπx', c22] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i hi => ?_
      show _ = (basis.representation i).character (t * q) *
        starRingEnd ℂ ((basis.representation i).character (t * q))
      rw [hvq i hi, map_sub, map_intCast, map_intCast]
      ring
    have htq : ∑ i ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation i).character t * (basis.representation i).character (t * q) =
          0 := by
      have h := GL2PrincipalColumns.principal_column_kernel ideal basis principal hprincipal ht π
        hπ hN ha hp hb hbz _ _ hxt hxq
      rw [hπx', hπt', c21] at h
      rw [← h]
      refine Finset.sum_congr rfl fun i hi => ?_
      show _ = (basis.representation i).character t *
        starRingEnd ℂ ((basis.representation i).character (t * q))
      rw [hvq i hi, map_sub, map_intCast, map_intCast]
    exact GL2Columns.columns_of_identities ht π hN hπt' ha hp hb hbz hφirr hφ' q hq basis
      (coefficientBlock basis (localizedComplexIntegerRing ideal) principal) hcoord htt hqq htq c
      rfl l hl hlinj hmemB hε hε₁ hε₂ hε₃ hβ0 hβ1 hβ2 hβ3 hβ4
  have hck : ∀ k, (c k) = (basis.representation (l k)).character := fun k => (hl k).symm
  have hctn : ∀ k (n : N), c k (t * ((n : C) : G)) = c k t := fun k n => by
    rw [hck k]
    exact htn (l k) (hmemB k) n
  have hctqn : ∀ k (q : C), π q = p → ∀ n : N,
      c k (t * (q : G) * ((n : C) : G)) = c k (t * (q : G)) := fun k q hq n => by
    rw [hck k]
    exact htqn (l k) (hmemB k) q hq n
  have hmemc : ∀ k, c k ∈ B₀ := fun k =>
    ⟨l k, Finset.mem_coe.mpr (hmemB k), hl k⟩
  refine ⟨⟨hmemc 1, hmemc 2, hmemc 3, hmemc 4, hmemc 5, hmemc 6, hmemc 7⟩, ?_, ?_, ?_⟩
  · intro q hq
    refine ⟨GL2Columns.odd_orderOf_of_map_eq π hN hp q hq, fun n => ?_⟩
    obtain ⟨⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, ⟨a4, b4⟩, ⟨a5, b5⟩, ⟨a6, b6⟩, ⟨a7, b7⟩, -⟩ :=
      hengine q hq
    refine ⟨?_, ?_⟩
    · ext k
      fin_cases k
      · exact (hctn 1 n).trans a1
      · exact (hctn 2 n).trans a2
      · exact (hctn 3 n).trans a3
      · exact (hctn 4 n).trans a4
      · exact (hctn 5 n).trans a5
      · exact (hctn 6 n).trans a6
      · exact (hctn 7 n).trans a7
    · ext k
      fin_cases k
      · exact (hctqn 1 q hq n).trans b1
      · exact (hctqn 2 q hq n).trans b2
      · exact (hctqn 3 q hq n).trans b3
      · exact (hctqn 4 q hq n).trans b4
      · exact (hctqn 5 q hq n).trans b5
      · exact (hctqn 6 q hq n).trans b6
      · exact (hctqn 7 q hq n).trans b7
  · rintro ψ ⟨j, hj, rfl⟩ hψ0 hψ1 hψ2 hψ3 hψ4 hψ5 hψ6 hψ7 q hq n
    have hj' : j ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal :=
      Finset.mem_coe.mp hj
    have hni : ∀ k, l k ≠ j := by
      intro k hk
      have e : (basis.representation j).character = c k := by rw [← hk, hl k]
      fin_cases k
      exacts [hψ0 e, hψ1 e, hψ2 e, hψ3 e, hψ4 e, hψ5 e, hψ6 e, hψ7 e]
    obtain ⟨-, -, -, -, -, -, -, hrest⟩ := hengine q hq
    obtain ⟨e1, e2⟩ := hrest j hj' hni
    exact ⟨(htn j hj' n).trans e1, (htqn j hj' q hq n).trans e2⟩
  · intro hidx
    have hidx2 : ¬ 2 ∣ (Subgroup.centralizer ({t} : Set G)).index := fun h =>
      (Nat.not_even_iff_odd.mpr hidx) (even_iff_two_dvd.mpr h)
    obtain ⟨-, -, -, -, -, -, -, hrest⟩ := hengine (Function.surjInv hπ p)
      (Function.surjInv_eq hπ p)
    ext ψ
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hj' : j ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal :=
        Finset.mem_coe.mp hj
      have hnv := (CFSG.LyonsUnitaryFour.principal_block_character_ne_zero basis ideal 2 principal
        hprincipal j hj' t hidx2).2
      by_cases hk : ∃ k, l k = j
      · obtain ⟨k, rfl⟩ := hk
        beta_reduce
        rw [hl k]
        fin_cases k <;> simp [c]
      · exact absurd (hrest j hj' fun k hkj => hk ⟨k, hkj⟩).1 hnv
    · intro hψ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
      rcases hψ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hmemc 0
      · exact hmemc 1
      · exact hmemc 2
      · exact hmemc 3
      · exact hmemc 4
      · exact hmemc 5
      · exact hmemc 6
      · exact hmemc 7

end CFSG.Semidihedral.Principal
