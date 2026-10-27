module

public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourNorm
public import CFSG.LocalAnalysis.LargeEvenClassification.FrattiniKernelCount
public import CFSG.LocalAnalysis.LargeEvenClassification.IndependentKernelCount

public section

namespace CFSG.LargeEvenClassification.Helpers

@[expose] def c8FourBinaryHom {A : Type*} [Group A]
    (coordinates : Additive A ≃+ CyclicPair 2 4) :
    A →* Multiplicative (ZMod 2 × ZMod 2) :=
  AddMonoidHom.toMultiplicativeRight
    (c8FourBinaryCoordinates.comp coordinates.toAddMonoidHom)

theorem c8FourBinaryHom_one_iff {A : Type*} [Group A]
    (coordinates : Additive A ≃+ CyclicPair 2 4) (a : A) :
    c8FourBinaryHom coordinates a = 1 ↔ ∃ b : A, b ^ 2 = a := by
  change c8FourBinaryCoordinates (coordinates (Additive.ofMul a)) = 0 ↔ _
  rw [c8FourBinaryCoordinates_zero]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(coordinates.symm y).toMul, ?_⟩
    apply Additive.ofMul.injective
    apply coordinates.injective
    change coordinates (2 • coordinates.symm y) = coordinates (Additive.ofMul a)
    rw [map_nsmul, coordinates.apply_symm_apply, hy]
  · rintro ⟨b, rfl⟩
    refine ⟨coordinates (Additive.ofMul b), ?_⟩
    change 2 • coordinates (Additive.ofMul b) = coordinates (2 • Additive.ofMul b)
    exact (map_nsmul coordinates _ _).symm

theorem c8FourBinaryHom_primitive {A : Type*} [Group A]
    (coordinates : Additive A ≃+ CyclicPair 2 4) (a : A)
    (hprimitive : ∀ b : A, a ≠ b ^ 2) : c8FourBinaryHom coordinates a ≠ 1 := by
  intro h
  obtain ⟨b, hb⟩ := (c8FourBinaryHom_one_iff coordinates a).mp h
  exact hprimitive b hb.symm

theorem card_two_addSubgroup_le_of_common_nonzero {V : Type*} [AddGroup V]
    (P Q : AddSubgroup V) (hP : Nat.card P = 2) (x : V)
    (hxP : x ∈ P) (hxQ : x ∈ Q) (hx : x ≠ 0) : P ≤ Q := by
  obtain ⟨z, _, hunique⟩ := (Nat.card_eq_two_iff' (0 : P)).mp hP
  have hx' : (⟨x, hxP⟩ : P) ≠ 0 := by
    intro h
    exact hx (congrArg Subtype.val h)
  intro y hyP
  by_cases hy : y = 0
  · rw [hy]
    exact Q.zero_mem
  · have hy' : (⟨y, hyP⟩ : P) ≠ 0 := by
      intro h
      exact hy (congrArg Subtype.val h)
    have heq : (⟨y, hyP⟩ : P) = ⟨x, hxP⟩ :=
      (hunique _ hy').trans (hunique _ hx').symm
    have hyx : y = x := congrArg Subtype.val heq
    rw [hyx]
    exact hxQ

theorem card_two_addSubgroup_nonzero_ne {V : Type*} [AddGroup V]
    (P Q : AddSubgroup V) (hP : Nat.card P = 2) (hQ : Nat.card Q = 2)
    (hdistinct : P ≠ Q) (x y : V) (hxP : x ∈ P) (hyQ : y ∈ Q)
    (hx : x ≠ 0) (hy : y ≠ 0) : x ≠ y := by
  intro hxy
  apply hdistinct
  apply le_antisymm
  · exact card_two_addSubgroup_le_of_common_nonzero P Q hP x hxP
      (hxy ▸ hyQ) hx
  · exact card_two_addSubgroup_le_of_common_nonzero Q P hQ y hyQ
      (hxy ▸ hxP) hy

theorem normal_binary_distinct_frattini_saving {G : Type*} [Group G] [Finite G]
    (hpgroup : IsPGroup 2 G) (B : Subgroup G) [B.Normal]
    (hcommutative : IsMulCommutative B)
    (binary : B →* Multiplicative (ZMod 2 × ZMod 2)) (b₀ b₁ : B)
    (h₀ : binary b₀ ≠ 1) (h₁ : binary b₁ ≠ 1)
    (hdistinct : binary b₀ ≠ binary b₁)
    (hfrattini₀ : b₀.val ∈ frattini G) (hfrattini₁ : b₁.val ∈ frattini G) :
    pGeneratorRank 2 G + 2 ≤ pGeneratorRank 2 (G ⧸ B) + pGeneratorRank 2 B := by
  let : CommGroup B := { (inferInstance : Group B) with
    mul_comm := @mul_comm' _ _ hcommutative }
  have hpB := hpgroup.to_subgroup B
  let : CommGroup (B ⧸ frattini B) := pGroupFrattiniCommGroup Nat.prime_two hpB
  let moduleB : Module (ZMod 2) (Additive (B ⧸ frattini B)) :=
    elementaryZModModule (pGroup_frattini_quotient_exponent Nat.prime_two hpB)
  let := moduleB
  have hkernel : frattini B ≤ binary.ker := by
    rw [commutative_frattini_eq_power_range Nat.prime_two hpB]
    rintro b ⟨a, rfl⟩
    change binary (a ^ 2) = 1
    rw [map_pow]
    have h : ∀ x : Multiplicative (ZMod 2 × ZMod 2), x ^ 2 = 1 := by decide +kernel
    exact h _
  let induced := QuotientGroup.lift (frattini B) binary hkernel
  let family : Fin 2 → B := ![b₀, b₁]
  let classes := fun i : Fin 2 =>
    Additive.ofMul ((QuotientGroup.mk' (frattini B)) (family i))
  have hindependent : LinearIndependent (ZMod 2) classes := by
    apply linearIndependent_fin2.mpr
    constructor
    · intro hzero
      have h := congrArg (fun x : Additive (B ⧸ frattini B) => induced x.toMul) hzero
      change binary b₁ = induced 1 at h
      rw [map_one] at h
      exact h₁ h
    · intro s heq
      have hcases : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide +kernel
      rcases hcases s with h | h
      · rw [h, zero_smul] at heq
        have hzero := congrArg (fun x : Additive (B ⧸ frattini B) => induced x.toMul) heq
        change induced 1 = binary b₀ at hzero
        rw [map_one] at hzero
        exact h₀ hzero.symm
      · rw [h, one_smul] at heq
        have hsame := congrArg (fun x : Additive (B ⧸ frattini B) => induced x.toMul) heq
        change binary b₁ = binary b₀ at hsame
        exact hdistinct hsame.symm
  have hfamily (i : Fin 2) : (family i).val ∈ frattini G := by
    fin_cases i
    · exact hfrattini₀
    · exact hfrattini₁
  have hsave := pGeneratorRank_normal_independent_saving Nat.prime_two hpgroup B
    family hfamily moduleB hindependent
  simpa only [Fintype.card_fin] using hsave

theorem abelian_kernel_primitive_square_saving
    {G A Q : Type*} [Group G] [Finite G] [Group A] [Group Q]
    (hpG : IsPGroup 2 G) (quotient : G →* Q)
    (hcommutative : IsMulCommutative quotient.ker) (embedding : quotient.ker →* A)
    (u : G) (b : quotient.ker) (hsquare : (b : G) = u ^ 2)
    (hprimitive : ∀ a : A, embedding b ≠ a ^ 2) :
    pGeneratorRank 2 G + 1 ≤
      pGeneratorRank 2 (G ⧸ quotient.ker) + pGeneratorRank 2 quotient.ker := by
  have hfrattini : (b : G) ∈ frattini G :=
    hsquare ▸ pGroup_pow_mem_frattini Nat.prime_two hpG u
  have hnotPower : ¬∃ a : quotient.ker, a ^ 2 = b := by
    rintro ⟨a, ha⟩
    exact hprimitive (embedding a)
      (congrArg embedding ha |>.symm.trans (map_pow embedding a 2))
  exact pGeneratorRank_normal_square_saving Nat.prime_two hpG quotient.ker
    hcommutative b hfrattini hnotPower

theorem abelian_kernel_two_binary_squares_saving
    {G A Q : Type*} [Group G] [Finite G] [Group A] [Group Q]
    (hpG : IsPGroup 2 G) (quotient : G →* Q)
    (hcommutative : IsMulCommutative quotient.ker) (embedding : quotient.ker →* A)
    (binary : A →* Multiplicative (ZMod 2 × ZMod 2))
    (u₀ u₁ : G) (b₀ b₁ : quotient.ker)
    (hsquare₀ : (b₀ : G) = u₀ ^ 2) (hsquare₁ : (b₁ : G) = u₁ ^ 2)
    (h₀ : binary (embedding b₀) ≠ 1) (h₁ : binary (embedding b₁) ≠ 1)
    (hdistinct : binary (embedding b₀) ≠ binary (embedding b₁)) :
    pGeneratorRank 2 G + 2 ≤
      pGeneratorRank 2 (G ⧸ quotient.ker) + pGeneratorRank 2 quotient.ker := by
  exact normal_binary_distinct_frattini_saving hpG quotient.ker hcommutative
    (binary.comp embedding) b₀ b₁ h₀ h₁ hdistinct
    (hsquare₀ ▸ pGroup_pow_mem_frattini Nat.prime_two hpG u₀)
    (hsquare₁ ▸ pGroup_pow_mem_frattini Nat.prime_two hpG u₁)

theorem abelian_kernel_four_action_primitive_squares_four_generators
    {G A Q : Type*} [Group G] [Finite G] [CommGroup A] [Finite A] [Group Q]
    (hpG : IsPGroup 2 G) (hpA : IsPGroup 2 A) (quotient : G →* Q)
    (hsurjective : Function.Surjective quotient) (embedding : quotient.ker →* A)
    (hinjective : Function.Injective embedding) (hArank : pGeneratorRank 2 A ≤ 2)
    (hQrank : pGeneratorRank 2 Q ≤ 4)
    (binary : A →* Multiplicative (ZMod 2 × ZMod 2))
    (hcriticalThree : pGeneratorRank 2 Q = 3 → ∃ u : G, ∃ b : quotient.ker,
      (b : G) = u ^ 2 ∧ ∀ a : A, embedding b ≠ a ^ 2)
    (hcriticalFour : pGeneratorRank 2 Q = 4 → ∃ u₀ u₁ : G, ∃ b₀ b₁ : quotient.ker,
      (b₀ : G) = u₀ ^ 2 ∧ (b₁ : G) = u₁ ^ 2 ∧
      binary (embedding b₀) ≠ 1 ∧ binary (embedding b₁) ≠ 1 ∧
      binary (embedding b₀) ≠ binary (embedding b₁)) :
    ∃ X : Finset G, Subgroup.closure (X : Set G) = ⊤ ∧ X.card ≤ 4 := by
  let B := quotient.ker
  have hcommutative : IsMulCommutative B := by
    apply isMulCommutative_iff.mpr
    intro b c
    apply hinjective
    rw [map_mul, map_mul, mul_comm]
  let : CommGroup B := { (inferInstance : Group B) with
    mul_comm := @mul_comm' _ _ hcommutative }
  have hBrank : pGeneratorRank 2 B ≤ 2 :=
    (commutative_pGeneratorRank_embedding_le Nat.prime_two hpA embedding hinjective).trans hArank
  have e : G ⧸ B ≃* Q := QuotientGroup.quotientKerEquivOfSurjective quotient hsurjective
  have hquotient := pGeneratorRank_mulEquiv Nat.prime_two (hpG.to_quotient B) e
  have hGrank : pGeneratorRank 2 G ≤ 4 := by
    by_cases hsmall : pGeneratorRank 2 Q ≤ 2
    · have h := pGeneratorRank_extension_le Nat.prime_two hpG B
      rw [hquotient] at h
      omega
    · by_cases hthree : pGeneratorRank 2 Q = 3
      · obtain ⟨u, b, hsquare, hprimitive⟩ := hcriticalThree hthree
        have h := abelian_kernel_primitive_square_saving hpG quotient hcommutative
          embedding u b hsquare hprimitive
        change pGeneratorRank 2 G + 1 ≤
          pGeneratorRank 2 (G ⧸ B) + pGeneratorRank 2 B at h
        rw [hquotient] at h
        omega
      · obtain ⟨u₀, u₁, b₀, b₁, hsquare₀, hsquare₁, h₀, h₁, hdistinct⟩ :=
          hcriticalFour (by omega)
        have h := abelian_kernel_two_binary_squares_saving hpG quotient hcommutative
          embedding binary u₀ u₁ b₀ b₁ hsquare₀ hsquare₁ h₀ h₁ hdistinct
        change pGeneratorRank 2 G + 2 ≤
          pGeneratorRank 2 (G ⧸ B) + pGeneratorRank 2 B at h
        rw [hquotient] at h
        omega
  obtain ⟨X, hgenerates, hcard⟩ := pGeneratorRank_generators Nat.prime_two hpG
  exact ⟨X, hgenerates, hcard.trans_le hGrank⟩

end CFSG.LargeEvenClassification.Helpers
