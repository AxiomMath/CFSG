module

public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralPrincipalInducedFamily
public import CFSG.CharacterTheory.Semidihedral.Principal.SectionPrincipalTransport
public import CFSG.CharacterTheory.Semidihedral.Principal.NormalKernelBlockInflation
public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.PrincipalNonvanishing

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

section InnerProduct

variable {G : Type} [Group G] [Fintype G]

theorem blocksInnerProduct_self_eq_zero {h : G → ℂ} (hh : BlocksInnerProduct h h = 0) :
    h = 0 := by
  unfold BlocksInnerProduct at hh
  have hcard : (Nat.card G : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hsum : ∑ x, h x * starRingEnd ℂ (h x) = 0 := (mul_eq_zero.mp hh).resolve_left hcard
  simp_rw [Complex.mul_conj] at hsum
  have hreal : ∑ x, Complex.normSq (h x) = 0 := by exact_mod_cast hsum
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => Complex.normSq_nonneg (h x))).mp
    hreal
  funext x
  exact Complex.normSq_eq_zero.mp (hzero x (Finset.mem_univ x))

theorem eq_zero_of_mem_span_of_orthogonal {V : Set (G → ℂ)} {h : G → ℂ}
    (hh : h ∈ Submodule.span ℂ V) (horth : ∀ v ∈ V, BlocksInnerProduct h v = 0) : h = 0 := by
  apply blocksInnerProduct_self_eq_zero
  let W : Submodule ℂ (G → ℂ) :=
    { carrier := {g | BlocksInnerProduct h g = 0}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        unfold BlocksInnerProduct at ha hb ⊢
        simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
        rw [ha, hb, add_zero]
      zero_mem' := by
        simp only [Set.mem_ofPred_eq]
        simp [BlocksInnerProduct]
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        unfold BlocksInnerProduct at ha ⊢
        simp only [Pi.smul_apply, smul_eq_mul, map_mul]
        have : ∑ x, h x * (starRingEnd ℂ c * starRingEnd ℂ (a x)) =
            starRingEnd ℂ c * ∑ x, h x * starRingEnd ℂ (a x) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => by ring
        rw [this, mul_left_comm, ha, mul_zero] }
  exact (Submodule.span_le.mpr horth : Submodule.span ℂ V ≤ W) hh

theorem blocksInnerProduct_comm (f g : G → ℂ) :
    BlocksInnerProduct f g = starRingEnd ℂ (BlocksInnerProduct g f) := by
  unfold BlocksInnerProduct
  rw [map_mul, map_sum, map_inv₀, Complex.conj_natCast]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, Complex.conj_conj, mul_comm]

theorem blocksInnerProduct_right_add (f g h : G → ℂ) :
    BlocksInnerProduct f (g + h) = BlocksInnerProduct f g + BlocksInnerProduct f h := by
  unfold BlocksInnerProduct
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Pi.add_apply, map_add, mul_add]

theorem blocksInnerProduct_right_sub (f g h : G → ℂ) :
    BlocksInnerProduct f (g - h) = BlocksInnerProduct f g - BlocksInnerProduct f h := by
  unfold BlocksInnerProduct
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Pi.sub_apply, map_sub, mul_sub]

theorem blocksInnerProduct_left_smul (c : ℂ) (f g : G → ℂ) :
    BlocksInnerProduct (c • f) g = c * BlocksInnerProduct f g := by
  unfold BlocksInnerProduct
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem blocksInnerProduct_mask_left (D : Set G) (f g : G → ℂ) (hg : ∀ x, x ∉ D → g x = 0) :
    BlocksInnerProduct (characterFunctionMask D f) g = BlocksInnerProduct f g := by
  unfold BlocksInnerProduct
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ D
  · rw [characterFunctionMask, ite_eq_left hx]
  · rw [characterFunctionMask, ite_eq_right hx, hg x hx, map_zero, mul_zero, mul_zero]

end InnerProduct

section SectionValues

variable {C S : Type} [Group C] [Fintype C] [Group S] [Fintype S]

omit [Fintype S] in
theorem eq_on_of_pairings (π : C →* S) (D : Set C) {ι : Type*} (b : ι → C → ℂ)
    (hspan : Submodule.span ℂ (Set.range b) = sectionQuotientSpace π D)
    (hbsupp : ∀ i x, x ∉ D → b i x = 0) (f : C → ℂ)
    (hf : characterFunctionMask D f ∈ sectionQuotientSpace π D) (F : S → ℂ)
    (hF : characterFunctionMask D (F ∘ π) ∈ sectionQuotientSpace π D)
    (hpair : ∀ i, BlocksInnerProduct f (b i) = BlocksInnerProduct (F ∘ π) (b i)) :
    ∀ x ∈ D, f x = F (π x) := by
  have hzero : characterFunctionMask D f - characterFunctionMask D (F ∘ π) = 0 := by
    apply eq_zero_of_mem_span_of_orthogonal (V := Set.range b)
    · rw [hspan]
      exact Submodule.sub_mem _ hf hF
    · rintro _ ⟨i, rfl⟩
      rw [blocksInnerProduct_left_sub, blocksInnerProduct_mask_left D _ _ (hbsupp i),
        blocksInnerProduct_mask_left D _ _ (hbsupp i), hpair i, sub_self]
  intro x hx
  have h := congrFun hzero x
  simp only [Pi.sub_apply, Pi.zero_apply, characterFunctionMask, ite_eq_left hx,
    Function.comp_apply] at h
  exact sub_eq_zero.mp h

end SectionValues

section Blocks

variable {C S : Type} [Group C] [Fintype C] [Group S] [Fintype S]
  (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
  [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]

theorem mem_coefficientBlock_of_isPGroup_two (hS : IsPGroup 2 S)
    (basis : FiniteIrreducibleCharacterBasis S) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (label : basis.index) :
    label ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal := by
  have h := (CFSG.LyonsUnitaryFour.normal_p_complement_principal_block basis ideal 2 principal
    hprincipal ⊥ (by simp) (hS.to_quotient ⊥)).1 label
  exact h.mpr bot_le

theorem comp_mem_principal_span (π : C →* S) (hπ : Function.Surjective π)
    (hodd : Odd (Nat.card π.ker)) (hS : IsPGroup 2 S) (basisC : FiniteIrreducibleCharacterBasis C)
    (principalC : basisC.index) (hprincipalC : (basisC.representation principalC).character = 1)
    {χ : S → ℂ} (hχ : χ ∈ BlocksIrr S) :
    χ ∘ π ∈ coefficientCharacterSpace basisC
      (coefficientBlock basisC (localizedComplexIntegerRing ideal) principalC) := by
  obtain ⟨basisS⟩ := finiteIrreducibleCharacterBasis_exists (G := S)
  obtain ⟨principalS, hprincipalS⟩ := finiteIrreducibleCharacterBasis_exists_principal_label basisS
  rw [blocksIrr_eq_irreducible_characters] at hχ
  obtain ⟨data, hdata, rfl⟩ := hχ
  obtain ⟨θ, hθ⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basisS data hdata
  obtain ⟨c, hc⟩ := exists_inflated_label π hπ basisC basisS θ
  have hblock := (normal_prime_kernel_principal_block_inflation_of_surjective π hπ basisC ideal 2
    hodd.not_two_dvd_nat basisS principalC hprincipalC principalS hprincipalS).1 c
  have hcB := hblock.mpr ⟨θ, mem_coefficientBlock_of_isPGroup_two ideal hS basisS principalS
    hprincipalS θ, hc⟩
  have heq : data.character ∘ π = (basisC.representation c).character := by rw [hc, hθ]
  rw [heq]
  exact Submodule.subset_span ⟨c, hcB, rfl⟩

theorem exists_inflation_of_mem_principal_span (π : C →* S) (hπ : Function.Surjective π)
    (hodd : Odd (Nat.card π.ker)) (basisC : FiniteIrreducibleCharacterBasis C)
    (principalC : basisC.index) (hprincipalC : (basisC.representation principalC).character = 1)
    {f : C → ℂ} (hf : f ∈ coefficientCharacterSpace basisC
      (coefficientBlock basisC (localizedComplexIntegerRing ideal) principalC)) :
    ∃ F : S → ℂ, BlocksIsClassFunction F ∧ f = F ∘ π := by
  obtain ⟨basisS⟩ := finiteIrreducibleCharacterBasis_exists (G := S)
  obtain ⟨principalS, hprincipalS⟩ := finiteIrreducibleCharacterBasis_exists_principal_label basisS
  have hblock := (normal_prime_kernel_principal_block_inflation_of_surjective π hπ basisC ideal 2
    hodd.not_two_dvd_nat basisS principalC hprincipalC principalS hprincipalS).1
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨c, hc, rfl⟩ := hg
    obtain ⟨θ, -, hθ⟩ := (hblock c).mp hc
    exact ⟨(basisS.representation θ).character,
      fun g h => Representation.char_conj _ g h, hθ⟩
  | zero => exact ⟨0, fun _ _ => rfl, rfl⟩
  | add a b _ _ ha hb =>
    obtain ⟨Fa, hFa, rfl⟩ := ha
    obtain ⟨Fb, hFb, rfl⟩ := hb
    refine ⟨Fa + Fb, fun g h => ?_, rfl⟩
    simp only [Pi.add_apply]
    rw [hFa g h, hFb g h]
  | smul c a _ ha =>
    obtain ⟨Fa, hFa, rfl⟩ := ha
    refine ⟨c • Fa, fun g h => ?_, rfl⟩
    simp only [Pi.smul_apply]
    rw [hFa g h]

end Blocks

theorem mask_comp_mem_sectionQuotientSpace {C S : Type*} [Group C] [Group S] (π : C →* S)
    (D : Set C) (A : Set S) (hD : D = π ⁻¹' A)
    (hA : ∀ g h : S, h * g * h⁻¹ ∈ A ↔ g ∈ A) {F : S → ℂ} (hF : BlocksIsClassFunction F) :
    characterFunctionMask D (F ∘ π) ∈ sectionQuotientSpace π D := by
  subst hD
  have hmask : characterFunctionMask (π ⁻¹' A) (F ∘ π) = characterFunctionMask A F ∘ π := by
    funext x
    simp only [characterFunctionMask, Set.mem_preimage, Function.comp_apply]
  have hclass : BlocksIsClassFunction (characterFunctionMask A F) := by
    intro g h
    simp only [characterFunctionMask, hA g h, hF g h]
  refine ⟨?_, fun x hx => ?_, characterFunctionMask A F, hclass, hmask⟩
  · rw [hmask]
    intro g h
    simp only [Function.comp_apply, map_mul, map_inv]
    exact hclass _ _
  · simp only [characterFunctionMask, ite_eq_right hx]

theorem card_eq_of_image_eq_four_union {X Y : Type*} [DecidableEq Y] {ι : Type*} [Fintype ι]
    (B : Finset X) (f : X → Y) (hf : Function.Injective f) (a b c d : Y) (ψ : ι → Y)
    (hψ : Function.Injective ψ) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (haψ : ∀ k, a ≠ ψ k) (hψb : ∀ k, ψ k ≠ b) (hψc : ∀ k, ψ k ≠ c)
    (hψd : ∀ k, ψ k ≠ d) (himage : f '' (B : Set X) = ({a, b, c, d} : Set Y) ∪ Set.range ψ) :
    B.card = 4 + Fintype.card ι := by
  have hfin : B.image f = insert a (insert b (insert c (insert d (Finset.univ.image ψ)))) := by
    apply Finset.coe_injective
    rw [Finset.coe_image, himage]
    simp only [Finset.coe_insert, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    ext y
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc]
  rw [← Finset.card_image_of_injective _ hf, hfin]
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_insert_of_notMem, Finset.card_image_of_injective _ hψ, Finset.card_univ]
  · omega
  · simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact fun k h => hψd k h
  · simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and, not_or,
      not_exists]
    exact ⟨hcd, fun k h => hψc k h⟩
  · simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and, not_or,
      not_exists]
    exact ⟨hbc, hbd, fun k h => hψb k h⟩
  · simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and, not_or,
      not_exists]
    exact ⟨hab, hac, had, fun k h => haψ k h.symm⟩

theorem dihedral_principal_block_exhaustion_of_normalHall {G : Type} [Group G] [Fintype G]
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] {n M : ℕ} (hn : 2 ≤ n)
    (hM : M = 2 ^ (n - 1)) (S : Sylow 2 G)
    (hSiso : Nonempty (DihedralGroup M ≃* (S : Subgroup G))) (r s : (S : Subgroup G))
    (hr : orderOf r = M) (hs : orderOf s = 2) (hrel : s * r * s = r⁻¹)
    (hgen : Subgroup.closure {r, s} = ⊤) (t : G)
    (ht : t = ((r ^ (M / 2) : (S : Subgroup G)) : G)) (C : Subgroup G)
    (hC : C = Subgroup.centralizer {t}) (basisG : FiniteIrreducibleCharacterBasis G)
    (principalG : basisG.index) (hprincipalG : (basisG.representation principalG).character = 1)
    (R : Subgroup C) [R.Normal] (hRodd : Odd (Nat.card R)) (hRidx : ∃ k : ℕ, R.index = 2 ^ k)
    (π : C →* (S : Subgroup G)) (hker : π.ker = R)
    (hid : ∀ (y : (S : Subgroup G)) (hy : (y : G) ∈ C), π ⟨y, hy⟩ = y) :
    ∃ (χ₁ χ₂ χ₃ : BlocksIrr G) (δ₁ δ₂ δ₃ ε : ℤ) (ψ : dihedralIndexSet M → BlocksIrr G),
      χ₁ ≠ χ₂ ∧ χ₁ ≠ χ₃ ∧ χ₂ ≠ χ₃ ∧
      (χ₁ : G → ℂ) ≠ 1 ∧ (χ₂ : G → ℂ) ≠ 1 ∧ (χ₃ : G → ℂ) ≠ 1 ∧
      (δ₁ = 1 ∨ δ₁ = -1) ∧ (δ₂ = 1 ∨ δ₂ = -1) ∧ (δ₃ = 1 ∨ δ₃ = -1) ∧ (ε = 1 ∨ ε = -1) ∧
      Function.Injective ψ ∧
      (∀ k, (ψ k : G → ℂ) ≠ 1 ∧ ψ k ≠ χ₁ ∧ ψ k ≠ χ₂ ∧ ψ k ≠ χ₃) ∧
      inducedFunction C (dihedralTheta r s M ∘ π) =
        1 + (δ₁ : ℂ) • (χ₁ : G → ℂ) + (δ₂ : ℂ) • (χ₂ : G → ℂ) + (δ₃ : ℂ) • (χ₃ : G → ℂ) ∧
      (∀ k : dihedralIndexSet M, inducedFunction C (dihedralEta r s M k ∘ π) =
        1 + (δ₁ : ℂ) • (χ₁ : G → ℂ) + (ε : ℂ) • (ψ k : G → ℂ)) ∧
      (fun l => (basisG.representation l).character) ''
          (coefficientBlock basisG (localizedComplexIntegerRing ideal) principalG :
            Set basisG.index) =
        {1, (χ₁ : G → ℂ), (χ₂ : G → ℂ), (χ₃ : G → ℂ)} ∪ Set.range (fun k => (ψ k : G → ℂ)) ∧
      (coefficientBlock basisG (localizedComplexIntegerRing ideal) principalG).card =
        M / 2 + 3 ∧
      (∀ x : C, (x : G) ∈ centralInvolutionSection t →
        (χ₁ : G → ℂ) x = δ₁ * dihedralLinearCharacter r s M 1 (π x) ∧
        (χ₂ : G → ℂ) x = -δ₂ * dihedralLinearCharacter r s M 2 (π x) ∧
        (χ₃ : G → ℂ) x = -δ₃ * dihedralLinearCharacter r s M 3 (π x) ∧
        ∀ k : dihedralIndexSet M,
          (ψ k : G → ℂ) x = -ε * dihedralRotationCharacter r s M k (π x)) ∧
      (χ₁ : G → ℂ) t = δ₁ ∧
      (n = 2 → (χ₂ : G → ℂ) t = δ₂ ∧ (χ₃ : G → ℂ) t = δ₃) ∧
      (3 ≤ n → (χ₂ : G → ℂ) t = -δ₂ ∧ (χ₃ : G → ℂ) t = -δ₃) ∧
      (∀ k : dihedralIndexSet M, (ψ k : G → ℂ) t = -2 * ε * (-1) ^ (k : ℤ)) ∧
      ∀ y : G, Odd (orderOf y) →
        1 + δ₁ * (χ₁ : G → ℂ) y + δ₂ * (χ₂ : G → ℂ) y + δ₃ * (χ₃ : G → ℂ) y = 0 ∧
        ∀ k : dihedralIndexSet M, 1 + δ₁ * (χ₁ : G → ℂ) y + ε * (ψ k : G → ℂ) y = 0 := by
  obtain ⟨χ₁, χ₂, χ₃, δ₁, δ₂, δ₃, ε, ψ, h12, h13, h23, h1, h2, h3, hδ₁, hδ₂, hδ₃, hε, hψ,
    hψne, hΘ, hE, -, -⟩ := (dihedral_principal_induced_character_family_of_normalHall hn hM S
      hSiso r s hr hs hrel hgen t ht C hC R hRodd hRidx).2 π hker hid
  subst hC
  have hM2 : 2 ≤ M := by
    rw [hM]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hEven : Even M := by
    rw [hM]
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hcard : Nat.card (S : Subgroup G) = 2 * M := by
    obtain ⟨e⟩ := hSiso
    rw [← Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hhalf : M / 2 = 2 ^ (n - 2) := by
    rw [hM, show n - 1 = (n - 2) + 1 by omega, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
  have hstruct := (dihedral_rotation_involution_structure (S := (S : Subgroup G)) hn
    (hM ▸ hSiso)).2 r s (hM ▸ hr) hs hrel hgen
  have hAnormal : (Subgroup.zpowers r).Normal := hstruct.1
  have htS : r ^ (M / 2) ∈ Subgroup.center (S : Subgroup G) := by
    rw [hhalf]
    exact hstruct.2.2.2.2.2.1
  have hSC : (S : Subgroup G) ≤ Subgroup.centralizer {t} := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff, ht]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp htS ⟨y, hy⟩)
  set ι := Subgroup.inclusion hSC with hιdef
  have hι : Function.Injective ι := Subgroup.inclusion_injective hSC
  have hιt : ((ι (r ^ (M / 2)) : Subgroup.centralizer {t}) : G) = t := ht.symm
  have htC : ι (r ^ (M / 2)) ∈ Subgroup.center (Subgroup.centralizer {t}) := by
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    have hc := Subgroup.mem_centralizer_singleton_iff.mp c.2
    simp only [Subgroup.coe_mul, hιt]
    exact hc
  obtain ⟨hprod, hRS⟩ := normalHallOdd_complement_of_sylow S hSC R hRodd hRidx
  obtain ⟨-, hfacts⟩ := dihedral_section_quotient_basis_of_embedding hn hM hcard hgen hr hs
    hrel hι hRodd hprod hRS htC
  have hid' : π.comp ι = MonoidHom.id _ := by
    ext y
    exact congrArg Subtype.val (hid y (hSC y.2))
  obtain ⟨hDA, -, hspan, -, hinfl⟩ := hfacts π hker hid'
  have hπι : ∀ y, π (ι y) = y := fun y => DFunLike.congr_fun hid' y
  have hπsurj : Function.Surjective π := fun y => ⟨ι y, hπι y⟩
  have hkerodd : Odd (Nat.card π.ker) := by rw [hker]; exact hRodd
  obtain ⟨-, -, hφirr, hγirr, hφinj, hγinj, hφγ, -, hφval, hγval, -, -, -, -, -, -, -, -, -,
    -⟩ := dihedral_explicit_character_family hM2 hEven hcard hgen hr hs hrel
  have hφφ : ∀ i j : Fin 4, BlocksInnerProduct (dihedralLinearCharacter r s M i)
      (dihedralLinearCharacter r s M j) = if i = j then 1 else 0 := by
    intro i j
    rw [blocksInnerProduct_of_mem_blocksIrr (hφirr i) (hφirr j)]
    exact if_congr hφinj.eq_iff rfl rfl
  have hφγS : ∀ (i : Fin 4), ∀ k ∈ dihedralIndexSet M, BlocksInnerProduct
      (dihedralLinearCharacter r s M i) (dihedralRotationCharacter r s M k) = 0 := by
    intro i k hk
    rw [blocksInnerProduct_of_mem_blocksIrr (hφirr i) (hγirr k hk)]
    exact ite_eq_right_iff.mpr fun h => absurd h (hφγ i k hk)
  have hγφS : ∀ k ∈ dihedralIndexSet M, ∀ (i : Fin 4), BlocksInnerProduct
      (dihedralRotationCharacter r s M k) (dihedralLinearCharacter r s M i) = 0 := by
    intro k hk i
    rw [blocksInnerProduct_of_mem_blocksIrr (hγirr k hk) (hφirr i)]
    exact ite_eq_right_iff.mpr fun h => absurd h.symm (hφγ i k hk)
  have hγγS : ∀ k ∈ dihedralIndexSet M, ∀ l ∈ dihedralIndexSet M, BlocksInnerProduct
      (dihedralRotationCharacter r s M k) (dihedralRotationCharacter r s M l) =
        if k = l then 1 else 0 := by
    intro k hk l hl
    rw [blocksInnerProduct_of_mem_blocksIrr (hγirr k hk) (hγirr l hl)]
    exact if_congr ⟨fun h => hγinj hk hl h, fun h => h ▸ rfl⟩ rfl rfl
  have hφθ : ∀ i : Fin 4, BlocksInnerProduct (dihedralLinearCharacter r s M i)
      (dihedralTheta r s M) = (if i = 0 then 1 else 0) + (if i = 1 then 1 else 0) -
        (if i = 2 then 1 else 0) - (if i = 3 then 1 else 0) := by
    intro i
    simp only [dihedralTheta, blocksInnerProduct_right_add, blocksInnerProduct_right_sub, hφφ]
  have hφη : ∀ (i : Fin 4), ∀ k ∈ dihedralIndexSet M, BlocksInnerProduct
      (dihedralLinearCharacter r s M i) (dihedralEta r s M k) =
        (if i = 0 then 1 else 0) + (if i = 1 then 1 else 0) := by
    intro i k hk
    simp only [dihedralEta, blocksInnerProduct_right_add, blocksInnerProduct_right_sub, hφφ,
      hφγS i k hk, sub_zero]
  have hγθ : ∀ l ∈ dihedralIndexSet M, BlocksInnerProduct (dihedralRotationCharacter r s M l)
      (dihedralTheta r s M) = 0 := by
    intro l hl
    simp only [dihedralTheta, blocksInnerProduct_right_add, blocksInnerProduct_right_sub,
      hγφS l hl, add_zero, sub_zero]
  have hγη : ∀ l ∈ dihedralIndexSet M, ∀ k ∈ dihedralIndexSet M, BlocksInnerProduct
      (dihedralRotationCharacter r s M l) (dihedralEta r s M k) =
        -(if l = k then 1 else 0) := by
    intro l hl k hk
    simp only [dihedralEta, blocksInnerProduct_right_add, blocksInnerProduct_right_sub,
      hγφS l hl, hγγS l hl k hk, add_zero, zero_sub]
  have hirr1 : (1 : G → ℂ) ∈ BlocksIrr G := principal_mem_blocksIrr G
  have hpair1 : ∀ ξ : BlocksIrr G, BlocksInnerProduct (1 : G → ℂ) ξ =
      if (1 : G → ℂ) = ξ then 1 else 0 :=
    fun ξ => blocksInnerProduct_of_mem_blocksIrr hirr1 ξ.2
  have hpairχ : ∀ χ ξ : BlocksIrr G, BlocksInnerProduct (χ : G → ℂ) ξ =
      if (χ : G → ℂ) = ξ then 1 else 0 :=
    fun χ ξ => blocksInnerProduct_of_mem_blocksIrr χ.2 ξ.2
  have hΘpair : ∀ ξ : BlocksIrr G, BlocksInnerProduct
      (inducedFunction (Subgroup.centralizer {t}) (dihedralTheta r s M ∘ π)) ξ =
        (if (1 : G → ℂ) = ξ then 1 else 0) + δ₁ * (if (χ₁ : G → ℂ) = ξ then 1 else 0) +
          δ₂ * (if (χ₂ : G → ℂ) = ξ then 1 else 0) +
          δ₃ * (if (χ₃ : G → ℂ) = ξ then 1 else 0) := by
    intro ξ
    rw [hΘ]
    simp only [blocksInnerProduct_left_add, blocksInnerProduct_left_smul, hpair1, hpairχ]
  have hEpair : ∀ (k : dihedralIndexSet M) (ξ : BlocksIrr G), BlocksInnerProduct
      (inducedFunction (Subgroup.centralizer {t}) (dihedralEta r s M k ∘ π)) ξ =
        (if (1 : G → ℂ) = ξ then 1 else 0) + δ₁ * (if (χ₁ : G → ℂ) = ξ then 1 else 0) +
          ε * (if (ψ k : G → ℂ) = ξ then 1 else 0) := by
    intro k ξ
    rw [hE k]
    simp only [blocksInnerProduct_left_add, blocksInnerProduct_left_smul, hpair1, hpairχ]
  have c1χ₁ : (1 : G → ℂ) ≠ χ₁ := fun h => h1 h.symm
  have c1χ₂ : (1 : G → ℂ) ≠ χ₂ := fun h => h2 h.symm
  have c1χ₃ : (1 : G → ℂ) ≠ χ₃ := fun h => h3 h.symm
  have c12 : (χ₁ : G → ℂ) ≠ χ₂ := fun h => h12 (Subtype.ext h)
  have c13 : (χ₁ : G → ℂ) ≠ χ₃ := fun h => h13 (Subtype.ext h)
  have c23 : (χ₂ : G → ℂ) ≠ χ₃ := fun h => h23 (Subtype.ext h)
  have c1ψ : ∀ k, (1 : G → ℂ) ≠ ψ k := fun k h => (hψne k).1 h.symm
  have cψχ₁ : ∀ k, (ψ k : G → ℂ) ≠ χ₁ := fun k h => (hψne k).2.1 (Subtype.ext h)
  have cψχ₂ : ∀ k, (ψ k : G → ℂ) ≠ χ₂ := fun k h => (hψne k).2.2.1 (Subtype.ext h)
  have cψχ₃ : ∀ k, (ψ k : G → ℂ) ≠ χ₃ := fun k h => (hψne k).2.2.2 (Subtype.ext h)
  have cψψ : ∀ k l, (ψ k : G → ℂ) = ψ l ↔ k = l :=
    fun k l => ⟨fun h => hψ (Subtype.ext h), fun h => h ▸ rfl⟩
  set DC := centralInvolutionSection (ι (r ^ (M / 2))) with hDCdef
  have hDCiff : ∀ x : Subgroup.centralizer {t},
      x ∈ DC ↔ (x : G) ∈ centralInvolutionSection t := by
    intro x
    rw [hDCdef, mem_centralInvolutionSection_subgroup_iff, hιt]
  have hDCset : DC = {x : Subgroup.centralizer {t} | (x : G) ∈ centralInvolutionSection t} :=
    Set.ext hDCiff
  have hU : ∀ o, dihedralSectionFamily π r s M o ∈ sectionQuotientSpace π DC := by
    intro o
    rw [← hspan]
    exact Submodule.subset_span ⟨o, rfl⟩
  have hbsupp : ∀ o x, x ∉ DC → dihedralSectionFamily π r s M o x = 0 := fun o => (hU o).2.1
  have hsuppG : ∀ o (x : Subgroup.centralizer {t}), (x : G) ∉ centralInvolutionSection t →
      dihedralSectionFamily π r s M o x = 0 :=
    fun o x hx => hbsupp o x fun h => hx ((hDCiff x).mp h)
  have hAinv : ∀ g h : (S : Subgroup G),
      h * g * h⁻¹ ∈ ((Subgroup.zpowers r : Set (S : Subgroup G)) \ {1}) ↔
        g ∈ ((Subgroup.zpowers r : Set (S : Subgroup G)) \ {1}) := by
    intro g h
    simp only [Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hA, h1'⟩
      refine ⟨?_, ?_⟩
      · have hc := hAnormal.conj_mem _ hA h⁻¹
        simpa [mul_assoc] using hc
      · rintro rfl
        exact h1' (by group)
    · rintro ⟨hA, h1'⟩
      refine ⟨hAnormal.conj_mem _ hA h, fun h' => h1' ?_⟩
      have hc := congrArg (fun z => h⁻¹ * z * h) h'
      simpa [mul_assoc] using hc
  have hmaskU : ∀ F : ↥(S : Subgroup G) → ℂ, BlocksIsClassFunction F →
      characterFunctionMask DC (F ∘ π) ∈ sectionQuotientSpace π DC :=
    fun F hF => mask_comp_mem_sectionQuotientSpace π DC _ hDA hAinv hF
  obtain ⟨basisC⟩ := finiteIrreducibleCharacterBasis_exists (G := Subgroup.centralizer {t})
  obtain ⟨principalC, hprincipalC⟩ :=
    finiteIrreducibleCharacterBasis_exists_principal_label basisC
  have hS2 : IsPGroup 2 (S : Subgroup G) := S.isPGroup'
  have hinflspan : ∀ χ : ↥(S : Subgroup G) → ℂ, χ ∈ BlocksIrr (S : Subgroup G) →
      χ ∘ π ∈ coefficientCharacterSpace basisC
        (coefficientBlock basisC (localizedComplexIntegerRing ideal) principalC) :=
    fun χ hχ => comp_mem_principal_span ideal π hπsurj hkerodd hS2 basisC principalC hprincipalC hχ
  have hθspan : dihedralTheta r s M ∘ π ∈ coefficientCharacterSpace basisC
      (coefficientBlock basisC (localizedComplexIntegerRing ideal) principalC) := by
    have heq : dihedralTheta r s M ∘ π = dihedralLinearCharacter r s M 0 ∘ π +
        dihedralLinearCharacter r s M 1 ∘ π - dihedralLinearCharacter r s M 2 ∘ π -
        dihedralLinearCharacter r s M 3 ∘ π := by
      funext x
      simp [dihedralTheta]
    rw [heq]
    exact sub_mem (sub_mem (add_mem (hinflspan _ (hφirr 0)) (hinflspan _ (hφirr 1)))
      (hinflspan _ (hφirr 2))) (hinflspan _ (hφirr 3))
  have hηspan : ∀ k ∈ dihedralIndexSet M, dihedralEta r s M k ∘ π ∈ coefficientCharacterSpace
      basisC (coefficientBlock basisC (localizedComplexIntegerRing ideal) principalC) := by
    intro k hk
    have heq : dihedralEta r s M k ∘ π = dihedralLinearCharacter r s M 0 ∘ π +
        dihedralLinearCharacter r s M 1 ∘ π - dihedralRotationCharacter r s M k ∘ π := by
      funext x
      simp [dihedralEta]
    rw [heq]
    exact sub_mem (add_mem (hinflspan _ (hφirr 0)) (hinflspan _ (hφirr 1)))
      (hinflspan _ (hγirr k hk))
  obtain ⟨htransport1, htransport2⟩ := central_involution_section_principal_block_transport
    ideal t basisG principalG hprincipalG basisC principalC hprincipalC
  have hΘspan := htransport2 _ hθspan (hsuppG none)
  have hEspan := fun k : dihedralIndexSet M => htransport2 _ (hηspan k k.2) (hsuppG (some k))
  have hlabel : ∀ ξ : BlocksIrr G, ∃ ℓ : basisG.index,
      (basisG.representation ℓ).character = ξ := by
    intro ξ
    obtain ⟨data, hdata, hchar⟩ :=
      (Set.ext_iff.mp (blocksIrr_eq_irreducible_characters G) (ξ : G → ℂ)).mp ξ.2
    obtain ⟨ℓ, hℓ⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basisG data hdata
    exact ⟨ℓ, hℓ.trans hchar⟩
  have hcharirr : ∀ ℓ : basisG.index, (basisG.representation ℓ).character ∈ BlocksIrr G := by
    intro ℓ
    rw [blocksIrr_eq_irreducible_characters]
    exact ⟨_, basisG.irreducible ℓ, rfl⟩
  have hmemB0 : ∀ f : G → ℂ, f ∈ coefficientCharacterSpace basisG
      (coefficientBlock basisG (localizedComplexIntegerRing ideal) principalG) →
      ∀ ξ : BlocksIrr G, BlocksInnerProduct f ξ ≠ 0 → ∃ ℓ ∈ coefficientBlock basisG
        (localizedComplexIntegerRing ideal) principalG,
          (basisG.representation ℓ).character = ξ := by
    intro f hf ξ hne
    obtain ⟨ℓ, hℓ⟩ := hlabel ξ
    refine ⟨ℓ, ?_, hℓ⟩
    by_contra hnot
    have hzero := coefficientCharacterSpace_pairing_zero_outside basisG _ f hf ℓ hnot
    rw [hℓ, ← blocksInnerProduct_eq_characterPairing f (AddSubgroup.subset_closure ξ.2)] at hzero
    exact hne hzero
  have hδne : ∀ δ : ℤ, (δ = 1 ∨ δ = -1) → (δ : ℂ) ≠ 0 := by
    rintro δ (rfl | rfl) <;> norm_num
  have hΘχ₁ : BlocksInnerProduct (inducedFunction (Subgroup.centralizer {t})
      (dihedralTheta r s M ∘ π)) χ₁ = δ₁ := by
    rw [hΘpair]
    simp [c1χ₁, c12.symm, c13.symm]
  have hΘχ₂ : BlocksInnerProduct (inducedFunction (Subgroup.centralizer {t})
      (dihedralTheta r s M ∘ π)) χ₂ = δ₂ := by
    rw [hΘpair]
    simp [c1χ₂, c12, c23.symm]
  have hΘχ₃ : BlocksInnerProduct (inducedFunction (Subgroup.centralizer {t})
      (dihedralTheta r s M ∘ π)) χ₃ = δ₃ := by
    rw [hΘpair]
    simp [c1χ₃, c13, c23]
  have hEψ : ∀ k : dihedralIndexSet M, BlocksInnerProduct
      (inducedFunction (Subgroup.centralizer {t}) (dihedralEta r s M k ∘ π)) (ψ k) = ε := by
    intro k
    rw [hEpair]
    have hne : (χ₁ : G → ℂ) ≠ ψ k := fun h => cψχ₁ k h.symm
    simp [c1ψ k, hne]
  obtain ⟨ℓ₁, hℓ₁, hℓ₁c⟩ := hmemB0 _ hΘspan χ₁ (by rw [hΘχ₁]; exact hδne δ₁ hδ₁)
  obtain ⟨ℓ₂, hℓ₂, hℓ₂c⟩ := hmemB0 _ hΘspan χ₂ (by rw [hΘχ₂]; exact hδne δ₂ hδ₂)
  obtain ⟨ℓ₃, hℓ₃, hℓ₃c⟩ := hmemB0 _ hΘspan χ₃ (by rw [hΘχ₃]; exact hδne δ₃ hδ₃)
  have hψB0 : ∀ k, ∃ ℓ ∈ coefficientBlock basisG (localizedComplexIntegerRing ideal) principalG,
      (basisG.representation ℓ).character = ψ k :=
    fun k => hmemB0 _ (hEspan k) (ψ k) (by rw [hEψ k]; exact hδne ε hε)
  have hclassG : ∀ ℓ : basisG.index, BlocksIsClassFunction (basisG.representation ℓ).character :=
    fun ℓ g h => Representation.char_conj _ g h
  have hfU : ∀ ℓ ∈ coefficientBlock basisG (localizedComplexIntegerRing ideal) principalG,
      characterFunctionMask DC (fun x : Subgroup.centralizer {t} =>
        (basisG.representation ℓ).character x) ∈ sectionQuotientSpace π DC := by
    intro ℓ hℓ
    have hmask := htransport1 (basisG.representation ℓ).character (hclassG ℓ)
    rw [characterSubsetProjection_character basisG _ ℓ hℓ, ← hDCset] at hmask
    rw [hmask]
    obtain ⟨F, hF, hFeq⟩ := exists_inflation_of_mem_principal_span ideal π hπsurj hkerodd basisC
      principalC hprincipalC (characterSubsetProjection_mem basisC _ _)
    rw [hFeq]
    exact hmaskU F hF
  have hsec : ∀ ℓ ∈ coefficientBlock basisG (localizedComplexIntegerRing ideal) principalG,
      ∀ F : ↥(S : Subgroup G) → ℂ, BlocksIsClassFunction F →
      (∀ o, BlocksInnerProduct (fun x : Subgroup.centralizer {t} =>
          (basisG.representation ℓ).character x) (dihedralSectionFamily π r s M o) =
        BlocksInnerProduct (F ∘ π) (dihedralSectionFamily π r s M o)) →
      ∀ x : Subgroup.centralizer {t}, (x : G) ∈ centralInvolutionSection t →
        (basisG.representation ℓ).character x = F (π x) :=
    fun ℓ hℓ F hF hp x hx => eq_on_of_pairings π DC (dihedralSectionFamily π r s M) hspan hbsupp
      _ (hfU ℓ hℓ) F (hmaskU F hF) hp x ((hDCiff x).mpr hx)
  have hLHS : ∀ (ℓ : basisG.index) (o : Option (dihedralIndexSet M)),
      BlocksInnerProduct (fun x : Subgroup.centralizer {t} =>
          (basisG.representation ℓ).character x) (dihedralSectionFamily π r s M o) =
        starRingEnd ℂ (BlocksInnerProduct (inducedFunction (Subgroup.centralizer {t})
          (dihedralSectionFamily π r s M o)) (basisG.representation ℓ).character) := by
    intro ℓ o
    rw [blocksInnerProduct_comm,
      blocksInnerProduct_inducedFunction_left _ _ _ (hclassG ℓ)]
  have hclassφ : ∀ i : Fin 4, BlocksIsClassFunction (dihedralLinearCharacter r s M i) :=
    fun i => blocksIrr_isClassFunction (hφirr i)
  have hclassγ : ∀ k ∈ dihedralIndexSet M,
      BlocksIsClassFunction (dihedralRotationCharacter r s M k) :=
    fun k hk => blocksIrr_isClassFunction (hγirr k hk)
  have hsmulclass : ∀ (c : ℂ) (F : ↥(S : Subgroup G) → ℂ), BlocksIsClassFunction F →
      BlocksIsClassFunction (c • F) := by
    intro c F hF g h
    simp only [Pi.smul_apply, hF g h]
  have hconjint : ∀ z : ℤ, starRingEnd ℂ (z : ℂ) = z := fun z => map_intCast _ z
  have hvχ₁ : ∀ x : Subgroup.centralizer {t}, (x : G) ∈ centralInvolutionSection t →
      (χ₁ : G → ℂ) x = δ₁ * dihedralLinearCharacter r s M 1 (π x) := by
    intro x hx
    have h := hsec ℓ₁ hℓ₁ ((δ₁ : ℂ) • dihedralLinearCharacter r s M 1)
      (hsmulclass _ _ (hclassφ 1)) ?_ x hx
    · rw [hℓ₁c] at h
      simpa only [Pi.smul_apply, smul_eq_mul] using h
    intro o
    rw [hLHS, hℓ₁c]
    cases o with
    | none =>
      change starRingEnd ℂ (BlocksInnerProduct (inducedFunction (Subgroup.centralizer {t})
        (dihedralTheta r s M ∘ π)) χ₁) = BlocksInnerProduct
          (((δ₁ : ℂ) • dihedralLinearCharacter r s M 1) ∘ π) (dihedralTheta r s M ∘ π)
      rw [hΘχ₁, hinfl, blocksInnerProduct_left_smul, hφθ, hconjint]
      simp
    | some k =>
      change starRingEnd ℂ (BlocksInnerProduct (inducedFunction (Subgroup.centralizer {t})
        (dihedralEta r s M k ∘ π)) χ₁) = BlocksInnerProduct
          (((δ₁ : ℂ) • dihedralLinearCharacter r s M 1) ∘ π) (dihedralEta r s M k ∘ π)
      rw [hEpair, hinfl, blocksInnerProduct_left_smul, hφη 1 k k.2]
      have hne : (ψ k : G → ℂ) ≠ χ₁ := cψχ₁ k
      simp [c1χ₁, hne, hconjint]
  have hvχ₂₃ : ∀ (i : Fin 4) (χ : BlocksIrr G) (δ : ℤ) (ℓ : basisG.index),
      ℓ ∈ coefficientBlock basisG (localizedComplexIntegerRing ideal) principalG →
      (basisG.representation ℓ).character = χ → (i = 2 ∨ i = 3) →
      BlocksInnerProduct (inducedFunction (Subgroup.centralizer {t})
        (dihedralTheta r s M ∘ π)) χ = δ →
      (∀ k : dihedralIndexSet M, BlocksInnerProduct (inducedFunction (Subgroup.centralizer {t})
        (dihedralEta r s M k ∘ π)) χ = 0) →
      ∀ x : Subgroup.centralizer {t}, (x : G) ∈ centralInvolutionSection t →
        (χ : G → ℂ) x = -δ * dihedralLinearCharacter r s M i (π x) := by
    intro i χ δ ℓ hℓ hℓc hi hΘχ hEχ x hx
    have h := hsec ℓ hℓ ((-(δ : ℂ)) • dihedralLinearCharacter r s M i)
      (hsmulclass _ _ (hclassφ i)) ?_ x hx
    · rw [hℓc] at h
      simpa only [Pi.smul_apply, smul_eq_mul] using h
    intro o
    rw [hLHS, hℓc]
    cases o with
    | none =>
      change starRingEnd ℂ (BlocksInnerProduct (inducedFunction (Subgroup.centralizer {t})
        (dihedralTheta r s M ∘ π)) χ) = BlocksInnerProduct
          (((-(δ : ℂ)) • dihedralLinearCharacter r s M i) ∘ π) (dihedralTheta r s M ∘ π)
      rw [hΘχ, hinfl, blocksInnerProduct_left_smul, hφθ, hconjint]
      rcases hi with rfl | rfl <;> simp
    | some k =>
      change starRingEnd ℂ (BlocksInnerProduct (inducedFunction (Subgroup.centralizer {t})
        (dihedralEta r s M k ∘ π)) χ) = BlocksInnerProduct
          (((-(δ : ℂ)) • dihedralLinearCharacter r s M i) ∘ π) (dihedralEta r s M k ∘ π)
      rw [hEχ k, hinfl, blocksInnerProduct_left_smul, hφη i k k.2]
      rcases hi with rfl | rfl <;> simp
  have hEχ₂ : ∀ k : dihedralIndexSet M, BlocksInnerProduct (inducedFunction
      (Subgroup.centralizer {t}) (dihedralEta r s M k ∘ π)) χ₂ = 0 := by
    intro k
    rw [hEpair]
    simp [c1χ₂, c12, cψχ₂ k]
  have hEχ₃ : ∀ k : dihedralIndexSet M, BlocksInnerProduct (inducedFunction
      (Subgroup.centralizer {t}) (dihedralEta r s M k ∘ π)) χ₃ = 0 := by
    intro k
    rw [hEpair]
    simp [c1χ₃, c13, cψχ₃ k]
  have hvχ₂ := hvχ₂₃ 2 χ₂ δ₂ ℓ₂ hℓ₂ hℓ₂c (Or.inl rfl) hΘχ₂ hEχ₂
  have hvχ₃ := hvχ₂₃ 3 χ₃ δ₃ ℓ₃ hℓ₃ hℓ₃c (Or.inr rfl) hΘχ₃ hEχ₃
  have hvψ : ∀ l : dihedralIndexSet M, ∀ x : Subgroup.centralizer {t},
      (x : G) ∈ centralInvolutionSection t →
      (ψ l : G → ℂ) x = -ε * dihedralRotationCharacter r s M l (π x) := by
    intro l x hx
    obtain ⟨ℓ, hℓ, hℓc⟩ := hψB0 l
    have h := hsec ℓ hℓ ((-(ε : ℂ)) • dihedralRotationCharacter r s M l)
      (hsmulclass _ _ (hclassγ l l.2)) ?_ x hx
    · rw [hℓc] at h
      simpa only [Pi.smul_apply, smul_eq_mul] using h
    intro o
    rw [hLHS, hℓc]
    cases o with
    | none =>
      change starRingEnd ℂ (BlocksInnerProduct (inducedFunction (Subgroup.centralizer {t})
        (dihedralTheta r s M ∘ π)) (ψ l)) = BlocksInnerProduct
          (((-(ε : ℂ)) • dihedralRotationCharacter r s M l) ∘ π) (dihedralTheta r s M ∘ π)
      rw [hΘpair, hinfl, blocksInnerProduct_left_smul, hγθ l l.2]
      have hne₁ : (χ₁ : G → ℂ) ≠ ψ l := fun h => cψχ₁ l h.symm
      have hne₂ : (χ₂ : G → ℂ) ≠ ψ l := fun h => cψχ₂ l h.symm
      have hne₃ : (χ₃ : G → ℂ) ≠ ψ l := fun h => cψχ₃ l h.symm
      simp [c1ψ l, hne₁, hne₂, hne₃]
    | some k =>
      change starRingEnd ℂ (BlocksInnerProduct (inducedFunction (Subgroup.centralizer {t})
        (dihedralEta r s M k ∘ π)) (ψ l)) = BlocksInnerProduct
          (((-(ε : ℂ)) • dihedralRotationCharacter r s M l) ∘ π) (dihedralEta r s M k ∘ π)
      rw [hEpair, hinfl, blocksInnerProduct_left_smul, hγη l l.2 k k.2]
      have hne₁ : (χ₁ : G → ℂ) ≠ ψ l := fun h => cψχ₁ l h.symm
      by_cases hkl : k = l
      · subst hkl
        simp [c1ψ k, hne₁, hconjint]
      · have hkl' : (ψ k : G → ℂ) ≠ ψ l := fun h => hkl ((cψψ k l).mp h)
        have hlk : (l : ℤ) ≠ k := fun h => hkl (Subtype.ext h.symm)
        simp [c1ψ l, hne₁, hkl', hlk]
  have htord : orderOf t = 2 := by
    rw [ht, Subgroup.orderOf_coe, hhalf]
    exact hstruct.2.2.2.1.2.1
  have htD : t ∈ centralInvolutionSection t := by
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, ?_, ?_⟩
    · rw [htord]
      exact even_two
    · rw [htord]
      simp
  have htcent : t ∈ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [ht]
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp htS ⟨y, hy⟩))
  have htCmem : t ∈ Subgroup.centralizer {t} := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hπt : π ⟨t, htCmem⟩ = r ^ (M / 2) := by
    have heq : (⟨t, htCmem⟩ : Subgroup.centralizer {t}) = ι (r ^ (M / 2)) :=
      Subtype.ext hιt.symm
    rw [heq, hπι]
  have hexhaust : ∀ ℓ ∈ coefficientBlock basisG (localizedComplexIntegerRing ideal) principalG,
      (basisG.representation ℓ).character ∈
        ({1, (χ₁ : G → ℂ), (χ₂ : G → ℂ), (χ₃ : G → ℂ)} : Set (G → ℂ)) ∪
          Set.range (fun k => (ψ k : G → ℂ)) := by
    intro ℓ hℓ
    by_contra hnot
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range,
      not_or, not_exists] at hnot
    obtain ⟨⟨hn1, hnχ₁, hnχ₂, hnχ₃⟩, hnψ⟩ := hnot
    set ξ : BlocksIrr G := ⟨(basisG.representation ℓ).character, hcharirr ℓ⟩
    have hξc : (ξ : G → ℂ) = (basisG.representation ℓ).character := rfl
    have hzero := hsec ℓ hℓ 0 (fun _ _ => rfl) ?_ ⟨t, htCmem⟩ htD
    · exact CFSG.LyonsUnitaryFour.principal_block_character_ne_zero_of_centralizes_sylow basisG
        ideal 2 principalG
        hprincipalG ℓ hℓ S t htcent hzero
    intro o
    rw [hLHS]
    have hfun0 : ((0 : ↥(S : Subgroup G) → ℂ) ∘ π) = 0 := rfl
    rw [hfun0]
    have hzl : BlocksInnerProduct (0 : Subgroup.centralizer {t} → ℂ)
        (dihedralSectionFamily π r s M o) = 0 := by
      simp [BlocksInnerProduct]
    rw [hzl]
    cases o with
    | none =>
      change starRingEnd ℂ (BlocksInnerProduct (inducedFunction (Subgroup.centralizer {t})
        (dihedralTheta r s M ∘ π)) ξ) = 0
      rw [hΘpair]
      simp [Ne.symm hn1, Ne.symm hnχ₁, Ne.symm hnχ₂, Ne.symm hnχ₃, hξc]
    | some k =>
      change starRingEnd ℂ (BlocksInnerProduct (inducedFunction (Subgroup.centralizer {t})
        (dihedralEta r s M k ∘ π)) ξ) = 0
      rw [hEpair]
      have hk := hnψ k
      simp [Ne.symm hn1, Ne.symm hnχ₁, hξc, hk]
  have himage : (fun l => (basisG.representation l).character) ''
      (coefficientBlock basisG (localizedComplexIntegerRing ideal) principalG :
        Set basisG.index) =
      ({1, (χ₁ : G → ℂ), (χ₂ : G → ℂ), (χ₃ : G → ℂ)} : Set (G → ℂ)) ∪
        Set.range (fun k => (ψ k : G → ℂ)) := by
    ext f
    constructor
    · rintro ⟨ℓ, hℓ, rfl⟩
      exact hexhaust ℓ hℓ
    · intro hf
      rcases hf with hf | ⟨k, rfl⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
        rcases hf with rfl | rfl | rfl | rfl
        · exact ⟨principalG, coefficientBlock_self_mem basisG _ principalG, hprincipalG⟩
        · exact ⟨ℓ₁, hℓ₁, hℓ₁c⟩
        · exact ⟨ℓ₂, hℓ₂, hℓ₂c⟩
        · exact ⟨ℓ₃, hℓ₃, hℓ₃c⟩
      · obtain ⟨ℓ, hℓ, hℓc⟩ := hψB0 k
        exact ⟨ℓ, hℓ, hℓc⟩
  have hcardB0 : (coefficientBlock basisG (localizedComplexIntegerRing ideal) principalG).card =
      M / 2 + 3 := by
    have hcardI : Fintype.card (dihedralIndexSet M) = M / 2 - 1 := by
      have h := card_option_dihedralIndexSet hM2
      rw [Fintype.card_option] at h
      omega
    rw [card_eq_of_image_eq_four_union _ _ basisG.distinct _ _ _ _ _
      (fun k l h => hψ (Subtype.ext h)) c1χ₁ c1χ₂ c1χ₃ c12 c13 c23 c1ψ cψχ₁ cψχ₂ cψχ₃ himage,
      hcardI]
    omega
  have hφt : ∀ i : Fin 4, dihedralLinearCharacter r s M i (r ^ (M / 2)) =
      dihedralRotationSign i ^ (M / 2) := by
    intro i
    have h := (hφval i ((M / 2 : ℕ) : ℤ)).1
    rwa [zpow_natCast, zpow_natCast] at h
  have hζ : dihedralZeta M ^ (M / 2) = -1 := by
    have hprim := dihedralZeta_isPrimitiveRoot (M := M) (by omega)
    have h2 := hprim.pow_of_dvd (p := M / 2) (by omega) (Nat.div_dvd_of_dvd (even_iff_two_dvd.mp
      hEven))
    have hM2' : M / (M / 2) = 2 := by
      obtain ⟨m, hm⟩ := hEven
      rw [hm, show (m + m) / 2 = m by omega, show m + m = m * 2 by ring,
        Nat.mul_div_cancel_left _ (by omega)]
    rw [hM2'] at h2
    exact h2.eq_neg_one_of_two_right
  have hγt : ∀ k : ℤ, dihedralRotationCharacter r s M k (r ^ (M / 2)) = 2 * (-1) ^ k := by
    intro k
    have h := (hγval k ((M / 2 : ℕ) : ℤ)).1
    rw [zpow_natCast] at h
    rw [h, mul_comm k, zpow_mul, zpow_natCast, hζ, ← neg_mul, zpow_mul, zpow_neg, zpow_natCast,
      hζ, inv_neg_one]
    ring
  have hχ₁t : (χ₁ : G → ℂ) t = δ₁ := by
    have h := hvχ₁ ⟨t, htCmem⟩ htD
    rw [hπt, hφt] at h
    simpa [dihedralRotationSign] using h
  have hχ₂₃t : ∀ (i : Fin 4) (χ : BlocksIrr G) (δ : ℤ), (i = 2 ∨ i = 3) →
      (∀ x : Subgroup.centralizer {t}, (x : G) ∈ centralInvolutionSection t →
        (χ : G → ℂ) x = -δ * dihedralLinearCharacter r s M i (π x)) →
      (n = 2 → (χ : G → ℂ) t = δ) ∧ (3 ≤ n → (χ : G → ℂ) t = -δ) := by
    intro i χ δ hi hv
    have h := hv ⟨t, htCmem⟩ htD
    rw [hπt, hφt] at h
    have hsign : dihedralRotationSign i = -1 := by
      rcases hi with rfl | rfl <;> rfl
    rw [hsign] at h
    refine ⟨fun hn2 => ?_, fun hn3 => ?_⟩
    · have hM1 : M / 2 = 1 := by
        rw [hhalf, hn2]
        norm_num
      rw [hM1] at h
      simpa using h
    · have hev : Even (M / 2) := by
        rw [hhalf]
        exact Nat.even_pow.mpr ⟨even_two, by omega⟩
      rw [hev.neg_one_pow] at h
      simpa using h
  have hψt : ∀ k : dihedralIndexSet M, (ψ k : G → ℂ) t = -2 * ε * (-1) ^ (k : ℤ) := by
    intro k
    have h := hvψ k ⟨t, htCmem⟩ htD
    rw [hπt, hγt] at h
    change (ψ k : G → ℂ) t = _ at h
    rw [h]
    ring
  obtain ⟨hAL3, -, -⟩ := central_involution_section_induction_isometry t
  have hθvanish := (hAL3 (dihedralTheta r s M ∘ π) (hU none).1 (hsuppG none)).2.1
  have hηvanish := fun k : dihedralIndexSet M =>
    (hAL3 (dihedralEta r s M k ∘ π) (hU (some k)).1 (hsuppG (some k))).2.1
  have hoddout : ∀ y : G, Odd (orderOf y) →
      y ∉ ⋃ g : G, (fun z => g * z * g⁻¹) '' centralInvolutionSection t := by
    intro y hy hmem
    obtain ⟨g, z, hz, rfl⟩ := Set.mem_iUnion.mp hmem
    have hord : orderOf (g * z * g⁻¹) = orderOf z := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    rw [hord] at hy
    exact (Nat.not_even_iff_odd.mpr hy) hz.2.1
  have hodd : ∀ y : G, Odd (orderOf y) →
      1 + δ₁ * (χ₁ : G → ℂ) y + δ₂ * (χ₂ : G → ℂ) y + δ₃ * (χ₃ : G → ℂ) y = 0 ∧
      ∀ k : dihedralIndexSet M, 1 + δ₁ * (χ₁ : G → ℂ) y + ε * (ψ k : G → ℂ) y = 0 := by
    intro y hy
    refine ⟨?_, fun k => ?_⟩
    · have h := hθvanish y (hoddout y hy)
      rw [hΘ] at h
      simpa only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul] using h
    · have h := hηvanish k y (hoddout y hy)
      rw [hE k] at h
      simpa only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul] using h
  refine ⟨χ₁, χ₂, χ₃, δ₁, δ₂, δ₃, ε, ψ, h12, h13, h23, h1, h2, h3, hδ₁, hδ₂, hδ₃, hε, hψ,
    hψne, hΘ, hE, himage, hcardB0, fun x hx => ⟨hvχ₁ x hx, hvχ₂ x hx, hvχ₃ x hx,
      fun k => hvψ k x hx⟩, hχ₁t, ?_, ?_, hψt, hodd⟩
  · intro hn2
    exact ⟨(hχ₂₃t 2 χ₂ δ₂ (Or.inl rfl) hvχ₂).1 hn2, (hχ₂₃t 3 χ₃ δ₃ (Or.inr rfl) hvχ₃).1 hn2⟩
  · intro hn3
    exact ⟨(hχ₂₃t 2 χ₂ δ₂ (Or.inl rfl) hvχ₂).2 hn3, (hχ₂₃t 3 χ₃ δ₃ (Or.inr rfl) hvχ₃).2 hn3⟩

theorem dihedral_principal_block_exhaustion_and_section_values {G : Type} [Group G]
    [Fintype G] (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] {n M : ℕ} (hn : 2 ≤ n)
    (hM : M = 2 ^ (n - 1)) (S : Sylow 2 G)
    (hSiso : Nonempty (DihedralGroup M ≃* (S : Subgroup G))) (r s : (S : Subgroup G))
    (hr : orderOf r = M) (hs : orderOf s = 2) (hrel : s * r * s = r⁻¹)
    (hgen : Subgroup.closure {r, s} = ⊤) (t : G)
    (ht : t = ((r ^ (M / 2) : (S : Subgroup G)) : G)) (C : Subgroup G)
    (hC : C = Subgroup.centralizer {t}) (basisG : FiniteIrreducibleCharacterBasis G)
    (principalG : basisG.index)
    (hprincipalG : (basisG.representation principalG).character = 1) :
    (∃! R : Subgroup C, R.Normal ∧ Odd (Nat.card R) ∧ ∃ k : ℕ, R.index = 2 ^ k) ∧
    ∀ R : Subgroup C, R.Normal → Odd (Nat.card R) → (∃ k : ℕ, R.index = 2 ^ k) →
      (∃! π : C →* (S : Subgroup G), π.ker = R ∧
        ∀ (y : (S : Subgroup G)) (hy : (y : G) ∈ C), π ⟨y, hy⟩ = y) ∧
      ∀ π : C →* (S : Subgroup G), π.ker = R →
        (∀ (y : (S : Subgroup G)) (hy : (y : G) ∈ C), π ⟨y, hy⟩ = y) →
        ∃ (χ₁ χ₂ χ₃ : BlocksIrr G) (δ₁ δ₂ δ₃ ε : ℤ) (ψ : dihedralIndexSet M → BlocksIrr G),
          χ₁ ≠ χ₂ ∧ χ₁ ≠ χ₃ ∧ χ₂ ≠ χ₃ ∧
          (χ₁ : G → ℂ) ≠ 1 ∧ (χ₂ : G → ℂ) ≠ 1 ∧ (χ₃ : G → ℂ) ≠ 1 ∧
          (δ₁ = 1 ∨ δ₁ = -1) ∧ (δ₂ = 1 ∨ δ₂ = -1) ∧ (δ₃ = 1 ∨ δ₃ = -1) ∧ (ε = 1 ∨ ε = -1) ∧
          Function.Injective ψ ∧
          (∀ k, (ψ k : G → ℂ) ≠ 1 ∧ ψ k ≠ χ₁ ∧ ψ k ≠ χ₂ ∧ ψ k ≠ χ₃) ∧
          inducedFunction C (dihedralTheta r s M ∘ π) =
            1 + (δ₁ : ℂ) • (χ₁ : G → ℂ) + (δ₂ : ℂ) • (χ₂ : G → ℂ) + (δ₃ : ℂ) • (χ₃ : G → ℂ) ∧
          (∀ k : dihedralIndexSet M, inducedFunction C (dihedralEta r s M k ∘ π) =
            1 + (δ₁ : ℂ) • (χ₁ : G → ℂ) + (ε : ℂ) • (ψ k : G → ℂ)) ∧
          (fun l => (basisG.representation l).character) ''
              (coefficientBlock basisG (localizedComplexIntegerRing ideal) principalG :
                Set basisG.index) =
            {1, (χ₁ : G → ℂ), (χ₂ : G → ℂ), (χ₃ : G → ℂ)} ∪
              Set.range (fun k => (ψ k : G → ℂ)) ∧
          (coefficientBlock basisG (localizedComplexIntegerRing ideal) principalG).card =
            M / 2 + 3 ∧
          (∀ x : C, (x : G) ∈ centralInvolutionSection t →
            (χ₁ : G → ℂ) x = δ₁ * dihedralLinearCharacter r s M 1 (π x) ∧
            (χ₂ : G → ℂ) x = -δ₂ * dihedralLinearCharacter r s M 2 (π x) ∧
            (χ₃ : G → ℂ) x = -δ₃ * dihedralLinearCharacter r s M 3 (π x) ∧
            ∀ k : dihedralIndexSet M,
              (ψ k : G → ℂ) x = -ε * dihedralRotationCharacter r s M k (π x)) ∧
          (χ₁ : G → ℂ) t = δ₁ ∧
          (n = 2 → (χ₂ : G → ℂ) t = δ₂ ∧ (χ₃ : G → ℂ) t = δ₃) ∧
          (3 ≤ n → (χ₂ : G → ℂ) t = -δ₂ ∧ (χ₃ : G → ℂ) t = -δ₃) ∧
          (∀ k : dihedralIndexSet M, (ψ k : G → ℂ) t = -2 * ε * (-1) ^ (k : ℤ)) ∧
          ∀ y : G, Odd (orderOf y) →
            1 + δ₁ * (χ₁ : G → ℂ) y + δ₂ * (χ₂ : G → ℂ) y + δ₃ * (χ₃ : G → ℂ) y = 0 ∧
            ∀ k : dihedralIndexSet M, 1 + δ₁ * (χ₁ : G → ℂ) y + ε * (ψ k : G → ℂ) y = 0 := by
  obtain ⟨hR, hRall⟩ := dihedral_principal_induced_character_family hn hM S hSiso r s hr hs
    hrel hgen t ht C hC
  refine ⟨hR, fun R hRn hRodd hRidx => ⟨(hRall R hRn hRodd hRidx).1, fun π hker hid => ?_⟩⟩
  exact dihedral_principal_block_exhaustion_of_normalHall ideal hn hM S hSiso r s hr hs hrel hgen
    t ht C hC basisG principalG hprincipalG R hRodd hRidx π hker hid

end CFSG.Semidihedral.Principal
