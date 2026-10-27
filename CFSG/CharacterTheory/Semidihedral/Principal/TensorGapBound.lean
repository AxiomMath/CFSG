module

public import CFSG.CharacterTheory.TwoRankLowerBound.BlockSectionMask
public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterConjugateInverse

public noncomputable section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers

universe u w

section Constructions

variable {H : Type u} [Group H]

theorem exists_character_eq_zero :
    ∃ data : FiniteComplexRepresentation.{u, u} H, data.character = 0 :=
  ⟨{ vector := PUnit.{u + 1}, representation := Representation.trivial ℂ H PUnit.{u + 1} }, by
    funext h
    change LinearMap.trace ℂ PUnit.{u + 1} ((Representation.trivial ℂ H PUnit.{u + 1}) h) = 0
    rw [Subsingleton.elim ((Representation.trivial ℂ H PUnit.{u + 1}) h) 0, map_zero]⟩

theorem exists_character_eq_add (a b : FiniteComplexRepresentation.{u, u} H) :
    ∃ data : FiniteComplexRepresentation.{u, u} H, data.character = a.character + b.character :=
  ⟨{ vector := a.vector × b.vector
     representation := a.representation.prod b.representation }, by
    funext h
    simp only [FiniteComplexRepresentation.character, Representation.character, Pi.add_apply]
    exact LinearMap.trace_prodMap' _ _⟩

theorem exists_character_eq_mul_inv (a b : FiniteComplexRepresentation.{u, u} H) :
    ∃ data : FiniteComplexRepresentation.{u, u} H,
      ∀ h, data.character h = a.character h * b.character h⁻¹ :=
  ⟨{ vector := TensorProduct ℂ a.vector (Module.Dual ℂ b.vector)
     representation := a.representation.tprod b.representation.dual }, fun h => by
    simp only [FiniteComplexRepresentation.character]
    rw [Representation.char_tensor, Pi.mul_apply, Representation.char_dual]⟩

end Constructions

section Genuine

variable {H : Type u} [Group H] [Fintype H]

theorem characterPairing_basis_natural (basis : FiniteIrreducibleCharacterBasis H)
    (data : FiniteComplexRepresentation.{u, w} H) (χ : basis.index) :
    ∃ m : ℕ, characterPairing data.character (basis.representation χ).character = m := by
  obtain ⟨size, summand, hirr, hsum⟩ :=
    finiteComplexRepresentation_exists_irreducible_character_sum data
  have hfun : data.character = fun h => ∑ k, (1 : ℂ) * (summand k).character h := by
    funext h
    simp only [one_mul]
    exact hsum h
  refine ⟨(Finset.univ.filter fun k =>
    (summand k).character = (basis.representation χ).character).card, ?_⟩
  rw [hfun, characterPairing_expansion_left]
  simp only [one_mul]
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [characterPairing_irreducible _ _ (hirr k) (basis.irreducible χ)]
  split_ifs <;> simp

theorem character_eq_sum_multiplicity (basis : FiniteIrreducibleCharacterBasis H)
    (data : FiniteComplexRepresentation.{u, w} H) :
    data.character = ∑ χ, characterPairing data.character (basis.representation χ).character •
      (basis.representation χ).character := by
  funext h
  rw [finiteIrreducibleCharacterBasis_reconstruction basis data.character
    (fun x y => Representation.char_conj _ x y) h]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem finrank_eq_sum_multiplicity (basis : FiniteIrreducibleCharacterBasis H)
    (data : FiniteComplexRepresentation.{u, w} H) (m : basis.index → ℕ)
    (hm : ∀ χ, (m χ : ℂ) = characterPairing data.character (basis.representation χ).character) :
    Module.finrank ℂ data.vector =
      ∑ χ, m χ * Module.finrank ℂ (basis.representation χ).vector := by
  have h := congrFun (character_eq_sum_multiplicity basis data) 1
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← hm,
    FiniteComplexRepresentation.character, Representation.char_one] at h
  exact_mod_cast h

theorem characterPairing_sum_smul_basis (basis : FiniteIrreducibleCharacterBasis H)
    (a : basis.index → ℂ) (χ : basis.index) :
    characterPairing (∑ ψ, a ψ • (basis.representation ψ).character)
      (basis.representation χ).character = a χ := by
  have hfun : (∑ ψ, a ψ • (basis.representation ψ).character) =
      fun h => ∑ ψ, a ψ * (basis.representation ψ).character h := by
    funext h
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun, characterPairing_expansion_left]
  rw [Finset.sum_eq_single χ]
  · rw [characterPairing_irreducible _ _ (basis.irreducible χ) (basis.irreducible χ),
      ite_eq_left rfl, mul_one]
  · intro ψ _ hψ
    rw [characterPairing_irreducible _ _ (basis.irreducible ψ) (basis.irreducible χ),
      ite_eq_right (fun h => hψ (basis.distinct h)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ χ) h

theorem exists_character_eq_sum (basis : FiniteIrreducibleCharacterBasis H)
    (m : basis.index → ℕ) :
    ∃ data : FiniteComplexRepresentation.{u, u} H,
      data.character = ∑ χ, (m χ : ℂ) • (basis.representation χ).character := by
  have hsingle : ∀ (a : FiniteComplexRepresentation.{u, u} H) (n : ℕ),
      ∃ data : FiniteComplexRepresentation.{u, u} H, data.character = (n : ℂ) • a.character := by
    intro a n
    induction n with
    | zero =>
      obtain ⟨data, hdata⟩ := exists_character_eq_zero (H := H)
      exact ⟨data, by rw [hdata, Nat.cast_zero, zero_smul]⟩
    | succ n ih =>
      obtain ⟨data, hdata⟩ := ih
      obtain ⟨sum, hsum⟩ := exists_character_eq_add data a
      exact ⟨sum, by rw [hsum, hdata, Nat.cast_succ, add_smul, one_smul]⟩
  have hfinset : ∀ s : Finset basis.index, ∃ data : FiniteComplexRepresentation.{u, u} H,
      data.character = ∑ χ ∈ s, (m χ : ℂ) • (basis.representation χ).character := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨data, hdata⟩ := exists_character_eq_zero (H := H)
      exact ⟨data, by rw [hdata, Finset.sum_empty]⟩
    | insert χ s hχ ih =>
      obtain ⟨data, hdata⟩ := ih
      obtain ⟨single, hsingle⟩ := hsingle (basis.representation χ) (m χ)
      obtain ⟨sum, hsum⟩ := exists_character_eq_add single data
      exact ⟨sum, by rw [hsum, hsingle, hdata, Finset.sum_insert hχ]⟩
  exact hfinset Finset.univ

end Genuine


theorem primary_mul_regular_coprime_iff {G : Type*} [Group G] {p : ℕ} (x y : G) (n : ℕ)
    (hx : orderOf x ∣ p ^ n) (hy : Nat.Coprime p (orderOf y)) (hxy : Commute x y) :
    Nat.Coprime p (orderOf (x * y)) ↔ x = 1 := by
  have hcop : Nat.Coprime (orderOf x) (orderOf y) := Nat.Coprime.coprime_dvd_left hx (hy.pow_left n)
  rw [hxy.orderOf_mul_eq_mul_orderOf_of_coprime hcop, Nat.coprime_mul_iff_right]
  constructor
  · rintro ⟨hpx, -⟩
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (hpx.pow_left n).symm hx)
  · rintro rfl
    rw [orderOf_one]
    exact ⟨Nat.coprime_one_right p, hy⟩

theorem regularElements_primeSectionUnion {G : Type*} [Group G] (p : ℕ) :
    primeSectionUnion p {x : G | Nat.Coprime p (orderOf x)} := by
  intro x x' y y' n n' hx hx' hy hy' hxy hxy' hconj
  change Nat.Coprime p (orderOf (x * y)) ↔ Nat.Coprime p (orderOf (x' * y'))
  rw [primary_mul_regular_coprime_iff x y n hx hy hxy,
    primary_mul_regular_coprime_iff x' y' n' hx' hy' hxy']
  constructor
  · intro h
    exact isConj_one_right.mp (h ▸ hconj)
  · intro h
    exact isConj_one_left.mp (h ▸ hconj)

section Gap

variable {H : Type u} [Group H] [Fintype H]

theorem characterPairing_finset_sum_right (f : H → ℂ) {ι : Type*} (s : Finset ι) (a : ι → ℂ)
    (g : ι → H → ℂ) :
    characterPairing f (∑ i ∈ s, a i • g i) = ∑ i ∈ s, a i * characterPairing f (g i) := by
  unfold characterPairing
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

theorem principal_tensor_gap_bounds_singular_vanishing_character
    (basis : FiniteIrreducibleCharacterBasis H) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (d μ : ℝ) (_hd : 0 < d) (_hμ : 0 < μ)
    (hdeg : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      χ ≠ principal → d ≤ (Module.finrank ℂ (basis.representation χ).vector : ℝ))
    (hΞ : ∀ Ξ : FiniteComplexRepresentation.{u, u} H,
      (∀ χ, χ ∉ coefficientBlock basis (localizedComplexIntegerRing ideal) principal →
        characterPairing Ξ.character (basis.representation χ).character = 0) →
      characterPairing Ξ.character (basis.representation principal).character = 1 →
      (∀ x : H, p ∣ orderOf x → Ξ.character x = 0) →
      μ ≤ (Module.finrank ℂ Ξ.vector : ℝ))
    (Θ : FiniteComplexRepresentation.{u, w} H) (hΘ : Θ.character ≠ 0)
    (hΘvan : ∀ x : H, p ∣ orderOf x → Θ.character x = 0) :
    min μ (4 * d) ≤ (Module.finrank ℂ Θ.vector : ℝ) ^ 2 := by
  have hp : p.Prime := Fact.out
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hB
  set D : Set H := {x | Nat.Coprime p (orderOf x)} with hD
  have hsec : primeSectionUnion p D := regularElements_primeSectionUnion p
  have hDiff : ∀ x : H, x ∉ D ↔ p ∣ orderOf x := fun x => by
    simp only [hD, Set.mem_ofPred_eq, hp.coprime_iff_not_dvd, not_not]
  have hDinv : ∀ x : H, x⁻¹ ∈ D ↔ x ∈ D := fun x => by
    simp only [hD, Set.mem_ofPred_eq, orderOf_inv]
  have hprinB : principal ∈ B := coefficientBlock_self_mem _ _ _
  set deg : basis.index → ℕ := fun χ => Module.finrank ℂ (basis.representation χ).vector
    with hdegdef
  have horth : ∀ χ ψ : basis.index, characterPairing (basis.representation χ).character
      (basis.representation ψ).character = if χ = ψ then 1 else 0 := by
    intro χ ψ
    rw [characterPairing_irreducible _ _ (basis.irreducible χ) (basis.irreducible ψ)]
    by_cases h : χ = ψ
    · subst h
      simp
    · rw [ite_eq_right (fun hc => h (basis.distinct hc)), ite_eq_right h]
  have hprincipalPairing : ∀ (F : FiniteComplexRepresentation.{u, u} H) (i k : basis.index),
      (∀ x, F.character x = (basis.representation i).character x *
        (basis.representation k).character x⁻¹) →
      characterPairing F.character (basis.representation principal).character =
        characterPairing (basis.representation i).character (basis.representation k).character := by
    intro F i k hF
    rw [hprincipal]
    unfold characterPairing
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hF x, Pi.one_apply, mul_one]
  have hdimProduct : ∀ (F : FiniteComplexRepresentation.{u, u} H) (i k : basis.index),
      (∀ x, F.character x = (basis.representation i).character x *
        (basis.representation k).character x⁻¹) →
      Module.finrank ℂ F.vector = deg i * deg k := by
    intro F i k hF
    have h := hF 1
    rw [inv_one] at h
    simp only [FiniteComplexRepresentation.character, Representation.char_one] at h
    simp only [hdegdef]
    exact_mod_cast h
  choose c hc using characterPairing_basis_natural basis Θ
  have hc' : ∀ χ, (c χ : ℂ) = characterPairing Θ.character (basis.representation χ).character :=
    fun χ => (hc χ).symm
  have hdimΘ := finrank_eq_sum_multiplicity basis Θ c hc'
  have hΘsum := character_eq_sum_multiplicity basis Θ
  obtain ⟨j₀, hj₀⟩ : ∃ j, c j ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hΘ
    rw [hΘsum]
    simp [← hc', hall]
  have hdeg_le : ∀ j, c j ≠ 0 → deg j ≤ Module.finrank ℂ Θ.vector := by
    intro j hj
    rw [hdimΘ]
    calc deg j ≤ c j * deg j := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hj)
      _ ≤ ∑ χ, c χ * deg χ :=
        Finset.single_le_sum (f := fun χ => c χ * deg χ) (fun χ _ => Nat.zero_le _)
          (Finset.mem_univ j)
  by_cases hcase : ∃ j, c j ≠ 0 ∧
      ∀ x : H, p ∣ orderOf x → (basis.representation j).character x = 0
  ·
    obtain ⟨j, hcj, hjvan⟩ := hcase
    obtain ⟨f, hf⟩ := exists_character_eq_mul_inv (basis.representation j) (basis.representation j)
    choose m hm using characterPairing_basis_natural basis f
    have hm' : ∀ χ, (m χ : ℂ) = characterPairing f.character (basis.representation χ).character :=
      fun χ => (hm χ).symm
    set a : basis.index → ℕ := fun χ => if χ ∈ B then m χ else 0 with ha
    obtain ⟨Ξ, hΞchar⟩ := exists_character_eq_sum basis a
    have hΞpair : ∀ χ, characterPairing Ξ.character (basis.representation χ).character =
        (a χ : ℂ) := fun χ => by
      rw [hΞchar]
      exact characterPairing_sum_smul_basis basis _ χ
    have hΞP : Ξ.character = characterSubsetProjection basis B f.character := by
      rw [hΞchar]
      change _ = ∑ χ ∈ B, characterPairing f.character (basis.representation χ).character •
        (basis.representation χ).character
      have hterm : ∀ χ, ((a χ : ℕ) : ℂ) • (basis.representation χ).character =
          if χ ∈ B then characterPairing f.character (basis.representation χ).character •
            (basis.representation χ).character else 0 := by
        intro χ
        simp only [ha]
        split_ifs with hχ
        · rw [hm']
        · rw [Nat.cast_zero, zero_smul]
      simp_rw [hterm]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    have hfmask : characterFunctionMask D f.character = f.character := by
      funext x
      simp only [characterFunctionMask]
      split_ifs with hx
      · rfl
      · rw [hf x, hjvan x ((hDiff x).mp hx), zero_mul]
    have h1 : ∀ χ, χ ∉ B → characterPairing Ξ.character (basis.representation χ).character = 0 :=
      fun χ hχ => by rw [hΞpair χ, ha]; simp [hχ]
    have h2 : characterPairing Ξ.character (basis.representation principal).character = 1 := by
      rw [hΞpair principal, ha]
      simp only [hprinB, ite_true]
      rw [hm', hprincipalPairing f j j hf, horth, ite_eq_left rfl]
    have h3 : ∀ x : H, p ∣ orderOf x → Ξ.character x = 0 := by
      intro x hx
      rw [hΞP, ← hfmask, coefficientBlock_section_mask_commute basis ideal p principal D hsec,
        characterFunctionMask, ite_eq_right ((hDiff x).mpr hx)]
    have hμle := hΞ Ξ h1 h2 h3
    have hdimΞ := finrank_eq_sum_multiplicity basis Ξ a fun χ => (hΞpair χ).symm
    have hdimf := finrank_eq_sum_multiplicity basis f m hm'
    have hfdeg := hdimProduct f j j hf
    have hle : Module.finrank ℂ Ξ.vector ≤ deg j * deg j := by
      rw [hdimΞ, ← hfdeg, hdimf]
      refine Finset.sum_le_sum fun χ _ => Nat.mul_le_mul_right _ ?_
      simp only [ha]
      split_ifs <;> omega
    have hjΘ := hdeg_le j hcj
    have hsq : (Module.finrank ℂ Ξ.vector : ℝ) ≤ (Module.finrank ℂ Θ.vector : ℝ) ^ 2 := by
      have : Module.finrank ℂ Ξ.vector ≤ Module.finrank ℂ Θ.vector ^ 2 := by
        calc Module.finrank ℂ Ξ.vector ≤ deg j * deg j := hle
          _ ≤ Module.finrank ℂ Θ.vector * Module.finrank ℂ Θ.vector :=
            Nat.mul_le_mul hjΘ hjΘ
          _ = Module.finrank ℂ Θ.vector ^ 2 := (sq _).symm
      exact_mod_cast this
    exact (min_le_left _ _).trans (hμle.trans hsq)
  ·
    push Not at hcase
    obtain ⟨x₀, hx₀p, hx₀⟩ := hcase j₀ hj₀
    set E : Set H := {x | p ∣ orderOf x} with hEdef
    set X : basis.index → ℂ := fun i => characterPairing
      (characterFunctionMask E (basis.representation i).character)
      (basis.representation j₀).character with hX
    have hXpos : 0 < (X j₀).re :=
      characterPairing_mask_character_pos E (basis.representation j₀) ⟨x₀, hx₀p, hx₀⟩
    have hsum0 : ∑ i, (c i : ℂ) * X i = 0 := by
      have hmaskΘ : characterFunctionMask E Θ.character = 0 := by
        funext x
        simp only [characterFunctionMask, Pi.zero_apply]
        split_ifs with hx
        · exact hΘvan x hx
        · rfl
      have hmask_sum : characterFunctionMask E Θ.character = fun x =>
          ∑ i, (c i : ℂ) * characterFunctionMask E (basis.representation i).character x := by
        funext x
        rw [hΘsum]
        simp only [characterFunctionMask, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← hc']
        split_ifs <;> simp
      have hpair := congrArg (fun F => characterPairing F (basis.representation j₀).character)
        hmask_sum
      rw [characterPairing_expansion_left, hmaskΘ] at hpair
      rw [← hpair]
      unfold characterPairing
      simp
    obtain ⟨i, hij, hci, hXi⟩ : ∃ i, i ≠ j₀ ∧ c i ≠ 0 ∧ X i ≠ 0 := by
      by_contra hnone
      push Not at hnone
      have hsingle : ∑ i, (c i : ℂ) * X i = (c j₀ : ℂ) * X j₀ := by
        rw [Finset.sum_eq_single j₀]
        · intro i _ hi
          by_cases hci : c i = 0
          · rw [hci, Nat.cast_zero, zero_mul]
          · rw [hnone i hi hci, mul_zero]
        · intro h
          exact absurd (Finset.mem_univ j₀) h
      rw [hsingle] at hsum0
      have hre : 0 < ((c j₀ : ℂ) * X j₀).re := by
        rw [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
        exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hj₀) hXpos
      rw [hsum0, Complex.zero_re] at hre
      exact lt_irrefl _ hre
    obtain ⟨F, hF⟩ := exists_character_eq_mul_inv (basis.representation i) (basis.representation j₀)
    choose mF hmF using characterPairing_basis_natural basis F
    have hmF' : ∀ χ, (mF χ : ℂ) = characterPairing F.character (basis.representation χ).character :=
      fun χ => (hmF χ).symm
    have hFD : characterPairing F.character (characterFunctionMask D 1) = -X i := by
      have e1 : characterPairing F.character (characterFunctionMask D 1) =
          characterPairing (characterFunctionMask D (basis.representation i).character)
            (basis.representation j₀).character := by
        unfold characterPairing
        congr 1
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hF x]
        simp only [characterFunctionMask, Pi.one_apply]
        by_cases hx : x ∈ D
        · rw [ite_eq_left ((hDinv x).mpr hx), ite_eq_left hx, mul_one]
        · rw [ite_eq_right (fun h => hx ((hDinv x).mp h)), ite_eq_right hx, mul_zero, zero_mul]
      have e2 : characterPairing (characterFunctionMask D (basis.representation i).character)
          (basis.representation j₀).character + X i =
          characterPairing (basis.representation i).character
            (basis.representation j₀).character := by
        simp only [hX]
        unfold characterPairing
        rw [← mul_add, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [characterFunctionMask]
        by_cases hx : x ∈ D
        · have hxE : x ∉ E := fun h => ((hDiff x).mpr h) hx
          rw [ite_eq_left hx, ite_eq_right hxE]
          ring
        · have hxE : x ∈ E := (hDiff x).mp hx
          rw [ite_eq_right hx, ite_eq_left hxE]
          ring
      have e3 := horth i j₀
      rw [ite_eq_right hij] at e3
      rw [e1]
      linear_combination e2 + e3
    have hDmem : characterFunctionMask D 1 ∈ coefficientCharacterSpace basis B := by
      have h1mem : (1 : H → ℂ) ∈ coefficientCharacterSpace basis B := by
        rw [← hprincipal]
        exact Submodule.subset_span ⟨principal, hprinB, rfl⟩
      exact coefficientBlock_section_mask_mem basis ideal p principal D hsec 1 h1mem
    obtain ⟨χ, hχB, hχne, hmχ⟩ : ∃ χ ∈ B, χ ≠ principal ∧ mF χ ≠ 0 := by
      by_contra hnone
      push Not at hnone
      have hzero : ∀ χ ∈ B,
          characterPairing F.character (basis.representation χ).character = 0 := by
        intro χ hχ
        by_cases hχp : χ = principal
        · rw [hχp, hprincipalPairing F i j₀ hF, horth, ite_eq_right hij]
        · rw [← hmF', hnone χ hχ hχp, Nat.cast_zero]
      have hexp := characterSubsetProjection_identity basis B _ hDmem
      have hpair : characterPairing F.character (characterFunctionMask D 1) = 0 := by
        rw [← hexp]
        change characterPairing F.character (∑ χ ∈ B, characterPairing (characterFunctionMask D 1)
          (basis.representation χ).character • (basis.representation χ).character) = 0
        rw [characterPairing_finset_sum_right]
        exact Finset.sum_eq_zero fun χ hχ => by rw [hzero χ hχ, mul_zero]
      rw [hFD, neg_eq_zero] at hpair
      exact hXi hpair
    have hdχ := hdeg χ hχB hχne
    have hdimF := finrank_eq_sum_multiplicity basis F mF hmF'
    have hFdeg := hdimProduct F i j₀ hF
    have hχF : deg χ ≤ deg i * deg j₀ := by
      rw [← hFdeg, hdimF]
      calc deg χ ≤ mF χ * deg χ := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hmχ)
        _ ≤ ∑ ψ, mF ψ * deg ψ :=
          Finset.single_le_sum (f := fun ψ => mF ψ * deg ψ) (fun ψ _ => Nat.zero_le _)
            (Finset.mem_univ χ)
    have hpairΘ : deg i + deg j₀ ≤ Module.finrank ℂ Θ.vector := by
      rw [hdimΘ]
      calc deg i + deg j₀ ≤ c i * deg i + c j₀ * deg j₀ :=
            Nat.add_le_add (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hci))
              (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hj₀))
        _ = ∑ ψ ∈ {i, j₀}, c ψ * deg ψ := (Finset.sum_pair (f := fun ψ => c ψ * deg ψ) hij).symm
        _ ≤ ∑ ψ, c ψ * deg ψ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun ψ _ _ => Nat.zero_le _
    have hdR : d ≤ (deg i : ℝ) * deg j₀ := by
      have : (deg χ : ℝ) ≤ (deg i : ℝ) * deg j₀ := by exact_mod_cast hχF
      exact hdχ.trans this
    have hΘR : ((deg i : ℝ) + deg j₀) ≤ Module.finrank ℂ Θ.vector := by exact_mod_cast hpairΘ
    have h4 : 4 * d ≤ (Module.finrank ℂ Θ.vector : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((deg i : ℝ) - deg j₀), sq_nonneg ((deg i : ℝ) + deg j₀),
        (Nat.cast_nonneg (deg i) : (0 : ℝ) ≤ deg i), (Nat.cast_nonneg (deg j₀) : (0 : ℝ) ≤ deg j₀)]
    exact (min_le_right _ _).trans h4

end Gap

end CFSG.Semidihedral.Principal
