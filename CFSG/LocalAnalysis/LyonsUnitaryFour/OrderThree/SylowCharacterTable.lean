module

public import CFSG.CharacterTheory.Blocks.CharacterCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementBlock
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.ProductCharacterFormula
public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderFourCentralizer

public section

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical

structure UnitaryFourSylowShape (S : Type*) [Group S] : Prop where
  card : Nat.card S = 64
  center_eq_commutator : Subgroup.center S = commutator S
  sq_eq_one_iff : ∀ y : S, y ^ 2 = 1 ↔ y ∈ Subgroup.center S
  sq_mem_center : ∀ y : S, y ^ 2 ∈ Subgroup.center S
  card_center : Nat.card (Subgroup.center S) = 4
  card_centralizer : ∀ x : S, x ∉ Subgroup.center S → Nat.card (Subgroup.centralizer {x}) = 16

section Shape

variable {S : Type*} [Group S] [Finite S]

theorem UnitaryFourSylowShape.isConj_iff_mul_center (h : UnitaryFourSylowShape S) (x : S)
    (hx : x ∉ Subgroup.center S) (y : S) :
    IsConj x y ↔ ∃ z ∈ Subgroup.center S, y = x * z := by
  let := Fintype.ofFinite S
  have hsub : ∀ y, IsConj x y → ∃ z ∈ Subgroup.center S, y = x * z := by
    intro y hy
    obtain ⟨g, rfl⟩ := _root_.isConj_iff.mp hy
    refine ⟨x⁻¹ * g * x * g⁻¹, ?_, by group⟩
    rw [h.center_eq_commutator, commutator_def]
    have := Subgroup.commutator_mem_commutator (Subgroup.mem_top x⁻¹) (Subgroup.mem_top g)
    rwa [commutatorElement_def, inv_inv] at this
  constructor
  · exact hsub y
  ·
    let A : Finset S := conjClassFinset x
    let B : Finset S := Finset.univ.filter (fun y => ∃ z ∈ Subgroup.center S, y = x * z)
    have hAB : A ⊆ B := by
      intro y hy
      simp only [A, conjClassFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hsub y hy
    have hAcard : A.card = 4 := by
      have hc := card_conjClassFinset_mul x
      rw [h.card_centralizer x hx, h.card] at hc
      have : (A.card : ℂ) = 4 := by
        have h16 : (16 : ℂ) ≠ 0 := by norm_num
        have := hc
        field_simp at this
        linear_combination this / 16
      exact_mod_cast this
    have hBcard : B.card = 4 := by
      have hB : B = (Subgroup.center S : Set S).toFinset.image (fun z => x * z) := by
        ext y
        simp only [B, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
          Set.mem_toFinset, SetLike.mem_coe]
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact ⟨z, hz, rfl⟩
        · rintro ⟨z, hz, rfl⟩
          exact ⟨z, hz, rfl⟩
      rw [hB, Finset.card_image_of_injective _ (mul_right_injective x), Set.toFinset_card,
        ← Nat.card_eq_fintype_card]
      exact h.card_center
    have hAeqB : A = B := Finset.eq_of_subset_of_card_le hAB (by rw [hAcard, hBcard])
    intro hy
    have hyB : y ∈ B := by
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hy
    rw [← hAeqB] at hyB
    simpa [A, conjClassFinset] using hyB

end Shape

section CentralCharacter

variable {S : Type*} [Group S]

theorem irreducible_central_smul (data : FiniteComplexRepresentation S)
    (hirr : data.IsIrreducible) (z : S) (hz : z ∈ Subgroup.center S) :
    data.representation z = (data.character z / data.character 1) • (1 : Module.End ℂ _) := by
  let : data.representation.IsIrreducible := hirr
  have hdegree := irreducible_character_degree_ne_zero data hirr
  have hinv : ∀ (conjugator element : S),
      element ∈ ({z} : Finset S) ↔ conjugator * element * conjugator⁻¹ ∈ ({z} : Finset S) := by
    intro conjugator element
    simp only [Finset.mem_singleton]
    constructor
    · rintro rfl
      rw [Subgroup.mem_center_iff.mp hz conjugator, mul_inv_cancel_right]
    · intro h'
      have h'' : conjugator * element * conjugator⁻¹ = conjugator * z * conjugator⁻¹ := by
        rw [h', Subgroup.mem_center_iff.mp hz conjugator, mul_inv_cancel_right]
      simpa using h''
  have h := irreducible_conjugacy_class_sum data.representation z {z} hinv
    (fun element helement => by rw [Finset.mem_singleton] at helement; rw [helement]) hdegree
  simpa using h

@[expose] noncomputable def centralCharacter (data : FiniteComplexRepresentation S)
    (hirr : data.IsIrreducible) : Subgroup.center S →* ℂ where
  toFun z := data.character z / data.character 1
  map_one' := div_self (irreducible_character_degree_ne_zero data hirr)
  map_mul' z w := by
    have hdeg := irreducible_character_degree_ne_zero data hirr
    have h1 : data.character ((z * w : Subgroup.center S) : S) =
        data.character z / data.character 1 * (data.character w / data.character 1) *
          data.character 1 := by
      change LinearMap.trace ℂ _ (data.representation (z * w)) = _
      rw [map_mul, irreducible_central_smul data hirr z z.property,
        irreducible_central_smul data hirr w w.property, smul_mul_smul, one_mul, map_smul,
        LinearMap.trace_one, smul_eq_mul]
      congr 1
      rw [FiniteComplexRepresentation.character, Representation.char_one]
    rw [h1]
    field_simp

theorem centralCharacter_apply (data : FiniteComplexRepresentation S)
    (hirr : data.IsIrreducible) (z : Subgroup.center S) :
    centralCharacter data hirr z = data.character z / data.character 1 := rfl

theorem character_central_eq (data : FiniteComplexRepresentation S) (hirr : data.IsIrreducible)
    (z : Subgroup.center S) :
    data.character z = data.character 1 * centralCharacter data hirr z := by
  have hdeg := irreducible_character_degree_ne_zero data hirr
  rw [centralCharacter_apply]
  field_simp

theorem character_mul_central (data : FiniteComplexRepresentation S) (hirr : data.IsIrreducible)
    (x : S) (z : Subgroup.center S) :
    data.character (x * z) = centralCharacter data hirr z * data.character x := by
  change LinearMap.trace ℂ _ (data.representation (x * z)) =
    centralCharacter data hirr z * LinearMap.trace ℂ _ (data.representation x)
  rw [map_mul, irreducible_central_smul data hirr z z.property, mul_smul_comm, mul_one,
    map_smul, smul_eq_mul, centralCharacter_apply]

theorem centralCharacter_sq (data : FiniteComplexRepresentation S) (hirr : data.IsIrreducible)
    (z : Subgroup.center S) (hz : (z : S) ^ 2 = 1) :
    centralCharacter data hirr z = 1 ∨ centralCharacter data hirr z = -1 := by
  have h : centralCharacter data hirr z ^ 2 = 1 := by
    rw [← map_pow]
    have : z ^ 2 = 1 := Subtype.ext (by simpa using hz)
    rw [this, map_one]
  rw [pow_two] at h
  exact mul_self_eq_one_iff.mp h

end CentralCharacter

section Fibers

variable {S : Type*} [Group S] [Finite S]

theorem UnitaryFourSylowShape.character_eq_zero_of_central (h : UnitaryFourSylowShape S)
    (data : FiniteComplexRepresentation S) (hirr : data.IsIrreducible)
    (hne : centralCharacter data hirr ≠ 1) (x : S) (hx : x ∉ Subgroup.center S) :
    data.character x = 0 := by
  obtain ⟨e, he⟩ : ∃ e, centralCharacter data hirr e ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hne (MonoidHom.ext fun z => by simpa using hall z)
  have he1 : centralCharacter data hirr e = -1 :=
    (centralCharacter_sq data hirr e ((h.sq_eq_one_iff e).mpr e.property)).resolve_left he
  have hconj : IsConj x (x * e) := (h.isConj_iff_mul_center x hx (x * e)).mpr ⟨e, e.property, rfl⟩
  have hval : data.character (x * e) = data.character x := by
    obtain ⟨c, hc⟩ := _root_.isConj_iff.mp hconj
    rw [← hc]
    exact Representation.char_conj _ x c
  rw [character_mul_central data hirr x e, he1] at hval
  linear_combination -hval / 2

theorem UnitaryFourSylowShape.finrank_eq_four_of_central (h : UnitaryFourSylowShape S)
    (data : FiniteComplexRepresentation S) (hirr : data.IsIrreducible)
    (hne : centralCharacter data hirr ≠ 1) : Module.finrank ℂ data.vector = 4 := by
  let := Fintype.ofFinite S
  have hpair := characterPairing_irreducible data data hirr hirr
  rw [ite_eq_left rfl] at hpair
  unfold characterPairing at hpair
  have hsplit : ∑ s : S, data.character s * data.character s⁻¹ =
      ∑ s ∈ Finset.univ.filter (· ∈ Subgroup.center S), data.character s * data.character s⁻¹ := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ Subgroup.center S)]
    rw [Finset.sum_eq_zero (s := Finset.univ.filter (fun s => ¬ s ∈ Subgroup.center S)),
      add_zero]
    intro s hs
    rw [Finset.mem_filter] at hs
    rw [h.character_eq_zero_of_central data hirr hne s hs.2, zero_mul]
  have hcenter : ∀ s ∈ Finset.univ.filter (· ∈ Subgroup.center S),
      data.character s * data.character s⁻¹ = data.character 1 ^ 2 := by
    intro s hs
    rw [Finset.mem_filter] at hs
    have h1 := character_central_eq data hirr ⟨s, hs.2⟩
    have h2 := character_central_eq data hirr ⟨s, hs.2⟩⁻¹
    simp only [Subgroup.coe_inv] at h1 h2
    rw [h1, h2, ← mul_mul_mul_comm, ← map_mul, mul_inv_cancel, map_one, mul_one, pow_two]
  rw [hsplit, Finset.sum_congr rfl hcenter, Finset.sum_const] at hpair
  have hcardZ : (Finset.univ.filter (· ∈ Subgroup.center S)).card = 4 := by
    rw [← h.card_center, Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  rw [hcardZ, h.card, nsmul_eq_mul] at hpair
  have hdim : data.character 1 = (Module.finrank ℂ data.vector : ℂ) := by
    rw [FiniteComplexRepresentation.character, Representation.char_one]
  rw [hdim] at hpair
  have hsq : ((Module.finrank ℂ data.vector : ℂ)) ^ 2 = 16 := by
    have := hpair
    field_simp at this
    linear_combination this / 4
  have hsqN : Module.finrank ℂ data.vector ^ 2 = 4 ^ 2 := by exact_mod_cast hsq
  exact Nat.pow_left_injective (by norm_num) hsqN

omit [Finite S] in
theorem finrank_eq_one_of_commutator_trivial (data : FiniteComplexRepresentation S)
    (hirr : data.IsIrreducible)
    (hcomm : ∀ g h : S, data.representation g * data.representation h =
      data.representation h * data.representation g) :
    Module.finrank ℂ data.vector = 1 := by
  let : data.representation.IsIrreducible := hirr
  have hscalar : ∀ g : S, ∃ c : ℂ, data.representation g = c • (1 : Module.End ℂ data.vector) := by
    intro g
    let f : data.representation.IntertwiningMap data.representation :=
      { toLinearMap := data.representation g
        isIntertwining' := fun h => hcomm g h }
    obtain ⟨c, hc⟩ :=
      Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed.2 f
    refine ⟨c, ?_⟩
    have hequal := congrArg Representation.IntertwiningMap.toLinearMap hc
    rw [Representation.IntertwiningMap.algebraMap_apply,
      Representation.IntertwiningMap.toLinearMap_smul] at hequal
    have hone : (1 : data.representation.IntertwiningMap data.representation).toLinearMap =
        (1 : Module.End ℂ data.vector) := by
      ext v
      exact congrFun (Representation.IntertwiningMap.coe_one data.representation) v
    erw [hone] at hequal
    exact hequal.symm
  have hnt : Nontrivial data.vector := by
    have hdeg := irreducible_character_degree_ne_zero data hirr
    rw [FiniteComplexRepresentation.character, Representation.char_one] at hdeg
    exact Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero (by exact_mod_cast hdeg))
  obtain ⟨v, hv⟩ := exists_ne (0 : data.vector)
  let W : Subrepresentation data.representation :=
    { toSubmodule := ℂ ∙ v
      apply_mem_toSubmodule := by
        intro g w hw
        obtain ⟨c, hc⟩ := hscalar g
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
        rw [hc]
        simp only [LinearMap.smul_apply, Module.End.one_apply, smul_smul]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v) }
  have hW : W ≠ ⊥ := by
    intro hbot
    apply hv
    have hmem : v ∈ W.toSubmodule := Submodule.mem_span_singleton_self v
    rw [hbot] at hmem
    exact hmem
  have hWtop : W = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W).resolve_left hW
  have hspan : (ℂ ∙ v) = ⊤ := by
    have := congrArg Subrepresentation.toSubmodule hWtop
    exact this
  rw [← finrank_top ℂ data.vector, ← hspan, finrank_span_singleton hv]

omit [Finite S] in
theorem UnitaryFourSylowShape.finrank_eq_one_of_central (h : UnitaryFourSylowShape S)
    (data : FiniteComplexRepresentation S) (hirr : data.IsIrreducible)
    (htriv : centralCharacter data hirr = 1) : Module.finrank ℂ data.vector = 1 := by
  have hZ : ∀ z ∈ Subgroup.center S, data.representation z = 1 := by
    intro z hz
    rw [irreducible_central_smul data hirr z hz]
    have := congrArg (fun f => f ⟨z, hz⟩) htriv
    simp only [MonoidHom.one_apply, centralCharacter_apply] at this
    rw [this, one_smul]
  apply finrank_eq_one_of_commutator_trivial data hirr
  intro g k
  have hcomm : g⁻¹ * k⁻¹ * g * k ∈ Subgroup.center S := by
    rw [h.center_eq_commutator, commutator_def]
    have := Subgroup.commutator_mem_commutator (Subgroup.mem_top g⁻¹) (Subgroup.mem_top k⁻¹)
    rwa [commutatorElement_def, inv_inv, inv_inv] at this
  have hgk : g * k = k * g * (g⁻¹ * k⁻¹ * g * k) := by group
  rw [← map_mul, ← map_mul, hgk, map_mul, hZ _ hcomm, mul_one]

end Fibers


section Signs

@[expose] noncomputable def signHom {A : Type*} [Group A] (l : A →* ℤˣ) : A →* ℂ :=
  (Int.castRingHom ℂ).toMonoidHom.comp ((Units.coeHom ℤ).comp l)

theorem signHom_apply {A : Type*} [Group A] (l : A →* ℤˣ) (a : A) :
    signHom l a = (((l a : ℤˣ) : ℤ) : ℂ) := rfl

theorem signHom_cases {A : Type*} [Group A] (l : A →* ℤˣ) (a : A) :
    signHom l a = 1 ∨ signHom l a = -1 := by
  rcases Int.units_eq_one_or (l a) with h | h <;> simp [signHom_apply, h]

theorem signHom_injective {A : Type*} [Group A] : Function.Injective (signHom (A := A)) := by
  intro l l' h
  ext a
  have := congrArg (fun f : A →* ℂ => f a) h
  simp only [signHom_apply] at this
  exact_mod_cast this

theorem exists_signHom_eq {A : Type*} [Group A] (ν : A →* ℂ)
    (hν : ∀ a, ν a = 1 ∨ ν a = -1) : ∃ l : A →* ℤˣ, signHom l = ν := by
  have hne : (-1 : ℂ) ≠ 1 := by norm_num
  let l : A →* ℤˣ :=
    { toFun := fun a => if ν a = 1 then 1 else -1
      map_one' := by simp
      map_mul' := by
        intro a b
        rw [map_mul]
        rcases hν a with ha | ha <;> rcases hν b with hb | hb <;> simp [ha, hb, hne] }
  refine ⟨l, ?_⟩
  ext a
  rw [signHom_apply]
  rcases hν a with ha | ha <;> simp [l, ha, hne]

theorem sum_signHom_mul {A : Type*} [Group A] [Fintype A] (l : A →* ℤˣ) (ν : A →* ℂ) :
    ∑ a, signHom l a * ν a = if ν = signHom l then (Fintype.card A : ℂ) else 0 := by
  by_cases heq : ν = signHom l
  · rw [ite_eq_left heq, heq]
    rw [Finset.sum_congr rfl (fun a _ => by
      rcases signHom_cases l a with h | h <;> rw [h] <;> norm_num :
      ∀ a ∈ (Finset.univ : Finset A), signHom l a * signHom l a = 1)]
    simp
  · rw [ite_eq_right heq]
    have hf : signHom l * ν ≠ 1 := by
      intro h1
      apply heq
      ext a
      have := congrArg (fun f : A →* ℂ => f a) h1
      simp only [MonoidHom.mul_apply, MonoidHom.one_apply] at this
      rcases signHom_cases l a with h | h <;> rw [h] at this ⊢
      · linear_combination this
      · linear_combination -this
    have := sum_hom_units_eq_zero (signHom l * ν) hf
    simpa using this

end Signs

section Basis

variable {S : Type*} [Group S] [Fintype S]

noncomputable abbrev basisCentralCharacter (basis : FiniteIrreducibleCharacterBasis S)
    (label : basis.index) : Subgroup.center S →* ℂ :=
  centralCharacter (basis.representation label) (basis.irreducible label)

theorem UnitaryFourSylowShape.fiber_degree_sum (h : UnitaryFourSylowShape S)
    (basis : FiniteIrreducibleCharacterBasis S) (l : Subgroup.center S →* ℤˣ) :
    ∑ label, (if basisCentralCharacter basis label = signHom l then
      (basis.representation label).character 1 ^ 2 else 0) = 16 := by
  have hcases : ∀ label (z : Subgroup.center S), basisCentralCharacter basis label z = 1 ∨
      basisCentralCharacter basis label z = -1 :=
    fun label z => centralCharacter_sq _ _ z ((h.sq_eq_one_iff z).mpr z.property)
  have hreg : ∀ z : Subgroup.center S, (∑ label, (basis.representation label).character 1 *
      (basis.representation label).character z) =
      if (z : S) = 1 then (Nat.card S : ℂ) else 0 := fun z => regular_character_sum basis z
  have hlhs : (∑ z : Subgroup.center S, signHom l z * ∑ label,
      (basis.representation label).character 1 * (basis.representation label).character z) =
      (Nat.card S : ℂ) := by
    simp_rw [hreg]
    rw [Finset.sum_eq_single 1]
    · simp
    · intro z _ hz
      have hz' : (z : S) ≠ 1 := fun h' => hz (Subtype.ext (by simpa using h'))
      rw [ite_eq_right hz', mul_zero]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  have hrhs : (∑ z : Subgroup.center S, signHom l z * ∑ label,
      (basis.representation label).character 1 * (basis.representation label).character z) =
      (Fintype.card (Subgroup.center S) : ℂ) * ∑ label,
        (if basisCentralCharacter basis label = signHom l then
          (basis.representation label).character 1 ^ 2 else 0) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro label _
    have hterm : ∀ z : Subgroup.center S, signHom l z *
        ((basis.representation label).character 1 * (basis.representation label).character z) =
        (basis.representation label).character 1 ^ 2 *
          (signHom l z * basisCentralCharacter basis label z) := by
      intro z
      rw [character_central_eq (basis.representation label) (basis.irreducible label) z]
      ring
    rw [Finset.sum_congr rfl (fun z _ => hterm z), ← Finset.mul_sum,
      sum_signHom_mul l _]
    split_ifs <;> ring
  have hZ : (Fintype.card (Subgroup.center S) : ℂ) = 4 := by
    rw [← Nat.card_eq_fintype_card, h.card_center]
    norm_num
  rw [hrhs, hZ, h.card] at hlhs
  linear_combination hlhs / 4

end Basis


section Counting

variable {S : Type*} [Group S] [Fintype S]

omit [Fintype S] in
theorem character_one_eq_finrank (data : FiniteComplexRepresentation S) :
    data.character 1 = (Module.finrank ℂ data.vector : ℂ) := by
  rw [FiniteComplexRepresentation.character, Representation.char_one]

theorem UnitaryFourSylowShape.basis_degree_one (h : UnitaryFourSylowShape S)
    (basis : FiniteIrreducibleCharacterBasis S) (label : basis.index)
    (hcc : basisCentralCharacter basis label = 1) :
    (basis.representation label).character 1 = 1 := by
  rw [character_one_eq_finrank, h.finrank_eq_one_of_central _ _ hcc, Nat.cast_one]

theorem UnitaryFourSylowShape.basis_degree_four (h : UnitaryFourSylowShape S)
    (basis : FiniteIrreducibleCharacterBasis S) (label : basis.index)
    (hcc : basisCentralCharacter basis label ≠ 1) :
    (basis.representation label).character 1 = 4 := by
  rw [character_one_eq_finrank, h.finrank_eq_four_of_central _ _ hcc]
  norm_num

theorem signHom_one {A : Type*} [Group A] : signHom (1 : A →* ℤˣ) = 1 := by
  ext a
  simp [signHom_apply]

theorem UnitaryFourSylowShape.card_trivial_central (h : UnitaryFourSylowShape S)
    (basis : FiniteIrreducibleCharacterBasis S) :
    (Finset.univ.filter (fun label => basisCentralCharacter basis label = 1)).card = 16 := by
  have hsum := h.fiber_degree_sum basis 1
  rw [signHom_one] at hsum
  have hterm : ∀ label, (if basisCentralCharacter basis label = 1 then
      (basis.representation label).character 1 ^ 2 else 0) =
      if basisCentralCharacter basis label = 1 then (1 : ℂ) else 0 := by
    intro label
    split_ifs with hcc
    · rw [h.basis_degree_one basis label hcc, one_pow]
    · rfl
  rw [Finset.sum_congr rfl (fun label _ => hterm label), Finset.sum_boole] at hsum
  exact_mod_cast hsum

theorem UnitaryFourSylowShape.existsUnique_central (h : UnitaryFourSylowShape S)
    (basis : FiniteIrreducibleCharacterBasis S) (l : Subgroup.center S →* ℤˣ) (hl : l ≠ 1) :
    ∃! label, basisCentralCharacter basis label = signHom l := by
  have hne : signHom l ≠ 1 := by
    intro h1
    apply hl
    apply signHom_injective
    rw [h1, signHom_one]
  have hsum := h.fiber_degree_sum basis l
  have hterm : ∀ label, (if basisCentralCharacter basis label = signHom l then
      (basis.representation label).character 1 ^ 2 else 0) =
      16 * if basisCentralCharacter basis label = signHom l then (1 : ℂ) else 0 := by
    intro label
    split_ifs with hcc
    · rw [h.basis_degree_four basis label (hcc ▸ hne)]
      norm_num
    · simp
  rw [Finset.sum_congr rfl (fun label _ => hterm label), ← Finset.mul_sum, Finset.sum_boole]
    at hsum
  have hcard : (Finset.univ.filter
      (fun label => basisCentralCharacter basis label = signHom l)).card = 1 := by
    have : ((Finset.univ.filter
        (fun label => basisCentralCharacter basis label = signHom l)).card : ℂ) = 1 := by
      linear_combination hsum / 16
    exact_mod_cast this
  obtain ⟨label, hlabel⟩ := Finset.card_eq_one.mp hcard
  refine ⟨label, ?_, ?_⟩
  · have : label ∈ Finset.univ.filter
        (fun label => basisCentralCharacter basis label = signHom l) := by
      rw [hlabel]
      exact Finset.mem_singleton_self _
    exact (Finset.mem_filter.mp this).2
  · intro other hother
    have : other ∈ Finset.univ.filter
        (fun label => basisCentralCharacter basis label = signHom l) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hother⟩
    rw [hlabel] at this
    exact Finset.mem_singleton.mp this

theorem UnitaryFourSylowShape.card_nontrivial_central (h : UnitaryFourSylowShape S)
    (basis : FiniteIrreducibleCharacterBasis S) :
    (Finset.univ.filter (fun label => basisCentralCharacter basis label ≠ 1)).card = 3 := by
  have htotal := finiteIrreducibleCharacterBasis_sum_degree_sq basis
  rw [h.card, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun label => basisCentralCharacter basis label = 1)] at htotal
  have h1 : ∑ label ∈ Finset.univ.filter (fun label => basisCentralCharacter basis label = 1),
      (basis.representation label).character 1 ^ 2 = 16 := by
    rw [Finset.sum_congr rfl (fun label hlabel => by
      rw [h.basis_degree_one basis label (Finset.mem_filter.mp hlabel).2, one_pow]),
      Finset.sum_const, h.card_trivial_central basis]
    norm_num
  have h2 : ∑ label ∈ Finset.univ.filter (fun label => ¬ basisCentralCharacter basis label = 1),
      (basis.representation label).character 1 ^ 2 =
      16 * ((Finset.univ.filter (fun label => ¬ basisCentralCharacter basis label = 1)).card :
        ℂ) := by
    rw [Finset.sum_congr rfl (fun label hlabel => by
      rw [h.basis_degree_four basis label (Finset.mem_filter.mp hlabel).2]),
      Finset.sum_const, nsmul_eq_mul]
    ring
  rw [h1, h2] at htotal
  have : ((Finset.univ.filter (fun label => ¬ basisCentralCharacter basis label = 1)).card : ℂ) =
      3 := by
    linear_combination htotal / 16
  exact_mod_cast this

theorem UnitaryFourSylowShape.card_basis (h : UnitaryFourSylowShape S)
    (basis : FiniteIrreducibleCharacterBasis S) : Fintype.card basis.index = 19 := by
  rw [← Finset.card_univ, ← Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun label => basisCentralCharacter basis label = 1),
    h.card_trivial_central basis, h.card_nontrivial_central basis]

end Counting


section Linear

variable {S : Type*} [Group S]

theorem representation_eq_character_smul (data : FiniteComplexRepresentation S)
    (hdim : Module.finrank ℂ data.vector = 1) (g : S) :
    data.representation g = data.character g • (1 : Module.End ℂ data.vector) := by
  obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim
    (data.representation g)
  have htr : data.character g = c := by
    change LinearMap.trace ℂ _ (data.representation g) = c
    rw [hc, map_smul, LinearMap.trace_id, hdim]
    simp
  rw [hc, htr]
  rfl

theorem isIrreducible_of_complex_line (ρ : Representation ℂ S ℂ) : ρ.IsIrreducible := by
  change IsSimpleOrder (Subrepresentation ρ)
  have hnontrivial : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro hequal
    have hmem : (1 : ℂ) ∈ (⊤ : Subrepresentation ρ).toSubmodule := trivial
    rw [← hequal] at hmem
    exact one_ne_zero hmem
  let : Nontrivial (Subrepresentation ρ) := ⟨⟨⊥, ⊤, hnontrivial⟩⟩
  constructor
  intro W
  obtain hbot | htop := eq_bot_or_eq_top W.toSubmodule
  · exact Or.inl (Subrepresentation.ext hbot)
  · exact Or.inr (Subrepresentation.ext htop)

@[expose] noncomputable def inflateSign (Z : Subgroup S) [Z.Normal] (l : S ⧸ Z →* ℤˣ) :
    S →* ℂ :=
  signHom (l.comp (QuotientGroup.mk' Z))

theorem inflateSign_apply (Z : Subgroup S) [Z.Normal] (l : S ⧸ Z →* ℤˣ) (s : S) :
    inflateSign Z l s = (((l (s : S ⧸ Z) : ℤˣ) : ℤ) : ℂ) := rfl

theorem inflateSign_injective (Z : Subgroup S) [Z.Normal] :
    Function.Injective (fun l : S ⧸ Z →* ℤˣ => (inflateSign Z l : S → ℂ)) := by
  intro l l' h
  ext s
  have := congrFun h s
  simp only [inflateSign_apply] at this
  exact_mod_cast this

theorem inflateSign_mem_blocksIrr (Z : Subgroup S) [Z.Normal] (l : S ⧸ Z →* ℤˣ) :
    (inflateSign Z l : S → ℂ) ∈ CFSG.BlocksIrr S := by
  refine ⟨ℂ, inferInstance, inferInstance, inferInstance,
    scalarHomRepresentation (inflateSign Z l), isIrreducible_of_complex_line _, ?_⟩
  rw [scalarHomRepresentation_character]

end Linear

section Table

variable {S : Type} [Group S]

theorem blocksIrr_eq_range_basis [Fintype S] (basis : FiniteIrreducibleCharacterBasis S) :
    CFSG.BlocksIrr S = Set.range fun label => (basis.representation label).character := by
  rw [CFSG.blocksIrr_eq_irreducible_characters]
  ext χ
  constructor
  · rintro ⟨data, hirr, rfl⟩
    obtain ⟨label, hlabel⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis data hirr
    exact ⟨label, hlabel⟩
  · rintro ⟨label, rfl⟩
    exact ⟨basis.representation label, basis.irreducible label, rfl⟩

variable [Fintype S]

theorem UnitaryFourSylowShape.exists_inflateSign (h : UnitaryFourSylowShape S)
    (basis : FiniteIrreducibleCharacterBasis S) (label : basis.index)
    (hcc : basisCentralCharacter basis label = 1) :
    ∃ l : S ⧸ Subgroup.center S →* ℤˣ,
      (basis.representation label).character = inflateSign (Subgroup.center S) l := by
  set data := basis.representation label
  have hdim := h.finrank_eq_one_of_central data (basis.irreducible label) hcc
  have hρ := representation_eq_character_smul data hdim
  have hdeg : data.character 1 = 1 := h.basis_degree_one basis label hcc
  have hmul : ∀ a b : S, data.character (a * b) = data.character a * data.character b := by
    intro a b
    have h1 := congrArg (LinearMap.trace ℂ data.vector) (map_mul data.representation a b)
    rw [hρ, hρ, hρ, smul_mul_smul, one_mul, map_smul, map_smul, LinearMap.trace_one, hdim] at h1
    simpa using h1
  let χHom : S →* ℂ :=
    { toFun := data.character
      map_one' := hdeg
      map_mul' := hmul }
  have hcenter : ∀ z ∈ Subgroup.center S, data.character z = 1 := by
    intro z hz
    rw [character_central_eq data (basis.irreducible label) ⟨z, hz⟩]
    have := congrArg (fun f => f ⟨z, hz⟩) hcc
    simp only [MonoidHom.one_apply] at this
    rw [this, hdeg, mul_one]
  have hsign : ∀ a : S, χHom a = 1 ∨ χHom a = -1 := by
    intro a
    have hsq : χHom a * χHom a = 1 := by
      rw [← map_mul, ← pow_two]
      exact hcenter _ (h.sq_mem_center a)
    exact mul_self_eq_one_iff.mp hsq
  obtain ⟨l', hl'⟩ := exists_signHom_eq χHom hsign
  have hker : Subgroup.center S ≤ MonoidHom.ker l' := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have := congrArg (fun f : S →* ℂ => f z) hl'
    simp only [signHom_apply] at this
    have h1 : (((l' z : ℤˣ) : ℤ) : ℂ) = 1 := this.trans (hcenter z hz)
    have h2 : ((l' z : ℤˣ) : ℤ) = 1 := by exact_mod_cast h1
    exact Units.val_eq_one.mp h2
  refine ⟨QuotientGroup.lift (Subgroup.center S) l' hker, ?_⟩
  funext s
  rw [inflateSign_apply, QuotientGroup.lift_mk]
  have := congrArg (fun f : S →* ℂ => f s) hl'
  simp only [signHom_apply] at this
  exact this.symm

theorem UnitaryFourSylowShape.character_table (h : UnitaryFourSylowShape S) :
    {χ | χ ∈ CFSG.BlocksIrr S ∧ χ 1 = 1} = Set.range (fun l : S ⧸ Subgroup.center S →* ℤˣ =>
      fun s : S => (((l (s : S ⧸ Subgroup.center S) : ℤˣ) : ℤ) : ℂ)) ∧
    Nat.card (S ⧸ Subgroup.center S →* ℤˣ) = 16 ∧
    {χ | χ ∈ CFSG.BlocksIrr S ∧ χ 1 = 1}.ncard = 16 ∧
    Nat.card {l : Subgroup.center S →* ℤˣ // l ≠ 1} = 3 ∧
    (∀ l : Subgroup.center S →* ℤˣ, l ≠ 1 → ∃! ψ : S → ℂ, ψ ∈ CFSG.BlocksIrr S ∧
      ∀ z : Subgroup.center S, ψ z = ψ 1 * (((l z : ℤˣ) : ℤ) : ℂ)) ∧
    (∀ l : Subgroup.center S →* ℤˣ, l ≠ 1 → ∀ ψ ∈ CFSG.BlocksIrr S,
      (∀ z : Subgroup.center S, ψ z = ψ 1 * (((l z : ℤˣ) : ℤ) : ℂ)) →
        ψ 1 = 4 ∧ (∀ z : Subgroup.center S, ψ z = 4 * (((l z : ℤˣ) : ℤ) : ℂ)) ∧
          ∀ x : S, x ∉ Subgroup.center S → ψ x = 0) ∧
    (∀ χ ∈ CFSG.BlocksIrr S, χ 1 = 1 ∨ ∃ l : Subgroup.center S →* ℤˣ, l ≠ 1 ∧
      ∀ z : Subgroup.center S, χ z = χ 1 * (((l z : ℤˣ) : ℤ) : ℂ)) ∧
    (CFSG.BlocksIrr S).ncard = 19 ∧
    (∀ χ ∈ CFSG.BlocksIrr S, ∀ s : S, ∃ n : ℤ, χ s = n) ∧
    (∀ x : S, x ∉ Subgroup.center S → ∀ y : S,
      IsConj x y ↔ ∃ z ∈ Subgroup.center S, y = x * z) := by
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := S)
  have hrange := blocksIrr_eq_range_basis basis
  have hinj : Function.Injective fun label => (basis.representation label).character :=
    basis.distinct
  have hcc : ∀ label, ∃ l : Subgroup.center S →* ℤˣ,
      signHom l = basisCentralCharacter basis label := fun label =>
    exists_signHom_eq _ (fun z => centralCharacter_sq _ _ z ((h.sq_eq_one_iff z).mpr z.property))
  have hccval : ∀ label (l : Subgroup.center S →* ℤˣ),
      basisCentralCharacter basis label = signHom l ↔
        ∀ z : Subgroup.center S, (basis.representation label).character z =
          (basis.representation label).character 1 * (((l z : ℤˣ) : ℤ) : ℂ) := by
    intro label l
    have hdeg := irreducible_character_degree_ne_zero (basis.representation label)
      (basis.irreducible label)
    constructor
    · intro heq z
      rw [character_central_eq (basis.representation label) (basis.irreducible label) z]
      exact congrArg _ (congrArg (fun f : Subgroup.center S →* ℂ => f z) heq)
    · intro hz
      ext z
      rw [centralCharacter_apply, hz z, signHom_apply]
      field_simp
  have hlinear : ∀ label, (basis.representation label).character 1 = 1 ↔
      basisCentralCharacter basis label = 1 := by
    intro label
    constructor
    · intro h1
      by_contra hne
      rw [h.basis_degree_four basis label hne] at h1
      norm_num at h1
    · exact h.basis_degree_one basis label
  have hlinset : {χ | χ ∈ CFSG.BlocksIrr S ∧ χ 1 = 1} =
      (fun label => (basis.representation label).character) ''
        {label | basisCentralCharacter basis label = 1} := by
    ext χ
    simp only [Set.mem_ofPred_eq, Set.mem_image, hrange, Set.mem_range]
    constructor
    · rintro ⟨⟨label, rfl⟩, h1⟩
      exact ⟨label, (hlinear label).mp h1, rfl⟩
    · rintro ⟨label, hlabel, rfl⟩
      exact ⟨⟨label, rfl⟩, (hlinear label).mpr hlabel⟩
  have hlinncard : {χ | χ ∈ CFSG.BlocksIrr S ∧ χ 1 = 1}.ncard = 16 := by
    rw [hlinset, Set.ncard_image_of_injective _ hinj, ← h.card_trivial_central basis,
      ← Set.ncard_coe_finset]
    congr 1
    ext label
    simp
  have hlinrange : {χ | χ ∈ CFSG.BlocksIrr S ∧ χ 1 = 1} = Set.range (fun l : S ⧸ Subgroup.center S
      →* ℤˣ => fun s : S => (((l (s : S ⧸ Subgroup.center S) : ℤˣ) : ℤ) : ℂ)) := by
    ext χ
    simp only [Set.mem_ofPred_eq, Set.mem_range]
    constructor
    · rintro ⟨hχ, h1⟩
      rw [hrange] at hχ
      obtain ⟨label, rfl⟩ := hχ
      obtain ⟨l, hl⟩ := h.exists_inflateSign basis label ((hlinear label).mp h1)
      exact ⟨l, by dsimp only; rw [hl]; rfl⟩
    · rintro ⟨l, rfl⟩
      refine ⟨inflateSign_mem_blocksIrr (Subgroup.center S) l, ?_⟩
      simp
  have hnonlin : Nat.card {l : Subgroup.center S →* ℤˣ // l ≠ 1} = 3 := by
    rw [← h.card_nontrivial_central basis, ← Nat.card_eq_finsetCard]
    symm
    apply Nat.card_congr
    refine Equiv.ofBijective (fun label => ⟨(hcc label.val).choose, ?_⟩) ⟨?_, ?_⟩
    · intro h1
      apply (Finset.mem_filter.mp label.property).2
      rw [← (hcc label.val).choose_spec, h1, signHom_one]
    · intro a b hab
      have h1 := (hcc a.val).choose_spec
      have h2 := (hcc b.val).choose_spec
      simp only [Subtype.mk.injEq] at hab
      rw [hab] at h1
      have hne : (hcc b.val).choose ≠ 1 := by
        intro h1'
        apply (Finset.mem_filter.mp b.property).2
        rw [← h2, h1', signHom_one]
      obtain ⟨c, -, hc⟩ := h.existsUnique_central basis _ hne
      exact Subtype.ext ((hc a.val h1.symm).trans (hc b.val h2.symm).symm)
    · rintro ⟨l, hl⟩
      obtain ⟨label, hlabel, -⟩ := h.existsUnique_central basis l hl
      have hmem : label ∈
          Finset.univ.filter (fun label => basisCentralCharacter basis label ≠ 1) := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, fun h1 => hl (signHom_injective ?_)⟩
        rw [← hlabel, h1, signHom_one]
      refine ⟨⟨label, hmem⟩, Subtype.ext ?_⟩
      apply signHom_injective
      rw [(hcc label).choose_spec, hlabel]
  have hover : ∀ l : Subgroup.center S →* ℤˣ, l ≠ 1 → ∀ ψ ∈ CFSG.BlocksIrr S,
      (∀ z : Subgroup.center S, ψ z = ψ 1 * (((l z : ℤˣ) : ℤ) : ℂ)) →
        ∃ label, ψ = (basis.representation label).character ∧
          basisCentralCharacter basis label = signHom l := by
    intro l hl ψ hψ hz
    rw [hrange] at hψ
    obtain ⟨label, rfl⟩ := hψ
    exact ⟨label, rfl, (hccval label l).mpr hz⟩
  have hsignne : ∀ l : Subgroup.center S →* ℤˣ, l ≠ 1 → signHom l ≠ 1 := by
    intro l hl h1
    apply hl
    apply signHom_injective
    rw [h1, signHom_one]
  refine ⟨hlinrange, ?_, hlinncard, hnonlin, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [← hlinncard, hlinrange, Set.ncard_range_of_injective]
    intro l l' hll'
    apply inflateSign_injective (Subgroup.center S)
    exact hll'
  · intro l hl
    obtain ⟨label, hlabel, huniq⟩ := h.existsUnique_central basis l hl
    refine ⟨(basis.representation label).character, ⟨?_, (hccval label l).mp hlabel⟩, ?_⟩
    · rw [hrange]
      exact ⟨label, rfl⟩
    · rintro ψ ⟨hψ, hz⟩
      obtain ⟨label', rfl, hlabel'⟩ := hover l hl ψ hψ hz
      rw [huniq label' hlabel']
  · intro l hl ψ hψ hz
    obtain ⟨label, rfl, hlabel⟩ := hover l hl ψ hψ hz
    have hne : basisCentralCharacter basis label ≠ 1 := by rw [hlabel]; exact hsignne l hl
    have h4 := h.basis_degree_four basis label hne
    refine ⟨h4, fun z => by rw [hz z, h4], fun x hx => ?_⟩
    exact h.character_eq_zero_of_central _ _ hne x hx
  · intro χ hχ
    rw [hrange] at hχ
    obtain ⟨label, rfl⟩ := hχ
    by_cases h1 : basisCentralCharacter basis label = 1
    · left
      exact h.basis_degree_one basis label h1
    · right
      obtain ⟨l, hl⟩ := hcc label
      refine ⟨l, fun hl1 => h1 ?_, (hccval label l).mp hl.symm⟩
      rw [← hl, hl1, signHom_one]
  · rw [hrange, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card]
    exact h.card_basis basis
  · intro χ hχ s
    rw [hrange] at hχ
    obtain ⟨label, rfl⟩ := hχ
    dsimp only
    by_cases h1 : basisCentralCharacter basis label = 1
    · obtain ⟨l, hl⟩ := h.exists_inflateSign basis label h1
      rw [hl, inflateSign_apply]
      exact ⟨_, rfl⟩
    · by_cases hs : s ∈ Subgroup.center S
      · obtain ⟨l, hl⟩ := hcc label
        refine ⟨4 * ((l ⟨s, hs⟩ : ℤˣ) : ℤ), ?_⟩
        have hval := (hccval label l).mp hl.symm ⟨s, hs⟩
        rw [hval, h.basis_degree_four basis label h1]
        push_cast
        ring
      · exact ⟨0, by rw [h.character_eq_zero_of_central _ _ h1 s hs]; simp⟩
  · intro x hx y
    exact h.isConj_iff_mul_center x hx y

end Table


section Model

theorem unitaryFourSylowShape_of_statedClassicalModel {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 T) :
    UnitaryFourSylowShape (S : Subgroup T) := by
  obtain ⟨hcard, hcz, hsq, hsqmem, hZ⟩ :=
    unitary_four_sylow_structure (G := T) hT S S ⟨MulEquiv.refl _⟩
  have hK : Nat.card (GaloisField 2 4) = 16 := by
    rw [GaloisField.card 2 4 (by norm_num)]
    norm_num
  obtain ⟨ψ⟩ := CFSG.RankTwoShapes.nonempty_sylow_equiv_unitaryFourW hT S (GaloisField 2 4) hK
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

theorem unitary_four_sylow_character_table {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 T) :
    {χ | χ ∈ CFSG.BlocksIrr (S : Subgroup T) ∧ χ 1 = 1} =
      Set.range (fun l : (S : Subgroup T) ⧸ Subgroup.center (S : Subgroup T) →* ℤˣ =>
        fun s : (S : Subgroup T) =>
          (((l (s : (S : Subgroup T) ⧸ Subgroup.center (S : Subgroup T)) : ℤˣ) : ℤ) : ℂ)) ∧
    Nat.card ((S : Subgroup T) ⧸ Subgroup.center (S : Subgroup T) →* ℤˣ) = 16 ∧
    {χ | χ ∈ CFSG.BlocksIrr (S : Subgroup T) ∧ χ 1 = 1}.ncard = 16 ∧
    Nat.card {l : Subgroup.center (S : Subgroup T) →* ℤˣ // l ≠ 1} = 3 ∧
    (∀ l : Subgroup.center (S : Subgroup T) →* ℤˣ, l ≠ 1 →
      ∃! ψ : ↥(S : Subgroup T) → ℂ, ψ ∈ CFSG.BlocksIrr (S : Subgroup T) ∧
        ∀ z : Subgroup.center (S : Subgroup T), ψ z = ψ 1 * (((l z : ℤˣ) : ℤ) : ℂ)) ∧
    (∀ l : Subgroup.center (S : Subgroup T) →* ℤˣ, l ≠ 1 →
      ∀ ψ ∈ CFSG.BlocksIrr (S : Subgroup T),
        (∀ z : Subgroup.center (S : Subgroup T), ψ z = ψ 1 * (((l z : ℤˣ) : ℤ) : ℂ)) →
          ψ 1 = 4 ∧
          (∀ z : Subgroup.center (S : Subgroup T), ψ z = 4 * (((l z : ℤˣ) : ℤ) : ℂ)) ∧
          ∀ x : (S : Subgroup T), x ∉ Subgroup.center (S : Subgroup T) → ψ x = 0) ∧
    (∀ χ ∈ CFSG.BlocksIrr (S : Subgroup T), χ 1 = 1 ∨
      ∃ l : Subgroup.center (S : Subgroup T) →* ℤˣ, l ≠ 1 ∧
        ∀ z : Subgroup.center (S : Subgroup T), χ z = χ 1 * (((l z : ℤˣ) : ℤ) : ℂ)) ∧
    (CFSG.BlocksIrr (S : Subgroup T)).ncard = 19 ∧
    (∀ χ ∈ CFSG.BlocksIrr (S : Subgroup T), ∀ s : (S : Subgroup T), ∃ n : ℤ, χ s = n) ∧
    (∀ x : (S : Subgroup T), x ∉ Subgroup.center (S : Subgroup T) →
      ∀ y : (S : Subgroup T),
        IsConj x y ↔ ∃ z ∈ Subgroup.center (S : Subgroup T), y = x * z) := by
  have : Finite T := CFSG.RankTwoShapes.finite_of_statedClassicalModel_PSU_three_two_two hT
  let : Fintype (S : Subgroup T) := Fintype.ofFinite _
  exact (unitaryFourSylowShape_of_statedClassicalModel hT S).character_table

end Model

end CFSG.LyonsUnitaryFour
