module

public import CFSG.CharacterTheory.Wreathed.ConditionalFourierColumnsAlgebra
public import CFSG.CharacterTheory.Semidihedral.Principal.SectionIntegralColumns

public section

open scoped BigOperators Classical ComplexConjugate

namespace CFSG.Wreathed.ConditionalGeneralBase

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.ConditionalFourier

section Coordinates

variable {A : Type*} [Group A] {σ υ : A}

theorem zpow_mul_zpow_mul (hc : Commute σ υ) (a b c d : ℤ) :
    σ ^ a * υ ^ b * (σ ^ c * υ ^ d) = σ ^ (a + c) * υ ^ (b + d) := by
  rw [Commute.mul_mul_mul_comm ((hc.zpow_zpow c b).symm), ← zpow_add, ← zpow_add]

theorem exists_zpow_mul_zpow (hc : Commute σ υ)
    (hgen : Subgroup.closure ({σ, υ} : Set A) = ⊤) (x : A) : ∃ a b : ℤ, σ ^ a * υ ^ b = x := by
  have hx : x ∈ Subgroup.closure ({σ, υ} : Set A) := hgen ▸ Subgroup.mem_top x
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · exact ⟨1, 0, by simp⟩
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨c, d, rfl⟩ := hz
    exact ⟨a + c, b + d, (zpow_mul_zpow_mul hc a b c d).symm⟩
  | inv y _ hy =>
    obtain ⟨a, b, rfl⟩ := hy
    refine ⟨-a, -b, ?_⟩
    rw [(hc.zpow_zpow (-a) (-b)).eq, mul_inv_rev, zpow_neg, zpow_neg]

theorem zpow_mul_zpow_eq_one_iff {m : ℕ} (hσ : orderOf σ = m) (hυ : orderOf υ = m)
    (hint : Subgroup.zpowers σ ⊓ Subgroup.zpowers υ = ⊥) (a b : ℤ) :
    σ ^ a * υ ^ b = 1 ↔ (m : ℤ) ∣ a ∧ (m : ℤ) ∣ b := by
  constructor
  · intro h
    have hσa : σ ^ a = (υ ^ b)⁻¹ := eq_inv_of_mul_eq_one_left h
    have hmem : σ ^ a ∈ Subgroup.zpowers σ ⊓ Subgroup.zpowers υ := by
      refine ⟨Subgroup.zpow_mem_zpowers σ a, ?_⟩
      rw [hσa]
      exact Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers υ b)
    rw [hint, Subgroup.mem_bot] at hmem
    have hυb : υ ^ b = 1 := by
      rw [hmem] at hσa
      exact inv_eq_one.mp hσa.symm
    exact ⟨hσ ▸ orderOf_dvd_iff_zpow_eq_one.mpr hmem, hυ ▸ orderOf_dvd_iff_zpow_eq_one.mpr hυb⟩
  · rintro ⟨⟨c, rfl⟩, ⟨d, rfl⟩⟩
    have h1 : σ ^ (m : ℤ) = 1 := by rw [zpow_natCast, ← hσ, pow_orderOf_eq_one]
    have h2 : υ ^ (m : ℤ) = 1 := by rw [zpow_natCast, ← hυ, pow_orderOf_eq_one]
    rw [zpow_mul, zpow_mul, h1, h2, one_zpow, one_zpow, one_mul]

theorem monoidHom_ext_pair (hc : Commute σ υ) (hgen : Subgroup.closure ({σ, υ} : Set A) = ⊤)
    (f g : A →* ℂ) (h1 : f σ = g σ) (h2 : f υ = g υ) : f = g := by
  ext x
  obtain ⟨a, b, rfl⟩ := exists_zpow_mul_zpow hc hgen x
  rw [map_mul, map_mul, map_zpow, map_zpow, map_zpow, map_zpow, h1, h2]

end Coordinates

section Characters

variable {A : Type*} [Group A] {σ υ : A} {m : ℕ} [NeZero m] {ζ : ℂ}

theorem zpow_eq_of_modEq (hζ : IsPrimitiveRoot ζ m) {a b : ℤ} (h : (m : ℤ) ∣ a - b) :
    ζ ^ a = ζ ^ b := by
  obtain ⟨c, hc⟩ := h
  have hab : a = b + m * c := by linarith
  rw [hab, zpow_add₀ (hζ.ne_zero (NeZero.ne m)), zpow_mul, zpow_natCast, hζ.pow_eq_one,
    one_zpow, mul_one]

noncomputable def charValue (hc : Commute σ υ) (hgen : Subgroup.closure ({σ, υ} : Set A) = ⊤)
    (ζ : ℂ) (i j : ℕ) (x : A) : ℂ :=
  ζ ^ ((i : ℤ) * (exists_zpow_mul_zpow hc hgen x).choose +
    (j : ℤ) * (exists_zpow_mul_zpow hc hgen x).choose_spec.choose)

theorem charValue_eq (hc : Commute σ υ) (hgen : Subgroup.closure ({σ, υ} : Set A) = ⊤)
    (hσ : orderOf σ = m) (hυ : orderOf υ = m)
    (hint : Subgroup.zpowers σ ⊓ Subgroup.zpowers υ = ⊥) (hζ : IsPrimitiveRoot ζ m)
    (i j : ℕ) (a b : ℤ) :
    charValue hc hgen ζ i j (σ ^ a * υ ^ b) = ζ ^ ((i : ℤ) * a + (j : ℤ) * b) := by
  unfold charValue
  set x := σ ^ a * υ ^ b with hx
  set a' := (exists_zpow_mul_zpow hc hgen x).choose
  set b' := (exists_zpow_mul_zpow hc hgen x).choose_spec.choose
  have hspec : σ ^ a' * υ ^ b' = x := (exists_zpow_mul_zpow hc hgen x).choose_spec.choose_spec
  have hrel : σ ^ (a' - a) * υ ^ (b' - b) = 1 := by
    have h := zpow_mul_zpow_mul hc (a' - a) (b' - b) a b
    rw [sub_add_cancel, sub_add_cancel, hspec, hx] at h
    exact mul_eq_right.mp h
  obtain ⟨hda, hdb⟩ := (zpow_mul_zpow_eq_one_iff hσ hυ hint _ _).mp hrel
  apply zpow_eq_of_modEq hζ
  have : (i : ℤ) * a' + (j : ℤ) * b' - ((i : ℤ) * a + (j : ℤ) * b) =
      (i : ℤ) * (a' - a) + (j : ℤ) * (b' - b) := by ring
  rw [this]
  exact dvd_add (dvd_mul_of_dvd_right hda _) (dvd_mul_of_dvd_right hdb _)

theorem sum_zmod_val (g : ℕ → ℂ) : ∑ i : ZMod m, g i.val = ∑ k ∈ Finset.range m, g k := by
  refine Finset.sum_nbij (fun i => i.val) (fun i _ => Finset.mem_range.mpr (ZMod.val_lt i))
    (fun i _ j _ h => ZMod.val_injective m h) (fun k hk => ?_) (fun i _ => rfl)
  exact ⟨(k : ZMod m), Finset.mem_coe.mpr (Finset.mem_univ _),
    ZMod.val_cast_of_lt (Finset.mem_range.mp hk)⟩

theorem sum_zmod_zpow (hζ : IsPrimitiveRoot ζ m) (a : ℤ) :
    ∑ i : ZMod m, ζ ^ ((i.val : ℤ) * a) = if (m : ℤ) ∣ a then (m : ℂ) else 0 := by
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne m
  obtain ⟨c, hc⟩ : ∃ c : ℕ, (m : ℤ) ∣ a - c := ⟨(a % m).toNat, by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg a hm0)]
    exact ⟨a / m, by linarith [Int.emod_add_mul_ediv a m]⟩⟩
  have hterm : ∀ i : ZMod m, ζ ^ ((i.val : ℤ) * a) = ζ ^ (c * i.val) := by
    intro i
    rw [← zpow_natCast]
    apply zpow_eq_of_modEq hζ
    push_cast
    have : (i.val : ℤ) * a - c * i.val = i.val * (a - c) := by ring
    rw [this]
    exact dvd_mul_of_dvd_right hc _
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  rw [sum_zmod_val (m := m) (fun k => ζ ^ (c * k)), sum_range_pow_mul hζ c]
  have hiff : m ∣ c ↔ (m : ℤ) ∣ a := by
    rw [← Int.natCast_dvd_natCast]
    constructor
    · intro h
      have := dvd_add h hc
      rwa [add_sub_cancel] at this
    · intro h
      have := dvd_sub h hc
      rwa [sub_sub_cancel] at this
  by_cases h : (m : ℤ) ∣ a
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
  · rw [ite_eq_right (mt hiff.mp h), ite_eq_right h]

variable (hc : Commute σ υ) (hgen : Subgroup.closure ({σ, υ} : Set A) = ⊤)
  (hσ : orderOf σ = m) (hυ : orderOf υ = m)
  (hint : Subgroup.zpowers σ ⊓ Subgroup.zpowers υ = ⊥) (hζ : IsPrimitiveRoot ζ m)
include hc hgen hσ hυ hint hζ

theorem exists_linearCharacter (i j : ℕ) :
    ∃ f : A →* ℂ, f σ = ζ ^ i ∧ f υ = ζ ^ j := by
  have hv := charValue_eq hc hgen hσ hυ hint hζ i j
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne m)
  let f : A →* ℂ :=
    { toFun := charValue hc hgen ζ i j
      map_one' := by
        have h := hv 0 0
        simp only [zpow_zero, mul_one, mul_zero, add_zero] at h
        exact h
      map_mul' := by
        intro x y
        obtain ⟨a, b, rfl⟩ := exists_zpow_mul_zpow hc hgen x
        obtain ⟨c, d, rfl⟩ := exists_zpow_mul_zpow hc hgen y
        rw [zpow_mul_zpow_mul hc, hv, hv, hv, ← zpow_add₀ hζ0]
        congr 1
        ring }
  refine ⟨f, ?_, ?_⟩
  · have h := hv 1 0
    simp only [zpow_one, zpow_zero, mul_one, mul_zero, add_zero] at h
    change charValue hc hgen ζ i j σ = _
    rw [h, zpow_natCast]
  · have h := hv 0 1
    simp only [zpow_one, zpow_zero, one_mul, mul_one, mul_zero, zero_add] at h
    change charValue hc hgen ζ i j υ = _
    rw [h, zpow_natCast]

theorem exists_linearCharacters :
    ∃ lam : ZMod m → ZMod m → A →* ℂ, ∀ i j, lam i j σ = ζ ^ i.val ∧ lam i j υ = ζ ^ j.val := by
  choose f hf using fun i j : ZMod m => exists_linearCharacter hc hgen hσ hυ hint hζ i.val j.val
  exact ⟨f, hf⟩

omit hc hgen hσ hυ hint in
theorem linearCharacter_zpow_mul_zpow (f : A →* ℂ) {i j : ℕ} (hf1 : f σ = ζ ^ i)
    (hf2 : f υ = ζ ^ j) (a b : ℤ) : f (σ ^ a * υ ^ b) = ζ ^ ((i : ℤ) * a + (j : ℤ) * b) := by
  rw [map_mul, map_zpow, map_zpow, hf1, hf2, ← zpow_natCast, ← zpow_natCast, ← zpow_mul,
    ← zpow_mul, ← zpow_add₀ (hζ.ne_zero (NeZero.ne m))]

omit hσ hυ hint in
theorem linearCharacter_eq_one_iff (f : A →* ℂ) {i j : ZMod m} (hf1 : f σ = ζ ^ i.val)
    (hf2 : f υ = ζ ^ j.val) : f = 1 ↔ i = 0 ∧ j = 0 := by
  constructor
  · intro h
    have h1 : ζ ^ i.val = 1 := by rw [← hf1, h, MonoidHom.one_apply]
    have h2 : ζ ^ j.val = 1 := by rw [← hf2, h, MonoidHom.one_apply]
    have hi := hζ.dvd_of_pow_eq_one _ h1
    have hj := hζ.dvd_of_pow_eq_one _ h2
    refine ⟨?_, ?_⟩
    · rw [← ZMod.natCast_zmod_val i, (ZMod.natCast_eq_zero_iff _ _).mpr hi]
    · rw [← ZMod.natCast_zmod_val j, (ZMod.natCast_eq_zero_iff _ _).mpr hj]
  · rintro ⟨rfl, rfl⟩
    refine monoidHom_ext_pair hc hgen f 1 ?_ ?_
    · rw [hf1, MonoidHom.one_apply, ZMod.val_zero, pow_zero]
    · rw [hf2, MonoidHom.one_apply, ZMod.val_zero, pow_zero]

variable [Fintype A]

omit hσ hυ hint in
theorem sum_linearCharacter (f : A →* ℂ) {i j : ZMod m} (hf1 : f σ = ζ ^ i.val)
    (hf2 : f υ = ζ ^ j.val) :
    ∑ x : A, f x = if i = 0 ∧ j = 0 then (Fintype.card A : ℂ) else 0 := by
  rw [sum_hom_units]
  by_cases h : i = 0 ∧ j = 0
  · rw [ite_eq_left ((linearCharacter_eq_one_iff hc hgen hζ f hf1 hf2).mpr h), ite_eq_left h]
  · rw [ite_eq_right (mt (linearCharacter_eq_one_iff hc hgen hζ f hf1 hf2).mp h),
      ite_eq_right h, Nat.cast_zero]

omit [Fintype A] in
theorem sum_indices_linearCharacter (lam : ZMod m → ZMod m → A →* ℂ)
    (hlam : ∀ i j, lam i j σ = ζ ^ i.val ∧ lam i j υ = ζ ^ j.val) (x : A) :
    ∑ i : ZMod m, ∑ j : ZMod m, lam i j x = if x = 1 then (m : ℂ) ^ 2 else 0 := by
  obtain ⟨a, b, rfl⟩ := exists_zpow_mul_zpow hc hgen x
  have hval : ∀ i j : ZMod m, lam i j (σ ^ a * υ ^ b) =
      ζ ^ ((i.val : ℤ) * a) * ζ ^ ((j.val : ℤ) * b) := by
    intro i j
    rw [linearCharacter_zpow_mul_zpow hζ (lam i j) (hlam i j).1 (hlam i j).2,
      zpow_add₀ (hζ.ne_zero (NeZero.ne m))]
  simp only [hval, ← Finset.mul_sum, ← Finset.sum_mul, sum_zmod_zpow hζ]
  rw [zpow_mul_zpow_eq_one_iff hσ hυ hint]
  by_cases ha : (m : ℤ) ∣ a <;> by_cases hb : (m : ℤ) ∣ b <;> simp [ha, hb, sq]

theorem card_eq_sq (lam : ZMod m → ZMod m → A →* ℂ)
    (hlam : ∀ i j, lam i j σ = ζ ^ i.val ∧ lam i j υ = ζ ^ j.val) :
    Fintype.card A = m ^ 2 := by
  have hsum := fun i j => sum_linearCharacter hc hgen hζ (lam i j) (hlam i j).1 (hlam i j).2
  have h1 : ∑ x : A, ∑ i : ZMod m, ∑ j : ZMod m, lam i j x = (m : ℂ) ^ 2 := by
    rw [Finset.sum_congr rfl fun x _ =>
      sum_indices_linearCharacter hc hgen hσ hυ hint hζ lam hlam x]
    rw [Finset.sum_ite_eq' Finset.univ (1 : A), ite_eq_left (Finset.mem_univ _)]
  have h2 : ∑ x : A, ∑ i : ZMod m, ∑ j : ZMod m, lam i j x = (Fintype.card A : ℂ) := by
    have hswap : ∑ x : A, ∑ i : ZMod m, ∑ j : ZMod m, lam i j x =
        ∑ i : ZMod m, ∑ j : ZMod m, ∑ x : A, lam i j x := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    rw [hswap, Finset.sum_eq_single (0 : ZMod m), Finset.sum_eq_single (0 : ZMod m), hsum,
      ite_eq_left ⟨rfl, rfl⟩]
    · intro j _ hj
      rw [hsum, ite_eq_right (fun h => hj h.2)]
    · simp
    · intro i _ hi
      exact Finset.sum_eq_zero fun j _ => by rw [hsum, ite_eq_right (fun h => hi h.1)]
    · simp
  exact_mod_cast h2.symm.trans h1

end Characters

section Conj

variable {A : Type*} [Group A] [Finite A]

omit [Finite A] in
theorem monoidHom_inv_eq (f : A →* ℂ) (x : A) : f x⁻¹ = (f x)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← map_mul, mul_inv_cancel, map_one]

theorem norm_monoidHom_apply (f : A →* ℂ) (x : A) : ‖f x‖ = 1 := by
  have h : f x ^ Nat.card A = 1 := by rw [← map_pow, pow_card_eq_one', map_one]
  exact Complex.norm_eq_one_of_pow_eq_one h Nat.card_pos.ne'

theorem conj_monoidHom_apply (f : A →* ℂ) (x : A) : conj (f x) = f x⁻¹ := by
  have hn := norm_monoidHom_apply f x
  have hx0 : f x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  rw [monoidHom_inv_eq, Complex.inv_def, Complex.normSq_eq_norm_sq, hn]
  simp

theorem conj_mul_monoidHom_apply (f : A →* ℂ) (x : A) : conj (f x) * f x = 1 := by
  rw [conj_monoidHom_apply, ← map_mul, inv_mul_cancel, map_one]

end Conj

section Pairing

@[expose] noncomputable def linearRepresentation {A : Type*} [Group A] (f : A →* ℂˣ) :
    FiniteComplexRepresentation A where
  vector := ℂ
  representation :=
    { toFun := fun g => (f g : ℂ) • LinearMap.id
      map_one' := by
        ext
        simp
      map_mul' := fun g h => by
        ext
        simp [mul_comm] }

theorem linearRepresentation_character {A : Type*} [Group A] (f : A →* ℂˣ) (g : A) :
    (linearRepresentation f).character g = (f g : ℂ) := by
  change LinearMap.trace ℂ ℂ ((f g : ℂ) • LinearMap.id) = _
  simp

theorem linearRepresentation_isIrreducible {A : Type*} [Group A] (f : A →* ℂˣ) :
    (linearRepresentation f).IsIrreducible := by
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := ?_ }
  · have h' := congrArg Subrepresentation.toSubmodule h
    exact (bot_ne_top : (⊥ : Submodule ℂ ℂ) ≠ ⊤) h'
  intro W
  have hsimple : IsSimpleOrder (Submodule ℂ ℂ) := by infer_instance
  rcases hsimple.eq_bot_or_eq_top W.toSubmodule with hbot | htop
  · left
    exact Subrepresentation.toSubmodule_injective hbot
  · right
    exact Subrepresentation.toSubmodule_injective htop

theorem restriction_linear_pairing_nat {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (U : Subgroup G) (f : U →* ℂ)
    (χ : basis.index) :
    ∃ k : ℕ, (Nat.card U : ℂ)⁻¹ * ∑ u : U, (basis.representation χ).character u * conj (f u) =
      k := by
  classical
  let localBasis : FiniteIrreducibleCharacterBasis U :=
    Classical.choice finiteIrreducibleCharacterBasis_exists
  obtain ⟨θ, hθ⟩ := finiteIrreducibleCharacterBasis_contains_irreducible localBasis
    (linearRepresentation f.toHomUnits) (linearRepresentation_isIrreducible _)
  obtain ⟨k, hk⟩ := CFSG.Semidihedral.Principal.restriction_pairing_nat basis localBasis χ θ
  refine ⟨k, ?_⟩
  rw [← hk, characterPairing, hθ]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [linearRepresentation_character, MonoidHom.coe_toHomUnits, conj_monoidHom_apply]

end Pairing

end CFSG.Wreathed.ConditionalGeneralBase
