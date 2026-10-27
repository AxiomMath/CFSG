module

public import CFSG.ClassicalInvolution.ModelFacts.Partner
public import CFSG.LieType.Universal.Spin.Roots.TypeB
public import CFSG.LieType.Universal.Spin.Roots.TypeD
public import CFSG.Blueprint.Chevalley
public import CFSG.LieType.Universal.SymplecticRoots

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Spin CFSG.Blueprint.Chevalley
open scoped Matrix

theorem isIrreducible_of_chain {m : ℕ} (hm : 0 < m) {A : Matrix (Fin m) (Fin m) ℤ}
    (h : ∀ a b : Fin m, a.val + 1 = b.val → A a b ≠ 0 ∧ A b a ≠ 0) : IsIrreducible A := by
  refine isIrreducible_of_parent ⟨0, hm⟩ (fun j => ⟨j.val - 1, by omega⟩) (fun j => j.val)
    fun j hj => ?_
  have hj' : 0 < j.val := by
    rcases Nat.eq_zero_or_pos j.val with h0 | h0
    · exact absurd (Fin.ext h0) hj
    · exact h0
  obtain ⟨h1, h2⟩ := h ⟨j.val - 1, by omega⟩ j (by simp only; omega)
  exact ⟨h1, h2, by simp only; omega⟩

theorem isIrreducible_A {m : ℕ} (hm : 0 < m) : IsIrreducible (CartanMatrix.A m) :=
  isIrreducible_of_chain hm fun a b hab => by
    have : a ≠ b := fun h => by rw [h] at hab; omega
    simp [CartanMatrix.A, hab, Fin.ext_iff]
    omega

theorem isIrreducible_cartanC {n : ℕ} (hn : 0 < n) : IsIrreducible (cartanC n) :=
  isIrreducible_of_chain hn fun a b hab => by
    have : a ≠ b := fun h => by rw [h] at hab; omega
    simp only [cartanC, Matrix.of_apply, this, this.symm, ite_false, hab, true_or, or_true,
      ite_true]
    split_ifs <;> simp

theorem isIrreducible_cartanB {n : ℕ} (hn : 0 < n) : IsIrreducible (cartanB n) :=
  isIrreducible_of_chain hn fun a b hab => by
    have : a ≠ b := fun h => by rw [h] at hab; omega
    simp only [cartanB, Matrix.of_apply, this, this.symm, ite_false, hab, true_or, or_true,
      ite_true]
    split_ifs <;> simp

theorem isIrreducible_cartanD {n : ℕ} (hn : 3 ≤ n) : IsIrreducible (cartanD n) := by
  refine isIrreducible_of_parent ⟨0, by omega⟩
    (fun j => if j.val + 1 = n then ⟨n - 3, by omega⟩ else ⟨j.val - 1, by omega⟩)
    (fun j => if j.val + 1 = n then n - 2 else j.val) fun j hj => ?_
  have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
  by_cases hjn : j.val + 1 = n
  · simp only [hjn, ite_true]
    have h3 : ¬ (n - 3 + 1 = n) := by omega
    have e1 : cartanD n ⟨n - 3, by omega⟩ j = -1 := by
      simp [cartanD, Fin.ext_iff]
      omega
    have e2 : cartanD n j ⟨n - 3, by omega⟩ = -1 := by
      simp [cartanD, Fin.ext_iff]
      omega
    refine ⟨by rw [e1]; norm_num, by rw [e2]; norm_num, ?_⟩
    simp only [h3, ite_false]
    omega
  · simp only [hjn, ite_false]
    have e1 : cartanD n ⟨j.val - 1, by omega⟩ j = -1 := by
      simp [cartanD, Fin.ext_iff]
      omega
    have e2 : cartanD n j ⟨j.val - 1, by omega⟩ = -1 := by
      simp [cartanD, Fin.ext_iff]
      omega
    refine ⟨by rw [e1]; norm_num, by rw [e2]; norm_num, ?_⟩
    have h3 : ¬ (j.val - 1 + 1 = n) := by omega
    simp only [h3, ite_false]
    omega

theorem isIrreducible_E6 : @IsIrreducible (Fin 6) (Tag.cartan .E6) :=
  isIrreducible_of_parent (0 : Fin 6) ![0, 3, 0, 2, 3, 4] ![0, 3, 1, 2, 3, 4] (by decide)

theorem isIrreducible_E7 : @IsIrreducible (Fin 7) (Tag.cartan .E7) :=
  isIrreducible_of_parent (0 : Fin 7) ![0, 3, 0, 2, 3, 4, 5] ![0, 3, 1, 2, 3, 4, 5]
    (by decide)

theorem isIrreducible_E8 : @IsIrreducible (Fin 8) (Tag.cartan .E8) :=
  isIrreducible_of_parent (0 : Fin 8) ![0, 3, 0, 2, 3, 4, 5, 6] ![0, 3, 1, 2, 3, 4, 5, 6]
    (by decide)

theorem isIrreducible_F4 : @IsIrreducible (Fin 4) (Tag.cartan .F4) :=
  isIrreducible_of_parent (0 : Fin 4) ![0, 0, 1, 2] ![0, 1, 2, 3] (by decide)

theorem isIrreducible_G2 : @IsIrreducible (Fin 2) (Tag.cartan .G2) :=
  isIrreducible_of_parent (0 : Fin 2) ![0, 0] ![0, 1] (by decide)

@[expose] def tabC (n : ℕ) (k : Fin n) : ℤ := if k.val + 1 = n then 2 else 1

@[expose] def tabB (n : ℕ) (k : Fin n) : ℤ := if k.val + 1 = n then 1 else 2

theorem tabC_pos (n : ℕ) (k : Fin n) : 0 < tabC n k := by
  unfold tabC
  split_ifs <;> omega

theorem tabB_pos (n : ℕ) (k : Fin n) : 0 < tabB n k := by
  unfold tabB
  split_ifs <;> omega

theorem tabC_sym (n : ℕ) (i j : Fin n) : tabC n i * cartanC n i j = tabC n j * cartanC n j i := by
  by_cases hij : i = j
  · subst hij
    rfl
  · simp only [tabC, cartanC, Matrix.of_apply, hij, Ne.symm hij, ite_false]
    split_ifs <;> omega

theorem tabB_sym (n : ℕ) (i j : Fin n) : tabB n i * cartanB n i j = tabB n j * cartanB n j i := by
  by_cases hij : i = j
  · subst hij
    rfl
  · simp only [tabB, cartanB, Matrix.of_apply, hij, Ne.symm hij, ite_false]
    split_ifs <;> omega

theorem tabB_sym_transpose_cartanC (n : ℕ) (i j : Fin n) :
    tabB n i * (cartanC n)ᵀ i j = tabB n j * (cartanC n)ᵀ j i := by
  by_cases hij : i = j
  · subst hij
    rfl
  · simp only [tabB, cartanC, Matrix.transpose_apply, Matrix.of_apply, hij, Ne.symm hij,
      ite_false]
    split_ifs <;> omega

theorem cartanD_symm (n : ℕ) (i j : Fin n) : cartanD n i j = cartanD n j i := by
  by_cases hij : i = j
  · subst hij
    rfl
  · simp only [cartanD, Matrix.of_apply, hij, Ne.symm hij, ite_false]
    split_ifs <;> omega

theorem cartanA_symm (n : ℕ) (i j : Fin n) : CartanMatrix.A n i j = CartanMatrix.A n j i := by
  by_cases hij : i = j
  · subst hij
    rfl
  · simp only [CartanMatrix.A, Matrix.of_apply, hij, Ne.symm hij, ite_false]
    split_ifs <;> omega

theorem cartanE6_symm : ∀ i j : Fin 6, (Tag.cartan .E6) i j = (Tag.cartan .E6) j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

theorem cartanE7_symm : ∀ i j : Fin 7, (Tag.cartan .E7) i j = (Tag.cartan .E7) j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

theorem cartanE8_symm : ∀ i j : Fin 8, (Tag.cartan .E8) i j = (Tag.cartan .E8) j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

theorem tabF4_sym : ∀ i j : Fin 4, ![2, 2, 1, 1] i * (Tag.cartan .F4) i j =
    ![2, 2, 1, 1] j * (Tag.cartan .F4) j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

theorem tabG2_sym : ∀ i j : Fin 2, ![3, 1] i * (Tag.cartan .G2) i j =
    ![3, 1] j * (Tag.cartan .G2) j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide

section Tables

variable {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)

theorem isLongest_single_of_table (hirr : IsIrreducible A) {d : I → ℤ} (hd : ∀ i, 0 < d i)
    (hsym : ∀ i j, d i * A i j = d j * A j i) {k : I} (hk : ∀ j, d j ≤ d k) :
    IsLongest hA ∅ (Pi.single k 1) :=
  isLongest_single hA hirr (d := fun i => (d i : ℚ)) (fun i => by exact_mod_cast hd i)
    (fun i j => by exact_mod_cast hsym i j) (fun j => by exact_mod_cast hk j)

theorem exists_longest_partner_of_adjacent (hirr : IsIrreducible A) {d : I → ℤ}
    (hd : ∀ i, 0 < d i) (hsym : ∀ i j, d i * A i j = d j * A j i) {i j : I}
    (hij : A i j = -1) (hji : A j i = -1) (hi : ∀ l, d l ≤ d i) :
    ∃ γ₀ δ₀ : I → ℤ, IsLongest hA ∅ γ₀ ∧ IsLongest hA ∅ δ₀ ∧ IsPartner hA γ₀ δ₀ := by
  have hdij : d i = d j := by
    have := hsym i j
    rw [hij, hji] at this
    omega
  exact ⟨Pi.single i 1, Pi.single j 1, isLongest_single_of_table hA hirr hd hsym hi,
    isLongest_single_of_table hA hirr hd hsym (fun l => hdij ▸ hi l),
    isPartner_single_single hA hij hji⟩

theorem exists_longest_partner_of_triple (hirr : IsIrreducible A) {d : I → ℤ}
    (hd : ∀ i, 0 < d i) (hsym : ∀ i j, d i * A i j = d j * A j i) {i j : I}
    (hij : A i j * A j i = 3) (hi : ∀ l, d l ≤ d i) :
    ∃ γ₀ δ₀ : I → ℤ, IsLongest hA ∅ γ₀ ∧ IsLongest hA ∅ δ₀ ∧ IsPartner hA γ₀ δ₀ :=
  ⟨Pi.single i 1, _, isLongest_single_of_table hA hirr hd hsym hi,
    (isLongest_single_of_table hA hirr hd hsym hi).map_weylAction _,
    isPartner_single_reflection hA hij⟩

theorem isLongest_two_nsmul_single_of_table (hirr : IsIrreducible A) {d : I → ℤ}
    (hd : ∀ i, 0 < d i) (hsym : ∀ i j, d i * A i j = d j * A j i) {D : Set I} {k : I}
    (hkD : k ∈ D) (hk1 : ∀ i ∈ D, d i ≤ d k) (hk2 : ∀ j, d j ≤ 4 * d k) :
    IsLongest hA D (2 • Pi.single k 1) :=
  isLongest_two_nsmul_single hA hirr (d := fun i => (d i : ℚ)) (fun i => by exact_mod_cast hd i)
    (fun i j => by exact_mod_cast hsym i j) hkD (fun i hi => by exact_mod_cast hk1 i hi)
    (fun j => by exact_mod_cast hk2 j)

theorem symmetrizer_lt_four_mul (hirr : IsIrreducible A) {d : I → ℤ} (hd : ∀ i, 0 < d i)
    (hsym : ∀ i j, d i * A i j = d j * A j i) {D : Set I}
    (h : ∀ i ∈ D, ∀ j, d j < 4 * d i) :
    ∀ i ∈ D, ∀ j, symmetrizer hA j < 4 * symmetrizer hA i := by
  obtain ⟨c, hc, hcd⟩ := exists_symmetrizer_eq_smul (hA := hA) hirr (d := fun i => (d i : ℚ))
    (fun i => by exact_mod_cast hd i) (fun i j => by exact_mod_cast hsym i j)
  intro i hi j
  rw [hcd j, hcd i]
  have : (d j : ℚ) < 4 * d i := by exact_mod_cast h i hi j
  nlinarith

end Tables

section Family

theorem isLongest_single_A {m : ℕ} (hm : 0 < m) {M : Matrix (Fin m) (Fin m) ℤ}
    (hM : M = CartanMatrix.A m) (hA : TauCeti.IsFiniteType M) (k : Fin m) :
    IsLongest hA ∅ (Pi.single k 1) := by
  subst hM
  exact isLongest_single_of_table hA (isIrreducible_A hm) (d := fun _ => 1)
    (fun _ => one_pos) (fun i j => by simp [cartanA_symm m i j]) (fun _ => le_rfl)

theorem exists_partner_A {m : ℕ} (hm : 2 ≤ m) {M : Matrix (Fin m) (Fin m) ℤ}
    (hM : M = CartanMatrix.A m) (hA : TauCeti.IsFiniteType M) :
    ∃ γ₀ δ₀ : Fin m → ℤ, IsLongest hA ∅ γ₀ ∧ IsLongest hA ∅ δ₀ ∧ IsPartner hA γ₀ δ₀ := by
  subst hM
  refine exists_longest_partner_of_adjacent hA (isIrreducible_A (by omega)) (d := fun _ => 1)
    (fun _ => one_pos) (fun i j => by simp [cartanA_symm m i j]) (i := ⟨0, by omega⟩)
    (j := ⟨1, hm⟩) ?_ ?_ (fun _ => le_rfl)
  · simp [CartanMatrix.A]
  · simp [CartanMatrix.A]

theorem isLongest_single_cartanC {m : ℕ} (hm : 0 < m) {M : Matrix (Fin m) (Fin m) ℤ}
    (hM : M = cartanC m) (hA : TauCeti.IsFiniteType M) {k : Fin m} (hk : k.val + 1 = m) :
    IsLongest hA ∅ (Pi.single k 1) := by
  subst hM
  refine isLongest_single_of_table hA (isIrreducible_cartanC hm) (tabC_pos m) (tabC_sym m) ?_
  intro j
  simp only [tabC, hk, ite_true]
  split_ifs <;> omega

theorem isLongest_single_cartanB {m : ℕ} (hm : 0 < m) {M : Matrix (Fin m) (Fin m) ℤ}
    (hM : M = cartanB m) (hA : TauCeti.IsFiniteType M) {k : Fin m} (hk : k.val + 1 < m) :
    IsLongest hA ∅ (Pi.single k 1) := by
  subst hM
  refine isLongest_single_of_table hA (isIrreducible_cartanB hm) (tabB_pos m) (tabB_sym m) ?_
  intro j
  have hk' : ¬ (k.val + 1 = m) := by omega
  simp only [tabB, hk', ite_false]
  split_ifs <;> omega

theorem exists_partner_cartanB {m : ℕ} (hm : 3 ≤ m) {M : Matrix (Fin m) (Fin m) ℤ}
    (hM : M = cartanB m) (hA : TauCeti.IsFiniteType M) :
    ∃ γ₀ δ₀ : Fin m → ℤ, IsLongest hA ∅ γ₀ ∧ IsLongest hA ∅ δ₀ ∧ IsPartner hA γ₀ δ₀ := by
  subst hM
  refine exists_longest_partner_of_adjacent hA (isIrreducible_cartanB (by omega)) (tabB_pos m)
    (tabB_sym m) (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) ?_ ?_ ?_
  · simp [cartanB]
    omega
  · simp [cartanB]
    omega
  · intro l
    have h0 : ¬ (0 + 1 = m) := by omega
    simp only [tabB, h0, ite_false]
    split_ifs <;> omega

theorem isLongest_single_cartanD {n : ℕ} (hn : 3 ≤ n) {M : Matrix (Fin n) (Fin n) ℤ}
    (hM : M = cartanD n) (hA : TauCeti.IsFiniteType M) (k : Fin n) :
    IsLongest hA ∅ (Pi.single k 1) := by
  subst hM
  exact isLongest_single_of_table hA (isIrreducible_cartanD hn) (d := fun _ => 1)
    (fun _ => one_pos) (fun i j => by simp [cartanD_symm n i j]) (fun _ => le_rfl)

theorem exists_partner_cartanD {n : ℕ} (hn : 3 ≤ n) {M : Matrix (Fin n) (Fin n) ℤ}
    (hM : M = cartanD n) (hA : TauCeti.IsFiniteType M) :
    ∃ γ₀ δ₀ : Fin n → ℤ, IsLongest hA ∅ γ₀ ∧ IsLongest hA ∅ δ₀ ∧ IsPartner hA γ₀ δ₀ := by
  subst hM
  refine exists_longest_partner_of_adjacent hA (isIrreducible_cartanD hn) (d := fun _ => 1)
    (fun _ => one_pos) (fun i j => by simp [cartanD_symm n i j]) (i := ⟨0, by omega⟩)
    (j := ⟨1, by omega⟩) ?_ ?_ (fun _ => le_rfl)
  · simp [cartanD]
    omega
  · simp [cartanD]
    omega

theorem isLongest_single_E6 {M : Matrix (Fin 6) (Fin 6) ℤ} (hM : M = Tag.cartan .E6)
    (hA : TauCeti.IsFiniteType M) (k : Fin 6) : IsLongest hA ∅ (Pi.single k 1) := by
  subst hM
  exact isLongest_single_of_table hA isIrreducible_E6 (d := fun _ => 1) (fun _ => one_pos)
    (fun i j => by simp [cartanE6_symm i j]) (fun _ => le_rfl)

theorem isLongest_single_E7 {M : Matrix (Fin 7) (Fin 7) ℤ} (hM : M = Tag.cartan .E7)
    (hA : TauCeti.IsFiniteType M) (k : Fin 7) : IsLongest hA ∅ (Pi.single k 1) := by
  subst hM
  exact isLongest_single_of_table hA isIrreducible_E7 (d := fun _ => 1) (fun _ => one_pos)
    (fun i j => by simp [cartanE7_symm i j]) (fun _ => le_rfl)

theorem isLongest_single_E8 {M : Matrix (Fin 8) (Fin 8) ℤ} (hM : M = Tag.cartan .E8)
    (hA : TauCeti.IsFiniteType M) (k : Fin 8) : IsLongest hA ∅ (Pi.single k 1) := by
  subst hM
  exact isLongest_single_of_table hA isIrreducible_E8 (d := fun _ => 1) (fun _ => one_pos)
    (fun i j => by simp [cartanE8_symm i j]) (fun _ => le_rfl)

theorem exists_partner_E6 {M : Matrix (Fin 6) (Fin 6) ℤ} (hM : M = Tag.cartan .E6)
    (hA : TauCeti.IsFiniteType M) :
    ∃ γ₀ δ₀ : Fin 6 → ℤ, IsLongest hA ∅ γ₀ ∧ IsLongest hA ∅ δ₀ ∧ IsPartner hA γ₀ δ₀ := by
  subst hM
  exact exists_longest_partner_of_adjacent hA isIrreducible_E6 (d := fun _ => 1)
    (fun _ => one_pos) (fun i j => by simp [cartanE6_symm i j]) (i := 0) (j := 2) (by decide)
    (by decide) (fun _ => le_rfl)

theorem exists_partner_E7 {M : Matrix (Fin 7) (Fin 7) ℤ} (hM : M = Tag.cartan .E7)
    (hA : TauCeti.IsFiniteType M) :
    ∃ γ₀ δ₀ : Fin 7 → ℤ, IsLongest hA ∅ γ₀ ∧ IsLongest hA ∅ δ₀ ∧ IsPartner hA γ₀ δ₀ := by
  subst hM
  exact exists_longest_partner_of_adjacent hA isIrreducible_E7 (d := fun _ => 1)
    (fun _ => one_pos) (fun i j => by simp [cartanE7_symm i j]) (i := 0) (j := 2) (by decide)
    (by decide) (fun _ => le_rfl)

theorem exists_partner_E8 {M : Matrix (Fin 8) (Fin 8) ℤ} (hM : M = Tag.cartan .E8)
    (hA : TauCeti.IsFiniteType M) :
    ∃ γ₀ δ₀ : Fin 8 → ℤ, IsLongest hA ∅ γ₀ ∧ IsLongest hA ∅ δ₀ ∧ IsPartner hA γ₀ δ₀ := by
  subst hM
  exact exists_longest_partner_of_adjacent hA isIrreducible_E8 (d := fun _ => 1)
    (fun _ => one_pos) (fun i j => by simp [cartanE8_symm i j]) (i := 0) (j := 2) (by decide)
    (by decide) (fun _ => le_rfl)

theorem isLongest_single_F4 {M : Matrix (Fin 4) (Fin 4) ℤ} (hM : M = Tag.cartan .F4)
    (hA : TauCeti.IsFiniteType M) {k : Fin 4} (hk : k.val < 2) :
    IsLongest hA ∅ (Pi.single k 1) := by
  subst hM
  refine isLongest_single_of_table hA isIrreducible_F4 (d := ![2, 2, 1, 1]) ?_ tabF4_sym ?_
  · intro i
    fin_cases i <;> decide
  · intro j
    fin_cases k <;> fin_cases j <;> first | decide | (exfalso; simp at hk)

theorem exists_partner_F4 {M : Matrix (Fin 4) (Fin 4) ℤ} (hM : M = Tag.cartan .F4)
    (hA : TauCeti.IsFiniteType M) :
    ∃ γ₀ δ₀ : Fin 4 → ℤ, IsLongest hA ∅ γ₀ ∧ IsLongest hA ∅ δ₀ ∧ IsPartner hA γ₀ δ₀ := by
  subst hM
  refine exists_longest_partner_of_adjacent hA isIrreducible_F4 (d := ![2, 2, 1, 1]) ?_
    tabF4_sym (i := 0) (j := 1) (by decide) (by decide) ?_
  · intro i
    fin_cases i <;> decide
  · intro l
    fin_cases l <;> decide

theorem isLongest_single_G2 {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M = Tag.cartan .G2)
    (hA : TauCeti.IsFiniteType M) {k : Fin 2} (hk : k.val = 0) :
    IsLongest hA ∅ (Pi.single k 1) := by
  subst hM
  refine isLongest_single_of_table hA isIrreducible_G2 (d := ![3, 1]) ?_ tabG2_sym ?_
  · intro i
    fin_cases i <;> decide
  · intro j
    fin_cases k <;> fin_cases j <;> first | decide | (exfalso; simp at hk)

theorem exists_partner_G2 {M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M = Tag.cartan .G2)
    (hA : TauCeti.IsFiniteType M) :
    ∃ γ₀ δ₀ : Fin 2 → ℤ, IsLongest hA ∅ γ₀ ∧ IsLongest hA ∅ δ₀ ∧ IsPartner hA γ₀ δ₀ := by
  subst hM
  refine exists_longest_partner_of_triple hA isIrreducible_G2 (d := ![3, 1]) ?_ tabG2_sym
    (i := 0) (j := 1) (by decide) ?_
  · intro i
    fin_cases i <;> decide
  · intro l
    fin_cases l <;> decide

theorem isIrreducible_transpose_cartanC {n : ℕ} (hn : 0 < n) : IsIrreducible (cartanC n)ᵀ :=
  isIrreducible_of_chain hn fun a b hab => by
    have : a ≠ b := fun h => by rw [h] at hab; omega
    simp only [cartanC, Matrix.transpose_apply, Matrix.of_apply, this, this.symm, ite_false, hab,
      true_or, or_true, ite_true]
    split_ifs <;> simp

theorem isLongest_two_nsmul_single_BC {m : ℕ} (hm : 0 < m) {M : Matrix (Fin m) (Fin m) ℤ}
    (hM : M = (cartanC m)ᵀ) (hA : TauCeti.IsFiniteType M) {k : Fin m} (hk : k.val + 1 = m) :
    IsLongest hA {j : Fin m | j.val + 1 = m} (2 • Pi.single k 1) := by
  subst hM
  refine isLongest_two_nsmul_single_of_table hA (isIrreducible_transpose_cartanC hm) (tabB_pos m)
    (tabB_sym_transpose_cartanC m) (D := {j : Fin m | j.val + 1 = m}) hk ?_ ?_
  · intro i hi
    have hi' : i.val + 1 = m := hi
    simp only [tabB, hi', hk, ite_true]
    omega
  · intro j
    simp only [tabB, hk, ite_true]
    split_ifs <;> omega

theorem symmetrizer_lt_four_mul_BC {m : ℕ} (hm : 0 < m) {M : Matrix (Fin m) (Fin m) ℤ}
    (hM : M = (cartanC m)ᵀ) (hA : TauCeti.IsFiniteType M) :
    ∀ i ∈ {j : Fin m | j.val + 1 = m}, ∀ j, symmetrizer hA j < 4 * symmetrizer hA i := by
  subst hM
  refine symmetrizer_lt_four_mul hA (isIrreducible_transpose_cartanC hm) (tabB_pos m)
    (tabB_sym_transpose_cartanC m) ?_
  intro i hi j
  have hi' : i.val + 1 = m := hi
  simp only [tabB, hi', ite_true]
  split_ifs <;> omega

end Family

end CFSG.ClassicalInvolution.ModelFacts
