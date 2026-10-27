module

public import CFSG.CharacterTheory.Wreathed.BrauerWreathedOrderColumns
public import CFSG.CharacterTheory.OddOrderBasics.AlgebraicIntegers
public import CFSG.CharacterTheory.Wreathed.ConditionalFourierColumnsSections
public import CFSG.CharacterTheory.Wreathed.ConditionalGeneralBaseOrbits

public noncomputable section

open scoped Classical ComplexConjugate

namespace CFSG.Wreathed.BrauerWreathedOrder

open CFSG CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed CFSG.Wreathed.ConditionalFourier

variable {G : Type} [Group G] [Fintype G]

theorem character_eq_conj_inv (basis : FiniteIrreducibleCharacterBasis G) (χ : basis.index)
    (g : G) :
    (basis.representation χ).character g = conj ((basis.representation χ).character g⁻¹) := by
  have h :=
    CFSG.OddOrderBasics.complex_character_inversion (basis.representation χ).representation g
  change _ = conj ((basis.representation χ).representation.character g⁻¹)
  rw [h, Complex.conj_conj]

theorem sum_principal_character_mul_eq_zero (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index) {u z : G}
    (hu : ¬ Odd (orderOf u)) (hz : Odd (orderOf z)) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (basis.representation χ).character u * (basis.representation χ).character z = 0 := by
  have hz' : Odd (orderOf z⁻¹) := by rwa [orderOf_inv]
  rw [← sum_principal_character_mul_conj_eq_zero basis ideal principal hu hz']
  exact Finset.sum_congr rfl fun χ _ => by rw [character_eq_conj_inv basis χ z]

theorem sum_principal_combination_mul_eq_zero (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index) {ι : Type*}
    (s : Finset ι) (w : ι → G) (hw : ∀ i ∈ s, ¬ Odd (orderOf (w i))) (coeff : ι → ℂ)
    (c : basis.index → ℂ)
    (hc : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      c χ = ∑ i ∈ s, coeff i * (basis.representation χ).character (w i))
    {z : G} (hz : Odd (orderOf z)) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      c χ * (basis.representation χ).character z = 0 := by
  have hz' : Odd (orderOf z⁻¹) := by rwa [orderOf_inv]
  rw [← sum_principal_combination_mul_conj_eq_zero basis ideal principal s w hw coeff c hc hz']
  exact Finset.sum_congr rfl fun χ _ => by rw [character_eq_conj_inv basis χ z]

omit [Fintype G] in
theorem not_odd_orderOf_mul {x r : G} (hx : ¬ Odd (orderOf x)) (hxr : Commute x r)
    (hr : Odd (orderOf r)) (hx2 : ∃ k : ℕ, orderOf x = 2 ^ k) : ¬ Odd (orderOf (x * r)) := by
  obtain ⟨k, hk⟩ := hx2
  have hcop : Nat.Coprime (orderOf x) (orderOf r) := by
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hr)
  rw [hxr.orderOf_mul_eq_mul_orderOf_of_coprime hcop, Nat.odd_mul]
  exact fun h => hx h.1

theorem sum_rows_mul_eq_zero (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (principal : basis.index)
    (a : G) (m : ℕ) (C : ℕ → Subgroup G) (Φ : G → ℂ) (ε : ℤ) (hε : ε ≠ 0)
    (v : basis.index → ℕ → Fin 2 → ℂ)
    (hv : IsCentralSectionRows basis ideal principal a m C Φ ε v)
    (huniq : ∀ k ∈ Finset.Ico 1 m, ∀ w : Fin 2 → ℂ,
      (∀ r ∈ C k, Odd (orderOf r) →
        (basis.representation principal).character (a ^ k * r) = w 0 + w 1 * (1 + ε * Φ r)) →
      w = v principal k)
    (hC : ∀ k ∈ Finset.Ico 1 m, ∀ r ∈ C k, Odd (orderOf r) → ¬ Odd (orderOf (a ^ k * r)))
    {k : ℕ} (hk : k ∈ Finset.Ico 1 m) (ℓ : Fin 2) {z : G} (hz : Odd (orderOf z)) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      v χ k ℓ * (basis.representation χ).character z = 0 := by
  have hprin : principal ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal :=
    coefficientBlock_self_mem basis _ principal
  have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
  obtain ⟨r₁, hr₁, hr₁o, r₂, hr₂, hr₂o, hne⟩ : ∃ r₁ ∈ C k, Odd (orderOf r₁) ∧
      ∃ r₂ ∈ C k, Odd (orderOf r₂) ∧ Φ r₁ ≠ Φ r₂ := by
    by_contra hall
    push Not at hall
    have h1 : (1 : G) ∈ C k := (C k).one_mem
    have h1o : Odd (orderOf (1 : G)) := by rw [orderOf_one]; exact odd_one
    have hconst : ∀ r ∈ C k, Odd (orderOf r) → Φ r = Φ 1 := fun r hr hro => hall r hr hro 1 h1 h1o
    have hw := huniq k hk ![v principal k 0 + (1 + ε * Φ 1), v principal k 1 - 1] (by
      intro r hr hro
      rw [hv principal hprin k hk r hr hro, hconst r hr hro]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      ring)
    have h := congrFun hw 1
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h
    have : (1 : ℂ) = 0 := by linear_combination -h
    exact one_ne_zero this
  set t₁ : ℂ := 1 + ε * Φ r₁ with ht₁
  set t₂ : ℂ := 1 + ε * Φ r₂ with ht₂
  have ht : t₁ - t₂ ≠ 0 := by
    rw [ht₁, ht₂]
    intro h
    apply hne
    have : (ε : ℂ) * (Φ r₁ - Φ r₂) = 0 := by linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hε')
  let coeff : Fin 2 → ℂ := fun i =>
    if ℓ = 0 then (![-t₂, t₁] i) / (t₁ - t₂) else (![1, -1] i) / (t₁ - t₂)
  apply sum_principal_combination_mul_eq_zero basis ideal principal Finset.univ
    ![a ^ k * r₁, a ^ k * r₂] _ coeff _ _ hz
  · intro i _
    fin_cases i
    · exact hC k hk r₁ hr₁ hr₁o
    · exact hC k hk r₂ hr₂ hr₂o
  · intro χ hχ
    have e₁ := hv χ hχ k hk r₁ hr₁ hr₁o
    have e₂ := hv χ hχ k hk r₂ hr₂ hr₂o
    rw [← ht₁] at e₁
    rw [← ht₂] at e₂
    rw [Fin.sum_univ_two]
    simp only [coeff, Matrix.cons_val_zero, Matrix.cons_val_one]
    fin_cases ℓ
    · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte]
      rw [e₁, e₂]
      field_simp
      ring
    · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
      rw [e₁, e₂]
      field_simp
      ring

theorem orbitKey_injective (m : ℕ) [NeZero m] :
    Function.Injective fun I : ZMod m × ZMod m => I.1.val * m + I.2.val := by
  intro I J hIJ
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have h1 := ZMod.val_lt I.2
  have h2 := ZMod.val_lt J.2
  have hdiv : I.1.val = J.1.val := by
    have e1 : (I.1.val * m + I.2.val) / m = I.1.val := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt h1, zero_add]
    have e2 : (J.1.val * m + J.2.val) / m = J.1.val := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt h2, zero_add]
    rw [← e1, ← e2]
    exact congrArg (· / m) hIJ
  have hmod : I.2.val = J.2.val := by
    have : I.1.val * m + I.2.val = J.1.val * m + J.2.val := hIJ
    rw [hdiv] at this
    omega
  exact Prod.ext (ZMod.val_injective m hdiv) (ZMod.val_injective m hmod)

theorem exists_orbitRepresentatives (m : ℕ) [NeZero m] :
    ∃ V : Finset (ZMod m × ZMod m),
      (∀ I ∈ V, (MulAction.orbit (ConditionalGeneralBase.dualGroup m) I).ncard = 6) ∧
      ∀ I, (MulAction.orbit (ConditionalGeneralBase.dualGroup m) I).ncard = 6 →
        ∃! I', I' ∈ V ∧ I' ∈ MulAction.orbit (ConditionalGeneralBase.dualGroup m) I := by
  set K := ConditionalGeneralBase.dualGroup m
  let key : ZMod m × ZMod m → ℕ := fun I => I.1.val * m + I.2.val
  have hkey : Function.Injective key := orbitKey_injective m
  refine ⟨Finset.univ.filter fun I => (MulAction.orbit K I).ncard = 6 ∧
    ∀ I' ∈ MulAction.orbit K I, key I ≤ key I', fun I hI => (Finset.mem_filter.mp hI).2.1,
    fun I hI => ?_⟩
  set T := (Set.toFinite (MulAction.orbit K I)).toFinset
  have hT : T.Nonempty := ⟨I, (Set.Finite.mem_toFinset _).mpr (MulAction.mem_orbit_self I)⟩
  obtain ⟨I₀, hI₀, hmin⟩ := Finset.exists_min_image T key hT
  have hI₀' : I₀ ∈ MulAction.orbit K I := (Set.Finite.mem_toFinset _).mp hI₀
  have horb : MulAction.orbit K I₀ = MulAction.orbit K I := MulAction.orbit_eq_iff.mpr hI₀'
  refine ⟨I₀, ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [horb]; exact hI, ?_⟩, hI₀'⟩, ?_⟩
  · intro I' hI'
    rw [horb] at hI'
    exact hmin I' ((Set.Finite.mem_toFinset _).mpr hI')
  · rintro J ⟨hJV, hJ⟩
    obtain ⟨-, -, hJmin⟩ := Finset.mem_filter.mp hJV
    have hJorb : MulAction.orbit K J = MulAction.orbit K I := MulAction.orbit_eq_iff.mpr hJ
    apply hkey
    apply le_antisymm
    · exact hJmin I₀ (by rw [hJorb]; exact hI₀')
    · exact hmin J ((Set.Finite.mem_toFinset _).mpr hJ)

end CFSG.Wreathed.BrauerWreathedOrder
