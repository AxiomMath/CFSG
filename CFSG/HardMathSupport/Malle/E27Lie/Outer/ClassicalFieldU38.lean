module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalFieldXAbs
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.Classical CFSG.RankThree.UnitaryDescent CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.Chevalley (fixSubfield)
open CFSG.HardMathSupport.Lang.Coordinator

section Field

variable {F : Type} [Field F] [Finite F]

theorem card_cubeRoots_le : Nat.card {y : F // y ^ 3 = 1} ≤ 3 := by
  classical
  have h : Nat.card {y : F // y ^ 3 = 1} = (Polynomial.nthRootsFinset 3 (1 : F)).card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun y =>
      (Polynomial.mem_nthRootsFinset (by norm_num) (1 : F)).symm)
  rw [h, Polynomial.nthRootsFinset_def]
  exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots 3 1)

theorem apply_eq_self_of_pow_three (σ : F ≃+* F) (h4 : Nat.card (fixSubfield σ) = 4) {y : F}
    (hy : y ^ 3 = 1) : σ y = y := by
  have hu : Nat.card (fixSubfield σ)ˣ = 3 := by rw [Nat.card_units, h4]
  let f : (fixSubfield σ)ˣ → {y : F // y ^ 3 = 1} := fun c =>
    ⟨((c : fixSubfield σ) : F), by
      have := congrArg (fun u : (fixSubfield σ)ˣ => ((u : fixSubfield σ) : F))
        (pow_card_eq_one' (G := (fixSubfield σ)ˣ) (x := c))
      simpa [hu] using this⟩
  have hinj : Function.Injective f := fun c d hcd => by
    have h' := congrArg Subtype.val hcd
    exact Units.ext (Subtype.ext h')
  have hbij : Function.Bijective f :=
    hinj.bijective_of_nat_card_le (by rw [hu]; exact card_cubeRoots_le)
  obtain ⟨c, hc⟩ := hbij.2 ⟨y, hy⟩
  have : y = ((c : fixSubfield σ) : F) := congrArg Subtype.val hc.symm
  rw [this]
  exact (c : fixSubfield σ).2

theorem exists_ninth_root (hF : Nat.card F = 64) (σ : F ≃+* F)
    (h4 : Nat.card (fixSubfield σ) = 4) : ∃ a : Fˣ, a ^ 9 = 1 ∧ σ (a : F) ≠ a := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hcard : Nat.card Fˣ = 63 := by rw [Nat.card_units, hF]
  have hog : orderOf g = 63 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have hox : orderOf (g ^ 7) = 9 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hog]; norm_num), hog]
  refine ⟨g ^ 7, by rw [← hox]; exact pow_orderOf_eq_one _, fun hfix => ?_⟩
  have hmem : ((g ^ 7 : Fˣ) : F) ∈ fixSubfield σ := hfix
  let u : (fixSubfield σ)ˣ := Units.mk0 ⟨_, hmem⟩ (by
    intro h0
    exact (g ^ 7).ne_zero (congrArg Subtype.val h0))
  have hu : Nat.card (fixSubfield σ)ˣ = 3 := by rw [Nat.card_units, h4]
  have h3 : u ^ 3 = 1 := by rw [← hu]; exact pow_card_eq_one'
  have h3' : (g ^ 7) ^ 3 = 1 := by
    apply Units.ext
    have := congrArg (fun v : (fixSubfield σ)ˣ => ((v : fixSubfield σ) : F)) h3
    simpa [u] using this
  have := orderOf_dvd_of_pow_eq_one h3'
  rw [hox] at this
  omega

end Field

section Unitary

variable {ℓ f : ℕ} {F : Type} [Field F]

@[expose] def diag3 (a b c : Fˣ) : GL (Fin 3) F :=
  ⟨diagonal ![(a : F), b, c], diagonal ![((a⁻¹ : Fˣ) : F), ((b⁻¹ : Fˣ) : F), ((c⁻¹ : Fˣ) : F)],
    by
      rw [diagonal_mul_diagonal]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [diagonal_apply],
    by
      rw [diagonal_mul_diagonal]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [diagonal_apply]⟩

theorem coe_diag3 (a b c : Fˣ) :
    ((diag3 a b c : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = diagonal ![(a : F), b, c] :=
  rfl

theorem diag3_mem_gramSU (h : UnitaryFieldData ℓ f F) {a b c : Fˣ} (ha : h.norm (a : F) = 1)
    (hb : h.norm (b : F) = 1) (hc : h.norm (c : F) = 1) (hdet : a * b * c = 1) :
    diag3 a b c ∈ gramSU h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  rw [mem_gramSU, coe_diag3, Units.val_one, Matrix.mul_one,
    diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagonal_apply, UnitaryFieldData.norm, mul_comm, ha, hb, hc] <;>
      first | exact ha | exact hb | exact hc | skip
  · rw [det_diagonal, Fin.prod_univ_three]
    simpa using congrArg Units.val hdet

theorem card_normOneScalars_dvd_three [Finite F] (h : UnitaryFieldData ℓ f F) :
    Nat.card (normOneScalars h (gramSU h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) 3) ∣
      3 := by
  classical
  set Z := normOneScalars h (gramSU h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) 3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 Z := by
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨c, -, hc3, hg⟩ := g.2
    have key : (g.1.1 : GL (Fin 3) F) ^ 3 = 1 := by
      rw [hg, ← map_pow, hc3, map_one]
    refine Subtype.ext (Subtype.ext ?_)
    simpa only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one] using key
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hp
  let e : Z → {y : F // y ^ 3 = 1} := fun g =>
    ⟨((g.1.1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0, by
      obtain ⟨c, -, hc3, hg⟩ := g.2
      rw [hg, GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq]
      rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]⟩
  have hinj : Function.Injective e := by
    intro g g' hgg
    obtain ⟨c, -, -, hg⟩ := g.2
    obtain ⟨c', -, -, hg'⟩ := g'.2
    have h1 : (c : F) = c' := by
      have := congrArg Subtype.val hgg
      simpa [e, hg, hg', GeneralLinearGroup.coe_scalar, scalar_apply] using this
    have h2 : c = c' := Units.ext h1
    apply Subtype.ext
    apply Subtype.ext
    rw [hg, hg', h2]
  have hle : Nat.card Z ≤ 3 :=
    (Nat.card_le_card_of_injective e hinj).trans card_cubeRoots_le
  rw [hn] at hle ⊢
  rcases n with _ | _ | n
  · simp
  · simp
  · exfalso
    have : 3 ^ (n + 2) = 9 * 3 ^ n := by ring
    have := Nat.one_le_pow n 3 (by norm_num)
    omega

theorem card_gramSU_one_two {K : Type} [Field K] {e : ℕ} (h : UnitaryFieldData 2 e K) :
    Nat.card (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) =
      (2 ^ e) ^ 3 * ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 + 1) := by
  have hfin : Finite K := h.finite
  have : Fintype K := Fintype.ofFinite K
  have h1 : ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := Units.val_one
  have hB : (gramForm h (1 : Matrix (Fin 3) (Fin 3) K)).IsSymm :=
    gramForm_isSymm h (by simp)
  have hBl : (gramForm h (1 : Matrix (Fin 3) (Fin 3) K)).SeparatingLeft :=
    gramForm_separatingLeft h (by simp)
  have hSU := (CFSG.LinearGroups.unitary_full_group_order h hB hBl
    (Module.finrank_fin_fun K) (by norm_num)).2.1
  rw [h1, card_gramSU]
  have hIcc : Finset.Icc 2 3 = {2, 3} := by decide
  rw [hIcc, Finset.prod_pair (by norm_num)] at hSU
  have hr1 : 1 ≤ (2 ^ e) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have : ((Nat.card (sesqSpecialUnitaryGroup (gramForm h (1 : Matrix (Fin 3) (Fin 3) K))) : ℕ) :
      ℤ) = (((2 ^ e) ^ 3 * ((2 ^ e) ^ 2 - 1) * ((2 ^ e) ^ 3 + 1) : ℕ) : ℤ) := by
    rw [hSU]
    push_cast [Nat.cast_sub hr1]
    norm_num
    ring
  exact_mod_cast this

theorem twentySeven_dvd_fixed_PSU_three_eight [Finite F] (h : UnitaryFieldData ℓ f F)
    (hℓ : ℓ = 2) (hf : f = 3) {σ : F ≃+* F} (hσ : orderOf σ = 3) :
    27 ∣ Nat.card (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup
      (primeFormFieldHom h (isPrimeFormGram_one (n := 3)) σ)) := by
  classical
  subst hℓ hf
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hF : Nat.card F = 64 := by rw [h.card]; norm_num
  obtain ⟨-, hcard⟩ := dvd_and_card_fixSubfield_unitary h hp hp2 hσ
  have h4 : Nat.card (fixSubfield σ) = 4 := by rw [hcard]; norm_num
  have h₀ := fixSubfield_unitaryFieldData h hp hp2 hσ
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  obtain ⟨a, ha9, hσa⟩ := exists_ninth_root hF σ h4
  have hn9 : ∀ c : Fˣ, c ^ 9 = 1 → h.norm (c : F) = 1 := fun c hc => by
    show (c : F) * h.bar c = 1
    rw [h.bar_apply]
    have : (c : F) ^ 9 = 1 := by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
    calc (c : F) * (c : F) ^ (2 ^ 3) = (c : F) ^ 9 := by ring
      _ = 1 := this
  have haF : (a : F) ^ 9 = 1 := by rw [← Units.val_pow_eq_pow_val, ha9, Units.val_one]
  have hσa0 : σ (a : F) ≠ 0 := (map_ne_zero σ).2 a.ne_zero
  let ω : Fˣ := Units.mk0 (σ (a : F) / a) (div_ne_zero hσa0 a.ne_zero)
  have hωF : (ω : F) = σ (a : F) / a := rfl
  have hωa : σ (a : F) = ω * a := by rw [hωF]; field_simp
  have hσa3 : σ ((a : F) ^ 3) = (a : F) ^ 3 :=
    apply_eq_self_of_pow_three σ h4 (by rw [← pow_mul]; exact haF)
  have hω3F : (ω : F) ^ 3 = 1 := by
    rw [hωF, div_pow, ← map_pow, hσa3, div_self (pow_ne_zero 3 a.ne_zero)]
  have hω3 : ω ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hω3F, Units.val_one])
  have hω9 : ω ^ 9 = 1 := by
    rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul, hω3, one_pow]
  have hωne : ω ≠ 1 := by
    intro h1
    apply hσa
    rw [hωa, h1, Units.val_one, one_mul]
  let b : Fˣ := a⁻¹ * a⁻¹
  have hb9 : b ^ 9 = 1 := by
    show (a⁻¹ * a⁻¹) ^ 9 = 1
    rw [mul_pow, inv_pow, ha9]
    simp
  have hdet : a * a * b = 1 := by
    show a * a * (a⁻¹ * a⁻¹) = 1
    group
  have hσb : σ (b : F) = ω * b := by
    have hωinv : (ω : F)⁻¹ = (ω : F) ^ 2 := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_succ']
      exact hω3F
    have : σ (b : F) = (σ (a : F))⁻¹ * (σ (a : F))⁻¹ := by
      show σ (((a⁻¹ * a⁻¹ : Fˣ)) : F) = _
      rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
    rw [this, hωa]
    show _ = (ω : F) * ((a⁻¹ * a⁻¹ : Fˣ) : F)
    rw [Units.val_mul, Units.val_inv_eq_inv_val, mul_inv, hωinv]
    linear_combination ((ω : F) * ((a : F)⁻¹ * (a : F)⁻¹)) * hω3F
  have hsc : (GeneralLinearGroup.scalar (Fin 3) ω : GL (Fin 3) F) = diag3 ω ω ω :=
    Units.ext (by
      rw [GeneralLinearGroup.coe_scalar, coe_diag3, scalar_apply]
      congr 1
      funext i
      fin_cases i <;> rfl)
  have hωdet : ω * ω * ω = 1 := by rw [mul_assoc, ← pow_three, hω3]
  have hzmem := diag3_mem_gramSU h (hn9 ω hω9) (hn9 ω hω9) (hn9 ω hω9) hωdet
  have hgmem := diag3_mem_gramSU h (hn9 a ha9) (hn9 a ha9) (hn9 b hb9) hdet
  let z0 : gramSU h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := ⟨diag3 ω ω ω, hzmem⟩
  let g0 : gramSU h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := ⟨diag3 a a b, hgmem⟩
  have hz0 : z0 ∈ normOneScalars h (gramSU h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) 3 :=
    ⟨ω, hn9 ω hω9, hω3, hsc.symm⟩
  let σS := primeFormFieldSU h (isPrimeFormGram_one (n := 3)) σ
  have hg0 : σS g0 = z0 * g0 := by
    refine Subtype.ext (Units.ext ?_)
    change ((g0 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map σ = _
    rw [Subgroup.coe_mul, Units.val_mul]
    change (diagonal ![(a : F), a, b]).map σ = diagonal ![(ω : F), ω, ω] * diagonal ![(a : F), a, b]
    rw [diagonal_map (map_zero _), diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i
    · exact hωa
    · exact hωa
    · exact hσb
  have hord : orderOf z0 = 3 := by
    apply orderOf_eq_prime
    · refine Subtype.ext ?_
      rw [Subgroup.coe_pow, show ((z0 : GL (Fin 3) F)) = GeneralLinearGroup.scalar (Fin 3) ω from
        hsc.symm, ← map_pow, hω3, map_one]
      rfl
    · intro h1
      have h2 : (z0 : GL (Fin 3) F) = 1 := congrArg Subtype.val h1
      rw [show ((z0 : GL (Fin 3) F)) = GeneralLinearGroup.scalar (Fin 3) ω from hsc.symm] at h2
      have h3 := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 0 0) h2
      simp [GeneralLinearGroup.coe_scalar, scalar_apply] at h3
      exact hωne h3
  have hinj := subfieldSU_injective h h₀ hbar 3
  have hK : ∀ k ∈ (subfieldSU h h₀ hbar 3).range, σS k = k := by
    rintro _ ⟨g, rfl⟩
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    exact (((g : GL (Fin 3) (fixSubfield σ)) : Matrix (Fin 3) (Fin 3) (fixSubfield σ)) i j).2
  have h27 : 27 ∣ Nat.card (subfieldSU h h₀ hbar 3).range := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, card_gramSU_one_two h₀]
    norm_num
  exact twentySeven_dvd_card_eqLocus_of_twist _ (normOneScalars_le_center h _ 3)
    (card_normOneScalars_dvd_three h) σS (primeFormFieldHom h (isPrimeFormGram_one (n := 3)) σ)
    (fun g => primeFormFieldAut_mk h isPrimeFormGram_one σ g) _ hK h27 g0 z0 hz0 hg0 hord

end Unitary

section Final

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem exists_fixed_three_subgroup_of_dvd_U38 {K : Type} [Group K] [Finite K] (u : MulAut K)
    (h : 27 ∣ Nat.card (fixedSubgroup u)) :
    ∃ Q : Subgroup K, (∀ x ∈ Q, u x = x) ∧ IsPGroup 3 Q ∧ 27 ≤ Nat.card Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 ↥(fixedSubgroup u)))
  refine ⟨(P : Subgroup ↥(fixedSubgroup u)).map (fixedSubgroup u).subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · exact P.isPGroup'.map _
  · rw [Subgroup.card_map_of_injective (fixedSubgroup u).subtype_injective,
      Sylow.card_eq_multiplicity P]
    have h3 : 3 ^ 3 ∣ Nat.card (fixedSubgroup u) := by simpa using h
    have hne : Nat.card (fixedSubgroup u) ≠ 0 := Nat.card_pos.ne'
    have : 3 ≤ (Nat.card (fixedSubgroup u)).factorization 3 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).1 h3
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (Nat.card (fixedSubgroup u)).factorization 3 :=
        Nat.pow_le_pow_right (by norm_num) this

variable {ℓ f : ℕ} {F : Type} [Field F] [Finite F]

theorem exists_fixed_three_subgroup_PSU_three_eight (h : UnitaryFieldData ℓ f F) (hn : 3 ≤ 3)
    (hne : ¬(3 = 3 ∧ ℓ ^ f = 2)) (hq0 : ℓ ^ (f / 3) = 2)
    (β : MulAut (primeFormP h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)))
    (hβ3 : β ^ 3 = 1) (hσ1 : primeFormFieldFactor h isPrimeFormGram_one hn hne β ≠ 1) :
    ∃ Q : Subgroup (primeFormP h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)),
      (∀ x ∈ Q, β x = x) ∧ IsPGroup 3 Q ∧ 27 ≤ Nat.card Q := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hβ1 : β ≠ 1 := fun h1 => hσ1 (by rw [h1, map_one])
  have hβord : orderOf β = 3 := orderOf_eq_prime hβ3 hβ1
  set σ := primeFormFieldFactor h isPrimeFormGram_one hn hne β with hσdef
  have hσp : σ ^ 3 = 1 := by rw [hσdef, ← map_pow, hβ3, map_one]
  have hσord : orderOf σ = 3 := orderOf_eq_prime hσp hσ1
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    unitary_prime_semilinear_field_descent' h hn hne hp hp2 β hβord σ hσdef.symm hσord
  set u := primeFormConjHom h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) M with hu
  set fσ := primeFormFieldHom h (isPrimeFormGram_one (n := 3)) σ with hfσ
  have hβu : β * u = u * fσ := by
    rw [← hM]
    group
  have hpf := (dvd_and_card_fixSubfield_unitary h hp hp2 hσord).1
  have hℓ : ℓ = 2 := by
    have hm : f / 3 ≠ 0 := by
      intro h0
      rw [h0] at hq0
      norm_num at hq0
    have : ℓ ∣ 2 := hq0 ▸ dvd_pow_self ℓ hm
    exact (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 this
  have hf : f = 3 := by
    subst hℓ
    have h1 : f / 3 = 1 := Nat.pow_right_injective le_rfl (by simpa using hq0)
    omega
  have h27 : 27 ∣ Nat.card (fixedSubgroup fσ) :=
    twentySeven_dvd_fixed_PSU_three_eight h hℓ hf hσord
  have hcard : Nat.card (fixedSubgroup fσ) = Nat.card (fixedSubgroup β) :=
    card_fixedSubgroup_eq_of_intertwine u fσ β fun x => by
      have := congrArg (fun g : MulAut _ => g x) hβu
      simpa only [MulAut.mul_apply] using this
  have : Finite (primeFormP h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := inferInstance
  exact exists_fixed_three_subgroup_of_dvd_U38 β (hcard ▸ h27)

theorem unitary_three_eight_false (h : UnitaryFieldData ℓ f F) (hn : 3 ≤ 3)
    (hne : ¬(3 = 3 ∧ ℓ ^ f = 2)) (hq0 : ℓ ^ (f / 3) = 2)
    (β : MulAut (primeFormP h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)))
    (hβ3 : β ^ 3 = 1) (hσ : primeFormFieldFactor h isPrimeFormGram_one hn hne β ≠ 1)
    (hQ : ∀ Q : Subgroup (primeFormP h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)),
      (∀ x ∈ Q, β x = x) → IsPGroup 3 Q → Nat.card Q ≤ 9) : False := by
  obtain ⟨Q, hfix, hQ3, hcard⟩ :=
    exists_fixed_three_subgroup_PSU_three_eight h hn hne hq0 β hβ3 hσ
  have := hQ Q hfix hQ3
  omega

end Final

end CFSG.HardMathSupport.Malle.E27Lie
