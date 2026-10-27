module

public import CFSG.GH74.GLS.Stage4.T2NegCfgThreeMat

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open CFSG.GH74.GLS

private theorem sdwK_aux_setup {X : Type} [Group X] {K : Subgroup X} {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : 3 ≤ p ^ n) (hK : HasSL2Model ↥K (fun q => q = p ^ n)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ n ∧ (p : F) = 0 ∧ Odd (Nat.card F) ∧
      (2 : F) ≠ 0 ∧ Nonempty (↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨F, iF, iFin, hF, ⟨e₀⟩⟩ := hK
  have hn : n ≠ 0 := by
    rintro rfl
    simp at hq
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (hp.odd_of_ne_two hp2).pow
  refine ⟨F, iF, iFin, hF, ?_, hodd, T2.two_ne_zero_of_odd_card hodd,
    ⟨e₀.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm⟩⟩
  have : Fintype F := Fintype.ofFinite F
  have h := Nat.cast_card_eq_zero F
  rw [← Nat.card_eq_fintype_card, hF, Nat.cast_pow] at h
  exact (pow_eq_zero_iff hn).1 h

private theorem sdwK_aux_transvection_pow {F : Type} [Field F] {p : ℕ} (h0 : (p : F) = 0)
    (i j : Fin 2) (h : i ≠ j) (c : F) :
    Matrix.SpecialLinearGroup.transvection h c ^ p = 1 := by
  have hpow : ∀ m : ℕ, Matrix.SpecialLinearGroup.transvection h c ^ m =
      Matrix.SpecialLinearGroup.transvection h ((m : F) * c) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, ih, ← Matrix.SpecialLinearGroup.transvection_add]
      congr 1
      push_cast
      ring
  rw [hpow p, h0, zero_mul, Matrix.SpecialLinearGroup.transvection_coeff_zero]

private theorem sdwK_aux_negOne_ne_one {F : Type} [Field F] (h2 : (2 : F) ≠ 0) :
    T2.negOne F ≠ 1 := by
  intro h
  have h' := congrArg
    (fun A : Matrix.SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp at h'
  apply h2
  linear_combination -h'

private theorem sdwK_aux_negOne_sq {F : Type} [Field F] : T2.negOne F * T2.negOne F = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, T2.coe_negOne]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem sdwK_aux_exists_unit {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) :
    ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  obtain ⟨x, hx⟩ : IsCyclic Fˣ := by infer_instance
  refine ⟨x, Units.ne_zero x, fun h ↦ ?_⟩
  grw [Nat.card_eq_card_units_add_one F, ← orderOf_eq_card_of_forall_mem_zpowers hx,
    orderOf_le_of_pow_eq_one zero_lt_two (Units.ext <| by simpa using h)] at h4
  omega

private theorem sdwK_aux_perfect {F : Type} [Field F] [Finite F] (h4 : 4 ≤ Nat.card F) :
    Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨a, ha, hasq⟩ := sdwK_aux_exists_unit h4
  exact ⟨Matrix.SL2.commutator_eq_top ha hasq⟩

theorem sdwK_hom_two_group {X : Type} [Group X] {K : Subgroup X} {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : 3 ≤ p ^ n) (hK : HasSL2Model ↥K (fun q => q = p ^ n)) {P : Type} [Group P] (hP : IsPGroup 2 P)
    (φ : ↥K →* P) : φ = 1 := by
  obtain ⟨F, iF, iFin, hF, h0, -, -, ⟨e⟩⟩ := sdwK_aux_setup hp hp2 hq hK
  let ψ : Matrix.SpecialLinearGroup (Fin 2) F →* P := φ.comp e.symm.toMonoidHom
  have htv : ∀ (i j : Fin 2) (h : i ≠ j) (c : F),
      ψ (Matrix.SpecialLinearGroup.transvection h c) = 1 := by
    intro i j h c
    have hp1 : (ψ (Matrix.SpecialLinearGroup.transvection h c)) ^ p = 1 := by
      rw [← map_pow, sdwK_aux_transvection_pow h0 i j h c, map_one]
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf (p := 2)).1 hP
      (ψ (Matrix.SpecialLinearGroup.transvection h c))
    have hdvd : 2 ^ k ∣ p := hk ▸ orderOf_dvd_of_pow_eq_one hp1
    have hcop : Nat.Coprime (2 ^ k) p :=
      Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
    rw [Nat.Coprime.eq_one_of_dvd hcop hdvd] at hk
    exact orderOf_eq_one_iff.1 hk
  have hall : ∀ A, ψ A = 1 := fun A =>
    Matrix.SL2.transvection_induction (fun A => ψ A = 1) htv
      (fun A B hA hB => by rw [map_mul, hA, hB, one_mul]) A
  ext k
  simpa [ψ] using hall (e k)

theorem sdwK_quaternion_pair {X : Type} [Group X] {K : Subgroup X} {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : 3 ≤ p ^ n) (hK : HasSL2Model ↥K (fun q => q = p ^ n)) :
    ∃ i j : X, i ∈ K ∧ j ∈ K ∧ orderOf i = 4 ∧ j * i * j⁻¹ = i⁻¹ ∧ j * j = i * i := by
  obtain ⟨F, iF, iFin, hF, -, hodd, h2, ⟨e⟩⟩ := sdwK_aux_setup hp hp2 hq hK
  obtain ⟨a, b, hab⟩ := negF_sq_add_sq hodd (-1 : F)
  obtain ⟨W, hW⟩ := negF_exists_W (F := F)
  obtain ⟨V, hV⟩ := negF_exists_V hab
  have hWW := negF_sq_W hW
  have hVV := negF_sq_V hab hV
  have hVW := negF_VW h2 hW hV hVV
  have hW2 : W ^ 2 = T2.negOne F := by rw [pow_two, hWW]
  have hordW : orderOf W = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := W) ?_ ?_
    · simpa using h
    · rw [pow_one, hW2]
      exact sdwK_aux_negOne_ne_one h2
    · rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, hW2, pow_two]
      exact sdwK_aux_negOne_sq
  refine ⟨(e.symm W : ↥K), (e.symm V : ↥K), (e.symm W).2, (e.symm V).2, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hordW
  · have h := congrArg (fun A => ((e.symm A : ↥K) : X)) hVW
    simpa using h
  · have h := congrArg (fun A => ((e.symm A : ↥K) : X)) (hVV.trans hWW.symm)
    simpa using h

theorem sdwK_solvable_trivial {X : Type} [Group X] {K : Subgroup X} {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ n) (hK : HasSL2Model ↥K (fun q => q = p ^ n)) {P : Type} [Group P] [Group.IsSolvable P]
    (φ : ↥K →* P) : φ = 1 := by
  obtain ⟨F, iF, iFin, hF, -, -, -, ⟨e⟩⟩ := sdwK_aux_setup hp hp2 (by omega) hK
  have := sdwK_aux_perfect (F := F) (by omega)
  have : Group.IsPerfect ↥K :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have : Group.IsPerfect ↥φ.range := Group.IsPerfect.range φ
  have hsub : Subsingleton ↥φ.range := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isSolvable ↥φ.range inferInstance
  ext k
  have h : (⟨φ k, k, rfl⟩ : ↥φ.range) = 1 := Subsingleton.elim _ _
  simpa using congrArg Subtype.val h

end CFSG.GH74.GLS.Stage4.Rest
