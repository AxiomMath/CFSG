module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKFrameBasis
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKFramePerm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PPerm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmega

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.ClassicalInvolution

variable {U : Type} [AddCommGroup U] [Module (ZMod 3) U] [FiniteDimensional (ZMod 3) U]
  {R : QuadraticForm (ZMod 3) U}

private def fkFrame {ε : ZMod 3} (b : Module.Basis (Fin 3) (ZMod 3) U) (hb : ∀ i, R (b i) = ε)
    (hbo : ∀ i j, i ≠ j → QuadraticMap.polar R (b i) (b j) = 0) :
    PFrame R (Fin 3) (fun _ => ε) := ⟨b, hb, hbo⟩

private noncomputable def fkRefl {ε : ZMod 3} (hε : ε ≠ 0)
    (b : Module.Basis (Fin 3) (ZMod 3) U) (hb : ∀ i, R (b i) = ε) (i : Fin 3) : OGroup R :=
  @TauCeti.QuadraticMap.reflectionOrthogonal (ZMod 3) U _ _ _ R (b i)
    (invertibleOfNonzero (by rw [hb i]; exact hε))

private lemma fkRefl_self {ε : ZMod 3} (hε : ε ≠ 0) (b : Module.Basis (Fin 3) (ZMod 3) U)
    (hb : ∀ i, R (b i) = ε) (i : Fin 3) :
    ((fkRefl hε b hb i : OGroup R) : U ≃ₗ[ZMod 3] U) (b i) = -b i := by
  rw [fkRefl, TauCeti.QuadraticMap.coe_reflectionOrthogonal]
  exact @TauCeti.QuadraticMap.reflection_apply_self (ZMod 3) U _ _ _ R (b i)
    (invertibleOfNonzero (by rw [hb i]; exact hε))

private lemma fkRefl_of_ne {ε : ZMod 3} (hε : ε ≠ 0) (b : Module.Basis (Fin 3) (ZMod 3) U)
    (hb : ∀ i, R (b i) = ε)
    (hbo : ∀ i j, i ≠ j → QuadraticMap.polar R (b i) (b j) = 0)
    {i j : Fin 3} (hij : i ≠ j) :
    ((fkRefl hε b hb i : OGroup R) : U ≃ₗ[ZMod 3] U) (b j) = b j := by
  rw [fkRefl, TauCeti.QuadraticMap.coe_reflectionOrthogonal]
  exact @TauCeti.QuadraticMap.reflection_apply_of_polar_eq_zero (ZMod 3) U _ _ _ R (b i)
    (invertibleOfNonzero (by rw [hb i]; exact hε)) (b j) (hbo i j hij)

private lemma fkRefl_detSpinor {ε : ZMod 3} (hR : R.Nondegenerate) (hε : ε ≠ 0)
    (b : Module.Basis (Fin 3) (ZMod 3) U) (hb : ∀ i, R (b i) = ε) (i : Fin 3) :
    detSpinorNorm hR (fkRefl hε b hb i) =
      ((-1 : (ZMod 3)ˣ), TauCeti.squareClassHom (Units.mk0 ε hε)) := by
  letI : Invertible (R (b i)) := invertibleOfNonzero (by rw [hb i]; exact hε)
  rw [fkRefl, detSpinorNorm_reflectionOrthogonal]
  have hu : unitOfInvertible (R (b i)) = Units.mk0 ε hε := by
    apply Units.ext
    rw [Units.val_mk0, val_unitOfInvertible, hb i]
  rw [hu]

private lemma fk_norm {ε : ZMod 3} (b : Module.Basis (Fin 3) (ZMod 3) U) (hb : ∀ i, R (b i) = ε)
    (hbo : ∀ i j, i ≠ j → QuadraticMap.polar R (b i) (b j) = 0) (v : U) :
    R v = ε * (b.repr v 0 ^ 2 + b.repr v 1 ^ 2 + b.repr v 2 ^ 2) := by
  have h := (fkFrame (R := R) b hb hbo).map_eq v
  rw [h, Fin.sum_univ_three]
  dsimp [fkFrame]
  ring

private lemma fk_coords_cases (a0 a1 a2 : ZMod 3) (h : a0 ^ 2 + a1 ^ 2 + a2 ^ 2 = 1) :
    (a0 = 1 ∧ a1 = 0 ∧ a2 = 0) ∨ (a0 = -1 ∧ a1 = 0 ∧ a2 = 0) ∨
    (a0 = 0 ∧ a1 = 1 ∧ a2 = 0) ∨ (a0 = 0 ∧ a1 = -1 ∧ a2 = 0) ∨
    (a0 = 0 ∧ a1 = 0 ∧ a2 = 1) ∨ (a0 = 0 ∧ a1 = 0 ∧ a2 = -1) := by
  revert a0 a1 a2
  decide

private lemma fk_norm_eq_eps {ε : ZMod 3} (hε : ε ≠ 0) (b : Module.Basis (Fin 3) (ZMod 3) U)
    (hb : ∀ i, R (b i) = ε)
    (hbo : ∀ i j, i ≠ j → QuadraticMap.polar R (b i) (b j) = 0) {v : U}
    (hv : R v = ε) :
    ∃ (j : Fin 3) (s : ZMod 3), (s = 1 ∨ s = -1) ∧ v = s • b j := by
  have hsum : b.repr v 0 ^ 2 + b.repr v 1 ^ 2 + b.repr v 2 ^ 2 = 1 := by
    have h := fk_norm (R := R) b hb hbo v
    rw [hv] at h
    exact mul_left_cancel₀ hε (by rw [mul_one, ← h])
  have hvsum : v = ∑ i, b.repr v i • b i := (b.sum_repr v).symm
  rcases fk_coords_cases _ _ _ hsum with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
      ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · exact ⟨0, 1, Or.inl rfl, by rw [hvsum, Fin.sum_univ_three]; simp [h0, h1, h2]⟩
  · exact ⟨0, -1, Or.inr rfl, by rw [hvsum, Fin.sum_univ_three]; simp [h0, h1, h2]⟩
  · exact ⟨1, 1, Or.inl rfl, by rw [hvsum, Fin.sum_univ_three]; simp [h0, h1, h2]⟩
  · exact ⟨1, -1, Or.inr rfl, by rw [hvsum, Fin.sum_univ_three]; simp [h0, h1, h2]⟩
  · exact ⟨2, 1, Or.inl rfl, by rw [hvsum, Fin.sum_univ_three]; simp [h0, h1, h2]⟩
  · exact ⟨2, -1, Or.inr rfl, by rw [hvsum, Fin.sum_univ_three]; simp [h0, h1, h2]⟩

private lemma fk_isometry_basis {ε : ZMod 3} (hε : ε ≠ 0) (b : Module.Basis (Fin 3) (ZMod 3) U)
    (hb : ∀ i, R (b i) = ε)
    (hbo : ∀ i j, i ≠ j → QuadraticMap.polar R (b i) (b j) = 0) (g : OGroup R) (i : Fin 3) :
    ∃ (j : Fin 3) (s : ZMod 3), (s = 1 ∨ s = -1) ∧
      (g : U ≃ₗ[ZMod 3] U) (b i) = s • b j := by
  refine fk_norm_eq_eps (R := R) hε b hb hbo ?_
  rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup g.2 (b i), hb i]

private lemma fk_same_line_false (b : Module.Basis (Fin 3) (ZMod 3) U)
    {i j : Fin 3} (hij : i ≠ j) (c : OGroup R)
    {l : Fin 3} {a d : ZMod 3} (ha : a ≠ 0) (hd : d ≠ 0)
    (hi : (c : U ≃ₗ[ZMod 3] U) (b i) = a • b l)
    (hj : (c : U ≃ₗ[ZMod 3] U) (b j) = d • b l) : False := by
  have hrel : d • b i - a • b j = 0 := by
    apply (c : U ≃ₗ[ZMod 3] U).injective
    rw [map_sub, map_smul, map_smul, map_zero, hi, hj, smul_smul, smul_smul, mul_comm d a,
      sub_self]
  have hcoeff := congrArg (fun v => b.repr v i) hrel
  simp [map_sub, map_smul, Module.Basis.repr_self, hij] at hcoeff
  exact hd hcoeff

private lemma fkSign_pair_eq_refl_mul {ε : ZMod 3} (hε : ε ≠ 0)
    (b : Module.Basis (Fin 3) (ZMod 3) U) (hb : ∀ i, R (b i) = ε)
    (hbo : ∀ i j, i ≠ j → QuadraticMap.polar R (b i) (b j) = 0)
    {i j : Fin 3} (hij : i ≠ j) :
    (fkFrame (R := R) b hb hbo).signChange ({i, j} : Finset (Fin 3)) =
      fkRefl hε b hb i * fkRefl hε b hb j := by
  apply Subtype.ext
  apply (fkFrame (R := R) b hb hbo).b.ext'
  intro l
  rw [PFrame.signChange_basis]
  rw [Subgroup.coe_mul, LinearEquiv.mul_apply]
  dsimp [fkFrame]
  by_cases hli : l = i
  · subst hli
    rw [fkRefl_of_ne hε b hb hbo (Ne.symm hij), fkRefl_self hε b hb]
    simp
  · by_cases hlj : l = j
    · subst hlj
      rw [fkRefl_self hε b hb, map_neg, fkRefl_of_ne hε b hb hbo hij]
      simp [hli]
    · rw [fkRefl_of_ne hε b hb hbo (Ne.symm hlj),
        fkRefl_of_ne hε b hb hbo (Ne.symm hli)]
      simp [hli, hlj]

private lemma fkMultiplicative_sq_eq_one
    (a : Multiplicative (TauCeti.SquareClassGroup (ZMod 3))) : a * a = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_one]
  have h : (2 : ℕ) • Multiplicative.toAdd a = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2) 2 (Multiplicative.toAdd a),
      CharP.cast_eq_zero (ZMod 2) 2, zero_smul]
  simpa [two_nsmul] using h

private lemma fkSquareClass_mul_self (u : (ZMod 3)ˣ) :
    TauCeti.squareClassHom u * TauCeti.squareClassHom u = 1 :=
  fkMultiplicative_sq_eq_one _

private lemma fkSign_pair_mem_omega {ε : ZMod 3} (hR : R.Nondegenerate) (hε : ε ≠ 0)
    (b : Module.Basis (Fin 3) (ZMod 3) U) (hb : ∀ i, R (b i) = ε)
    (hbo : ∀ i j, i ≠ j → QuadraticMap.polar R (b i) (b j) = 0)
    {i j : Fin 3} (hij : i ≠ j) :
    (fkFrame (R := R) b hb hbo).signChange ({i, j} : Finset (Fin 3)) ∈ omegaGroup hR := by
  rw [fkSign_pair_eq_refl_mul hε b hb hbo hij, mem_omegaGroup_iff hR, map_mul,
    fkRefl_detSpinor hR hε b hb, fkRefl_detSpinor hR hε b hb, Prod.mk_mul_mk]
  refine Prod.ext ?_ ?_
  · exact (by decide : ((-1 : (ZMod 3)ˣ) * -1) = 1)
  · exact fkSquareClass_mul_self (Units.mk0 ε hε)

private lemma fkE_le_omega {ε : ZMod 3} (hR : R.Nondegenerate) (hε : ε ≠ 0)
    (b : Module.Basis (Fin 3) (ZMod 3) U) (hb : ∀ i, R (b i) = ε)
    (hbo : ∀ i j, i ≠ j → QuadraticMap.polar R (b i) (b j) = 0) :
    fkE (R := R) (fkFrame (R := R) b hb hbo) ≤ omegaGroup hR := by
  intro g hg
  obtain ⟨J, hJ, rfl⟩ := hg
  have hcases : J = ∅ ∨ J = {0, 1} ∨ J = {0, 2} ∨ J = {1, 2} := by revert J; decide
  rcases hcases with rfl | rfl | rfl | rfl
  · rw [PFrame.signChange_empty]
    exact (omegaGroup hR).one_mem
  · exact fkSign_pair_mem_omega hR hε b hb hbo (by decide)
  · exact fkSign_pair_mem_omega hR hε b hb hbo (by decide)
  · exact fkSign_pair_mem_omega hR hε b hb hbo (by decide)

private lemma fkE_nontrivial {ε : ZMod 3} (b : Module.Basis (Fin 3) (ZMod 3) U)
    (hb : ∀ i, R (b i) = ε)
    (hbo : ∀ i j, i ≠ j → QuadraticMap.polar R (b i) (b j) = 0) :
    ∃ e ∈ fkE (R := R) (fkFrame (R := R) b hb hbo), e ≠ 1 := by
  let fr := fkFrame (R := R) b hb hbo
  refine ⟨fr.signChange {0, 1}, ⟨{0, 1}, by decide, rfl⟩, ?_⟩
  intro h
  have h1 := PFrame.signChange_basis fr {0, 1} 0
  rw [h] at h1
  have h1' : b (0 : Fin 3) = -b (0 : Fin 3) := by
    simpa [fr, fkFrame, Finset.mem_insert, Finset.mem_singleton] using h1
  have h2 : (2 : ZMod 3) • b (0 : Fin 3) = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp h1'
  rcases smul_eq_zero.mp h2 with h2 | h2
  · exact (by decide : (2 : ZMod 3) ≠ 0) h2
  · exact (b.ne_zero 0) h2

theorem fkFrame_exists_of_basis (hR : R.Nondegenerate)
    (b : Module.Basis (Fin 3) (ZMod 3) U) {ε : ZMod 3} (hε : ε ≠ 0) (hb : ∀ i, R (b i) = ε)
    (hbo : ∀ i j, i ≠ j → QuadraticMap.polar R (b i) (b j) = 0) {c : OGroup R}
    (hc : Odd (orderOf c)) (hc1 : c ≠ 1) :
    ∃ E : Subgroup (OGroup R), E ≤ omegaGroup hR ∧ (∀ e ∈ E, e * e = 1) ∧ (∃ e ∈ E, e ≠ 1) ∧
      (∀ e ∈ E, c * e * c⁻¹ ∈ E) ∧ (∀ e ∈ E, e ≠ 1 → c * e * c⁻¹ ≠ e) := by
  let fr := fkFrame (R := R) b hb hbo
  let E := fkE (R := R) fr
  choose σ s hs hcσ using fun i => fk_isometry_basis (R := R) hε b hb hbo c i
  have hs0 : ∀ i, s i ≠ 0 := fun i => by rcases hs i with h | h <;> rw [h] <;> decide
  have hσinj : Function.Injective σ := by
    intro i j hij; by_contra hne
    exact fk_same_line_false b hne c (hs0 i) (hs0 j) (hcσ i) (by rw [hij]; exact hcσ j)
  let σe : Equiv.Perm (Fin 3) := Equiv.ofBijective σ hσinj.bijective_of_finite
  let J : Finset (Fin 3) := Finset.univ.filter (fun i => s i = -1)
  have hdecomp : c = fkPerm fr σe * fr.signChange J := by
    apply Subtype.ext; apply fr.b.ext'; intro i
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, fr.signChange_basis]
    rw [show (c : U ≃ₗ[ZMod 3] U) (fr.b i) = s i • fr.b (σ i) from by
      simpa [fr, fkFrame] using hcσ i]
    by_cases hi : i ∈ J
    · rw [if_pos hi, map_neg, fkPerm_basis]
      rw [show s i = -1 from by simpa [J] using hi]
      simp [σe]
    · rw [if_neg hi, fkPerm_basis]
      rcases hs i with h | h
      · rw [h]
        simp [σe]
      · exact absurd (by simpa [J] using h) hi
  refine ⟨E, fkE_le_omega hR hε b hb hbo, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨K, hK, rfl⟩ := he
    exact fr.signChange_mul_self K
  · simpa [E] using fkE_nontrivial b hb hbo
  · intro e he
    obtain ⟨K, hK, rfl⟩ := he
    refine ⟨K.map σe.toEmbedding, ?_, ?_⟩
    · simpa using hK
    · rw [hdecomp]
      exact fkConj_signChange fr σe J K
  · intro e he he1 hfix
    obtain ⟨K, hK, rfl⟩ := he
    have hKne : K ≠ ∅ := by intro h0; apply he1; rw [h0, PFrame.signChange_empty]
    have hK2 : K.card = 2 := by
      have hpos : 0 < K.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hKne)
      have hle : K.card ≤ 3 := by simpa using Finset.card_le_univ (s := K)
      rcases hK with ⟨m, hm⟩; omega
    have hconj : c * fr.signChange K * c⁻¹ = fr.signChange (K.map σe.toEmbedding) :=
      (hdecomp ▸ fkConj_signChange fr σe J K)
    have hmap : K.map σe.toEmbedding = K := by
      exact (PFrame.signChange_injective fr (hfix.symm.trans hconj)).symm
    have hσ2 : σe ^ 2 = 1 := fkPerm_sq_eq_one_of_maps_pair σe K hK2 hmap
    have hmiddle : fr.signChange J * fkPerm fr σe =
        fkPerm fr σe * fr.signChange (J.map σe.symm.toEmbedding) := by
      have h := fkPerm_mul_signChange fr σe (J.map σe.symm.toEmbedding)
      rw [Finset.map_map] at h
      simpa using h.symm
    have hc2 : c * c = fr.signChange (symmDiff (J.map σe.symm.toEmbedding) J) := by
      calc c * c = fkPerm fr σe * (fr.signChange J * fkPerm fr σe) * fr.signChange J := by
            rw [hdecomp]
            group
        _ = fkPerm fr σe *
              (fkPerm fr σe * fr.signChange (J.map σe.symm.toEmbedding)) *
              fr.signChange J := by rw [hmiddle]
        _ = (fkPerm fr σe * fkPerm fr σe) *
              fr.signChange (J.map σe.symm.toEmbedding) * fr.signChange J := by group
        _ = fr.signChange (symmDiff (J.map σe.symm.toEmbedding) J) := by
            have hσ2' : σe * σe = 1 := by simpa [pow_two] using hσ2
            rw [← fkPerm_mul, hσ2', fkPerm_one, one_mul, fr.signChange_mul]
    have hc4 : c ^ 4 = 1 := by
      have h : c ^ 4 = (c * c) * (c * c) := by
        rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two]
      rw [h]
      calc (c * c) * (c * c)
          = fr.signChange (symmDiff (J.map σe.symm.toEmbedding) J) *
              fr.signChange (symmDiff (J.map σe.symm.toEmbedding) J) := by rw [hc2]
        _ = 1 := fr.signChange_mul_self _
    have hdvd : orderOf c ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr hc4
    have hmem : orderOf c ∈ Nat.divisors 4 := by rw [Nat.mem_divisors]; exact ⟨hdvd, by norm_num⟩
    rw [show Nat.divisors 4 = {1, 2, 4} by decide] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    have h1 : orderOf c = 1 := by
      rcases hmem with h | h | h
      · exact h
      · exact absurd (h ▸ hc) (by decide)
      · exact absurd (h ▸ hc) (by decide)
    rw [orderOf_eq_one_iff] at h1
    exact hc1 h1

theorem fkFrame_exists (hR : R.Nondegenerate) (hdim : Module.finrank (ZMod 3) U = 3)
    {c : OGroup R} (hc : Odd (orderOf c)) (hc1 : c ≠ 1) :
    ∃ E : Subgroup (OGroup R), E ≤ omegaGroup hR ∧ (∀ e ∈ E, e * e = 1) ∧ (∃ e ∈ E, e ≠ 1) ∧
      (∀ e ∈ E, c * e * c⁻¹ ∈ E) ∧ (∀ e ∈ E, e ≠ 1 → c * e * c⁻¹ ≠ e) := by
  obtain ⟨b, ε, hε, hb, hbo⟩ := fkFrameBasis_exists hR hdim
  exact fkFrame_exists_of_basis hR b hε hb hbo hc hc1

end CFSG.OddStandard.SmallF3.Omega
