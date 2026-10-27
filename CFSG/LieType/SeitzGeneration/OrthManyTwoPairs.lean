module

public import CFSG.LieType.SeitzGeneration.OrthManyTwoTools
public import CFSG.LieType.SeitzGeneration.OrthManyPieces
public import CFSG.LieType.SeitzGeneration.OrthRelRoot
public import CFSG.LieType.SeitzGeneration.OrthManyGlue

public section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical
  CFSG.Open OrthNS OrthBlk
open CFSG.RankThree.Classical2 (orthDerived)

section Matching

open Polynomial

variable {K : Type} [Field K]

theorem manyTwo_not_isRoot_one {h : K[X]} (hm : h.Monic) (hi : Irreducible h)
    (hne : h ≠ X - 1) : ¬ h.IsRoot 1 := by
  intro hr
  have hdvd : (X - C 1 : K[X]) ∣ h := Polynomial.dvd_iff_isRoot.mpr hr
  have h1 : X - C 1 = h := eq_of_monic_of_associated (monic_X_sub_C 1) hm
    (irreducible_X_sub_C 1 |>.associated_of_dvd hi hdvd)
  exact hne (by rw [← h1, map_one])

theorem manyTwo_exists_primitiveRoot {p : ℕ} (hp : p.Prime) {h : K[X]} (hm : h.Monic)
    (hi : Irreducible h) (hd : h ∣ X ^ p - 1) (hne : h ≠ X - 1) :
    ∃ ρ : AlgebraicClosure K, aeval ρ h = 0 ∧ IsPrimitiveRoot ρ p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ρ, hρ⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K) h
    (degree_pos_of_irreducible hi).ne'
  have hρp : ρ ^ p = 1 := by
    obtain ⟨g, hg⟩ := hd
    have := congrArg (aeval ρ) hg
    simp only [map_sub, map_pow, aeval_X, map_one, map_mul, hρ, zero_mul] at this
    exact sub_eq_zero.mp this
  have hρ1 : ρ ≠ 1 := by
    rintro rfl
    refine manyTwo_not_isRoot_one hm hi hne ?_
    have h1 : algebraMap K (AlgebraicClosure K) (h.eval 1) = 0 := by
      rw [← Polynomial.eval₂_at_one, ← Polynomial.aeval_def]
      exact hρ
    exact (map_eq_zero _).mp h1
  refine ⟨ρ, hρ, ?_⟩
  have := IsPrimitiveRoot.orderOf ρ
  rwa [orderOf_eq_prime hρp hρ1] at this

theorem manyTwo_exists_dvd_comp_X_pow {p : ℕ} (hp : p.Prime) {h₁ h₂ : K[X]} (hm₁ : h₁.Monic)
    (hm₂ : h₂.Monic) (hi₁ : Irreducible h₁) (hi₂ : Irreducible h₂) (hd₁ : h₁ ∣ X ^ p - 1)
    (hd₂ : h₂ ∣ X ^ p - 1) (hn₁ : h₁ ≠ X - 1) (hn₂ : h₂ ≠ X - 1) :
    ∃ c : ℕ, ¬ p ∣ c ∧ h₂ ∣ h₁.comp (X ^ c) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ρ₁, hρ₁, hp₁⟩ := manyTwo_exists_primitiveRoot hp hm₁ hi₁ hd₁ hn₁
  obtain ⟨ρ₂, hρ₂, hp₂⟩ := manyTwo_exists_primitiveRoot hp hm₂ hi₂ hd₂ hn₂
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨c, -, hc⟩ := hp₂.eq_pow_of_pow_eq_one hp₁.pow_eq_one
  refine ⟨c, ?_, ?_⟩
  · intro hdvd
    have : ρ₁ = 1 := by
      rw [← hc]
      obtain ⟨k, rfl⟩ := hdvd
      rw [pow_mul, hp₂.pow_eq_one, one_pow]
    exact hp₁.ne_one hp.one_lt this
  · have hf : aeval ρ₂ (h₁.comp (X ^ c)) = 0 := by
      rw [aeval_comp, aeval_X_pow, hc, hρ₁]
    have := minpoly.dvd K ρ₂ hf
    rwa [← minpoly.eq_of_irreducible_of_monic hi₂ hρ₂ hm₂] at this

theorem manyTwo_tau_ne_zero {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {τ : K}
    (hm : (X ^ 2 - C τ * X + 1 : K[X]).Monic) (hi : Irreducible (X ^ 2 - C τ * X + 1 : K[X]))
    (hd : (X ^ 2 - C τ * X + 1 : K[X]) ∣ X ^ p - 1) (hne : (X ^ 2 - C τ * X + 1 : K[X]) ≠ X - 1) :
    τ ≠ 0 := by
  rintro rfl
  obtain ⟨ρ, hρ, hprim⟩ := manyTwo_exists_primitiveRoot hp hm hi hd hne
  simp only [map_sub, map_add, map_pow, map_mul, aeval_X, aeval_C, map_one, map_zero, zero_mul,
    sub_zero] at hρ
  have h4 : ρ ^ 4 = 1 := by
    have : ρ ^ 2 = -1 := eq_neg_of_add_eq_zero_left hρ
    calc ρ ^ 4 = (ρ ^ 2) ^ 2 := by ring
      _ = 1 := by rw [this]; norm_num
  have hdvd : p ∣ 2 ^ 2 := by simpa using hprim.dvd_of_pow_eq_one 4 h4
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))

theorem manyTwo_not_isRoot_of_natDegree_two {h : K[X]} (hi : Irreducible h)
    (hd : h.natDegree = 2) (a : K) : ¬ h.IsRoot a := fun hroot => by
  have := degree_eq_one_of_irreducible_of_root hi hroot
  rw [degree_eq_natDegree hi.ne_zero, hd] at this
  exact absurd (by exact_mod_cast this : (2 : ℕ) = 1) (by norm_num)

theorem manyTwo_exists_eq_X_sq_sub {h : K[X]} (hm : h.Monic) (hi : Irreducible h)
    (hd : h.natDegree = 2) (hself : h = reciprocalPolynomial h) :
    ∃ τ : K, h = X ^ 2 - C τ * X + 1 := by
  have hnoroot : ∀ a : K, ¬ h.IsRoot a := manyTwo_not_isRoot_of_natDegree_two hi hd
  have hc0 : h.coeff 0 ≠ 0 := fun h0 =>
    hnoroot 0 (by rw [Polynomial.IsRoot, ← coeff_zero_eq_eval_zero]; exact h0)
  have e0 : h.coeff 0 = (h.coeff 0)⁻¹ := by
    have := congrArg (fun f => f.coeff 0) hself
    simpa only [coeff_zero_reciprocalPolynomial hm] using this
  have e1 : h.coeff 1 = (h.coeff 0)⁻¹ * h.coeff 1 := by
    have := congrArg (fun f => f.coeff 1) hself
    rw [reciprocalPolynomial, coeff_C_mul, coeff_reverse, hd,
      revAt_le (by norm_num : 1 ≤ 2)] at this
    exact this
  have hsq : h.coeff 0 * h.coeff 0 = 1 := by
    rw [mul_comm]; nth_rewrite 1 [e0]; exact inv_mul_cancel₀ hc0
  have hhform : h = X ^ 2 + C (h.coeff 1) * X + C (h.coeff 0) := by
    ext n
    rcases n with _ | _ | _ | n
    · simp [coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]
    · simp [coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]
    · have := hm.coeff_natDegree
      rw [hd] at this
      simp [coeff_X_pow, coeff_C_mul, coeff_X, coeff_C, this]
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      simp [coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]
  have hc1 : h.coeff 0 = 1 := by
    by_contra hne
    have hm1 : h.coeff 0 = -1 := by
      have : (h.coeff 0 - 1) * (h.coeff 0 + 1) = 0 := by linear_combination hsq
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd (sub_eq_zero.mp h') hne
      · exact eq_neg_of_add_eq_zero_left h'
    have h2 : (2 : K) ≠ 0 := by
      intro h2
      apply hne
      rw [hm1]
      linear_combination -h2
    have hb : h.coeff 1 = 0 := by
      rw [hm1, inv_neg, inv_one] at e1
      have : (2 : K) * h.coeff 1 = 0 := by linear_combination e1
      exact (mul_eq_zero.mp this).resolve_left h2
    refine hnoroot 1 ?_
    rw [Polynomial.IsRoot, hhform]
    simp [hb, hm1]
  refine ⟨-(h.coeff 1), ?_⟩
  calc h = X ^ 2 + C (h.coeff 1) * X + C (h.coeff 0) := hhform
    _ = X ^ 2 - C (-(h.coeff 1)) * X + 1 := by rw [hc1]; simp

theorem manyTwo_apply_sq_of_aeval {A : Type*} [AddCommGroup A] [Module K A] (T : Module.End K A)
    (τ : K) (v : A) (h : aeval T (X ^ 2 - C τ * X + 1 : K[X]) v = 0) :
    T (T v) = τ • T v - v := by
  simp only [map_add, map_sub, map_pow, map_mul, aeval_X, aeval_C, map_one,
    LinearMap.add_apply, LinearMap.sub_apply, Module.End.pow_apply, Module.End.mul_apply,
    Module.algebraMap_end_apply, Module.End.one_apply] at h
  have h2 : (⇑T)^[2] v = T (T v) := rfl
  rw [h2] at h
  linear_combination (norm := module) h

end Matching

section SqRel

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem manyTwo_sqRel_sup {g : V ≃ₗ[K] V} {τ : K} {S T : Submodule K V}
    (hS : ∀ u ∈ S, g (g u) = τ • g u - u) (hT : ∀ u ∈ T, g (g u) = τ • g u - u) :
    ∀ u ∈ S ⊔ T, g (g u) = τ • g u - u := by
  intro u hu
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hu
  simp only [map_add]
  rw [hS s hs, hT t ht]
  module

theorem manyTwo_sqRel_congr {g h : V ≃ₗ[K] V} {τ : K} {S : Submodule K V} (hstab : ∀ u ∈ S, h u ∈ S)
    (hgh : ∀ u ∈ S, g u = h u) (hS : ∀ u ∈ S, h (h u) = τ • h u - u) :
    ∀ u ∈ S, g (g u) = τ • g u - u := by
  intro u hu
  rw [hgh u hu, hgh _ (hstab u hu), hS u hu]

theorem manyTwo_sqRel_symm {g : V ≃ₗ[K] V} {τ : K} {S : Submodule K V}
    (hstab : ∀ u ∈ S, g.symm u ∈ S) (hS : ∀ u ∈ S, g (g u) = τ • g u - u) :
    ∀ u ∈ S, g.symm (g.symm u) = τ • g.symm u - u := by
  intro u hu
  have h1 := hS (g.symm (g.symm u)) (hstab _ (hstab u hu))
  simp only [LinearEquiv.apply_symm_apply] at h1
  linear_combination (norm := module) h1

end SqRel

section Quadratic

open Polynomial

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (orthDerived Q)} {P : Submodule K V}

theorem manyTwo_ne_two_and_ne_ringChar (hp : p.Prime)
    (h2 : orderOf ((Nat.card K : ℕ) : ZMod p) = 2) : p ≠ 2 ∧ p ≠ ringChar K := by
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  have hsq : ((Nat.card K : ℕ) : ZMod p) ^ 2 = 1 := by
    rw [← h2]; exact pow_orderOf_eq_one _
  have hne1 : ((Nat.card K : ℕ) : ZMod p) ≠ 1 := by
    intro h; rw [h, orderOf_one] at h2; omega
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact hne1 (by
      generalize ((Nat.card K : ℕ) : ZMod 2) = x at hsq
      revert x; decide)
  · intro hpl
    have : ((Nat.card K : ℕ) : ZMod p) = 0 := by
      classical
      haveI : Fintype K := Fintype.ofFinite K
      haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
      obtain ⟨n, -, hcard⟩ := FiniteField.card K (ringChar K)
      rw [ZMod.natCast_eq_zero_iff, Nat.card_eq_fintype_card, hcard, ← hpl]
      exact dvd_pow_self p (PNat.pos n).ne'
    rw [this] at hsq
    simp at hsq

theorem IsPiece.exists_quadratic (hK : KernelLineData Q p E) (hp : p.Prime)
    (hpl : p ≠ ringChar K) (hP : IsPiece Q E P) {M : Subgroup E} (hM : Nat.card M = p)
    (hPM : P ≤ lineSpace M) (h2 : orderOf ((Nat.card K : ℕ) : ZMod p) = 2) {a : E} (haM : a ∉ M) :
    ∃ q : K[X], q.Monic ∧ Irreducible q ∧ q ≠ X - 1 ∧ q ∣ X ^ p - 1 ∧
      (∃ τ : K, q = X ^ 2 - C τ * X + 1 ∧ ∀ r : K, r ^ 2 - τ * r + 1 ≠ 0) ∧
      ∀ v ∈ P, aeval (((a : E) : orthDerived Q) : V ≃ₗ[K] V).toLinearMap q v = 0 := by
  classical
  have hker := hP.actKernel_eq hK hp hM hPM
  obtain ⟨q, hmon, hirr, hne1, hself, hhf, hkill, -, hdeg⟩ :=
    hP.exists_primary hK hp hpl hM hker haM
  have hd2 : q.natDegree = 2 := hdeg.trans h2
  obtain ⟨τ, hτ⟩ := manyTwo_exists_eq_X_sq_sub hmon hirr hd2 hself
  refine ⟨q, hmon, hirr, hne1, ?_, ⟨τ, hτ, fun r hr => ?_⟩, hkill⟩
  swap
  · refine manyTwo_not_isRoot_of_natDegree_two hirr hd2 r ?_
    rw [hτ]
    simpa [Polynomial.IsRoot] using hr
  have hmq := (mem_primaryFactors.mp hhf).2.2
  set T : Module.End K V := (((a : E) : orthDerived Q) : V ≃ₗ[K] V).toLinearMap with hT
  have hTp : T ^ p = 1 := by
    rw [hT, ← toLinearMap_pow, coe_pow_eq_one hK a]
    rfl
  have hTa : aeval T (X ^ p - 1 : K[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, map_one, hTp, sub_self]
  exact hmq.trans (minpoly.dvd K T hTa)

theorem exists_two_mixing_elements_aux (hK : KernelLineData Q p E) (hp : p.Prime)
    {M₁ M₂ : Subgroup E} (hM₁ : Nat.card M₁ = p) (hM₂ : Nat.card M₂ = p) (hM : M₁ ≠ M₂)
    {P₁ P₂ : Submodule K V} (hP₁ : IsPiece Q E P₁) (hP₂ : IsPiece Q E P₂)
    (h₁ : P₁ ≤ lineSpace M₁) (h₂ : P₂ ≤ lineSpace M₂)
    (h2 : orderOf ((Nat.card K : ℕ) : ZMod p) = 2) :
    ∃ x y : E, ∃ τ : K, τ ≠ 0 ∧ (∀ r : K, r ^ 2 - τ * r + 1 ≠ 0) ∧
      Subgroup.closure {x, y} = ⊤ ∧
      (∀ u ∈ P₁ ⊔ P₂, ((x : orthDerived Q) : V ≃ₗ[K] V) (((x : orthDerived Q) : V ≃ₗ[K] V) u) =
        τ • ((x : orthDerived Q) : V ≃ₗ[K] V) u - u) ∧
      (∀ u ∈ P₁ ⊔ P₂, ((y : orthDerived Q) : V ≃ₗ[K] V) (((y : orthDerived Q) : V ≃ₗ[K] V) u) =
        τ • ((y : orthDerived Q) : V ≃ₗ[K] V) u - u) := by
  classical
  obtain ⟨hp2, hpl⟩ := manyTwo_ne_two_and_ne_ringChar hp h2
  haveI : Fact p.Prime := ⟨hp⟩
  have hfinE : Finite E :=
    Nat.finite_of_card_ne_zero (by rw [hK.card]; exact pow_ne_zero 2 hp.ne_zero)
  haveI : Nontrivial M₁ := Finite.one_lt_card_iff_nontrivial.mp (by rw [hM₁]; exact hp.one_lt)
  haveI : Nontrivial M₂ := Finite.one_lt_card_iff_nontrivial.mp (by rw [hM₂]; exact hp.one_lt)
  obtain ⟨m₁, hm₁⟩ := exists_ne (1 : M₁)
  obtain ⟨m₂, hm₂⟩ := exists_ne (1 : M₂)
  have hbot := inf_eq_bot_of_card_prime' hp hM₁ hM₂ hM
  set a₁ : E := (m₁ : E) with ha₁
  set a₂ : E := (m₂ : E) with ha₂
  have ha₁1 : a₁ ≠ 1 := fun h => hm₁ (Subtype.ext h)
  have ha₂1 : a₂ ≠ 1 := fun h => hm₂ (Subtype.ext h)
  have ha₁M₁ : a₁ ∈ M₁ := m₁.2
  have ha₂M₂ : a₂ ∈ M₂ := m₂.2
  have ha₁M₂ : a₁ ∉ M₂ := fun h => ha₁1 (by
    have : a₁ ∈ M₁ ⊓ M₂ := ⟨ha₁M₁, h⟩
    rwa [hbot, Subgroup.mem_bot] at this)
  have ha₂M₁ : a₂ ∉ M₁ := fun h => ha₂1 (by
    have : a₂ ∈ M₁ ⊓ M₂ := ⟨h, ha₂M₂⟩
    rwa [hbot, Subgroup.mem_bot] at this)
  obtain ⟨q₁, hmo₁, hi₁, hn₁, hd₁, ⟨τ, hq₁, hnoroot⟩, hk₁⟩ :=
    hP₁.exists_quadratic hK hp hpl hM₁ h₁ h2 ha₂M₁
  obtain ⟨q₂, hmo₂, hi₂, hn₂, hd₂, -, hk₂⟩ := hP₂.exists_quadratic hK hp hpl hM₂ h₂ h2 ha₁M₂
  obtain ⟨c, hcp, hcq⟩ := manyTwo_exists_dvd_comp_X_pow hp hmo₁ hmo₂ hi₁ hi₂ hd₁ hd₂ hn₁ hn₂
  have hτ : τ ≠ 0 := by
    subst hq₁
    exact manyTwo_tau_ne_zero hp hp2 hmo₁ hi₁ hd₁ hn₁
  set g₁ : V ≃ₗ[K] V := ((a₁ : orthDerived Q) : V ≃ₗ[K] V) with hg₁
  set g₂ : V ≃ₗ[K] V := ((a₂ : orthDerived Q) : V ≃ₗ[K] V) with hg₂
  have hfix₁ : ∀ n : ℕ, ∀ u ∈ P₁, (g₁ ^ n) u = u := by
    intro n u hu
    have h1 : g₁ u = u :=
      apply_eq_of_mem_lineFixSpace (E := E) m₁ (lineSpace_le_lineFixSpace _ (h₁ hu))
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, LinearEquiv.mul_apply, h1, ih]
  have hfix₂ : ∀ u ∈ P₂, g₂ u = u := fun u hu =>
    apply_eq_of_mem_lineFixSpace (E := E) m₂ (lineSpace_le_lineFixSpace _ (h₂ hu))
  have hst₁ : ∀ u ∈ P₁, g₂ u ∈ P₁ := fun u hu => hP₁.eStable a₂ a₂.2 u hu
  have hst₁' : ∀ u ∈ P₁, g₂.symm u ∈ P₁ := fun u hu =>
    hP₁.eStable.symm_apply_mem hK hp.pos a₂.2 hu
  have hst₂ : ∀ u ∈ P₂, g₁ u ∈ P₂ := fun u hu => hP₂.eStable a₁ a₁.2 u hu
  have hst₂c : ∀ u ∈ P₂, (g₁ ^ c) u ∈ P₂ := OrthBlk.pow_apply_mem hst₂ c
  have hrel₂ : ∀ u ∈ P₁, g₂ (g₂ u) = τ • g₂ u - u := fun u hu => by
    have := hk₁ u hu
    rw [hq₁] at this
    exact manyTwo_apply_sq_of_aeval g₂.toLinearMap τ u this
  have hrel₁ : ∀ u ∈ P₂, (g₁ ^ c) ((g₁ ^ c) u) = τ • (g₁ ^ c) u - u := by
    intro u hu
    obtain ⟨g, hg⟩ := hcq
    have h0 : aeval g₁.toLinearMap (q₁.comp (X ^ c)) u = 0 := by
      rw [hg, mul_comm, map_mul, Module.End.mul_apply, hk₂ u hu, map_zero]
    rw [aeval_comp, aeval_X_pow, ← toLinearMap_pow, hq₁] at h0
    exact manyTwo_apply_sq_of_aeval (g₁ ^ c).toLinearMap τ u h0
  have hxa : ∀ u, (((a₁ ^ c * a₂ : E) : orthDerived Q) : V ≃ₗ[K] V) u = (g₁ ^ c) (g₂ u) :=
    fun u => rfl
  have hya : ∀ u, (((a₁ ^ c * a₂⁻¹ : E) : orthDerived Q) : V ≃ₗ[K] V) u =
      (g₁ ^ c) (g₂.symm u) := fun u => rfl
  have hx₁ : ∀ u ∈ P₁, (((a₁ ^ c * a₂ : E) : orthDerived Q) : V ≃ₗ[K] V) u = g₂ u :=
    fun u hu => by rw [hxa]; exact hfix₁ c _ (hst₁ u hu)
  have hx₂ : ∀ u ∈ P₂, (((a₁ ^ c * a₂ : E) : orthDerived Q) : V ≃ₗ[K] V) u = (g₁ ^ c) u :=
    fun u hu => by rw [hxa, hfix₂ u hu]
  have hy₁ : ∀ u ∈ P₁, (((a₁ ^ c * a₂⁻¹ : E) : orthDerived Q) : V ≃ₗ[K] V) u = g₂.symm u :=
    fun u hu => by rw [hya]; exact hfix₁ c _ (hst₁' u hu)
  have hy₂ : ∀ u ∈ P₂, (((a₁ ^ c * a₂⁻¹ : E) : orthDerived Q) : V ≃ₗ[K] V) u = (g₁ ^ c) u :=
    fun u hu => by rw [hya, (LinearEquiv.symm_apply_eq g₂).mpr (hfix₂ u hu).symm]
  have hx := manyTwo_sqRel_sup (manyTwo_sqRel_congr hst₁ hx₁ hrel₂)
    (manyTwo_sqRel_congr hst₂c hx₂ hrel₁)
  have hy := manyTwo_sqRel_sup (manyTwo_sqRel_congr hst₁' hy₁ (manyTwo_sqRel_symm hst₁' hrel₂))
    (manyTwo_sqRel_congr hst₂c hy₂ hrel₁)
  have hordp : orderOf a₁ = p := orderOf_eq_prime (hK.exp a₁) ha₁1
  have hc1 : a₁ ^ c ∉ M₂ := by
    intro h
    have h' : a₁ ^ c ∈ M₁ ⊓ M₂ := ⟨M₁.pow_mem ha₁M₁ c, h⟩
    rw [hbot, Subgroup.mem_bot] at h'
    exact hcp (hordp ▸ orderOf_dvd_of_pow_eq_one h')
  have hclosure : Subgroup.closure ({a₁ ^ c * a₂, a₁ ^ c * a₂⁻¹} : Set E) = ⊤ := by
    set N := Subgroup.closure ({a₁ ^ c * a₂, a₁ ^ c * a₂⁻¹} : Set E) with hN
    have hxN : a₁ ^ c * a₂ ∈ N := Subgroup.subset_closure (by simp)
    have hyN : a₁ ^ c * a₂⁻¹ ∈ N := Subgroup.subset_closure (by simp)
    have hsq : a₂ ^ 2 ∈ N := by
      have hcomm : ∀ u v : E, u * v = v * u := hK.comm
      have key : ∀ A B : E, (A * B) * (A * B⁻¹)⁻¹ = B ^ 2 := by
        intro A B
        calc (A * B) * (A * B⁻¹)⁻¹ = (A * (B * B)) * A⁻¹ := by group
          _ = ((B * B) * A) * A⁻¹ := by rw [hcomm A (B * B)]
          _ = B ^ 2 := by rw [mul_inv_cancel_right, pow_two]
      have : (a₁ ^ c * a₂) * (a₁ ^ c * a₂⁻¹)⁻¹ = a₂ ^ 2 := key _ _
      rw [← this]
      exact N.mul_mem hxN (N.inv_mem hyN)
    have ha₂N : a₂ ∈ N := by
      obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
      have : a₂ = (a₂ ^ 2) ^ (k + 1) := by
        rw [← pow_mul]
        have h3 : 2 * (k + 1) = p + 1 := by omega
        rw [h3, pow_succ, hK.exp a₂, one_mul]
      rw [this]
      exact N.pow_mem hsq _
    have hM₂N : M₂ ≤ N := by
      have hzp : Subgroup.zpowers a₂ = M₂ := by
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ha₂M₂) ?_
        rw [Nat.card_zpowers, orderOf_eq_prime (hK.exp a₂) ha₂1, hM₂]
      rw [← hzp]
      exact Subgroup.zpowers_le.mpr ha₂N
    have hNne : N ≠ M₂ := by
      intro h
      have hxM : a₁ ^ c * a₂ ∈ M₂ := h ▸ hxN
      exact hc1 (by simpa using M₂.mul_mem hxM (M₂.inv_mem ha₂M₂))
    exact eq_top_of_line_lt hK hp hM₂ hM₂N hNne
  exact ⟨a₁ ^ c * a₂, a₁ ^ c * a₂⁻¹, τ, hτ, hnoroot, hclosure, hx, hy⟩

end Quadratic

section Det

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem manyTwo_det_restrict_pair {g : V ≃ₗ[K] V} {e : V} {τ : K}
    (hli : LinearIndependent K ![e, g e]) (hrel : g (g e) = τ • g e - e)
    (hTg : ∀ t ∈ Submodule.span K (Set.range ![e, g e]),
      g t ∈ Submodule.span K (Set.range ![e, g e])) :
    LinearMap.det ((g : V →ₗ[K] V).restrict hTg) = 1 := by
  classical
  set b := Basis.span hli with hb
  rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two]
  have h0 : ((g : V →ₗ[K] V).restrict hTg) (b 0) = b 1 := by
    apply Subtype.ext
    simp [hb, Basis.span_apply]
  have h1 : ((g : V →ₗ[K] V).restrict hTg) (b 1) = τ • b 1 - b 0 := by
    apply Subtype.ext
    simp [hb, Basis.span_apply, hrel]
  simp [LinearMap.toMatrix_apply, h0, h1]

theorem manyTwo_linearIndependent_pair {g : V ≃ₗ[K] V} {e : V} (he : e ≠ 0) {τ : K}
    (hrel : g (g e) = τ • g e - e) (hnoroot : ∀ r : K, r ^ 2 - τ * r + 1 ≠ 0) :
    LinearIndependent K ![e, g e] := by
  rw [LinearIndependent.pair_iff]
  intro α β hαβ
  by_cases hβ : β = 0
  · subst hβ
    rw [zero_smul, add_zero] at hαβ
    exact ⟨(smul_eq_zero.mp hαβ).resolve_right he, rfl⟩
  · exfalso
    have hge : g e = (-(α / β)) • e := by
      have : β • g e = -(α • e) := eq_neg_of_add_eq_zero_right hαβ
      calc g e = β⁻¹ • (β • g e) := by rw [smul_smul, inv_mul_cancel₀ hβ, one_smul]
        _ = (-(α / β)) • e := by rw [this, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
    set r : K := -(α / β) with hr
    have h1 : g (g e) = r ^ 2 • e := by rw [hge, map_smul, hge, smul_smul, pow_two]
    rw [h1, hge, smul_smul] at hrel
    have h2 : (r ^ 2 - τ * r + 1) • e = 0 := by
      linear_combination (norm := module) hrel
    exact hnoroot r ((smul_eq_zero.mp h2).resolve_right he)

end Det

section Plane

open Polynomial

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (orthDerived Q)}

theorem manyTwo_plane_facts {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {e : V} (heQ : Q e = 0) {τ : K} (hτ : τ ≠ 0) (hrel : g (g e) = τ • g e - e) :
    (∀ t ∈ Submodule.span K (Set.range ![e, g e]), Q t = 0) ∧
    (∀ t ∈ Submodule.span K (Set.range ![e, g e]),
      ∀ t' ∈ Submodule.span K (Set.range ![e, g e]), polar Q t t' = 0) := by
  have h1 : polar Q e (g e) = 0 := polar_self_apply_eq_zero hg hτ hrel heQ
  have hgQ : Q (g e) = 0 := by rw [map_of_mem hg, heQ]
  have hee : polar Q e e = 0 := polar_self_eq_zero heQ
  have hgg : polar Q (g e) (g e) = 0 := polar_self_eq_zero hgQ
  have h1' : polar Q (g e) e = 0 := by rw [polar_comm]; exact h1
  refine ⟨fun t ht => ?_, fun t ht t' ht' => ?_⟩
  · obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp ht
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, polar_smul_left_eq,
      polar_smul_right_eq, heQ, hgQ, h1]
    ring
  · obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp ht
    obtain ⟨c', rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp ht'
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq, h1, h1',
      hee, hgg]
    ring

theorem manyTwo_eichler_mem_of_plane (hEΩ : elementaryGroup Q ≤ orthDerived Q) {z : E} (hz1 : z ≠ 1)
    {e : V} (heQ : Q e = 0) {τ : K} (hτ : τ ≠ 0)
    (hrel : ((z : orthDerived Q) : V ≃ₗ[K] V) (((z : orthDerived Q) : V ≃ₗ[K] V) e) =
      τ • ((z : orthDerived Q) : V ≃ₗ[K] V) e - e)
    (hli : LinearIndependent K ![e, ((z : orthDerived Q) : V ≃ₗ[K] V) e]) :
    ∀ w ∈ Submodule.span K (Set.range ![e, ((z : orthDerived Q) : V ≃ₗ[K] V) e]),
      eichler Q e w ∈ orthCentralizerSpan Q E := by
  classical
  set g : V ≃ₗ[K] V := ((z : orthDerived Q) : V ≃ₗ[K] V) with hg
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := orthDerived_mem_orthogonalGroup
  obtain ⟨hTQ, hTp⟩ := manyTwo_plane_facts hgO heQ hτ hrel
  set T := Submodule.span K (Set.range ![e, g e]) with hT
  have he : e ∈ T := Submodule.subset_span ⟨0, rfl⟩
  have hge : g e ∈ T := Submodule.subset_span ⟨1, rfl⟩
  have hT2 : finrank K T = 2 := by rw [hT, finrank_span_eq_card hli]; simp
  have hTg : ∀ t ∈ T, g t ∈ T := by
    intro t ht
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp ht
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_smul]
    rw [hrel]
    exact T.add_mem (T.smul_mem _ hge) (T.smul_mem _ (T.sub_mem (T.smul_mem _ hge) he))
  have hdet := manyTwo_det_restrict_pair hli hrel hTg
  intro w hw
  have hc := commute_eichler_of_det_one hgO hT2 hTQ hTp hTg hdet he hw
  exact mem_orthCentralizerSpan_of_commute (a := (z : orthDerived Q))
    (hEΩ (eichler_mem_elementaryGroup Q e w)) z.2 (fun h => hz1 (Subtype.ext h)) hc.eq

omit [Finite K] [FiniteDimensional K V] in
theorem manyTwo_eStable_of_closure (hK : KernelLineData Q p E) (hp : 0 < p) {x y : E}
    (hcl : Subgroup.closure ({x, y} : Set E) = ⊤) {T : Submodule K V}
    (hx : ∀ t ∈ T, ((x : orthDerived Q) : V ≃ₗ[K] V) t ∈ T)
    (hy : ∀ t ∈ T, ((y : orthDerived Q) : V ≃ₗ[K] V) t ∈ T) : EStable E T := by
  let S : Subgroup E :=
    { carrier := {b | ∀ s ∈ T, ((b : orthDerived Q) : V ≃ₗ[K] V) s ∈ T}
      mul_mem' := fun {b c} hb hc s hs => hb _ (hc s hs)
      one_mem' := fun s hs => hs
      inv_mem' := fun {b} hb s hs =>
        stable_symm_of_pow (coe_pow_eq_one hK b) hp hb s hs }
  have hle : Subgroup.closure ({x, y} : Set E) ≤ S := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    exacts [hx, hy]
  intro g hg
  have : (⟨g, hg⟩ : E) ∈ S := by
    apply hle
    rw [hcl]
    exact Subgroup.mem_top _
  exact this

end Plane

section Pair

open Polynomial

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (orthDerived Q)}

theorem eichler_mem_of_pair_pieces (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hK : KernelLineData Q p E) (hEΩ : elementaryGroup Q ≤ orthDerived Q)
    (hNS : OrthNoInvariantSingular Q E) {M₁ M₂ : Subgroup E} (hM₁ : Nat.card M₁ = p)
    (hM₂ : Nat.card M₂ = p) (hM : M₁ ≠ M₂) {P₁ P₂ : Submodule K V} (hP₁ : IsPiece Q E P₁)
    (hP₂ : IsPiece Q E P₂) (h₁ : P₁ ≤ lineSpace M₁) (h₂ : P₂ ≤ lineSpace M₂)
    (hperp : OrthSep Q P₁ P₂) (h2 : orderOf ((Nat.card K : ℕ) : ZMod p) = 2) :
    ∀ e ∈ P₁ ⊔ P₂, ∀ w ∈ P₁ ⊔ P₂, eichler Q e w ∈ orthCentralizerSpan Q E := by
  classical
  obtain ⟨hp2, hpl⟩ := manyTwo_ne_two_and_ne_ringChar hp h2
  obtain ⟨x, y, τ, hτ, hnoroot, hcl, hx, hy⟩ :=
    exists_two_mixing_elements_aux hK hp hM₁ hM₂ hM hP₁ hP₂ h₁ h₂ h2
  set X : Submodule K V := P₁ ⊔ P₂ with hX
  have hXreg : PolarNondegOn Q X := polarNondegOn_sup hP₁.regular hP₂.regular hperp
  have hd₁ : finrank K P₁ = 2 := by
    obtain ⟨-, -, -, -, h, -⟩ := hP₁.exists_line hK hp hp2 hpl
    exact h.trans h2
  have hd₂ : finrank K P₂ = 2 := by
    obtain ⟨-, -, -, -, h, -⟩ := hP₂.exists_line hK hp hp2 hpl
    exact h.trans h2
  have hX4 : finrank K X = 4 := by
    have hdisj := OrthSep.disjoint hP₁.regular hperp
    have := Submodule.finrank_sup_add_finrank_inf_eq P₁ P₂
    rw [hdisj.eq_bot, finrank_bot, add_zero, ← hX] at this
    omega
  have hXst : ∀ z : E, ∀ u ∈ X, ((z : orthDerived Q) : V ≃ₗ[K] V) u ∈ X := by
    intro z u hu
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hu
    rw [map_add]
    exact Submodule.add_mem_sup (hP₁.eStable z z.2 u₁ hu₁) (hP₂.eStable z z.2 u₂ hu₂)
  have hroot : ∀ e ∈ X, e ≠ 0 → Q e = 0 → ∀ w ∈ X, polar Q e w = 0 →
      eichler Q e w ∈ orthCentralizerSpan Q E := by
    intro e heX he0 heQ w hwX hew
    have hrx := hx e heX
    have hry := hy e heX
    have hx1 : x ≠ 1 := by
      rintro rfl
      have h1 : e = τ • e - e := hrx
      have h3 : (τ - 2) • e = 0 := by linear_combination (norm := module) -h1
      have h4 : τ = 2 := sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right he0)
      exact hnoroot 1 (by rw [h4]; norm_num)
    have hy1 : y ≠ 1 := by
      rintro rfl
      have h1 : e = τ • e - e := hry
      have h3 : (τ - 2) • e = 0 := by linear_combination (norm := module) -h1
      have h4 : τ = 2 := sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right he0)
      exact hnoroot 1 (by rw [h4]; norm_num)
    have hlix := manyTwo_linearIndependent_pair he0 hrx hnoroot
    have hliy := manyTwo_linearIndependent_pair he0 hry hnoroot
    obtain ⟨hTxQ, hTxp⟩ := manyTwo_plane_facts
      (orthDerived_mem_orthogonalGroup (g := (x : orthDerived Q))) heQ hτ hrx
    obtain ⟨hTyQ, hTyp⟩ := manyTwo_plane_facts
      (orthDerived_mem_orthogonalGroup (g := (y : orthDerived Q))) heQ hτ hry
    set Tx := Submodule.span K (Set.range ![e, ((x : orthDerived Q) : V ≃ₗ[K] V) e]) with hTx
    set Ty := Submodule.span K (Set.range ![e, ((y : orthDerived Q) : V ≃ₗ[K] V) e]) with hTy
    have hexT : e ∈ Tx := Submodule.subset_span ⟨0, rfl⟩
    have hexT' : e ∈ Ty := Submodule.subset_span ⟨0, rfl⟩
    have hTx2 : finrank K Tx = 2 := by rw [hTx, finrank_span_eq_card hlix]; simp
    have hTy2 : finrank K Ty = 2 := by rw [hTy, finrank_span_eq_card hliy]; simp
    set S : Submodule K V := X ⊓ LinearMap.ker (polarBilin Q e) with hS
    have hmemS : ∀ v, v ∈ S ↔ v ∈ X ∧ polar Q e v = 0 := fun v => by
      rw [hS, Submodule.mem_inf, LinearMap.mem_ker, polarBilin_apply_apply]
    have hTxX : Tx ≤ X := by
      rw [hTx, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact heX
      · exact hXst x e heX
    have hTyX : Ty ≤ X := by
      rw [hTy, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact heX
      · exact hXst y e heX
    have hTxS : Tx ≤ S := fun v hv => (hmemS v).mpr ⟨hTxX hv, hTxp e hexT v hv⟩
    have hTyS : Ty ≤ S := fun v hv => (hmemS v).mpr ⟨hTyX hv, hTyp e hexT' v hv⟩
    have hSlt : S < X := by
      refine lt_of_le_of_ne inf_le_left fun hSX => ?_
      obtain ⟨u, huX, hu⟩ := hXreg.exists_polar_ne_zero heX he0
      have : u ∈ S := hSX ▸ huX
      exact hu ((hmemS u).mp this).2
    have hS3 : finrank K S ≤ 3 := by
      have := Submodule.finrank_lt_finrank_of_lt hSlt
      omega
    have hne : Tx ≠ Ty := by
      intro hxy
      have hTstx : ∀ t ∈ Tx, ((x : orthDerived Q) : V ≃ₗ[K] V) t ∈ Tx := by
        intro t ht
        obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp ht
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_smul]
        rw [hrx]
        have h1 : ((x : orthDerived Q) : V ≃ₗ[K] V) e ∈ Tx := Submodule.subset_span ⟨1, rfl⟩
        exact Tx.add_mem (Tx.smul_mem _ h1) (Tx.smul_mem _ (Tx.sub_mem (Tx.smul_mem _ h1) hexT))
      have hTsty : ∀ t ∈ Tx, ((y : orthDerived Q) : V ≃ₗ[K] V) t ∈ Tx := by
        intro t ht
        rw [hxy] at ht ⊢
        obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp ht
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_smul]
        rw [hry]
        have h1 : ((y : orthDerived Q) : V ≃ₗ[K] V) e ∈ Ty := Submodule.subset_span ⟨1, rfl⟩
        exact Ty.add_mem (Ty.smul_mem _ h1) (Ty.smul_mem _ (Ty.sub_mem (Ty.smul_mem _ h1) hexT'))
      have hst := manyTwo_eStable_of_closure hK hp.pos hcl hTstx hTsty
      have hbot := hNS Tx hst hTxQ
      rw [hbot] at hexT
      exact he0 ((Submodule.mem_bot K).mp hexT)
    have hinf : finrank K ↥(Tx ⊓ Ty) ≤ 1 := by
      by_contra hcon
      push Not at hcon
      have e1 : Tx ⊓ Ty = Tx :=
        Submodule.eq_of_le_of_finrank_le inf_le_left (by omega)
      have e2 : Tx ⊓ Ty = Ty :=
        Submodule.eq_of_le_of_finrank_le inf_le_right (by omega)
      exact hne (e1.symm.trans e2)
    have hsup3 : 3 ≤ finrank K ↥(Tx ⊔ Ty) := by
      have := Submodule.finrank_sup_add_finrank_inf_eq Tx Ty
      omega
    have hSeq : Tx ⊔ Ty = S :=
      Submodule.eq_of_le_of_finrank_le (sup_le hTxS hTyS) (by omega)
    have hwS : w ∈ Tx ⊔ Ty := by rw [hSeq, hmemS]; exact ⟨hwX, hew⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hwS
    rw [← eichler_mul (hTxp e hexT a ha) (hTyp e hexT' b hb)]
    exact (orthCentralizerSpan Q E).mul_mem
      (manyTwo_eichler_mem_of_plane hEΩ hx1 heQ hτ hrx hlix a ha)
      (manyTwo_eichler_mem_of_plane hEΩ hy1 heQ hτ hry hliy b hb)
  obtain ⟨u, huX, hu0, huQ⟩ := exists_singular_of_three_le_any (Q := Q) (S := X) (by omega)
  obtain ⟨u', hu'X, hu'Q, huu'⟩ := exists_partner_of_polarNondegOn hXreg huX hu0 huQ
  have hu'0 : u' ≠ 0 := fun h0 => by
    rw [h0, polar_zero_right] at huu'
    exact zero_ne_one huu'
  exact eichler_mem_of_relRoot (orthCentralizerSpan_le_orthogonalGroup E) hXreg huX hu'X huQ hu'Q
    (by rw [huu']; exact one_ne_zero) (fun w hw hpw => hroot u huX hu0 huQ w hw hpw)
    (fun w hw hpw => hroot u' hu'X hu'0 hu'Q w hw hpw)

end Pair

section Mixed

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem manyTwo_exists_ne_zero_polar_eq_zero {P : Submodule K V} (hP : 2 ≤ finrank K P) (v : V) :
    ∃ f ∈ P, f ≠ 0 ∧ polar Q v f = 0 := by
  let φ : P →ₗ[K] K := (polarBilin Q v).comp P.subtype
  have hrn := LinearMap.finrank_range_add_finrank_ker φ
  have hrange : finrank K (LinearMap.range φ) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range φ)
    simpa using this
  have hker : LinearMap.ker φ ≠ ⊥ := by
    rw [← Submodule.one_le_finrank_iff]
    omega
  obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨(f : V), f.2, fun h => hf0 (Subtype.ext h), ?_⟩
  have := LinearMap.mem_ker.mp hf
  simpa [φ, polarBilin_apply_apply] using this

theorem exists_mixed_vector {H : Subgroup (V ≃ₗ[K] V)}
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q) {P₁ P₂ P₃ Y : Submodule K V}
    (hP₁ : PolarNondegOn Q P₁) (hP₂ : PolarNondegOn Q P₂) (hP₃ : PolarNondegOn Q P₃)
    (h12 : OrthSep Q P₁ P₂) (h13 : OrthSep Q P₁ P₃) (h23 : OrthSep Q P₂ P₃)
    (hd₁ : Module.finrank K P₁ = 2) (hd₂ : Module.finrank K P₂ = 2)
    (hd₃ : Module.finrank K P₃ = 2)
    (ha₁ : ∀ t ∈ P₁, Q t = 0 → t = 0) (ha₂ : ∀ t ∈ P₂, Q t = 0 → t = 0)
    (ha₃ : ∀ t ∈ P₃, Q t = 0 → t = 0) (hK3 : 3 ≤ Nat.card K)
    (hY : P₃ ≤ Y) (hYP : OrthSep Q Y (P₁ ⊔ P₂))
    (hEich : ∀ e ∈ P₂ ⊔ P₃, ∀ w ∈ P₂ ⊔ P₃, eichler Q e w ∈ H)
    {s : V} (hs : s ∈ P₁ ⊔ P₂) (hs0 : s ≠ 0) (hsQ : Q s = 0)
    (hrel : ∀ w ∈ P₁ ⊔ P₂, polar Q s w = 0 → w ∈ rootSet Q H s) :
    ∃ w ∈ rootSet Q H s, ∃ y ∈ Y, ∃ r : V, w = y + r ∧ (∀ z ∈ Y, polar Q z r = 0) ∧ y ≠ 0 := by
  classical
  obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := Submodule.mem_sup.mp hs
  have hs₁0 : s₁ ≠ 0 := by
    rintro rfl
    rw [zero_add] at hsQ hs0
    exact hs0 (ha₂ s₂ hs₂ hsQ)
  have hs₂0 : s₂ ≠ 0 := by
    rintro rfl
    rw [add_zero] at hsQ hs0
    exact hs0 (ha₁ s₁ hs₁ hsQ)
  obtain ⟨f₀, hf₀P, hf₀0, hf₀s⟩ := manyTwo_exists_ne_zero_polar_eq_zero (Q := Q) (P := P₂) hd₂.ge s₂
  have hdisj : Disjoint (Submodule.span K {f₀}) P₃ :=
    (OrthSep.disjoint hP₂ h23).mono_left (Submodule.span_le.mpr (by simpa using hf₀P))
  have hS₃dim : 3 ≤ finrank K ↥(Submodule.span K {f₀} ⊔ P₃) := by
    have := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span K {f₀}) P₃
    rw [hdisj.eq_bot, finrank_bot, add_zero, finrank_span_singleton hf₀0] at this
    omega
  obtain ⟨f, hfS, hf0, hfQ⟩ := exists_singular_of_three_le_any (Q := Q) hS₃dim
  obtain ⟨a, ha, f₃, hf₃, rfl⟩ := Submodule.mem_sup.mp hfS
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
  have hf₂P : c • f₀ ∈ P₂ := P₂.smul_mem c hf₀P
  have hf₂s : polar Q s₂ (c • f₀) = 0 := by rw [polar_smul_right_eq, hf₀s, mul_zero]
  have hf₂0 : c • f₀ ≠ 0 := by
    intro h0
    rw [h0, zero_add] at hf0 hfQ
    exact hf0 (ha₃ f₃ hf₃ hfQ)
  have hf₃0 : f₃ ≠ 0 := by
    intro h0
    rw [h0, add_zero] at hf0 hfQ
    exact hf0 (ha₂ _ hf₂P hfQ)
  obtain ⟨d₁, d₂, hd₁, hd₂', hd₁₂⟩ : ∃ d₁ d₂ : K, d₁ ≠ 0 ∧ d₂ ≠ 0 ∧ d₁ ≠ d₂ := by
    haveI := Fintype.ofFinite K
    have h3 : 2 < Fintype.card K := by rw [← Nat.card_eq_fintype_card]; omega
    obtain ⟨x, y, z, hxy, hxz, hyz⟩ := Fintype.two_lt_card_iff.mp h3
    exact ⟨x - y, x - z, sub_ne_zero.mpr hxy, sub_ne_zero.mpr hxz,
      fun h => hyz (sub_right_injective h)⟩
  obtain ⟨v, hvP, hv0, hvf⟩ := manyTwo_exists_ne_zero_polar_eq_zero (Q := Q) (P := P₃) hd₃.ge f₃
  have hex : ∃ d : K, d • v - Q (d • v) • f₃ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have e1 := hcon d₁
    have e2 := hcon d₂
    rw [map_smul_eq_sq] at e1 e2
    have h0 : (d₁ * d₂ * (d₂ - d₁) * Q v) • f₃ = 0 := by
      linear_combination (norm := module) d₂ • e1 - d₁ • e2
    rcases smul_eq_zero.mp h0 with h | h
    · have hQv : Q v = 0 := by
        have h' : d₁ * d₂ * (d₂ - d₁) ≠ 0 :=
          mul_ne_zero (mul_ne_zero hd₁ hd₂') (sub_ne_zero.mpr hd₁₂.symm)
        exact (mul_eq_zero.mp h).resolve_left h'
      exact hv0 (ha₃ v hvP hQv)
    · exact hf₃0 h
  obtain ⟨d, hd⟩ := hex
  have hdvP : d • v ∈ P₃ := P₃.smul_mem d hvP
  have hf₂v : polar Q (c • f₀) v = 0 := h23 _ hf₂P _ hvP
  have hpol : polar Q (c • f₀ + f₃) (d • v) = 0 := by
    rw [polar_add_left, polar_smul_right_eq, polar_smul_right_eq, hf₂v, hvf]
    ring
  have hfmem : c • f₀ + f₃ ∈ P₂ ⊔ P₃ := Submodule.add_mem_sup hf₂P hf₃
  have hg : eichler Q (c • f₀ + f₃) (d • v) ∈ H :=
    hEich _ hfmem _ (Submodule.mem_sup_right hdvP)
  have e1₂ : polar Q s₁ (c • f₀) = 0 := h12 _ hs₁ _ hf₂P
  have e1₃ : polar Q s₁ f₃ = 0 := h13 _ hs₁ _ hf₃
  have e2₃ : polar Q s₂ f₃ = 0 := h23 _ hs₂ _ hf₃
  have e1v : polar Q s₁ v = 0 := h13 _ hs₁ _ hvP
  have e2v : polar Q s₂ v = 0 := h23 _ hs₂ _ hvP
  have hgs : eichler Q (c • f₀ + f₃) (d • v) (s₁ + s₂) = s₁ + s₂ := by
    refine eichler_apply_of_polar_eq_zero ?_ ?_
    · simp only [polar_add_left, polar_add_right, e1₂, e1₃, hf₂s, e2₃]
      ring
    · simp only [polar_add_left, polar_smul_right_eq, e1v, e2v]
      ring
  obtain ⟨u₂, hu₂P, hu₂⟩ := hP₂.exists_polar_ne_zero hf₂P hf₂0
  obtain ⟨z, hzP, hz⟩ := hP₁.exists_polar_ne_zero hs₁ hs₁0
  have hu₁P : (-polar Q s₂ u₂ / polar Q s₁ z) • z ∈ P₁ := P₁.smul_mem _ hzP
  have hsu₁ : polar Q s₁ ((-polar Q s₂ u₂ / polar Q s₁ z) • z) = -polar Q s₂ u₂ := by
    rw [polar_smul_right_eq]
    field_simp
  set u₁ : V := (-polar Q s₂ u₂ / polar Q s₁ z) • z with hu₁def
  have hw₀P : u₁ + u₂ ∈ P₁ ⊔ P₂ := Submodule.add_mem_sup hu₁P hu₂P
  have e12 : polar Q s₁ u₂ = 0 := h12 _ hs₁ _ hu₂P
  have e21 : polar Q s₂ u₁ = 0 := by rw [polar_comm]; exact h12 _ hu₁P _ hs₂
  have hw₀s : polar Q (s₁ + s₂) (u₁ + u₂) = 0 := by
    simp only [polar_add_left, polar_add_right, hsu₁, e12, e21]
    ring
  have hw₀ : u₁ + u₂ ∈ rootSet Q H (s₁ + s₂) := hrel _ hw₀P hw₀s
  have h1 := rootSet_map hH hg hw₀
  rw [hgs] at h1
  have h2 := AddSubgroup.sub_mem _ h1 hw₀
  have f12 : polar Q u₁ (c • f₀) = 0 := h12 _ hu₁P _ hf₂P
  have f13 : polar Q u₁ f₃ = 0 := h13 _ hu₁P _ hf₃
  have f23 : polar Q u₂ f₃ = 0 := h23 _ hu₂P _ hf₃
  have g13 : polar Q u₁ v = 0 := h13 _ hu₁P _ hvP
  have g23 : polar Q u₂ v = 0 := h23 _ hu₂P _ hvP
  have hpolf : polar Q (u₁ + u₂) (c • f₀ + f₃) = polar Q u₂ (c • f₀) := by
    simp only [polar_add_left, polar_add_right, f12, f13, f23]
    ring
  have hpolv : polar Q (u₁ + u₂) (d • v) = 0 := by
    simp only [polar_add_left, polar_smul_right_eq, g13, g23]
    ring
  have hδ0 : polar Q u₂ (c • f₀) ≠ 0 := by rw [polar_comm]; exact hu₂
  have hgw : eichler Q (c • f₀ + f₃) (d • v) (u₁ + u₂) - (u₁ + u₂) =
      polar Q u₂ (c • f₀) • (d • v - Q (d • v) • f₃) +
        (-(Q (d • v) * polar Q u₂ (c • f₀))) • (c • f₀) := by
    rw [eichler_apply hfQ hpol, hpolf, hpolv]
    module
  refine ⟨_, h2, polar Q u₂ (c • f₀) • (d • v - Q (d • v) • f₃), ?_,
    (-(Q (d • v) * polar Q u₂ (c • f₀))) • (c • f₀), hgw, ?_, smul_ne_zero hδ0 hd⟩
  · exact hY (P₃.smul_mem _ (P₃.sub_mem hdvP (P₃.smul_mem _ hf₃)))
  · intro y hy
    exact hYP y hy _ (Submodule.mem_sup_right (P₂.smul_mem _ hf₂P))

end Mixed

end CFSG.LieType.SeitzGeneration
