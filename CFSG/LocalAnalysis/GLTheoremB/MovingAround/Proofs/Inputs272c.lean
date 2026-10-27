module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs272b

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs272c

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Prop1116Design
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs245
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs272b
open CFSG.LieType.SeitzGeneration (companionMat)
open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

section Singer

open Polynomial Matrix

variable {F : Type} [Field F] {p : ℕ}

theorem irreducible_kpoly (hp : p.Prime) {c : Fˣ} (hc : ¬ ∃ μ : Fˣ, μ ^ p = c) :
    Irreducible (X ^ p - C (c : F)) := by
  apply X_pow_sub_C_irreducible_of_prime hp
  intro b hb
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hb
    exact c.ne_zero hb.symm
  exact hc ⟨Units.mk0 b hb0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hb])⟩

theorem exists_algebraMap_of_pow [Finite F] {E : Type*} [Field E] [Algebra F E] {e : E}
    (h : e ^ (Nat.card F - 1) = 1) : ∃ b : F, algebraMap F E b = e := by
  classical
  haveI := Fintype.ofFinite F
  by_contra hne
  push Not at hne
  have hQ : 1 < Nat.card F := Finite.one_lt_card
  set P : E[X] := X ^ (Nat.card F - 1) - C 1 with hP
  have hdeg : P.natDegree = Nat.card F - 1 := natDegree_X_pow_sub_C
  have hP0 : P ≠ 0 := X_pow_sub_C_ne_zero (by omega) 1
  set T : Finset E := insert e (Finset.univ.image (fun b : Fˣ => algebraMap F E (b : F))) with hT
  have hTsub : T ⊆ P.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot, hP, eval_sub, eval_pow, eval_X, eval_C,
      sub_eq_zero]
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact h
    · obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hx
      rw [← map_pow, ← Units.val_pow_eq_pow_val, ← Nat.card_units, pow_card_eq_one',
        Units.val_one, map_one]
  have hTcard : T.card = Nat.card F := by
    rw [hT, Finset.card_insert_of_notMem, Finset.card_image_of_injective, Finset.card_univ,
      ← Nat.card_eq_fintype_card, Nat.card_units]
    · omega
    · intro b b' hbb'
      exact Units.ext ((algebraMap F E).injective hbb')
    · intro hmem
      obtain ⟨b, -, hb⟩ := Finset.mem_image.1 hmem
      exact hne b hb
  have h1 := Finset.card_le_card hTsub
  have h2 := Multiset.toFinset_card_le P.roots
  have h3 := card_roots' P
  omega

theorem sub_one_mul_geom {Q : ℕ} (hQ : 1 ≤ Q) (p : ℕ) :
    (Q - 1) * (∑ i ∈ Finset.range p, Q ^ i) = Q ^ p - 1 := by
  have h : ((Q : ℤ) - 1) * (∑ i ∈ Finset.range p, (Q : ℤ) ^ i) = (Q : ℤ) ^ p - 1 := by
    rw [mul_comm, geom_sum_mul]
  have hQp : 1 ≤ Q ^ p := Nat.one_le_pow _ _ hQ
  zify [hQ, hQp]
  exact h

theorem geom_modEq {Q ℓ : ℕ} (hQ : Q ≡ 1 [MOD ℓ]) (k : ℕ) :
    ∑ i ∈ Finset.range k, Q ^ i ≡ k [MOD ℓ] := by
  induction k with
  | zero => simp [Nat.ModEq.refl]
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have h1 : Q ^ k ≡ 1 [MOD ℓ] := by simpa using hQ.pow k
    exact ih.add h1

theorem exists_prime_dvd_geom {Q : ℕ} (hQ : 1 < Q) (hp : p.Prime) (hp2 : p ≠ 2) (hpQ : p ∣ Q - 1) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ p ∧ ℓ ∣ Q ^ p - 1 ∧ ¬ ℓ ∣ Q - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 := three_le_of_prime_ne_two hp hp2
  set N := ∑ i ∈ Finset.range p, Q ^ i with hN
  have hmul := sub_one_mul_geom hQ.le p
  rw [← hN] at hmul
  have hNp : N ≡ p [MOD p] := geom_modEq ((Nat.modEq_iff_dvd' hQ.le).2 hpQ).symm p
  have hpN : p ∣ N := (Nat.modEq_zero_iff_dvd.1 (hNp.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl)))
  have hpQ' : ¬ p ∣ Q := by
    intro h
    have h1 : p ∣ Q - (Q - 1) := Nat.dvd_sub h hpQ
    rw [show Q - (Q - 1) = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hlte := padicValNat.pow_sub_pow (p := p) (hp.odd_of_ne_two hp2) (y := 1) (x := Q) hQ
    (by simpa using hpQ) hpQ' hp.ne_zero
  rw [one_pow, padicValNat_self] at hlte
  have hQ1 : Q - 1 ≠ 0 := by omega
  have hN0 : N ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmul
    have : 1 < Q ^ p := Nat.one_lt_pow hp.ne_zero hQ
    omega
  rw [← hmul, padicValNat.mul hQ1 hN0] at hlte
  have hvN : padicValNat p N = 1 := by omega
  have hp2N : ¬ p ^ 2 ∣ N := by
    intro h
    have := (padicValNat_dvd_iff_le hN0).1 h
    omega
  have hNgt : p < N := by
    have h1 : ∀ k, k ≤ ∑ i ∈ Finset.range k, Q ^ i := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_range_succ]
        have : 1 ≤ Q ^ k := Nat.one_le_pow _ _ (by omega)
        omega
    obtain ⟨k, hk⟩ : ∃ k, p = k + 2 := ⟨p - 2, by omega⟩
    rw [hN, hk, Finset.sum_range_succ]
    have h2 := h1 (k + 1)
    have h3 : Q ≤ Q ^ (k + 1) := by
      calc Q = Q ^ 1 := (pow_one Q).symm
        _ ≤ Q ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  obtain ⟨r, hr⟩ := hpN
  have hr1 : r ≠ 1 := by
    rintro rfl
    rw [mul_one] at hr
    omega
  have hpr : ¬ p ∣ r := by
    rintro ⟨t, rfl⟩
    apply hp2N
    exact ⟨t, by rw [hr]; ring⟩
  set ℓ := r.minFac with hℓ
  have hℓp : ℓ.Prime := Nat.minFac_prime hr1
  have hℓr : ℓ ∣ r := Nat.minFac_dvd r
  have hℓN : ℓ ∣ N := hr ▸ Dvd.dvd.mul_left hℓr p
  refine ⟨ℓ, hℓp, fun h => hpr (h ▸ hℓr), ?_, fun hℓQ => ?_⟩
  · rw [← hmul]
    exact Dvd.dvd.mul_left hℓN _
  · have h1 : N ≡ p [MOD ℓ] := geom_modEq ((Nat.modEq_iff_dvd' hQ.le).2 hℓQ).symm p
    have h2 : ℓ ∣ p := (Nat.modEq_zero_iff_dvd.1 (h1.symm.trans (Nat.modEq_zero_iff_dvd.2 hℓN)))
    have h3 := (Nat.prime_dvd_prime_iff_eq hℓp hp).1 h2
    exact hpr (h3 ▸ hℓr)

theorem singer_setup [Finite F] [NeZero p] (hp : p.Prime) {c : Fˣ} (hc : ¬ ∃ μ : Fˣ, μ ^ p = c) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra F E) (_ : Finite E)
      (φ : E →ₐ[F] Matrix (Fin p) (Fin p) F),
      Function.Injective φ ∧ Nat.card E = Nat.card F ^ p ∧
      (∀ Xm : Matrix (Fin p) (Fin p) F, Xm * companionMat p (c : F) = companionMat p (c : F) * Xm →
        ∃ e, φ e = Xm) ∧
      (∀ e, φ e * companionMat p (c : F) = companionMat p (c : F) * φ e) := by
  classical
  set f : F[X] := X ^ p - C (c : F) with hf
  haveI : Fact (Irreducible f) := ⟨irreducible_kpoly hp hc⟩
  have hf0 : f ≠ 0 := X_pow_sub_C_ne_zero (NeZero.pos p) _
  have hfC : aeval (companionMat p (c : F)) f = 0 := by
    rw [hf, map_sub, map_pow, aeval_X, aeval_C,
      CFSG.LieType.SeitzGeneration.thmU_companionMat_pow_p, Algebra.algebraMap_eq_smul_one, sub_self]
  have hI : ∀ a : F[X], a ∈ Ideal.span {f} → aeval (companionMat p (c : F)) a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, hfC, mul_zero]
  let φ : AdjoinRoot f →ₐ[F] Matrix (Fin p) (Fin p) F :=
    Ideal.Quotient.liftₐ (Ideal.span {f}) (aeval (companionMat p (c : F))) hI
  have hφmk : ∀ g : F[X], φ (AdjoinRoot.mk f g) = aeval (companionMat p (c : F)) g := fun g => rfl
  have hroot : φ (AdjoinRoot.root f) = companionMat p (c : F) := by
    rw [← AdjoinRoot.mk_X, hφmk, aeval_X]
  haveI : Module.Finite F (AdjoinRoot f) := (AdjoinRoot.powerBasis hf0).finite
  haveI : Finite (AdjoinRoot f) := Module.finite_of_finite F
  refine ⟨AdjoinRoot f, inferInstance, inferInstance, inferInstance, φ, ?_, ?_, ?_, ?_⟩
  · exact (φ : AdjoinRoot f →+* Matrix (Fin p) (Fin p) F).injective
  · rw [Module.natCard_eq_pow_finrank (K := F), (AdjoinRoot.powerBasis hf0).finrank,
      AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C]
  · intro Xm hXm
    refine ⟨AdjoinRoot.mk f (∑ k : Fin p, monomial (k : ℕ) (Xm k 0)), ?_⟩
    rw [hφmk]
    exact (eq_aeval_of_comm_companion (c : F) hXm).symm
  · intro e
    rw [← hroot, ← map_mul, ← map_mul, mul_comm]

theorem eq_scalar_of_two_comm_companion [Finite F] (hp : p.Prime) (hQ : Odd (Nat.card F))
    (hpodd : Odd p) {M g u : GL (Fin p) F} {c : Fˣ} (hc : ¬ ∃ μ : Fˣ, μ ^ p = c)
    (hg : ((M⁻¹ * g * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = companionMat p (c : F))
    (hug : u * g = g * u) {k : ℕ} {a : Fˣ}
    (hu : u ^ 2 ^ k = Matrix.GeneralLinearGroup.scalar (Fin p) a) :
    ∃ b : Fˣ, u = Matrix.GeneralLinearGroup.scalar (Fin p) b := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨E, _, _, _, φ, hφ, hcard, hrange, -⟩ := singer_setup hp hc
  have hUC : ((M⁻¹ * u * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) * companionMat p (c : F) =
      companionMat p (c : F) * ((M⁻¹ * u * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
    rw [← hg, ← Units.val_mul, ← Units.val_mul]
    congr 1
    calc M⁻¹ * u * M * (M⁻¹ * g * M) = M⁻¹ * (u * g) * M := by group
      _ = M⁻¹ * (g * u) * M := by rw [hug]
      _ = M⁻¹ * g * M * (M⁻¹ * u * M) := by group
  obtain ⟨e, he⟩ := hrange _ hUC
  have hU2 : ((M⁻¹ * u * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) ^ 2 ^ k = (a : F) • 1 := by
    have hc' := conj_pow (a := M⁻¹) (b := u) (i := 2 ^ k)
    rw [inv_inv] at hc'
    rw [← Units.val_pow_eq_pow_val, hc', hu, mul_assoc,
      Matrix.GeneralLinearGroup.scalar_commute a M, ← mul_assoc, inv_mul_cancel, one_mul,
      CFSG.LieType.SeitzGeneration.coe_scalarGL]
  have he2 : e ^ 2 ^ k = algebraMap F E a := by
    apply hφ
    rw [map_pow, he, hU2, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
  set Q := Nat.card F with hQdef
  have hQ1 : 1 < Q := Finite.one_lt_card
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [zero_pow (by positivity), eq_comm, map_eq_zero] at he2
    exact a.ne_zero he2
  set N := ∑ i ∈ Finset.range p, Q ^ i with hN
  have hmul := sub_one_mul_geom hQ1.le p
  rw [← hN] at hmul
  have hNodd : Nat.Coprime (2 ^ k) N := by
    apply Nat.Coprime.pow_left
    have h1 : N ≡ p [MOD 2] := geom_modEq (Nat.odd_iff.1 hQ) p
    rw [Nat.coprime_two_left, Nat.odd_iff, ← Nat.odd_iff.1 hpodd]
    exact h1
  have h1 : (e ^ (Q - 1)) ^ 2 ^ k = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, he2, ← map_pow, ← Units.val_pow_eq_pow_val,
      ← Nat.card_units, pow_card_eq_one', Units.val_one, map_one]
  have h2 : (e ^ (Q - 1)) ^ N = 1 := by
    rw [← pow_mul, hmul]
    have h3 : (Units.mk0 e he0) ^ Nat.card Eˣ = 1 := pow_card_eq_one'
    rw [Nat.card_units, hcard] at h3
    have := congrArg Units.val h3
    simpa using this
  have h3 := pow_gcd_eq_one.2 ⟨h1, h2⟩
  rw [hNodd, pow_one] at h3
  obtain ⟨b, hb⟩ := exists_algebraMap_of_pow h3
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero] at hb
    exact he0 hb.symm
  refine ⟨Units.mk0 b hb0, ?_⟩
  have h4 : M⁻¹ * u * M = Matrix.GeneralLinearGroup.scalar (Fin p) (Units.mk0 b hb0) := by
    apply Units.ext
    rw [← he, ← hb, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
      CFSG.LieType.SeitzGeneration.coe_scalarGL, Units.val_mk0]
  calc u = M * (M⁻¹ * u * M) * M⁻¹ := by group
    _ = M * Matrix.GeneralLinearGroup.scalar (Fin p) (Units.mk0 b hb0) * M⁻¹ := by rw [h4]
    _ = Matrix.GeneralLinearGroup.scalar (Fin p) (Units.mk0 b hb0) := by
      rw [← Matrix.GeneralLinearGroup.scalar_commute (Units.mk0 b hb0) M, mul_inv_cancel_right]

theorem exists_singer_elt [Finite F] (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1)
    {M g : GL (Fin p) F} {c : Fˣ} (hc : ¬ ∃ μ : Fˣ, μ ^ p = c)
    (hg : ((M⁻¹ * g * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = companionMat p (c : F)) :
    ∃ ℓ : ℕ, Nat.Coprime p ℓ ∧ ∃ u : GL (Fin p) F, (u : Matrix (Fin p) (Fin p) F).det = 1 ∧
      u * g = g * u ∧ u ^ ℓ = 1 ∧ ∀ b : Fˣ, u ≠ Matrix.GeneralLinearGroup.scalar (Fin p) b := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨E, _, _, _, φ, hφ, hcard, -, hcomm⟩ := singer_setup hp hc
  set Q := Nat.card F with hQdef
  have hQ1 : 1 < Q := Finite.one_lt_card
  obtain ⟨ℓ, hℓ, hℓp, hℓdvd, hℓQ⟩ := exists_prime_dvd_geom hQ1 hp hp2 hpF
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hEu : Nat.card Eˣ = Q ^ p - 1 := by rw [Nat.card_units, hcard]
  obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' ℓ (hEu ▸ hℓdvd)
  let u₀ : GL (Fin p) F :=
    ⟨φ (e : E), φ ((e⁻¹ : Eˣ) : E), by rw [← map_mul, Units.mul_inv, map_one],
      by rw [← map_mul, Units.inv_mul, map_one]⟩
  have hu₀ : (u₀ : Matrix (Fin p) (Fin p) F) = φ (e : E) := rfl
  have hu₀pow : ∀ n : ℕ, ((u₀ ^ n : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = φ ((e ^ n : Eˣ) : E) := by
    intro n
    rw [Units.val_pow_eq_pow_val, hu₀, ← map_pow, Units.val_pow_eq_pow_val]
  have hdet : (u₀ : Matrix (Fin p) (Fin p) F).det = 1 := by
    set d := (u₀ : Matrix (Fin p) (Fin p) F).det with hd
    have hd0 : d ≠ 0 := by
      rw [hd]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 u₀.isUnit).ne_zero
    have hdℓ : d ^ ℓ = 1 := by
      rw [hd, ← Matrix.det_pow, ← Units.val_pow_eq_pow_val, hu₀pow, ← he, pow_orderOf_eq_one,
        Units.val_one, map_one, Matrix.det_one]
    have hdQ : d ^ (Q - 1) = 1 := by
      have := pow_card_eq_one' (G := Fˣ) (x := Units.mk0 d hd0)
      rw [Nat.card_units] at this
      simpa using congrArg Units.val this
    have hg1 : Nat.gcd ℓ (Q - 1) = 1 := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓQ).symm)
    have := pow_gcd_eq_one.2 ⟨hdℓ, hdQ⟩
    rwa [hg1, pow_one] at this
  refine ⟨ℓ, (Nat.coprime_primes hp hℓ).2 (Ne.symm hℓp), M * u₀ * M⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, one_mul, hdet]
  · have h1 : u₀ * (M⁻¹ * g * M) = (M⁻¹ * g * M) * u₀ := by
      apply Units.ext
      have e1 := Units.val_mul u₀ (M⁻¹ * g * M)
      have e2 := Units.val_mul (M⁻¹ * g * M) u₀
      rw [e1, e2, hg, hu₀]
      exact hcomm (e : E)
    calc M * u₀ * M⁻¹ * g = M * (u₀ * (M⁻¹ * g * M)) * M⁻¹ := by group
      _ = M * ((M⁻¹ * g * M) * u₀) * M⁻¹ := by rw [h1]
      _ = g * (M * u₀ * M⁻¹) := by group
  · rw [conj_pow]
    have : u₀ ^ ℓ = 1 := by
      apply Units.ext
      rw [hu₀pow, ← he, pow_orderOf_eq_one, Units.val_one, map_one, Units.val_one]
    rw [this, mul_one, mul_inv_cancel]
  · intro b hb
    have h1 : u₀ = Matrix.GeneralLinearGroup.scalar (Fin p) b := by
      calc u₀ = M⁻¹ * (M * u₀ * M⁻¹) * M := by group
        _ = M⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin p) b * M := by rw [hb]
        _ = Matrix.GeneralLinearGroup.scalar (Fin p) b := by
          rw [mul_assoc, Matrix.GeneralLinearGroup.scalar_commute b M, ← mul_assoc, inv_mul_cancel,
            one_mul]
    have h2 : (e : E) = algebraMap F E b := by
      apply hφ
      rw [← hu₀, h1, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
        CFSG.LieType.SeitzGeneration.coe_scalarGL]
    have h3 : e ^ (Q - 1) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, h2, ← map_pow, ← Units.val_pow_eq_pow_val, ← Nat.card_units,
        pow_card_eq_one', Units.val_one, map_one, Units.val_one]
    have h4 := orderOf_dvd_of_pow_eq_one h3
    rw [he] at h4
    exact hℓQ h4

end Singer

section InnDiagCore

open Matrix

variable {F : Type} [Field F] {p : ℕ}

theorem eq_scalar_of_comm_pair (hp : p.Prime) {M y x g : GL (Fin p) F} {δ : Fin p → F}
    (hδ : Function.Injective δ) {c : F}
    (hy : ((M⁻¹ * y * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = diagonal δ)
    (hx : ((M⁻¹ * x * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = companionMat p c)
    (hgy : g * y = y * g) (hgx : g * x = x * g) :
    ∃ a : Fˣ, g = Matrix.GeneralLinearGroup.scalar (Fin p) a := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hconj : ∀ u v : GL (Fin p) F, u * v = v * u →
      ((M⁻¹ * u * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) *
        ((M⁻¹ * v * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) =
      ((M⁻¹ * v * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) *
        ((M⁻¹ * u * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
    intro u v huv
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    calc M⁻¹ * u * M * (M⁻¹ * v * M) = M⁻¹ * (u * v) * M := by group
      _ = M⁻¹ * (v * u) * M := by rw [huv]
      _ = M⁻¹ * v * M * (M⁻¹ * u * M) := by group
  set G := ((M⁻¹ * g * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) with hG
  set t : Fin p → F := fun i => G i i with ht
  have hGd : G = diagonal t := by
    have h1 := hconj g y hgy
    rw [hy] at h1
    exact eq_diagonal_of_mul_diagonal hδ h1
  have hGC := hconj g x hgx
  rw [hx, ← hG, hGd, CFSG.LieType.SeitzGeneration.thmU_companionMat_mul_diagonal] at hGC
  have hCu : IsUnit (companionMat p c) := by rw [← hx]; exact (M⁻¹ * x * M).isUnit
  have hshift : diagonal t = diagonal (fun i => t (i - 1)) := by
    obtain ⟨Cu, hCu'⟩ := hCu
    have h1 := congrArg (fun X => X * ((Cu⁻¹ : (Matrix (Fin p) (Fin p) F)ˣ) : Matrix (Fin p) (Fin p) F))
      hGC
    simp only [← hCu', Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at h1
    exact h1
  have hstep : ∀ i, t i = t (i - 1) := fun i => by
    have := congrFun (congrFun hshift i) i
    simpa using this
  have h10 : (1 : Fin p) ≠ 0 := by
    rw [Ne, Fin.ext_iff, Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt hp.one_lt]
    exact one_ne_zero
  have hconst : ∀ i, t i = t 0 := by
    intro i
    obtain ⟨m, rfl⟩ := exists_nsmul_eq_of_ne_zero hp h10 i
    induction m with
    | zero => simp
    | succ m ih => rw [succ_nsmul, hstep, add_sub_cancel_right, ih]
  have ht0 : t 0 ≠ 0 := by
    intro h0
    have : G = 0 := by
      rw [hGd]
      ext i j
      by_cases hij : i = j
      · subst hij; simp [hconst i, h0]
      · simp [diagonal_apply_ne _ hij]
    have h1 := (M⁻¹ * g * M).isUnit
    rw [← hG, this] at h1
    exact not_isUnit_zero h1
  refine ⟨Units.mk0 _ ht0, ?_⟩
  have h1 : M⁻¹ * g * M = Matrix.GeneralLinearGroup.scalar (Fin p) (Units.mk0 _ ht0) := by
    apply Units.ext
    rw [← hG, hGd, CFSG.LieType.SeitzGeneration.coe_scalarGL, Units.val_mk0]
    ext i j
    by_cases hij : i = j
    · subst hij; simp [hconst i]
    · simp [diagonal_apply_ne _ hij, hij]
  calc g = M * (M⁻¹ * g * M) * M⁻¹ := by group
    _ = M * Matrix.GeneralLinearGroup.scalar (Fin p) (Units.mk0 _ ht0) * M⁻¹ := by rw [h1]
    _ = _ := by rw [← Matrix.GeneralLinearGroup.scalar_commute _ M, mul_inv_cancel_right]

theorem comm_of_pow_scalar (hp : p.Prime) {x g : GL (Fin p) F} {c : Fˣ}
    (h1 : x * g = Matrix.GeneralLinearGroup.scalar (Fin p) c * (g * x)) {m : ℕ} (hm : Nat.Coprime p m)
    {a : Fˣ} (hxm : x ^ m = Matrix.GeneralLinearGroup.scalar (Fin p) a) : x * g = g * x := by
  have hz : ∀ k : GL (Fin p) F, Matrix.GeneralLinearGroup.scalar (Fin p) c * k =
      k * Matrix.GeneralLinearGroup.scalar (Fin p) c := fun k => scalar_mul_comm c k
  have h2 := CFSG.LieType.SeitzGeneration.sgo_pow_left_comm hz h1 m
  rw [hxm, ← map_pow, scalar_mul_comm a] at h2
  have h3 : Matrix.GeneralLinearGroup.scalar (Fin p) (c ^ m) = 1 :=
    (mul_right_cancel (b := g * Matrix.GeneralLinearGroup.scalar (Fin p) a)
      (by rw [one_mul]; exact h2.symm))
  have hcm : c ^ m = 1 := scalar_injective' (m := p) hp.one_lt.le (by rw [h3, map_one])
  have hcp : c ^ p = 1 := by
    have hdet := congrArg Matrix.GeneralLinearGroup.det h1
    rw [map_mul, map_mul, map_mul, CFSG.RankThree.PartOne.KCLinPlane.det_scalar_gl_units,
      mul_comm (Matrix.GeneralLinearGroup.det g)] at hdet
    exact mul_right_cancel (b := Matrix.GeneralLinearGroup.det x * Matrix.GeneralLinearGroup.det g)
      (by rw [one_mul]; exact hdet.symm)
  have hc1 : c = 1 := by
    have := pow_gcd_eq_one.2 ⟨hcp, hcm⟩
    rwa [hm, pow_one] at this
  rw [h1, hc1, map_one, one_mul]

variable {Y : Type} [Group Y] {H Γ : Subgroup (GL (Fin p) F)}

theorem comm_of_actsAsConj (hp : p.Prime) (hH1 : CentScalar H Γ)
    {θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj H} {x g : GL (Fin p) F} (hxΓ : x ∈ Γ) (hgΓ : g ∈ Γ)
    {r α : MulAut Y} (hx : ActsAsConj H θ x r) (hg : ActsAsConj H θ g α) (hrα : r * α = α * r)
    {m : ℕ} (hm : Nat.Coprime p m) (hrm : r ^ m = 1) : x * g = g * x := by
  obtain ⟨c, hc⟩ := actsAsConj_comm hH1 hgΓ hxΓ hg hx hrα.symm
  have hxm := actsAsConj_pow hx m
  rw [hrm] at hxm
  obtain ⟨a, ha⟩ := actsAsConj_one_scalar hH1 (Γ.pow_mem hxΓ m) hxm
  exact comm_of_pow_scalar hp hc hm ha

@[expose] def matGroup (Γ : Subgroup (GL (Fin p) F)) (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj H)
    (S : Subgroup (MulAut Y)) : Subgroup (GL (Fin p) F) where
  carrier := {x | x ∈ Γ ∧ ∃ s ∈ S, ActsAsConj H θ x s}
  mul_mem' := by
    rintro x x' ⟨hx, s, hs, hxs⟩ ⟨hx', s', hs', hxs'⟩
    exact ⟨Γ.mul_mem hx hx', s * s', S.mul_mem hs hs', ActsAsConj.mul hxs hxs'⟩
  one_mem' := ⟨Γ.one_mem, 1, S.one_mem, actsAsConj_one H θ⟩
  inv_mem' := by
    rintro x ⟨hx, s, hs, hxs⟩
    exact ⟨Γ.inv_mem hx, s⁻¹, S.inv_mem hs, ActsAsConj.inv hxs⟩

theorem claim_aut [Finite F] (hp : p.Prime) (hH1 : CentScalar H Γ) [Group.IsPerfect Y]
    {θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj H} {α eh : MulAut Y} {gα h M : GL (Fin p) F}
    (hgαΓ : gα ∈ Γ) (hhΓ : h ∈ Γ) (hgα : ActsAsConj H θ gα α) (hh : ActsAsConj H θ h eh)
    {δ : Fin p → F} (hδ : Function.Injective δ) {c : F}
    (hMα : ((M⁻¹ * gα * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = diagonal δ)
    (hMh : ((M⁻¹ * h * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = companionMat p c)
    {S R : Subgroup (MulAut Y)} (hSD : S ≤ innDiag H Γ θ) (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥)
    (hSα : ∀ s ∈ S, s * α = α * s) (hSh : ∀ s ∈ S, eh * s * eh⁻¹ ∈ S)
    (hRD : R ≤ innDiag H Γ θ) (hRS : ∀ r ∈ R, ∀ s ∈ S, r * s * r⁻¹ ∈ S)
    (hRh : ∀ r ∈ R, eh * r * eh⁻¹ ∈ R) (hRh' : ∀ r ∈ R, eh⁻¹ * r * eh ∈ R)
    (hRp : ∀ r ∈ R, ∃ m, Nat.Coprime p m ∧ r ^ m = 1) (hp2 : p ≠ 2) :
    ∀ r ∈ R, r * α = α * r := by
  classical
  have hcop2 : ∀ k : ℕ, Nat.Coprime p (2 ^ k) := fun k =>
    Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hdiag : ∀ x ∈ Γ, x * gα = gα * x →
      ∃ t, ((M⁻¹ * x * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = diagonal t := by
    intro x _ hx
    refine ⟨_, eq_diagonal_of_mul_diagonal hδ ?_⟩
    rw [← hMα, ← Units.val_mul, ← Units.val_mul]
    congr 1
    calc M⁻¹ * x * M * (M⁻¹ * gα * M) = M⁻¹ * (x * gα) * M := by group
      _ = M⁻¹ * (gα * x) * M := by rw [hx]
      _ = M⁻¹ * gα * M * (M⁻¹ * x * M) := by group
  have key := diag_of_claim hp M h hMh (matGroup Γ θ S) (matGroup Γ θ R)
    (fun x ⟨hxΓ, s, hs, hxs⟩ => by
      obtain ⟨k, hk⟩ := hS2 ⟨s, hs⟩
      have hsk : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      exact hdiag x hxΓ (comm_of_actsAsConj hp hH1 hxΓ hgαΓ hxs hgα (hSα s hs) (hcop2 k) hsk))
    (fun x ⟨hxΓ, s, hs, hxs⟩ => ⟨Γ.mul_mem (Γ.mul_mem hhΓ hxΓ) (Γ.inv_mem hhΓ), _, hSh s hs,
      ActsAsConj.mul (ActsAsConj.mul hh hxs) (ActsAsConj.inv hh)⟩)
    (by
      obtain ⟨s, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hS1
      obtain ⟨x, hxΓ, hxs⟩ := hSD s.2
      refine ⟨x, ⟨hxΓ, s, s.2, hxs⟩, fun a ha => hs1 (Subtype.ext ?_)⟩
      rw [ha] at hxs
      exact actsAsConj_eq hxs (actsAsConj_scalar θ a))
    (fun y ⟨hyΓ, r, hr, hyr⟩ x ⟨hxΓ, s, hs, hxs⟩ => ⟨Γ.mul_mem (Γ.mul_mem hyΓ hxΓ) (Γ.inv_mem hyΓ), _,
      hRS r hr s hs, ActsAsConj.mul (ActsAsConj.mul hyr hxs) (ActsAsConj.inv hyr)⟩)
    (fun y ⟨hyΓ, r, hr, hyr⟩ => ⟨Γ.mul_mem (Γ.mul_mem hhΓ hyΓ) (Γ.inv_mem hhΓ), _, hRh r hr,
      ActsAsConj.mul (ActsAsConj.mul hh hyr) (ActsAsConj.inv hh)⟩)
    (fun y ⟨hyΓ, r, hr, hyr⟩ => ⟨Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hhΓ) hyΓ) hhΓ, _, hRh' r hr,
      ActsAsConj.mul (ActsAsConj.mul (ActsAsConj.inv hh) hyr) hh⟩)
    (fun y ⟨hyΓ, r, hr, hyr⟩ => by
      obtain ⟨m, hm, hrm⟩ := hRp r hr
      have hym := actsAsConj_pow hyr m
      rw [hrm] at hym
      exact ⟨m, hm, actsAsConj_one_scalar hH1 (Γ.pow_mem hyΓ m) hym⟩)
  intro r hr
  obtain ⟨y, hyΓ, hyr⟩ := hRD hr
  obtain ⟨t, ht⟩ := key y ⟨hyΓ, r, hr, hyr⟩
  have hyg : y * gα = gα * y := comm_of_both_diag ht hMα
  have h1 := ActsAsConj.mul hyr hgα
  have h2 := ActsAsConj.mul hgα hyr
  rw [hyg] at h1
  exact actsAsConj_eq h1 h2

theorem pow_eq_one_of_comm_scalar {x g : GL (Fin p) F} {c : Fˣ}
    (h1 : x * g = Matrix.GeneralLinearGroup.scalar (Fin p) c * (g * x)) : c ^ p = 1 := by
  have hdet := congrArg Matrix.GeneralLinearGroup.det h1
  rw [map_mul, map_mul, map_mul, CFSG.RankThree.PartOne.KCLinPlane.det_scalar_gl_units,
    mul_comm (Matrix.GeneralLinearGroup.det g)] at hdet
  exact mul_right_cancel (b := Matrix.GeneralLinearGroup.det x * Matrix.GeneralLinearGroup.det g)
    (by rw [one_mul]; exact hdet.symm)

theorem isPrimitiveRoot_of_pow (hp : p.Prime) {c : Fˣ} (hcp : c ^ p = 1) (hc1 : c ≠ 1) :
    IsPrimitiveRoot (c : F) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  apply IsPrimitiveRoot.coe_units_iff.2
  rw [← orderOf_eq_prime hcp hc1]
  exact IsPrimitiveRoot.orderOf c

theorem inj_of_prim {w d : F} (hw : IsPrimitiveRoot w p) (hd : d ≠ 0) :
    Function.Injective (fun k : Fin p => d * w ^ (k : ℕ)) := by
  intro k k' hkk'
  exact Fin.ext (hw.pow_inj k.2 k'.2 (mul_left_cancel₀ hd hkk'))

theorem exists_pow_eq_of_comm_diag (hp0 : 0 < p) {M y g : GL (Fin p) F} {δ : Fin p → F}
    (hδ : Function.Injective δ)
    (hy : ((M⁻¹ * y * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = diagonal δ)
    (hgy : g * y = y * g) {ν : Fˣ} (hν : g ^ p = Matrix.GeneralLinearGroup.scalar (Fin p) ν) :
    ∃ l : Fˣ, l ^ p = ν := by
  set G := ((M⁻¹ * g * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) with hG
  have hGd : G = diagonal (fun i => G i i) := by
    apply eq_diagonal_of_mul_diagonal hδ
    rw [hG, ← hy, ← Units.val_mul, ← Units.val_mul]
    congr 1
    calc M⁻¹ * g * M * (M⁻¹ * y * M) = M⁻¹ * (g * y) * M := by group
      _ = M⁻¹ * (y * g) * M := by rw [hgy]
      _ = M⁻¹ * y * M * (M⁻¹ * g * M) := by group
  have hGp : G ^ p = (ν : F) • 1 := by
    have hc' := conj_pow (a := M⁻¹) (b := g) (i := p)
    rw [inv_inv] at hc'
    rw [hG, ← Units.val_pow_eq_pow_val, hc', hν, mul_assoc,
      Matrix.GeneralLinearGroup.scalar_commute ν M, ← mul_assoc, inv_mul_cancel, one_mul,
      CFSG.LieType.SeitzGeneration.coe_scalarGL]
  have h0 := congrFun (congrFun hGp ⟨0, hp0⟩) ⟨0, hp0⟩
  rw [hGd, diagonal_pow, diagonal_apply_eq] at h0
  simp only [Pi.pow_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h0
  have h00 : G ⟨0, hp0⟩ ⟨0, hp0⟩ ≠ 0 := by
    intro h00
    rw [h00, zero_pow hp0.ne'] at h0
    exact ν.ne_zero h0.symm
  exact ⟨Units.mk0 _ h00, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0]; exact h0)⟩

theorem mulAut_conj_conj {Y : Type} [Group Y] (e : MulAut Y) (y : Y) :
    e * MulAut.conj y * e⁻¹ = MulAut.conj (e y) := by
  ext z
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

@[expose] def RichCent (H : Subgroup (GL (Fin p) F)) (g : GL (Fin p) F) : Prop :=
  ∃ m : ℕ, Nat.Coprime p m ∧ ∃ u ∈ H, u * g = g * u ∧ u ^ m = 1 ∧
    ∀ b : Fˣ, u ≠ Matrix.GeneralLinearGroup.scalar (Fin p) b

@[expose] def RichD (H Γ : Subgroup (GL (Fin p) F)) : Prop :=
  ∀ g ∈ Γ, ∀ (M : GL (Fin p) F) (δ₀ : F) (w : Fˣ), δ₀ ≠ 0 → IsPrimitiveRoot (w : F) p →
    ((M⁻¹ * g * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) =
      diagonal (fun k : Fin p => δ₀ * (w : F) ^ (k : ℕ)) → RichCent H g

@[expose] def RichS (H Γ : Subgroup (GL (Fin p) F)) : Prop :=
  ∀ g ∈ Γ, ∀ (M : GL (Fin p) F) (c : Fˣ), (¬ ∃ μ : Fˣ, μ ^ p = c) →
    ((M⁻¹ * g * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = companionMat p (c : F) → RichCent H g

theorem innDiag_core [Finite F] (hp : p.Prime) (hp2 : p ≠ 2) (hQodd : Odd (Nat.card F))
    {H Γ : Subgroup (GL (Fin p) F)} (hHΓ : H ≤ Γ) (hH1 : CentScalar H Γ)
    (hRD : RichD H Γ) (hRS : RichS H Γ)
    {Y : Type} [Group Y] [Finite Y] (hY : CFSG.Open.IsQuasisimple Y) (hYO : GLAPPrimeCore p Y = ⊥)
    (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj H) {A : Subgroup (MulAut Y)}
    (hAel : IsElemAbelian p A) (hAc : Nat.card A = p ^ 2) (hIm : IsImageOfNonabelianP p H Γ θ A)
    {W : Subgroup (MulAut Y)} (hWD : W ≤ innDiag H Γ θ) (hW2 : IsPGroup 2 W)
    (hAW : A ≤ Subgroup.normalizer (W : Set (MulAut Y)))
    (hJW : ∀ α ∈ A, α ≠ 1 → ∀ y ∈ GLAPPrimeCoreOf p (fixSub α),
      MulAut.conj y ∈ Subgroup.normalizer (W : Set (MulAut Y))) : W = ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsPerfect Y := ⟨hY.1⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Finite (MulAut Y) :=
    Finite.of_injective (fun β : MulAut Y => (β : Y → Y)) fun _ _ h => MulEquiv.ext (congrFun h)
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hZ := isPGroup_center hp hYO
  have hcop2 : ∀ k : ℕ, Nat.Coprime p (2 ^ k) := fun k =>
    Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  obtain ⟨x₁, y₁, ex₁, ey₁, w₁, c₁, l₁, hx₁Γ, hy₁Γ, hex₁A, hey₁A, hgex₁, hgey₁, hw₁, hx₁p, hy₁p,
    hy₁x₁⟩ := exists_heis_pair hp hp2 hH1 hAel hIm
  obtain ⟨M₁, δ₁, hδ₁, hM₁y, hM₁x⟩ := exists_normal_form hp hw₁ hx₁p hy₁p hy₁x₁
  have hinj₁ := inj_of_prim hw₁ hδ₁
  obtain ⟨P, hPΓ, -, -, hAP, -⟩ := hIm
  have hmat : ∀ a ∈ A, ∃ g ∈ Γ, ActsAsConj H θ g a := fun a ha => by
    obtain ⟨g, hg, hga⟩ := hAP a ha
    exact ⟨g, hPΓ hg, hga⟩
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAel.1.is_comm.comm (⟨a, ha⟩ : ↥A) ⟨b, hb⟩)
  have hnsc : ∀ (a : MulAut Y) (g : GL (Fin p) F), a ≠ 1 → ActsAsConj H θ g a →
      ∀ b : Fˣ, g ≠ Matrix.GeneralLinearGroup.scalar (Fin p) b := by
    intro a g ha hga b hb
    rw [hb] at hga
    exact ha (actsAsConj_eq hga (actsAsConj_scalar θ b))
  have hrichY : (∀ u v : GL (Fin p) F, u * y₁ = y₁ * u → v * y₁ = y₁ * v → u * v = v * u) ∧
      RichCent H y₁ := ⟨comm_of_diag hinj₁ hM₁y, hRD y₁ hy₁Γ M₁ δ₁ w₁ hδ₁ hw₁ hM₁y⟩
  have hrichX : (∀ u v : GL (Fin p) F, u * x₁ = x₁ * u → v * x₁ = x₁ * v → u * v = v * u) ∧
      RichCent H x₁ := by
    by_cases hc₁ : ∃ μ : Fˣ, μ ^ p = c₁
    · obtain ⟨μ, hμ⟩ := hc₁
      have hw₁' : IsPrimitiveRoot ((w₁⁻¹ : Fˣ) : F) p :=
        IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.coe_units_iff.1 hw₁).inv
      have hrel : x₁ * y₁ = Matrix.GeneralLinearGroup.scalar (Fin p) w₁⁻¹ * (y₁ * x₁) := by
        rw [hy₁x₁, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
      obtain ⟨M', δ', hδ', hM'x, -⟩ :=
        exists_normal_form hp hw₁' (c := l₁ ^ p) hy₁p (by rw [hx₁p, hμ]) hrel
      exact ⟨comm_of_diag (inj_of_prim hw₁' hδ') hM'x,
        hRD x₁ hx₁Γ M' δ' w₁⁻¹ hδ' hw₁' hM'x⟩
    · exact ⟨comm_of_companion hM₁x, hRS x₁ hx₁Γ M₁ c₁ hc₁ hM₁x⟩
  by_contra hW1
  obtain ⟨α, hαA, hα1, w₀, hw₀W, hw₀1, hw₀α⟩ :=
    exists_centralizer_ne_bot hp hp2 hAel hAc hW2 hAW hW1
  obtain ⟨gα, hgαΓ, hgα⟩ := hmat α hαA
  have hgαp := actsAsConj_pow hgα p
  rw [hAel.2 α hαA] at hgαp
  obtain ⟨ν, hν⟩ := actsAsConj_one_scalar hH1 (Γ.pow_mem hgαΓ p) hgαp
  obtain ⟨ky, hky⟩ := actsAsConj_comm hH1 hgαΓ hy₁Γ hgα hgey₁ (hAcomm α hαA ey₁ hey₁A)
  obtain ⟨kx, hkx⟩ := actsAsConj_comm hH1 hgαΓ hx₁Γ hgα hgex₁ (hAcomm α hαA ex₁ hex₁A)
  have hkyp := pow_eq_one_of_comm_scalar hky
  have hkxp := pow_eq_one_of_comm_scalar hkx
  have hD : ∃ l : Fˣ, l ^ p = ν := by
    by_contra hS
    have hky1 : ky ≠ 1 := by
      rintro rfl
      rw [map_one, one_mul] at hky
      exact hS (exists_pow_eq_of_comm_diag (NeZero.pos p) hinj₁ hM₁y hky.symm hν)
    obtain ⟨M, δ, hδ, -, hMg⟩ :=
      exists_normal_form hp (isPrimitiveRoot_of_pow hp hkyp hky1) hν hy₁p hky
    obtain ⟨g₀, hg₀Γ, hg₀⟩ := hWD hw₀W
    obtain ⟨k, hk⟩ := hW2 ⟨w₀, hw₀W⟩
    have hw₀k : w₀ ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hg₀α := comm_of_actsAsConj hp hH1 hg₀Γ hgαΓ hg₀ hgα hw₀α (hcop2 k) hw₀k
    have hg₀k := actsAsConj_pow hg₀ (2 ^ k)
    rw [hw₀k] at hg₀k
    obtain ⟨a, ha⟩ := actsAsConj_one_scalar hH1 (Γ.pow_mem hg₀Γ _) hg₀k
    obtain ⟨b, hb⟩ := eq_scalar_of_two_comm_companion hp hQodd hpodd hS hMg hg₀α ha
    exact hnsc w₀ g₀ hw₀1 hg₀ b hb
  obtain ⟨l, hl⟩ := hD
  obtain ⟨h, eh, hhΓ, hehA, hgeh, u, hu, hrel, ch, hhp, hch, hrich⟩ :
      ∃ (h : GL (Fin p) F) (eh : MulAut Y), h ∈ Γ ∧ eh ∈ A ∧ ActsAsConj H θ h eh ∧
        ∃ u : Fˣ, IsPrimitiveRoot (u : F) p ∧
          gα * h = Matrix.GeneralLinearGroup.scalar (Fin p) u * (h * gα) ∧
          ∃ ch : Fˣ, h ^ p = Matrix.GeneralLinearGroup.scalar (Fin p) ch ∧
            (∀ u v : GL (Fin p) F, u * h = h * u → v * h = h * v → u * v = v * u) ∧
            RichCent H h := by
    by_cases hky1 : ky = 1
    · rw [hky1, map_one, one_mul] at hky
      have hkx1 : kx ≠ 1 := by
        rintro rfl
        rw [map_one, one_mul] at hkx
        obtain ⟨b, hb⟩ := eq_scalar_of_comm_pair hp hinj₁ hM₁y hM₁x hky.symm hkx.symm
        exact hnsc α gα hα1 hgα b hb
      refine ⟨x₁, ex₁, hx₁Γ, hex₁A, hgex₁, kx⁻¹,
        IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.coe_units_iff.1
          (isPrimitiveRoot_of_pow hp hkxp hkx1)).inv, ?_, c₁, hx₁p, hrichX⟩
      rw [hkx, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
    · refine ⟨y₁, ey₁, hy₁Γ, hey₁A, hgey₁, ky⁻¹,
        IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.coe_units_iff.1
          (isPrimitiveRoot_of_pow hp hkyp hky1)).inv, ?_, l₁ ^ p, hy₁p, hrichY⟩
      rw [hky, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  obtain ⟨M, δ₀, hδ₀, hMα, hMh⟩ := exists_normal_form hp hu hhp (by rw [hν, hl]) hrel
  have hinjα := inj_of_prim hu hδ₀
  have heh1 : eh ≠ 1 := by
    intro h1
    rw [h1] at hgeh
    obtain ⟨b, hb⟩ := actsAsConj_one_scalar hH1 hhΓ hgeh
    rw [hb, ← scalar_mul_comm b gα, ← mul_assoc] at hrel
    have h2 : Matrix.GeneralLinearGroup.scalar (Fin p) u * Matrix.GeneralLinearGroup.scalar (Fin p) b =
        1 * Matrix.GeneralLinearGroup.scalar (Fin p) b := by
      rw [one_mul]
      exact (mul_right_cancel hrel).symm
    have h3 : Matrix.GeneralLinearGroup.scalar (Fin p) u = 1 := mul_right_cancel h2
    have h4 : u = 1 := scalar_injective' (m := p) hp.one_lt.le (by rw [h3, map_one])
    exact hu.ne_one hp.one_lt (by rw [h4, Units.val_one])
  have hAn : ∀ e ∈ A, e ∈ Subgroup.normalizer
      ((W ⊓ Subgroup.centralizer {α} : Subgroup (MulAut Y)) : Set (MulAut Y)) := by
    intro e he
    refine mem_normalizer_inf (hAW he) (Subgroup.le_normalizer ?_)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hAcomm e he α hαA
  have hWα : ∀ w ∈ W, w * α = α * w := by
    set S : Subgroup (MulAut Y) := W ⊓ Subgroup.centralizer {α} with hS
    set R : Subgroup (MulAut Y) := W ⊓ Subgroup.normalizer (S : Set (MulAut Y)) with hR
    have hRα := claim_aut hp hH1 hgαΓ hhΓ hgα hgeh hinjα hMα hMh (S := S) (R := R)
      (inf_le_left.trans hWD) (hW2.to_le inf_le_left)
      (fun hS0 => hw₀1 (by
        have : w₀ ∈ S := ⟨hw₀W, Subgroup.mem_centralizer_singleton_iff.2 hw₀α⟩
        rw [hS0] at this
        exact this))
      (fun s hs => Subgroup.mem_centralizer_singleton_iff.1 hs.2)
      (fun s hs => (Subgroup.mem_normalizer_iff.1 (hAn eh hehA) s).1 hs)
      (inf_le_left.trans hWD)
      (fun r hr s hs => (Subgroup.mem_normalizer_iff.1 hr.2 s).1 hs)
      (fun r hr => ⟨(Subgroup.mem_normalizer_iff.1 (hAW hehA) r).1 hr.1,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (hAn eh hehA) hr.2) (Subgroup.inv_mem _ (hAn eh hehA))⟩)
      (fun r hr => ⟨by
          have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ (hAW hehA)) r).1 hr.1
          simpa using h1,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hAn eh hehA)) hr.2)
          (hAn eh hehA)⟩)
      (fun r hr => by
        obtain ⟨k, hk⟩ := hW2 ⟨r, hr.1⟩
        exact ⟨2 ^ k, hcop2 k, by simpa using congrArg Subtype.val hk⟩) hp2
    have hSW : S = W := eq_of_normalizer_le hW2 inf_le_left (fun w hw hwN =>
      ⟨hw, Subgroup.mem_centralizer_singleton_iff.2 (hRα w ⟨hw, hwN⟩)⟩)
    intro w hw
    rw [← hSW] at hw
    exact Subgroup.mem_centralizer_singleton_iff.1 hw.2
  obtain ⟨m, hm, u₀, hu₀H, hu₀h, hu₀m, hu₀nsc⟩ := hrich
  obtain ⟨X₀, hX₀core, -, hX₀lift, hX₀inv⟩ := exists_lift_centPow hp hZ θ hgeh hm hch
  obtain ⟨x₀, hx₀X₀, hx₀u⟩ := hX₀lift ⟨u₀, hu₀H⟩ hu₀h hu₀m
  set C := GLAPPrimeCoreOf p (fixSub eh) with hCdef
  have hCcop : Nat.Coprime p (Nat.card C) :=
    CFSG.HardMathSupport.Timmesfeld.Proving.coprime_card_GLAPPrimeCoreOf hp (fixSub eh)
  have hCpow : ∀ y ∈ X₀, y ^ Nat.card C = 1 := by
    intro y hy
    have h1 := congrArg (fun z : C => (z : Y)) (pow_card_eq_one' (x := (⟨y, hX₀core hy⟩ : C)))
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1
    exact h1
  have hRα := claim_aut hp hH1 hgαΓ hhΓ hgα hgeh hinjα hMα hMh (S := W)
    (R := X₀.map (MulAut.conj : Y →* MulAut Y)) hWD hW2 hW1 hWα
    (fun s hs => (Subgroup.mem_normalizer_iff.1 (hAW hehA) s).1 hs)
    (by
      rintro _ ⟨y, -, rfl⟩
      exact conj_mem_innDiag hHΓ θ y)
    (by
      rintro _ ⟨y, hy, rfl⟩ s hs
      exact (Subgroup.mem_normalizer_iff.1 (hJW eh hehA heh1 y (hX₀core hy)) s).1 hs)
    (by
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨eh y, hX₀inv eh h hgeh ⟨1, by simp⟩ y hy, ?_⟩
      exact (mulAut_conj_conj eh y).symm)
    (by
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨eh⁻¹ y, hX₀inv eh⁻¹ h⁻¹ (ActsAsConj.inv hgeh) ⟨1, by simp⟩ y hy, ?_⟩
      have := mulAut_conj_conj eh⁻¹ y
      rw [inv_inv] at this
      exact this.symm)
    (by
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨Nat.card C, hCcop, by rw [← map_pow, hCpow y hy, map_one]⟩) hp2
  have hr₀α : MulAut.conj x₀ * α = α * MulAut.conj x₀ := hRα _ ⟨x₀, hx₀X₀, rfl⟩
  have hr₀eh : MulAut.conj x₀ * eh = eh * MulAut.conj x₀ := by
    have hfix : eh x₀ = x₀ := CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_le
      (fixSub eh) (hX₀core hx₀X₀)
    have := mulAut_conj_conj eh x₀
    rw [hfix] at this
    calc MulAut.conj x₀ * eh = eh * MulAut.conj x₀ * eh⁻¹ * eh := by rw [this]
      _ = eh * MulAut.conj x₀ := by group
  obtain ⟨y₀, hy₀Γ, hy₀⟩ := conj_mem_innDiag hHΓ θ x₀
  have hr₀m : MulAut.conj x₀ ^ Nat.card C = 1 := by rw [← map_pow, hCpow x₀ hx₀X₀, map_one]
  have hy₀α := comm_of_actsAsConj hp hH1 hy₀Γ hgαΓ hy₀ hgα hr₀α hCcop hr₀m
  obtain ⟨kh, hkh⟩ := actsAsConj_comm hH1 hhΓ hy₀Γ hgeh hy₀ hr₀eh.symm
  have hkhp := pow_eq_one_of_comm_scalar hkh
  have hy₀ph : y₀ ^ p * h = h * y₀ ^ p := by
    have hz : ∀ k : GL (Fin p) F, Matrix.GeneralLinearGroup.scalar (Fin p) kh * k =
        k * Matrix.GeneralLinearGroup.scalar (Fin p) kh := fun k => scalar_mul_comm kh k
    have h1 := CFSG.LieType.SeitzGeneration.sgo_pow_left_comm hz hkh p
    rw [← map_pow, hkhp, map_one, one_mul] at h1
    exact h1
  have hy₀pα : y₀ ^ p * gα = gα * y₀ ^ p := (Commute.pow_left hy₀α p).eq
  obtain ⟨b, hb⟩ := eq_scalar_of_comm_pair hp hinjα hMα hMh hy₀pα hy₀ph
  have hr₀p : MulAut.conj x₀ ^ p = 1 := by
    have h1 := actsAsConj_pow hy₀ p
    rw [hb] at h1
    exact actsAsConj_eq h1 (actsAsConj_scalar θ b)
  have hr₀ : MulAut.conj x₀ = 1 := eq_one_of_pow_coprime hCcop hr₀m (k := 1) (by rwa [pow_one])
  have hx₀Z : x₀ ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro z
    have := congrArg (fun e : MulAut Y => e z) hr₀
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc z * x₀ = x₀ * z * x₀⁻¹ * x₀ := by rw [this]
      _ = x₀ * z := by group
  have hmk : (QuotientGroup.mk (⟨u₀, hu₀H⟩ : H) : StatedProj H) = 1 := by
    rw [← hx₀u, ← MonoidHom.mem_ker, ker_projY]
    exact hx₀Z
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hmk
  obtain ⟨b', hb'⟩ := hmk
  exact hu₀nsc b' hb'.symm

end InnDiagCore

section Assembly

open Matrix

variable {F : Type} [Field F] {p : ℕ}

theorem neg_one_ne_one_of_odd [Finite F] (hQ : Odd (Nat.card F)) : (-1 : F) ≠ 1 := by
  classical
  haveI := Fintype.ofFinite F
  apply Ring.neg_one_ne_one_of_char_ne_two
  intro h
  have h1 := FiniteField.even_card_iff_char_two.1 h
  rw [← Nat.card_eq_fintype_card] at h1
  rw [Nat.odd_iff] at hQ
  omega

theorem richD_SL [Finite F] (hp : p.Prime) (hp2 : p ≠ 2) (hQ : Odd (Nat.card F)) :
    RichD (StatedSL p F) ⊤ := by
  intro g _ M δ₀ w _ _ hg
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hev : Even (p - 1) := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    exact ⟨k, by omega⟩
  have hlast : ((-1 : Fˣ)⁻¹) ^ (p - 1) = 1 := by rw [inv_neg_one, hev.neg_one_pow]
  set Du : Fin p → Fˣ := fun i => if (i : ℕ) = p - 1 then ((-1 : Fˣ)⁻¹) ^ (p - 1) else -1 with hDu
  set u : GL (Fin p) F := M * TauCeti.diagGL Du * M⁻¹ with hu
  have hMu : ((M⁻¹ * u * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = diagonal (fun i => (Du i : F)) := by
    rw [show M⁻¹ * u * M = TauCeti.diagGL Du by rw [hu]; group, TauCeti.diagGL_coe]
  refine ⟨2, (Nat.coprime_primes hp Nat.prime_two).2 hp2, u, ?_, comm_of_both_diag hMu hg, ?_, ?_⟩
  · rw [CFSG.Open.StatedAPI.mem_statedSL_iff, hu, Units.val_mul, Units.val_mul, Matrix.det_mul,
      Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.det_one, one_mul, TauCeti.diagGL_coe, Matrix.det_diagonal, ← Units.coe_prod, hDu,
      prod_last hp.pos (-1 : Fˣ), Units.val_one]
  · rw [hu, conj_pow, ← map_pow]
    have h1 : Du ^ 2 = 1 := by
      funext i
      simp only [Pi.pow_apply, Pi.one_apply, hDu]
      split_ifs
      · rw [hlast, one_pow]
      · rw [neg_one_sq]
    rw [h1, map_one, mul_one, mul_inv_cancel]
  · intro b hb
    have hp0 := hp.pos
    have h1 : TauCeti.diagGL Du = Matrix.GeneralLinearGroup.scalar (Fin p) b := by
      calc TauCeti.diagGL Du = M⁻¹ * u * M := by rw [hu]; group
        _ = M⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin p) b * M := by rw [hb]
        _ = Matrix.GeneralLinearGroup.scalar (Fin p) b := by
          rw [mul_assoc, Matrix.GeneralLinearGroup.scalar_commute b M, ← mul_assoc, inv_mul_cancel,
            one_mul]
    have h2 := congrArg (fun g : GL (Fin p) F => (g : Matrix (Fin p) (Fin p) F)) h1
    simp only [TauCeti.diagGL_coe, CFSG.LieType.SeitzGeneration.coe_scalarGL] at h2
    have h0 : ((Du ⟨0, hp.pos⟩ : Fˣ) : F) = b := by
      have := congrFun (congrFun h2 ⟨0, hp.pos⟩) ⟨0, hp.pos⟩
      simpa using this
    have hl : ((Du ⟨p - 1, by omega⟩ : Fˣ) : F) = b := by
      have := congrFun (congrFun h2 ⟨p - 1, by omega⟩) ⟨p - 1, by omega⟩
      simpa using this
    have hp1 : (0 : ℕ) ≠ p - 1 := by have := hp.two_le; omega
    simp only [hDu, if_neg hp1, if_pos rfl, hlast, Units.val_neg, Units.val_one] at h0 hl
    exact neg_one_ne_one_of_odd hQ (h0.trans hl.symm)

theorem richS_SL [Finite F] (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F - 1) :
    RichS (StatedSL p F) ⊤ := by
  intro g _ M c hc hg
  obtain ⟨ℓ, hℓ, u, hdet, hug, huℓ, hnsc⟩ := exists_singer_elt hp hp2 hpF hc hg
  exact ⟨ℓ, hℓ, u, CFSG.Open.StatedAPI.mem_statedSL_iff.2 hdet, hug, huℓ, hnsc⟩

end Assembly

section UnitaryCent

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

theorem centScalar_SU {q n : ℕ} (hq : q.Prime) {F : Type} [Field F] [Finite F]
    (hcard : Nat.card F = (q ^ n) ^ 2) {p : ℕ} (hp3 : 3 ≤ p) :
    CentScalar (StatedSU p (q ^ n) F) (GUn p (q ^ n) F) := by
  intro u hu hcomm
  have h := unitaryFieldData_of_card hq hcard
  have hC : IsPrimeFormGram (1 : GL (Fin p) F) := isPrimeFormGram_one
  rw [gUn_eq_primeFormUnitary h] at hu
  have h1 : primeFormConjHom h _ (⟨u, hu⟩ :
      primeFormUnitary h ((1 : GL (Fin p) F) : Matrix (Fin p) (Fin p) F)) = 1 := by
    ext x
    obtain ⟨s', rfl⟩ := QuotientGroup.mk_surjective x
    rw [primeFormConjHom_mk, MulAut.one_apply]
    obtain ⟨c, hc⟩ := hcomm s' (mem_statedSU_of_mem h s')
    have hcU : Matrix.GeneralLinearGroup.scalar (Fin p) c ∈
        primeFormUnitary h ((1 : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) := by
      have e : Matrix.GeneralLinearGroup.scalar (Fin p) c =
          u * (s' : GL (Fin p) F) * u⁻¹ * (s' : GL (Fin p) F)⁻¹ := by
        rw [hc, mul_inv_cancel_right]
      rw [e]
      have hs' : (s' : GL (Fin p) F) ∈ primeFormUnitary h ((1 : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) :=
        ((mem_gramSU_iff_unitary h).1 s'.2).1
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hu hs') (Subgroup.inv_mem _ hu))
        (Subgroup.inv_mem _ hs')
    have hnorm : h.norm (c : F) = 1 := by
      have h2 := (mem_primeFormUnitary).1 hcU
      rw [CFSG.LieType.SeitzGeneration.coe_scalarGL, Units.val_one, Matrix.mul_one,
        Matrix.smul_one_eq_diagonal, Matrix.diagonal_map (map_zero _), diagonal_transpose,
        diagonal_mul_diagonal, ← Matrix.smul_one_eq_diagonal] at h2
      have h3 := congrFun (congrFun h2 ⟨0, by omega⟩) ⟨0, by omega⟩
      simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h3
      rw [UnitaryFieldData.norm, mul_comm]
      exact h3
    have hcp : c ^ p = 1 := by
      have hdet := congrArg Matrix.GeneralLinearGroup.det hc
      rw [map_mul, map_mul, map_mul, map_inv,
        CFSG.RankThree.PartOne.KCLinPlane.det_scalar_gl_units,
        mul_comm (Matrix.GeneralLinearGroup.det u), mul_assoc, mul_inv_cancel, mul_one] at hdet
      exact mul_right_cancel (b := Matrix.GeneralLinearGroup.det (s' : GL (Fin p) F))
        (by rw [one_mul]; exact hdet.symm)
    rw [QuotientGroup.eq]
    refine ⟨c⁻¹, ?_, by rw [inv_pow, hcp, inv_one], ?_⟩
    · rw [Units.val_inv_eq_inv_val, norm_inv_eq h, hnorm, inv_one]
    · show ((⟨_, conj_mem_gramSU h _ hu s'.2⟩ : gramSU h _)⁻¹ * s' : gramSU h _).1 = _
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      show (u * (s' : GL (Fin p) F) * u⁻¹)⁻¹ * (s' : GL (Fin p) F) = _
      rw [hc, _root_.mul_inv_rev, mul_assoc, ← map_inv, scalar_mul_comm c⁻¹, inv_mul_cancel_left]
  have h2 : primeFormPsi h hC ⟨⟨u, hu⟩, 1⟩ = 1 := by
    rw [primeFormPsi_apply, map_one, mul_one, h1]
  obtain ⟨-, c, -, hc⟩ := (primeFormPsi_eq_one_iff h hC hp3 _).1 h2
  exact ⟨c, hc⟩

end UnitaryCent

section Assembly2

@[expose] def UnitaryRich : Prop :=
  ∀ (p q n : ℕ), p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
    ∀ (F : Type) [Field F] [Finite F], Nat.card F = (q ^ n) ^ 2 → p ∣ q ^ n + 1 →
      RichD (StatedSU p (q ^ n) F) (GUn p (q ^ n) F) ∧ RichS (StatedSU p (q ^ n) F) (GUn p (q ^ n) F)

theorem input27_2_innDiag_of_unitaryRich (hU : UnitaryRich) : Input27_2_innDiag := by
  intro p q n hp hp2 hq hq2 hqp Y _ _ hY hYO F _ _ H Γ hD θ A hAel hAc hIm W hWD hW2 hAW hJW
  have hp3 := three_le_of_prime_ne_two hp hp2
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  rcases hD with ⟨rfl, rfl, hcard, hdvd⟩ | ⟨rfl, rfl, hcard, hdvd⟩
  · have hQ : Odd (Nat.card F) := by rw [hcard]; exact hqodd.pow
    exact innDiag_core hp hp2 hQ le_top (centScalar_SL hp3) (richD_SL hp hp2 hQ)
      (richS_SL hp hp2 (by rw [hcard]; exact hdvd)) hY hYO θ hAel hAc hIm hWD hW2 hAW hJW
  · have hQ : Odd (Nat.card F) := by rw [hcard]; exact hqodd.pow.pow
    obtain ⟨h2, h3⟩ := hU p q n hp hp2 hq hq2 hqp F hcard hdvd
    exact innDiag_core hp hp2 hQ (statedSU_le_gUn _ _ _) (centScalar_SU hq hcard hp3) h2 h3 hY hYO θ
      hAel hAc hIm hWD hW2 hAW hJW

end Assembly2

section Gram

variable {q n : ℕ} {F : Type} [Field F] {p : ℕ}

theorem mem_gUn_iff (h : UnitaryFieldData q n F) {g : GL (Fin p) F} :
    g ∈ GUn p (q ^ n) F ↔
      ((g : Matrix (Fin p) (Fin p) F).map h.bar)ᵀ * (g : Matrix (Fin p) (Fin p) F) = 1 := by
  rw [gUn_eq_primeFormUnitary h, mem_primeFormUnitary, Units.val_one, Matrix.mul_one]

theorem mem_statedSU_iff' (h : UnitaryFieldData q n F) {g : GL (Fin p) F} :
    g ∈ StatedSU p (q ^ n) F ↔ g ∈ GUn p (q ^ n) F ∧ (g : Matrix (Fin p) (Fin p) F).det = 1 := by
  rw [← mem_gramSU_iff_mem_statedSU h, mem_gramSU_iff_unitary, gUn_eq_primeFormUnitary h]

theorem gram_conj (h : UnitaryFieldData q n F) {g M X : Matrix (Fin p) (Fin p) F}
    (hg : (g.map h.bar)ᵀ * g = 1) (hgM : g * M = M * X) :
    (X.map h.bar)ᵀ * ((M.map h.bar)ᵀ * M) * X = (M.map h.bar)ᵀ * M := by
  have h1 : ((g * M).map h.bar)ᵀ * (g * M) = (M.map h.bar)ᵀ * M := by
    rw [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (g.map h.bar)ᵀ, hg,
      Matrix.one_mul]
  rw [hgM, Matrix.map_mul, Matrix.transpose_mul] at h1
  calc (X.map h.bar)ᵀ * ((M.map h.bar)ᵀ * M) * X = (X.map h.bar)ᵀ * (M.map h.bar)ᵀ * (M * X) := by
        simp only [Matrix.mul_assoc]
    _ = _ := h1

theorem mul_eq_of_conj {M g : GL (Fin p) F} {X : Matrix (Fin p) (Fin p) F}
    (h : ((M⁻¹ * g * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = X) :
    (g : Matrix (Fin p) (Fin p) F) * (M : Matrix (Fin p) (Fin p) F) =
      (M : Matrix (Fin p) (Fin p) F) * X := by
  rw [← h, ← Units.val_mul, ← Units.val_mul]
  congr 1
  group

theorem gram_mul_inv (h : UnitaryFieldData q n F) (M : GL (Fin p) F) :
    ((M : Matrix (Fin p) (Fin p) F).map h.bar)ᵀ * (M : Matrix (Fin p) (Fin p) F) *
      (((M⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) *
        (((M⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F).map h.bar)ᵀ) = 1 := by
  have h1 : (M : Matrix (Fin p) (Fin p) F) * ((M⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : ((M⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) * (M : Matrix (Fin p) (Fin p) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc ((M : Matrix (Fin p) (Fin p) F).map h.bar)ᵀ * (M : Matrix (Fin p) (Fin p) F) *
        (((M⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) *
          (((M⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F).map h.bar)ᵀ)
      = ((M : Matrix (Fin p) (Fin p) F).map h.bar)ᵀ *
          (((M⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F).map h.bar)ᵀ := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (M : Matrix (Fin p) (Fin p) F), h1, Matrix.one_mul]
    _ = 1 := by
        rw [← Matrix.transpose_mul, ← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _),
          Matrix.transpose_one]

theorem unitary_of_gram (h : UnitaryFieldData q n F) (M : GL (Fin p) F) {X : Matrix (Fin p) (Fin p) F}
    (hX : (X.map h.bar)ᵀ * (((M : Matrix (Fin p) (Fin p) F).map h.bar)ᵀ * (M : Matrix (Fin p) (Fin p) F)) * X =
      ((M : Matrix (Fin p) (Fin p) F).map h.bar)ᵀ * (M : Matrix (Fin p) (Fin p) F)) :
    (((M : Matrix (Fin p) (Fin p) F) * X * ((M⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F)).map h.bar)ᵀ *
      ((M : Matrix (Fin p) (Fin p) F) * X * ((M⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F)) = 1 := by
  set Mm := (M : Matrix (Fin p) (Fin p) F)
  set Mi := ((M⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F)
  have h2 : Mi * Mm = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc ((Mm * X * Mi).map h.bar)ᵀ * (Mm * X * Mi)
      = (Mi.map h.bar)ᵀ * ((X.map h.bar)ᵀ * ((Mm.map h.bar)ᵀ * Mm) * X) * Mi := by
        rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
    _ = (Mi.map h.bar)ᵀ * ((Mm.map h.bar)ᵀ * Mm) * Mi := by rw [hX]
    _ = ((Mm * Mi).map h.bar)ᵀ * (Mm * Mi) := by
        rw [Matrix.map_mul, Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [show Mm * Mi = 1 by rw [← Units.val_mul, mul_inv_cancel, Units.val_one],
          Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul]

end Gram

section RichD

variable {q n : ℕ} {F : Type} [Field F] {p : ℕ}

theorem bar_root (h : UnitaryFieldData q n F) (hpQ : p ∣ q ^ n + 1) {w : Fˣ}
    (hw : (w : F) ^ p = 1) : h.bar (w : F) = (w : F)⁻¹ := by
  rw [UnitaryFieldData.bar_apply]
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ]
  obtain ⟨k, hk⟩ := hpQ
  rw [hk, pow_mul, hw, one_pow]

theorem richD_SU (h : UnitaryFieldData q n F) [Finite F] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpQ : p ∣ q ^ n + 1) (hQ : Odd (Nat.card F)) :
    RichD (StatedSU p (q ^ n) F) (GUn p (q ^ n) F) := by
  classical
  intro g hg M δ₀ w hδ₀ hw hMg
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp0 := hp.pos
  set Q := q ^ n with hQdef
  have hgU := (mem_gUn_iff h).1 hg
  set Mm := (M : Matrix (Fin p) (Fin p) F) with hMm
  set Mi := ((M⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) with hMi
  set δ : Fin p → F := fun k => δ₀ * (w : F) ^ (k : ℕ) with hδ
  have hgM := mul_eq_of_conj hMg
  set G := (Mm.map h.bar)ᵀ * Mm with hG
  have hGinv := gram_mul_inv h M
  have hGc := gram_conj h hgU hgM
  rw [Matrix.diagonal_map (map_zero _), diagonal_transpose] at hGc
  have hGe : ∀ i j, G i j * (h.bar (δ i) * δ j - 1) = 0 := by
    intro i j
    have h1 := congrFun (congrFun hGc i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
    linear_combination h1
  have hwp : (w : F) ^ p = 1 := hw.pow_eq_one
  have hbw := bar_root h hpQ hwp
  have hw0 : (w : F) ≠ 0 := w.ne_zero
  have hN : δ₀ * h.bar δ₀ = 1 := by
    have hGu : IsUnit G := ⟨⟨G, _, hGinv, mul_eq_one_comm.1 hGinv⟩, rfl⟩
    obtain ⟨j, hj⟩ := Inputs272b.exists_ne_zero_row hGu ⟨0, hp0⟩
    have h1 := hGe ⟨0, hp0⟩ j
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 hj
    · have h3 : h.bar δ₀ * δ₀ * (w : F) ^ (j : ℕ) = 1 := by
        have : h.bar (δ ⟨0, hp0⟩) * δ j = 1 := sub_eq_zero.1 h2
        simp only [hδ, pow_zero, mul_one] at this
        linear_combination this
      set n₀ := δ₀ * h.bar δ₀ with hn₀
      have hn₀p : n₀ ^ p = 1 := by
        have h4 : (n₀ * (w : F) ^ (j : ℕ)) ^ p = 1 := by rw [hn₀, mul_comm δ₀, h3, one_pow]
        rwa [mul_pow, ← pow_mul, mul_comm (j : ℕ) p, pow_mul, hwp, one_pow, mul_one] at h4
      have hn₀b : h.bar n₀ = n₀ := by
        rw [hn₀, map_mul, UnitaryFieldData.bar_bar, mul_comm]
      have hn₀0 : n₀ ≠ 0 := by
        intro h0
        rw [h0, zero_pow hp.ne_zero] at hn₀p
        exact zero_ne_one hn₀p
      have hQ1 : 1 ≤ Q := Nat.one_le_pow _ _ h.prime.pos
      have hn₀Q : n₀ ^ (Q - 1) = 1 := by
        have h5 : n₀ ^ Q = n₀ := by rw [← UnitaryFieldData.bar_apply]; exact hn₀b
        have h6 : n₀ ^ (Q - 1) * n₀ = 1 * n₀ := by
          rw [← pow_succ, Nat.sub_add_cancel hQ1, h5, one_mul]
        exact mul_right_cancel₀ hn₀0 h6
      have hcop : Nat.gcd p (Q - 1) = 1 := by
        rw [← Nat.Coprime, Nat.Prime.coprime_iff_not_dvd hp]
        intro hd
        have h7 : p ∣ (Q + 1) - (Q - 1) := Nat.dvd_sub hpQ hd
        rw [show Q + 1 - (Q - 1) = 2 by omega] at h7
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h7)
      have := pow_gcd_eq_one.2 ⟨hn₀p, hn₀Q⟩
      rwa [hcop, pow_one] at this
  have hGd : ∀ i j, i ≠ j → G i j = 0 := by
    intro i j hij
    rcases mul_eq_zero.1 (hGe i j) with h1 | h1
    · exact h1
    · exfalso
      have h2 : h.bar (δ i) * δ j = 1 := sub_eq_zero.1 h1
      simp only [hδ, map_mul, map_pow, hbw] at h2
      have h3 : (w : F) ^ (j : ℕ) = (w : F) ^ (i : ℕ) := by
        have h4 : (h.bar δ₀ * δ₀) * ((w : F)⁻¹ ^ (i : ℕ) * (w : F) ^ (j : ℕ)) = 1 := by
          linear_combination h2
        rw [mul_comm (h.bar δ₀), hN, one_mul, inv_pow] at h4
        have h5 : (w : F) ^ (i : ℕ) ≠ 0 := pow_ne_zero _ hw0
        field_simp at h4
        exact h4
      exact hij (Fin.ext (hw.pow_inj i.2 j.2 h3.symm))
  have hev : Even (p - 1) := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    exact ⟨k, by omega⟩
  have hlast : ((-1 : Fˣ)⁻¹) ^ (p - 1) = 1 := by rw [inv_neg_one, hev.neg_one_pow]
  set Du : Fin p → Fˣ := fun i => if (i : ℕ) = p - 1 then ((-1 : Fˣ)⁻¹) ^ (p - 1) else -1 with hDu
  have hDu2 : ∀ i, (Du i : F) * (Du i : F) = 1 := by
    intro i
    simp only [hDu]
    split_ifs
    · rw [hlast, Units.val_one, one_mul]
    · simp
  have hDub : ∀ i, h.bar (Du i : F) = Du i := by
    intro i
    simp only [hDu]
    split_ifs
    · rw [hlast, Units.val_one, map_one]
    · simp
  set u : GL (Fin p) F := M * TauCeti.diagGL Du * M⁻¹ with hu
  have hMu : ((M⁻¹ * u * M : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) =
      diagonal (fun i => (Du i : F)) := by
    rw [show M⁻¹ * u * M = TauCeti.diagGL Du by rw [hu]; group, TauCeti.diagGL_coe]
  have huM : (u : Matrix (Fin p) (Fin p) F) = Mm * diagonal (fun i => (Du i : F)) * Mi := by
    rw [hu, Units.val_mul, Units.val_mul, TauCeti.diagGL_coe]
  have huU : u ∈ GUn p (q ^ n) F := by
    rw [mem_gUn_iff h, huM]
    apply unitary_of_gram h M
    rw [Matrix.diagonal_map (map_zero _), diagonal_transpose]
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hij : i = j
    · subst hij
      rw [hDub, mul_comm, ← mul_assoc, hDu2, one_mul]
    · rw [← hG, hGd i j hij, mul_zero, zero_mul]
  refine ⟨2, (Nat.coprime_primes hp Nat.prime_two).2 hp2, u, ?_, comm_of_both_diag hMu hMg, ?_, ?_⟩
  · refine (mem_statedSU_iff' h).2 ⟨huU, ?_⟩
    rw [hu, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_right_comm,
      ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, one_mul,
      TauCeti.diagGL_coe, Matrix.det_diagonal, ← Units.coe_prod, hDu,
      Inputs272b.prod_last hp.pos (-1 : Fˣ), Units.val_one]
  · rw [hu, conj_pow, ← map_pow]
    have h1 : Du ^ 2 = 1 := by
      funext i
      simp only [Pi.pow_apply, Pi.one_apply, hDu]
      split_ifs
      · rw [hlast, one_pow]
      · rw [neg_one_sq]
    rw [h1, map_one, mul_one, mul_inv_cancel]
  · intro b hb
    have h1 : TauCeti.diagGL Du = Matrix.GeneralLinearGroup.scalar (Fin p) b := by
      calc TauCeti.diagGL Du = M⁻¹ * u * M := by rw [hu]; group
        _ = M⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin p) b * M := by rw [hb]
        _ = Matrix.GeneralLinearGroup.scalar (Fin p) b := by
          rw [mul_assoc, Matrix.GeneralLinearGroup.scalar_commute b M, ← mul_assoc, inv_mul_cancel,
            one_mul]
    have h2 := congrArg (fun g : GL (Fin p) F => (g : Matrix (Fin p) (Fin p) F)) h1
    simp only [TauCeti.diagGL_coe, CFSG.LieType.SeitzGeneration.coe_scalarGL] at h2
    have h0 : ((Du ⟨0, hp0⟩ : Fˣ) : F) = b := by
      have := congrFun (congrFun h2 ⟨0, hp0⟩) ⟨0, hp0⟩
      simpa using this
    have hl : ((Du ⟨p - 1, by omega⟩ : Fˣ) : F) = b := by
      have := congrFun (congrFun h2 ⟨p - 1, by omega⟩) ⟨p - 1, by omega⟩
      simpa using this
    have hp1 : (0 : ℕ) ≠ p - 1 := by have := hp.two_le; omega
    simp only [hDu, if_neg hp1, if_pos rfl, hlast, Units.val_neg, Units.val_one] at h0 hl
    exact neg_one_ne_one_of_odd hQ (h0.trans hl.symm)

end RichD

section RichS

theorem geom_intModEq {x y m : ℤ} (hxy : x ≡ y [ZMOD m]) (k : ℕ) :
    ∑ i ∈ Finset.range k, x ^ i ≡ ∑ i ∈ Finset.range k, y ^ i [ZMOD m] := by
  induction k with
  | zero => simp [Int.ModEq.refl]
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    exact ih.add (hxy.pow k)

theorem sum_neg_one_pow_odd {p : ℕ} (hp : Odd p) : ∑ i ∈ Finset.range p, (-1 : ℤ) ^ i = 1 := by
  obtain ⟨m, rfl⟩ := hp
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih]
    have h1 : (-1 : ℤ) ^ (2 * m + 1) = -1 := Odd.neg_one_pow ⟨m, rfl⟩
    have h2 : (-1 : ℤ) ^ (2 * m + 1 + 1) = 1 := Even.neg_one_pow ⟨m + 1, by ring⟩
    rw [h1, h2]
    ring

theorem pow_ge_mul {Q : ℕ} (hQ : 3 ≤ Q) {p : ℕ} (hp : 3 ≤ p) : (Q + 1) * p ≤ Q ^ p := by
  induction p, hp using Nat.le_induction with
  | base => nlinarith [sq_nonneg Q]
  | succ k hk ih =>
    rw [pow_succ]
    have h1 := Nat.mul_le_mul_right Q ih
    have h2 : k + 1 ≤ k * Q := by nlinarith
    have h3 : (Q + 1) * (k + 1) ≤ (Q + 1) * (k * Q) := Nat.mul_le_mul_left _ h2
    have h4 : (Q + 1) * k * Q = (Q + 1) * (k * Q) := by ring
    omega

theorem exists_prime_dvd_geomU {Q p : ℕ} (hQ3 : 3 ≤ Q) (hp : p.Prime) (hp2 : p ≠ 2) (hpQ : p ∣ Q + 1) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ p ∧ ℓ ∣ Q ^ p + 1 ∧ ¬ ℓ ∣ Q + 1 ∧ ¬ ℓ ∣ Q - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 := three_le_of_prime_ne_two hp hp2
  obtain ⟨N, hN⟩ : Q + 1 ∣ Q ^ p + 1 := by
    have := Odd.nat_add_dvd_pow_add_pow Q 1 hpodd
    rwa [one_pow] at this
  have hNS : (N : ℤ) = ∑ i ∈ Finset.range p, (-(Q : ℤ)) ^ i := by
    have h1 : (∑ i ∈ Finset.range p, (-(Q : ℤ)) ^ i) * (-(Q : ℤ) - 1) = (-(Q : ℤ)) ^ p - 1 :=
      geom_sum_mul _ _
    rw [hpodd.neg_pow] at h1
    have h2 : ((Q : ℤ) + 1) * N = (Q : ℤ) ^ p + 1 := by exact_mod_cast hN.symm
    have h3 : ((Q : ℤ) + 1) * (∑ i ∈ Finset.range p, (-(Q : ℤ)) ^ i) = (Q : ℤ) ^ p + 1 := by
      linear_combination -h1
    have hQ0 : ((Q : ℤ) + 1) ≠ 0 := by positivity
    exact mul_left_cancel₀ hQ0 (h2.trans h3.symm)
  have hcong1 : ∀ ℓ : ℕ, ℓ ∣ Q + 1 → (N : ℤ) ≡ p [ZMOD ℓ] := by
    intro ℓ hℓ
    have h1 : -(Q : ℤ) ≡ 1 [ZMOD ℓ] := by
      apply Int.ModEq.symm
      rw [Int.modEq_iff_dvd]
      have : (ℓ : ℤ) ∣ (Q : ℤ) + 1 := by exact_mod_cast hℓ
      rw [show -(Q : ℤ) - 1 = -((Q : ℤ) + 1) by ring]
      exact Int.dvd_neg.2 this
    rw [hNS]
    have h2 := geom_intModEq h1 p
    simpa using h2
  have hcong2 : ∀ ℓ : ℕ, ℓ ∣ Q - 1 → (N : ℤ) ≡ 1 [ZMOD ℓ] := by
    intro ℓ hℓ
    have h1 : -(Q : ℤ) ≡ -1 [ZMOD ℓ] := by
      apply Int.ModEq.neg
      apply Int.ModEq.symm
      rw [Int.modEq_iff_dvd]
      have : (ℓ : ℤ) ∣ ((Q - 1 : ℕ) : ℤ) := by exact_mod_cast hℓ
      rw [Nat.cast_sub (by omega), Nat.cast_one] at this
      exact this
    rw [hNS]
    have h2 := geom_intModEq h1 p
    rwa [sum_neg_one_pow_odd hpodd] at h2
  have hpQ' : ¬ p ∣ Q := by
    intro h
    have h1 : p ∣ Q + 1 - Q := Nat.dvd_sub hpQ h
    rw [show Q + 1 - Q = 1 by omega] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hlte := padicValNat.pow_add_pow (p := p) hpodd (x := Q) (y := 1) hpQ hpQ' hpodd
  rw [one_pow, padicValNat_self, hN] at hlte
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hN
    omega
  rw [padicValNat.mul (by omega) hN0] at hlte
  have hvN : padicValNat p N = 1 := by omega
  have hp2N : ¬ p ^ 2 ∣ N := by
    intro h
    have := (padicValNat_dvd_iff_le hN0).1 h
    omega
  have hNgt : p < N := by
    have h1 := pow_ge_mul hQ3 hp3
    by_contra h2
    push Not at h2
    have h3 : (Q + 1) * N ≤ (Q + 1) * p := Nat.mul_le_mul_left _ h2
    omega
  have hpN : p ∣ N := by
    have h1 := hcong1 p hpQ
    have h2 : (p : ℤ) ∣ (N : ℤ) := by
      have := h1.symm.dvd
      simpa using this
    exact_mod_cast h2
  obtain ⟨r, hr⟩ := hpN
  have hr1 : r ≠ 1 := by
    rintro rfl
    rw [mul_one] at hr
    omega
  have hpr : ¬ p ∣ r := by
    rintro ⟨t, rfl⟩
    exact hp2N ⟨t, by rw [hr]; ring⟩
  set ℓ := r.minFac with hℓ
  have hℓp : ℓ.Prime := Nat.minFac_prime hr1
  have hℓr : ℓ ∣ r := Nat.minFac_dvd r
  have hℓN : ℓ ∣ N := hr ▸ Dvd.dvd.mul_left hℓr p
  refine ⟨ℓ, hℓp, fun h => hpr (h ▸ hℓr), ?_, fun hℓQ => ?_, fun hℓQ => ?_⟩
  · rw [hN]
    exact Dvd.dvd.mul_left hℓN _
  · have h1 := hcong1 ℓ hℓQ
    have h2 : (ℓ : ℤ) ∣ (p : ℤ) := by
      have h3 : (ℓ : ℤ) ∣ (N : ℤ) := by exact_mod_cast hℓN
      have h4 := h1.dvd
      have h5 : (ℓ : ℤ) ∣ (p : ℤ) - N + N := dvd_add h4 h3
      simpa using h5
    have h3 : ℓ ∣ p := by exact_mod_cast h2
    exact hpr ((Nat.prime_dvd_prime_iff_eq hℓp hp).1 h3 ▸ hℓr)
  · have h1 := hcong2 ℓ hℓQ
    have h2 : (ℓ : ℤ) ∣ 1 := by
      have h3 : (ℓ : ℤ) ∣ (N : ℤ) := by exact_mod_cast hℓN
      have h4 := h1.dvd
      have h5 : (ℓ : ℤ) ∣ 1 - N + N := dvd_add h4 h3
      simpa using h5
    have h3 : ℓ ∣ 1 := by exact_mod_cast h2
    exact hℓp.one_lt.ne' (Nat.dvd_one.1 h3)

variable {q n : ℕ} {F : Type} [Field F] {p : ℕ}

theorem richS_SU (h : UnitaryFieldData q n F) [Finite F] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpQ : p ∣ q ^ n + 1) (hQ3 : 3 ≤ q ^ n) :
    RichS (StatedSU p (q ^ n) F) (GUn p (q ^ n) F) := by
  classical
  intro g hg M c hc hMg
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨E, _, _, _, φ, hφ, hcard, hrange, hcomm⟩ := singer_setup hp hc
  set Q := q ^ n with hQdef
  have hFcard : Nat.card F = Q ^ 2 := by rw [h.card, hQdef, ← pow_mul, mul_comm]
  have hgU := (mem_gUn_iff h).1 hg
  set Mm := (M : Matrix (Fin p) (Fin p) F) with hMm
  set Mi := ((M⁻¹ : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) with hMi
  have hMMi : Mm * Mi = 1 := by rw [hMm, hMi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hMiM : Mi * Mm = 1 := by rw [hMm, hMi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  set G := (g : Matrix (Fin p) (Fin p) F) with hGdef
  have hMC : Mi * G * Mm = companionMat p (c : F) := by
    rw [← hMg, Units.val_mul, Units.val_mul]
  set adj : Matrix (Fin p) (Fin p) F → Matrix (Fin p) (Fin p) F := fun Y => (Y.map h.bar)ᵀ with hadj
  have adj_mul : ∀ Y Z, adj (Y * Z) = adj Z * adj Y := fun Y Z => by
    simp only [hadj, Matrix.map_mul, Matrix.transpose_mul]
  have adj_add : ∀ Y Z, adj (Y + Z) = adj Y + adj Z := fun Y Z => by
    simp only [hadj]
    rw [Matrix.map_add _ (map_add h.bar), Matrix.transpose_add]
  have adj_adj : ∀ Y, adj (adj Y) = Y := fun Y => by
    simp only [hadj]
    ext i j
    simp [Matrix.transpose_apply, UnitaryFieldData.bar_bar]
  have adj_smul_one : ∀ a : F, adj (a • 1) = h.bar a • 1 := fun a => by
    simp only [hadj]
    rw [Matrix.smul_one_eq_diagonal, Matrix.diagonal_map (map_zero _), diagonal_transpose,
      ← Matrix.smul_one_eq_diagonal]
  have adj_one : adj 1 = 1 := by
    simp only [hadj]
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  have hgg : adj G * G = 1 := hgU
  have hgg' : G * adj G = 1 := mul_eq_one_comm.1 hgg
  set φ' : E → Matrix (Fin p) (Fin p) F := fun e => Mm * φ e * Mi with hφ'
  have hφ'g : ∀ e, φ' e * G = G * φ' e := by
    intro e
    have h1 := hcomm e
    rw [← hMC] at h1
    calc φ' e * G = Mm * (φ e * (Mi * G * Mm)) * Mi := by
          simp only [hφ', Matrix.mul_assoc]
          rw [hMMi, Matrix.mul_one]
      _ = Mm * ((Mi * G * Mm) * φ e) * Mi := by rw [h1]
      _ = G * φ' e := by
          simp only [hφ', Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Mm Mi, hMMi, Matrix.one_mul]
  have hφ'r : ∀ Y, Y * G = G * Y → ∃ e, φ' e = Y := by
    intro Y hY
    have h1 : (Mi * Y * Mm) * companionMat p (c : F) = companionMat p (c : F) * (Mi * Y * Mm) := by
      rw [← hMC]
      calc Mi * Y * Mm * (Mi * G * Mm) = Mi * (Y * G) * Mm := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc Mm Mi, hMMi, Matrix.one_mul]
        _ = Mi * (G * Y) * Mm := by rw [hY]
        _ = Mi * G * Mm * (Mi * Y * Mm) := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc Mm Mi, hMMi, Matrix.one_mul]
    obtain ⟨e, he⟩ := hrange _ h1
    refine ⟨e, ?_⟩
    simp only [hφ']
    rw [he]
    simp only [← Matrix.mul_assoc]
    rw [hMMi, Matrix.one_mul, Matrix.mul_assoc, hMMi, Matrix.mul_one]
  have hφ'inj : ∀ e e', φ' e = φ' e' → e = e' := by
    intro e e' hee
    apply hφ
    have e1 : ∀ X, Mi * (Mm * X * Mi) * Mm = X := fun X => by
      rw [← Matrix.mul_assoc Mi, ← Matrix.mul_assoc Mi, hMiM, Matrix.one_mul, Matrix.mul_assoc, hMiM,
        Matrix.mul_one]
    have h1 : Mi * (Mm * φ e * Mi) * Mm = Mi * (Mm * φ e' * Mi) * Mm := by
      have : Mm * φ e * Mi = Mm * φ e' * Mi := hee
      rw [this]
    rw [e1, e1] at h1
    exact h1
  have hφ'mul : ∀ e e', φ' (e * e') = φ' e * φ' e' := by
    intro e e'
    simp only [hφ', map_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Mi Mm, hMiM, Matrix.one_mul]
  have hφ'add : ∀ e e', φ' (e + e') = φ' e + φ' e' := by
    intro e e'
    simp only [hφ', map_add, Matrix.mul_add, Matrix.add_mul]
  have hφ'alg : ∀ a : F, φ' (algebraMap F E a) = a • 1 := by
    intro a
    show Mm * φ (algebraMap F E a) * Mi = a • 1
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hMMi]
  have hφ'one : φ' 1 = 1 := by
    have := hφ'alg 1
    rwa [map_one, one_smul] at this
  have hadjg : ∀ e, adj (φ' e) * G = G * adj (φ' e) := by
    intro e
    have h1 : adj G * adj (φ' e) = adj (φ' e) * adj G := by
      rw [← adj_mul, ← adj_mul, hφ'g e]
    calc adj (φ' e) * G = G * (adj G * adj (φ' e)) * G := by
          rw [← Matrix.mul_assoc, hgg', Matrix.one_mul]
      _ = G * (adj (φ' e) * adj G) * G := by rw [h1]
      _ = G * adj (φ' e) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, hgg, Matrix.mul_one]
  choose ψ hψ using fun e => hφ'r _ (hadjg e)
  have hψmul : ∀ e e', ψ (e * e') = ψ e * ψ e' := by
    intro e e'
    apply hφ'inj
    rw [hψ, hφ'mul, adj_mul, ← hψ, ← hψ, ← hφ'mul, mul_comm]
  have hψadd : ∀ e e', ψ (e + e') = ψ e + ψ e' := by
    intro e e'
    apply hφ'inj
    rw [hψ, hφ'add, adj_add, ← hψ, ← hψ, ← hφ'add]
  have hψψ : ∀ e, ψ (ψ e) = e := by
    intro e
    apply hφ'inj
    rw [hψ, hψ, adj_adj]
  have hψalg : ∀ a : F, ψ (algebraMap F E a) = algebraMap F E (h.bar a) := by
    intro a
    apply hφ'inj
    rw [hψ, hφ'alg, adj_smul_one, hφ'alg]
  let σ : E ≃+* E :=
    { toFun := ψ, invFun := ψ, left_inv := hψψ, right_inv := hψψ, map_mul' := hψmul,
      map_add' := hψadd }
  have hσσ : σ * σ = 1 := RingEquiv.ext fun e => hψψ e
  have hσ1 : σ ≠ 1 := by
    intro h1
    obtain ⟨a, ha⟩ := h.exists_bar_ne
    apply ha
    have h2 : ψ (algebraMap F E a) = algebraMap F E a := by
      have := congrArg (fun τ : E ≃+* E => τ (algebraMap F E a)) h1
      exact this
    rw [hψalg] at h2
    exact (algebraMap F E).injective h2
  have hEcard : Nat.card E = q ^ (2 * (n * p)) := by
    rw [hcard, h.card, ← pow_mul]
    ring_nf
  have h1np : 1 ≤ 2 * (n * p) := by
    have h1 := h.one_le
    have h2 := hp.pos
    nlinarith
  obtain ⟨-, hσpow⟩ := LinearFlag.even_and_eq_pow_of_involution_prime h.prime h1np hEcard hσ1 hσσ
  have hψpow : ∀ e, ψ e = e ^ (Q ^ p) := by
    intro e
    have := hσpow e
    rw [show 2 * (n * p) / 2 = n * p by omega, pow_mul] at this
    exact this
  obtain ⟨ℓ, hℓ, hℓp, hℓdvd, hℓQ1, hℓQ2⟩ := exists_prime_dvd_geomU hQ3 hp hp2 hpQ
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hQp1 : 1 ≤ Q ^ p := Nat.one_le_pow _ _ (by omega)
  have hEu : Nat.card Eˣ = (Q ^ p + 1) * (Q ^ p - 1) := by
    rw [Nat.card_units, hcard, hFcard, ← pow_mul, mul_comm 2 p, pow_mul]
    zify [hQp1, Nat.one_le_pow 2 (Q ^ p) (by omega)]
    ring
  obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' ℓ (hEu ▸ Dvd.dvd.mul_right hℓdvd _)
  have heQ : e ^ (Q ^ p + 1) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, he]
    exact hℓdvd
  let u₀ : GL (Fin p) F :=
    ⟨φ (e : E), φ ((e⁻¹ : Eˣ) : E), by rw [← map_mul, Units.mul_inv, map_one],
      by rw [← map_mul, Units.inv_mul, map_one]⟩
  set u : GL (Fin p) F := M * u₀ * M⁻¹ with hu
  have huφ : (u : Matrix (Fin p) (Fin p) F) = φ' (e : E) := by
    rw [hu, Units.val_mul, Units.val_mul]
  have huU : adj (u : Matrix (Fin p) (Fin p) F) * (u : Matrix (Fin p) (Fin p) F) = 1 := by
    rw [huφ, ← hψ, ← hφ'mul, hψpow, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← pow_succ, heQ,
      Units.val_one, hφ'one]
  have huGU : u ∈ GUn p (q ^ n) F := (mem_gUn_iff h).2 huU
  have hupow : ∀ k : ℕ, ((u ^ k : GL (Fin p) F) : Matrix (Fin p) (Fin p) F) = φ' ((e ^ k : Eˣ) : E) := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, Units.val_one, Units.val_one, hφ'one]
    | succ k ih => rw [pow_succ, Units.val_mul, ih, huφ, ← hφ'mul, ← Units.val_mul, ← pow_succ]
  have huℓ : u ^ ℓ = 1 := by
    apply Units.ext
    rw [hupow, ← he, pow_orderOf_eq_one, Units.val_one, hφ'one, Units.val_one]
  have hdet : (u : Matrix (Fin p) (Fin p) F).det = 1 := by
    set d := (u : Matrix (Fin p) (Fin p) F).det with hd
    have hd0 : d ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 u.isUnit).ne_zero
    have hdℓ : d ^ ℓ = 1 := by
      rw [hd, ← Matrix.det_pow, ← Units.val_pow_eq_pow_val, huℓ, Units.val_one, Matrix.det_one]
    have hdQ : d ^ (Q + 1) = 1 := by
      have h1 := congrArg Matrix.det huU
      rw [Matrix.det_mul, Matrix.det_one] at h1
      simp only [hadj, Matrix.det_transpose] at h1
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, UnitaryFieldData.bar_apply, ← hd] at h1
      rw [pow_succ]
      exact h1
    have hg1 : Nat.gcd ℓ (Q + 1) = 1 :=
      (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓQ1).symm)
    have := pow_gcd_eq_one.2 ⟨hdℓ, hdQ⟩
    rwa [hg1, pow_one] at this
  have hug : u * g = g * u := by
    apply Units.ext
    have e1 := Units.val_mul u g
    have e2 := Units.val_mul g u
    rw [e1, e2, huφ]
    exact hφ'g (e : E)
  refine ⟨ℓ, (Nat.coprime_primes hp hℓ).2 (Ne.symm hℓp), u, (mem_statedSU_iff' h).2 ⟨huGU, hdet⟩,
    hug, huℓ, ?_⟩
  intro b hb
  have h1 : (e : E) = algebraMap F E b := by
    apply hφ'inj
    rw [← huφ, hb, hφ'alg, CFSG.LieType.SeitzGeneration.coe_scalarGL]
  have h2 : e ^ (Q ^ 2 - 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, h1, ← map_pow, ← hFcard, ← Units.val_pow_eq_pow_val,
      ← Nat.card_units, pow_card_eq_one', Units.val_one, map_one, Units.val_one]
  have h3 := orderOf_dvd_of_pow_eq_one h2
  rw [he] at h3
  have hQ1 : 1 ≤ Q := by omega
  have h4 : Q ^ 2 - 1 = (Q + 1) * (Q - 1) := by
    zify [hQ1, Nat.one_le_pow 2 Q (by omega)]
    ring
  rw [h4] at h3
  rcases (Nat.Prime.dvd_mul hℓ).1 h3 with h5 | h5
  · exact hℓQ1 h5
  · exact hℓQ2 h5

end RichS

section Final

theorem unitaryRich_holds : UnitaryRich := by
  intro p q n hp hp2 hq hq2 hqp F _ _ hcard hdvd
  have h := unitaryFieldData_of_card hq hcard
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  have hQ : Odd (Nat.card F) := by rw [hcard]; exact hqodd.pow.pow
  have hQ3 : 3 ≤ q ^ n := by
    have h1 : 1 ≤ n := h.one_le
    have h2 : 3 ≤ q := by
      have := hq.two_le
      rcases Nat.lt_or_ge q 3 with h3 | h3
      · exfalso; exact hq2 (by omega)
      · exact h3
    calc 3 ≤ q := h2
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ n := Nat.pow_le_pow_right hq.pos h1
  exact ⟨richD_SU h hp hp2 hdvd hQ, richS_SU h hp hp2 hdvd hQ3⟩

theorem input27_2_innDiag_holds : Input27_2_innDiag :=
  input27_2_innDiag_of_unitaryRich unitaryRich_holds

theorem input27_2Q_holds : Inputs123b.Input27_2Q :=
  input27_2Q_of_innDiag_outerL input27_2_innDiag_holds input27_2_outerL_holds

end Final

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs272c

end
