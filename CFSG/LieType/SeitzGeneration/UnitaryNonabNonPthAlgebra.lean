module

public import Mathlib.FieldTheory.KummerPolynomial
public import CFSG.LieType.SeitzGeneration.HeisTorusIdent
public import Mathlib.LinearAlgebra.Eigenspace.Basic

public section

namespace CFSG.LieType.SeitzGeneration.NonPth

open Polynomial

variable {K : Type} [Field K] {p : ℕ}

section Basic

variable {V : Type*} [AddCommGroup V] [Module K V]

theorem irreducible_X_pow_sub_C {α : K} (hp : p.Prime) (hc : ¬ ∃ μ : K, μ ^ p = α) :
    Irreducible (X ^ p - C α : K[X]) :=
  X_pow_sub_C_irreducible_of_prime hp fun b hb => hc ⟨b, hb⟩

theorem minpoly_eq_X_pow_sub_C [Nontrivial V] {T : Module.End K V} {α : K} (hp : p.Prime)
    (hT : T ^ p = algebraMap K (Module.End K V) α) (hc : ¬ ∃ μ : K, μ ^ p = α) :
    minpoly K T = X ^ p - C α := by
  symm
  refine minpoly.eq_of_irreducible_of_monic (irreducible_X_pow_sub_C hp hc) ?_
    (monic_X_pow_sub_C _ hp.ne_zero)
  simp [hT]

theorem eq_zero_of_aeval_eq_zero {T : Module.End K V} {α : K} (hp : p.Prime)
    (hT : T ^ p = algebraMap K (Module.End K V) α) (hc : ¬ ∃ μ : K, μ ^ p = α) {v : V}
    (hv : v ≠ 0) {q : K[X]} (hq : q.degree < p) (hqv : aeval T q v = 0) : q = 0 := by
  by_contra hq0
  have hirr := irreducible_X_pow_sub_C hp hc
  have hndvd : ¬ (X ^ p - C α : K[X]) ∣ q := by
    intro hd
    have h1 := Polynomial.degree_le_of_dvd hd hq0
    rw [degree_X_pow_sub_C hp.pos] at h1
    exact absurd hq (not_lt.mpr h1)
  have hcop : IsCoprime (X ^ p - C α : K[X]) q :=
    (Irreducible.coprime_iff_not_dvd hirr).2 hndvd
  obtain ⟨a, b, hab⟩ := hcop
  have h1 := congrArg (fun r : K[X] => aeval T r v) hab
  simp only [map_add, map_mul, map_one, LinearMap.add_apply, Module.End.mul_apply,
    Module.End.one_apply, map_sub, map_pow, aeval_X, aeval_C] at h1
  rw [hqv, hT] at h1
  simp at h1
  exact hv h1.symm

theorem p_le_finrank_of_stable {T : Module.End K V} {α : K} (hp : p.Prime)
    (hT : T ^ p = algebraMap K (Module.End K V) α)
    (hc : ¬ ∃ μ : K, μ ^ p = α) {S : Submodule K V} (hS : ∀ s ∈ S, T s ∈ S) (hne : S ≠ ⊥)
    [Module.Finite K S] : p ≤ Module.finrank K S := by
  obtain ⟨v, hvS, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hpow : ∀ i : ℕ, ∀ s ∈ S, (T ^ i) s ∈ S := by
    intro i
    induction i with
    | zero => intro s hs; simpa using hs
    | succ k ih =>
      intro s hs
      rw [pow_succ', Module.End.mul_apply]
      exact hS _ (ih s hs)
  let b : Fin p → S := fun i => ⟨(T ^ (i : ℕ)) v, hpow _ v hvS⟩
  have hind : LinearIndependent K b := by
    apply LinearIndependent.of_comp S.subtype
    rw [Fintype.linearIndependent_iff]
    intro c hc0 i
    have hsum : ∑ j : Fin p, c j • (T ^ (j : ℕ)) v = 0 := by
      simpa [b] using hc0
    have hq := eq_zero_of_aeval_eq_zero hp hT hc hv0
      (q := ∑ j : Fin p, C (c j) * X ^ (j : ℕ)) (degree_sum_fin_lt _)
      (by simpa [map_sum, map_mul, aeval_C, aeval_X_pow, LinearMap.sum_apply,
        Module.End.mul_apply, Module.algebraMap_end_apply] using hsum)
    have hci := congrArg (fun r : K[X] => r.coeff (i : ℕ)) hq
    simpa [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, Fin.val_inj] using hci
  simpa using hind.fintype_card_le_finrank

end Basic

theorem iSup_eigenspace_eq_top_p {V : Type*} [AddCommGroup V] [Module K V] (hp : p.Prime)
    (hpK : (p : K) ≠ 0) {Y : Module.End K V} {ν ζ : K} (hζ : IsPrimitiveRoot ζ p) (hν : ν ≠ 0)
    (hY : Y ^ p = algebraMap K (Module.End K V) (ν ^ p)) :
    (⨆ j : Fin p, Module.End.eigenspace Y (ν * ζ ^ (j : ℕ))) = ⊤ := by
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hw : IsPrimitiveRoot ζ⁻¹ p := hζ.inv
  obtain ⟨c, hc⟩ : ∃ c : Fin p → K, ∀ j : Fin p, c j = (ν * ζ ^ (j : ℕ))⁻¹ :=
    ⟨_, fun j => rfl⟩
  have hc' : ∀ j : Fin p, c j = ν⁻¹ * ζ⁻¹ ^ (j : ℕ) := by
    intro j
    rw [hc j, mul_inv, inv_pow]
  have hνζ : ∀ j : Fin p, ν * ζ ^ (j : ℕ) * c j = 1 := fun j => by
    rw [hc j, mul_inv_cancel₀ (mul_ne_zero hν (pow_ne_zero _ hζ0))]
  have hcp : ∀ j : Fin p, c j ^ p * ν ^ p = 1 := by
    intro j
    have hζp : (ζ ^ (j : ℕ)) ^ p = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    rw [hc j, inv_pow, mul_pow, hζp, mul_one, inv_mul_cancel₀ (pow_ne_zero p hν)]
  have hgeom : ∀ j : Fin p, (1 - c j • Y) * ∑ i ∈ Finset.range p, (c j • Y) ^ i = 0 := by
    intro j
    have hpow1 : (c j • Y) ^ p = 1 := by
      rw [smul_pow, hY, Algebra.algebraMap_eq_smul_one, smul_smul, hcp j, one_smul]
    rw [mul_neg_geom_sum, hpow1, sub_self]
  have heig : ∀ (j : Fin p) (v : V), Y ((∑ i ∈ Finset.range p, (c j • Y) ^ i) v) =
      (ν * ζ ^ (j : ℕ)) • (∑ i ∈ Finset.range p, (c j • Y) ^ i) v := by
    intro j v
    have h1 := congrArg (fun T : Module.End K V => T v) (hgeom j)
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.smul_apply, LinearMap.zero_apply] at h1
    have h2 : (∑ i ∈ Finset.range p, (c j • Y) ^ i) v =
        c j • Y ((∑ i ∈ Finset.range p, (c j • Y) ^ i) v) := sub_eq_zero.mp h1
    calc Y ((∑ i ∈ Finset.range p, (c j • Y) ^ i) v)
        = (ν * ζ ^ (j : ℕ) * c j) • Y ((∑ i ∈ Finset.range p, (c j • Y) ^ i) v) := by
          rw [hνζ j, one_smul]
      _ = (ν * ζ ^ (j : ℕ)) • (c j • Y ((∑ i ∈ Finset.range p, (c j • Y) ^ i) v)) := by
          rw [mul_smul]
      _ = (ν * ζ ^ (j : ℕ)) • (∑ i ∈ Finset.range p, (c j • Y) ^ i) v := by rw [← h2]
  have hcs : ∀ i ∈ Finset.range p, ∑ j : Fin p, c j ^ i = if i = 0 then (p : K) else 0 := by
    intro i hi
    have hi' : i < p := Finset.mem_range.mp hi
    have hcj : ∀ j : Fin p, c j ^ i = ν⁻¹ ^ i * (ζ⁻¹ ^ i) ^ (j : ℕ) := by
      intro j
      rw [hc' j, mul_pow, ← pow_mul, ← pow_mul, mul_comm (j : ℕ) i]
    rw [Finset.sum_congr rfl (fun j _ => hcj j), ← Finset.mul_sum]
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      simp
    · have hu1 : ζ⁻¹ ^ i ≠ 1 := hw.pow_ne_one_of_pos_of_lt hpos.ne' hi'
      have hup : (ζ⁻¹ ^ i) ^ p = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hw.pow_eq_one, one_pow]
      rw [geom_sum_fin_eq_zero hup hu1, mul_zero, if_neg hpos.ne']
  have hsum : ∀ v : V, ∑ j : Fin p, (∑ i ∈ Finset.range p, (c j • Y) ^ i) v = (p : K) • v := by
    intro v
    have hexp : ∀ j : Fin p, (∑ i ∈ Finset.range p, (c j • Y) ^ i) v =
        ∑ i ∈ Finset.range p, c j ^ i • (Y ^ i) v := by
      intro j
      rw [LinearMap.sum_apply]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_pow, LinearMap.smul_apply]
    have e1 : ∑ j : Fin p, (∑ i ∈ Finset.range p, (c j • Y) ^ i) v =
        ∑ i ∈ Finset.range p, (∑ j : Fin p, c j ^ i) • (Y ^ i) v := by
      simp only [hexp, Finset.sum_smul]
      exact Finset.sum_comm
    have e2 : ∑ i ∈ Finset.range p, (∑ j : Fin p, c j ^ i) • (Y ^ i) v =
        ∑ i ∈ Finset.range p, (if i = 0 then (p : K) else 0) • (Y ^ i) v :=
      Finset.sum_congr rfl fun i hi => by rw [hcs i hi]
    rw [e1, e2, Finset.sum_eq_single 0]
    · simp
    · intro i _ hi0
      simp [hi0]
    · intro h0
      exact absurd (Finset.mem_range.mpr hp.pos) h0
  rw [eq_top_iff]
  intro v _
  have hmem : ∑ j : Fin p, (p : K)⁻¹ • (∑ i ∈ Finset.range p, (c j • Y) ^ i) v ∈
      ⨆ j : Fin p, Module.End.eigenspace Y (ν * ζ ^ (j : ℕ)) := by
    refine Submodule.sum_mem _ fun j _ => Submodule.mem_iSup_of_mem j ?_
    rw [Module.End.mem_eigenspace_iff, map_smul, heig j v, smul_comm]
  have hv : ∑ j : Fin p, (p : K)⁻¹ • (∑ i ∈ Finset.range p, (c j • Y) ^ i) v = v := by
    rw [← Finset.smul_sum, hsum v, smul_smul, inv_mul_cancel₀ hpK, one_smul]
  rwa [hv] at hmem

end CFSG.LieType.SeitzGeneration.NonPth
