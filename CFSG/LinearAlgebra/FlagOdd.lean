module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.FieldTheory.Finiteness

import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderFlip
import CFSG.Holt.H78.Lemma16Basic

public section

namespace CFSG.LinearAlgebra.FlagOdd

open Module

universe u

variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V]

theorem add_self_eq_zero (h2 : (2 : K) = 0) (v : V) : v + v = 0 := by
  rw [← two_smul K v, h2, zero_smul]

theorem pow_four_eq_one (h2 : (2 : K) = 0) {f : Module.End K V} (hN3 : (f - 1) ^ 3 = 0) :
    f ^ 4 = 1 := by
  have h2E : (2 : Module.End K V) = 0 := by
    rw [← map_ofNat (algebraMap K (Module.End K V)) 2, h2, map_zero]
  set N := f - 1 with hNdef
  have hf : f = 1 + N := by rw [hNdef]; abel
  have hN4 : N ^ 4 = 0 := by rw [pow_succ, hN3, zero_mul]
  have key : (1 + N) ^ 4 = 1 + 2 * (2 * N + 3 * N ^ 2 + 2 * N ^ 3) + N ^ 4 := by
    noncomm_ring
  rw [hf, key, h2E, zero_mul, add_zero, hN4, add_zero]

theorem pow_four_eq_one_of_flag (h2 : (2 : K) = 0) {A B : Submodule K V} (f : Module.End K V)
    (hA : ∀ v ∈ A, f v = v) (hBA : ∀ v ∈ B, f v - v ∈ A) (hB : ∀ v, f v - v ∈ B) :
    f ^ 4 = 1 := by
  refine pow_four_eq_one h2 ?_
  ext v
  have hN : ∀ w, (f - 1) w = f w - w := fun w => rfl
  simp only [pow_succ, pow_zero, one_mul, Module.End.mul_apply, LinearMap.zero_apply, hN]
  have h1 := hB v
  have h2' := hBA _ h1
  have h3 := hA _ h2'
  rw [h3, sub_self]

theorem mul_self_eq_one_of_apply_eq (h2 : (2 : K) = 0) {M : Type u} [AddCommGroup M]
    [Module K M] [Module.Finite K M] (hM : finrank K M = 2) (f : M →ₗ[K] M)
    (hdet : LinearMap.det f = 1) {m : M} (hm : m ≠ 0) (hfm : f m = m) : f * f = 1 := by
  classical
  have hlt : K ∙ m < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have := finrank_span_singleton (K := K) hm
    rw [htop, finrank_top, hM] at this
    exact absurd this (by norm_num)
  obtain ⟨m', -, hm'⟩ := SetLike.exists_of_lt hlt
  have hli : LinearIndependent K ![m, m'] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.1 hst).resolve_right hm, rfl⟩
    · exfalso
      apply hm'
      have : m' = (-(t⁻¹ * s)) • m := by
        have h := congrArg (fun x => t⁻¹ • x) hst
        simp only [smul_add, smul_smul, smul_zero, inv_mul_cancel₀ ht, one_smul] at h
        rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm]
        exact h
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self m)
  have hdet0 : LinearMap.det f ≠ 0 := by rw [hdet]; exact one_ne_zero
  let g := LinearMap.equivOfDetNeZero f hdet0
  have hg : ∀ x, g x = f x := fun x => rfl
  obtain ⟨c, hc⟩ := CFSG.QuasithinUnique.Setup.Offender.unitriangular_of_fixed hM hli g
    (by rw [hg]; exact hfm) (by
      have : (g : M →ₗ[K] M) = f := LinearMap.ext hg
      rw [this]; exact hdet)
  rw [hg] at hc
  have hcard : Fintype.card (Fin 2) = finrank K M := by simp [hM]
  let bs := basisOfLinearIndependentOfCardEqFinrank hli hcard
  apply bs.ext
  intro i
  fin_cases i
  · change f (f (bs 0)) = bs 0
    have : bs 0 = m := by simp [bs]
    rw [this, hfm, hfm]
  · change f (f (bs 1)) = bs 1
    have : bs 1 = m' := by simp [bs]
    rw [this, hc, map_add, map_smul, hfm, hc, ← add_assoc, ← add_smul,
      show c + c = 0 by rw [← two_mul, h2, zero_mul], zero_smul, zero_add]

theorem eq_one_of_pow_eight_eq_one {P : Type*} [Group P] {p : P} (hodd : Odd (orderOf p))
    (h8 : p ^ 8 = 1) : p = 1 := by
  have hd : orderOf p ∣ 2 ^ 3 := orderOf_dvd_of_pow_eq_one h8
  exact orderOf_eq_one_iff.mp ((hodd.coprime_two_right.pow_right 3).eq_one_of_dvd hd)

theorem card_dvd_of_flag [Finite K] [FiniteDimensional K V] {P : Type*} [Group P] [Finite P]
    (h2 : (2 : K) = 0) (ρ : P →* Module.End K V) (hinj : Function.Injective ρ)
    (hodd : Odd (Nat.card P)) (hdet : ∀ p, LinearMap.det (ρ p) = 1)
    {A B : Submodule K V} (hAB : A ≤ B) (hdim : finrank K B = finrank K A + 2)
    (hA : ∀ p, ∀ v ∈ A, ρ p v = v) (hB : ∀ p v, ρ p v - v ∈ B) :
    Nat.card P ∣ Nat.card K ^ 2 - 1 := by
  classical
  have hBinv : ∀ p, B ≤ B.comap (ρ p) := fun p v hv => by
    have h := B.add_mem (hB p v) hv
    rwa [sub_add_cancel] at h
  set A' : Submodule K B := A.comap B.subtype with hA'
  have hA'inv : ∀ p, A' ≤ A'.comap ((ρ p).restrict (hBinv p)) := fun p v hv => by
    simp only [hA', Submodule.mem_comap, Submodule.coe_subtype] at hv ⊢
    change ρ p v ∈ A
    rw [hA p _ hv]
    exact hv
  let fM : P → Module.End K (B ⧸ A') := fun p => A'.mapQ A' ((ρ p).restrict (hBinv p)) (hA'inv p)
  have fM_mk : ∀ p (v : B), fM p (A'.mkQ v) = A'.mkQ ⟨ρ p v, hBinv p v.2⟩ := fun p v => rfl
  have fM_mul : ∀ p q, fM (p * q) = fM p * fM q := by
    intro p q
    ext v
    simp only [LinearMap.coe_comp, Function.comp_apply, Module.End.mul_apply, fM_mk]
    congr 1
    ext
    simp [map_mul]
  have fM_one : fM 1 = 1 := by
    ext v
    simp only [LinearMap.coe_comp, Function.comp_apply, Module.End.one_apply, fM_mk]
    congr 1
    ext
    simp
  have hA'dim : finrank K A' = finrank K A :=
    (Submodule.comapSubtypeEquivOfLe hAB).finrank_eq
  have hM : finrank K (B ⧸ A') = 2 := by
    have := A'.finrank_quotient_add_finrank
    omega
  have hdetM : ∀ p, LinearMap.det (fM p) = 1 := by
    intro p
    have hVB : B.mapQ B (ρ p) (hBinv p) = LinearMap.id := by
      ext v
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
        Submodule.mapQ_apply, LinearMap.id_comp]
      exact (Submodule.Quotient.eq B).2 (hB p v)
    have hAA : ((ρ p).restrict (hBinv p)).restrict (hA'inv p) = LinearMap.id := by
      ext v
      simp only [LinearMap.restrict_coe_apply, LinearMap.id_coe, id_eq]
      exact hA p _ v.2
    have h1 := LinearMap.det_eq_det_mul_det B (ρ p) (hBinv p)
    have h2' := LinearMap.det_eq_det_mul_det A' _ (hA'inv p)
    rw [hVB, LinearMap.det_id, mul_one, h2', hAA, LinearMap.det_id, one_mul, hdet p] at h1
    exact h1.symm
  have hne : ∀ p (m : B ⧸ A'), m ≠ 0 → fM p m ≠ 0 := by
    intro p m hm h
    apply hm
    have := congrArg (fM p⁻¹) h
    rwa [map_zero, ← Module.End.mul_apply, ← fM_mul, inv_mul_cancel, fM_one,
      Module.End.one_apply] at this
  let : MulAction P {m : B ⧸ A' // m ≠ 0} :=
    { smul := fun p m => ⟨fM p m.1, hne p m.1 m.2⟩
      one_smul := fun m => Subtype.ext (by
        change fM 1 m.1 = m.1
        rw [fM_one, Module.End.one_apply])
      mul_smul := fun p q m => Subtype.ext (by
        change fM (p * q) m.1 = fM p (fM q m.1)
        rw [fM_mul, Module.End.mul_apply]) }
  have hfree : ∀ (p : P) (m : {m : B ⧸ A' // m ≠ 0}), p • m = m → p = 1 := by
    intro p m hpm
    have hfm : fM p m.1 = m.1 := congrArg Subtype.val hpm
    have hsq := mul_self_eq_one_of_apply_eq h2 hM (fM p) (hdetM p) m.2 hfm
    rw [← fM_mul, ← pow_two] at hsq
    have hBA : ∀ v ∈ B, ρ (p ^ 2) v - v ∈ A := by
      intro v hv
      have h := LinearMap.congr_fun hsq (A'.mkQ ⟨v, hv⟩)
      rw [fM_mk, Module.End.one_apply, Submodule.mkQ_apply, Submodule.mkQ_apply,
        Submodule.Quotient.eq] at h
      exact h
    have h4 := pow_four_eq_one_of_flag h2 (ρ (p ^ 2)) (hA (p ^ 2)) hBA (hB (p ^ 2))
    refine eq_one_of_pow_eight_eq_one (hodd.of_dvd_nat (orderOf_dvd_natCard p)) ?_
    exact hinj (by rw [map_one, show p ^ 8 = (p ^ 2) ^ 4 by rw [← pow_mul], map_pow, h4])
  have : Finite (B ⧸ A') := Module.finite_of_finite K
  have hdvd := CFSG.Holt.H78.L16.natCard_dvd_natCard_of_free hfree
  have hcard : Nat.card {m : B ⧸ A' // m ≠ 0} = Nat.card K ^ 2 - 1 := by
    have := Fintype.ofFinite (B ⧸ A')
    rw [← hM, ← Module.natCard_eq_pow_finrank, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  rwa [hcard] at hdvd

end CFSG.LinearAlgebra.FlagOdd
