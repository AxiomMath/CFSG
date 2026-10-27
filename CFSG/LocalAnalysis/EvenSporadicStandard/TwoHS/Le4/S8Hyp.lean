module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Coord
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Fin

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup Matrix

variable {G : Type*} [Group G]

theorem ECoord.mat_inv_mul {C : ECoord G} {m : G} (hm : m ∈ normalizer (C.E : Set G)) :
    C.mat m⁻¹ * C.mat m = 1 := by
  rw [← C.mat_mul (inv_mem hm) hm, inv_mul_cancel, C.mat_one]

theorem ECoord.mat_mul_inv {C : ECoord G} {m : G} (hm : m ∈ normalizer (C.E : Set G)) :
    C.mat m * C.mat m⁻¹ = 1 := by
  rw [← C.mat_mul hm (inv_mem hm), mul_inv_cancel, C.mat_one]

structure Sect8Hyp (C : ECoord G) (f n : G) (S₀ : Subgroup G) : Prop where
  f_mem : f ∈ C.E
  vec_f : C.vec f = fVec
  centN : ∀ x : G, x * f ^ 2 = f ^ 2 * x → (∀ e ∈ C.E, x * e = e * x) → x ∈ C.E
  E_le : C.E ≤ S₀
  S₀_cent : ∀ x ∈ S₀, x * f ^ 2 = f ^ 2 * x
  S₀_norm : ∀ x ∈ S₀, x ∈ normalizer (C.E : Set G)
  E_char : ∀ g : G, (∀ x, x ∈ S₀ ↔ g * x * g⁻¹ ∈ S₀) → g ∈ normalizer (C.E : Set G)
  actN : ∀ x : G, x * f ^ 2 = f ^ 2 * x → x ∈ normalizer (C.E : Set G) → C.mat x ∈ q0List
  actN' : ∀ A ∈ q0List, ∃ x : G, x * f ^ 2 = f ^ 2 * x ∧ x ∈ normalizer (C.E : Set G) ∧
    C.mat x = A
  actS : ∀ x ∈ S₀, C.mat x ∈ shatList
  actS' : ∀ A ∈ shatList, ∃ x ∈ S₀, C.mat x = A
  n_norm : ∀ x : G, x ∈ S₀ ↔ n * x * n⁻¹ ∈ S₀

namespace Sect8Hyp

variable {C : ECoord G} {f n : G} {S₀ : Subgroup G} (h : Sect8Hyp C f n S₀)
include h

theorem vec_f2 (hQ : Q0Facts) : C.vec (f ^ 2) = tVec := by
  rw [sq, C.vec_mul h.f_mem h.f_mem, h.vec_f, hQ.two_f]

theorem f2_eq (hQ : Q0Facts) : f ^ 2 = C.elt tVec := by
  rw [← h.vec_f2 hQ, C.elt_vec (pow_mem h.f_mem 2)]

theorem exists_n0 {s : G} (hQ : Q0Facts) (hNC : NormComplete) (hCF : CandFacts)
    (hnt : n * f ^ 2 * n⁻¹ = s ^ 2) (hs2 : s ^ 2 ≠ f ^ 2) :
    ∃ n₀ : G, n₀ ∈ normalizer (C.E : Set G) ∧ C.mat n₀ ∈ alphaReps ∧
      n₀ * f ^ 2 * n₀⁻¹ = s ^ 2 ∧ s ^ 2 = C.elt zpVec := by
  have hn : n ∈ normalizer (C.E : Set G) := h.E_char n h.n_norm
  have hf2 : f ^ 2 = C.elt tVec := h.f2_eq hQ
  have hs2e : s ^ 2 = C.elt (C.mat n *ᵥ tVec) := by
    calc s ^ 2 = n * f ^ 2 * n⁻¹ := hnt.symm
      _ = n * C.elt tVec * n⁻¹ := by rw [← hf2]
      _ = C.elt (C.mat n *ᵥ tVec) := C.conj_elt hn tVec
  have hnorm1 : ∀ s' ∈ shatList, ∃ s'' ∈ shatList, C.mat n * s' = s'' * C.mat n := by
    intro s' hs'
    obtain ⟨x, hxS, hx⟩ := h.actS' s' hs'
    have hxn : n * x * n⁻¹ ∈ S₀ := (h.n_norm x).1 hxS
    refine ⟨C.mat (n * x * n⁻¹), h.actS _ hxn, ?_⟩
    have e1 : C.mat (n * x * n⁻¹) * C.mat n = C.mat n * C.mat x := by
      rw [← C.mat_mul (h.S₀_norm _ hxn) hn, ← C.mat_mul hn (h.S₀_norm _ hxS)]
      congr 1
      group
    rw [← hx]
    exact e1.symm
  have hnorm2 : ∀ s'' ∈ shatList, ∃ s' ∈ shatList, C.mat n * s' = s'' * C.mat n := by
    intro s'' hs''
    obtain ⟨y, hyS, hy⟩ := h.actS' s'' hs''
    have hxS : n⁻¹ * y * n ∈ S₀ := by
      rw [h.n_norm]
      have : n * (n⁻¹ * y * n) * n⁻¹ = y := by group
      rw [this]
      exact hyS
    refine ⟨C.mat (n⁻¹ * y * n), h.actS _ hxS, ?_⟩
    have e1 : C.mat n * C.mat (n⁻¹ * y * n) = C.mat y * C.mat n := by
      rw [← C.mat_mul hn (h.S₀_norm _ hxS), ← C.mat_mul (h.S₀_norm _ hyS) hn]
      congr 1
      group
    rw [← hy]
    exact e1
  have hne : C.mat n *ᵥ tVec ≠ tVec := by
    intro h1
    apply hs2
    rw [hs2e, h1, ← hf2]
  obtain ⟨hAz, hα⟩ :=
    (hNC (C.mat n) ⟨C.mat n⁻¹, C.mat_mul_inv hn, C.mat_inv_mul hn⟩ hnorm1 hnorm2).resolve_left hne
  have hswap := hCF.1 _ hα
  have hs2z : s ^ 2 = C.elt zpVec := by rw [hs2e, hAz]
  have hstar : ∀ p ∈ q0List, p *ᵥ zpVec = zpVec → ∃ q ∈ q0List, p * C.mat n = C.mat n * q := by
    intro p hp hpz
    obtain ⟨x, hxc, hxn, hxp⟩ := h.actN' p hp
    have hxs : x * s ^ 2 * x⁻¹ = s ^ 2 := by
      rw [hs2z, C.conj_elt hxn, hxp, hpz]
    have hyn : n⁻¹ * x * n ∈ normalizer (C.E : Set G) := mul_mem (mul_mem (inv_mem hn) hxn) hn
    have hy : n⁻¹ * x * n * f ^ 2 = f ^ 2 * (n⁻¹ * x * n) := by
      have h1 : x * (n * f ^ 2 * n⁻¹) * x⁻¹ = n * f ^ 2 * n⁻¹ := by rw [hnt]; exact hxs
      calc n⁻¹ * x * n * f ^ 2 = n⁻¹ * (x * (n * f ^ 2 * n⁻¹) * x⁻¹) * x * n := by group
        _ = n⁻¹ * (n * f ^ 2 * n⁻¹) * x * n := by rw [h1]
        _ = f ^ 2 * (n⁻¹ * x * n) := by group
    refine ⟨C.mat (n⁻¹ * x * n), h.actN _ hy hyn, ?_⟩
    have e1 : C.mat n * C.mat (n⁻¹ * x * n) = C.mat x * C.mat n := by
      rw [C.mat_mul (mul_mem (inv_mem hn) hxn) hn, C.mat_mul (inv_mem hn) hxn]
      calc C.mat n * (C.mat n⁻¹ * C.mat x * C.mat n)
          = (C.mat n * C.mat n⁻¹) * C.mat x * C.mat n := by simp only [mul_assoc]
        _ = C.mat x * C.mat n := by rw [C.mat_mul_inv hn, one_mul]
    rw [← hxp]
    exact e1.symm
  have hsq : C.mat n * C.mat n ∈ q0List := by
    have hc : n * n * f ^ 2 = f ^ 2 * (n * n) := by
      have h1 : n * s ^ 2 * n⁻¹ = f ^ 2 := by
        rw [hs2z, C.conj_elt hn, hswap.2, ← hf2]
      calc n * n * f ^ 2 = (n * (n * f ^ 2 * n⁻¹) * n⁻¹) * (n * n) := by group
        _ = (n * s ^ 2 * n⁻¹) * (n * n) := by rw [hnt]
        _ = f ^ 2 * (n * n) := by rw [h1]
    rw [← C.mat_mul hn hn]
    exact h.actN _ hc (mul_mem hn hn)
  obtain ⟨α₀, hα₀, r, hr, q, hq, hαrq⟩ := hCF.2.2 _ hα hstar hsq
  obtain ⟨xr, -, hxrn, hxr⟩ := h.actN' r (hQ.reps_mem r hr)
  obtain ⟨xq, -, hxqn, hxq⟩ := h.actN' q hq
  have hn0n : xr⁻¹ * n * xq⁻¹ ∈ normalizer (C.E : Set G) :=
    mul_mem (mul_mem (inv_mem hxrn) hn) (inv_mem hxqn)
  have hmat : C.mat (xr⁻¹ * n * xq⁻¹) = α₀ := by
    rw [C.mat_mul (mul_mem (inv_mem hxrn) hn) (inv_mem hxqn), C.mat_mul (inv_mem hxrn) hn, hαrq,
      ← hxr, ← hxq]
    calc C.mat xr⁻¹ * (C.mat xr * α₀ * C.mat xq) * C.mat xq⁻¹
        = (C.mat xr⁻¹ * C.mat xr) * α₀ * (C.mat xq * C.mat xq⁻¹) := by simp only [mul_assoc]
      _ = α₀ := by rw [C.mat_inv_mul hxrn, C.mat_mul_inv hxqn, one_mul, mul_one]
  refine ⟨xr⁻¹ * n * xq⁻¹, hn0n, hmat ▸ hα₀, ?_, hs2z⟩
  rw [hf2, C.conj_elt hn0n, hmat, hs2z]
  congr 1
  exact (hCF.1 α₀ (hCF.2.1 α₀ hα₀)).1

end Sect8Hyp

end CFSG.EvenSporadicStandard.TwoHS
