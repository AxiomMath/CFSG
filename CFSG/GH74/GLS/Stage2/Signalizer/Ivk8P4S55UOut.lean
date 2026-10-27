module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55UTor
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55UDesc
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55GenFU
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAUGen
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55GenT

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 (innSub)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

include h in
theorem uConjAut_inner_of_pow (hn : 3 ≤ n) (A : uU h n)
    (hA : (uConjAut h (by omega) A) ^ p = 1) :
    uConjAut h (by omega) A ∈ innSub (StatedProj (StatedSU n (p ^ f) K)) := by
  have hn1 : 1 ≤ n := by omega
  have : Fact p.Prime := ⟨h.prime⟩
  rw [← map_pow, uConjAut_eq_one_iff h hn] at hA
  obtain ⟨c, hc⟩ := hA
  have hcN : h.norm (c : K) = 1 :=
    norm_eq_one_of_scalar_mem_primeFormUnitary h hn1 1 (hc ▸ (A ^ p).2)
  have hAm : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ p =
      Matrix.scalar (Fin n) (c : K) := by
    have := congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) hc
    simpa [Subgroup.coe_pow, Units.val_pow_eq_pow_val] using this
  set δ : K := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det with hδ
  have hδp : δ ^ p = (c : K) ^ n := by
    rw [hδ, ← Matrix.det_pow, hAm, Matrix.scalar_apply, Matrix.det_diagonal]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hδN : h.norm δ = 1 := norm_det_eq_one h 1 A.2
  have hδq : δ ^ (p ^ f + 1) = 1 := by rw [← norm_eq_pow h]; exact hδN
  have hcop : Nat.Coprime p (p ^ f + 1) := by
    obtain ⟨k, hk⟩ : p ∣ p ^ f := dvd_pow_self p (by have := h.one_le; omega)
    rw [hk, Nat.coprime_mul_left_add_right]
    exact Nat.coprime_one_right p
  have hcop' : Nat.Coprime p (orderOf δ) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hδq) hcop
  obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hcop'
  have hdet : δ = (((c ^ u : Kˣ) : K)) ^ n := by
    rw [← hu, hδp, ← pow_mul, mul_comm, pow_mul, Units.val_pow_eq_pow_val]
  have hμ : h.norm (((c ^ u : Kˣ) : K)) = 1 := by
    rw [norm_eq_pow h, Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul,
      ← norm_eq_pow h, hcN, one_pow]
  exact ka_uConjAut_inner_of_det h hn1 A (c ^ u) hμ hdet

include h in
theorem outerFalse_unitary (hp2 : p ≠ 2) (hn : 3 ≤ n) {i₀ i₁ i₂ : Fin n} (hij : i₀ ≠ i₁)
    (h02 : i₂ ≠ i₀) (h12 : i₂ ≠ i₁) : OuterFalse p (StatedProj (StatedSU n (p ^ f) K)) := by
  intro α hα hαp _ hHH
  have hn1 : 1 ≤ n := by omega
  have : Finite K := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have hq : ¬(n = 3 ∧ p ^ f = 2) := by
    rintro ⟨-, h2⟩
    have hodd : Odd (p ^ f) := (h.prime.odd_of_ne_two hp2).pow
    rw [h2] at hodd
    exact (by decide : ¬ Odd 2) hodd
  have hα1 : α ≠ 1 := fun h1 => hα ⟨1, by simp [h1]⟩
  have hord : orderOf α = p := orderOf_eq_prime hαp hα1
  obtain ⟨A, φ, hαeq⟩ := exists_uConjAut_mul_uFieldAut h hn hq α
  have hφp : φ ^ p = 1 := fieldAut_pow_eq_one h hn hq (hαeq ▸ hαp)
  have hφ1 : φ ≠ 1 := by
    intro hφ1
    apply hα
    have hcA : uConjAut h hn1 A ^ p = 1 := by
      rw [hφ1, map_one, mul_one] at hαeq
      rw [← hαeq]
      exact hαp
    obtain ⟨y, hy⟩ := uConjAut_inner_of_pow h hn A hcA
    refine ⟨y, ?_⟩
    rw [hy, hαeq, hφ1, map_one, mul_one]
  have hφord : orderOf φ = p := orderOf_eq_prime hφp hφ1
  let a' : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    MulAut.congr (uTransport h hn1) α
  have ha' : orderOf a' = p :=
    (MulEquiv.orderOf_eq (MulAut.congr (uTransport h hn1)) α).trans hord
  have hσa : primeFormFieldFactor h isPrimeFormGram_one hn hq a' = φ := by
    have := uFactor_apply h hn hq A φ
    rw [← hαeq] at this
    exact this
  obtain ⟨hpf, hcard, -, -, -, M, hM⟩ :=
    unitary_prime_descent_char h hn hq h.prime hp2 a' ha' φ hσa hφord
  have hαh : α = uConjAut h hn1 M * uFieldAut h hn1 φ * (uConjAut h hn1 M)⁻¹ := by
    have h1 : a' = primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M *
        primeFormFieldHom h isPrimeFormGram_one φ *
        (primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M)⁻¹ := by
      rw [← hM]
      group
    have h2 : α = (MulAut.congr (uTransport h hn1)).symm a' :=
      ((MulAut.congr (uTransport h hn1)).symm_apply_apply α).symm
    rw [h2, h1, map_mul, map_mul, map_inv]
    rfl
  obtain ⟨e, rfl⟩ := hpf
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · have := h.one_le
      rw [h0, mul_zero] at this
      omega
    · exact h0
  have hpe : (p ^ e) ^ p = p ^ (p * e) := by rw [← pow_mul, mul_comm]
  have hcardK : Nat.card K = ((p ^ e) ^ p) ^ 2 := by
    rw [h.card, hpe, ← pow_mul]
    congr 1
    ring
  have hfix' : Nat.card (semilinearFixedSubfield φ) = (p ^ e) ^ 2 := by
    rw [hcard, Nat.mul_div_cancel_left e h.prime.pos]
  obtain ⟨r, c, hr, hr2, hrp, hcr, hcq, hσc⟩ :=
    exists_torsion_moved_unitary h.prime hp2 he φ hcardK hfix'
  have hcmem : c ∈ normOneU (p ^ (p * e)) K := by
    rw [normOneU, MonoidHom.mem_ker, powMonoidHom_apply, ← hpe]
    exact hcq
  let cc : ↥(normOneU (p ^ (p * e)) K) := ⟨c, hcmem⟩
  have hfsig : ∀ l : ↥(normOneU (p ^ (p * e)) K),
      uFieldAut h hn1 φ (uTor h hij l) =
        uTor h hij ⟨Units.map (φ : K →* K) (l : Kˣ), map_mem_normOneU φ l.2⟩ :=
    fun l => uFieldAut_uTor h hn1 hij φ l
  let T : Subgroup (StatedProj (StatedSU n (p ^ (p * e)) K)) :=
    ((powMonoidHom r : ↥(normOneU (p ^ (p * e)) K) →* ↥(normOneU (p ^ (p * e)) K)).ker).map
      (uTor h hij)
  have hT : IsPGroup r ↥T := by
    rintro ⟨_, l, hl, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    have hl' : l ^ r = 1 := hl
    show (uTor h hij l) ^ r ^ 1 = 1
    rw [pow_one, ← map_pow, hl', map_one]
  have hfT : ∀ x ∈ T, uFieldAut h hn1 φ x ∈ T := by
    rintro _ ⟨l, hl, rfl⟩
    refine ⟨⟨Units.map (φ : K →* K) (l : Kˣ), map_mem_normOneU φ l.2⟩, ?_, (hfsig l).symm⟩
    have hl' : l ^ r = 1 := hl
    show (⟨Units.map (φ : K →* K) (l : Kˣ), map_mem_normOneU φ l.2⟩ :
      ↥(normOneU (p ^ (p * e)) K)) ^ r = 1
    apply Subtype.ext
    show (Units.map (φ : K →* K) (l : Kˣ)) ^ r = 1
    rw [← map_pow]
    have h3 := congrArg Subtype.val hl'
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h3
    rw [h3, map_one]
  have hcT : uTor h hij cc ∈ T := ⟨cc, Subtype.ext hcr, rfl⟩
  have hne : uFieldAut h hn1 φ (uTor h hij cc) ≠ uTor h hij cc := by
    rw [hfsig]
    intro h'
    apply hσc
    have := uTor_injective h hij h02 h12 h'
    exact congrArg (fun x : ↥(normOneU (p ^ (p * e)) K) => ((x : Kˣ) : K)) this
  exact false_of_torus_moved hαh hr hr2 hrp hT hfT hcT hne hHH

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
