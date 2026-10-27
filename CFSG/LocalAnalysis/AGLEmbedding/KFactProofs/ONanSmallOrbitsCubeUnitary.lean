module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallOrbitsCubeCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryTorus
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs

public section

namespace CFSG.AGLEmbedding.KFactProofs.OrbitsCube

open CFSG.AGLEmbedding.UnitaryModel CFSG.UnitaryThreeRecognition.Model
  CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.ClassicalGroups.Unitary
open scoped commutatorElement

section Coordinates

variable {K : Type} [Field K] (J : HermitianForm 3 K)

theorem coord_comm_of_fst_eq_zero (z w : Coord J) (hz : (z : K × K).1 = 0) : z * w = w * z := by
  apply Subtype.ext
  rw [coord_mul_val, coord_mul_val, hz]
  simp [add_comm]

theorem coord_noncomm_of_fst_ne (h2 : (2 : K) ≠ 0) (τ : Kˣ) (hτ : J.conj (τ : K) = -τ)
    (z : Coord J) (hz : (z : K × K).1 ≠ 0) :
    z * hermitianTorusAction J τ z ≠ hermitianTorusAction J τ z * z := by
  intro h
  have hτ0 : (τ : K) ≠ 0 := τ.ne_zero
  have hσa : J.conj (z : K × K).1 ≠ 0 := by simpa using hz
  have hw1 : ((hermitianTorusAction J τ z : Coord J) : K × K).1 = (z : K × K).1 * (τ : K)⁻¹ := by
    rw [torusAction_val, hτ]
    field_simp
  have h2nd := congrArg (fun u : Coord J => (u : K × K).2) h
  simp only [coord_mul_val] at h2nd
  have h3 : (z : K × K).1 * J.conj ((hermitianTorusAction J τ z : Coord J) : K × K).1 =
      ((hermitianTorusAction J τ z : Coord J) : K × K).1 * J.conj (z : K × K).1 := by
    linear_combination -h2nd
  rw [hw1, map_mul, map_inv₀, hτ, inv_neg] at h3
  have h4 : (z : K × K).1 * J.conj (z : K × K).1 * ((τ : K)⁻¹) * 2 = 0 := by
    linear_combination -h3
  have h5 : (2 : K) = 0 := by
    have hne : (z : K × K).1 * J.conj (z : K × K).1 * ((τ : K)⁻¹) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hz hσa) (inv_ne_zero hτ0)
    exact (mul_eq_zero.mp h4).resolve_left hne
  exact h2 h5

end Coordinates

section Model

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

include hK hfix

theorem normalizerWitness_rootGroup (hp2 : p ≠ 2) : NormalizerWitness (rootGroup J hJ) := by
  have hσ := isUnitaryInvolution_conj J hK hfix
  have hchar : CharP K p := charP_of_card Fact.out hK
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).1 (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)
  obtain ⟨τ, hτ0, hτs⟩ := hσ.exists_traceZero
  have hτ : J.conj τ = -τ := by linear_combination hτs
  obtain ⟨c, hc⟩ := hσ.exists_norm (d := -1) (by rw [map_neg, map_one])
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  obtain ⟨b₀, hb₀, hb₀s⟩ := hσ.exists_traceZero
  let z₀ : Coord J := ⟨(0, b₀), by show b₀ + J.conj b₀ + 0 * J.conj 0 = 0; simp [hb₀s]⟩
  refine ⟨torus J hJ (Units.mk0 c hc0),
    torusGroup_le_normalizer_rootGroup J hJ (torus_mem_torusGroup J hJ _),
    torus J hJ (Units.mk0 τ hτ0),
    torusGroup_le_normalizer_rootGroup J hJ (torus_mem_torusGroup J hJ _),
    ⟨root J hJ z₀, root_mem_rootGroup J hJ z₀, ?_, ?_⟩, ?_⟩
  · intro b hb
    obtain ⟨w, rfl⟩ := (mem_rootGroup J hJ).1 hb
    rw [← map_mul, ← map_mul, coord_comm_of_fst_eq_zero J z₀ w rfl]
  · rw [torus_mul_root_mul_inv]
    intro h
    have h1 := root_injective J hJ h
    have h3 := congrArg (fun u : Coord J => (u : K × K).2) h1
    simp only [torusAction_val, Units.val_mk0] at h3
    have hcσ : J.conj c * c = -1 := hc
    have : b₀ * (J.conj c)⁻¹ * c⁻¹ = -b₀ := by
      rw [mul_assoc, ← mul_inv, hcσ]
      simp
    have h4 : -b₀ = b₀ := by rw [← this]; exact h3
    exact hb₀ (by
      have : (2 : K) * b₀ = 0 := by linear_combination -h4
      exact (mul_eq_zero.mp this).resolve_left h2)
  · intro t ht htn
    obtain ⟨z, rfl⟩ := (mem_rootGroup J hJ).1 ht
    have hz : (z : K × K).1 ≠ 0 := by
      intro hz0
      obtain ⟨b, hb, hne⟩ := htn
      obtain ⟨w, rfl⟩ := (mem_rootGroup J hJ).1 hb
      exact hne (by rw [← map_mul, ← map_mul, coord_comm_of_fst_eq_zero J z w hz0])
    rw [torus_mul_root_mul_inv, Ne, commutatorElement_eq_one_iff_mul_comm, ← map_mul, ← map_mul]
    intro h
    exact coord_noncomm_of_fst_ne J h2 (Units.mk0 τ hτ0) hτ z hz (root_injective J hJ h)

end Model

theorem normalizerWitness_isSmallUnitary {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : CFSG.AGLEmbedding.IsSmallUnitary p K) (T : Sylow p K) :
    NormalizerWitness (T : Subgroup K) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, ⟨q, hqp, -, hdq⟩, ⟨e⟩⟩ := h
  have hd : CFSG.AGLEmbedding.IsUnitaryIndex p d := ⟨q, hqp, hdq⟩
  obtain ⟨-, hf, -, K', _, _, J, hJ, hK, hfix, ⟨e0⟩⟩ :=
    exists_equiv_psu (statedClassicalModel hd ⟨e⟩)
  obtain ⟨S, hS⟩ := exists_sylow_eq_rootGroup J hJ hK hfix hf
  obtain ⟨e', he'⟩ := exists_equiv_map_eq e0 T S
  exact NormalizerWitness.of_map e' (T := (T : Subgroup K)) (he'.trans hS ▸
    normalizerWitness_rootGroup J hJ hK hfix hp2)

end CFSG.AGLEmbedding.KFactProofs.OrbitsCube
