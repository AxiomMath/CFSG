module

public import CFSG.LieType.Chevalley.LangNormalizerInvolutionTorus
public import CFSG.LieType.Chevalley.E6GraphInvolutionFiniteReduction

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem exceptional_Lang_algebraic_prime_field_involution_torus
    {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) (τ : Tag)
    {x : ModGL τ k} (hx : x ∈ adjointGroup τ k) (hx2 : x ^ 2 = 1) :
    ∃ g ∈ adjointGroup τ k, ∃ a : Fin τ.rank → kˣ, (∀ i, a i = 1 ∨ a i = -1) ∧
      g * x * g⁻¹ = rootDiagUnit τ a := by
  classical
  let := ZMod.algebra k p
  have hk : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp2
  obtain ⟨E, hE⟩ := exists_finset_descent hx
  set M := Nat.card (WeylGroup τ) with hMdef
  have hM : 1 ≤ M := Nat.card_pos
  have hWM : ¬ 2 ^ M ∣ M := fun h => absurd (Nat.le_of_dvd (by omega) h) (by
    have := Nat.lt_two_pow_self (n := M)
    omega)
  obtain ⟨K, hKfin, hEK, hKq⟩ := exceptional_Lang_finite_subfield_congruence_enlargement hp2 E
    (fun z _ => Algebra.IsAlgebraic.isAlgebraic z) hM
  have hKodd : Odd (Nat.card K) := by
    have h2 : Nat.card K ≡ 1 [MOD 2] := Nat.ModEq.of_dvd (dvd_pow_self 2 (by omega)) hKq
    exact Nat.odd_iff.2 h2
  obtain ⟨y, hyC, hyx⟩ := hE K hEK
  set ι := K.subtype with hι
  have hy2 : y ^ 2 = 1 := by
    apply baseChangeGL_injective ι
    rw [map_pow, hyx, hx2, map_one]
  obtain ⟨u, huC, huN⟩ :=
    (exceptional_Lang_finite_normalizer_odd_index_involutions τ K hKodd hM hKq hWM).2 y hyC hy2
  set n := baseChangeGL ι u * x * (baseChangeGL ι u)⁻¹ with hndef
  have hnN : n ∈ monomialSubgroup τ k := by
    have := baseChangeGL_mem_monomialSubgroup ι huN
    rwa [map_mul, map_mul, map_inv, hyx] at this
  have hn2 : n ^ 2 = 1 := by
    rw [hndef, sq]
    calc baseChangeGL ι u * x * (baseChangeGL ι u)⁻¹ * (baseChangeGL ι u * x *
          (baseChangeGL ι u)⁻¹) = baseChangeGL ι u * x ^ 2 * (baseChangeGL ι u)⁻¹ := by
          rw [sq]; group
      _ = 1 := by rw [hx2]; group
  have hw2 : weylQuotientHom τ k ⟨n, hnN⟩ ^ 2 = 1 := by
    have e : (⟨n, hnN⟩ : monomialSubgroup τ k) ^ 2 = 1 := Subtype.ext (by
      simpa using hn2)
    rw [← map_pow, e, map_one]
  obtain ⟨v, hvC, hvH⟩ := exceptional_Lang_normalizer_Weyl_involution_torus_conjugacy τ k hk hnN hw2
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hvH
  refine ⟨v * baseChangeGL ι u, mul_mem hvC (baseChangeGL_mem_adjointGroup ι huC), a,
    fun i => ?_, ?_⟩
  ·
    have hsq : rootDiagUnit τ (a * a) = rootDiagUnit τ 1 := by
      rw [rootDiagUnit_mul, ← ha, rootDiagUnit_one]
      calc v * n * v⁻¹ * (v * n * v⁻¹) = v * n ^ 2 * v⁻¹ := by rw [sq]; group
        _ = 1 := by rw [hn2]; group
    have := congrFun (rootDiagUnit_injective hsq) i
    exact units_eq_one_or_neg_one_of_mul_self this
  · rw [← ha, hndef]
    group

end CFSG.LieType.Chevalley
