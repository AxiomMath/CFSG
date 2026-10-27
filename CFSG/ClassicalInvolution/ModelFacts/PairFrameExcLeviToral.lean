module

public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLevi
public import CFSG.LieType.Chevalley.E6GraphInvolutionFiniteReduction

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


section T0

variable {τ : Tag}

theorem baseChangeGL_mem_parabolicLevi {K L : Type} [Field K] [Field L] (f : K →+* L)
    {J : Set (Fin τ.rank)} {g : ModGL τ K} (hg : g ∈ parabolicLevi τ K J) :
    baseChangeGL f g ∈ parabolicLevi τ L J := by
  have hle : (parabolicLevi τ K J).map (baseChangeGL f) ≤ parabolicLevi τ L J := by
    rw [parabolicLevi, Subgroup.map_sup, sup_le_iff]
    constructor
    · rw [torusGroup, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨⟨i, t⟩, rfl⟩, rfl⟩
      rw [baseChangeGL_torusElt]
      exact torusGroup_le_parabolicLevi J (torusElt_mem_torusGroup i _)
    · rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨j, hj, c, rfl | rfl⟩, rfl⟩
      · rw [baseChangeGL_xUnit]
        exact xUnit_mem_parabolicLevi hj _
      · rw [baseChangeGL_yUnit]
        exact yUnit_mem_parabolicLevi hj _
  exact hle (Subgroup.mem_map_of_mem _ hg)




end T0

section T1

variable {τ : Tag}

theorem exists_finset_descent_levi {k : Type} [Field k] {J : Set (Fin τ.rank)} {x : ModGL τ k}
    (hx : x ∈ parabolicLevi τ k J) :
    ∃ E : Finset k, ∀ K : Subfield k, (E : Set k) ⊆ K →
      ∃ y ∈ parabolicLevi τ K J, baseChangeGL K.subtype y = x := by
  classical
  have hcl : parabolicLevi τ k J = Subgroup.closure
      (Set.range (fun p : Fin τ.rank × kˣ => torusElt τ k p.1 p.2) ∪
        {g | ∃ j ∈ J, ∃ c : k, g = xUnit τ k j c ∨ g = yUnit τ k j c}) := by
    rw [Subgroup.closure_union]
    rfl
  rw [hcl] at hx
  induction hx using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with ⟨⟨i, t⟩, rfl⟩ | ⟨j, hj, c, rfl | rfl⟩
    · refine ⟨{(t : k), ((t⁻¹ : kˣ) : k)}, fun K hK => ?_⟩
      have ht : (t : k) ∈ K := hK (by simp)
      have hti : ((t⁻¹ : kˣ) : k) ∈ K := hK (by simp)
      let t' : Kˣ := ⟨⟨t, ht⟩, ⟨(t⁻¹ : kˣ), hti⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩
      refine ⟨torusElt τ K i t', torusGroup_le_parabolicLevi J (torusElt_mem_torusGroup i t'), ?_⟩
      rw [baseChangeGL_torusElt]
      congr 2
    · refine ⟨{c}, fun K hK => ?_⟩
      have hc : c ∈ K := hK (by simp)
      refine ⟨xUnit τ K j ⟨c, hc⟩, xUnit_mem_parabolicLevi hj _, ?_⟩
      rw [baseChangeGL_xUnit]
      rfl
    · refine ⟨{c}, fun K hK => ?_⟩
      have hc : c ∈ K := hK (by simp)
      refine ⟨yUnit τ K j ⟨c, hc⟩, yUnit_mem_parabolicLevi hj _, ?_⟩
      rw [baseChangeGL_yUnit]
      rfl
  | one => exact ⟨∅, fun K _ => ⟨1, one_mem _, map_one _⟩⟩
  | mul g h _ _ ihg ihh =>
    obtain ⟨E₁, h₁⟩ := ihg
    obtain ⟨E₂, h₂⟩ := ihh
    refine ⟨E₁ ∪ E₂, fun K hK => ?_⟩
    rw [Finset.coe_union, Set.union_subset_iff] at hK
    obtain ⟨y₁, hy₁, e₁⟩ := h₁ K hK.1
    obtain ⟨y₂, hy₂, e₂⟩ := h₂ K hK.2
    exact ⟨y₁ * y₂, mul_mem hy₁ hy₂, by rw [map_mul, e₁, e₂]⟩
  | inv g _ ih =>
    obtain ⟨E, hE⟩ := ih
    refine ⟨E, fun K hK => ?_⟩
    obtain ⟨y, hy, e⟩ := hE K hK
    exact ⟨y⁻¹, inv_mem hy, by rw [map_inv, e]⟩




end T1

section T2

variable {τ : Tag}

theorem exists_levi_conj_eq_rootDiagUnit {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (k : Type)
    [Field k] [IsAlgClosed k] [CharP k p]
    (halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {J : Set (Fin τ.rank)}
    {x : ModGL τ k} (hx : x ∈ parabolicLevi τ k J) (hx2 : x ^ 2 = 1) :
    ∃ v ∈ parabolicLevi τ k J, ∃ a : Fin τ.rank → kˣ, (∀ i, a i = 1 ∨ a i = -1) ∧
      v * x * v⁻¹ = rootDiagUnit τ a := by
  classical
  let := ZMod.algebra k p
  have hk : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp2
  obtain ⟨E, hE⟩ := exists_finset_descent_levi hx
  set M := Nat.card (parabolicWeylGroup τ J) with hMdef
  have hM : 1 ≤ M := Nat.card_pos
  have hWM : ¬ 2 ^ M ∣ M := fun h => absurd (Nat.le_of_dvd (by omega) h) (by
    have := Nat.lt_two_pow_self (n := M)
    omega)
  obtain ⟨K, hKfin, hEK, hKq⟩ := exceptional_Lang_finite_subfield_congruence_enlargement hp2 E
    (fun z _ => Algebra.IsAlgebraic.isAlgebraic z) hM
  have hKodd : Odd (Nat.card K) := by
    have h2 : Nat.card K ≡ 1 [MOD 2] := Nat.ModEq.of_dvd (dvd_pow_self 2 (by omega)) hKq
    exact Nat.odd_iff.2 h2
  obtain ⟨y, hyL, hyx⟩ := hE K hEK
  set ι := K.subtype with hι
  have hy2 : y * y = 1 := by
    apply baseChangeGL_injective ι
    rw [map_mul, hyx, map_one, ← sq, hx2]
  obtain ⟨u, huL, huN⟩ := exists_conj_leviMonomial (τ := τ) (K := K) J hKodd hKq hWM hyL hy2
  set n := baseChangeGL ι u * x * (baseChangeGL ι u)⁻¹ with hndef
  have hnN : n ∈ monomialSubgroup τ k := by
    have := baseChangeGL_mem_monomialSubgroup ι huN.2
    rwa [map_mul, map_mul, map_inv, hyx] at this
  have hnL : n ∈ parabolicLevi τ k J := by
    have := baseChangeGL_mem_parabolicLevi ι huN.1
    rwa [map_mul, map_mul, map_inv, hyx] at this
  have hn2 : n ^ 2 = 1 := by
    rw [hndef, sq]
    calc baseChangeGL ι u * x * (baseChangeGL ι u)⁻¹ * (baseChangeGL ι u * x *
          (baseChangeGL ι u)⁻¹) = baseChangeGL ι u * x ^ 2 * (baseChangeGL ι u)⁻¹ := by
          rw [sq]; group
      _ = 1 := by rw [hx2]; group
  have hw2 : weylQuotientHom τ k ⟨n, hnN⟩ ^ 2 = 1 := by
    have e : (⟨n, hnN⟩ : monomialSubgroup τ k) ^ 2 = 1 := Subtype.ext (by simpa using hn2)
    rw [← map_pow, e, map_one]
  obtain ⟨v, hvL, hvH⟩ := exists_levi_conj_mem_torusGroup hk hnN hnL hw2
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hvH
  refine ⟨v * baseChangeGL ι u, mul_mem hvL (baseChangeGL_mem_parabolicLevi ι huL), a,
    fun i => ?_, ?_⟩
  · have hsq : rootDiagUnit τ (a * a) = rootDiagUnit τ 1 := by
      rw [rootDiagUnit_mul, ← ha, rootDiagUnit_one]
      calc v * n * v⁻¹ * (v * n * v⁻¹) = v * n ^ 2 * v⁻¹ := by rw [sq]; group
        _ = 1 := by rw [hn2]; group
    have := congrFun (rootDiagUnit_injective hsq) i
    exact units_eq_one_or_neg_one_of_mul_self this
  · rw [← ha, hndef]
    group


end T2


end CFSG.ClassicalInvolution.ModelFacts.Levi
