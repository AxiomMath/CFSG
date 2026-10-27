module

public import CFSG.FeitThompson.Representations.AnchoredArrayPrincipalAxis
public import CFSG.FeitThompson.Representations.LocalCharacterRowsRestrictIrreducibly
public import CFSG.FeitThompson.Representations.CyclicTITwoColumnHalfSelection
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
import CFSG.FeitThompson.Representations.ArrayProjectionEnergySaturation
import CFSG.FeitThompson.Representations.DadeAveragingOrthogonalProjection
import CFSG.FeitThompson.Representations.MixedValuesNormTwoArrayDifference
import CFSG.FeitThompson.Representations.DisjointCoherentRowColumnContradiction
public import CFSG.FeitThompson.Representations.CoprimePowerNonprincipalPrimeChars
public import CFSG.FeitThompson.Representations.CyclicTIIsometryPowerEquivariance
public import CFSG.FeitThompson.Representations.CyclicTIAxesNonrealConjugatePairs
public import CFSG.FeitThompson.Representations.DadeMapPreservesInnerProduct
public import CFSG.FeitThompson.Representations.CoreCoherentIrreducibleArrayOrthogonality
public import CFSG.FeitThompson.Representations.SmallIntegralNormOrthogonalArray

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace PrimeDadeAxis

open scoped ComplexConjugate ComplexOrder

variable {G : Type*} [Group G] [Fintype G] {W W1 W2 : Subgroup G} [Fintype ↥W]
  {ω : classFun ↥W →ₗ[ℂ] classFun G}

theorem sum_sq_lt_of_cfInner_eq_ite {ι : Type*} [Fintype ι] [DecidableEq ι] {η : ι → G → ℂ}
    {ψ : G → ℂ} {n : ι → ℤ} {N : ℤ}
    (hηmem : ∀ k, η k ∈ Submodule.span ℤ (Irr G))
    (hη : ∀ k l, cfInner (η k) (η l) = if k = l then 1 else 0)
    (hψ : ψ ∈ Submodule.span ℤ (Irr G)) (hn : ∀ k, cfInner ψ (η k) = (n k : ℂ))
    (hN : cfInner ψ ψ = (N : ℂ))
    (hne : ψ - ∑ k, cfInner ψ (η k) • η k ≠ 0) :
    ∑ k, n k ^ 2 < N := by
  have hXmem : (∑ k, cfInner ψ (η k) • η k) ∈ Submodule.span ℤ (Irr G) := by
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [hn k, Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ (hηmem k)
  have hsub : (ψ - ∑ k, cfInner ψ (η k) • η k) ∈ Submodule.span ℤ (Irr G) :=
    Submodule.sub_mem _ hψ hXmem
  obtain ⟨m, hm⟩ := exists_int_cfInner_of_mem_span_Irr hsub hsub
  have hpyth := CauchySchwarzProjection.classFunInner_self_eq_add_of_inner_eq
    (η := η) (fun k l => by rw [← cfInner_eq_classFunInner]; exact hη k l)
    ψ (fun k => cfInner ψ (η k)) (fun k => (cfInner_eq_classFunInner _ _).symm)
  simp only [← cfInner_eq_classFunInner] at hpyth
  have hsum : ∑ k, cfInner ψ (η k) * conj (cfInner ψ (η k)) = ((∑ k, n k ^ 2 : ℤ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hn k, map_intCast]
    ring
  rw [hsum, hN, hm] at hpyth
  have hcast : N = (∑ k, n k ^ 2) + m := by exact_mod_cast hpyth
  have hm0 : (0 : ℂ) ≤ (m : ℂ) := hm ▸ cfInner_self_nonneg _
  have hm0' : 0 ≤ m := by exact_mod_cast hm0
  have hmne : m ≠ 0 := by
    intro h0
    have : Nonempty G := ⟨1⟩
    exact hne (cfInner_self_eq_zero.mp (by rw [hm, h0]; simp))
  omega

theorem eq_col_sum_or_eq_row_sum_of_cfInner_eq_ite {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {η : ι × κ → G → ℂ} {ψ : G → ℂ} {s t : ℂ} {i₀ : ι} {j₀ : κ}
    (hq : 3 ≤ Fintype.card ι) (hp : 3 ≤ Fintype.card κ)
    (hηmem : ∀ k, η k ∈ Submodule.span ℤ (Irr G))
    (hη : ∀ k l, cfInner (η k) (η l) = if k = l then 1 else 0)
    (hψ : ψ ∈ Submodule.span ℤ (Irr G))
    (hnorm : cfInner ψ ψ = (Fintype.card ι : ℂ) + 1)
    (h00 : cfInner ψ (η (i₀, j₀)) = 1)
    (hadd : ∀ i j, cfInner ψ (η (i, j))
      = cfInner ψ (η (i, j₀)) + cfInner ψ (η (i₀, j)) - 1)
    (hs : ∀ i, i ≠ i₀ → cfInner ψ (η (i, j₀)) = s)
    (ht : ∀ j, j ≠ j₀ → cfInner ψ (η (i₀, j)) = t)
    (hrem : ψ - ∑ k, cfInner ψ (η k) • η k ≠ 0) :
    (∑ k, cfInner ψ (η k) • η k = ∑ i, η (i, j₀)) ∨
      (∑ k, cfInner ψ (η k) • η k = ∑ j, η (i₀, j) ∧ Fintype.card κ ≤ Fintype.card ι) := by
  classical
  choose a ha using fun k => exists_int_cfInner_of_mem_span_Irr hψ (hηmem k)
  obtain ⟨i₁, hi₁⟩ := Fintype.exists_ne_of_one_lt_card (by omega) i₀
  obtain ⟨j₁, hj₁⟩ := Fintype.exists_ne_of_one_lt_card (by omega) j₀
  set S := a (i₁, j₀) with hS
  set T := a (i₀, j₁) with hT
  have hsS : s = (S : ℂ) := (hs i₁ hi₁).symm.trans (ha _)
  have htT : t = (T : ℂ) := (ht j₁ hj₁).symm.trans (ha _)
  have hpat : ∀ k : ι × κ, a k = if k.1 = i₀ then (if k.2 = j₀ then 1 else T)
      else (if k.2 = j₀ then S else S + T - 1) := by
    rintro ⟨i, j⟩
    have key : ((a (i, j) : ℂ)) = ((if i = i₀ then (if j = j₀ then 1 else T)
        else (if j = j₀ then S else S + T - 1) : ℤ) : ℂ) := by
      rw [← ha (i, j)]
      by_cases hi : i = i₀ <;> by_cases hj : j = j₀
      · subst hi; subst hj; simpa using h00
      · subst hi; rw [ht j hj, htT]; simp [hj]
      · subst hj; rw [hs i hi, hsS]; simp [hi]
      · rw [hadd i j, hs i hi, ht j hj, hsS, htT]; push_cast [hi, hj]; ring
    exact_mod_cast key
  have hNc : cfInner ψ ψ = (((Fintype.card ι : ℤ) + 1 : ℤ) : ℂ) := by rw [hnorm]; push_cast; ring
  have hlt := sum_sq_lt_of_cfInner_eq_ite hηmem hη hψ ha hNc hrem
  have hsumsq : ∑ k : ι × κ, a k ^ 2
      = (1 + ((Fintype.card κ : ℤ) - 1) * T ^ 2) + ((Fintype.card ι : ℤ) - 1) *
        (S ^ 2 + ((Fintype.card κ : ℤ) - 1) * (S + T - 1) ^ 2) := by
    rw [← AnchoredPrimeArray.sum_pattern i₀ j₀ 1 (T ^ 2) (S ^ 2) ((S + T - 1) ^ 2)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hpat k]
    by_cases hi : k.1 = i₀ <;> by_cases hj : k.2 = j₀ <;> simp [hi, hj]
  have hbound : 1 + ((Fintype.card κ : ℤ) - 1) * T ^ 2
      + ((Fintype.card ι : ℤ) - 1) * (S ^ 2 + ((Fintype.card κ : ℤ) - 1) * (S + T - 1) ^ 2)
      ≤ (Fintype.card ι : ℤ) := by rw [← hsumsq] at *; omega
  rcases AnchoredPrimeArray.cases_of_le (q := (Fintype.card ι : ℤ)) (p := (Fintype.card κ : ℤ))
    (by exact_mod_cast hq) (by exact_mod_cast hp) hbound with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · refine Or.inl (AnchoredPrimeArray.sum_smul_eq_sum_col ha fun k => ?_)
    rw [hpat k, h1, h2]
    by_cases hi : k.1 = i₀ <;> by_cases hj : k.2 = j₀ <;> simp [hi, hj]
  · refine Or.inr ⟨AnchoredPrimeArray.sum_smul_eq_sum_row ha fun k => ?_, by exact_mod_cast h3⟩
    rw [hpat k, h1, h2]
    by_cases hi : k.1 = i₀ <;> by_cases hj : k.2 = j₀ <;> simp [hi, hj]

section LocalPairing

variable {Lg : Type*} [Group Lg] [Fintype Lg] {K W₁ W₂ : Subgroup Lg} [K.Normal]
  [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↑(Irr ↥W₁)]
  {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun Lg}

omit [K.Normal] in
theorem primeTIrow_principal_eq_sum_inflateLeft (hpc : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) :
    hpc.primeTIrow σ (principalIrr ↥W₂) = ∑ i : ↑(Irr ↥W₁), hpc.inflateLeft i := by
  rw [← hpc.indClassFun_primeTIres hσ, hpc.primeTIres_principal hσ, hpc.sum_inflateLeft]

theorem cfInner_primeTIrow_principal_eq_zero (hpc : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {χ : Lg → ℂ} (hχ : χ ∈ Irr Lg)
    (hχ1 : χ 1 ≠ 1) : cfInner (hpc.primeTIrow σ (principalIrr ↥W₂)) χ = 0 := by
  classical
  rw [primeTIrow_principal_eq_sum_inflateLeft hpc hσ, cfInner_sum_left]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [cfInner_eq_ite_of_mem_Irr (hpc.inflateLeft_mem_Irr i) hχ, if_neg]
  intro hc
  exact hχ1 (by rw [← hc, hpc.inflateLeft_one])

theorem cfInner_primeTIrow_sub_sub_star (hpc : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {ζ : Lg → ℂ} (hζ : ζ ∈ Irr Lg)
    (hζ1 : ζ 1 ≠ 1) (hζr : star ζ ≠ ζ) :
    cfInner (hpc.primeTIrow σ (principalIrr ↥W₂) - ζ) (ζ - star ζ) = -1 := by
  have hstarIrr : star ζ ∈ Irr Lg := star_mem_Irr hζ
  have hstar1 : (star ζ) 1 ≠ 1 := by
    intro hc
    have h : conj (ζ 1) = 1 := by simpa [Pi.star_apply, RCLike.star_def] using hc
    exact hζ1 (by simpa using congrArg conj h)
  rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right,
    cfInner_primeTIrow_principal_eq_zero hpc hσ hζ hζ1,
    cfInner_primeTIrow_principal_eq_zero hpc hσ hstarIrr hstar1,
    cfInner_eq_ite_of_mem_Irr hζ hζ, if_pos rfl,
    cfInner_eq_ite_of_mem_Irr hζ hstarIrr, if_neg (Ne.symm hζr)]
  ring

theorem cfInner_dadeMap_primeTIrow_sub_dadeMap_sub_star {H : Type*} [Group H] [Fintype H]
    {Lsub : Subgroup H} [Fintype ↥Lsub] {K' V₁ V₂ : Subgroup ↥Lsub} [K'.Normal]
    [Fintype ↥(V₁ ⊔ V₂)]
    [Fintype ↑(Irr ↥V₁)] {τ : classFun ↥(V₁ ⊔ V₂) →ₗ[ℂ] classFun ↥Lsub}
    {A0 : Set H} {T : H → Subgroup H} {ζ : ↥Lsub → ℂ}
    (hpc : IsPrimeCyclicTIHyp K' V₁ V₂)
    (hτ : IsCyclicTIIsometry (V₁ ⊔ V₂) V₁ V₂ τ) (hD : IsDadeData Lsub A0 T)
    (hζ : ζ ∈ Irr ↥Lsub) (hζ1 : ζ 1 ≠ 1) (hζr : star ζ ≠ ζ)
    (hF : (hpc.primeTIrow τ (principalIrr ↥V₂) - ζ) ∈ dadeDomain Lsub A0)
    (hΘ : (ζ - star ζ) ∈ dadeDomain Lsub A0) :
    cfInner ((dadeMap hD ⟨hpc.primeTIrow τ (principalIrr ↥V₂) - ζ, hF⟩ : classFun H) : H → ℂ)
        ((dadeMap hD ⟨ζ - star ζ, hΘ⟩ : classFun H) : H → ℂ) = -1 := by
  rw [cfInner_dadeMap hD]
  exact cfInner_primeTIrow_sub_sub_star hpc hτ hζ hζ1 hζr

end LocalPairing

section PowerInvariance

omit [Fintype G] [Fintype ↥W] in
theorem powOp_prodChar (hW : IsCyclicTIPair W W1 W2) (lam : ↥W1 → ℂ) (mu : ↥W2 → ℂ) (k : ℕ) :
    powOp k (hW.prodChar lam mu) = hW.prodChar (powOp k lam) (powOp k mu) := by
  funext z
  rw [powOp_apply, hW.prodChar_apply, hW.prodChar_apply, map_pow]
  simp [powOp_apply]

omit [Fintype G] [Fintype ↥W] in
theorem powOp_coe_principalIrr (X : Type*) [Group X] (k : ℕ) :
    ((principalIrr X : Irr X) : X → ℂ) = powOp k ((principalIrr X : Irr X) : X → ℂ) := by
  funext x
  rw [powOp_apply, coe_principalIrr]
  rfl

omit [Fintype G] [Fintype ↥W] in
theorem powOpₗ_basisProdIrr (hW : IsCyclicTIPair W W1 W2) {k : ℕ}
    {i i' : Irr ↥W1} {j j' : Irr ↥W2}
    (hi : (i' : ↥W1 → ℂ) = powOp k (i : ↥W1 → ℂ))
    (hj : (j' : ↥W2 → ℂ) = powOp k (j : ↥W2 → ℂ)) :
    classFun.powOpₗ ↥W k (hW.basisProdIrr (i, j)) = hW.basisProdIrr (i', j') := by
  refine Subtype.ext ?_
  rw [classFun.coe_powOpₗ_apply, hW.coe_basisProdIrr_apply, hW.coe_basisProdIrr_apply,
    powOp_prodChar, hi, hj]

variable {ω' : classFun ↥W →ₗ[ℂ] classFun G}

theorem powOp_prodCharEta (hW : IsCyclicTIPair W W1 W2) (hω : IsCyclicTIIsometry W W1 W2 ω')
    {k : ℕ} (hk1 : 1 ≤ k) (hk : k.Coprime (Nat.card G)) {i i' : Irr ↥W1} {j j' : Irr ↥W2}
    (hi : (i' : ↥W1 → ℂ) = powOp k (i : ↥W1 → ℂ))
    (hj : (j' : ↥W2 → ℂ) = powOp k (j : ↥W2 → ℂ)) :
    hW.prodCharEta ω' i' j' = powOp k (hW.prodCharEta ω' i j) := by
  rw [hW.prodCharEta_eq_coe_apply, hW.prodCharEta_eq_coe_apply,
    ← powOpₗ_basisProdIrr hW hi hj, hω.coe_apply_powOpₗ hW hk1 hk]

theorem cfInner_prodCharEta_eq_of_ne_principal_left (hW : IsCyclicTIPair W W1 W2)
    (hω : IsCyclicTIIsometry W W1 W2 ω') (hq : (Nat.card ↥W1).Prime) {ψ : G → ℂ}
    (hpow : ∀ k : ℕ, 1 ≤ k → k.Coprime (Nat.card G) → ∀ (i : Irr ↥W1) (j : Irr ↥W2),
      cfInner ψ (powOp k (hW.prodCharEta ω' i j)) = cfInner ψ (hW.prodCharEta ω' i j))
    {i i' : Irr ↥W1} (hi : i ≠ principalIrr ↥W1) (hi' : i' ≠ principalIrr ↥W1) :
    cfInner ψ (hW.prodCharEta ω' i' (principalIrr ↥W2))
      = cfInner ψ (hW.prodCharEta ω' i (principalIrr ↥W2)) := by
  have hfin := hW.finite_left
  have hne0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  obtain ⟨k, hk1, hk, hkeq⟩ :=
    exists_pow_apply_eq_of_mem_Irr_of_natCard_eq_prime hq hne0 (C := ↥W1) rfl
      i.2 (coe_ne_one_of_ne_principalIrr (X := ↥W1) hi) i'.2
      (coe_ne_one_of_ne_principalIrr (X := ↥W1) hi')
  have hi'e : (i' : ↥W1 → ℂ) = powOp k (i : ↥W1 → ℂ) := funext fun c => by
    rw [powOp_apply]; exact hkeq c
  rw [powOp_prodCharEta hW hω hk1 hk hi'e (powOp_coe_principalIrr ↥W2 k)]
  exact hpow k hk1 hk i (principalIrr ↥W2)

theorem cfInner_prodCharEta_eq_of_ne_principal_right (hW : IsCyclicTIPair W W1 W2)
    (hω : IsCyclicTIIsometry W W1 W2 ω') (hp : (Nat.card ↥W2).Prime) {ψ : G → ℂ}
    (hpow : ∀ k : ℕ, 1 ≤ k → k.Coprime (Nat.card G) → ∀ (i : Irr ↥W1) (j : Irr ↥W2),
      cfInner ψ (powOp k (hW.prodCharEta ω' i j)) = cfInner ψ (hW.prodCharEta ω' i j))
    {j j' : Irr ↥W2} (hj : j ≠ principalIrr ↥W2) (hj' : j' ≠ principalIrr ↥W2) :
    cfInner ψ (hW.prodCharEta ω' (principalIrr ↥W1) j')
      = cfInner ψ (hW.prodCharEta ω' (principalIrr ↥W1) j) := by
  have hfin := hW.finite_right
  have hne0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
  obtain ⟨k, hk1, hk, hkeq⟩ :=
    exists_pow_apply_eq_of_mem_Irr_of_natCard_eq_prime hp hne0 (C := ↥W2) rfl
      j.2 (coe_ne_one_of_ne_principalIrr (X := ↥W2) hj) j'.2
      (coe_ne_one_of_ne_principalIrr (X := ↥W2) hj')
  have hj'e : (j' : ↥W2 → ℂ) = powOp k (j : ↥W2 → ℂ) := funext fun c => by
    rw [powOp_apply]; exact hkeq c
  rw [powOp_prodCharEta hW hω hk1 hk (powOp_coe_principalIrr ↥W1 k) hj'e]
  exact hpow k hk1 hk (principalIrr ↥W1) j

end PowerInvariance

section Main

variable [Fintype ↑(Irr ↥W1)] [Fintype ↑(Irr ↥W2)]
  (hW : IsCyclicTIPair W W1 W2) (hω : IsCyclicTIIsometry W W1 W2 ω)
  {ψ : G → ℂ} (hψ : ψ ∈ Submodule.span ℤ (Irr G))
  (hnorm : cfInner ψ ψ = (Nat.card ↥W1 : ℂ) + 1)
  (hV : ∀ v ∈ cyclicTIDiff W W1 W2, ψ v = 0)
  (h00 : cfInner ψ (hW.prodCharEta ω (principalIrr ↥W1) (principalIrr ↥W2)) = 1)
  (hq : (Nat.card ↥W1).Prime) (hp : (Nat.card ↥W2).Prime)
  (hpow : ∀ k : ℕ, 1 ≤ k → k.Coprime (Nat.card G) → ∀ (i : ↑(Irr ↥W1)) (j : ↑(Irr ↥W2)),
    cfInner ψ (powOp k (hW.prodCharEta ω i j)) = cfInner ψ (hW.prodCharEta ω i j))
  {Δ : G → ℂ} (hΔη : ∀ i j, cfInner Δ (hW.prodCharEta ω i j) = 0)
  (hΔψ : cfInner ψ Δ ≠ 0)

omit [Fintype ↥W] in
include hW hΔη hΔψ in
open scoped Classical in
theorem sub_sum_smul_prodCharEta_ne_zero :
    ψ - ∑ k : ↑(Irr ↥W1) × ↑(Irr ↥W2),
      cfInner ψ (hW.prodCharEta ω k.1 k.2) • hW.prodCharEta ω k.1 k.2 ≠ 0 := by
  intro hzero
  refine hΔψ ?_
  rw [sub_eq_zero.1 hzero, cfInner_sum_left]
  refine Finset.sum_eq_zero fun k _ => ?_
  have h : cfInner (hW.prodCharEta ω k.1 k.2) Δ = 0 := by
    rw [← conj_cfInner, hΔη k.1 k.2, map_zero]
  rw [cfInner_smul_left, h, mul_zero]

include hW hω hψ in
open scoped Classical in
theorem sub_sum_smul_prodCharEta_mem_span_Irr :
    ψ - ∑ k : ↑(Irr ↥W1) × ↑(Irr ↥W2),
        cfInner ψ (hW.prodCharEta ω k.1 k.2) • hW.prodCharEta ω k.1 k.2
      ∈ Submodule.span ℤ (Irr G) := by
  have hηmem : ∀ k : ↑(Irr ↥W1) × ↑(Irr ↥W2),
      hW.prodCharEta ω k.1 k.2 ∈ Submodule.span ℤ (Irr G) := fun k =>
    virtualChars_le_span_Irr (hW.prodCharEta_mem_virtualChars hω k.1 k.2)
  refine Submodule.sub_mem _ hψ (Submodule.sum_mem _ fun k _ => ?_)
  obtain ⟨m, hm⟩ := exists_int_cfInner_of_mem_span_Irr hψ (hηmem k)
  rw [hm, Int.cast_smul_eq_zsmul]
  exact Submodule.smul_mem _ _ (hηmem k)

include hW hω in
open scoped Classical in
theorem isOrthogonal_sub_sum_smul_prodCharEta (i : ↑(Irr ↥W1)) (j : ↑(Irr ↥W2)) :
    IsOrthogonal (ψ - ∑ k : ↑(Irr ↥W1) × ↑(Irr ↥W2),
        cfInner ψ (hW.prodCharEta ω k.1 k.2) • hW.prodCharEta ω k.1 k.2)
      (hW.prodCharEta ω i j) := by
  have hη : ∀ k l : ↑(Irr ↥W1) × ↑(Irr ↥W2),
      cfInner (hW.prodCharEta ω k.1 k.2) (hW.prodCharEta ω l.1 l.2) = if k = l then 1 else 0 :=
    fun k l => hW.cfInner_prodCharEta_pair hω k l
  rw [isOrthogonal_iff, cfInner_sub_left, cfInner_sum_left,
    Finset.sum_eq_single_of_mem (i, j) (Finset.mem_univ (i, j))
      (fun k _ hk => by rw [cfInner_smul_left, hη k (i, j), if_neg hk, mul_zero]),
    cfInner_smul_left, hη (i, j) (i, j), if_pos rfl, mul_one, sub_self]

include hW hω hψ hnorm hV h00 hq hp hpow hΔη hΔψ in
open scoped Classical in
theorem eq_prodCharEta_col_or_row :
    (∑ k : ↑(Irr ↥W1) × ↑(Irr ↥W2),
        cfInner ψ (hW.prodCharEta ω k.1 k.2) • hW.prodCharEta ω k.1 k.2
      = ∑ i : ↑(Irr ↥W1), hW.prodCharEta ω i (principalIrr ↥W2)) ∨
      (∑ k : ↑(Irr ↥W1) × ↑(Irr ↥W2),
          cfInner ψ (hW.prodCharEta ω k.1 k.2) • hW.prodCharEta ω k.1 k.2
        = ∑ j : ↑(Irr ↥W2), hW.prodCharEta ω (principalIrr ↥W1) j ∧
        Nat.card ↥W2 ≤ Nat.card ↥W1) := by
  have hcomm1 := hW.isMulCommutative_left
  have hcomm2 := hW.isMulCommutative_right
  have hfin1 := hW.finite_left
  have hfin2 := hW.finite_right
  have hcard1 : Fintype.card ↑(Irr ↥W1) = Nat.card ↥W1 := by
    rw [← Nat.card_eq_fintype_card, card_Irr_eq_card_of_isMulCommutative]
  have hcard2 : Fintype.card ↑(Irr ↥W2) = Nat.card ↥W2 := by
    rw [← Nat.card_eq_fintype_card, card_Irr_eq_card_of_isMulCommutative]
  obtain ⟨hq3, hp3, -⟩ := hW.card_Irr_ge
  rw [Nat.card_eq_fintype_card] at hq3 hp3
  have hψcf : ψ ∈ classFun G := mem_classFun_of_mem_span_Irr hψ
  obtain ⟨i₁, hi₁⟩ := Fintype.exists_ne_of_one_lt_card (by omega) (principalIrr ↥W1)
  obtain ⟨j₁, hj₁⟩ := Fintype.exists_ne_of_one_lt_card (by omega) (principalIrr ↥W2)
  have hs : ∀ i, i ≠ principalIrr ↥W1 → cfInner ψ (hW.prodCharEta ω i (principalIrr ↥W2))
      = cfInner ψ (hW.prodCharEta ω i₁ (principalIrr ↥W2)) := fun i hi =>
    cfInner_prodCharEta_eq_of_ne_principal_left hW hω hq hpow hi₁ hi
  have ht : ∀ j, j ≠ principalIrr ↥W2 → cfInner ψ (hW.prodCharEta ω (principalIrr ↥W1) j)
      = cfInner ψ (hW.prodCharEta ω (principalIrr ↥W1) j₁) := fun j hj =>
    cfInner_prodCharEta_eq_of_ne_principal_right hW hω hp hpow hj₁ hj
  have hadd : ∀ (i : ↑(Irr ↥W1)) (j : ↑(Irr ↥W2)),
      cfInner ψ (hW.prodCharEta ω i j)
        = cfInner ψ (hW.prodCharEta ω i (principalIrr ↥W2))
          + cfInner ψ (hW.prodCharEta ω (principalIrr ↥W1) j) - 1 := by
    intro i j
    have h := hW.cfInner_prodCharEta_exchange hω hψcf hV i j
    rw [h00] at h
    linear_combination h
  have hmain := eq_col_sum_or_eq_row_sum_of_cfInner_eq_ite
    (η := fun k : ↑(Irr ↥W1) × ↑(Irr ↥W2) => hW.prodCharEta ω k.1 k.2)
    (ψ := ψ) (s := cfInner ψ (hW.prodCharEta ω i₁ (principalIrr ↥W2)))
    (t := cfInner ψ (hW.prodCharEta ω (principalIrr ↥W1) j₁))
    (i₀ := principalIrr ↥W1) (j₀ := principalIrr ↥W2) hq3 hp3
    (fun k => virtualChars_le_span_Irr (hW.prodCharEta_mem_virtualChars hω k.1 k.2))
    (fun k l => hW.cfInner_prodCharEta_pair hω k l)
    hψ (by rw [hnorm, hcard1]) h00 hadd hs ht
    (sub_sum_smul_prodCharEta_ne_zero hW hΔη hΔψ)
  rcases hmain with h | ⟨h, hle⟩
  · exact Or.inl h
  · exact Or.inr ⟨h, by rw [← hcard1, ← hcard2]; exact hle⟩

include hW hω hψ hnorm hV h00 hq hp hpow hΔη hΔψ in
open scoped Classical in
theorem eq_prodCharEtaColSum_or_row :
    (∑ k : ↑(Irr ↥W1) × ↑(Irr ↥W2),
        cfInner ψ (hW.prodCharEta ω k.1 k.2) • hW.prodCharEta ω k.1 k.2
      = hW.prodCharEtaColSum ω (principalIrr ↥W2)) ∨
      (∑ k : ↑(Irr ↥W1) × ↑(Irr ↥W2),
          cfInner ψ (hW.prodCharEta ω k.1 k.2) • hW.prodCharEta ω k.1 k.2
        = ∑ j : ↑(Irr ↥W2), hW.prodCharEta ω (principalIrr ↥W1) j ∧
        Nat.card ↥W2 ≤ Nat.card ↥W1) := by
  rcases eq_prodCharEta_col_or_row hW hω hψ hnorm hV h00 hq hp hpow hΔη hΔψ with h | h
  · exact Or.inl (by rw [h, hW.prodCharEtaColSum_eq_sum])
  · exact Or.inr h

include hW hω hψ hnorm hV h00 hq hp hpow hΔη hΔψ in
open scoped Classical in
theorem axis_projection :
    ((∑ k : ↑(Irr ↥W1) × ↑(Irr ↥W2),
          cfInner ψ (hW.prodCharEta ω k.1 k.2) • hW.prodCharEta ω k.1 k.2
        = hW.prodCharEtaColSum ω (principalIrr ↥W2)) ∨
        (∑ k : ↑(Irr ↥W1) × ↑(Irr ↥W2),
            cfInner ψ (hW.prodCharEta ω k.1 k.2) • hW.prodCharEta ω k.1 k.2
          = ∑ j : ↑(Irr ↥W2), hW.prodCharEta ω (principalIrr ↥W1) j ∧
          Nat.card ↥W2 ≤ Nat.card ↥W1)) ∧
      (ψ - ∑ k : ↑(Irr ↥W1) × ↑(Irr ↥W2),
          cfInner ψ (hW.prodCharEta ω k.1 k.2) • hW.prodCharEta ω k.1 k.2 ≠ 0) ∧
      (ψ - ∑ k : ↑(Irr ↥W1) × ↑(Irr ↥W2),
          cfInner ψ (hW.prodCharEta ω k.1 k.2) • hW.prodCharEta ω k.1 k.2
        ∈ Submodule.span ℤ (Irr G)) ∧
      ∀ (i : ↑(Irr ↥W1)) (j : ↑(Irr ↥W2)),
        IsOrthogonal (ψ - ∑ k : ↑(Irr ↥W1) × ↑(Irr ↥W2),
            cfInner ψ (hW.prodCharEta ω k.1 k.2) • hW.prodCharEta ω k.1 k.2)
          (hW.prodCharEta ω i j) :=
  ⟨eq_prodCharEtaColSum_or_row hW hω hψ hnorm hV h00 hq hp hpow hΔη hΔψ,
    sub_sum_smul_prodCharEta_ne_zero hW hΔη hΔψ,
    sub_sum_smul_prodCharEta_mem_span_Irr hW hω hψ,
    isOrthogonal_sub_sum_smul_prodCharEta hW hω⟩

end Main

section DadeConfiguration

variable {L : Subgroup G} [Fintype ↥L] {Kn : Subgroup ↥L} [Kn.Normal] {Hd : Subgroup ↥Kn}
  {A0 : Set G} {T : G → Subgroup G} {S : Set (↥L → ℂ)}
  {ν : Submodule.span ℤ S →+ virtualChars G} {ζ : ↥L → ℂ}
  {V₁ V₂ : Subgroup ↥L} [Fintype ↥(V₁ ⊔ V₂)] [Fintype ↑(Irr ↥V₁)]
  {σ : classFun ↥(V₁ ⊔ V₂) →ₗ[ℂ] classFun ↥L}
  (hodd : Odd (Nat.card G)) (hW : IsCyclicTIPair W W1 W2)
  (hW2 : W2 ≤ Kn.map L.subtype) (hW1 : W1 ⊓ Kn.map L.subtype = ⊥)
  (hω : IsCyclicTIIsometry W W1 W2 ω) (hD : IsDadeData L A0 T)
  (hVA : cyclicTIDiff W W1 W2 ⊆ A0)
  (hS : S ⊆ indFamDetect Kn Hd) (hSstar : ∀ χ ∈ S, star χ ∈ S)
  (hνiso : ∀ f h : Submodule.span ℤ S,
    cfInner (ν f : G → ℂ) (ν h : G → ℂ) = cfInner (f : ↥L → ℂ) (h : ↥L → ℂ))
  (hS0 : ∀ (f : charSpanZero S) (x : ↥L), (x : G) ∉ A0 → (f : ↥L → ℂ) x = 0)
  (hντ : ∀ (f : Submodule.span ℤ S) (F : dadeDomain L A0), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
    (ν f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
  (hζS : ζ ∈ S) (hζIrr : ζ ∈ Irr ↥L)

omit [Fintype G] [Fintype ↥W] [Kn.Normal] in
include hSstar hζS in
theorem sub_star_mem_span_of_mem : ζ - star ζ ∈ Submodule.span ℤ S :=
  Submodule.sub_mem _ (Submodule.subset_span hζS) (Submodule.subset_span (hSstar _ hζS))

omit [Fintype G] [Fintype ↥W] [Kn.Normal] in
include hSstar hζS hζIrr in
theorem sub_star_mem_charSpanZero_of_mem : ζ - star ζ ∈ charSpanZero S := by
  refine mem_charSpanZero.2 ⟨sub_star_mem_span_of_mem hSstar hζS, ?_⟩
  have h := conj_apply_one_of_mem_Irr hζIrr
  simp only [Pi.sub_apply, Pi.star_apply, RCLike.star_def]
  rw [h]
  ring

omit [Fintype G] [Fintype ↥W] in
include hS hSstar hS0 hζS hζIrr in
theorem sub_star_mem_dadeDomain_of_mem : ζ - star ζ ∈ dadeDomain L A0 :=
  mem_dadeDomain.2
    ⟨Submodule.sub_mem _
        (mem_classFun_of_mem_span_indFamDetect hS (Submodule.subset_span hζS))
        (mem_classFun_of_mem_span_indFamDetect hS (Submodule.subset_span (hSstar _ hζS))),
      fun x hx => hS0 ⟨ζ - star ζ, sub_star_mem_charSpanZero_of_mem hSstar hζS hζIrr⟩ x hx⟩

include hodd hW hW2 hW1 hω hD hVA hS hSstar hνiso hS0 hντ hζS hζIrr in
theorem cfInner_dadeMap_sub_star_prodCharEta_eq_zero
    (hΘ : ζ - star ζ ∈ dadeDomain L A0) (i : ↑(Irr ↥W1)) (j : ↑(Irr ↥W2)) :
    cfInner ((dadeMap hD ⟨ζ - star ζ, hΘ⟩ : classFun G) : G → ℂ) (hW.prodCharEta ω i j) = 0 := by
  have hspan : ζ - star ζ ∈ Submodule.span ℤ S := sub_star_mem_span_of_mem hSstar hζS
  have hsub : (ν ⟨ζ - star ζ, hspan⟩ : G → ℂ)
      = ((dadeMap hD ⟨ζ - star ζ, hΘ⟩ : classFun G) : G → ℂ) := hντ _ _ rfl
  have hadd : (ν ⟨ζ - star ζ, hspan⟩ : G → ℂ)
      = (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ)
        - (ν ⟨star ζ, Submodule.subset_span (hSstar _ hζS)⟩ : G → ℂ) := by
    have hsplit : (⟨ζ - star ζ, hspan⟩ : Submodule.span ℤ S)
        = ⟨ζ, Submodule.subset_span hζS⟩
          - ⟨star ζ, Submodule.subset_span (hSstar _ hζS)⟩ := Subtype.ext rfl
    rw [hsplit, map_sub]
    rfl
  rw [← hsub, hadd, cfInner_sub_left,
    isOrthogonal_iff.1 (CoherentCore.isOrthogonal_nu_prodCharEta hodd hW hW2 hW1 hω hD hVA hS
      hSstar hνiso hS0 hντ hζS hζIrr i j),
    isOrthogonal_iff.1 (CoherentCore.isOrthogonal_nu_prodCharEta hodd hW hW2 hW1 hω hD hVA hS
      hSstar hνiso hS0 hντ (hSstar _ hζS) (star_mem_Irr hζIrr) i j), sub_zero]

variable [Fintype ↑(Irr ↥W1)] [Fintype ↑(Irr ↥W2)] {ψ : G → ℂ}

include hodd hW hW2 hW1 hω hD hVA hS hSstar hνiso hS0 hντ hζS hζIrr in
open scoped Classical in
theorem axis_projection_dadeMap (hpc : IsPrimeCyclicTIHyp Kn V₁ V₂)
    (hσ : IsCyclicTIIsometry (V₁ ⊔ V₂) V₁ V₂ σ) (hζ1 : ζ 1 ≠ 1)
    (hF : hpc.primeTIrow σ (principalIrr ↥V₂) - ζ ∈ dadeDomain L A0)
    (hψτ : ψ = ((dadeMap hD ⟨hpc.primeTIrow σ (principalIrr ↥V₂) - ζ, hF⟩ : classFun G) : G → ℂ))
    (hψ : ψ ∈ Submodule.span ℤ (Irr G))
    (hnorm : cfInner ψ ψ = (Nat.card ↥W1 : ℂ) + 1)
    (hV : ∀ v ∈ cyclicTIDiff W W1 W2, ψ v = 0)
    (h00 : cfInner ψ (hW.prodCharEta ω (principalIrr ↥W1) (principalIrr ↥W2)) = 1)
    (hq : (Nat.card ↥W1).Prime) (hp : (Nat.card ↥W2).Prime)
    (hpow : ∀ k : ℕ, 1 ≤ k → k.Coprime (Nat.card G) → ∀ (i : ↑(Irr ↥W1)) (j : ↑(Irr ↥W2)),
      cfInner ψ (powOp k (hW.prodCharEta ω i j)) = cfInner ψ (hW.prodCharEta ω i j)) :
    ((∑ k : ↑(Irr ↥W1) × ↑(Irr ↥W2),
          cfInner ψ (hW.prodCharEta ω k.1 k.2) • hW.prodCharEta ω k.1 k.2
        = hW.prodCharEtaColSum ω (principalIrr ↥W2)) ∨
        (∑ k : ↑(Irr ↥W1) × ↑(Irr ↥W2),
            cfInner ψ (hW.prodCharEta ω k.1 k.2) • hW.prodCharEta ω k.1 k.2
          = ∑ j : ↑(Irr ↥W2), hW.prodCharEta ω (principalIrr ↥W1) j ∧
          Nat.card ↥W2 ≤ Nat.card ↥W1)) ∧
      (ψ - ∑ k : ↑(Irr ↥W1) × ↑(Irr ↥W2),
          cfInner ψ (hW.prodCharEta ω k.1 k.2) • hW.prodCharEta ω k.1 k.2 ≠ 0) ∧
      (ψ - ∑ k : ↑(Irr ↥W1) × ↑(Irr ↥W2),
          cfInner ψ (hW.prodCharEta ω k.1 k.2) • hW.prodCharEta ω k.1 k.2
        ∈ Submodule.span ℤ (Irr G)) ∧
      ∀ (i : ↑(Irr ↥W1)) (j : ↑(Irr ↥W2)),
        IsOrthogonal (ψ - ∑ k : ↑(Irr ↥W1) × ↑(Irr ↥W2),
            cfInner ψ (hW.prodCharEta ω k.1 k.2) • hW.prodCharEta ω k.1 k.2)
          (hW.prodCharEta ω i j) := by
  have hΘ : ζ - star ζ ∈ dadeDomain L A0 :=
    sub_star_mem_dadeDomain_of_mem hS hSstar hS0 hζS hζIrr
  have hζr : star ζ ≠ ζ := CoherentCore.star_ne_self hodd hS hζS hζIrr
  refine axis_projection hW hω hψ hnorm hV h00 hq hp hpow
    (Δ := ((dadeMap hD ⟨ζ - star ζ, hΘ⟩ : classFun G) : G → ℂ))
    (fun i j => cfInner_dadeMap_sub_star_prodCharEta_eq_zero hodd hW hW2 hW1 hω hD hVA hS hSstar
      hνiso hS0 hντ hζS hζIrr hΘ i j) ?_
  rw [hψτ, cfInner_dadeMap_primeTIrow_sub_dadeMap_sub_star hpc hσ hD hζIrr hζ1 hζr hF hΘ]
  norm_num

end DadeConfiguration

end PrimeDadeAxis

end CFSG.FeitThompson

end
