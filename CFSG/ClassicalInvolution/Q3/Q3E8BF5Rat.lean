module

public import CFSG.ClassicalInvolution.ModelFacts.E7ModelLeviRat
public import CFSG.ClassicalInvolution.Q3.Q3E8BF5Desc

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.ClassicalInvolution.ModelFacts.E7Model

set_option linter.unusedSectionVars false


section Rational

variable {K : Type} [Field K] [Finite K]

theorem exists_rational_levi_conj_nj (hK : Odd (Nat.card K)) {J : Set (Fin (Tag.rank .E7))}
    {l : Fin (Tag.rank .E7) → ℤ} {B : ℕ} (hlJ : ∀ j ∈ J, iform l (Pi.single j 1) = 0)
    (hB : ∀ σ ∈ rootFinset .E7, |iform l σ| ≤ B)
    (hker : ∀ σ ∈ rootFinset .E7, iform l σ = 0 → σ ∈ parabolicRoots .E7 J)
    {c g : ModGL .E7 K} (hcG : c ∈ adjointGroup .E7 K) (hgG : g ∈ adjointGroup .E7 K)
    (hc2 : c * c = 1)
    (hcL : baseChangeGL (algebraMap K (AlgebraicClosure K)) c ∈
      parabolicLevi .E7 (AlgebraicClosure K) J)
    (hgc : g * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : Kˣ)) * g⁻¹ = c) :
    ∃ δ, IsRoot .E7 δ ∧ ∃ u ∈ adjointGroup .E7 K,
      u * c * u⁻¹ = rootDiagUnit .E7 (thetaDiag δ (-1 : Kˣ)) ∧
      (∀ b : Fin (Tag.rank .E7) → Kˣ, (∀ j ∈ J, b j = 1) →
        u * rootDiagUnit .E7 b = rootDiagUnit .E7 b * u) ∧
      ∃ a : Fin (Tag.rank .E7) → Kˣ, ∃ η ∈ NJ K J, u = rootDiagUnit .E7 a * η := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set k := AlgebraicClosure K
  set ι := algebraMap K k with hι
  set p := ringChar K with hp_def
  have hpK : CharP K p := ringChar.charP K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K p
  have : Fact p.Prime := ⟨hp⟩
  have : CharP k p := charP_of_injective_algebraMap (algebraMap K k).injective p
  have hp2 : p ≠ 2 := by
    intro h2
    rw [Nat.card_eq_fintype_card, hcard, h2] at hK
    exact Nat.not_even_iff_odd.2 hK ((Nat.even_pow' n.ne_zero).2 even_two)
  set Fr := iterateFrobenius k p n with hFr_def
  have hFr : ∀ x, Fr x = x ^ Nat.card K := fun x => by
    rw [hFr_def, iterateFrobenius_def, Nat.card_eq_fintype_card, hcard]
  have halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k := by
    let _ : Algebra (ZMod p) k := ZMod.algebra k p
    refine ⟨fun y => ?_⟩
    obtain ⟨E, hEf, hyE, -⟩ := exists_finite_subfield_of_finset (K := K) ({y} : Finset k)
    have hy : y ∈ E := hyE (Finset.mem_coe.2 (Finset.mem_singleton_self y))
    have : Fintype E := Fintype.ofFinite E
    have hpow : y ^ Fintype.card E = y := congrArg Subtype.val (FiniteField.pow_card (⟨y, hy⟩ : E))
    refine ⟨Polynomial.X ^ Fintype.card E - Polynomial.X,
      FiniteField.X_pow_card_sub_X_ne_zero (ZMod p) Fintype.one_lt_card, ?_⟩
    rw [map_sub, map_pow, Polynomial.aeval_X, hpow, sub_self]
  obtain ⟨-, hHR, -, -⟩ := exceptional_Lang_Frobenius_fixed_derived_root_group .E7 K hK k Fr hFr
  set y := baseChangeGL ι c with hy_def
  set g' := baseChangeGL ι g with hg'_def
  have hycG : y ∈ adjointGroup .E7 k ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) :=
    hHR (Subgroup.mem_map_of_mem _ hcG)
  have hFy : entrywiseFrobGL .E7 k p n y = y := (Subgroup.mem_inf.1 hycG).2
  have hy2 : y ^ 2 = 1 := by rw [hy_def, sq, ← map_mul, hc2, map_one]
  have hg'G : g' ∈ adjointGroup .E7 k := baseChangeGL_mem_adjointGroup ι hgG
  have hk : ringChar k ≠ 2 := by rw [ringChar.eq k p]; exact hp2
  obtain ⟨v, hv, a, ha, hva⟩ := exists_levi_conj_eq_rootDiagUnit hp2 k halg hcL hy2
  have hvg : v * g' ∈ adjointGroup .E7 k :=
    mul_mem (parabolicSubgroup_le_adjointGroup _ _ _ (parabolicLevi_le_parabolicSubgroup J hv)) hg'G
  have hgy : g' * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : kˣ)) * g'⁻¹ = y := by
    rw [hg'_def, hy_def, ← hgc, map_mul, map_mul, map_inv, baseChangeGL_rootDiagUnit_thetaDiag_E7]
  obtain ⟨δ, hδ, rfl⟩ := exists_root_of_conj_thetaDiag_E7 hk ha hvg
    (by rw [← hva, ← hgy]; group)
  obtain ⟨h, hhL, hFh, hhy⟩ := exists_levi_fixed_conj_G p hp2 n.pos hlJ hB hker hδ hv hFy hva
  have hhG : h ∈ adjointGroup .E7 k :=
    parabolicSubgroup_le_adjointGroup _ _ _ (parabolicLevi_le_parabolicSubgroup J hhL)
  obtain ⟨a', u, hu, hh⟩ := exists_rootDiagUnit_mul_of_frobenius_fixed .E7 Fr hFr hhG hFh
  obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.1 hu
  have hdiag : ∀ b b' : Fin (Tag.rank .E7) → kˣ,
      rootDiagUnit .E7 b * rootDiagUnit .E7 b' = rootDiagUnit .E7 b' * rootDiagUnit .E7 b :=
    fun b b' => by rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  set D := baseChangeGL ι (rootDiagUnit .E7 a') with hD
  have hDd : ∀ b : Fin (Tag.rank .E7) → kˣ,
      D * rootDiagUnit .E7 b = rootDiagUnit .E7 b * D := fun b => by
    rw [hD, baseChangeGL_rootDiagUnit]
    exact hdiag _ _
  refine ⟨δ, hδ, u₀, hu₀, ?_, ?_, ?_⟩
  · apply baseChangeGL_injective ι
    rw [map_mul, map_mul, map_inv, baseChangeGL_rootDiagUnit_thetaDiag_E7]
    have h1 := hhy
    rw [hh] at h1
    calc baseChangeGL ι u₀ * y * (baseChangeGL ι u₀)⁻¹ =
        D⁻¹ * (D * baseChangeGL ι u₀ * y * (D * baseChangeGL ι u₀)⁻¹) * D := by group
      _ = D⁻¹ * rootDiagUnit .E7 (thetaDiag δ (-1 : kˣ)) * D := by rw [h1]
      _ = D⁻¹ * (rootDiagUnit .E7 (thetaDiag δ (-1 : kˣ)) * D) := by group
      _ = D⁻¹ * (D * rootDiagUnit .E7 (thetaDiag δ (-1 : kˣ))) := by rw [hDd]
      _ = _ := by group
  · intro b hb
    apply baseChangeGL_injective ι
    rw [map_mul, map_mul, baseChangeGL_rootDiagUnit]
    have hc' := rootDiagUnit_comm_levi_of_one (J := J)
      (b := fun i => Units.map (ι : K →+* k).toMonoidHom (b i))
      (fun j hj => by simp [hb j hj]) hhL
    have hDi : D⁻¹ * rootDiagUnit .E7 (fun i => Units.map (ι : K →+* k).toMonoidHom (b i)) =
        rootDiagUnit .E7 (fun i => Units.map (ι : K →+* k).toMonoidHom (b i)) * D⁻¹ := by
      have := hDd (fun i => Units.map (ι : K →+* k).toMonoidHom (b i))
      calc D⁻¹ * rootDiagUnit .E7 (fun i => Units.map (ι : K →+* k).toMonoidHom (b i)) =
          D⁻¹ * (rootDiagUnit .E7 (fun i => Units.map (ι : K →+* k).toMonoidHom (b i)) * D) *
            D⁻¹ := by group
        _ = D⁻¹ * (D * rootDiagUnit .E7 (fun i => Units.map (ι : K →+* k).toMonoidHom (b i))) *
            D⁻¹ := by rw [this]
        _ = _ := by group
    have e : baseChangeGL ι u₀ = D⁻¹ * h := by rw [hh, inv_mul_cancel_left]
    rw [e]
    calc D⁻¹ * h * rootDiagUnit .E7 (fun i => Units.map (ι : K →+* k).toMonoidHom (b i)) =
        D⁻¹ * (h * rootDiagUnit .E7 (fun i => Units.map (ι : K →+* k).toMonoidHom (b i))) := by
          group
      _ = D⁻¹ * (rootDiagUnit .E7 (fun i => Units.map (ι : K →+* k).toMonoidHom (b i)) * h) := by
          rw [← hc']
      _ = (D⁻¹ * rootDiagUnit .E7 (fun i => Units.map (ι : K →+* k).toMonoidHom (b i))) * h := by
          group
      _ = (rootDiagUnit .E7 (fun i => Units.map (ι : K →+* k).toMonoidHom (b i)) * D⁻¹) * h := by
          rw [hDi]
      _ = _ := by group
  · have e : baseChangeGL ι u₀ = D⁻¹ * h := by rw [hh, inv_mul_cancel_left]
    have hDT : D ∈ torusGroup .E7 k := by
      rw [hD, baseChangeGL_rootDiagUnit]
      exact rootDiagUnit_mem_torusGroup _
    have hmem : baseChangeGL ι u₀ ∈ parabolicLevi .E7 k J := by
      rw [e]
      exact mul_mem (inv_mem (torusGroup_le_parabolicLevi J hDT)) hhL
    exact mem_rational_levi_of_baseChange Fr hFr hmem

end Rational

end CFSG.ClassicalInvolution.Q3.Q3W
