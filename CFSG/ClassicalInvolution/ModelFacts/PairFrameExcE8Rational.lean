module

public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Class
public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Base

variable {K L : Type} [Field K] [Field L]

theorem map_thetaDiag (f : K →+* L) (δ : Fin (Tag.rank .E8) → ℤ) :
    (fun i => Units.map f.toMonoidHom (thetaDiag δ (-1 : Kˣ) i)) = thetaDiag δ (-1 : Lˣ) := by
  funext i
  simp only [thetaDiag, map_zpow]
  congr 1
  exact Units.ext (by simp)

theorem baseChangeGL_rootDiagUnit_thetaDiag (f : K →+* L) (δ : Fin (Tag.rank .E8) → ℤ) :
    baseChangeGL f (rootDiagUnit .E8 (thetaDiag δ (-1 : Kˣ))) =
      rootDiagUnit .E8 (thetaDiag δ (-1 : Lˣ)) := by
  rw [baseChangeGL_rootDiagUnit, map_thetaDiag]

theorem baseChangeGL_rootSL2_uSL_one (f : K →+* L) :
    baseChangeGL f (rootSL2 .E8 K thetaE8 (uSL 1)) = rootSL2 .E8 L thetaE8 (uSL 1) := by
  rw [rootSL2_uSL_eq, rootSL2_uSL_eq, baseChangeGL_pinnedX]
  congr 1
  rw [map_zsmul, map_one]

end Base

section Rational

variable {K : Type} [Field K] [Finite K]

theorem exists_rational_conj_e8 (hK : Odd (Nat.card K)) {c g : ModGL .E8 K}
    (hcG : c ∈ adjointGroup .E8 K) (hgG : g ∈ adjointGroup .E8 K) (hc2 : c * c = 1)
    (hcL : c ∈ parabolicLevi .E8 K JE8)
    (hcU : c * rootSL2 .E8 K thetaE8 (uSL 1) = rootSL2 .E8 K thetaE8 (uSL 1) * c)
    (hgc : g * rootDiagUnit .E8 (thetaDiag thetaE8 (-1 : Kˣ)) * g⁻¹ = c) :
    c = rootDiagUnit .E8 (thetaDiag thetaE8 (-1 : Kˣ)) ∨
      ∃ δ, IsRoot .E8 δ ∧ ∃ u ∈ adjointGroup .E8 K,
        u * c * u⁻¹ = rootDiagUnit .E8 (thetaDiag δ (-1 : Kˣ)) ∧
        u * rootDiagUnit .E8 (thetaDiag thetaE8 (-1 : Kˣ)) =
          rootDiagUnit .E8 (thetaDiag thetaE8 (-1 : Kˣ)) * u := by
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
  obtain ⟨-, hHR, -, -⟩ := exceptional_Lang_Frobenius_fixed_derived_root_group .E8 K hK k Fr hFr
  set y := baseChangeGL ι c with hy_def
  set g' := baseChangeGL ι g with hg'_def
  have hycG : y ∈ adjointGroup .E8 k ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) :=
    hHR (Subgroup.mem_map_of_mem _ hcG)
  have hFy : entrywiseFrobGL .E8 k p n y = y := (Subgroup.mem_inf.1 hycG).2
  have hy2 : y ^ 2 = 1 := by rw [hy_def, sq, ← map_mul, hc2, map_one]
  have hyL : y ∈ parabolicLevi .E8 k JE8 := baseChangeGL_mem_parabolicLevi ι hcL
  have hg'G : g' ∈ adjointGroup .E8 k := baseChangeGL_mem_adjointGroup ι hgG
  have hgy : g' * rootDiagUnit .E8 (thetaDiag thetaE8 (-1 : kˣ)) * g'⁻¹ = y := by
    rw [hg'_def, hy_def, ← hgc, map_mul, map_mul, map_inv, baseChangeGL_rootDiagUnit_thetaDiag]
  have hyU : y * rootSL2 .E8 k thetaE8 (uSL 1) = rootSL2 .E8 k thetaE8 (uSL 1) * y := by
    rw [hy_def, ← baseChangeGL_rootSL2_uSL_one ι, ← map_mul, ← map_mul, hcU]
  have hn1 : 1 ≤ (n : ℕ) := n.pos
  rcases exists_levi_fixed_conj_or_eq_thetaDiag halg hp2 hn1 hyL hy2 hFy hg'G hgy hyU with
    hyd | ⟨δ, hδ, -, h, hhL, hFh, hhy⟩
  · left
    apply baseChangeGL_injective ι
    rw [← hy_def, hyd, baseChangeGL_rootDiagUnit_thetaDiag]
  · right
    have hhG : h ∈ adjointGroup .E8 k :=
      parabolicSubgroup_le_adjointGroup _ _ _ (parabolicLevi_le_parabolicSubgroup JE8 hhL)
    obtain ⟨a, u, hu, hh⟩ := exists_rootDiagUnit_mul_of_frobenius_fixed .E8 Fr hFr hhG hFh
    obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.1 hu
    have hdiag : ∀ b b' : Fin (Tag.rank .E8) → kˣ,
        rootDiagUnit .E8 b * rootDiagUnit .E8 b' = rootDiagUnit .E8 b' * rootDiagUnit .E8 b :=
      fun b b' => by rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
    set D := baseChangeGL ι (rootDiagUnit .E8 a) with hD
    have hDd : ∀ b : Fin (Tag.rank .E8) → kˣ,
        D * rootDiagUnit .E8 b = rootDiagUnit .E8 b * D := fun b => by
      rw [hD, baseChangeGL_rootDiagUnit]
      exact hdiag _ _
    refine ⟨δ, hδ, u₀, hu₀, ?_, ?_⟩
    · apply baseChangeGL_injective ι
      rw [map_mul, map_mul, map_inv, baseChangeGL_rootDiagUnit_thetaDiag]
      have h1 := hhy
      rw [hh] at h1
      calc baseChangeGL ι u₀ * y * (baseChangeGL ι u₀)⁻¹ =
          D⁻¹ * (D * baseChangeGL ι u₀ * y * (D * baseChangeGL ι u₀)⁻¹) * D := by group
        _ = D⁻¹ * rootDiagUnit .E8 (thetaDiag δ (-1 : kˣ)) * D := by rw [h1]
        _ = D⁻¹ * (rootDiagUnit .E8 (thetaDiag δ (-1 : kˣ)) * D) := by group
        _ = D⁻¹ * (D * rootDiagUnit .E8 (thetaDiag δ (-1 : kˣ))) := by rw [hDd]
        _ = _ := by group
    · apply baseChangeGL_injective ι
      rw [map_mul, map_mul, baseChangeGL_rootDiagUnit_thetaDiag]
      have hc := rootDiagUnit_thetaDiag_comm_levi (-1 : kˣ) hhL
      have hDi : D⁻¹ * rootDiagUnit .E8 (thetaDiag thetaE8 (-1 : kˣ)) =
          rootDiagUnit .E8 (thetaDiag thetaE8 (-1 : kˣ)) * D⁻¹ := by
        have := hDd (thetaDiag thetaE8 (-1 : kˣ))
        calc D⁻¹ * rootDiagUnit .E8 (thetaDiag thetaE8 (-1 : kˣ)) =
            D⁻¹ * (rootDiagUnit .E8 (thetaDiag thetaE8 (-1 : kˣ)) * D) * D⁻¹ := by group
          _ = D⁻¹ * (D * rootDiagUnit .E8 (thetaDiag thetaE8 (-1 : kˣ))) * D⁻¹ := by rw [this]
          _ = _ := by group
      have e : baseChangeGL ι u₀ = D⁻¹ * h := by rw [hh, inv_mul_cancel_left]
      rw [e]
      calc D⁻¹ * h * rootDiagUnit .E8 (thetaDiag thetaE8 (-1 : kˣ)) =
          D⁻¹ * (h * rootDiagUnit .E8 (thetaDiag thetaE8 (-1 : kˣ))) := by group
        _ = D⁻¹ * (rootDiagUnit .E8 (thetaDiag thetaE8 (-1 : kˣ)) * h) := by rw [← hc]
        _ = (D⁻¹ * rootDiagUnit .E8 (thetaDiag thetaE8 (-1 : kˣ))) * h := by group
        _ = (rootDiagUnit .E8 (thetaDiag thetaE8 (-1 : kˣ)) * D⁻¹) * h := by rw [hDi]
        _ = _ := by group

end Rational

end CFSG.ClassicalInvolution.ModelFacts.Levi
