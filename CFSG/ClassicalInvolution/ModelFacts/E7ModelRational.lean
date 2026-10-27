module

public import CFSG.ClassicalInvolution.ModelFacts.E7ModelStab
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE7Rational

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E7Model

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts.Levi

section Glue

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem uSL_inv_eq {F : Type} [Field F] (z : F) : (uSL z : SL2 F)⁻¹ = uSL (-z) := by
  rw [inv_eq_iff_mul_eq_one]
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_uSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem exists_levi_fixed_conj_adj_E7
    (halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) (hp2 : p ≠ 2) {e : ℕ}
    (he : 1 ≤ e) {y g : ModGL .E7 k} (hy : y ∈ parabolicLevi .E7 k JE7) (hy2 : y ^ 2 = 1)
    (hFy : entrywiseFrobGL .E7 k p e y = y) (hg : g ∈ adjointGroup .E7 k)
    (hgy : g * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : kˣ)) * g⁻¹ = y)
    (hyU : y * rootSL2 .E7 k thetaE7 (uSL 1) * y⁻¹ = (rootSL2 .E7 k thetaE7 (uSL 1))⁻¹) :
    ∃ δ, IsRoot .E7 δ ∧ (iform thetaE7 δ = 1 ∨ iform thetaE7 δ = -1) ∧
      ∃ h ∈ parabolicLevi .E7 k JE7, entrywiseFrobGL .E7 k p e h = h ∧
        h * y * h⁻¹ = rootDiagUnit .E7 (thetaDiag δ (-1 : kˣ)) := by
  have hk : ringChar k ≠ 2 := by rw [ringChar.eq k p]; exact hp2
  have hk2 : (-1 : kˣ) ≠ 1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hk (by simpa using congrArg Units.val h)
  obtain ⟨v, hv, a, ha, hva⟩ := exists_levi_conj_eq_rootDiagUnit hp2 k halg hy hy2
  have hvg : v * g ∈ adjointGroup .E7 k :=
    mul_mem (parabolicSubgroup_le_adjointGroup _ _ _ (parabolicLevi_le_parabolicSubgroup JE7 hv)) hg
  obtain ⟨δ, hδ, rfl⟩ := exists_root_of_conj_thetaDiag_E7 hk ha hvg
    (by rw [← hva, ← hgy]; group)
  obtain ⟨l, hu, -⟩ := exists_levi_conj_rootSL2_thetaE7 hv
  have hinj : Function.Injective (rootSL2 .E7 k thetaE7) :=
    ((exceptional_Lang_root_rank_one_data .E7 k thetaE7).2.2.2.2.2.2.2.1 hk).1
  have hχ : rootChar (thetaDiag δ (-1 : kˣ)) thetaE7 = -1 := by
    have h1 : rootDiagUnit .E7 (thetaDiag δ (-1 : kˣ)) *
          rootSL2 .E7 k thetaE7 (uSL ((l : k) * 1)) *
          (rootDiagUnit .E7 (thetaDiag δ (-1 : kˣ)))⁻¹ =
        rootSL2 .E7 k thetaE7 (uSL (-((l : k) * 1))) := by
      rw [← hu 1, ← hva, ← uSL_inv_eq, map_inv, ← hu 1]
      calc v * y * v⁻¹ * (v * rootSL2 .E7 k thetaE7 (uSL 1) * v⁻¹) * (v * y * v⁻¹)⁻¹ =
          v * (y * rootSL2 .E7 k thetaE7 (uSL 1) * y⁻¹) * v⁻¹ := by group
        _ = v * (rootSL2 .E7 k thetaE7 (uSL 1))⁻¹ * v⁻¹ := by rw [hyU]
        _ = _ := by group
    have h2 := (rootDiagUnit_conj_rootSL2 (thetaDiag δ (-1 : kˣ)) isRoot_thetaE7
      ((l : k) * 1)).1
    rw [h2] at h1
    have h3 := uSL_injective_of_field (hinj h1)
    have hl : (l : k) * 1 ≠ 0 := by simp
    have h4 : ((rootChar (thetaDiag δ (-1 : kˣ)) thetaE7 : kˣ) : k) = ((-1 : kˣ) : k) := by
      have : (rootChar (thetaDiag δ (-1 : kˣ)) thetaE7 : k) * ((l : k) * 1) =
          (-1 : k) * ((l : k) * 1) := by rw [h3]; ring
      simpa using mul_right_cancel₀ hl this
    exact Units.ext h4
  have hodd : Odd (iform thetaE7 δ) := by
    rw [rootChar_thetaDiag] at hχ
    rcases Int.even_or_odd (iform δ thetaE7) with hev | hodd
    · exfalso
      rw [hev.neg_one_zpow] at hχ
      exact hk2 hχ.symm
    · rwa [iform_comm]
  have hδθ : iform thetaE7 δ = 1 ∨ iform thetaE7 δ = -1 := by
    have hb := abs_iform_le_two_E7 isRoot_thetaE7 hδ
    rw [abs_le] at hb
    obtain ⟨m, hm⟩ := hodd
    omega
  exact ⟨δ, hδ, hδθ, exists_levi_fixed_conj_E7_adj p hp2 he hδ hδθ hv hFy hva⟩

end Glue

section Rational

variable {K : Type} [Field K] [Finite K]

theorem exists_rational_conj_e7_adj (hK : Odd (Nat.card K)) {c g : ModGL .E7 K}
    (hcG : c ∈ adjointGroup .E7 K) (hgG : g ∈ adjointGroup .E7 K) (hc2 : c * c = 1)
    (hcL : c ∈ parabolicLevi .E7 K JE7)
    (hcU : c * rootSL2 .E7 K thetaE7 (uSL 1) * c⁻¹ = (rootSL2 .E7 K thetaE7 (uSL 1))⁻¹)
    (hgc : g * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : Kˣ)) * g⁻¹ = c) :
    ∃ δ, IsRoot .E7 δ ∧ (iform thetaE7 δ = 1 ∨ iform thetaE7 δ = -1) ∧
      ∃ u ∈ adjointGroup .E7 K,
        u * c * u⁻¹ = rootDiagUnit .E7 (thetaDiag δ (-1 : Kˣ)) ∧
        u * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : Kˣ)) =
          rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : Kˣ)) * u := by
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
  have hyL : y ∈ parabolicLevi .E7 k JE7 := baseChangeGL_mem_parabolicLevi ι hcL
  have hg'G : g' ∈ adjointGroup .E7 k := baseChangeGL_mem_adjointGroup ι hgG
  have hgy : g' * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : kˣ)) * g'⁻¹ = y := by
    rw [hg'_def, hy_def, ← hgc, map_mul, map_mul, map_inv, baseChangeGL_rootDiagUnit_thetaDiag_E7]
  have hyU : y * rootSL2 .E7 k thetaE7 (uSL 1) * y⁻¹ = (rootSL2 .E7 k thetaE7 (uSL 1))⁻¹ := by
    rw [hy_def, ← baseChangeGL_rootSL2_uSL_one_E7 ι, ← map_inv, ← map_mul, ← map_inv, ← map_mul,
      hcU]
  have hn1 : 1 ≤ (n : ℕ) := n.pos
  obtain ⟨δ, hδ, hδθ, h, hhL, hFh, hhy⟩ :=
    exists_levi_fixed_conj_adj_E7 halg hp2 hn1 hyL hy2 hFy hg'G hgy hyU
  have hhG : h ∈ adjointGroup .E7 k :=
    parabolicSubgroup_le_adjointGroup _ _ _ (parabolicLevi_le_parabolicSubgroup JE7 hhL)
  obtain ⟨a, u, hu, hh⟩ := exists_rootDiagUnit_mul_of_frobenius_fixed .E7 Fr hFr hhG hFh
  obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.1 hu
  have hdiag : ∀ b b' : Fin (Tag.rank .E7) → kˣ,
      rootDiagUnit .E7 b * rootDiagUnit .E7 b' = rootDiagUnit .E7 b' * rootDiagUnit .E7 b :=
    fun b b' => by rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  set D := baseChangeGL ι (rootDiagUnit .E7 a) with hD
  have hDd : ∀ b : Fin (Tag.rank .E7) → kˣ,
      D * rootDiagUnit .E7 b = rootDiagUnit .E7 b * D := fun b => by
    rw [hD, baseChangeGL_rootDiagUnit]
    exact hdiag _ _
  refine ⟨δ, hδ, hδθ, u₀, hu₀, ?_, ?_⟩
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
  · apply baseChangeGL_injective ι
    rw [map_mul, map_mul, baseChangeGL_rootDiagUnit_thetaDiag_E7]
    have hc := rootDiagUnit_thetaDiag_comm_levi_E7 (-1 : kˣ) hhL
    have hDi : D⁻¹ * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : kˣ)) =
        rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : kˣ)) * D⁻¹ := by
      have := hDd (thetaDiag thetaE7 (-1 : kˣ))
      calc D⁻¹ * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : kˣ)) =
          D⁻¹ * (rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : kˣ)) * D) * D⁻¹ := by group
        _ = D⁻¹ * (D * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : kˣ))) * D⁻¹ := by rw [this]
        _ = _ := by group
    have e : baseChangeGL ι u₀ = D⁻¹ * h := by rw [hh, inv_mul_cancel_left]
    rw [e]
    calc D⁻¹ * h * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : kˣ)) =
        D⁻¹ * (h * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : kˣ))) := by group
      _ = D⁻¹ * (rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : kˣ)) * h) := by rw [← hc]
      _ = (D⁻¹ * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : kˣ))) * h := by group
      _ = (rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : kˣ)) * D⁻¹) * h := by rw [hDi]
      _ = _ := by group

end Rational

end CFSG.ClassicalInvolution.ModelFacts.E7Model
