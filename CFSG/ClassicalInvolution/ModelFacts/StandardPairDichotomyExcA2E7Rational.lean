module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E7Descent
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Interface
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E7Cocycle

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Helpers

variable {k : Type} [Field k]

theorem entrywiseFrobGL_mem_h1E7 (p : ℕ) [Fact p.Prime] [CharP k p] (e : ℕ) {g : ModGL .E7 k}
    (hg : g ∈ h1E7 k) : entrywiseFrobGL .E7 k p e g ∈ h1E7 k := by
  obtain ⟨n, hn, A, rfl⟩ := hg
  refine ⟨entrywiseFrobGL .E7 k p e n,
    baseChangeGL_mem_parabolicLevi (iterateFrobenius k p e) hn,
    Matrix.SpecialLinearGroup.map (iterateFrobenius k p e) A, ?_⟩
  rw [map_mul, entrywiseFrobGL_rootSL2 p e isRoot_thetaE7]

theorem mul_signDiagE7_theta_of_mem_h1E7 {g : ModGL .E7 k} (hg : g ∈ h1E7 k) :
    g * signDiagE7 k thetaE7 = signDiagE7 k thetaE7 * g := by
  obtain ⟨n, hn, A, rfl⟩ := hg
  have h1 : n * signDiagE7 k thetaE7 = signDiagE7 k thetaE7 * n :=
    (rootDiagUnit_thetaDiag_comm_levi_E7 (-1 : kˣ) hn).symm
  have h2 : rootSL2 .E7 k thetaE7 A * signDiagE7 k thetaE7 =
      signDiagE7 k thetaE7 * rootSL2 .E7 k thetaE7 A := by
    have hd : signDiagE7 k thetaE7 = rootSL2 .E7 k thetaE7 (HSL (-1)) :=
      (rootTorusSL2_thetaE7 (-1)).symm
    rw [hd, ← map_mul, ← map_mul, HSL_neg_one_mul_comm_A2]
  calc n * rootSL2 .E7 k thetaE7 A * signDiagE7 k thetaE7 =
      n * (rootSL2 .E7 k thetaE7 A * signDiagE7 k thetaE7) := by group
    _ = n * (signDiagE7 k thetaE7 * rootSL2 .E7 k thetaE7 A) := by rw [h2]
    _ = (n * signDiagE7 k thetaE7) * rootSL2 .E7 k thetaE7 A := by group
    _ = (signDiagE7 k thetaE7 * n) * rootSL2 .E7 k thetaE7 A := by rw [h1]
    _ = _ := by group

end Helpers

section Main

theorem h1E7_le_adjointGroup {k : Type} [Field k] {g : ModGL .E7 k} (hg : g ∈ h1E7 k) :
    g ∈ adjointGroup .E7 k := by
  obtain ⟨n, hn, A, rfl⟩ := hg
  exact mul_mem (parabolicSubgroup_le_adjointGroup _ _ _
    (parabolicLevi_le_parabolicSubgroup JE7 hn)) (rootSL2_mem_adjointGroup _ A)

theorem exists_split_or_anti_E7 {p e : ℕ} [Fact p.Prime] [NeZero e] (hp2 : p ≠ 2)
    {c g : ModGL .E7 (GaloisField p e)} (hcG : c ∈ adjointGroup .E7 (GaloisField p e))
    (hgG : g ∈ adjointGroup .E7 (GaloisField p e)) (hc2 : c * c = 1)
    (hcd : c * signDiagE7 (GaloisField p e) thetaE7 = signDiagE7 (GaloisField p e) thetaE7 * c)
    (hgc : g * signDiagE7 (GaloisField p e) thetaE7 * g⁻¹ = c)
    (hnc : ¬ ∀ A : SL2 (GaloisField p e), c * rootSL2 .E7 (GaloisField p e) thetaE7 A =
      rootSL2 .E7 (GaloisField p e) thetaE7 A * c) :
    (∃ u ∈ adjointGroup .E7 (GaloisField p e),
      u * c * u⁻¹ = signDiagE7 (GaloisField p e) deltaE7 ∧
      u * signDiagE7 (GaloisField p e) thetaE7 = signDiagE7 (GaloisField p e) thetaE7 * u) ∨
    (∃ v ∈ h1E7 (AlgClosGF p e),
      v * baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e)) c * v⁻¹ =
        signDiagE7 (AlgClosGF p e) deltaE7 ∧
      ∃ m ∈ parabolicLevi .E7 (AlgClosGF p e) JE7,
        entrywiseFrobGL .E7 (AlgClosGF p e) p e v * v⁻¹ =
          m * rootSL2 .E7 (AlgClosGF p e) thetaE7 WSL) := by
  classical
  have hcard : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (NeZero.ne e)
  have hK : Odd (Nat.card (GaloisField p e)) := by
    rw [hcard]
    exact (Fact.out : p.Prime).odd_of_ne_two hp2 |>.pow
  have hk : ringChar (AlgClosGF p e) ≠ 2 := by
    rw [ringChar.eq (AlgClosGF p e) p]
    exact hp2
  set Fr := iterateFrobenius (AlgClosGF p e) p e with hFr_def
  have hFr : ∀ x, Fr x = x ^ Nat.card (GaloisField p e) := fun x => by
    rw [hFr_def, iterateFrobenius_def, hcard]
  have halg : letI := ZMod.algebra (AlgClosGF p e) p;
      Algebra.IsAlgebraic (ZMod p) (AlgClosGF p e) := by
    let _ : Algebra (ZMod p) (AlgClosGF p e) := ZMod.algebra (AlgClosGF p e) p
    refine ⟨fun y => ?_⟩
    obtain ⟨E, hEf, hyE, -⟩ := exists_finite_subfield_of_finset (K := GaloisField p e)
      ({y} : Finset (AlgClosGF p e))
    have hy : y ∈ E := hyE (Finset.mem_coe.2 (Finset.mem_singleton_self y))
    have : Fintype E := Fintype.ofFinite E
    have hpow : y ^ Fintype.card E = y :=
      congrArg Subtype.val (FiniteField.pow_card (⟨y, hy⟩ : E))
    refine ⟨Polynomial.X ^ Fintype.card E - Polynomial.X,
      FiniteField.X_pow_card_sub_X_ne_zero (ZMod p) Fintype.one_lt_card, ?_⟩
    rw [map_sub, map_pow, Polynomial.aeval_X, hpow, sub_self]
  obtain ⟨-, hHR, -, -⟩ := exceptional_Lang_Frobenius_fixed_derived_root_group .E7
    (GaloisField p e) hK (AlgClosGF p e) Fr hFr
  set ι := algebraMap (GaloisField p e) (AlgClosGF p e) with hι
  set y := baseChangeGL ι c with hy_def
  set g' := baseChangeGL ι g with hg'_def
  have hycG : y ∈ adjointGroup .E7 (AlgClosGF p e) ⊓
      (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) :=
    hHR (Subgroup.mem_map_of_mem _ hcG)
  have hFy : entrywiseFrobGL .E7 (AlgClosGF p e) p e y = y := (Subgroup.mem_inf.1 hycG).2
  have hy2 : y * y = 1 := by rw [hy_def, ← map_mul, hc2, map_one]
  have hg'G : g' ∈ adjointGroup .E7 (AlgClosGF p e) := baseChangeGL_mem_adjointGroup ι hgG
  have hdθ : baseChangeGL ι (signDiagE7 (GaloisField p e) thetaE7) =
      signDiagE7 (AlgClosGF p e) thetaE7 := baseChangeGL_rootDiagUnit_thetaDiag_E7 ι thetaE7
  have hdδ : baseChangeGL ι (signDiagE7 (GaloisField p e) deltaE7) =
      signDiagE7 (AlgClosGF p e) deltaE7 := baseChangeGL_rootDiagUnit_thetaDiag_E7 ι deltaE7
  have hgy : g' * signDiagE7 (AlgClosGF p e) thetaE7 * g'⁻¹ = y := by
    rw [← hdθ, hg'_def, hy_def, ← hgc, map_mul, map_mul, map_inv]
  have hycom : y * signDiagE7 (AlgClosGF p e) thetaE7 =
      signDiagE7 (AlgClosGF p e) thetaE7 * y := by
    rw [← hdθ, hy_def, ← map_mul, ← map_mul, hcd]
  have hyH : y ∈ h1E7 (AlgClosGF p e) := by
    have hcT : y ∈ toralCentralizer .E7 (AlgClosGF p e)
        (thetaDiag thetaE7 (-1 : (AlgClosGF p e)ˣ)) := by
      rw [mem_toralCentralizer]
      refine ⟨(Subgroup.mem_inf.1 hycG).1, ?_⟩
      show signDiagE7 (AlgClosGF p e) thetaE7 * y * (signDiagE7 (AlgClosGF p e) thetaE7)⁻¹ = y
      rw [mul_inv_eq_iff_eq_mul, hycom]
    have hM := toralCentralizer_le_toralRootGroup_thetaE7 hk hcT
    exact toralRootGroup_le_h1E7 hk hM
  have hnc' : ¬ ∀ A : SL2 (AlgClosGF p e), y * rootSL2 .E7 (AlgClosGF p e) thetaE7 A =
      rootSL2 .E7 (AlgClosGF p e) thetaE7 A * y := by
    intro h
    apply hnc
    intro A
    rw [commute_rootSL2_iff_pinnedX isRoot_thetaE7] at h
    refine (commute_rootSL2_iff_pinnedX isRoot_thetaE7 c).2 ⟨fun b => ?_, fun b => ?_⟩ A
    · apply baseChangeGL_injective ι
      rw [map_mul, map_mul, baseChangeGL_pinnedX]
      exact h.1 (ι b)
    · apply baseChangeGL_injective ι
      rw [map_mul, map_mul, baseChangeGL_pinnedX]
      exact h.2 (ι b)
  obtain ⟨v, hv, hvy⟩ := exists_conj_signDiag_deltaE7 halg hp2 hg'G hy2 hyH hgy hnc'
  have hFv : entrywiseFrobGL .E7 (AlgClosGF p e) p e v * v⁻¹ ∈ h1E7 (AlgClosGF p e) :=
    mul_mem (entrywiseFrobGL_mem_h1E7 p e hv) (inv_mem hv)
  have hFd : entrywiseFrobGL .E7 (AlgClosGF p e) p e (signDiagE7 (AlgClosGF p e) deltaE7) =
      signDiagE7 (AlgClosGF p e) deltaE7 :=
    entrywiseFrobGL_rootDiagUnit_of_sign p e (thetaDiag_neg_one_sign_E7 deltaE7)
  have hud : (entrywiseFrobGL .E7 (AlgClosGF p e) p e v * v⁻¹) *
      signDiagE7 (AlgClosGF p e) deltaE7 =
      signDiagE7 (AlgClosGF p e) deltaE7 *
        (entrywiseFrobGL .E7 (AlgClosGF p e) p e v * v⁻¹) := by
    have hF1 : entrywiseFrobGL .E7 (AlgClosGF p e) p e v * y *
        (entrywiseFrobGL .E7 (AlgClosGF p e) p e v)⁻¹ = signDiagE7 (AlgClosGF p e) deltaE7 := by
      have := congrArg (entrywiseFrobGL .E7 (AlgClosGF p e) p e) hvy
      rw [map_mul, map_mul, map_inv, hFy, hFd] at this
      exact this
    have hy' : v⁻¹ * signDiagE7 (AlgClosGF p e) deltaE7 * v = y := by rw [← hvy]; group
    have h1 : (entrywiseFrobGL .E7 (AlgClosGF p e) p e v * v⁻¹) *
        signDiagE7 (AlgClosGF p e) deltaE7 *
        (entrywiseFrobGL .E7 (AlgClosGF p e) p e v * v⁻¹)⁻¹ =
        signDiagE7 (AlgClosGF p e) deltaE7 := by
      calc (entrywiseFrobGL .E7 (AlgClosGF p e) p e v * v⁻¹) *
          signDiagE7 (AlgClosGF p e) deltaE7 *
          (entrywiseFrobGL .E7 (AlgClosGF p e) p e v * v⁻¹)⁻¹ =
          entrywiseFrobGL .E7 (AlgClosGF p e) p e v *
            (v⁻¹ * signDiagE7 (AlgClosGF p e) deltaE7 * v) *
            (entrywiseFrobGL .E7 (AlgClosGF p e) p e v)⁻¹ := by group
        _ = _ := by rw [hy', hF1]
    calc (entrywiseFrobGL .E7 (AlgClosGF p e) p e v * v⁻¹) * signDiagE7 (AlgClosGF p e) deltaE7 =
        ((entrywiseFrobGL .E7 (AlgClosGF p e) p e v * v⁻¹) *
          signDiagE7 (AlgClosGF p e) deltaE7 *
          (entrywiseFrobGL .E7 (AlgClosGF p e) p e v * v⁻¹)⁻¹) *
          (entrywiseFrobGL .E7 (AlgClosGF p e) p e v * v⁻¹) := by group
      _ = _ := by rw [h1]
  rcases eq_levi_or_eq_levi_mul_WSL_E7 hk isPartnerE7_deltaE7 hFv hud with hJ | ⟨m, hm, hmu⟩
  · left
    obtain ⟨h, hh, hFh, hhy⟩ := exists_h1_fixed_conj_E7 p hp2 (Nat.pos_of_ne_zero (NeZero.ne e))
      isPartnerE7_deltaE7 hv hFy hvy hJ
    have hhG : h ∈ adjointGroup .E7 (AlgClosGF p e) := h1E7_le_adjointGroup hh
    obtain ⟨a, u₁, hu₁, hha⟩ := exists_rootDiagUnit_mul_of_frobenius_fixed .E7 Fr hFr hhG hFh
    obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.1 hu₁
    set D := baseChangeGL ι (rootDiagUnit .E7 a) with hD
    have hdiag : ∀ b : Fin (Tag.rank .E7) → (AlgClosGF p e)ˣ,
        D * rootDiagUnit .E7 b = rootDiagUnit .E7 b * D := fun b => by
      rw [hD, baseChangeGL_rootDiagUnit, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
    have hDi : ∀ b : Fin (Tag.rank .E7) → (AlgClosGF p e)ˣ,
        D⁻¹ * rootDiagUnit .E7 b = rootDiagUnit .E7 b * D⁻¹ := fun b => by
      have := hdiag b
      calc D⁻¹ * rootDiagUnit .E7 b = D⁻¹ * (rootDiagUnit .E7 b * D) * D⁻¹ := by group
        _ = D⁻¹ * (D * rootDiagUnit .E7 b) * D⁻¹ := by rw [this]
        _ = _ := by group
    refine ⟨u₀, hu₀, ?_, ?_⟩
    · apply baseChangeGL_injective ι
      rw [map_mul, map_mul, map_inv, hdδ]
      have h1 := hhy
      rw [hha] at h1
      calc baseChangeGL ι u₀ * y * (baseChangeGL ι u₀)⁻¹ =
          D⁻¹ * (D * baseChangeGL ι u₀ * y * (D * baseChangeGL ι u₀)⁻¹) * D := by group
        _ = D⁻¹ * signDiagE7 (AlgClosGF p e) deltaE7 * D := by rw [h1]
        _ = D⁻¹ * (D * signDiagE7 (AlgClosGF p e) deltaE7) := by
          have hdd : D * signDiagE7 (AlgClosGF p e) deltaE7 =
              signDiagE7 (AlgClosGF p e) deltaE7 * D := hdiag _
          rw [hdd, mul_assoc]
        _ = _ := by group
    · apply baseChangeGL_injective ι
      rw [map_mul, map_mul, hdθ]
      have e' : baseChangeGL ι u₀ = D⁻¹ * h := by rw [hha, inv_mul_cancel_left]
      rw [e']
      calc D⁻¹ * h * signDiagE7 (AlgClosGF p e) thetaE7 =
          D⁻¹ * (h * signDiagE7 (AlgClosGF p e) thetaE7) := by group
        _ = D⁻¹ * (signDiagE7 (AlgClosGF p e) thetaE7 * h) := by
          rw [mul_signDiagE7_theta_of_mem_h1E7 hh]
        _ = (D⁻¹ * signDiagE7 (AlgClosGF p e) thetaE7) * h := by group
        _ = (signDiagE7 (AlgClosGF p e) thetaE7 * D⁻¹) * h := by
          have hdd : D⁻¹ * signDiagE7 (AlgClosGF p e) thetaE7 =
              signDiagE7 (AlgClosGF p e) thetaE7 * D⁻¹ := hDi _
          rw [hdd]
        _ = _ := by group
  · right
    exact ⟨v, hv, hvy, m, hm, hmu⟩

end Main

end CFSG.ClassicalInvolution.ModelFacts.Levi
