module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E8Descent
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Interface
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Rational
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E8Cocycle

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Helpers

variable {k : Type} [Field k]

theorem entrywiseFrobGL_mem_h1E8 (p : ℕ) [Fact p.Prime] [CharP k p] (e : ℕ) {g : ModGL .E8 k}
    (hg : g ∈ h1E8 k) : entrywiseFrobGL .E8 k p e g ∈ h1E8 k := by
  obtain ⟨n, hn, A, rfl⟩ := hg
  refine ⟨entrywiseFrobGL .E8 k p e n,
    baseChangeGL_mem_parabolicLevi (iterateFrobenius k p e) hn,
    Matrix.SpecialLinearGroup.map (iterateFrobenius k p e) A, ?_⟩
  rw [map_mul, entrywiseFrobGL_rootSL2 p e isRoot_thetaE8]

theorem mul_signDiagE8_theta_of_mem_h1E8 {g : ModGL .E8 k} (hg : g ∈ h1E8 k) :
    g * signDiagE8 k thetaE8 = signDiagE8 k thetaE8 * g := by
  obtain ⟨n, hn, A, rfl⟩ := hg
  have h1 : n * signDiagE8 k thetaE8 = signDiagE8 k thetaE8 * n :=
    (rootDiagUnit_thetaDiag_comm_levi (-1 : kˣ) hn).symm
  have h2 : rootSL2 .E8 k thetaE8 A * signDiagE8 k thetaE8 =
      signDiagE8 k thetaE8 * rootSL2 .E8 k thetaE8 A := by
    have hd : signDiagE8 k thetaE8 = rootSL2 .E8 k thetaE8 (HSL (-1)) :=
      (rootTorusSL2_thetaE8 (-1)).symm
    rw [hd, ← map_mul, ← map_mul, HSL_neg_one_mul_comm_A2]
  calc n * rootSL2 .E8 k thetaE8 A * signDiagE8 k thetaE8 =
      n * (rootSL2 .E8 k thetaE8 A * signDiagE8 k thetaE8) := by group
    _ = n * (signDiagE8 k thetaE8 * rootSL2 .E8 k thetaE8 A) := by rw [h2]
    _ = (n * signDiagE8 k thetaE8) * rootSL2 .E8 k thetaE8 A := by group
    _ = (signDiagE8 k thetaE8 * n) * rootSL2 .E8 k thetaE8 A := by rw [h1]
    _ = _ := by group

end Helpers

section Main

theorem h1E8_le_adjointGroup {k : Type} [Field k] {g : ModGL .E8 k} (hg : g ∈ h1E8 k) :
    g ∈ adjointGroup .E8 k := by
  obtain ⟨n, hn, A, rfl⟩ := hg
  exact mul_mem (parabolicSubgroup_le_adjointGroup _ _ _
    (parabolicLevi_le_parabolicSubgroup JE8 hn)) (rootSL2_mem_adjointGroup _ A)

theorem exists_split_or_anti_E8 {p e : ℕ} [Fact p.Prime] [NeZero e] (hp2 : p ≠ 2)
    {c g : ModGL .E8 (GaloisField p e)} (hcG : c ∈ adjointGroup .E8 (GaloisField p e))
    (hgG : g ∈ adjointGroup .E8 (GaloisField p e)) (hc2 : c * c = 1)
    (hcd : c * signDiagE8 (GaloisField p e) thetaE8 = signDiagE8 (GaloisField p e) thetaE8 * c)
    (hgc : g * signDiagE8 (GaloisField p e) thetaE8 * g⁻¹ = c)
    (hnc : ¬ ∀ A : SL2 (GaloisField p e), c * rootSL2 .E8 (GaloisField p e) thetaE8 A =
      rootSL2 .E8 (GaloisField p e) thetaE8 A * c) :
    (∃ u ∈ adjointGroup .E8 (GaloisField p e),
      u * c * u⁻¹ = signDiagE8 (GaloisField p e) deltaE8 ∧
      u * signDiagE8 (GaloisField p e) thetaE8 = signDiagE8 (GaloisField p e) thetaE8 * u) ∨
    (∃ v ∈ h1E8 (AlgClosGF p e),
      v * baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e)) c * v⁻¹ =
        signDiagE8 (AlgClosGF p e) deltaE8 ∧
      ∃ m ∈ parabolicLevi .E8 (AlgClosGF p e) JE8,
        entrywiseFrobGL .E8 (AlgClosGF p e) p e v * v⁻¹ =
          m * rootSL2 .E8 (AlgClosGF p e) thetaE8 WSL) := by
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
  obtain ⟨-, hHR, -, -⟩ := exceptional_Lang_Frobenius_fixed_derived_root_group .E8
    (GaloisField p e) hK (AlgClosGF p e) Fr hFr
  set ι := algebraMap (GaloisField p e) (AlgClosGF p e) with hι
  set y := baseChangeGL ι c with hy_def
  set g' := baseChangeGL ι g with hg'_def
  have hycG : y ∈ adjointGroup .E8 (AlgClosGF p e) ⊓
      (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) :=
    hHR (Subgroup.mem_map_of_mem _ hcG)
  have hFy : entrywiseFrobGL .E8 (AlgClosGF p e) p e y = y := (Subgroup.mem_inf.1 hycG).2
  have hy2 : y * y = 1 := by rw [hy_def, ← map_mul, hc2, map_one]
  have hg'G : g' ∈ adjointGroup .E8 (AlgClosGF p e) := baseChangeGL_mem_adjointGroup ι hgG
  have hdθ : baseChangeGL ι (signDiagE8 (GaloisField p e) thetaE8) =
      signDiagE8 (AlgClosGF p e) thetaE8 := baseChangeGL_rootDiagUnit_thetaDiag ι thetaE8
  have hdδ : baseChangeGL ι (signDiagE8 (GaloisField p e) deltaE8) =
      signDiagE8 (AlgClosGF p e) deltaE8 := baseChangeGL_rootDiagUnit_thetaDiag ι deltaE8
  have hgy : g' * signDiagE8 (AlgClosGF p e) thetaE8 * g'⁻¹ = y := by
    rw [← hdθ, hg'_def, hy_def, ← hgc, map_mul, map_mul, map_inv]
  have hycom : y * signDiagE8 (AlgClosGF p e) thetaE8 =
      signDiagE8 (AlgClosGF p e) thetaE8 * y := by
    rw [← hdθ, hy_def, ← map_mul, ← map_mul, hcd]
  have hyH : y ∈ h1E8 (AlgClosGF p e) := by
    have hcT : y ∈ toralCentralizer .E8 (AlgClosGF p e)
        (thetaDiag thetaE8 (-1 : (AlgClosGF p e)ˣ)) := by
      rw [mem_toralCentralizer]
      refine ⟨(Subgroup.mem_inf.1 hycG).1, ?_⟩
      show signDiagE8 (AlgClosGF p e) thetaE8 * y * (signDiagE8 (AlgClosGF p e) thetaE8)⁻¹ = y
      rw [mul_inv_eq_iff_eq_mul, hycom]
    have hM := toralCentralizer_le_toralRootGroup_of_sign (Or.inr (Or.inr (Or.inr rfl))) hk
      (thetaDiag_neg_one_sign thetaE8) hcT
    exact toralRootGroup_le_h1E8 hk hM
  have hnc' : ¬ ∀ A : SL2 (AlgClosGF p e), y * rootSL2 .E8 (AlgClosGF p e) thetaE8 A =
      rootSL2 .E8 (AlgClosGF p e) thetaE8 A * y := by
    intro h
    apply hnc
    intro A
    rw [commute_rootSL2_iff_pinnedX isRoot_thetaE8] at h
    refine (commute_rootSL2_iff_pinnedX isRoot_thetaE8 c).2 ⟨fun b => ?_, fun b => ?_⟩ A
    · apply baseChangeGL_injective ι
      rw [map_mul, map_mul, baseChangeGL_pinnedX]
      exact h.1 (ι b)
    · apply baseChangeGL_injective ι
      rw [map_mul, map_mul, baseChangeGL_pinnedX]
      exact h.2 (ι b)
  obtain ⟨v, hv, hvy⟩ := exists_conj_signDiag_deltaE8 halg hp2 hg'G hy2 hyH hgy hnc'
  have hFv : entrywiseFrobGL .E8 (AlgClosGF p e) p e v * v⁻¹ ∈ h1E8 (AlgClosGF p e) :=
    mul_mem (entrywiseFrobGL_mem_h1E8 p e hv) (inv_mem hv)
  have hFd : entrywiseFrobGL .E8 (AlgClosGF p e) p e (signDiagE8 (AlgClosGF p e) deltaE8) =
      signDiagE8 (AlgClosGF p e) deltaE8 :=
    entrywiseFrobGL_rootDiagUnit_of_sign p e (thetaDiag_neg_one_sign deltaE8)
  have hud : (entrywiseFrobGL .E8 (AlgClosGF p e) p e v * v⁻¹) *
      signDiagE8 (AlgClosGF p e) deltaE8 =
      signDiagE8 (AlgClosGF p e) deltaE8 *
        (entrywiseFrobGL .E8 (AlgClosGF p e) p e v * v⁻¹) := by
    have hF1 : entrywiseFrobGL .E8 (AlgClosGF p e) p e v * y *
        (entrywiseFrobGL .E8 (AlgClosGF p e) p e v)⁻¹ = signDiagE8 (AlgClosGF p e) deltaE8 := by
      have := congrArg (entrywiseFrobGL .E8 (AlgClosGF p e) p e) hvy
      rw [map_mul, map_mul, map_inv, hFy, hFd] at this
      exact this
    have hy' : v⁻¹ * signDiagE8 (AlgClosGF p e) deltaE8 * v = y := by rw [← hvy]; group
    have h1 : (entrywiseFrobGL .E8 (AlgClosGF p e) p e v * v⁻¹) *
        signDiagE8 (AlgClosGF p e) deltaE8 *
        (entrywiseFrobGL .E8 (AlgClosGF p e) p e v * v⁻¹)⁻¹ =
        signDiagE8 (AlgClosGF p e) deltaE8 := by
      calc (entrywiseFrobGL .E8 (AlgClosGF p e) p e v * v⁻¹) *
          signDiagE8 (AlgClosGF p e) deltaE8 *
          (entrywiseFrobGL .E8 (AlgClosGF p e) p e v * v⁻¹)⁻¹ =
          entrywiseFrobGL .E8 (AlgClosGF p e) p e v *
            (v⁻¹ * signDiagE8 (AlgClosGF p e) deltaE8 * v) *
            (entrywiseFrobGL .E8 (AlgClosGF p e) p e v)⁻¹ := by group
        _ = _ := by rw [hy', hF1]
    calc (entrywiseFrobGL .E8 (AlgClosGF p e) p e v * v⁻¹) * signDiagE8 (AlgClosGF p e) deltaE8 =
        ((entrywiseFrobGL .E8 (AlgClosGF p e) p e v * v⁻¹) *
          signDiagE8 (AlgClosGF p e) deltaE8 *
          (entrywiseFrobGL .E8 (AlgClosGF p e) p e v * v⁻¹)⁻¹) *
          (entrywiseFrobGL .E8 (AlgClosGF p e) p e v * v⁻¹) := by group
      _ = _ := by rw [h1]
  rcases eq_levi_or_eq_levi_mul_WSL_E8 hk isPartnerE8_deltaE8 hFv hud with hJ | ⟨m, hm, hmu⟩
  · left
    obtain ⟨h, hh, hFh, hhy⟩ := exists_h1_fixed_conj_E8 p hp2 (Nat.pos_of_ne_zero (NeZero.ne e))
      isPartnerE8_deltaE8 hv hFy hvy hJ
    have hhG : h ∈ adjointGroup .E8 (AlgClosGF p e) := h1E8_le_adjointGroup hh
    obtain ⟨a, u₁, hu₁, hha⟩ := exists_rootDiagUnit_mul_of_frobenius_fixed .E8 Fr hFr hhG hFh
    obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.1 hu₁
    set D := baseChangeGL ι (rootDiagUnit .E8 a) with hD
    have hdiag : ∀ b : Fin (Tag.rank .E8) → (AlgClosGF p e)ˣ,
        D * rootDiagUnit .E8 b = rootDiagUnit .E8 b * D := fun b => by
      rw [hD, baseChangeGL_rootDiagUnit, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
    have hDi : ∀ b : Fin (Tag.rank .E8) → (AlgClosGF p e)ˣ,
        D⁻¹ * rootDiagUnit .E8 b = rootDiagUnit .E8 b * D⁻¹ := fun b => by
      have := hdiag b
      calc D⁻¹ * rootDiagUnit .E8 b = D⁻¹ * (rootDiagUnit .E8 b * D) * D⁻¹ := by group
        _ = D⁻¹ * (D * rootDiagUnit .E8 b) * D⁻¹ := by rw [this]
        _ = _ := by group
    refine ⟨u₀, hu₀, ?_, ?_⟩
    · apply baseChangeGL_injective ι
      rw [map_mul, map_mul, map_inv, hdδ]
      have h1 := hhy
      rw [hha] at h1
      calc baseChangeGL ι u₀ * y * (baseChangeGL ι u₀)⁻¹ =
          D⁻¹ * (D * baseChangeGL ι u₀ * y * (D * baseChangeGL ι u₀)⁻¹) * D := by group
        _ = D⁻¹ * signDiagE8 (AlgClosGF p e) deltaE8 * D := by rw [h1]
        _ = D⁻¹ * (D * signDiagE8 (AlgClosGF p e) deltaE8) := by
          have hdd : D * signDiagE8 (AlgClosGF p e) deltaE8 =
              signDiagE8 (AlgClosGF p e) deltaE8 * D := hdiag _
          rw [hdd, mul_assoc]
        _ = _ := by group
    · apply baseChangeGL_injective ι
      rw [map_mul, map_mul, hdθ]
      have e' : baseChangeGL ι u₀ = D⁻¹ * h := by rw [hha, inv_mul_cancel_left]
      rw [e']
      calc D⁻¹ * h * signDiagE8 (AlgClosGF p e) thetaE8 =
          D⁻¹ * (h * signDiagE8 (AlgClosGF p e) thetaE8) := by group
        _ = D⁻¹ * (signDiagE8 (AlgClosGF p e) thetaE8 * h) := by
          rw [mul_signDiagE8_theta_of_mem_h1E8 hh]
        _ = (D⁻¹ * signDiagE8 (AlgClosGF p e) thetaE8) * h := by group
        _ = (signDiagE8 (AlgClosGF p e) thetaE8 * D⁻¹) * h := by
          have hdd : D⁻¹ * signDiagE8 (AlgClosGF p e) thetaE8 =
              signDiagE8 (AlgClosGF p e) thetaE8 * D⁻¹ := hDi _
          rw [hdd]
        _ = _ := by group
  · right
    exact ⟨v, hv, hvy, m, hm, hmu⟩

end Main

end CFSG.ClassicalInvolution.ModelFacts.Levi
