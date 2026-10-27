module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2F4Descent
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Interface
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcF4Rational
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2F4Cocycle

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Helpers

variable {k : Type} [Field k]

theorem entrywiseFrobGL_mem_h1F4 (p : ℕ) [Fact p.Prime] [CharP k p] (e : ℕ) {g : ModGL .F4 k}
    (hg : g ∈ h1F4 k) : entrywiseFrobGL .F4 k p e g ∈ h1F4 k := by
  obtain ⟨n, hn, A, rfl⟩ := hg
  refine ⟨entrywiseFrobGL .F4 k p e n,
    baseChangeGL_mem_parabolicLevi (iterateFrobenius k p e) hn,
    Matrix.SpecialLinearGroup.map (iterateFrobenius k p e) A, ?_⟩
  rw [map_mul, entrywiseFrobGL_rootSL2 p e isRoot_thetaF4]

theorem mul_signDiagF4_theta_of_mem_h1F4 {g : ModGL .F4 k} (hg : g ∈ h1F4 k) :
    g * signDiagF4 k thetaF4 = signDiagF4 k thetaF4 * g := by
  obtain ⟨n, hn, A, rfl⟩ := hg
  have h1 : n * signDiagF4 k thetaF4 = signDiagF4 k thetaF4 * n :=
    (rootDiagUnit_corootDiagF4_comm_levi (-1 : kˣ) hn).symm
  have h2 : rootSL2 .F4 k thetaF4 A * signDiagF4 k thetaF4 =
      signDiagF4 k thetaF4 * rootSL2 .F4 k thetaF4 A := by
    have hd : signDiagF4 k thetaF4 = rootSL2 .F4 k thetaF4 (HSL (-1)) :=
      (rootTorusSL2_thetaF4 (-1)).symm
    rw [hd, ← map_mul, ← map_mul, HSL_neg_one_mul_comm_A2]
  calc n * rootSL2 .F4 k thetaF4 A * signDiagF4 k thetaF4 =
      n * (rootSL2 .F4 k thetaF4 A * signDiagF4 k thetaF4) := by group
    _ = n * (signDiagF4 k thetaF4 * rootSL2 .F4 k thetaF4 A) := by rw [h2]
    _ = (n * signDiagF4 k thetaF4) * rootSL2 .F4 k thetaF4 A := by group
    _ = (signDiagF4 k thetaF4 * n) * rootSL2 .F4 k thetaF4 A := by rw [h1]
    _ = _ := by group

end Helpers

section Main

theorem h1F4_le_adjointGroup {k : Type} [Field k] {g : ModGL .F4 k} (hg : g ∈ h1F4 k) :
    g ∈ adjointGroup .F4 k := by
  obtain ⟨n, hn, A, rfl⟩ := hg
  exact mul_mem (parabolicSubgroup_le_adjointGroup _ _ _
    (parabolicLevi_le_parabolicSubgroup JF4 hn)) (rootSL2_mem_adjointGroup _ A)

theorem exists_split_or_anti_F4 {p e : ℕ} [Fact p.Prime] [NeZero e] (hp2 : p ≠ 2)
    {c g : ModGL .F4 (GaloisField p e)} (hcG : c ∈ adjointGroup .F4 (GaloisField p e))
    (hgG : g ∈ adjointGroup .F4 (GaloisField p e)) (hc2 : c * c = 1)
    (hcd : c * signDiagF4 (GaloisField p e) thetaF4 = signDiagF4 (GaloisField p e) thetaF4 * c)
    (hgc : g * signDiagF4 (GaloisField p e) thetaF4 * g⁻¹ = c)
    (hnc : ¬ ∀ A : SL2 (GaloisField p e), c * rootSL2 .F4 (GaloisField p e) thetaF4 A =
      rootSL2 .F4 (GaloisField p e) thetaF4 A * c) :
    (∃ u ∈ adjointGroup .F4 (GaloisField p e),
      u * c * u⁻¹ = signDiagF4 (GaloisField p e) deltaF4 ∧
      u * signDiagF4 (GaloisField p e) thetaF4 = signDiagF4 (GaloisField p e) thetaF4 * u) ∨
    (∃ v ∈ h1F4 (AlgClosGF p e),
      v * baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e)) c * v⁻¹ =
        signDiagF4 (AlgClosGF p e) deltaF4 ∧
      ∃ m ∈ parabolicLevi .F4 (AlgClosGF p e) JF4,
        entrywiseFrobGL .F4 (AlgClosGF p e) p e v * v⁻¹ =
          m * rootSL2 .F4 (AlgClosGF p e) thetaF4 WSL) := by
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
  obtain ⟨-, hHR, -, -⟩ := exceptional_Lang_Frobenius_fixed_derived_root_group .F4
    (GaloisField p e) hK (AlgClosGF p e) Fr hFr
  set ι := algebraMap (GaloisField p e) (AlgClosGF p e) with hι
  set y := baseChangeGL ι c with hy_def
  set g' := baseChangeGL ι g with hg'_def
  have hycG : y ∈ adjointGroup .F4 (AlgClosGF p e) ⊓
      (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) :=
    hHR (Subgroup.mem_map_of_mem _ hcG)
  have hFy : entrywiseFrobGL .F4 (AlgClosGF p e) p e y = y := (Subgroup.mem_inf.1 hycG).2
  have hy2 : y * y = 1 := by rw [hy_def, ← map_mul, hc2, map_one]
  have hg'G : g' ∈ adjointGroup .F4 (AlgClosGF p e) := baseChangeGL_mem_adjointGroup ι hgG
  have hdθ : baseChangeGL ι (signDiagF4 (GaloisField p e) thetaF4) =
      signDiagF4 (AlgClosGF p e) thetaF4 := baseChangeGL_rootDiagUnit_corootDiagF4 ι thetaF4
  have hdδ : baseChangeGL ι (signDiagF4 (GaloisField p e) deltaF4) =
      signDiagF4 (AlgClosGF p e) deltaF4 := baseChangeGL_rootDiagUnit_corootDiagF4 ι deltaF4
  have hgy : g' * signDiagF4 (AlgClosGF p e) thetaF4 * g'⁻¹ = y := by
    rw [← hdθ, hg'_def, hy_def, ← hgc, map_mul, map_mul, map_inv]
  have hycom : y * signDiagF4 (AlgClosGF p e) thetaF4 =
      signDiagF4 (AlgClosGF p e) thetaF4 * y := by
    rw [← hdθ, hy_def, ← map_mul, ← map_mul, hcd]
  have hyH : y ∈ h1F4 (AlgClosGF p e) := by
    have hcT : y ∈ toralCentralizer .F4 (AlgClosGF p e)
        (corootDiagF4 thetaF4 (-1 : (AlgClosGF p e)ˣ)) := by
      rw [mem_toralCentralizer]
      refine ⟨(Subgroup.mem_inf.1 hycG).1, ?_⟩
      show signDiagF4 (AlgClosGF p e) thetaF4 * y * (signDiagF4 (AlgClosGF p e) thetaF4)⁻¹ = y
      rw [mul_inv_eq_iff_eq_mul, hycom]
    have hM := toralCentralizer_le_toralRootGroup_of_sign (Or.inr (Or.inl rfl)) hk
      (corootDiagF4_neg_one_sign thetaF4) hcT
    exact toralRootGroup_le_h1F4 hk hM
  have hnc' : ¬ ∀ A : SL2 (AlgClosGF p e), y * rootSL2 .F4 (AlgClosGF p e) thetaF4 A =
      rootSL2 .F4 (AlgClosGF p e) thetaF4 A * y := by
    intro h
    apply hnc
    intro A
    rw [commute_rootSL2_iff_pinnedX isRoot_thetaF4] at h
    refine (commute_rootSL2_iff_pinnedX isRoot_thetaF4 c).2 ⟨fun b => ?_, fun b => ?_⟩ A
    · apply baseChangeGL_injective ι
      rw [map_mul, map_mul, baseChangeGL_pinnedX]
      exact h.1 (ι b)
    · apply baseChangeGL_injective ι
      rw [map_mul, map_mul, baseChangeGL_pinnedX]
      exact h.2 (ι b)
  obtain ⟨v, hv, hvy⟩ := exists_conj_signDiag_deltaF4 halg hp2 hg'G hy2 hyH hgy hnc'
  have hFv : entrywiseFrobGL .F4 (AlgClosGF p e) p e v * v⁻¹ ∈ h1F4 (AlgClosGF p e) :=
    mul_mem (entrywiseFrobGL_mem_h1F4 p e hv) (inv_mem hv)
  have hFd : entrywiseFrobGL .F4 (AlgClosGF p e) p e (signDiagF4 (AlgClosGF p e) deltaF4) =
      signDiagF4 (AlgClosGF p e) deltaF4 :=
    entrywiseFrobGL_rootDiagUnit_of_sign p e (fun i => corootDiagF4_neg_one_sign deltaF4 i)
  have hud : (entrywiseFrobGL .F4 (AlgClosGF p e) p e v * v⁻¹) *
      signDiagF4 (AlgClosGF p e) deltaF4 =
      signDiagF4 (AlgClosGF p e) deltaF4 *
        (entrywiseFrobGL .F4 (AlgClosGF p e) p e v * v⁻¹) := by
    have hF1 : entrywiseFrobGL .F4 (AlgClosGF p e) p e v * y *
        (entrywiseFrobGL .F4 (AlgClosGF p e) p e v)⁻¹ = signDiagF4 (AlgClosGF p e) deltaF4 := by
      have := congrArg (entrywiseFrobGL .F4 (AlgClosGF p e) p e) hvy
      rw [map_mul, map_mul, map_inv, hFy, hFd] at this
      exact this
    have hy' : v⁻¹ * signDiagF4 (AlgClosGF p e) deltaF4 * v = y := by rw [← hvy]; group
    have h1 : (entrywiseFrobGL .F4 (AlgClosGF p e) p e v * v⁻¹) *
        signDiagF4 (AlgClosGF p e) deltaF4 *
        (entrywiseFrobGL .F4 (AlgClosGF p e) p e v * v⁻¹)⁻¹ =
        signDiagF4 (AlgClosGF p e) deltaF4 := by
      calc (entrywiseFrobGL .F4 (AlgClosGF p e) p e v * v⁻¹) *
          signDiagF4 (AlgClosGF p e) deltaF4 *
          (entrywiseFrobGL .F4 (AlgClosGF p e) p e v * v⁻¹)⁻¹ =
          entrywiseFrobGL .F4 (AlgClosGF p e) p e v *
            (v⁻¹ * signDiagF4 (AlgClosGF p e) deltaF4 * v) *
            (entrywiseFrobGL .F4 (AlgClosGF p e) p e v)⁻¹ := by group
        _ = _ := by rw [hy', hF1]
    calc (entrywiseFrobGL .F4 (AlgClosGF p e) p e v * v⁻¹) * signDiagF4 (AlgClosGF p e) deltaF4 =
        ((entrywiseFrobGL .F4 (AlgClosGF p e) p e v * v⁻¹) *
          signDiagF4 (AlgClosGF p e) deltaF4 *
          (entrywiseFrobGL .F4 (AlgClosGF p e) p e v * v⁻¹)⁻¹) *
          (entrywiseFrobGL .F4 (AlgClosGF p e) p e v * v⁻¹) := by group
      _ = _ := by rw [h1]
  rcases eq_levi_or_eq_levi_mul_WSL_F4 hk isPartnerF4_deltaF4 hFv hud with hJ | ⟨m, hm, hmu⟩
  · left
    obtain ⟨h, hh, hFh, hhy⟩ := exists_h1_fixed_conj_F4 p hp2 (Nat.pos_of_ne_zero (NeZero.ne e))
      isPartnerF4_deltaF4 hv hFy hvy hJ
    have hhG : h ∈ adjointGroup .F4 (AlgClosGF p e) := h1F4_le_adjointGroup hh
    obtain ⟨a, u₁, hu₁, hha⟩ := exists_rootDiagUnit_mul_of_frobenius_fixed .F4 Fr hFr hhG hFh
    obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.1 hu₁
    set D := baseChangeGL ι (rootDiagUnit .F4 a) with hD
    have hdiag : ∀ b : Fin (Tag.rank .F4) → (AlgClosGF p e)ˣ,
        D * rootDiagUnit .F4 b = rootDiagUnit .F4 b * D := fun b => by
      rw [hD, baseChangeGL_rootDiagUnit, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
    have hDi : ∀ b : Fin (Tag.rank .F4) → (AlgClosGF p e)ˣ,
        D⁻¹ * rootDiagUnit .F4 b = rootDiagUnit .F4 b * D⁻¹ := fun b => by
      have := hdiag b
      calc D⁻¹ * rootDiagUnit .F4 b = D⁻¹ * (rootDiagUnit .F4 b * D) * D⁻¹ := by group
        _ = D⁻¹ * (D * rootDiagUnit .F4 b) * D⁻¹ := by rw [this]
        _ = _ := by group
    refine ⟨u₀, hu₀, ?_, ?_⟩
    · apply baseChangeGL_injective ι
      rw [map_mul, map_mul, map_inv, hdδ]
      have h1 := hhy
      rw [hha] at h1
      calc baseChangeGL ι u₀ * y * (baseChangeGL ι u₀)⁻¹ =
          D⁻¹ * (D * baseChangeGL ι u₀ * y * (D * baseChangeGL ι u₀)⁻¹) * D := by group
        _ = D⁻¹ * signDiagF4 (AlgClosGF p e) deltaF4 * D := by rw [h1]
        _ = D⁻¹ * (D * signDiagF4 (AlgClosGF p e) deltaF4) := by
          have hdd : D * signDiagF4 (AlgClosGF p e) deltaF4 =
              signDiagF4 (AlgClosGF p e) deltaF4 * D := hdiag _
          rw [hdd, mul_assoc]
        _ = _ := by group
    · apply baseChangeGL_injective ι
      rw [map_mul, map_mul, hdθ]
      have e' : baseChangeGL ι u₀ = D⁻¹ * h := by rw [hha, inv_mul_cancel_left]
      rw [e']
      calc D⁻¹ * h * signDiagF4 (AlgClosGF p e) thetaF4 =
          D⁻¹ * (h * signDiagF4 (AlgClosGF p e) thetaF4) := by group
        _ = D⁻¹ * (signDiagF4 (AlgClosGF p e) thetaF4 * h) := by
          rw [mul_signDiagF4_theta_of_mem_h1F4 hh]
        _ = (D⁻¹ * signDiagF4 (AlgClosGF p e) thetaF4) * h := by group
        _ = (signDiagF4 (AlgClosGF p e) thetaF4 * D⁻¹) * h := by
          have hdd : D⁻¹ * signDiagF4 (AlgClosGF p e) thetaF4 =
              signDiagF4 (AlgClosGF p e) thetaF4 * D⁻¹ := hDi _
          rw [hdd]
        _ = _ := by group
  · right
    exact ⟨v, hv, hvy, m, hm, hmu⟩

end Main

end CFSG.ClassicalInvolution.ModelFacts.Levi
