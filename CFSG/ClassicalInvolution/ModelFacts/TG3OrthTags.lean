module

public import CFSG.ClassicalInvolution.ModelFacts.TG3OrthTwin
public import CFSG.ClassicalInvolution.ModelFacts.CF3SpinOdd
public import CFSG.ClassicalInvolution.ModelFacts.CF3SpinPlus
public import CFSG.ClassicalInvolution.ModelFacts.CF3SpinMinus
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinStd
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofOrthWitt
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE6
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE7
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcF4Main
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryCocycleGen
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryHom

public section

namespace CFSG.ClassicalInvolution.ModelFacts.TG3

open CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Models.Transfer CFSG.LieType.CurtisTits
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local notation "𝔽₃" => GaloisField 3 1

section Odd

variable {n : ℕ}

theorem spinCtx3_odd (hn3 : 3 ≤ n) (k₀ : Fin n) (hk₀ : k₀.val = 0)
    (hsingle : FundamentalSingleClass .POmegaOdd (oddDatum n 𝔽₃))
    (hlong : IsLongestRoot (oddDatum n 𝔽₃) (Pi.single k₀ 1))
    (hG3 : ∀ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum n 𝔽₃), Gen3 R)
    (hsl2 : ∀ R ∈ fundamentalSubgroups .POmegaOdd (oddDatum n 𝔽₃), Nonempty (R ≃* SL(2, 𝔽₃))) :
    SpinCtx3 (quadOdd n 𝔽₃) (fundamentalSubgroups .POmegaOdd (oddDatum n 𝔽₃)) := by
  classical
  have hodd := odd_natCard_galoisField_three
  have h2 : (2 : 𝔽₃) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have : Invertible (2 : 𝔽₃) := invertibleOfNonzero h2
  have hQ : (quadOdd n 𝔽₃).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadOdd n 𝔽₃ h2)
  have : Nonempty (Fin n ⊕ Fin n ⊕ Unit) := ⟨Sum.inr (Sum.inr ())⟩
  have hk : k₀.val + 1 < n := by omega
  let j₀ : Fin n := ⟨k₀.val + 1, hk⟩
  have hij : k₀ ≠ j₀ := fun h => by simpa [j₀] using congrArg Fin.val h
  have hdim : Module.finrank 𝔽₃ (Fin n ⊕ Fin n ⊕ Unit → 𝔽₃) = 2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
    ring
  let fr₀ : OFrame (quadOdd n 𝔽₃) := (oddFrame n 𝔽₃).toHypFrame.toFrame hij true false
  have hR₀mem : rankOne (oddDatum n 𝔽₃).rootGroup k₀ ∈
      fundamentalSubgroups .POmegaOdd (oddDatum n 𝔽₃) :=
    ⟨1, Pi.single k₀ 1, Or.inl hlong, by ext y; simp [rankOne]⟩
  have hperp : 2 ≤ Module.finrank 𝔽₃ fr₀.perp := by
    have := finrank_perp_add_four fr₀
    omega
  obtain ⟨hframe, -⟩ := frames_of_single_class hodd hQ
    (fundamentalSubgroups .POmegaOdd (oddDatum n 𝔽₃))
    (rankOne (oddDatum n 𝔽₃).rootGroup k₀) fr₀
    (map_rankOne_odd k₀ hk (j := j₀) rfl hij) hperp
    (fun y => ⟨y, Pi.single k₀ 1, Or.inl hlong, rfl⟩) (fun R hR => hsingle _ hR₀mem R hR)
  exact ⟨nondegenerate_polarBilin_quadOdd n 𝔽₃ h2, range_spinAction_quadOdd h2 hn3,
    centerScalar_quadOdd h2 hn3, by rw [hdim]; omega, OrthAut.odd_hker2 h2 n, hframe, hG3, hsl2⟩

theorem hproj_odd (F₁ F₂ : OFrame (quadOdd n 𝔽₃))
    (h : F₂.La (-1) = LinearEquiv.neg 𝔽₃ * F₁.La (-1)) : False := by
  have hdim : Module.finrank 𝔽₃ (Fin n ⊕ Fin n ⊕ Unit → 𝔽₃) = 2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
    ring
  have := finrank_eq_eight_of_proj odd_natCard_galoisField_three F₁ F₂ h
  omega

end Odd

section Plus

variable {n : ℕ}

theorem spinCtx3_plus (hn3 : 3 ≤ n) (hn : 4 ≤ n)
    (hsingle : FundamentalSingleClass .POmegaPlus (plusDatum n 𝔽₃ hn3))
    (hlong : ∀ k : Fin n, IsLongestRoot (plusDatum n 𝔽₃ hn3) (Pi.single k 1))
    (hG3 : ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum n 𝔽₃ hn3), Gen3 R)
    (hsl2 : ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum n 𝔽₃ hn3),
      Nonempty (R ≃* SL(2, 𝔽₃))) :
    SpinCtx3 (quadPlus n 𝔽₃) (fundamentalSubgroups .POmegaPlus (plusDatum n 𝔽₃ hn3)) := by
  classical
  have hodd := odd_natCard_galoisField_three
  have : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hdim : Module.finrank 𝔽₃ (Fin n ⊕ Fin n → 𝔽₃) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  exact ⟨nondegenerate_polarBilin_quadPlus n 𝔽₃, range_spinAction_quadPlus hn3,
    centerScalar_quadPlus hn3, by rw [hdim]; omega, OrthAut.plus_hker2 n,
    fun R hR => exists_frame_of_mem_fund_plus hn3 hsingle hlong hR, hG3, hsl2⟩

theorem hproj_plus (hn5 : 5 ≤ n) (F₁ F₂ : OFrame (quadPlus n 𝔽₃))
    (h : F₂.La (-1) = LinearEquiv.neg 𝔽₃ * F₁.La (-1)) : False := by
  have hdim : Module.finrank 𝔽₃ (Fin n ⊕ Fin n → 𝔽₃) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have := finrank_eq_eight_of_proj odd_natCard_galoisField_three F₁ F₂ h
  omega

end Plus

section Minus

variable {n : ℕ} {b c : 𝔽₃}

theorem false_of_orth_quadMinus_four3 {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0) {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (h4 : 2 ≤ Nat.card F)
    (F₀ F₁ : OFrame (quadMinus 4 F b c)) (h : F₁.span ≤ F₀.perp) : False := by
  classical
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have hv := CFSG.ClassicalInvolution.RouteD.Exotic.isHypFam_of_orth F₀ F₁ h
  set v : Fin 4 → Bool → (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) := fun (i : Fin 4) (s : Bool) =>
      if s then ![F₀.e₁, F₀.e₂, F₁.e₁, F₁.e₂] i else ![F₀.f₁, F₀.f₂, F₁.f₁, F₁.f₂] i with hvdef
  let e' : Fin 4 × Bool ≃ Fin 4 ⊕ Fin 4 :=
    (Equiv.prodComm (Fin 4) Bool).trans (Equiv.boolProdEquivSum (Fin 4))
  let ψ₀ : (Fin 4 ⊕ Fin 4 → F) →ₗ[F] (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) :=
    (OrthAut.hypComb v).comp (LinearMap.funLeft F F e')
  have hψQ : ∀ w, quadMinus 4 F b c (ψ₀ w) = quadPlus 4 F w := by
    intro w
    show quadMinus 4 F b c (OrthAut.hypComb v (w ∘ e')) = _
    rw [OrthAut.map_hypComb hv, quadPlus_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    show w (e' (i, true)) * w (e' (i, false)) = _
    simp [e', Equiv.boolProdEquivSum, mul_comm]
  have hinj : Function.Injective ψ₀ :=
    (OrthAut.hypComb_injective hv).comp
      (LinearMap.funLeft_injective_of_surjective F F e' e'.surjective)
  have hdim : Module.finrank F (Fin 4 ⊕ Fin 4 → F) =
      Module.finrank F (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]
    simp
  have hsurj : Function.Surjective ψ₀ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  have hcard : Nat.card {w : Fin 4 ⊕ Fin 4 → F // quadPlus 4 F w = 0} =
      Nat.card {x : (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) // quadMinus 4 F b c x = 0} :=
    Nat.card_congr ((Equiv.ofBijective ψ₀ ⟨hinj, hsurj⟩).subtypeEquiv fun w => by
      rw [show (Equiv.ofBijective ψ₀ ⟨hinj, hsurj⟩) w = ψ₀ w from rfl, hψQ w])
  have e1 : (Nat.card {w : Fin 4 ⊕ Fin 4 → F // quadPlus 4 F w = 0} : ℤ) =
      1 + ((Nat.card F : ℤ) ^ 4 - 1) * ((Nat.card F : ℤ) ^ 3 + 1) :=
    CFSG.ClassicalInvolution.card_singular_quadPlus 3
  have e2 : (Nat.card {x : (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → F) //
      quadMinus 4 F b c x = 0} : ℤ) = 1 + ((Nat.card F : ℤ) ^ 4 + 1) * ((Nat.card F : ℤ) ^ 3 - 1) :=
    CFSG.ClassicalInvolution.card_singular_quadMinus_of_two_ne_zero h2 hirr 3
  rw [hcard] at e1
  have hq : (2 : ℤ) ≤ (Nat.card F : ℤ) := by exact_mod_cast h4
  have key : ((Nat.card F : ℤ) ^ 4 - 1) * ((Nat.card F : ℤ) ^ 3 + 1) -
      ((Nat.card F : ℤ) ^ 4 + 1) * ((Nat.card F : ℤ) ^ 3 - 1) =
      2 * ((Nat.card F : ℤ) ^ 3 * ((Nat.card F : ℤ) - 1)) := by ring
  have hpos : 0 < (Nat.card F : ℤ) ^ 3 * ((Nat.card F : ℤ) - 1) :=
    mul_pos (pow_pos (by linarith) 3) (by linarith)
  linarith

theorem spinCtx3_minus (hirr : ∀ s : 𝔽₃, s ^ 2 + b * s + c ≠ 0) (hn : 4 ≤ n) (k₀ : Fin (n - 1))
    (hk₀ : k₀.val = 0)
    (hsingle : FundamentalSingleClass .POmegaMinus (minusDatum n hirr))
    (hlong : IsLongestRoot (minusDatum n hirr) (Pi.single k₀ 1))
    (hG3 : ∀ R ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr), Gen3 R)
    (hsl2 : ∀ R ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr),
      Nonempty (R ≃* SL(2, 𝔽₃))) :
    SpinCtx3 (quadMinus n 𝔽₃ b c) (fundamentalSubgroups .POmegaMinus (minusDatum n hirr)) := by
  classical
  have hodd := odd_natCard_galoisField_three
  have h2 : (2 : 𝔽₃) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have : Invertible (2 : 𝔽₃) := invertibleOfNonzero h2
  have hQ : (quadMinus n 𝔽₃ b c).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_quadMinus_of_finite n 𝔽₃ hirr)
  have : Nonempty (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  have hk : k₀.val + 1 < n - 1 := by omega
  have hdim : Module.finrank 𝔽₃ (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → 𝔽₃) = 2 * (n - 1) + 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    ring
  have hij : k₀ ≠ (⟨k₀.val + 1, hk⟩ : Fin (n - 1)) := succ_ne_of_lt n hk
  let fr₀ : OFrame (quadMinus n 𝔽₃ b c) := (minusFrame n b c).toHypFrame.toFrame hij true false
  have hR₀mem : rankOne (minusDatum n hirr).rootGroup k₀ ∈
      fundamentalSubgroups .POmegaMinus (minusDatum n hirr) :=
    ⟨1, Pi.single k₀ 1, Or.inl hlong, by ext y; simp [rankOne]⟩
  have hperp : 2 ≤ Module.finrank 𝔽₃ fr₀.perp := by
    have := finrank_perp_add_four fr₀
    omega
  obtain ⟨hframe, -⟩ := frames_of_single_class hodd hQ
    (fundamentalSubgroups .POmegaMinus (minusDatum n hirr))
    (rankOne (minusDatum n hirr).rootGroup k₀) fr₀ (map_rankOne_minus hirr hk) hperp
    (fun y => ⟨y, Pi.single k₀ 1, Or.inl hlong, rfl⟩) (fun R hR => hsingle _ hR₀mem R hR)
  exact ⟨nondegenerate_polarBilin_quadMinus_of_finite n 𝔽₃ hirr, range_spinAction_quadMinus hn hirr,
    centerScalar_quadMinus hn hirr, by rw [hdim]; omega, OrthAut.minus_hker2 hirr, hframe, hG3,
    hsl2⟩

theorem hproj_minus (hirr : ∀ s : 𝔽₃, s ^ 2 + b * s + c ≠ 0) (hn4 : 4 ≤ n)
    (F₁ F₂ : OFrame (quadMinus n 𝔽₃ b c))
    (h : F₂.La (-1) = LinearEquiv.neg 𝔽₃ * F₁.La (-1)) : False := by
  have hodd := odd_natCard_galoisField_three
  have h2 : (2 : 𝔽₃) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have hdim : Module.finrank 𝔽₃ (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → 𝔽₃) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    omega
  by_cases hn : n = 4
  · subst hn
    exact false_of_orth_quadMinus_four3 h2 hirr (by rw [natCard_galoisField_three]; norm_num) F₁ F₂
      (span_le_perp_of_proj h2 F₁ F₂ h)
  · have := finrank_eq_eight_of_proj hodd F₁ F₂ h
    omega

end Minus

end CFSG.ClassicalInvolution.ModelFacts.TG3
