module

public import CFSG.LargeExtraspecial.S12Main
public import CFSG.LargeExtraspecial.S14W4LocNine

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.W4Loc

open Subgroup Module QuadraticMap CFSG.Open CFSG.RankThree.OrthogonalInvolutions

theorem false_of_two_pow_dvd {K : Type*} [Group K] [Finite K]
    (hP : ∀ P : Subgroup K, IsPGroup 2 P → Nat.card P ≤ 2 ^ 7) (hdvd : 2 ^ 8 ∣ Nat.card K) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP8⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  have h := hP P (IsPGroup.of_card hP8)
  rw [hP8] at h
  norm_num at h

variable {X : Type} [Group X] [Finite X] (T : Setting X)

theorem two_pow_dvd_card_spIsometries {b : LinearMap.BilinForm (ZMod 2) (Fin 6 → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) :
    2 ^ 8 ∣ Nat.card (s12SpIsometries b) := by
  have he : s12SpIsometries b = TauCeti.BilinForm.isometryGroup b := by
    ext g
    exact TauCeti.BilinForm.mem_isometryGroup_iff.symm
  have hnd' : b.Nondegenerate :=
    (LinearMap.IsAlt.isRefl halt).nondegenerate_iff_separatingLeft.mpr hnd
  have hcard := CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_isometryGroup 3 b
    halt hnd' (by simp)
  rw [he, hcard, Nat.card_zmod]
  decide

theorem two_pow_dvd_of_omegaPlusEight (hT : T.S12OmegaPlusEight) : 2 ^ 8 ∣ Nat.card T.Mbar := by
  obtain ⟨hw, -, hM⟩ := hT
  have : Finite T.Qt := inferInstance
  have : FiniteDimensional (ZMod 2) T.Qt := Module.Finite.of_finite
  have hfin : finrank (ZMod 2) T.Qt = 2 * 4 := by rw [T.finrank_Qt_eq_two_mul_width, hw]
  have : Nontrivial T.Qt := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have hq := T.q_nondegenerate
  have hΩ : timmesfeldOmega T.q = omegaGroup T.q hq := s12_timmesfeldOmega_eq T.q hq
  have hcardM : Nat.card T.Mbar = Nat.card (omegaGroup T.q hq) := by
    rw [← hΩ, ← hM, Subgroup.card_map_of_injective T.O.subtype_injective]
  have h1 := S12DW.card_orthogonalGroup_mul_ncard_eq hq (m := 4) hfin
  have h2 := S12DW.card_orthogonalGroup_eq hq
  have hc := S12DW.natCard_eq_four_pow (V := T.Qt) hfin
  have h3 := CFSG.Fischer.Classification.LocalSymp.two_mul_ncard_quadratic T.q
    (S12DW.polar_eq_zero_imp hq) hc
  have h4 := S12DW.ncard_eq_zero_eq T.q
  have hP : 2 ^ (4 ^ 2) * ∏ j ∈ Finset.Icc 1 4, (2 ^ (2 * j) - 1) = 47377612800 := by decide
  rw [hP, h2] at h1
  rw [hc] at h4
  rw [hcardM]
  rcases h3 with h3 | h3
  · have hn : {v | T.q v = 0}.ncard = 136 := by omega
    rw [hn] at h1
    have hw' : Nat.card (omegaGroup T.q hq) = 174182400 := by omega
    rw [hw']
    decide
  · have hn : {v | T.q v = 0}.ncard = 120 := by omega
    rw [hn] at h1
    have hw' : Nat.card (omegaGroup T.q hq) = 197406720 := by omega
    rw [hw']
    decide

theorem two_pow_dvd_of_spSixSpin {g : X} (hT : T.S12SpSixSpin g) : 2 ^ 8 ∣ Nat.card T.Mbar := by
  obtain ⟨-, hXM, b, halt, hnd, ⟨e⟩⟩ := hT
  have h1 : Nat.card (T.Xbar12 g) = Nat.card (s12SpIsometries b) := Nat.card_congr e.toEquiv
  have h2 : Nat.card (T.Xbar12 g) = Nat.card T.Mbar :=
    congrArg (fun H : Subgroup T.O => Nat.card H) hXM
  rw [← h2, h1]
  exact two_pow_dvd_card_spIsometries halt hnd

open scoped MatrixGroups in
theorem false_of_gammaL_of_orderOf {g : X} {t : T.O} (hT : T.S12GammaLResidual g t)
    (hw : T.width = 4) (x : T.Mbar) (hx : orderOf x = 9) : False := by
  obtain ⟨-, -, -, hidx, ⟨e⟩, -⟩ := hT
  have key : ∀ n : ℕ, n = 4 → (T.Xbar12 g ≃* SL(n, ZMod 2)) →
      Nonempty (T.Xbar12 g ≃* SL(4, ZMod 2)) := by
    rintro n rfl e'
    exact ⟨e'⟩
  obtain ⟨e4⟩ := key _ hw e
  have hH : ((T.Xbar12 g).subgroupOf T.Mbar).index = 2 := hidx
  exact false_of_orderOf_eq_nine hH
    ((Subgroup.subgroupOfEquivOfLe Setting.Xbar12_le_Mbar).trans e4) x hx

end CFSG.LargeExtraspecial.S14.W4Loc
