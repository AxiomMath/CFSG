module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowStepOneMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaLagCore
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaLagStd
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelLagMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2PositionBHigh
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassicalSymplecticField

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Matrix Subgroup Module QuadraticMap CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.LieType.BorelTits (spJ transpose_mul_mul_of_mem_statedSp)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

section Small

variable {m : ℕ} {F : Type} [Field F]

theorem not_dvd_card_GL_of_lagX_two [CharP F 2] [Finite F] (hF : Nat.card F = 2) {K : Type}
    [Field K] (hK : Nat.card K = 2) (hm : 1 ≤ m) {n : ℕ} (hn : n + 1 = 2 * m) (d : ℕ)
    (hd : d ≤ n) :
    ¬ Nat.card (lagX m F) ∣ ∏ i : Fin d, (Nat.card K ^ d - Nat.card K ^ (i : ℕ)) := by
  rw [← Nat.card_congr (lagXEquiv m F).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF, hK]
  exact not_dvd_prod_two_pow_sub_two_pow hm (by omega)

end Small

section Model

theorem exists_perfect_not_embed_of_lagrangian_two {F V : Type} [Field F] [Finite F] [CharP F 2]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V}
    (hF : Nat.card F = 2) (hnd : (polarBilin Q).Nondegenerate) {N : ℕ} (hN4 : N % 4 = 2)
    (hN5 : 5 ≤ N) (hdim : finrank F V = 2 * N)
    (s : ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hss : s * s = 1) (hlag : 2 * finrank F (omegaInvSpace (s : V ≃ₗ[F] V)) = finrank F V)
    (hQW : ∀ w ∈ omegaInvSpace (s : V ≃ₗ[F] V), Q w = 0) :
    ∃ P : Subgroup ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆,
      commutator P = ⊤ ∧ (∀ p ∈ P, p * s = s * p) ∧
      ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
        ∀ ψ : P →* StatedSp (N - 1) K, ¬ Function.Injective ψ := by
  classical
  have hsO : (s : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    lag_commutator_le_self _ s.2
  have hss' : (s : V ≃ₗ[F] V) * s = 1 := congrArg Subtype.val hss
  obtain ⟨m, rfl⟩ : ∃ m, N = 2 * m := ⟨N / 2, by omega⟩
  have hmo : Odd m := ⟨m / 2, by omega⟩
  have hm1 : 1 ≤ m := by omega
  have hm3 : 3 ≤ m := by omega
  have hdimW : finrank F (omegaInvSpace (s : V ≃ₗ[F] V)) = 2 * m := by omega
  have hdimV : finrank F V = 2 * (2 * m) := by omega
  obtain ⟨b, hbQ, hbll, hbrr, hblr, hsl, hsr⟩ := exists_lagBasis hnd hsO hss' hdimW hdimV hQW
  set ι : ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m) → F) ≃ₗ[F] V := b.equivFun.symm with hιdef
  set Φ : GL ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) F ≃* (V ≃ₗ[F] V) :=
    (lagMatEquiv F _).trans (lagConj ι) with hΦdef
  have hΦapp : ∀ (g : GL ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) F) v, Φ g (ι v) = ι (g.1 *ᵥ v) :=
    fun g v => by
    rw [hΦdef, MulEquiv.trans_apply, lagConj_apply, lagMatEquiv_apply]
  have hbx : ∀ x, ι (Pi.single x 1) = b x := fun x => by
    rw [hιdef, Basis.equivFun_symm_apply]
    simp [Pi.single_apply]
  have hQι : ∀ v, Q (ι v) = lagQ v := by
    intro v
    rw [hιdef, Basis.equivFun_symm_apply, Fintype.sum_sum_type, QuadraticMap.map_add Q,
      lag_map_sum_eq_zero _ _ _ (fun a _ => hbQ _) (fun a _ a' _ => hbll a a'),
      lag_map_sum_eq_zero _ _ _ (fun a _ => hbQ _) (fun a _ a' _ => hbrr a a'), zero_add, zero_add,
      lag_polar_sum_left]
    simp_rw [lag_polar_sum_right, polar_smul_left, polar_smul_right, hblr]
    simp [lagQ]
  have hΦO : ∀ g : GL ((Fin m ⊕ Fin m) ⊕ (Fin m ⊕ Fin m)) F,
      (∀ v, lagQ (g.1 *ᵥ v) = lagQ v) → Φ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    intro g hg
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    obtain ⟨v, rfl⟩ := ι.surjective x
    rw [hΦapp, hQι, hQι, hg]
  have hΦs : Φ (lagRad m F (Multiplicative.ofAdd (spJ m F))) = s := by
    apply LinearEquiv.toLinearMap_injective
    refine b.ext fun x => ?_
    simp only [LinearEquiv.coe_coe]
    rw [← hbx, hΦapp]
    rcases x with a | d
    · rw [lagRadJ_mulVec_inl, hbx, hsl]
    · rw [lagRadJ_mulVec_inr, map_add, hbx, hbx, hsr]
  have : Group.IsPerfect (StatedSp m F) := isPerfect_statedSp_of_three_le hm3
  have hPperf : ⁅lagP m F, lagP m F⁆ = lagP m F := commutator_lagP_two hm1
  set PV := (lagP m F).map Φ.toMonoidHom with hPVdef
  have hPVO : PV ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [hPVdef, Subgroup.map_le_iff_le_comap]
    apply sup_le
    · rintro _ ⟨C, hC, rfl⟩
      exact hΦO _ (lagQ_lagRad hC.1)
    · rintro _ ⟨A, rfl⟩
      exact hΦO _ (lagQ_lagLevi A)
  have hPVΩ : PV ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
    have h1 : ⁅PV, PV⁆ = PV := by rw [hPVdef, ← Subgroup.map_commutator, hPperf]
    rw [← h1]
    exact Subgroup.commutator_mono hPVO hPVO
  set eP : lagP m F ≃* PV.subgroupOf ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
    ((lagP m F).equivMapOfInjective Φ.toMonoidHom Φ.injective).trans
      (Subgroup.subgroupOfEquivOfLe hPVΩ).symm with heP
  refine ⟨PV.subgroupOf ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
    TauCeti.QuadraticMap.orthogonalGroup Q⁆, ?_, ?_, ?_⟩
  · have : Group.IsPerfect (lagP m F) := Subgroup.isPerfect_iff.2 hPperf
    exact commutator_top_transfer eP Group.IsPerfect.commutator_eq_top
  · intro p hp
    obtain ⟨g, hg, hgp⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hp)
    have hc := mem_centralizer_singleton_iff.1 (lagP_le_centralizer hg)
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hgp, ← hΦs]
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hc]
  · intro K _ _ hK ψ hψ
    have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow (f := 1) (by rw [hK, pow_one])
    have : IsSimpleGroup (StatedSp m F) := isSimpleGroup_statedSp_two hF hm3
    have : IsSimpleGroup (lagX m F) := (lagXEquiv m F).symm.isSimpleGroup
    have hXp : Group.IsPerfect (lagX m F) := Group.IsPerfect.range _
    have hR0 := card_le_of_lagrangian_core_of_le_of_not_dvd (K := K) (P := lagP m F)
      le_sup_left le_sup_right (by omega : 2 * m - 1 + 1 = 2 * m) (ψ.comp eP.toMonoidHom)
      (hψ.comp eP.injective) isPGroup_lagR0Grp lagX_le_normalizer hXp
      (commutator_lagR0Grp_lagX_two hm1) (fun r hr hrX => eq_one_of_commute_lagX_two hmo hr hrX)
      (not_dvd_card_GL_of_lagX_two hF hK hm1 (by omega))
    rw [hK] at hR0
    have hlow := card_lagR0Grp_lower (F := F) hm1
    rw [hF] at hlow
    have e1 : 2 * m * (2 * m + 1) / 2 = m * (2 * m + 1) := by
      rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    rw [e1] at hlow
    have h3 : 2 ^ (m * (2 * m + 1)) ≤ 2 ^ (2 * m * (m - 1) + 1 + 2 * m) := by
      calc 2 ^ (m * (2 * m + 1))
          ≤ Nat.card (lagR0Grp m F) * 2 * 2 ^ (2 * m) := hlow
        _ ≤ 2 ^ (2 * m * (m - 1)) * 2 * 2 ^ (2 * m) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hR0)
        _ = 2 ^ (2 * m * (m - 1) + 1 + 2 * m) := by rw [pow_add, pow_add, pow_one]
    have h4 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h3
    obtain ⟨t, rfl⟩ : ∃ t, m = t + 3 := ⟨m - 3, by omega⟩
    have e2 : t + 3 - 1 = t + 2 := by omega
    rw [e2] at h4
    nlinarith

end Model

section Global

theorem spTwoOmegaLagrangianATwoFourInput_holds (κ : Sp2mKind) :
    SpTwoOmegaLagrangianATwoFourInput κ := by
  intro G _ _ L hset n K _ _ _ hK hn hn4 e t ht hKt _ _ F _ _ _ V _ _ _ Q φ hF hnd hdim g hw hcl
  obtain ⟨hQW, hlag, -⟩ := hcl
  set s := φ ⟨g⁻¹ * t * g, hw⟩ with hs
  have hss : s * s = 1 := mul_self_map_conj_eq_one φ ht hw
  obtain ⟨P, hPc, hPs, hPne⟩ := exists_perfect_not_embed_of_lagrangian_two hF hnd
    (N := n + 2) (by omega) (by omega) (by rw [hdim]) s hss hlag hQW
  set eP : P ≃* P.map φ.symm.toMonoidHom :=
    P.equivMapOfInjective φ.symm.toMonoidHom φ.symm.injective with heP
  have hP'c : commutator (P.map φ.symm.toMonoidHom) = ⊤ := commutator_top_transfer eP hPc
  have hwN : g⁻¹ * t * g ∈ normalizer (nsGlobal e : Set G) := Subgroup.le_normalizer hw
  have hP'F : P.map φ.symm.toMonoidHom ≤
      fixedSubgroup ((nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hwN⟩) := by
    rintro _ ⟨p, hp, rfl⟩
    have hc : φ.symm p * ⟨g⁻¹ * t * g, hw⟩ = ⟨g⁻¹ * t * g, hw⟩ * φ.symm p := by
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, ← hs]
      exact hPs p hp
    have hc' := congrArg Subtype.val hc
    simp only [Subgroup.coe_mul] at hc'
    show ((nsGlobal e).normalizerMonoidHom ⟨g⁻¹ * t * g, hwN⟩) (φ.symm p) = φ.symm p
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    show (g⁻¹ * t * g) * ((φ.symm p : nsGlobal e) : G) * (g⁻¹ * t * g)⁻¹ = _
    rw [← hc', mul_inv_cancel_right]
  obtain ⟨ψ, hψ⟩ := exists_injective_of_perfect_le_fixedSubgroup_conj hset (by omega) e ht hKt
    hwN (P.map φ.symm.toMonoidHom) hP'c hP'F
  exact hPne K hK (ψ.comp eP.toMonoidHom) (hψ.comp eP.injective)

theorem spTwoOmegaLagrangianATwoInput_holds (κ : Sp2mKind) : SpTwoOmegaLagrangianATwoInput κ :=
  spTwoOmegaLagrangianATwoInput_of_four (spTwoOmegaLagrangianATwoFourInput_holds κ)

end Global

end CFSG.SeitzReduction.SymplecticPilot
