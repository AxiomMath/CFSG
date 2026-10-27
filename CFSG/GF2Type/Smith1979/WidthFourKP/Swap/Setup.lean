module

public import CFSG.GF2Type.Smith1979.W4AsSel
public import CFSG.GF2Type.Smith1979.WidthFourKP.OmegaMinusSchur
public import CFSG.CharacterTheory.Burnside
public import CFSG.GF2Type.Smith1979.W4FiveSwap

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4Swap

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S5
  CFSG.Open Subgroup Module
open CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

structure SwapW4 (D : S5.SwapData S g) : Prop where
  H : Hyp4 S g
  C : Cons311 S g
  hNo : NoA2 S g
  hw : S.width = 4
  F : W4Five.SwapFacts D H
  hVQ : ¬ V S g D.t ≤ S.Qa g
  hΩ : OmegaCase H C D.mem_Lbar D.t_ne_one hVQ
  h4 : finrank (ZMod 2) (Vt S g D.t) = 4
  hKR : imgR H.conj_mem D.t D.Xhat = RmodN S g D.t
  hXbot : D.Xhat ⊓ Nbar S g D.t = ⊥
  hNzp : Nbar S g D.t = zpowers D.t
  hRX : Rbar S g D.t = zpowers D.t ⊔ D.Xhat
  hFix : fixSpace (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) = Vt S g D.t

section Build

theorem SwapW4.mk' (hCE : CentralExtInput.{0}) (hw : S.width = 4) (hno : S11.NoA2All S)
    (H4 : Hyp4 S g) (C311 : Cons311 S g) (D : S5.SwapData S g) : SwapW4 D := by
  have hNo : NoA2 S g := S14.noA2_of (hno g H4.conj_mem H4.conj_ne)
  have hQ45 := S45Q.hyp45Q H4 C311
  have hS := W4Five.swap_structure_w4 hCE H4 hNo C311 hQ45 hw D
  obtain ⟨hVQ, -, -, hKR, hXbot, hNzp, hRX⟩ := hS
  have hF := W4Five.swap_facts D H4 hNo C311 hQ45
  have hClass := W4As.classify_four hw H4 hNo C311 D.mem_Lbar D.t_ne_one hF.RL
  have h4 : finrank (ZMod 2) (Vt S g D.t) = 4 := by
    rcases hClass with h | ⟨-, -, h4⟩
    · exact absurd h.1.le_Qa hVQ
    · exact h4
  have hΩ : OmegaCase H4 C311 D.mem_Lbar D.t_ne_one hVQ := by
    rcases hClass with h | ⟨hVQ', hΩ', -⟩
    · exact absurd h.1.le_Qa hVQ
    · have hEq : hVQ' = hVQ := Subsingleton.elim _ _
      rwa [hEq] at hΩ'
  have hFix : fixSpace (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) = Vt S g D.t :=
    ((S4.commSpace_t_eq H4 C311 D.mem_Lbar D.t_ne_one hVQ).2).trans
      (W4Minus.Wt_eq_Vt_w4 hw H4 D.t_ne_one h4)
  exact { H := H4, C := C311, hNo, hw, F := hF, hVQ, hΩ, h4, hKR, hXbot, hNzp, hRX, hFix }

end Build

variable (D : S5.SwapData S g)

@[expose] noncomputable def SwapW4.xhatEquivRmodN (W : SwapW4 D) : D.Xhat ≃* RmodN S g D.t := by
  classical
  let resX : D.Xhat →* (Vt S g D.t ≃ₗ[ZMod 2] Vt S g D.t) :=
    (resV W.H.conj_mem D.t).comp (Subgroup.inclusion W.F.XR)
  have hresX_range : resX.range = imgR W.H.conj_mem D.t D.Xhat := by
    ext e
    rw [MonoidHom.mem_range, S5.mem_imgR]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x, W.F.XR x.2⟩, x.2, rfl⟩
    · rintro ⟨y, hyX, rfl⟩
      exact ⟨⟨y, hyX⟩, rfl⟩
  have hresX_ker : resX.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hN : (x : S.O) ∈ Nbar S g D.t :=
      (S4.resV_eq_one_iff W.H.conj_mem ⟨x, W.F.XR x.2⟩).mp hx
    have hxbot : (x : S.O) ∈ D.Xhat ⊓ Nbar S g D.t := ⟨x.2, hN⟩
    rw [W.hXbot] at hxbot
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hxbot))
  let resXcod : D.Xhat →* RmodN S g D.t :=
    resX.codRestrict (RmodN S g D.t) fun x => by
      have hx : resX x ∈ imgR W.H.conj_mem D.t D.Xhat := by
        rw [← hresX_range]
        exact ⟨x, rfl⟩
      rwa [W.hKR] at hx
  have hresXcod_inj : Function.Injective resXcod := by
    intro a b hab
    have hmem : a * b⁻¹ ∈ resXcod.ker := by
      rw [MonoidHom.mem_ker]
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    have hker : resXcod.ker = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hx' : resX x = 1 := congrArg Subtype.val hx
      have hxbot : x ∈ resX.ker := by rwa [MonoidHom.mem_ker]
      rw [hresX_ker] at hxbot
      exact Subgroup.mem_bot.mp hxbot
    rw [hker] at hmem
    have h1 : a * b⁻¹ = 1 := Subgroup.mem_bot.mp hmem
    calc a = a * b⁻¹ * b := by group
      _ = b := by rw [h1, one_mul]
  have hresXcod_surj : Function.Surjective resXcod := by
    intro y
    have hy : (y : Vt S g D.t ≃ₗ[ZMod 2] Vt S g D.t) ∈
        imgR W.H.conj_mem D.t D.Xhat := by
      rw [W.hKR]
      exact y.2
    rw [S5.mem_imgR] at hy
    obtain ⟨z, hzX, hzy⟩ := hy
    refine ⟨⟨z, hzX⟩, ?_⟩
    apply Subtype.ext
    exact hzy
  exact MulEquiv.ofBijective resXcod ⟨hresXcod_inj, hresXcod_surj⟩

theorem SwapW4.coe_xhatEquivRmodN_apply (W : SwapW4 D) (ξ : D.Xhat) :
    ((SwapW4.xhatEquivRmodN D W ξ : RmodN S g D.t) :
        Vt S g D.t ≃ₗ[ZMod 2] Vt S g D.t) =
      (resV W.H.conj_mem D.t) ⟨ξ, W.F.XR ξ.2⟩ := rfl


theorem SwapW4.exists_form_minus (W : SwapW4 D) :
    ∃ (Q : QuadraticForm (ZMod 2) (Vt S g D.t)) (hQ : Q.polarBilin.Nondegenerate),
      RmodN S g D.t = omegaGroup Q hQ ∧
        (∀ v : Vt S g D.t, v ≠ 0 →
          (Q v = 0 ↔ v ∈ orbitOf (RmodN S g D.t) (aV D.mem_Lbar))) ∧
        ∀ U : Submodule (ZMod 2) (Vt S g D.t), finrank (ZMod 2) U = 2 →
          ∃ u ∈ U, Q u ≠ 0 := by
  obtain ⟨Q, hQ, hpol, hR, hL, hsing⟩ := W.hΩ.exists_form
  refine ⟨Q, hQ, hR, hsing, fun U hU => ?_⟩
  by_contra hcon
  push Not at hcon
  have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q :=
    ⟨U, by rw [hU, W.h4], hcon⟩
  haveI : Finite (Vt S g D.t ≃ₗ[ZMod 2] Vt S g D.t) := finite_linearEquiv_of_finite
  have hcardZ := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type
    (K := ZMod 2) (V := Vt S g D.t) hQ (m := 1) (by rw [W.h4]) (ε := 1)
    (Or.inl ⟨rfl, hplus⟩)
  have h72 : (2 * (Nat.card (ZMod 2) : ℤ) ^ (1 * (1 + 1)) *
      ((Nat.card (ZMod 2) : ℤ) ^ (1 + 1) - 1) *
        ∏ i ∈ Finset.Icc 1 1, (((Nat.card (ZMod 2) : ℤ) ^ 2) ^ i - 1)) = 72 := by
    norm_num [Nat.card_zmod]
  rw [h72] at hcardZ
  have hcard : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) = 72 :=
    Nat.cast_injective hcardZ
  haveI : Fintype ↥(TauCeti.QuadraticMap.orthogonalGroup Q) :=
    Fintype.ofFinite _
  have hcardF : Fintype.card ↥(TauCeti.QuadraticMap.orthogonalGroup Q) = 72 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have hsolvO : Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup Q) :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      Nat.prime_two Nat.prime_three (by norm_num) (a := 3) (b := 2)
      (by rw [hcardF]; norm_num)
  have hsolvΩ : Group.IsSolvable ↥(omegaGroup Q hQ) :=
    Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (omegaGroup_le Q hQ))
  have hsolvR : Group.IsSolvable ↥(RmodN S g D.t) := by
    rw [hR]
    exact hsolvΩ
  exact S5.false_of_isQuasisimple_of_le_solvable
    (S5.imgR_le_RmodN W.H.conj_mem D.t D.Xhat)
    (S5.isQuasisimple_imgR W.H.conj_mem W.F.XR D.isQuasisimple_Xhat W.F.XN) hsolvR


theorem SwapW4.exists_herm (W : SwapW4 D)
    (Q : QuadraticForm (ZMod 2) (Vt S g D.t)) (hQ : Q.polarBilin.Nondegenerate)
    (hR : RmodN S g D.t = omegaGroup Q hQ)
    (hmin : ∀ U : Submodule (ZMod 2) (Vt S g D.t), finrank (ZMod 2) U = 2 →
      ∃ u ∈ U, Q u ≠ 0) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra (ZMod 2) E)
      (P : CFSG.RankThree.PartOne.KCOrthogonal.EvenNormPlane (ZMod 2) E)
      (ψ : Vt S g D.t ≃ₗ[ZMod 2]
        CFSG.RankThree.PartOne.KCOrthogonal.hermFourSpace P.σ)
      (φ : D.Xhat ≃* Matrix.SpecialLinearGroup (Fin 2) E),
      Nat.card E = 4 ∧
        (∀ v : Vt S g D.t,
          CFSG.RankThree.PartOne.KCOrthogonal.hermFourForm P (ψ v) = Q v) ∧
        ∀ (ξ : D.Xhat) (v : Vt S g D.t),
          ψ (resV W.H.conj_mem D.t ⟨ξ, W.F.XR ξ.2⟩ v) =
            CFSG.RankThree.PartOne.KCOrthogonal.hermFourRho P (φ ξ) (ψ v) := by
  classical
  open CFSG.RankThree.PartOne.KCOrthogonal in
  have hcomm : ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ = RmodN S g D.t := by
    rw [CFSG.LargeExtraspecial.S8.commutator_orthogonalGroup_eq_omegaGroup_minus_four
      hQ W.h4 hmin, hR]
  obtain ⟨-, -, -, -, -, h4data, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction Q hQ
      (Or.inl W.h4) (by
        intro U hU
        exact hmin U (by rw [W.h4] at hU; omega))
  obtain ⟨E, hField, hAlg, P, ψ, ρ, hψQ, hρψ, hρinj, hρrange, -⟩ := h4data W.h4
  letI := hField
  letI := hAlg
  have hρrange' : ρ.range = RmodN S g D.t := by
    rw [hρrange, hcomm]
  let ρEquiv : Matrix.SpecialLinearGroup (Fin 2) E ≃* ρ.range :=
    MulEquiv.ofBijective ρ.rangeRestrict
      ⟨fun a b h => hρinj (by simpa using congrArg Subtype.val h),
        MonoidHom.rangeRestrict_surjective ρ⟩
  let φ : D.Xhat ≃* Matrix.SpecialLinearGroup (Fin 2) E :=
    (SwapW4.xhatEquivRmodN D W).trans
      ((MulEquiv.subgroupCongr hρrange').symm.trans ρEquiv.symm)
  have hφρ : ∀ ξ : D.Xhat,
      (ρ (φ ξ) : Vt S g D.t ≃ₗ[ZMod 2] Vt S g D.t) =
        (resV W.H.conj_mem D.t) ⟨ξ, W.F.XR ξ.2⟩ := by
    intro ξ
    unfold φ
    rw [MulEquiv.trans_apply]
    change (ρEquiv (ρEquiv.symm
      ((MulEquiv.subgroupCongr hρrange').symm (SwapW4.xhatEquivRmodN D W ξ))) :
        Vt S g D.t ≃ₗ[ZMod 2] Vt S g D.t) = _
    rw [MulEquiv.apply_symm_apply, MulEquiv.subgroupCongr_symm_apply]
    exact SwapW4.coe_xhatEquivRmodN_apply D W ξ
  refine ⟨E, hField, hAlg, P, ψ, φ, ?_, hψQ, ?_⟩
  · rw [P.card_E, Nat.card_zmod]
    norm_num
  · intro ξ v
    change ψ ((resV W.H.conj_mem D.t) ⟨ξ, W.F.XR ξ.2⟩ v) =
      CFSG.RankThree.PartOne.KCOrthogonal.hermFourRho P (φ ξ) (ψ v)
    rw [← hφρ ξ, hρψ]



theorem SwapW4.card_Xhat (W : SwapW4 D) : Nat.card D.Xhat = 60 := by
  obtain ⟨Q, hQ, hR, -, hmin⟩ := W.exists_form_minus
  exact (Nat.card_congr (SwapW4.xhatEquivRmodN D W).toEquiv).trans
    (by rw [hR]; exact S8.card_omegaGroup_minus_four hQ W.h4 hmin)


end CFSG.GF2Type.Smith1979.W4Swap
