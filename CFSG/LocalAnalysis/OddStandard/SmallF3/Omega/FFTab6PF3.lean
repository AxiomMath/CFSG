module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFFundamental

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private theorem ff_sq_of_orderOf_eq_two {G : Type} [Group G] {x : G} (hx : orderOf x = 2) :
    x * x = 1 := by
  rw [← pow_two, ← hx]
  exact pow_orderOf_eq_one x

private theorem ff_dinv_of_kindP {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : G}
    (hGA : CFSG.Open.GriessAllModelsStatement) (hL : IsOm6P L) (hs2 : orderOf s = 2)
    (hsn : s ∈ Subgroup.normalizer (L : Set G)) {k : ℕ} (h : KindP L s k) (hk : k < 5) :
    DInv L s k :=
  (ff_kindP_iff_dinv (k := k) hGA hL hs2 hsn hk).mp h

private theorem ff_orderOf_eq_two_of_induces_i2 {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hGA : CFSG.Open.GriessAllModelsStatement) (hL : IsOm6P L) {v : G} (hv : v ∈ L)
    (hType : InducesTypeSome L v 6 1 2 (-1)) : orderOf v = 2 := by
  obtain ⟨V, _, _, _, Q, hQ, e, x, _, _, hInd, hTypex⟩ := hType
  have hz := ff_center_eq_bot_six_plus hGA hL
  have h5 : 5 ≤ Module.finrank (ZMod 3) V := by omega
  have hx2 : x * x = 1 := ff_KM1_sq hTypex
  have hxne : x ≠ 1 := ff_KM1_ne_one hTypex
  have hproj := ff_induces_unique hQ h5 e (ff_induces_of_mem hQ hz e hv) hInd
  have hy2proj : ((ffPhi hz e ⟨v, hv⟩ : ↥(omegaProj hQ)) : ProjOrth Q) *
      ((ffPhi hz e ⟨v, hv⟩ : ↥(omegaProj hQ)) : ProjOrth Q) = 1 := by
    apply projOrthToProjSim_injective (Q := Q)
    rw [map_mul, map_one, hproj, hx2]
  have hy2 : ffPhi hz e ⟨v, hv⟩ * ffPhi hz e ⟨v, hv⟩ = 1 := by
    apply Subtype.ext
    simpa using hy2proj
  have hvv : v * v = 1 := by
    have h1 : ffPhi hz e (⟨v, hv⟩ * ⟨v, hv⟩) = ffPhi hz e 1 := by
      rw [map_mul, map_one]
      exact hy2
    simpa using congrArg Subtype.val ((ffPhi hz e).injective h1)
  have hvne : v ≠ 1 := by
    intro hv1
    have h1 : (⟨v, hv⟩ : ↥L) = 1 := Subtype.ext hv1
    apply hxne
    rw [← hproj, h1]
    simp
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (p := 2) (by rwa [pow_two]) hvne

theorem ff_prod_i2 (hGA : CFSG.Open.GriessAllModelsStatement) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ v : G, v ∈ L → InducesTypeSome L v 6 1 2 (-1) → ∀ u ∈ XOut L v, orderOf u = 2 →
      orderOf (u * v) = 2 ∧ InducesTypeSome L (u * v) 6 1 4 1 := by
  intro G _ _ L hL v hv hType u hu hu2
  have hz := ff_center_eq_bot_six_plus hGA hL
  have hv2 : orderOf v = 2 := ff_orderOf_eq_two_of_induces_i2 hGA hL hv hType
  have hss : v * v = 1 := ff_sq_of_orderOf_eq_two hv2
  obtain ⟨V, _, _, _, Q, hQ, e, hdim, hsgn⟩ := ff_exists_model_six_plus hL
  have h5 : 5 ≤ Module.finrank (ZMod 3) V := by omega
  let y : ↥(omegaProj hQ) := ffPhi hz e ⟨v, hv⟩
  have hInd : InducesViaP L (Subgroup.center ↥L) hQ e v
      (projOrthToProjSim Q (y : ProjOrth Q)) := ff_induces_of_mem hQ hz e hv
  have hsn : v ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hv
  have hD1 : DInv L v 1 :=
    ff_dinv_of_kindP hGA hL hv2 hsn (show KindP L v 1 from hType) (by norm_num)
  have hyKM1 : KM1 (projOrthToProjSim Q (y : ProjOrth Q)) :=
    ff_KM1_of_dinv1 hQ hdim hsgn hz e hInd hss hD1
  have huL : u ∈ L := ff_XOut_le L v hu
  have hwmem : ffPhi hz e ⟨u, huL⟩ ∈
      twoPrimeRes (twoRes (ffFix hQ (by omega) (projOrthToProjSim Q (y : ProjOrth Q)))) :=
    (ff_mem_XOut_iff hQ h5 hz e hInd huL).mp hu
  have hw2 : orderOf (ffPhi hz e ⟨u, huL⟩) = 2 := by
    rw [ff_orderOf_phi hQ hz e huL]
    exact hu2
  obtain ⟨hwy2, hyKM0⟩ := ff_K1_prod hQ hdim hsgn (y := y) hyKM1 hwmem hw2
  have huv : u * v ∈ L := L.mul_mem huL hv
  have hphi : ffPhi hz e ⟨u * v, huv⟩ = ffPhi hz e ⟨u, huL⟩ * y := by
    rw [show (⟨u * v, huv⟩ : ↥L) = ⟨u, huL⟩ * ⟨v, hv⟩ from Subtype.ext rfl, map_mul]
  have horder : orderOf (u * v) = 2 := by
    rw [← ff_orderOf_phi hQ hz e huv, hphi, hwy2]
  refine ⟨horder, ?_⟩
  refine ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, e,
    projOrthToProjSim Q ((ffPhi hz e ⟨u, huL⟩ * y : ↥(omegaProj hQ)) : ProjOrth Q),
    hdim, hsgn, ?_, hyKM0⟩
  simpa [hphi] using ff_induces_of_mem hQ hz e huv

theorem ff_excl (hGA : CFSG.Open.GriessAllModelsStatement) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      ∀ i j : ℕ, i < 5 → j < 5 → i ≠ j → KindP L s i → ¬ KindP L s j := by
  intro G _ _ L hL s hs2 hsn i j hi hj hij hI hJ
  exact hij (ff_dinv_excl L s hi hj (ff_dinv_of_kindP hGA hL hs2 hsn hI hi)
    (ff_dinv_of_kindP hGA hL hs2 hsn hJ hj))

theorem ff_xout_eq (hGA : CFSG.Open.GriessAllModelsStatement) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) → layerCent L s ≠ ⊥ →
      XOut L s = layerCent L s := by
  intro G _ _ L hL s hs2 hsn hl
  have hz := ff_center_eq_bot_six_plus hGA hL
  have hev := ff_two_dvd_card_of_isOmega6Plus hL.2
  rcases ff_dinv_classify hGA hL hs2 hsn with hc | h0 | h1 | h2 | h3 | h4
  · obtain ⟨hLay, hX⟩ := ff_layerCent_eq_of_central hL.1 hz hev hc
    exact hX.trans hLay.symm
  · exact absurd (ff_layerCent_eq_bot_of_solvable L s h0.2.2) hl
  · exact h1.2.2.2
  · exact h2.2.2
  · exact absurd (ff_layerCent_eq_bot_of_solvable L s h3.2) hl
  · exact h4.2.2

theorem ff_xout_i3 (hGA : CFSG.Open.GriessAllModelsStatement) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      (∃ α : ℤˣ, InducesTypeSome L s 6 1 3 α) →
      XOut L s = CFSG.inSubgroup (CFSG.pCore 2) (twoRes (L ⊓ centralizer ({s} : Set G))) := by
  intro G _ _ L hL s hs2 hsn h
  have hz := ff_center_eq_bot_six_plus hGA hL
  obtain ⟨V, _, _, _, Q, hQ, e, hdim, hsgn⟩ := ff_exists_model_six_plus hL
  have h5 : 5 ≤ Module.finrank (ZMod 3) V := by omega
  obtain ⟨x, hs⟩ := ff_exists_induces hQ (Or.inr ⟨hdim, Or.inl hsgn⟩) e hsn
  have hss : s * s = 1 := ff_sq_of_orderOf_eq_two hs2
  have hD3 : DInv L s 3 :=
    ff_dinv_of_kindP hGA hL hs2 hsn (show KindP L s 3 from h) (by norm_num)
  have hKM3 : KM3 x := ff_KM3_of_dinv3 hQ hdim hsgn hz e hs hss hD3
  have hxTC : XTwoCore ↥(ffFix hQ (by omega) x) := ff_K3_xTwoCore hQ hdim hsgn hKM3
  obtain ⟨f, _⟩ := ff_exists_centEquiv hQ h5 hz e hs
  exact (ff_X_eq_pCore_iff (C := L ⊓ centralizer ({s} : Set G)) f).mpr hxTC

end CFSG.OddStandard.SmallF3.Omega
