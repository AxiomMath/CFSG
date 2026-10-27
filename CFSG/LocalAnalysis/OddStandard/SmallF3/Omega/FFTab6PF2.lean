module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFFundamental

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

private theorem ffP2_sq_of_orderOf_eq_two {G : Type} [Group G] {x : G} (hx : orderOf x = 2) :
    x * x = 1 := by
  rw [← pow_two, ← hx]
  exact pow_orderOf_eq_one x

private theorem ffP2_dinv_of_kindP {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : G}
    (hGA : CFSG.Open.GriessAllModelsStatement) (hL : IsOm6P L) (hs2 : orderOf s = 2)
    (hsn : s ∈ Subgroup.normalizer (L : Set G)) {k : ℕ} (h : KindP L s k) (hk : k < 5) :
    DInv L s k :=
  (ff_kindP_iff_dinv (k := k) hGA hL hs2 hsn hk).mp h

private theorem ffP2_kindP_of_dinv {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : G}
    (hGA : CFSG.Open.GriessAllModelsStatement) (hL : IsOm6P L) (hs2 : orderOf s = 2)
    (hsn : s ∈ Subgroup.normalizer (L : Set G)) {k : ℕ} (h : DInv L s k) (hk : k < 5) :
    KindP L s k :=
  (ff_kindP_iff_dinv (k := k) hGA hL hs2 hsn hk).mpr h

theorem ff_classify (hGA : CFSG.Open.GriessAllModelsStatement) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      s ∈ centralizer (L : Set G) ∨ InducesTypeSome L s 6 1 4 1 ∨ InducesTypeSome L s 6 1 2 (-1) ∨
        (∃ α : ℤˣ, InducesTypeSome L s 6 1 1 α) ∨ (∃ α : ℤˣ, InducesTypeSome L s 6 1 3 α) ∨
        InducesOutsideGStar L 6 1 s := by
  intro G _ _ L hL s hs2 hsn
  rcases ff_dinv_classify hGA hL hs2 hsn with hc | h0 | h1 | h2 | h3 | h4
  · exact Or.inl hc
  · exact Or.inr (Or.inl (ffP2_kindP_of_dinv hGA hL hs2 hsn h0 (by norm_num)))
  · exact Or.inr (Or.inr (Or.inl (ffP2_kindP_of_dinv hGA hL hs2 hsn h1 (by norm_num))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (ffP2_kindP_of_dinv hGA hL hs2 hsn h2 (by norm_num)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl (ffP2_kindP_of_dinv hGA hL hs2 hsn h3 (by norm_num))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (ffP2_kindP_of_dinv hGA hL hs2 hsn h4 (by norm_num))))))

theorem ff_nontrivial (hGA : CFSG.Open.GriessAllModelsStatement) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      (InducesTypeSome L s 6 1 4 1 ∨ InducesTypeSome L s 6 1 2 (-1) ∨
        (∃ α : ℤˣ, InducesTypeSome L s 6 1 1 α) ∨ (∃ α : ℤˣ, InducesTypeSome L s 6 1 3 α) ∨
        InducesOutsideGStar L 6 1 s) → s ∉ centralizer (L : Set G) := by
  intro G _ _ L hL s hs2 hsn h
  rcases h with h0 | h1 | h2 | h3 | h4
  · exact ff_dinv_not_mem_centralizer L s (by norm_num)
      (ffP2_dinv_of_kindP hGA hL hs2 hsn (show KindP L s 0 from h0) (by norm_num))
  · exact ff_dinv_not_mem_centralizer L s (by norm_num)
      (ffP2_dinv_of_kindP hGA hL hs2 hsn (show KindP L s 1 from h1) (by norm_num))
  · exact ff_dinv_not_mem_centralizer L s (by norm_num)
      (ffP2_dinv_of_kindP hGA hL hs2 hsn (show KindP L s 2 from h2) (by norm_num))
  · exact ff_dinv_not_mem_centralizer L s (by norm_num)
      (ffP2_dinv_of_kindP hGA hL hs2 hsn (show KindP L s 3 from h3) (by norm_num))
  · exact ff_dinv_not_mem_centralizer L s (by norm_num)
      (ffP2_dinv_of_kindP hGA hL hs2 hsn (show KindP L s 4 from h4) (by norm_num))

theorem ff_layer_om5_iff (hGA : CFSG.Open.GriessAllModelsStatement) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      (IsOmega5 (layerCent L s) ↔ ∃ α : ℤˣ, InducesTypeSome L s 6 1 1 α) := by
  intro G _ _ L hL s hs2 hsn
  constructor
  · intro h5
    rcases ff_dinv_classify hGA hL hs2 hsn with hc | h0 | h1 | h2 | h3 | h4
    · have hz : Subgroup.center ↥L = ⊥ := ff_center_eq_bot_six_plus hGA hL
      have hev : 2 ∣ Nat.card ↥L := ff_two_dvd_card_of_isOmega6Plus hL.2
      obtain ⟨hLay, -⟩ := ff_layerCent_eq_of_central hL.1 hz hev hc
      rw [hLay] at h5
      exact absurd h5 (ff_not_isOmega6Plus_and_isOmega5 hL.2)
    · exfalso
      exact (ff_isOmega5_ne_bot ((ff_layerCent_eq_bot_of_solvable L s h0.2.2) ▸ h5)) rfl
    · exact ((ff_not_isOmega5_and_isL29 h5) h1.2.2.1).elim
    · exact (ff_kindP_iff_dinv hGA hL hs2 hsn (k := 2) (by norm_num)).mpr h2
    · exfalso
      exact (ff_isOmega5_ne_bot ((ff_layerCent_eq_bot_of_solvable L s h3.2) ▸ h5)) rfl
    · rcases h4.2.1 with h43 | h42
      · exact ((ff_not_isOmega5_and_isL3Eps3 h5) h43).elim
      · exact ((ff_not_isOmega5_and_isL29 h5) h42).elim
  · intro h
    exact ((ff_kindP_iff_dinv hGA hL hs2 hsn (k := 2) (by norm_num)).mp
      (show KindP L s 2 from h)).2.1

theorem ff_cover_i4 (hGA : CFSG.Open.GriessAllModelsStatement) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) →
      ((∃ α : ℤˣ, InducesTypeSome L s 6 1 3 α) ∨ InducesOutsideGStar L 6 1 s) →
        ∃ u ∈ XOut L s, orderOf u = 2 ∧ InducesTypeSome L u 6 1 4 1 ∧ s * u ∈ conjClassIn L s := by
  intro G _ _ L hL s hs2 hsn h
  have hss : s * s = 1 := ffP2_sq_of_orderOf_eq_two hs2
  have hz : Subgroup.center ↥L = ⊥ := ff_center_eq_bot_six_plus hGA hL
  obtain ⟨V, _, _, _, Q, hQ, e, hdim, hsgn⟩ := ff_exists_model_six_plus hL
  have h5 : 5 ≤ Module.finrank (ZMod 3) V := by omega
  obtain ⟨x, hs⟩ := ff_exists_induces hQ (Or.inr ⟨hdim, Or.inl hsgn⟩) e hsn
  have hx2 : x * x = 1 := ff_induces_sq hQ h5 hz e hs hss
  have hcover : ∃ w : ↥(omegaProj hQ),
      w ∈ twoPrimeRes (twoRes (ffFix hQ (by omega) x)) ∧ w * w = 1 ∧
      KM0 (projOrthToProjSim Q (w : ProjOrth Q)) ∧
      ∃ a : ↥(omegaProj hQ), ffSimOmegaAct hQ (by omega) x a * a⁻¹ = w := by
    rcases h with h3 | h4
    · have hD3 : DInv L s 3 :=
        ffP2_dinv_of_kindP hGA hL hs2 hsn (show KindP L s 3 from h3) (by norm_num)
      exact ff_K3_cover hQ hdim hsgn (ff_KM3_of_dinv3 hQ hdim hsgn hz e hs hss hD3)
    · have hD4 : DInv L s 4 :=
        ffP2_dinv_of_kindP hGA hL hs2 hsn (show KindP L s 4 from h4) (by norm_num)
      exact ff_K4_cover hQ hdim hsgn hx2 (ff_KM4_of_dinv4 hQ hdim hsgn hz e hs hss hD4)
  obtain ⟨w, hwX, hw2, hKM0, a, ha⟩ := hcover
  let l : ↥L := (ffPhi hz e).symm w
  have hphiu : ffPhi hz e ⟨(l : G), l.2⟩ = w := (ffPhi hz e).apply_symm_apply w
  have huX : (l : G) ∈ XOut L s :=
    (ff_mem_XOut_iff hQ h5 hz e hs l.2).mpr (by rw [hphiu]; exact hwX)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hwne : w ≠ 1 := fun hw1 => ff_KM0_ne_one hKM0 (by rw [hw1]; rfl)
  have hordw : orderOf w = 2 := orderOf_eq_prime (p := 2) (by rwa [pow_two]) hwne
  have hordl : orderOf (l : G) = 2 := by
    rw [← ff_orderOf_phi hQ hz e l.2, hphiu]
    exact hordw
  have hIndVia : InducesViaP L (Subgroup.center ↥L) hQ e (l : G)
      (projOrthToProjSim Q (w : ProjOrth Q)) := by
    rw [← hphiu]
    exact ff_induces_of_mem hQ hz e l.2
  refine ⟨(l : G), huX, hordl, ?_, ?_⟩
  · exact ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, e,
      projOrthToProjSim Q (w : ProjOrth Q), hdim, hsgn, hIndVia, hKM0⟩
  · exact (ff_cover_iff hQ h5 hz e hs hss l.2).mpr ⟨a, by rw [hphiu]; exact ha⟩

theorem ff_inv_of_i4m (hGA : CFSG.Open.GriessAllModelsStatement) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) → InducesTypeSome L s 6 1 2 (-1) →
      ∀ u ∈ XOut L s, orderOf u = 2 → InducesTypeSome L u 6 1 2 (-1) := by
  intro G _ _ L hL s hs2 hsn h u hu hu2
  have hss : s * s = 1 := ffP2_sq_of_orderOf_eq_two hs2
  have hz : Subgroup.center ↥L = ⊥ := ff_center_eq_bot_six_plus hGA hL
  obtain ⟨V, _, _, _, Q, hQ, e, hdim, hsgn⟩ := ff_exists_model_six_plus hL
  have h5 : 5 ≤ Module.finrank (ZMod 3) V := by omega
  obtain ⟨x, hs⟩ := ff_exists_induces hQ (Or.inr ⟨hdim, Or.inl hsgn⟩) e hsn
  have hD1 : DInv L s 1 :=
    ffP2_dinv_of_kindP hGA hL hs2 hsn (show KindP L s 1 from h) (by norm_num)
  have hKM1 : KM1 x := ff_KM1_of_dinv1 hQ hdim hsgn hz e hs hss hD1
  have huL : u ∈ L := ff_XOut_le L s hu
  have hw : ffPhi hz e ⟨u, huL⟩ ∈ twoPrimeRes (twoRes (ffFix hQ (by omega) x)) :=
    (ff_mem_XOut_iff hQ h5 hz e hs huL).mp hu
  have hw2 : orderOf (ffPhi hz e ⟨u, huL⟩) = 2 := by
    rw [ff_orderOf_phi hQ hz e huL]
    exact hu2
  have hKM1w : KM1 (projOrthToProjSim Q ((ffPhi hz e ⟨u, huL⟩ : ↥(omegaProj hQ)) : ProjOrth Q)) :=
    ff_K1_invol hQ hdim hsgn hKM1 hw hw2
  exact ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, e,
    projOrthToProjSim Q ((ffPhi hz e ⟨u, huL⟩ : ↥(omegaProj hQ)) : ProjOrth Q),
    hdim, hsgn, ff_induces_of_mem hQ hz e huL, hKM1w⟩

theorem ff_i4m_of_inv (hGA : CFSG.Open.GriessAllModelsStatement) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6P L →
    ∀ s : G, orderOf s = 2 → s ∈ normalizer (L : Set G) → IsL29 (XOut L s) →
      (∀ u ∈ XOut L s, orderOf u = 2 → InducesTypeSome L u 6 1 2 (-1)) →
        InducesTypeSome L s 6 1 2 (-1) := by
  intro G _ _ L hL s hs2 hsn hX H
  have hss : s * s = 1 := ffP2_sq_of_orderOf_eq_two hs2
  have hz : Subgroup.center ↥L = ⊥ := ff_center_eq_bot_six_plus hGA hL
  obtain ⟨V, _, _, _, Q, hQ, e, hdim, hsgn⟩ := ff_exists_model_six_plus hL
  have h5 : 5 ≤ Module.finrank (ZMod 3) V := by omega
  obtain ⟨x, hs⟩ := ff_exists_induces hQ (Or.inr ⟨hdim, Or.inl hsgn⟩) e hsn
  rcases ff_dinv_classify hGA hL hs2 hsn with hc | h0 | h1 | h2 | h3 | h4
  · have hz' : Subgroup.center ↥L = ⊥ := ff_center_eq_bot_six_plus hGA hL
    have hev : 2 ∣ Nat.card ↥L := ff_two_dvd_card_of_isOmega6Plus hL.2
    obtain ⟨-, hXout⟩ := ff_layerCent_eq_of_central hL.1 hz' hev hc
    exact ((ff_not_isOmega6Plus_and_isL29 hL.2) (hXout ▸ hX)).elim
  · exact ((ff_not_isL29_X_of_solvable (C := L ⊓ centralizer ({s} : Set G)) h0.2.2) hX).elim
  · exact (ff_kindP_iff_dinv hGA hL hs2 hsn (k := 1) (by norm_num)).mpr h1
  · exact ((ff_not_isOmega5_and_isL29 h2.2.1) (h2.2.2 ▸ hX)).elim
  · exact ((ff_not_isL29_X_of_solvable (C := L ⊓ centralizer ({s} : Set G)) h3.2) hX).elim
  · have hx2 : x * x = 1 := ff_induces_sq hQ h5 hz e hs hss
    have hKM4 : KM4 x := ff_KM4_of_dinv4 hQ hdim hsgn hz e hs hss h4
    obtain ⟨w, hwX, hw2, hKM0, a, ha⟩ := ff_K4_cover hQ hdim hsgn hx2 hKM4
    let l : ↥L := (ffPhi hz e).symm w
    have hphiu : ffPhi hz e ⟨(l : G), l.2⟩ = w := (ffPhi hz e).apply_symm_apply w
    have huX : (l : G) ∈ XOut L s :=
      (ff_mem_XOut_iff hQ h5 hz e hs l.2).mpr (by rw [hphiu]; exact hwX)
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hwne : w ≠ 1 := fun hw1 => ff_KM0_ne_one hKM0 (by rw [hw1]; rfl)
    have hordw : orderOf w = 2 := orderOf_eq_prime (p := 2) (by rwa [pow_two]) hwne
    have hordl : orderOf (l : G) = 2 := by
      rw [← ff_orderOf_phi hQ hz e l.2, hphiu]
      exact hordw
    have hIndVia : InducesViaP L (Subgroup.center ↥L) hQ e (l : G)
        (projOrthToProjSim Q (w : ProjOrth Q)) := by
      rw [← hphiu]
      exact ff_induces_of_mem hQ hz e l.2
    have hK0 : InducesTypeSome L (l : G) 6 1 4 1 :=
      ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, e,
        projOrthToProjSim Q (w : ProjOrth Q), hdim, hsgn, hIndVia, hKM0⟩
    have hK1 : InducesTypeSome L (l : G) 6 1 2 (-1) := H (l : G) huX hordl
    have hun : (l : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer l.2
    have hD0 : DInv L (l : G) 0 :=
      (ff_kindP_iff_dinv (k := 0) hGA hL hordl hun (by norm_num)).mp
        (show KindP L (l : G) 0 from hK0)
    have hD1 : DInv L (l : G) 1 :=
      (ff_kindP_iff_dinv (k := 1) hGA hL hordl hun (by norm_num)).mp
        (show KindP L (l : G) 1 from hK1)
    exact absurd (ff_dinv_excl L (l : G) (i := 0) (j := 1) (by norm_num) (by norm_num)
      hD0 hD1) (by decide)

end CFSG.OddStandard.SmallF3.Omega
