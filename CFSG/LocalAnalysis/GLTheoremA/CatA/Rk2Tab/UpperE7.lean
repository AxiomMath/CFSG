module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20x
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankArith
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourDescent
public import CFSG.RankThree.PartOne.KE.E7A6Native
public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4RestLevi
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.ExcE6
public import CFSG.RankThree.PartOne.KA5L.Frame
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2E7Levi
public import CFSG.Quasithin.EmptyFaithful.R3c2Types

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType.F4Rest CFSG.RankThree.PartOne.KE
open scoped MatrixGroups

theorem card_le_pow_six_subsystemGroup_e7a6 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1)
    {E : Subgroup (ModGL Tag.E7 K)} (hE : E ≤ subsystemGroup Tag.E7 K e7a6support)
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 6 := by
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_charTwo (K := K) hp hp2
  let e : subsystemGroup Tag.E7 K e7a6support ≃* SL(7, K) :=
    MulEquiv.ofBijective (e7a6Rep K) (e7a6Rep_bijective (K := K))
  have hE' : IsElemAbelian p (E.subgroupOf (subsystemGroup Tag.E7 K e7a6support)) :=
    hEel.subgroupOf _
  have hEmap : IsElemAbelian p
      ((E.subgroupOf (subsystemGroup Tag.E7 K e7a6support)).map e.toMonoidHom) :=
    hE'.map _
  have hbound := card_le_pow_of_injective_GL (G := SL(7, K)) (ι := Fin 7) (K := K) hp hpK
    (φ := Matrix.SpecialLinearGroup.toGL) Matrix.SpecialLinearGroup.toGL_injective hEmap
  have hd : 2 ≤ CFSG.StandardType.OrdPNS.ordQ K p := two_le_ordQ hp hpK hpq
  have h7 : Fintype.card (Fin 7) / CFSG.StandardType.OrdPNS.ordQ K p ≤ 6 := by
    rw [Fintype.card_fin]
    have : 7 / CFSG.StandardType.OrdPNS.ordQ K p ≤ 7 / 2 := Nat.div_le_div_left hd (by norm_num)
    omega
  calc Nat.card E = Nat.card (E.subgroupOf (subsystemGroup Tag.E7 K e7a6support)) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv).symm
    _ = Nat.card ((E.subgroupOf (subsystemGroup Tag.E7 K e7a6support)).map e.toMonoidHom) :=
        (Subgroup.card_map_of_injective e.injective).symm
    _ ≤ p ^ (Fintype.card (Fin 7) / CFSG.StandardType.OrdPNS.ordQ K p) := hbound
    _ ≤ p ^ 6 := Nat.pow_le_pow_right hp.pos h7

open CFSG.LocalAnalysis.RankThreeUC.S15 in
theorem pRank_perpLevi_E7_le_six {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ Nat.card K + 1) :
    CFSG.Open.pRank p (⊤ : Subgroup (CFSG.SeitzReduction.EPilot.perpLevi .E7 K)) ≤ 6 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hn, hK⟩ := FiniteField.card K 2
  have hn' : 1 ≤ (n : ℕ) := by
    have := n.pos
    omega
  have hKn : Nat.card K = 2 ^ (n : ℕ) := by
    rw [← Fintype.card_eq_nat_card]; exact hK
  have hG : CFSG.Open.GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have hT : LieOddRankChev :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20x_lieOddRankChev hG
  have hLM : CFSG.Blueprint.LieModel
      (CFSG.SeitzReduction.EPilot.perpLevi .E7 K ⧸
        Subgroup.center (CFSG.SeitzReduction.EPilot.perpLevi .E7 K)) .POmegaPlus 6 2 (n : ℕ) :=
    CFSG.SeitzReduction.E7Pilot.lieModel_perpLevi_E7_quotient_center (f := (n : ℕ)) hKn
  have hSCM : CFSG.Open.StatedClassicalModel
      (CFSG.SeitzReduction.EPilot.perpLevi .E7 K ⧸
        Subgroup.center (CFSG.SeitzReduction.EPilot.perpLevi .E7 K)) .POmegaPlus 6 2 (n : ℕ) :=
    hLM.statedClassicalModel (by decide)
  have hq : CFSG.Open.IsQuasisimple (CFSG.SeitzReduction.EPilot.perpLevi .E7 K) :=
    CFSG.SeitzReduction.E7Pilot.isQuasisimple_open_perpLevi_E7
  have hpr := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20w_pRank_pomegaPlus hT hq hSCM
    (r := p) hp hp2
  rw [hpr]
  have hd' : p ∣ 2 ^ (n : ℕ) + 1 := by rw [← hKn]; exact hd
  have hd0 : (((2 : ℕ) ^ (n : ℕ) + 1 : ℕ) : ZMod p) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]; exact hd'
  have hpow : (((2 : ℕ) ^ (n : ℕ) : ℕ) : ZMod p) = (2 : ZMod p) ^ (n : ℕ) := by
    push_cast; ring
  have hneg : (2 : ZMod p) ^ (n : ℕ) = -1 := by
    have h := hd0
    push_cast at h
    linear_combination h
  have hsq : (((2 : ℕ) ^ (n : ℕ) : ℕ) : ZMod p) ^ 2 = 1 := by
    rw [hpow, hneg]; ring
  have hne : (((2 : ℕ) ^ (n : ℕ) : ℕ) : ZMod p) ≠ 1 := by
    intro h1
    have h1' : eP (2 ^ (n : ℕ)) p = 1 := by
      unfold eP
      rw [orderOf_eq_one_iff]
      rw [hpow] at h1 ⊢
      exact h1
    have hQ : 1 ≤ 2 ^ (n : ℕ) := by
      have hpos : 0 < 2 ^ (n : ℕ) := pow_pos (by norm_num) _
      omega
    have hd1 : p ∣ 2 ^ (n : ℕ) - 1 := (eP_eq_one_iff hQ).1 h1'
    have h2 : p ∣ (2 ^ (n : ℕ) + 1) - (2 ^ (n : ℕ) - 1) := Nat.dvd_sub hd' hd1
    have h3 : (2 ^ (n : ℕ) + 1) - (2 ^ (n : ℕ) - 1) = 2 := by
      have hQ' : 1 ≤ 2 ^ (n : ℕ) := Nat.one_le_two_pow
      omega
    rw [h3] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  have heP : eP (2 ^ (n : ℕ)) p = 2 := by
    unfold eP
    exact orderOf_eq_prime hsq hne
  have heS : eS (2 ^ (n : ℕ)) p = 1 := by
    rw [eS_eq_eP_div_gcd, heP]; norm_num
  unfold rkOmPlus
  rw [heP, heS]
  norm_num

theorem card_le_pow_six_subsystemGroup_e7D6 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ Nat.card K + 1)
    {E : Subgroup (ModGL Tag.E7 K)}
    (hE : E ≤ subsystemGroup Tag.E7 K {j | j ≠ (0 : Fin 7)})
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 6 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hEadj : E ≤ adjointGroup Tag.E7 K :=
    hE.trans (CFSG.RankThree.Chevalley.subsystemGroup_le_adjointGroup_of_any _)
  set E' : Subgroup (adjointGroup Tag.E7 K) := E.subgroupOf (adjointGroup Tag.E7 K) with hE'def
  have hcard : Nat.card E' = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEadj).toEquiv
  have hE'el : IsElemAbelian p E' := hEel.subgroupOf _
  have hE'perp : E' ≤ CFSG.SeitzReduction.EPilot.perpLevi .E7 K := by
    rw [CFSG.SeitzReduction.E7Pilot.perpLevi_E7_eq_subgroupOf_subsystemGroup]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hE hx
  have hE''el : IsElemAbelian p (E'.subgroupOf (CFSG.SeitzReduction.EPilot.perpLevi .E7 K)) :=
    hE'el.subgroupOf _
  have hcard'' : Nat.card (E'.subgroupOf (CFSG.SeitzReduction.EPilot.perpLevi .E7 K)) =
      Nat.card E' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'perp).toEquiv
  obtain ⟨k, hk⟩ := (hE'el.isPGroup : IsPGroup p E').exists_card_eq
  have hk'' : Nat.card (E'.subgroupOf (CFSG.SeitzReduction.EPilot.perpLevi .E7 K)) = p ^ k := by
    rw [hcard'', hk]
  have hk6 : k ≤ 6 :=
    (CFSG.SectionRank.le_pRank hp.one_lt le_top hE''el hk'').trans
      (pRank_perpLevi_E7_le_six hp hp2 hd)
  calc Nat.card E = Nat.card E' := hcard.symm
    _ = p ^ k := hk
    _ ≤ p ^ 6 := Nat.pow_le_pow_right hp.pos hk6

theorem lieModel_e7LeviE6 {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) :
    CFSG.Blueprint.LieModel
      (CFSG.ComponentClassification.Burgoyne.E2.e7LeviE6 K ⧸
        Subgroup.center (CFSG.ComponentClassification.Burgoyne.E2.e7LeviE6 K)) .E6 0 2 n := by
  have hn : 1 ≤ n := CFSG.Quasithin.R3c2.one_le_of_natCard_eq_two_pow hK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hadm : StatedLieAdmissible .E6 0 2 n := ⟨Nat.prime_two, hn, rfl⟩
  obtain ⟨O, C, hE⟩ := CFSG.ComponentClassification.CatLeafProof.exists_e7_chevalleyExtras K
  obtain ⟨ρ, hρ, hcomm, hψ⟩ := CFSG.ComponentClassification.CatLeafProof.exists_levi_frame
    hE rfl CFSG.ComponentClassification.Burgoyne.E2.e7LeviE6Node
    CFSG.ComponentClassification.Burgoyne.E2.e7LeviE6_adj
    CFSG.ComponentClassification.Burgoyne.E2.e7LeviE6_nadj
  exact (CFSG.ComponentClassification.CatLeafProof.e6_frame_subgroup hadm hK hcomm hρ hψ).choose_spec.2.2.2

theorem isQuasisimple_e7LeviE6_two {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) :
    CFSG.IsQuasisimple (CFSG.ComponentClassification.Burgoyne.E2.e7LeviE6 K) := by
  have hn : 1 ≤ n := CFSG.Quasithin.R3c2.one_le_of_natCard_eq_two_pow hK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hadm : StatedLieAdmissible .E6 0 2 n := ⟨Nat.prime_two, hn, rfl⟩
  obtain ⟨O, C, hE⟩ := CFSG.ComponentClassification.CatLeafProof.exists_e7_chevalleyExtras K
  obtain ⟨ρ, hρ, hcomm, hψ⟩ := CFSG.ComponentClassification.CatLeafProof.exists_levi_frame
    hE rfl CFSG.ComponentClassification.Burgoyne.E2.e7LeviE6Node
    CFSG.ComponentClassification.Burgoyne.E2.e7LeviE6_adj
    CFSG.ComponentClassification.Burgoyne.E2.e7LeviE6_nadj
  exact (CFSG.ComponentClassification.CatLeafProof.e6_frame_subgroup hadm hK hcomm hρ hψ).choose_spec.2.2.1

theorem pRank_e7LeviE6_le_four {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : p ∣ 2 ^ n + 1) :
    CFSG.Open.pRank p (⊤ : Subgroup (CFSG.ComponentClassification.Burgoyne.E2.e7LeviE6 K)) ≤ 4 := by
  haveI : Fact p.Prime := ⟨hp⟩
  let S := CFSG.ComponentClassification.Burgoyne.E2.e7LeviE6 K
  have hQs : CFSG.IsQuasisimple S := isQuasisimple_e7LeviE6_two hK
  have hZ : ¬ p ∣ Nat.card (Subgroup.center S) := by
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models
      (S ⧸ Subgroup.center S) .E6 0 2 n (lieModel_e7LeviE6 hK)
    have hg : CFSG.Blueprint.Multiplier.genericOrders .E6 0 2 n =
        (Nat.gcd 3 (2 ^ n - 1), 1) := rfl
    have he : CFSG.Blueprint.Multiplier.exceptionalOrders .E6 0 2 n = (1, 1) := rfl
    have hcard : Nat.card (CFSG.Open.griessHopfMultiplier (S ⧸ Subgroup.center S)) =
        Nat.gcd 3 (2 ^ n - 1) := by
      rw [Nat.card_congr eM.toEquiv,
        CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_generic_exceptional', hg, he]
      norm_num
    haveI : Finite (CFSG.Open.griessHopfMultiplier (S ⧸ Subgroup.center S)) :=
      Nat.finite_of_card_ne_zero
        (by rw [hcard]; exact (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne')
    have hdvd := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hQs
      (MulEquiv.refl (S ⧸ Subgroup.center S))
    rw [hcard] at hdvd
    intro hpZ
    have h3 : p ∣ Nat.gcd 3 (2 ^ n - 1) := hpZ.trans hdvd
    have hp3 : p = 3 :=
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (h3.trans (Nat.gcd_dvd_left _ _))
    subst hp3
    have h1 : 3 ∣ 2 ^ n - 1 := h3.trans (Nat.gcd_dvd_right _ _)
    have h2 : 3 ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub hd h1
    have h3' : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by
      have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega
    rw [h3'] at h2
    exact (by norm_num : ¬ (3 : ℕ) ∣ 2) h2
  have hq : CFSG.Open.pRank p (⊤ : Subgroup (S ⧸ Subgroup.center S)) ≤ 4 := by
    obtain ⟨-, F', hF', hFin', hFcard', ⟨φ⟩⟩ :=
      (lieModel_e7LeviE6 hK).chevalleyExceptionalModel (by decide : StatedLieTag.E6 ∈ chevalleyExceptionalTags)
    letI : Field F' := hF'
    letI : Finite F' := hFin'
    let χ : AdjointQuotient .E6 F' ≃* adjointGroup .E6 F' :=
      (QuotientGroup.quotientMulEquivOfEq
        (center_adjointGroup_eq_bot (τ := Tag.E6) (K := F'))).trans QuotientGroup.quotientBot
    have he : CFSG.Open.pRank p (⊤ : Subgroup (S ⧸ Subgroup.center S)) =
        CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup .E6 F')) :=
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (φ.trans χ)
    rw [he]
    by_cases hp3 : p = 3
    · subst hp3
      have hord : rk2Ord 3 n = 2 := (rk2Ord_eq_two_iff Nat.prime_three (by norm_num)).mpr hd
      have hF2 : Nat.card F' = 2 ^ n := hFcard'
      exact rk2E6ThreeTwoFrontier F' n hF2 hord
    · have hp5 : 5 ≤ p := by
        have h2 := hp.two_le
        have h4 : p ≠ 4 := by
          rintro rfl
          exact absurd hp (by norm_num)
        omega
      have heord : orderOf ((Nat.card F' : ℕ) : ZMod p) = 2 := by
        rw [hFcard']
        have hcast : (((2 : ℕ) ^ n : ℕ) : ZMod p) = (2 : ZMod p) ^ n := by
          push_cast; ring
        rw [hcast]
        exact (rk2Ord_eq_two_iff hp hp2).mpr hd
      exact CFSG.SectionRank.pRank_le hp.one_lt fun E _ hE =>
        CFSG.LieType.SeitzGeneration.SylowTorus.rank_le
          (CFSG.StandardType.ExcFrames.sylowTorus_adjoint_E6_two F' hp (by omega) heord) hp hE
  calc CFSG.Open.pRank p (⊤ : Subgroup S)
      = CFSG.Open.pRank p (⊤ : Subgroup (S ⧸ Subgroup.center S)) :=
        (CFSG.SectionRank.pRank_quotient_eq (Subgroup.center S) hZ).symm
    _ ≤ 4 := hq

theorem card_le_pow_four_subsystemGroup_e7E6 {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hK : Nat.card K = 2 ^ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : p ∣ 2 ^ n + 1) {E : Subgroup (ModGL Tag.E7 K)}
    (hE : E ≤ subsystemGroup Tag.E7 K {j | j ≠ (6 : Fin 7)})
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 4 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hset : ({j : Fin Tag.E7.rank | j ≠ (6 : Fin 7)} : Set (Fin Tag.E7.rank)) =
      Set.range CFSG.ComponentClassification.Burgoyne.E2.e7LeviE6Node := by
    ext j
    constructor
    · intro hj
      by_contra h
      exact hj (CFSG.ComponentClassification.Burgoyne.E2.eq_six_of_forall_e7LeviE6Node_ne j
        (fun k hk => h ⟨k, hk⟩))
    · rintro ⟨k, rfl⟩
      exact CFSG.ComponentClassification.Burgoyne.E2.e7LeviE6Node_ne_six k
  have hmap : (CFSG.ComponentClassification.Burgoyne.E2.e7LeviE6 K).map
        (adjointGroup Tag.E7 K).subtype =
      subsystemGroup Tag.E7 K
        (Set.range CFSG.ComponentClassification.Burgoyne.E2.e7LeviE6Node) :=
    CFSG.ComponentClassification.CatLeafProof.map_subtype_iSup_rankOne
      CFSG.ComponentClassification.Burgoyne.E2.e7LeviE6Node
  rw [hset, ← hmap] at hE
  set EA : Subgroup (adjointGroup Tag.E7 K) :=
    E.comap (adjointGroup Tag.E7 K).subtype with hEAdef
  have hErange : E ≤ (adjointGroup Tag.E7 K).subtype.range :=
    hE.trans (Subgroup.map_le_range _ _)
  have hEAle : EA ≤ CFSG.ComponentClassification.Burgoyne.E2.e7LeviE6 K := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hE hx
    rwa [show y = x from Subtype.ext hyx] at hy
  have hcard : Nat.card EA = Nat.card E := by
    calc Nat.card EA = Nat.card (EA.map (adjointGroup Tag.E7 K).subtype) :=
          (Subgroup.card_map_of_injective (adjointGroup Tag.E7 K).subtype_injective).symm
      _ = Nat.card E := by rw [hEAdef, Subgroup.map_comap_eq_self hErange]
  have hEAel : IsElemAbelian p EA :=
    isElemAbelian_comap (adjointGroup Tag.E7 K).subtype_injective hEel
  have hpr := pRank_e7LeviE6_le_four hK hp hp2 hd
  have hEAel' : IsElemAbelian p
      (EA.subgroupOf (CFSG.ComponentClassification.Burgoyne.E2.e7LeviE6 K)) :=
    hEAel.subgroupOf _
  have hcard' : Nat.card (EA.subgroupOf (CFSG.ComponentClassification.Burgoyne.E2.e7LeviE6 K)) =
      Nat.card EA :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEAle).toEquiv
  obtain ⟨k, hk⟩ := (hEAel.isPGroup : IsPGroup p EA).exists_card_eq
  have hk' : Nat.card (EA.subgroupOf (CFSG.ComponentClassification.Burgoyne.E2.e7LeviE6 K)) =
      p ^ k := by rw [hcard', hk]
  have hk4 : k ≤ 4 := (CFSG.SectionRank.le_pRank hp.one_lt le_top hEAel' hk').trans hpr
  calc Nat.card E = Nat.card EA := hcard.symm
    _ = p ^ k := hk
    _ ≤ p ^ 4 := Nat.pow_le_pow_right hp.pos hk4

theorem card_le_pow_three_subsystemGroup_e7a6 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1)
    {E : Subgroup (ModGL Tag.E7 K)} (hE : E ≤ subsystemGroup Tag.E7 K e7a6support)
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 3 := by
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_charTwo (K := K) hp hp2
  let e : subsystemGroup Tag.E7 K e7a6support ≃* SL(7, K) :=
    MulEquiv.ofBijective (e7a6Rep K) (e7a6Rep_bijective (K := K))
  have hE' : IsElemAbelian p (E.subgroupOf (subsystemGroup Tag.E7 K e7a6support)) :=
    hEel.subgroupOf _
  have hEmap : IsElemAbelian p
      ((E.subgroupOf (subsystemGroup Tag.E7 K e7a6support)).map e.toMonoidHom) :=
    hE'.map _
  have hbound := card_le_pow_of_injective_GL (G := SL(7, K)) (ι := Fin 7) (K := K) hp hpK
    (φ := Matrix.SpecialLinearGroup.toGL) Matrix.SpecialLinearGroup.toGL_injective hEmap
  have hd : 2 ≤ CFSG.StandardType.OrdPNS.ordQ K p := two_le_ordQ hp hpK hpq
  have h7 : Fintype.card (Fin 7) / CFSG.StandardType.OrdPNS.ordQ K p ≤ 3 := by
    rw [Fintype.card_fin]
    have : 7 / CFSG.StandardType.OrdPNS.ordQ K p ≤ 7 / 2 :=
      Nat.div_le_div_left hd (by norm_num)
    omega
  calc Nat.card E = Nat.card (E.subgroupOf (subsystemGroup Tag.E7 K e7a6support)) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv).symm
    _ = Nat.card ((E.subgroupOf (subsystemGroup Tag.E7 K e7a6support)).map e.toMonoidHom) :=
        (Subgroup.card_map_of_injective e.injective).symm
    _ ≤ p ^ (Fintype.card (Fin 7) / CFSG.StandardType.OrdPNS.ordQ K p) := hbound
    _ ≤ p ^ 3 := Nat.pow_le_pow_right hp.pos h7

theorem card_le_pow_one_subsystemGroup_e7node {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1)
    (i : Fin Tag.E7.rank) {E : Subgroup (ModGL Tag.E7 K)}
    (hE : E ≤ subsystemGroup Tag.E7 K {i}) (hEel : IsElemAbelian p E) :
    Nat.card E ≤ p ^ 1 := by
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_charTwo (K := K) hp hp2
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hinj : Function.Injective (simpleRootSL2 Tag.E7 K i) :=
    CFSG.LieType.Chevalley.E6GraphRadical.simpleRootSL2_injective_of_two h2 i
  have hrange : (simpleRootSL2 Tag.E7 K i).range = subsystemGroup Tag.E7 K {i} := by
    rw [range_simpleRootSL2, subsystemGroup]
    congr 1
    ext g
    constructor
    · rintro (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact ⟨i, by simp, c, Or.inl rfl⟩
      · exact ⟨i, by simp, c, Or.inr rfl⟩
    · rintro ⟨j, hj, c, rfl | rfl⟩
      · rw [Set.mem_singleton_iff] at hj
        subst hj
        exact Or.inl ⟨c, rfl⟩
      · rw [Set.mem_singleton_iff] at hj
        subst hj
        exact Or.inr ⟨c, rfl⟩
  let Et : Subgroup (SL(2, K)) := E.comap (simpleRootSL2 Tag.E7 K i)
  have hEtrange : E ≤ (simpleRootSL2 Tag.E7 K i).range := hrange ▸ hE
  have hEtcard : Nat.card Et = Nat.card E := by
    calc Nat.card Et = Nat.card (Et.map (simpleRootSL2 Tag.E7 K i)) :=
          (Subgroup.card_map_of_injective hinj).symm
      _ = Nat.card E := by rw [Subgroup.map_comap_eq_self hEtrange]
  have hEtel : IsElemAbelian p Et := isElemAbelian_comap hinj hEel
  have hbound := card_le_pow_of_injective_GL (G := SL(2, K)) (ι := Fin 2) (K := K) hp hpK
    (φ := Matrix.SpecialLinearGroup.toGL) Matrix.SpecialLinearGroup.toGL_injective hEtel
  have hd : 2 ≤ CFSG.StandardType.OrdPNS.ordQ K p := two_le_ordQ hp hpK hpq
  have h2d : Fintype.card (Fin 2) / CFSG.StandardType.OrdPNS.ordQ K p ≤ 1 := by
    rw [Fintype.card_fin]
    have : 2 / CFSG.StandardType.OrdPNS.ordQ K p ≤ 2 / 2 :=
      Nat.div_le_div_left hd (by norm_num)
    omega
  calc Nat.card E = Nat.card Et := hEtcard.symm
    _ ≤ p ^ (Fintype.card (Fin 2) / CFSG.StandardType.OrdPNS.ordQ K p) := hbound
    _ ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos h2d

theorem card_le_pow_three_subsystemGroup_e7a5 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1)
    {E : Subgroup (ModGL Tag.E7 K)} (hE : E ≤ subsystemGroup Tag.E7 K (a5Nodes Tag.E7))
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 3 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_charTwo (K := K) hp hp2
  have hpker : ¬ p ∣ Nat.card (CFSG.RankThree.PartOne.KA5L.a5Frame K).ker := by
    intro hd
    have hcenter : Nat.card (Subgroup.center (SL(6, K))) ∣ Nat.card K - 1 :=
      (CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd (n := 6) (by norm_num) K).trans
        (Nat.gcd_dvd_right _ _)
    exact hpq (hd.trans ((Subgroup.card_dvd_of_le
      (CFSG.RankThree.PartOne.KA5L.ker_a5Frame_le_center (L := K))).trans hcenter))
  have hErange : E ≤ (CFSG.RankThree.PartOne.KA5L.a5Frame K).range := by
    rw [CFSG.RankThree.PartOne.KA5L.range_a5Frame]
    exact hE
  have hrank_range : CFSG.Open.pRank p (⊤ : Subgroup ((CFSG.RankThree.PartOne.KA5L.a5Frame K).range)) ≤ 3 := by
    have h1 : CFSG.Open.pRank p (⊤ : Subgroup ((CFSG.RankThree.PartOne.KA5L.a5Frame K).range)) =
        CFSG.Open.pRank p (⊤ : Subgroup (SL(6, K) ⧸ (CFSG.RankThree.PartOne.KA5L.a5Frame K).ker)) :=
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt
        (QuotientGroup.quotientKerEquivRange (CFSG.RankThree.PartOne.KA5L.a5Frame K)).symm
    rw [h1, CFSG.SectionRank.pRank_quotient_eq (CFSG.RankThree.PartOne.KA5L.a5Frame K).ker hpker]
    refine CFSG.SectionRank.pRank_le hp.one_lt fun F _ hF => ?_
    have hb := card_le_pow_of_injective_GL (G := SL(6, K)) (ι := Fin 6) (K := K) hp hpK
      (φ := Matrix.SpecialLinearGroup.toGL) Matrix.SpecialLinearGroup.toGL_injective hF
    have hd : 2 ≤ CFSG.StandardType.OrdPNS.ordQ K p := two_le_ordQ hp hpK hpq
    have h63 : Fintype.card (Fin 6) / CFSG.StandardType.OrdPNS.ordQ K p ≤ 3 := by
      rw [Fintype.card_fin]
      have : 6 / CFSG.StandardType.OrdPNS.ordQ K p ≤ 6 / 2 :=
        Nat.div_le_div_left hd (by norm_num)
      omega
    exact hb.trans (Nat.pow_le_pow_right hp.pos h63)
  have hErank : CFSG.Open.pRank p (⊤ : Subgroup E) ≤ 3 := by
    calc CFSG.Open.pRank p (⊤ : Subgroup E) = CFSG.Open.pRank p E :=
          (CFSG.SectionRank.pRank_eq_pRank_top_subgroup E).symm
      _ ≤ CFSG.Open.pRank p ((CFSG.RankThree.PartOne.KA5L.a5Frame K).range) :=
          CFSG.SectionRank.pRank_mono hp.one_lt hErange
      _ = CFSG.Open.pRank p (⊤ : Subgroup ((CFSG.RankThree.PartOne.KA5L.a5Frame K).range)) :=
          CFSG.SectionRank.pRank_eq_pRank_top_subgroup _
      _ ≤ 3 := hrank_range
  have hEcard : Nat.card E = p ^ CFSG.Open.pRank p (⊤ : Subgroup E) := by
    obtain ⟨k, hk⟩ := (hEel.isPGroup : IsPGroup p E).exists_card_eq
    have hk' : k = CFSG.Open.pRank p (⊤ : Subgroup E) := by
      rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup E]
      refine le_antisymm (CFSG.SectionRank.le_pRank hp.one_lt (le_refl E) hEel hk) ?_
      refine CFSG.SectionRank.pRank_le hp.one_lt fun F hF hFel => ?_
      calc Nat.card F ≤ Nat.card E := Subgroup.card_le_of_le hF
        _ = p ^ k := hk
    rw [hk, hk']
  rw [hEcard]
  exact Nat.pow_le_pow_right hp.pos hErank

theorem card_le_pow_one_subsystemGroup_e7a2_56 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1)
    {E : Subgroup (ModGL Tag.E7 K)}
    (hE : E ≤ subsystemGroup Tag.E7 K
      ({CFSG.RankThree.PartOne.KA5L.a5chain 3, CFSG.RankThree.PartOne.KA5L.a5chain 4} :
        Set (Fin Tag.E7.rank)))
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_charTwo (K := K) hp hp2
  let θ : SL(3, K) →* ModGL Tag.E7 K :=
    (CFSG.RankThree.PartOne.KA5L.a5Frame K).comp (CFSG.ClassicalInvolution.WeakCT.blockSL K 6 3 3 (by omega))
  have hθinj : Function.Injective θ :=
    CFSG.ClassicalInvolution.WeakCT.comp_blockSL_injective
      (CFSG.RankThree.PartOne.KA5L.ker_a5Frame_le_center (L := K)) (by omega) (by omega)
  have hgen : ∀ g ∈ {g : ModGL Tag.E7 K | ∃ i ∈
      ({CFSG.RankThree.PartOne.KA5L.a5chain 3, CFSG.RankThree.PartOne.KA5L.a5chain 4} :
        Set (Fin Tag.E7.rank)), ∃ c : K,
        g = xUnit Tag.E7 K i c ∨ g = yUnit Tag.E7 K i c}, g ∈ θ.range := by
    rintro g ⟨i, hi, c, hg | hg⟩
    · rw [hg]
      have hi' : i = CFSG.RankThree.PartOne.KA5L.a5chain 3 ∨
          i = CFSG.RankThree.PartOne.KA5L.a5chain 4 := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hi
      rcases hi' with rfl | rfl
      · refine ⟨CFSG.ClassicalInvolution.WeakCT.blockSL K 3 2 0 (by omega) (uSL c), ?_⟩
        show (CFSG.RankThree.PartOne.KA5L.a5Frame K)
          (CFSG.ClassicalInvolution.WeakCT.blockSL K 6 3 3 (by omega)
            (CFSG.ClassicalInvolution.WeakCT.blockSL K 3 2 0 (by omega) (uSL c))) =
          xUnit Tag.E7 K (CFSG.RankThree.PartOne.KA5L.a5chain 3) c
        rw [← CFSG.LieType.Chevalley.simpleRootSL2_uSL]
        rw [← CFSG.RankThree.PartOne.KA5L.a5Frame_comp_blockSL2, MonoidHom.comp_apply]
        congr 1
        rw [CFSG.ClassicalInvolution.WeakCT.blockSL_comp_apply (i := 3) (k := 3) (j := 0)
          (l := 2) (by omega) (by omega)]
        rfl
      · refine ⟨CFSG.ClassicalInvolution.WeakCT.blockSL K 3 2 1 (by omega) (uSL c), ?_⟩
        show (CFSG.RankThree.PartOne.KA5L.a5Frame K)
          (CFSG.ClassicalInvolution.WeakCT.blockSL K 6 3 3 (by omega)
            (CFSG.ClassicalInvolution.WeakCT.blockSL K 3 2 1 (by omega) (uSL c))) =
          xUnit Tag.E7 K (CFSG.RankThree.PartOne.KA5L.a5chain 4) c
        rw [← CFSG.LieType.Chevalley.simpleRootSL2_uSL]
        rw [← CFSG.RankThree.PartOne.KA5L.a5Frame_comp_blockSL2, MonoidHom.comp_apply]
        congr 1
        rw [CFSG.ClassicalInvolution.WeakCT.blockSL_comp_apply (i := 3) (k := 3) (j := 1)
          (l := 2) (by omega) (by omega)]
        rfl
    · rw [hg]
      have hi' : i = CFSG.RankThree.PartOne.KA5L.a5chain 3 ∨
          i = CFSG.RankThree.PartOne.KA5L.a5chain 4 := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hi
      rcases hi' with rfl | rfl
      · refine ⟨CFSG.ClassicalInvolution.WeakCT.blockSL K 3 2 0 (by omega) (vSL c), ?_⟩
        show (CFSG.RankThree.PartOne.KA5L.a5Frame K)
          (CFSG.ClassicalInvolution.WeakCT.blockSL K 6 3 3 (by omega)
            (CFSG.ClassicalInvolution.WeakCT.blockSL K 3 2 0 (by omega) (vSL c))) =
          yUnit Tag.E7 K (CFSG.RankThree.PartOne.KA5L.a5chain 3) c
        rw [← CFSG.LieType.Chevalley.simpleRootSL2_vSL]
        rw [← CFSG.RankThree.PartOne.KA5L.a5Frame_comp_blockSL2, MonoidHom.comp_apply]
        congr 1
        rw [CFSG.ClassicalInvolution.WeakCT.blockSL_comp_apply (i := 3) (k := 3) (j := 0)
          (l := 2) (by omega) (by omega)]
        rfl
      · refine ⟨CFSG.ClassicalInvolution.WeakCT.blockSL K 3 2 1 (by omega) (vSL c), ?_⟩
        show (CFSG.RankThree.PartOne.KA5L.a5Frame K)
          (CFSG.ClassicalInvolution.WeakCT.blockSL K 6 3 3 (by omega)
            (CFSG.ClassicalInvolution.WeakCT.blockSL K 3 2 1 (by omega) (vSL c))) =
          yUnit Tag.E7 K (CFSG.RankThree.PartOne.KA5L.a5chain 4) c
        rw [← CFSG.LieType.Chevalley.simpleRootSL2_vSL]
        rw [← CFSG.RankThree.PartOne.KA5L.a5Frame_comp_blockSL2, MonoidHom.comp_apply]
        congr 1
        rw [CFSG.ClassicalInvolution.WeakCT.blockSL_comp_apply (i := 3) (k := 3) (j := 1)
          (l := 2) (by omega) (by omega)]
        rfl
  have hEθ : E ≤ θ.range := by
    refine hE.trans ?_
    rw [subsystemGroup]
    exact (Subgroup.closure_le _).2 hgen
  let Et : Subgroup (SL(3, K)) := E.comap θ
  have hEtcard : Nat.card Et = Nat.card E := by
    calc Nat.card Et = Nat.card (Et.map θ) := (Subgroup.card_map_of_injective hθinj).symm
      _ = Nat.card E := by rw [Subgroup.map_comap_eq_self hEθ]
  have hEtel : IsElemAbelian p Et := isElemAbelian_comap hθinj hEel
  have hbound := card_le_pow_of_injective_GL (G := SL(3, K)) (ι := Fin 3) (K := K) hp hpK
    (φ := Matrix.SpecialLinearGroup.toGL) Matrix.SpecialLinearGroup.toGL_injective hEtel
  have hd : 2 ≤ CFSG.StandardType.OrdPNS.ordQ K p := two_le_ordQ hp hpK hpq
  have h31 : Fintype.card (Fin 3) / CFSG.StandardType.OrdPNS.ordQ K p ≤ 1 := by
    rw [Fintype.card_fin]
    have : 3 / CFSG.StandardType.OrdPNS.ordQ K p ≤ 3 / 2 :=
      Nat.div_le_div_left hd (by norm_num)
    omega
  calc Nat.card E = Nat.card Et := hEtcard.symm
    _ ≤ p ^ (Fintype.card (Fin 3) / CFSG.StandardType.OrdPNS.ordQ K p) := hbound
    _ ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos h31

theorem card_le_pow_four_subsystemGroup_e7A4 {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hK : Nat.card K = 2 ^ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : p ∣ 2 ^ n + 1) {E : Subgroup (ModGL Tag.E7 K)}
    (hE : E ≤ subsystemGroup Tag.E7 K
      ({CFSG.RankThree.PartOne.KE.e7Index 0, CFSG.RankThree.PartOne.KE.e7Index 1,
        CFSG.RankThree.PartOne.KE.e7Index 2, CFSG.RankThree.PartOne.KE.e7Index 3} :
        Set (Fin Tag.E7.rank)))
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 4 := by
  refine card_le_pow_four_subsystemGroup_e7E6 hK hp hp2 hd (hE.trans (subsystemGroup_mono ?_)) hEel
  intro j hj
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hj
  rintro h
  have hval : (j : ℕ) = 6 := congrArg Fin.val h
  rcases hj with rfl | rfl | rfl | rfl <;>
    norm_num [CFSG.RankThree.PartOne.KE.e7Index] at hval

theorem card_le_pow_four_subsystemGroup_e7D5 {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hK : Nat.card K = 2 ^ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : p ∣ 2 ^ n + 1) {E : Subgroup (ModGL Tag.E7 K)}
    (hE : E ≤ subsystemGroup Tag.E7 K
      ({CFSG.RankThree.PartOne.KE.e7Index 0, CFSG.RankThree.PartOne.KE.e7Index 1,
        CFSG.RankThree.PartOne.KE.e7Index 2, CFSG.RankThree.PartOne.KE.e7Index 3,
        CFSG.RankThree.PartOne.KE.e7Index 4} : Set (Fin Tag.E7.rank)))
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 4 := by
  refine card_le_pow_four_subsystemGroup_e7E6 hK hp hp2 hd (hE.trans (subsystemGroup_mono ?_)) hEel
  intro j hj
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hj
  rintro h
  have hval : (j : ℕ) = 6 := congrArg Fin.val h
  rcases hj with rfl | rfl | rfl | rfl | rfl <;>
    norm_num [CFSG.RankThree.PartOne.KE.e7Index] at hval

theorem bound_subgroup_of_ambient {τ : Tag} {K : Type} [Field K] {p k : ℕ}
    {J : Set (Fin τ.rank)}
    (h : ∀ E : Subgroup (ModGL τ K), E ≤ subsystemGroup τ K J → IsElemAbelian p E →
      Nat.card E ≤ p ^ k) :
    ∀ F : Subgroup (subsystemGroup τ K J), IsElemAbelian p F → Nat.card F ≤ p ^ k := by
  intro F hF
  have hF' : IsElemAbelian p (F.map (subsystemGroup τ K J).subtype) := hF.map _
  have hcard : Nat.card (F.map (subsystemGroup τ K J).subtype) = Nat.card F :=
    Subgroup.card_map_of_injective (subsystemGroup τ K J).subtype_injective
  have hle : F.map (subsystemGroup τ K J).subtype ≤ subsystemGroup τ K J := by
    simpa [Subgroup.range_subtype] using
      Subgroup.map_le_range (subsystemGroup τ K J).subtype F
  rw [← hcard]
  exact h _ hle hF'

theorem twoLocalRank_le_of_elemAbelian_bound {G : Type} [Group G] [Finite G] {p k : ℕ}
    (hp : p.Prime)
    (h : ∀ R E : Subgroup G, R ≠ ⊥ → IsPGroup 2 R →
      E ≤ Subgroup.normalizer (R : Set G) → IsElemAbelian p E → Nat.card E ≤ p ^ k) :
    GLATwoLocalRank p G ≤ k := by
  show sSup {k' | ∃ H : Subgroup G, IsTwoLocal H ∧ CFSG.Open.pRank p H = k'} ≤ k
  refine csSup_le' ?_
  rintro k' ⟨H, hH, rfl⟩
  obtain ⟨R, hR, hR2, rfl⟩ := hH
  exact CFSG.SectionRank.pRank_le hp.one_lt fun E hE hEel => h R E hR hR2 hE hEel

end CFSG.LocalAnalysis.GLTheoremA
