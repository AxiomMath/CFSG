module

public import CFSG.GF2Type.Smith1979.WidthFourKP.TrialityFusion
public import CFSG.GF2Type.Smith1979.W4AsTI
public import CFSG.CGT.PushingUpLit.SolKR2.Engine
public import CFSG.Adapters.LieModelSmallOrders
public import CFSG.GF2Type.Smith1979.WidthFourKPLeaves

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4Tri

open CFSG CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S14 CFSG.CGT.Timmesfeld75 CFSG.RankThree.OrthogonalInvolutions
  CFSG.Timmesfeld CFSG.Timmesfeld.CorB
open scoped MatrixGroups commutatorElement
open Subgroup Module QuadraticMap

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem setup_z (hM : Nat.card S.Mbar ∣ 1512) (hw : S.width = 4) (hno : S11.NoA2All S)
    (hirr : ¬ S.IsReducible) (H : Hyp4 S g) (C : Cons311 S g)
    (h8 : StatedClassicalModel (M0 S g) .PSL 2 2 3) :
    CFSG.Timmesfeld.CorB.Setup S.z := by
  have htoQ : ∀ τ : G, τ ∈ CFSG.Timmesfeld.CorB.conjCent S.z → τ ∈ S.QG := by
    rintro τ ⟨hτcomm, hτconj⟩
    exact mem_QG_of_isConj_of_mem_M hM hw H C hirr h8 hno hτconj (S.mem_M_iff.mpr hτcomm)
  have hle : CFSG.Timmesfeld.CorB.weakClosure S.z ≤ S.QG :=
    (Subgroup.closure_le (K := S.QG)).mpr htoQ
  refine ⟨S.orderOf_z, S.isPGroup_QG.to_le hle, ?_, ?_⟩
  ·
    have hcomm : ⁅S.QG, S.QG⁆ ≤ Subgroup.zpowers S.z := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      rcases S.commutator_eq_one_or_z hx hy with h | h
      · rw [commutatorElement_def, h]
        exact Subgroup.one_mem _
      · rw [commutatorElement_def, h]
        exact Subgroup.mem_zpowers S.z
    have hzQ : ⁅Subgroup.zpowers S.z, S.QG⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_iff.mpr fun y hy => S.z_comm_QG hy
    rw [eq_bot_iff]
    calc ⁅⁅CFSG.Timmesfeld.CorB.weakClosure S.z, CFSG.Timmesfeld.CorB.weakClosure S.z⁆,
          CFSG.Timmesfeld.CorB.weakClosure S.z⁆
        ≤ ⁅⁅S.QG, S.QG⁆, S.QG⁆ :=
          Subgroup.commutator_mono (Subgroup.commutator_mono hle hle) hle
      _ ≤ ⁅Subgroup.zpowers S.z, S.QG⁆ := Subgroup.commutator_mono hcomm le_rfl
      _ = ⊥ := hzQ
  ·
    intro τ hτcomm hτconj hτne
    have hτQ : τ ∈ S.QG := htoQ τ ⟨hτcomm, hτconj⟩
    have hτ1 : τ ≠ 1 := SME.ne_one_of_isConj S hτconj
    obtain ⟨u, hu, huτ⟩ := S.exists_conj_eq_mul_z hτQ hτ1 hτne
    have hconj : IsConj S.z (u * τ * u⁻¹) :=
      hτconj.trans (isConj_iff.mpr ⟨u, rfl⟩)
    have hzτ : u * τ * u⁻¹ = S.z * τ := by
      rw [huτ, S.z_comm_QG hτQ]
    rwa [hzτ] at hconj

theorem exists_orderOf_mul_eq_four (hw : S.width = 4) (H : Hyp4 S g) (C : Cons311 S g)
    (hirr : ¬ S.IsReducible) (h8 : StatedClassicalModel (M0 S g) .PSL 2 2 3) :
    ∃ d e : G, IsConj S.z d ∧ IsConj S.z e ∧ orderOf (d * e) = 4 := by
  obtain ⟨m, hm⟩ := exists_polar_ne_zero H hirr
  let d : G := g * S.z * g⁻¹
  let e : G := (m : G) * d * (m : G)⁻¹
  have hd : IsConj S.z d := isConj_iff.mpr ⟨g, rfl⟩
  have he : IsConj S.z e := by
    refine isConj_iff.mpr ⟨(m : G) * g, ?_⟩
    dsimp [e, d]
    group
  have haQ : d ∈ S.QG := H.conj_mem
  have heQ : e ∈ S.QG := S.conj_mem_QG m.2 H.conj_mem
  have hd2 : d * d = 1 := by
    dsimp [d]
    calc (g * S.z * g⁻¹) * (g * S.z * g⁻¹) = g * (S.z * S.z) * g⁻¹ := by group
      _ = 1 := by rw [S.z_mul_z]; group
  have he2 : e * e = 1 := by
    dsimp [e]
    calc ((m : G) * d * (m : G)⁻¹) * ((m : G) * d * (m : G)⁻¹)
        = (m : G) * (d * d) * (m : G)⁻¹ := by group
      _ = 1 := by rw [hd2]; group
  have hne : d * e ≠ e * d := by
    intro h
    have hcle : S.cl e = ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl d) := by
      dsimp [e, d]
      have hg : (m : G) * g * S.z * ((m : G) * g)⁻¹ =
          (m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹ := by group
      rw [← hg]
      exact (S.ρ_cl_conj_z m.2 H.conj_mem).symm
    have hcl : polar S.q (S.cl d) (S.cl e) = 0 :=
      (S.polar_cl_eq_zero_iff haQ heQ).mpr h
    rw [hcle] at hcl
    exact hm hcl
  refine ⟨d, e, hd, he, ?_⟩
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
  have hsq : ¬ (d * e) ^ 2 ^ 1 = 1 := by
    intro h
    apply hne
    have h1 : (d * e) * (d * e) = 1 := by
      rw [← _root_.sq]; simpa using h
    calc d * e = (d * e)⁻¹ := eq_inv_of_mul_eq_one_left h1
      _ = e * d := by rw [mul_inv_rev, hdi, hei]
  have h4 : (d * e) ^ 2 ^ (1 + 1) = 1 := by
    simpa using S.pow_four_eq_one (S.QG.mul_mem haQ heQ)
  exact orderOf_eq_prime_pow hsq h4

theorem card_rootGroup_eq_two (hM : Nat.card S.Mbar ∣ 1512) (hw : S.width = 4)
    (hno : S11.NoA2All S) (hirr : ¬ S.IsReducible) (H : Hyp4 S g) (C : Cons311 S g)
    (h8 : StatedClassicalModel (M0 S g) .PSL 2 2 3)
    {d : G} (hd : d ∈ CFSG.Timmesfeld.CorB.cls S.z) :
    Nat.card (CFSG.Timmesfeld.rootGroup (CFSG.Timmesfeld.CorB.cls S.z) d) = 2 := by
  have hset : CFSG.Timmesfeld.rootSet (CFSG.Timmesfeld.CorB.cls S.z) S.z = {S.z} := by
    ext e
    constructor
    · intro he
      have heD : e ∈ CFSG.Timmesfeld.CorB.cls S.z := he.1
      have heComm : Commute e S.z :=
        (he.2 S.z (CFSG.Timmesfeld.CorB.mem_cls_self S.z)).mpr (Commute.refl S.z)
      have heM : e ∈ S.M := S.mem_M_iff.mpr heComm.eq
      have heQ : e ∈ S.QG := mem_QG_of_isConj_of_mem_M hM hw H C hirr h8 hno heD heM
      have horth : ∀ m : S.M, polar S.q (S.cl e)
          (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) = 0 := by
        intro m
        set f := (m : G) * g * S.z * ((m : G) * g)⁻¹ with hf
        have hfD : f ∈ CFSG.Timmesfeld.CorB.cls S.z := isConj_iff.mpr ⟨(m : G) * g, rfl⟩
        have hfQ : f ∈ S.QG := by
          rw [hf]
          have h : (m : G) * g * S.z * ((m : G) * g)⁻¹ =
              (m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹ := by group
          rw [h]
          exact S.conj_mem_QG m.2 H.conj_mem
        have hcommz : Commute S.z f := by
          have hfm : (m : G) * S.z * (m : G)⁻¹ = S.z := by
            rw [S.z_comm m.2]; group
          have h := commute_conj (m : G) (S.z_comm_QG H.conj_mem)
          rw [hfm] at h
          rw [hf]
          have e : (m : G) * g * S.z * ((m : G) * g)⁻¹ =
              (m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹ := by group
          rw [e]
          exact h.symm
        have hef : Commute e f := (he.2 f hfD).mpr hcommz
        have hcle : S.cl f = ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) := by
          rw [hf]
          exact (S.ρ_cl_conj_z m.2 H.conj_mem).symm
        rw [← hcle]
        exact (S.polar_cl_eq_zero_iff heQ hfQ).mpr hef.eq
      have hzero : S.cl e = 0 := by
        refine S.q_nondegenerate.1 (S.cl e) fun w => ?_
        have hw : w ∈ Submodule.span (ZMod 2) (Set.range fun m : S.M =>
            ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))) := by
          rw [span_points_eq_top H hirr]
          trivial
        have horth' : ∀ u ∈ Submodule.span (ZMod 2) (Set.range fun m : S.M =>
            ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))),
            polar S.q (S.cl e) u = 0 := by
          intro u hu
          induction hu using Submodule.span_induction with
          | mem x hx =>
            obtain ⟨m, rfl⟩ := hx
            exact horth m
          | zero => rw [polar_zero_right]
          | add x y _ _ hx hy => rw [polar_add_right, hx, hy, add_zero]
          | smul a x _ hx => rw [polar_smul_right, hx, smul_zero]
        rw [polarBilin_apply_apply]
        exact horth' w hw
      rcases (S.cl_eq_zero_iff heQ).mp hzero with h1 | hz
      · exact absurd h1 (SME.ne_one_of_isConj S heD)
      · simp [hz]
    · rintro rfl
      exact ⟨CFSG.Timmesfeld.CorB.mem_cls_self S.z, fun f _ => Iff.rfl⟩
  have hz : Nat.card (CFSG.Timmesfeld.rootGroup (CFSG.Timmesfeld.CorB.cls S.z) S.z) = 2 := by
    rw [CFSG.Timmesfeld.rootGroup, hset, ← Subgroup.zpowers_eq_closure, Nat.card_zpowers,
      S.orderOf_z]
  have hclass : ∃ d₀ : G, CFSG.Timmesfeld.CorB.cls S.z = {x | IsConj d₀ x} := ⟨S.z, rfl⟩
  obtain ⟨k, hk⟩ := isConj_iff.mp hd
  rw [← hk, CFSG.Timmesfeld.rootGroup_conj hclass k S.z,
    Subgroup.card_map_of_injective (MulAut.conj k).injective]
  exact hz

end CFSG.GF2Type.Smith1979.W4Tri

namespace CFSG.GF2Type.Smith1979

open CFSG CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.GF2Type.Smith1979.W4Tri CFSG.GF2Type.Smith1979.W4As
  CFSG.Timmesfeld CFSG.Timmesfeld.CorB
  CFSG.CGT.PushingUpLit.SolKR2
open Subgroup Module


theorem widthFourTrialityCase_holds : WidthFourTrialityCase := by
  intro G _ _ _ hnab hs hK S hw hno hirr g H C h8
  have hM : Nat.card S.Mbar ∣ 1512 := W4As.card_Mbar_dvd_1512 H hirr h8
  have hsetup : CorB.Setup S.z := W4Tri.setup_z hM hw hno hirr H C h8
  have hnd : ∃ d e : G, IsConj S.z d ∧ IsConj S.z e ∧ orderOf (d * e) = 4 :=
    W4Tri.exists_orderOf_mul_eq_four hw H C hirr h8
  have hHyp : CFSG.Timmesfeld.Hyp G (CorB.cls S.z) :=
    Engine.hyp_of_simple hnab hsetup hnd
  have hnoOdd : CorB.NoOddCent (CorB.cls S.z) := hsetup.noOddCent
  have hQ9 : Nat.card S.QG = 2 ^ 9 := by
    rw [S.card_QG_eq_card_Q, S.card_Q_eq, hw]
  have hdvd : 2 ^ 9 ∣ Nat.card G := by
    rw [← hQ9]
    exact Subgroup.card_subgroup_dvd_card S.QG
  have hroot2 : ∀ d ∈ CorB.cls S.z,
      Nat.card (CFSG.Timmesfeld.rootGroup (CorB.cls S.z) d) = 2 :=
    fun d hd => W4Tri.card_rootGroup_eq_two hM hw hno hirr H C h8 hd
  rcases CorB.outcomeTwo_of_noOddCent hHyp hnoOdd with
      ⟨f, hf1, ⟨d, hd, hrg⟩, hL⟩ | ⟨f, hf2, ⟨d, hd, hrg⟩, hL⟩ |
      ⟨f, hf1, ⟨d, hd, hrg⟩, hL⟩ | hU3 | hA6 | hJ2
  ·
    have hf : f = 1 := by
      have h2 : 2 ^ f = 2 := by rw [← hrg]; exact hroot2 d hd
      exact Nat.pow_right_injective le_rfl (by simpa using h2)
    rw [hf] at hL
    have hcard : Nat.card G = 168 := CFSG.Blueprint.LieModel.card_psl_three_two hL
    rw [hcard] at hdvd
    norm_num at hdvd
  ·
    have h2 : 2 ^ f = 2 := by rw [← hrg]; exact hroot2 d hd
    have h4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
    rw [h2] at h4
    norm_num at h4
  ·
    have hf : f = 1 := by
      have h2 : 2 ^ f = 2 := by rw [← hrg]; exact hroot2 d hd
      exact Nat.pow_right_injective le_rfl (by simpa using h2)
    rwa [hf] at hL
  ·
    have hcard : Nat.card G = 6048 := CFSG.Blueprint.LieModel.card_psu_three_three hU3
    rw [hcard] at hdvd
    norm_num at hdvd
  ·
    obtain ⟨e⟩ := hA6
    have hcard : Nat.card G = 360 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      norm_num
    rw [hcard] at hdvd
    norm_num at hdvd
  ·
    obtain ⟨e⟩ := hJ2
    have hcard : Nat.card G = 604800 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Sporadic.J2.card_J2
    rw [hcard] at hdvd
    norm_num at hdvd

end CFSG.GF2Type.Smith1979
