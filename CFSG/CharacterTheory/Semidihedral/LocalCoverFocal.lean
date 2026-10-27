module

public import CFSG.CharacterTheory.Semidihedral.SameParameterInvolutionColumns
public import CFSG.CharacterTheory.Semidihedral.QuaternionFocalFactorization

public section

namespace CFSG.Semidihedral.LocalCoverFocal

noncomputable section

open CFSG.Open
open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.StationaryOddLocalization

theorem actual_covering_centralizer_every_original_presentation_lifts
    {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G)
    (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (H : Subgroup G) (hVH : Subgroup.closure ({t, s} : Set G) ≤ H)
    (hcover : (H.subgroupOf (C t) ⊓
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) :
    let B := H.subgroupOf (C t)
    Odd B.index ∧ Odd H.index ∧
      ∀ SB : Sylow 2 B,
        Nonempty (SemidihedralGroup n ≃* SB) ∧
        ∃ (SH : Sylow 2 H) (SG : Sylow 2 G),
          (SG : Subgroup G) = ((SB : Subgroup B).map B.subtype).map (C t).subtype ∧
          (SG : Subgroup G) = (SH : Subgroup H).map H.subtype ∧
          (SH : Subgroup H) ≤ (H ⊓ C t).subgroupOf H ∧
          ∀ fB : SemidihedralGroup n ≃* SB,
            (((fB (CFSG.Semidihedral.z n) : B) : C t) : G) = t ∧
            ∃ (fH : SemidihedralGroup n ≃* SH) (fG : SemidihedralGroup n ≃* SG),
              (fG (CFSG.Semidihedral.z n) : G) = t ∧
              ((fH (CFSG.Semidihedral.z n) : H) : G) = t ∧
              ∀ x, (fG x : G) = (((fB x : B) : C t) : G) ∧
                (fG x : G) = ((fH x : H) : G) := by
  intro B
  obtain ⟨hB, hH, hlift⟩ := actual_covering_centralizer_every_sylow_presentation
    n hn S0 f0 hG t s ht hs hsC hts hnonab hcentral hnc p f hp hpodd hf hmodel H hVH hcover
  refine ⟨hB, hH, ?_⟩
  intro SB
  obtain ⟨fB0, SH, fH0, SG, fG0, hSG, hSH, hSHC, -, -, -, hrep⟩ := hlift SB
  refine ⟨⟨fB0⟩, SH, SG, hSG, hSH, hSHC, ?_⟩
  intro fB
  have htB : tInC t ∈ B := hVH (Subgroup.mem_closure_of_mem (Set.mem_insert t _))
  let tB : B := ⟨tInC t, htB⟩
  have htBcentral : tB ∈ Subgroup.center B := by
    apply Subgroup.mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (tInC_central t) (x : C t)
  have htBorder : orderOf tB = 2 :=
    (Subgroup.orderOf_coe tB).symm.trans ((Subgroup.orderOf_coe (tInC t)).symm.trans ht)
  have hzB : (fB (CFSG.Semidihedral.z n) : B) = tB :=
    central_involution_eq_supplied_semidihedral_center n hn SB fB tB htBcentral htBorder
  let a : SemidihedralGroup n ≃* SemidihedralGroup n := fB.trans fB0.symm
  let fH := a.trans fH0
  let fG := a.trans fG0
  have hrepB (x : SemidihedralGroup n) :
      (fG x : G) = (((fB x : B) : C t) : G) := by
    simpa only [fG, a, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] using (hrep (a x)).1
  have hrepH (x : SemidihedralGroup n) : (fG x : G) = ((fH x : H) : G) :=
    (hrep (a x)).2
  have hzBG : (((fB (CFSG.Semidihedral.z n) : B) : C t) : G) = t :=
    congrArg (fun x : B => ((x : C t) : G)) hzB
  have hzG : (fG (CFSG.Semidihedral.z n) : G) = t := (hrepB _).trans hzBG
  exact ⟨hzBG, fH, fG, hzG, (hrepH _).symm.trans hzG,
    fun x => ⟨hrepB x, hrepH x⟩⟩

theorem actual_layer_cover_derived_image_and_every_sylow_lower_bound
    {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G)
    (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2)
    (t : G) (ht : orderOf t = 2)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (B : Subgroup (C t))
    (hcover : (B ⊓
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) :
    let T0 := (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)
    Group.IsPerfect T0 ∧
      T0 ≤ (commutator B).map ((nu t).comp B.subtype) ∧
      Nat.card T0 = p ^ f * ((p ^ f) ^ 2 - 1) ∧
      Nat.card T0 ∣ Nat.card (commutator B) ∧
      ∀ SB : Sylow 2 B,
        2 ^ (n - 1) ≤ Nat.card ↥((SB : Subgroup B) ⊓ commutator B) := by
  intro T0
  obtain ⟨F, hF, hfinite, A, rho, data⟩ := actual_simple_layer_matrix_data
    n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hmodel
  let : Field F := hF
  let : Finite F := hfinite
  obtain ⟨-, -, hz, -, -, -, -⟩ := actual_quotient_inputs n hn S0 f0 hG t ht
  obtain ⟨hperfect, -, -, -, hcard, -, -⟩ :=
    SameParameterRegularity.actual_matrix_layer_properties
      t n p f hp hpodd hf hq F A rho data hcentral hz
  let : Group.IsPerfect T0 := hperfect
  let pi : B →* H t := (nu t).comp B.subtype
  have hTB : T0 ≤ B.map (nu t) := by
    change (CFSG.generalizedFitting (Gamma t)).comap (barKappa t) ≤ B.map (nu t)
    rw [← hcover]
    exact Subgroup.map_mono inf_le_left
  have hTrange : T0 ≤ pi.range := by
    intro x hx
    obtain ⟨b, hb, hbx⟩ := hTB hx
    exact ⟨⟨b, hb⟩, hbx⟩
  have himage : T0 ≤ (commutator B).map pi := by
    rw [map_commutator_eq]
    calc
      T0 = ⁅T0, T0⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ ⁅pi.range, pi.range⁆ := Subgroup.commutator_mono hTrange hTrange
  have hcarddiv : Nat.card T0 ∣ Nat.card (commutator B) :=
    (Subgroup.card_dvd_of_le himage).trans (Subgroup.card_map_dvd _ pi)
  have htwo : 2 ^ (n - 1) ∣ Nat.card T0 := by
    rw [hcard]
    have heq : 2 ^ ((p ^ f) ^ 2 - 1).factorization 2 = 2 ^ (n - 1) := by
      simpa only [data.field_card] using data.two_part
    have hd : 2 ^ (n - 1) ∣ (p ^ f) ^ 2 - 1 := by
      rw [← heq]
      exact Nat.ordProj_dvd _ 2
    exact hd.trans (dvd_mul_left _ _)
  refine ⟨hperfect, himage, hcard, hcarddiv, ?_⟩
  intro SB
  obtain ⟨D, hD⟩ :=
    CFSG.DisconnectedInvolutionGraph.Helpers.normal_subgroup_sylow_intersection
      2 (commutator B) SB
  have hmap : (D : Subgroup (commutator B)).map (commutator B).subtype =
      (SB : Subgroup B) ⊓ commutator B := by
    rw [hD, Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [← hmap, Subgroup.card_map_of_injective (commutator B).subtype_injective,
    Sylow.card_eq_multiplicity]
  exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
    ((Nat.prime_two.pow_dvd_iff_le_factorization (ne_of_gt Nat.card_pos)).mp
      (htwo.trans hcarddiv))

theorem actual_covering_centralizer_every_sylow_commutator_quaternion
    {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 4 ≤ n) (S0 : Sylow 2 G)
    (f0 : SemidihedralGroup n ≃* S0)
    (hG : ∀ U : Subgroup G, U.index ≠ 2)
    (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2)
    (hsC : s ∈ C t) (hts : t ≠ s)
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer
      (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f)
    (H : Subgroup G) (hVH : Subgroup.closure ({t, s} : Set G) ≤ H)
    (hcover : (H.subgroupOf (C t) ⊓
      ((CFSG.generalizedFitting (Gamma t)).comap (barKappa t)).comap (nu t)).map (nu t) =
        (CFSG.generalizedFitting (Gamma t)).comap (barKappa t)) :
    let B := H.subgroupOf (C t)
    Odd B.index ∧ Odd H.index ∧
      ∀ SB : Sylow 2 B,
        Nonempty (SemidihedralGroup n ≃* SB) ∧
        ∃ (SH : Sylow 2 H) (SG : Sylow 2 G),
          (SG : Subgroup G) = ((SB : Subgroup B).map B.subtype).map (C t).subtype ∧
          (SG : Subgroup G) = (SH : Subgroup H).map H.subtype ∧
          (SH : Subgroup H) ≤ (H ⊓ C t).subgroupOf H ∧
          ∀ fB : SemidihedralGroup n ≃* SB,
            (((fB (CFSG.Semidihedral.z n) : B) : C t) : G) = t ∧
            (SB : Subgroup B) ⊓ commutator B =
              Subgroup.closure ({(fB (CFSG.Semidihedral.r n) : B) ^ 2,
                (fB (CFSG.Semidihedral.r n) : B) *
                  (fB (CFSG.Semidihedral.s n) : B)} : Set B) ∧
            ∃ (fH : SemidihedralGroup n ≃* SH) (fG : SemidihedralGroup n ≃* SG),
              (fG (CFSG.Semidihedral.z n) : G) = t ∧
              ((fH (CFSG.Semidihedral.z n) : H) : G) = t ∧
              ∀ x, (fG x : G) = (((fB x : B) : C t) : G) ∧
                (fG x : G) = ((fH x : H) : G) := by
  intro B
  obtain ⟨hB, hH, hlift⟩ := actual_covering_centralizer_every_original_presentation_lifts
    n hn S0 f0 hG t s ht hs hsC hts hnonab hcentral hnc p f hp hpodd hf hmodel H hVH hcover
  obtain ⟨-, -, -, -, hbound⟩ :=
    actual_layer_cover_derived_image_and_every_sylow_lower_bound
      n hn S0 f0 hG t ht hnonab hcentral hnc p f hp hpodd hf hq hmodel B hcover
  refine ⟨hB, hH, ?_⟩
  intro SB
  obtain ⟨hSD, SH, SG, hSG, hSH, hSHC, hpresent⟩ := hlift SB
  refine ⟨hSD, SH, SG, hSG, hSH, hSHC, ?_⟩
  intro fB
  obtain ⟨hzB, fH, fG, hzG, hzH, hrep⟩ := hpresent fB
  let Q : Subgroup B := Subgroup.closure
    ({(fB (CFSG.Semidihedral.r n) : B) ^ 2,
      (fB (CFSG.Semidihedral.r n) : B) * (fB (CFSG.Semidihedral.s n) : B)} : Set B)
  have hQcard : Nat.card Q = 2 ^ (n - 1) :=
    QuaternionFocalFactorization.originalQuaternion_card n hn SB fB
  let C0 := CentralizerResidual.involutionCentralizer n SG fG
  have hC0 : C0 = C t := by
    change Subgroup.centralizer {(fG (CFSG.Semidihedral.z n) : G)} = C t
    rw [hzG]
  let i : B →* C0 :=
    { toFun := fun x => ⟨((x : C t) : G), by rw [hC0]; exact (x : C t).property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let j : B →* G := (C t).subtype.comp B.subtype
  have hij : C0.subtype.comp i = j := by
    ext x
    rfl
  have hj : Function.Injective j := (C t).subtype_injective.comp B.subtype_injective
  have hSBmap : (SB : Subgroup B).map j = (SG : Subgroup G) := by
    dsimp only [j]
    rw [← Subgroup.map_map]
    exact hSG.symm
  have hderived : (commutator B).map i ≤ commutator C0 := by
    rw [map_commutator_eq, commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  have hderivedMap : (commutator B).map j ≤ (commutator C0).map C0.subtype := by
    rw [← hij, ← Subgroup.map_map]
    exact Subgroup.map_mono hderived
  have hSCmap :
      (CentralizerResidual.centralizerSylow n hn SG fG : Subgroup C0).map C0.subtype =
        (SG : Subgroup G) := by
    rw [CentralizerResidual.centralizerSylow, Sylow.coe_subtype]
    exact Subgroup.map_subgroupOf_eq_of_le
      (CentralizerResidual.sylow_le_involutionCentralizer n hn SG fG)
  have hcentral := congrArg (Subgroup.map C0.subtype)
    (CentralizerResidual.centralizer_derived_inf n hn SG fG hG)
  rw [Subgroup.map_inf _ _ _ C0.subtype_injective, hSCmap,
    CentralizerResidual.centralizerQuaternion_ambient_map] at hcentral
  have hQmap : Q.map j =
      Subgroup.closure {((fG (CFSG.Semidihedral.r n) ^ 2 : SG) : G),
        ((fG (CFSG.Semidihedral.r n) * fG (CFSG.Semidihedral.s n) : SG) : G)} := by
    dsimp only [Q]
    rw [MonoidHom.map_closure]
    simp only [Set.image_insert_eq, Set.image_singleton, map_pow, map_mul]
    change Subgroup.closure
      {(((fB (CFSG.Semidihedral.r n) : B) : C t) : G) ^ 2,
        (((fB (CFSG.Semidihedral.r n) : B) : C t) : G) *
          (((fB (CFSG.Semidihedral.s n) : B) : C t) : G)} = _
    rw [← (hrep (CFSG.Semidihedral.r n)).1, ← (hrep (CFSG.Semidihedral.s n)).1]
    rfl
  have hle : (SB : Subgroup B) ⊓ commutator B ≤ Q := by
    apply (Subgroup.map_le_map_iff_of_injective hj).mp
    calc
      ((SB : Subgroup B) ⊓ commutator B).map j ≤
          (SB : Subgroup B).map j ⊓ (commutator B).map j := Subgroup.map_inf_le _ _ _
      _ ≤ (SG : Subgroup G) ⊓ (commutator C0).map C0.subtype := by
        rw [hSBmap]
        exact inf_le_inf le_rfl hderivedMap
      _ = Q.map j := hcentral.trans hQmap.symm
  have hfocal : (SB : Subgroup B) ⊓ commutator B = Q :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hQcard]; exact hbound SB)
  exact ⟨hzB, hfocal, fH, fG, hzG, hzH, hrep⟩

end

end CFSG.Semidihedral.LocalCoverFocal
