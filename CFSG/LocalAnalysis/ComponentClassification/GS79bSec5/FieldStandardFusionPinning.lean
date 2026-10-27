module

public import CFSG.LocalAnalysis.OddStandard.Seitz77FusionDefs
public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardInvolutionCentralizer
public import CFSG.LocalAnalysis.EvenBN.U5.LinTwin39dDih
public import CFSG.GroupTheory.ABGLocalTools.Criteria

public section

open Subgroup
open CFSG.ABGLocalTools
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.RankTwoL3Even
open CFSG.LocalAnalysis.EvenBN.U5

namespace CFSG.ComponentClassification.GS79bSec5

universe u

theorem exists_datum_pinned_to_standard_roots
    {G : Type u} [Group G] [Finite G]
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (A : Subgroup G)
    (hA : CFSG.Open.standardComponentIsStandard A)
    (hZ : Odd (Nat.card (Subgroup.center A)))
    (e : (A ⧸ Subgroup.center A) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F)
    (φ : Matrix.SpecialLinearGroup (Fin 3) F →* A)
    (hφproj :
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))).comp φ =
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F)
    (hcyc : ∀ S : Sylow 2 (Subgroup.centralizer (A : Set G)), IsCyclic ↥S)
    (t : G) (ht : orderOf t = 2)
    (htC : t ∈ Subgroup.centralizer (A : Set G)) :
    ∃ d : CFSG.OddStandard.Seitz77.Datum A,
      d.t = t ∧
      (φ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipU F 0 1 0) : G) ∈
        d.P ⊓ Subgroup.centralizer (d.P : Set G) ∧
      (φ (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.unipU F 0 0 1) : G) ∈ d.V := by
  classical
  let zA : A := φ (unipU F 0 1 0)
  let uA : A := φ (unipU F 0 0 1)
  let π : A →* projectiveSL 3 F :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center A))
  have hπφ : ∀ x : Matrix.SpecialLinearGroup (Fin 3) F, π (φ x) = proj 3 F x :=
    fun x => DFunLike.congr_fun hφproj x
  have hzA2 : zA * zA = 1 := by
    have h := congrArg φ (unipU_mul_self (F := F) (a := 0) (b := 1) (c := 0))
    simpa [zA, unipU_zero] using h
  have huA2 : uA * uA = 1 := by
    have h := congrArg φ (unipU_mul_self (F := F) (a := 0) (b := 0) (c := 1))
    simpa [uA, unipU_zero] using h
  have hzu : zA * uA = uA * zA := by
    have h : unipU F 0 1 0 * unipU F 0 0 1 = unipU F 0 0 1 * unipU F 0 1 0 := by
      rw [unipU_mul, unipU_mul]
      norm_num
    calc zA * uA = φ (unipU F 0 1 0 * unipU F 0 0 1) := (map_mul φ _ _).symm
      _ = φ (unipU F 0 0 1 * unipU F 0 1 0) := by rw [h]
      _ = uA * zA := map_mul φ _ _
  have hker_eq : π.ker = Subgroup.center A := by
    change ((e : (A ⧸ Subgroup.center A) →* projectiveSL 3 F).comp
      (QuotientGroup.mk' (Subgroup.center A))).ker = Subgroup.center A
    rw [MonoidHom.ker_mulEquiv_comp (QuotientGroup.mk' (Subgroup.center A)) e,
      QuotientGroup.ker_mk' (Subgroup.center A)]
  have hker : π.ker ≤ Subgroup.center A := hker_eq.le
  have hodd : Odd (Nat.card π.ker) := by
    rw [hker_eq]
    exact hZ
  have hπz : π zA = proj 3 F (unipU F 0 1 0) := hπφ _
  have hπu : π uA = proj 3 F (unipU F 0 0 1) := hπφ _
  have hprojz : proj 3 F (unipU F 0 1 0) ≠ 1 := proj_unipU_ne_one (by simp)
  have hproju : proj 3 F (unipU F 0 0 1) ≠ 1 := proj_unipU_ne_one (by simp)
  have hzA_ne : zA ≠ 1 := fun h => hprojz (by rw [← hπz, h, map_one])
  have huA_ne : uA ≠ 1 := fun h => hproju (by rw [← hπu, h, map_one])
  have hzA_order : orderOf zA = 2 := orderOf_eq_prime (by simpa [sq] using hzA2) hzA_ne
  have hπz2 : π zA * π zA = 1 := by rw [← map_mul, hzA2, map_one]
  have hπu2 : π uA * π uA = 1 := by rw [← map_mul, huA2, map_one]
  have hπz_ne : π zA ≠ 1 := by rw [hπz]; exact hprojz
  have hπu_ne : π uA ≠ 1 := by rw [hπu]; exact hproju
  let N : Subgroup G := normalizer (A : Set G)
  let tC : Subgroup.centralizer (A : Set G) := ⟨t, htC⟩
  have htC_order : orderOf tC = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact ht
  have hcyc_tC : IsPGroup 2 (zpowers tC) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htC_order, pow_one])
  obtain ⟨R, hR⟩ := hcyc_tC.exists_le_sylow
  have hsec : CFSG.OddStandard.Sector A R t :=
    ⟨hA, hcyc R, ⟨tC, hR (mem_zpowers tC), rfl⟩, ht⟩
  have hsgRN : IsPGroup 2 ((CFSG.OddStandard.sg A R).subgroupOf N) :=
    CFSG.OddStandard.isPGroup_sg.comap_subtype
  obtain ⟨Q₀, hQ₀⟩ := hsgRN.exists_le_sylow
  let P0 : Subgroup G := (Q₀ : Subgroup N).map N.subtype
  have hP0syl : IsSylowOf 2 P0 N := ⟨Q₀, rfl⟩
  have hRP0 : CFSG.OddStandard.sg A R ≤ P0 := by
    intro x hx
    exact Subgroup.mem_map.mpr
      ⟨⟨x, CFSG.OddStandard.sg_le_normalizer hx⟩, hQ₀ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hEvenA : 2 ∣ Nat.card A := by
    rw [← hzA_order]
    exact orderOf_dvd_natCard zA
  have hEvenL : 2 ∣ Nat.card (A.subgroupOf N) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := A))).toEquiv]
    exact hEvenA
  have hNormal : (A.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.le_normalizer (H := A))).mpr le_rfl
  obtain ⟨w, hwZ, hw1, hw2, hwL⟩ :=
    @exists_central_involution_of_even N _ _ Q₀ (A.subgroupOf N) hNormal hEvenL
  let cA : A := ⟨(w : N), hwL⟩
  have hcA_coe : ((cA : A) : G) = ((w : N) : G) := rfl
  have hwN2 : (w : N) * (w : N) = 1 := by
    simpa [pow_two] using congrArg (fun z : Q₀ => (z : N)) hw2
  have hwN_ne : (w : N) ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hcA2 : cA * cA = 1 := Subtype.ext (by
    have h := congrArg N.subtype hwN2
    simpa [cA] using h)
  have hwN_ne' : ((w : N) : G) ≠ 1 := fun h => hwN_ne (N.subtype_injective h)
  have hcA_ne : cA ≠ 1 := fun h => hwN_ne' (by simpa [cA] using congrArg A.subtype h)
  have hcA_order : orderOf cA = 2 := orderOf_eq_prime (by simpa [sq] using hcA2) hcA_ne
  have hcA_not_center : cA ∉ Subgroup.center A := by
    intro hc
    have hdvd : 2 ∣ Nat.card (Subgroup.center A) := by
      rw [← hcA_order]
      exact (Subgroup.center A).orderOf_dvd_natCard hc
    exact hZ.not_two_dvd_nat hdvd
  have hπc_ne : π cA ≠ 1 := fun h =>
    hcA_not_center (hker ((MonoidHom.mem_ker (f := π)).mpr h))
  have hπc2 : π cA * π cA = 1 := by rw [← map_mul, hcA2, map_one]
  obtain ⟨yc, hyc⟩ := exists_conj_eq_x0 (F := F) hπc2 hπc_ne
  obtain ⟨yz, hyz⟩ := exists_conj_eq_x0 (F := F) hπz2 hπz_ne
  have hπsurj : Function.Surjective π :=
    e.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center A))
  obtain ⟨ycA, hycA⟩ := hπsurj yc
  obtain ⟨yzA, hyzA⟩ := hπsurj yz
  have hconj : ∃ m : A, π (m * cA * m⁻¹) = π zA := by
    refine ⟨yzA⁻¹ * ycA, ?_⟩
    calc π ((yzA⁻¹ * ycA) * cA * (yzA⁻¹ * ycA)⁻¹)
        = yz⁻¹ * (yc * π cA * yc⁻¹) * yz := by
          simp only [map_mul, map_inv, hycA, hyzA]
          group
      _ = yz⁻¹ * x0 F * yz := by rw [hyc]
      _ = π zA := by
          rw [← hyz]
          group
  obtain ⟨aA, ha_conj⟩ :=
    CFSG.LocalAnalysis.EvenBN.U5.LinCase.invol_conj_of_odd_ker π hodd hzA2 hcA2 hconj
  let aG : G := (aA : A)
  have haN : aG ∈ N := Subgroup.le_normalizer aA.2
  let P : Subgroup G := P0.map (MulAut.conj aG).toMonoidHom
  have hPsyl : IsSylowOf 2 P N := by
    let aNe : N := ⟨aG, haN⟩
    let Q' : Sylow 2 N :=
      Q₀.mapSurjective (f := (MulAut.conj aNe).toMonoidHom)
        (by simpa using (MulAut.conj aNe).surjective)
    refine ⟨Q', ?_⟩
    dsimp only [Q']
    rw [Sylow.coe_mapSurjective, Subgroup.map_map]
    have hcomp : N.subtype.comp (MulAut.conj aNe).toMonoidHom =
        (MulAut.conj aG).toMonoidHom.comp N.subtype := by
      ext x
      rfl
    rw [hcomp, ← Subgroup.map_map]
  have hRP : CFSG.OddStandard.sg A R ≤ P := by
    intro x hx
    have hxP0 : x ∈ P0 := hRP0 hx
    have hxK : x ∈ Subgroup.centralizer (A : Set G) := CFSG.OddStandard.sg_le_centralizer hx
    have hcomm : aG * x = x * aG := (Subgroup.mem_centralizer_iff.mp hxK) aG aA.2
    have hxfix : aG * x * aG⁻¹ = x := by
      calc aG * x * aG⁻¹ = x * aG * aG⁻¹ := by rw [hcomm]
        _ = x := by group
    exact Subgroup.mem_map.mpr ⟨x, hxP0, by simpa [MulAut.conj_apply] using hxfix⟩
  let d : CFSG.OddStandard.Seitz77.Datum A := ⟨R, t, hsec, P, hPsyl, hRP⟩
  have hz_eq : aG * ((cA : A) : G) * aG⁻¹ = ((zA : A) : G) := by
    simpa [aG] using congrArg A.subtype ha_conj
  have hwP0 : ((w : N) : G) ∈ P0 :=
    Subgroup.mem_map.mpr ⟨(w : N), w.2, rfl⟩
  have hcP0 : ((cA : A) : G) ∈ P0 := by
    simpa [cA] using hwP0
  have hc_comm_P0 : ∀ x ∈ P0, ((cA : A) : G) * x = x * ((cA : A) : G) := by
    intro x hx
    obtain ⟨q, hqQ, hqx⟩ := Subgroup.mem_map.mp hx
    have h := Subgroup.mem_center_iff.mp hwZ ⟨q, hqQ⟩
    have h' := congrArg (fun z : Q₀ => (z : N)) h
    rw [← hqx]
    simpa [cA] using (congrArg N.subtype h').symm
  have hzP : ((zA : A) : G) ∈ P := by
    refine Subgroup.mem_map.mpr ⟨((cA : A) : G), hcP0, ?_⟩
    simpa [MulAut.conj_apply] using hz_eq
  have hzZ : ((zA : A) : G) ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨y, hyP0, hyx⟩ := Subgroup.mem_map.mp hx
    have hc_comm : ((cA : A) : G) * y = y * ((cA : A) : G) := hc_comm_P0 y hyP0
    have hx_eq : x = aG * y * aG⁻¹ := hyx.symm
    have hz_eq' : ((zA : A) : G) = aG * ((cA : A) : G) * aG⁻¹ := hz_eq.symm
    rw [hx_eq, hz_eq']
    calc (aG * y * aG⁻¹) * (aG * ((cA : A) : G) * aG⁻¹)
        = aG * (y * ((cA : A) : G)) * aG⁻¹ := by group
      _ = aG * (((cA : A) : G) * y) * aG⁻¹ := by rw [hc_comm]
      _ = (aG * ((cA : A) : G) * aG⁻¹) * (aG * y * aG⁻¹) := by group
  let C : Subgroup A := Subgroup.centralizer ({zA} : Set A)
  have hVAsyl : IsSylowOf 2 (d.V.subgroupOf A) ⊤ := by
    refine (isSylowOf_map_subtype_iff (p := 2) (K := A)
      (A := d.V.subgroupOf A) (B := (⊤ : Subgroup A))).mp ?_
    rw [Subgroup.map_subgroupOf_eq_of_le (show d.V ≤ A from inf_le_right), Subgroup.map_top,
      Subgroup.range_subtype]
    exact d.V_isSylow
  have hV_le_C : d.V.subgroupOf A ≤ C := by
    intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hzZ (v : G) (Subgroup.mem_subgroupOf.mp hv).1
  have hVC : IsSylowOf 2 (d.V.subgroupOf A) C := hVAsyl.of_le hV_le_C le_top
  obtain ⟨Q, hQ⟩ := hVC.exists_sylow_eq_subgroupOf
  have hQnormal : (Q : Subgroup C).Normal :=
    normal_sylow_two_involution_centralizer_of_odd_central_psl_three (F := F)
      π hker hodd hzA2 hzA_ne Q
  have huniq : Unique (Sylow 2 C) := Sylow.unique_of_normal Q hQnormal
  have huAC : uA ∈ C := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hzu.symm
  let uC : C := ⟨uA, huAC⟩
  have huC2 : uC * uC = 1 := by
    apply Subtype.ext
    exact huA2
  have hcyc_uC : IsPGroup 2 (zpowers uC) :=
    isPGroup_zpowers_of_pow_two (x := uC) (k := 1) (by simpa [pow_two] using huC2)
  obtain ⟨R₂, hR₂⟩ := hcyc_uC.exists_le_sylow
  have hR₂Q : R₂ = Q := (huniq.uniq R₂).trans (huniq.uniq Q).symm
  have huC_Q : uC ∈ (Q : Subgroup C) := hR₂Q ▸ hR₂ (mem_zpowers uC)
  have huC_VA : uC ∈ (d.V.subgroupOf A).subgroupOf C := by
    rw [← hQ]
    exact huC_Q
  have huV : ((uA : A) : G) ∈ d.V := by
    exact Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp huC_VA)
  refine ⟨d, rfl, ⟨hzP, hzZ⟩, huV⟩

end CFSG.ComponentClassification.GS79bSec5
