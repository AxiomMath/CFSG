module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTFinComm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTFinOdd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTFinOrd3
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Aut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTResGUIso
public import CFSG.LieType.SemisimpleCentralizers.OrderThree.CenterQuot

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT

open CFSG.Open CFSG.Fischer CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LieType.SemisimpleCentralizers.Held Matrix
open CFSG.LieType.SemisimpleCentralizers.OrderThree (nonempty_quotientCenter_mulEquiv_of_surjective)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni (isComponentOf_centralizer_gu_of_su)
open scoped commutatorElement

@[expose] noncomputable def piS6 : M6 →* S6 :=
  QuotientGroup.mk' ((StatedScalars (Fin 6) F4).subgroupOf (StatedSU 6 (2 ^ 1) F4))

theorem piS6_apply (x : M6) : piS6 x = QuotientGroup.mk x := rfl

theorem piS6_ker_le_center : piS6.ker ≤ Subgroup.center M6 := by
  intro z hz
  rw [MonoidHom.mem_ker, piS6_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hz
  obtain ⟨c, hc⟩ := hz
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  change (g : GL (Fin 6) F4) * z = z * g
  rw [← hc]
  exact (commute_scalar c (g : GL (Fin 6) F4)).eq

theorem three_dvd_card_of_component_fix (β : MulAut S6) (hβ : β ^ 3 = 1)
    {L : Subgroup S6} (hL : IsComponentOf L (fixSubgroup β)) : 3 ∣ Nat.card ↥L := by
  obtain ⟨B, hB, ⟨c, hBc⟩, hβB⟩ := exists_unitary_of_pow_three β hβ
  let A : primeFormUnitary hF4 (idGram F4 6) := ⟨B, hB⟩
  let cj : M6 ≃* M6 := conjM6 A
  have hβcj : ∀ x : M6, β (piS6 x) = piS6 (cj x) := fun x =>
    hβB x (cj x) (conjM6_apply A x)
  have hfixβ : ∀ x : M6, piS6 x ∈ fixSubgroup β → cj x * x⁻¹ ∈ Subgroup.center M6 := by
    intro x hx
    rw [mem_fixSubgroup] at hx
    apply piS6_ker_le_center
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hβcj x, hx, mul_inv_cancel]
  have hcomm : ∀ x y : M6, piS6 x ∈ fixSubgroup β → piS6 y ∈ fixSubgroup β →
      cj ⁅x, y⁆ = ⁅x, y⁆ := by
    intro x y hx hy
    have hz1 := hfixβ x hx
    have hz2 := hfixβ y hy
    have ex : cj x = (cj x * x⁻¹) * x := by group
    have ey : cj y = (cj y * y⁻¹) * y := by group
    rw [map_commutatorElement, ex, ey]
    exact commutatorElement_central_mul hz1 hz2
  let X : Subgroup M6 := (fixSubgroup β).comap piS6
  let Lh : Subgroup M6 := L.comap piS6
  let P : Subgroup M6 := ⁅Lh, Lh⁆
  let C : Subgroup M6 := fixSubgroup cj
  have hLh_sub : IsSubnormal Lh X := isSubnormal_comap_open piS6 hL.2.1
  have hPsub_X : IsSubnormal P X := isSubnormal_commutator_open hLh_sub
  have hP_le_C : P ≤ C := by
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    rw [mem_fixSubgroup]
    exact hcomm x y (hL.1 hx) (hL.1 hy)
  have hC_le_X : C ≤ X := by
    intro x hx
    rw [mem_fixSubgroup] at hx
    show piS6 x ∈ fixSubgroup β
    rw [mem_fixSubgroup, hβcj x, hx]
  have hPsub_C : IsSubnormal P C := by
    have h := hPsub_X.inf_of_le hC_le_X
    rwa [inf_eq_left.mpr hP_le_C] at h
  have hLperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp ⟨hL.2.2.1⟩
  have hsurj : Function.Surjective piS6 := QuotientGroup.mk'_surjective _
  have hPmap : P.map piS6 = L := by
    have hLh_map : Lh.map piS6 = L := Subgroup.map_comap_eq_self_of_surjective hsurj L
    show Subgroup.map piS6 ⁅Lh, Lh⁆ = L
    rw [Subgroup.map_commutator, hLh_map, hLperf]
  have hPsurj : ∀ l ∈ L, ∃ p ∈ P, piS6 p = l := by
    intro l hl
    have hl' : l ∈ P.map piS6 := by rw [hPmap]; exact hl
    exact Subgroup.mem_map.mp hl'
  have hPdecomp : ∀ x ∈ Lh, ∃ z ∈ Subgroup.center M6, ∃ p ∈ P, x = z * p := by
    intro x hx
    obtain ⟨p, hp, hpx⟩ := hPsurj (piS6 x) hx
    refine ⟨x * p⁻¹, piS6_ker_le_center ?_, p, hp, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hpx, mul_inv_cancel]
  have hPperf : ⁅P, P⁆ = P := by
    apply le_antisymm
    · exact commutator_self_le P
    · show ⁅Lh, Lh⁆ ≤ ⁅P, P⁆
      refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
      obtain ⟨z₁, hz₁, p, hp, rfl⟩ := hPdecomp x hx
      obtain ⟨z₂, hz₂, q, hq, rfl⟩ := hPdecomp y hy
      rw [commutatorElement_central_mul hz₁ hz₂]
      exact Subgroup.commutator_mem_commutator hp hq
  have hPLh : P ≤ Lh := commutator_self_le Lh
  let πP : ↥P →* ↥L := MonoidHom.codRestrict (piS6.comp P.subtype) L
    (fun p => hPLh p.2)
  have hπsurj : Function.Surjective πP := by
    intro l
    obtain ⟨p, hp, hpl⟩ := hPsurj l.1 l.2
    exact ⟨⟨p, hp⟩, Subtype.ext hpl⟩
  have hπker : πP.ker ≤ Subgroup.center ↥P := by
    intro p hp
    rw [MonoidHom.mem_ker] at hp
    have hp' : piS6 (p : M6) = 1 := by
      have := congrArg Subtype.val hp
      exact this
    have hz : (p : M6) ∈ Subgroup.center M6 := piS6_ker_le_center (MonoidHom.mem_ker.mpr hp')
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hz g
  have hpf : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hPperf
  obtain ⟨eQ⟩ := nonempty_quotientCenter_mulEquiv_of_surjective hpf πP hπsurj hπker
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.2.2.2
  have hPQ : CFSG.Open.IsQuasisimple ↥P := ⟨hpf.commutator_eq_top, MulEquiv.isSimpleGroup eQ⟩
  have hPcomp : IsComponentOf P C := ⟨hP_le_C, hPsub_C, hPQ⟩
  let ι : M6 →* GL (Fin 6) F4 := (StatedSU 6 (2 ^ 1) F4).subtype
  have hι : Function.Injective ι := Subtype.val_injective
  have hCmap : C.map ι = Subgroup.centralizer ({B} : Set (GL (Fin 6) F4)) ⊓ StatedSU 6 (2 ^ 1) F4 := by
    have hC : C = CenD B := fixSubgroup_conjM6 A
    rw [hC]
    exact Subgroup.subgroupOf_map_subtype _ _
  have hJcomp : IsComponentOf (P.map ι)
      (Subgroup.centralizer ({B} : Set (GL (Fin 6) F4)) ⊓ StatedSU 6 (2 ^ 1) F4) := by
    rw [← hCmap]
    exact isComponentOf_map_of_injective ι hι hPcomp
  have hτ : ∀ x, resTau hF4 (resTau hF4 x) = x := resTau_invol hF4
  have hτQ : ∀ x : F4, resTau hF4 x = x ^ 2 := fun x => resTau_apply hF4 x
  have hτQ2 : ∀ x : F4, resTau hF4 x = x ^ (2 ^ 1) := fun x => by rw [hτQ x]; norm_num
  have hSU : heldSU 6 F4 (resTau hF4) hτ = StatedSU 6 (2 ^ 1) F4 := hct_heldSU_eq_statedSU hτQ2
  have hJSU : IsComponentOf (P.map ι)
      (Subgroup.centralizer ({B} : Set (GL (Fin 6) F4)) ⊓ heldSU 6 F4 (resTau hF4) hτ) := by
    rw [hSU]
    exact hJcomp
  have hJGU := isComponentOf_centralizer_gu_of_su hτ B hJSU
  have hL4 : Nat.card F4 = 2 ^ 2 := by rw [CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer.hF4card]; norm_num
  have hB_gu : B ∈ heldGU 6 F4 (resTau hF4) hτ := by
    rw [mem_heldGU, resTau_coe hF4]
    have h := (mem_primeFormUnitary).mp hB
    simpa [idGram] using h
  have hord : (orderOf B : F4) ≠ 0 := by
    have hc3 : c ^ 3 = 1 := by
      ext
      simp only [Units.val_pow_eq_pow_val, Units.val_one]
      have h := FiniteField.pow_card_sub_one_eq_one (c : F4) (Units.ne_zero c)
      rw [F4.card] at h
      simpa using h
    have h9 : B ^ 9 = 1 := by
      have e9 : B ^ 9 = (B ^ 3) ^ 3 := by rw [← pow_mul]
      rw [e9, hBc, ← map_pow, hc3, map_one]
    have hdvd : orderOf B ∣ 9 := orderOf_dvd_of_pow_eq_one h9
    intro h0
    have h2 : 2 ∣ orderOf B := (CharP.cast_eq_zero_iff F4 2 (orderOf B)).mp h0
    have : 2 ∣ 9 := h2.trans hdvd
    norm_num at this
  have h3PZ : 3 ∣ Nat.card (↥P ⧸ Subgroup.center ↥P) := by
    have eP : ↥P ≃* ↥(P.map ι) := Subgroup.equivMapOfInjective P ι hι
    have eQP : (↥P ⧸ Subgroup.center ↥P) ≃* (↥(P.map ι) ⧸ Subgroup.center ↥(P.map ι)) :=
      QuotientGroup.congr (Subgroup.center ↥P) (Subgroup.center ↥(P.map ι)) eP
        (Subgroup.map_center_eq eP)
    rw [Nat.card_congr eQP.toEquiv]
    rcases held_unitary_components_gu_odd SUComponentsTrivial_holds SLComponentsTrivial_holds hτ
        hτQ hL4 B hB_gu hord (P.map ι) hJGU with
      ⟨a, dd, E, hE, hEfin, τ', hτ', ha, hτ'dd, hcardE, hodd, ⟨eJ⟩⟩ |
      ⟨b, e, E, hE, hEfin, hb, hcardE, ⟨eJ⟩⟩
    · rw [Nat.card_congr eJ.toEquiv]
      exact three_dvd_card_heldSU_quot ha hτ' hτ'dd hodd hcardE
    · rw [Nat.card_congr eJ.toEquiv]
      exact three_dvd_card_statedProj_statedSL hb
        (by rw [hcardE, pow_mul]; norm_num : Nat.card E = 4 ^ e)
  have hdvd : Nat.card (↥P ⧸ Subgroup.center ↥P) ∣ Nat.card ↥L := by
    have h1 : (Subgroup.center ↥P).index ∣ (πP.ker).index := Subgroup.index_dvd_of_le hπker
    have h2 : (πP.ker).index = Nat.card ↥L := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hπsurj]
      exact Nat.card_congr Subgroup.topEquiv.toEquiv
    rw [h2] at h1
    exact h1
  exact h3PZ.trans hdvd

end CFSG.LocalAnalysis.GLTheoremA.HSubT

end
