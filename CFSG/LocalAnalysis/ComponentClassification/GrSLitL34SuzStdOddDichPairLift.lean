module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddDichDefs
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SFieldActiveSupport
import CFSG.LieType.SeitzGeneration.SpHyperGen
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSecLift
import CFSG.GroupTheory.InvolutionPow
import CFSG.GroupTheory.SubgroupOfLattice
import CFSG.LocalAnalysis.UniquenessCase.UCKP3Abs
import CFSG.RankThree.PartTwo.Sec21.Hering2119SGrp
import CFSG.GH74.Generic.BProg.Stage2QSProofAbs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3NineOdd
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Std
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddSwapAction

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A V K : Subgroup G} {t y : G}

section Certified


private theorem exists_elemTwo_card_eight_le_of_l34 {H : Type} [Group H] [Finite H]
    {L : Subgroup H} (hL : IsComponent L) (hZL : pPrimeCore 2 ↥L = ⊥)
    (hLtype : IsL34Type (↥L ⧸ center ↥L)) :
    ∃ B : Subgroup H, B ≤ L ∧ IsElemTwo B ∧ Nat.card ↥B = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZeq : Open.fusionZStar ↥L = center ↥L := by
    refine GrS5.fusionZStar_eq_center_of_le hL.1.1.commutator_eq_top ?_
    rw [hZL]
    exact bot_le
  have hLfusion : IsL34Type (↥L ⧸ Open.fusionZStar ↥L) :=
    Blueprint.LieModel.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZeq).symm hLtype
  obtain ⟨Ebar, hEbar, hEbar8⟩ := GrS5.exists_eight_quotient_of_l34 hLfusion
  obtain ⟨A, hAmap, -, hAcomm, hAexp, hAcard⟩ :=
    LieType.SeitzGeneration.exists_lift_elemAbelian
      (QuotientGroup.mk' (pPrimeCore 2 ↥L)) (QuotientGroup.mk'_surjective _)
      (by
        have hodd : Odd (Nat.card (pPrimeCore 2 ↥L)) :=
          Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥L))
        exact fun h2 => hodd.not_two_dvd_nat (by simpa only [QuotientGroup.ker_mk'] using h2))
      (E := Ebar) hEbar.1 (fun x hx => by rw [pow_two]; exact hEbar.2 x hx)
  let B : Subgroup H := A.map L.subtype
  have hB8 : Nat.card ↥B = 8 := by
    change Nat.card ↥(A.map L.subtype) = 8
    rw [Subgroup.card_map_of_injective L.subtype_injective, hAcard, hEbar8]
  have hBe : IsElemTwo B := by
    refine ⟨?_, ?_⟩
    · intro x hx y hy
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
      exact congrArg L.subtype (hAcomm a ha b hb)
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
      simpa only [Subgroup.coe_mul, Subgroup.coe_one, pow_two, map_mul, map_one] using
        congrArg L.subtype (hAexp a ha)
  exact ⟨B, Subgroup.map_subtype_le A, hBe, hB8⟩

private theorem exists_noncentral_involution_of_elemTwo {H : Type} [Group H] [Finite H]
    {L : Subgroup H} (hL : IsComponent L) (hZL : pPrimeCore 2 ↥L = ⊥)
    (hLtype : IsL34Type (↥L ⧸ center ↥L))
    {B : Subgroup H} (hBL : B ≤ L) (hBe : IsElemTwo B) (hB8 : Nat.card ↥B = 8) :
    ∃ x ∈ L, x * x = 1 ∧ x ∉ Subgroup.centralizer (L : Set H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZeq : Open.fusionZStar ↥L = center ↥L := by
    refine GrS5.fusionZStar_eq_center_of_le hL.1.1.commutator_eq_top ?_
    rw [hZL]
    exact bot_le
  have hLfusion : IsL34Type (↥L ⧸ Open.fusionZStar ↥L) :=
    Blueprint.LieModel.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZeq).symm hLtype
  have hB2L : IsPGroup 2 ↥(B.subgroupOf L) := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv, hB8]
    norm_num
  obtain ⟨Q, hBQ⟩ := hB2L.exists_le_sylow (p := 2) (G := ↥L)
  let P : Subgroup H := (Q : Subgroup ↥L).map L.subtype
  have hP : IsSylowTwoIn P L := by
    refine ⟨Subgroup.map_subtype_le _, Q, ?_⟩
    dsimp only [P]
    rw [CFSG.subgroupOf_map_subtype_eq]
  have hBP : B ≤ P := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hBL]
    exact Subgroup.map_mono hBQ
  by_contra hcon
  push Not at hcon
  have hBZ : B ≤ zStarIn L := by
    intro x hx
    have hxL : x ∈ L := hBL hx
    have hxc : x ∈ Subgroup.centralizer (L : Set H) := hcon x hxL (hBe.2 x hx)
    have hxcen : (⟨x, hxL⟩ : ↥L) ∈ center ↥L := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc (g : H) g.2)
    have hxmap : x ∈ (center ↥L).map L.subtype := ⟨⟨x, hxL⟩, hxcen, rfl⟩
    simpa only [zStarIn, hZeq] using hxmap
  have hJ : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hL.1.1
  have hfour := card_le_four_of_le_inf_zStarIn (G := H) hJ hLfusion hP
    (B := B) (fun x hx => ⟨hBP hx, hBZ hx⟩) hBe.2
  omega

private theorem exists_noncentral_involution_of_l34 {H : Type} [Group H] [Finite H]
    {L : Subgroup H} (hL : IsComponent L)
    (hLtype : IsL34Type (↥L ⧸ center ↥L)) (hO : pPrimeCore 2 H = ⊥) :
    ∃ x ∈ L, x * x = 1 ∧ x ∉ Subgroup.centralizer (L : Set H) := by
  obtain ⟨B, hBL, hBe, hB8⟩ :=
    exists_elemTwo_card_eight_le_of_l34 hL (HarrisLit.pPrimeCore_eq_bot_of_isSubnormal hO hL.2)
      hLtype
  exact exists_noncentral_involution_of_elemTwo hL
    (HarrisLit.pPrimeCore_eq_bot_of_isSubnormal hO hL.2) hLtype hBL hBe hB8

private theorem pairLift_E_facts (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y)
    {u : G} (hu : u ∈ V) (ht : t ∈ centralizer ({u} : Set G)) :
    V ⊔ zpowers t ≤ centralizer ({u} : Set G) ∧ IsElemTwo (V ⊔ zpowers t) ∧
      Nat.card ↥((V ⊔ zpowers t).subgroupOf (centralizer ({u} : Set G))) = 8 := by
  have hEX : V ⊔ zpowers t ≤ centralizer ({u} : Set G) := by
    refine sup_le ?_ ?_
    · intro v hv
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact mul_comm_of_mem_of_l34SuzOdd hD hv hu
    · rw [Subgroup.zpowers_le]
      exact ht
  have hEelem : IsElemTwo (V ⊔ zpowers t) := by
    have hV2 : ∀ x ∈ V, x * x = 1 := hD.mul_self
    have hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x :=
      fun x hx y hy => mul_comm_of_mem_of_l34SuzOdd hD hx hy
    have hVt : ∀ y ∈ V, t * y = y * t := by
      intro y hy
      exact (Subgroup.mem_centralizer_iff.mp hS.t_mem y (hD.le_A hy)).symm
    have htV : t ∉ V := fun htv => not_mem_of_l34SuzOdd hS (hD.le_A htv)
    have hres := GrS5.elemTwo_zpowers_sup (x := t) (H := V)
      (by rw [← pow_two, ← hS.orderOf_t]; exact pow_orderOf_eq_one t)
      ⟨hVcomm, hV2⟩ hVt htV
    rw [sup_comm] at hres
    exact hres.1
  have hEXcard : Nat.card ↥((V ⊔ zpowers t).subgroupOf (centralizer ({u} : Set G))) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv,
      card_sup_zpowers_of_l34SuzOdd hS hD]
  exact ⟨hEX, hEelem, hEXcard⟩

private theorem pairLift_S_facts {X : Subgroup G}
    (hEXcard : Nat.card ↥((V ⊔ zpowers t).subgroupOf X) = 8) :
    ((V ⊔ zpowers t).subgroupOf X) ⊓ (QuotientGroup.mk' (pPrimeCore 2 ↥X)).ker = ⊥ ∧
      Nat.card ↥(((V ⊔ zpowers t).subgroupOf X).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥X))) = 8 ∧
      IsPGroup 2 ↥(((V ⊔ zpowers t).subgroupOf X).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥X))) ∧
      Function.Surjective (QuotientGroup.mk' (pPrimeCore 2 ↥X)) ∧
      Odd (Nat.card ↥(QuotientGroup.mk' (pPrimeCore 2 ↥X)).ker) := by
  set π : ↥X →* (↥X ⧸ pPrimeCore 2 ↥X) := QuotientGroup.mk' (pPrimeCore 2 ↥X)
  have hEXdisj : ((V ⊔ zpowers t).subgroupOf X) ⊓ π.ker = ⊥ := by
    have hodd : Odd (Nat.card (pPrimeCore 2 ↥X)) :=
      Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥X))
    have hker : π.ker = pPrimeCore 2 ↥X := QuotientGroup.ker_mk' _
    have h2cop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥X)) :=
      Nat.coprime_two_left.mpr hodd
    have h8cop : Nat.Coprime 8 (Nat.card (pPrimeCore 2 ↥X)) := by
      simpa using h2cop.pow_left 3
    have hcop : Nat.Coprime (Nat.card ↥((V ⊔ zpowers t).subgroupOf X))
        (Nat.card ↥(π.ker)) := by
      rw [hEXcard, hker]
      exact h8cop
    exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hS8 : Nat.card ↥(((V ⊔ zpowers t).subgroupOf X).map π) = 8 := by
    have h := CFSG.GorensteinWalter.card_map_eq_card_mul_card_ker π
      ((V ⊔ zpowers t).subgroupOf X)
    rw [hEXcard, hEXdisj, Subgroup.card_bot, mul_one] at h
    exact h.symm
  have hS2 : IsPGroup 2 ↥(((V ⊔ zpowers t).subgroupOf X).map π) :=
    IsPGroup.of_card (n := 3) (by rw [hS8]; norm_num)
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπodd : Odd (Nat.card ↥π.ker) := by
    rw [QuotientGroup.ker_mk']
    exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥X))
  exact ⟨hEXdisj, hS8, hS2, hπsurj, hπodd⟩

private theorem pairLift_P_exists {X : Subgroup G}
    {π : ↥X →* (↥X ⧸ pPrimeCore 2 ↥X)}
    (hπsurj : Function.Surjective π) (hπodd : Odd (Nat.card ↥π.ker))
    {L : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)} (hL : IsComponent L) :
    ∃ P : Subgroup G, P ≤ X ∧ IsPComponent 2 (P.subgroupOf X) ∧
      (P.subgroupOf X).map π = L ∧
      ∀ x : ↥X, π x ∈ Subgroup.centralizer (L : Set (↥X ⧸ pPrimeCore 2 ↥X)) →
        (x : G) ∈ GH74.GLS.centralizerSection P (GH74.GLS.pPrimeCoreOf 2 P) := by
  obtain ⟨P, hPcomp, hPmap, -, hPcent⟩ :=
    GH74.GLS.Stage2.Signalizer.Odd87.exists_pcomp_lift (G := G)
      (B := ↥X ⧸ pPrimeCore 2 ↥X) π hπsurj hπodd hL
  exact ⟨P, hPcomp.1, hPcomp.2, hPmap, hPcent⟩

private theorem pairLift_Kbar_facts (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y)
    {X : Subgroup G} {π : ↥X →* (↥X ⧸ pPrimeCore 2 ↥X)} :
    V ⊔ zpowers t ≤ Subgroup.centralizer (K : Set G) ∧
      V ⊔ zpowers t ≤ Subgroup.centralizer ({t} : Set G) ∧
      ∀ s ∈ ((V ⊔ zpowers t).subgroupOf X).map π,
        ∀ k ∈ (K.subgroupOf X).map π, s * k = k * s := by
  have hEK : V ⊔ zpowers t ≤ Subgroup.centralizer (K : Set G) :=
    (sup_zpowers_le_centralizer_inf_of_l34SuzOdd hS hD).trans inf_le_right
  have hEt : V ⊔ zpowers t ≤ Subgroup.centralizer ({t} : Set G) := by
    refine sup_le ?_ ?_
    · intro v hv
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hS.t_mem v (hD.le_A hv))
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hScent : ∀ s ∈ ((V ⊔ zpowers t).subgroupOf X).map π,
      ∀ k ∈ (K.subgroupOf X).map π, s * k = k * s := by
    intro s hs k hk
    obtain ⟨e, heEX, rfl⟩ := Subgroup.mem_map.mp hs
    obtain ⟨k0, hk0, rfl⟩ := Subgroup.mem_map.mp hk
    have heX : (e : G) ∈ V ⊔ zpowers t := Subgroup.mem_subgroupOf.mp heEX
    have hkG : (k0 : G) ∈ K := Subgroup.mem_subgroupOf.mp hk0
    have hmem : (k0 : G) * (e : G) = (e : G) * (k0 : G) :=
      Subgroup.mem_centralizer_iff.mp (hEK heX) (k0 : G) hkG
    have hXcomm : e * k0 = k0 * e := Subtype.ext hmem.symm
    rw [← map_mul, ← map_mul, hXcomm]
  exact ⟨hEK, hEt, hScent⟩

private theorem pairLift_Lt_facts {X : Subgroup G}
    {tbar : ↥X ⧸ pPrimeCore 2 ↥X}
    {L : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    (hL : IsComponent L) (hLtne : L.map (MulAut.conj tbar).toMonoidHom ≠ L) :
    IsComponent (L.map (MulAut.conj tbar).toMonoidHom) ∧
      L ≤ Subgroup.centralizer ((L.map (MulAut.conj tbar).toMonoidHom) : Set _) := by
  have hLtcomp : IsComponent (L.map (MulAut.conj tbar).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj tbar) hL
  have hc : L ≤ Subgroup.centralizer ((L.map (MulAut.conj tbar).toMonoidHom) : Set _) := by
    have hbot : ⁅L, L.map (MulAut.conj tbar).toMonoidHom⁆ = ⊥ :=
      (CFSG.LocalCores.distinct_components_commute hL hLtcomp).resolve_left (Ne.symm hLtne)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  exact ⟨hLtcomp, hc⟩

omit [Finite G]
  in
private theorem pairLift_Kbar_range {X : Subgroup G}
    {Kbar : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    {tbar : ↥X ⧸ pPrimeCore 2 ↥X}
    {L : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    (hc : L ≤ Subgroup.centralizer ((L.map (MulAut.conj tbar).toMonoidHom) : Set _))
    (hdiag : ((Kbar : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)) :
        Set (↥X ⧸ pPrimeCore 2 ↥X)) =
      {g | ∃ k ∈ L, k * (tbar * k * tbar⁻¹) = g}) :
    Kbar = (HarrisLit.swapDiag L tbar hc).range := by
  ext g
  change g ∈ ((Kbar : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)) : Set _) ↔
    g ∈ (HarrisLit.swapDiag L tbar hc).range
  rw [hdiag]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, by simp [HarrisLit.swapDiag_apply, MulAut.conj_apply]⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k.1, k.2, by simp [HarrisLit.swapDiag_apply, MulAut.conj_apply]⟩

omit [Finite G]
  in
private theorem pairLift_class {X : Subgroup G}
    {tbar : ↥X ⧸ pPrimeCore 2 ↥X}
    {S Kbar : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    {L : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    (hL : IsComponent L)
    (hScent : ∀ s ∈ S, ∀ k ∈ Kbar, s * k = k * s)
    (hsupp : ∀ L' : Subgroup (↥X ⧸ pPrimeCore 2 ↥X), IsComponent L' →
      (⁅Kbar, L'⁆ ≠ ⊥ ↔ L' = L ∨ L' = L.map (MulAut.conj tbar).toMonoidHom)) :
    ∀ s ∈ S, L.map (MulAut.conj s).toMonoidHom = L ∨
      L.map (MulAut.conj s).toMonoidHom = L.map (MulAut.conj tbar).toMonoidHom := by
  intro s hs
  have hfix : Kbar.map (MulAut.conj s).toMonoidHom = Kbar := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      change s * k * s⁻¹ ∈ Kbar
      rw [hScent s hs k hk, mul_inv_cancel_right]
      exact hk
    · intro hx
      refine ⟨x, hx, ?_⟩
      change s * x * s⁻¹ = x
      rw [hScent s hs x hx, mul_inv_cancel_right]
  have hne : ⁅Kbar, L.map (MulAut.conj s).toMonoidHom⁆ ≠ ⊥ := by
    intro hbot
    have hmap : (⁅Kbar, L⁆).map (MulAut.conj s).toMonoidHom = ⊥ := by
      rw [Subgroup.map_commutator, hfix, hbot]
    have hne0 : ⁅Kbar, L⁆ ≠ ⊥ := (hsupp L hL).mpr (Or.inl rfl)
    exact hne0 ((Subgroup.map_eq_bot_iff_of_injective (H := ⁅Kbar, L⁆)
      (f := (MulAut.conj s).toMonoidHom) (MulAut.conj s).injective).mp hmap)
  have hcomp : IsComponent (L.map (MulAut.conj s).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj s) hL
  exact (hsupp (L.map (MulAut.conj s).toMonoidHom) hcomp).mp hne

omit [Finite G]
  in
private theorem pairLift_tbarS_exp {X : Subgroup G}
    {π : ↥X →* (↥X ⧸ pPrimeCore 2 ↥X)} {tX : ↥X} {tbar : ↥X ⧸ pPrimeCore 2 ↥X}
    (htX : (tX : G) = t) (htbar : tbar = π tX)
    {EX : Subgroup ↥X} (hEX : EX = (V ⊔ zpowers t).subgroupOf X)
    {S : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)} (hS : S = EX.map π)
    (hEelem : IsElemTwo (V ⊔ zpowers t)) :
    tbar ∈ S ∧ ∀ s ∈ S, s * s = 1 := by
  have htbarS : tbar ∈ S := by
    rw [hS, htbar]
    refine Subgroup.mem_map.mpr ⟨tX, ?_, rfl⟩
    rw [hEX, Subgroup.mem_subgroupOf, htX]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hSexp : ∀ s ∈ S, s * s = 1 := by
    intro s hs
    rw [hS, hEX] at hs
    obtain ⟨e, heEX, rfl⟩ := Subgroup.mem_map.mp hs
    have heE : (e : G) ∈ V ⊔ zpowers t := Subgroup.mem_subgroupOf.mp heEX
    have he2G : (e : G) * (e : G) = 1 := hEelem.2 (e : G) heE
    have he2 : e * e = 1 := Subtype.ext he2G
    rw [← map_mul, he2, map_one]
  exact ⟨htbarS, hSexp⟩

omit [Finite G]
  in
private theorem pairLift_fix_centralizes {X : Subgroup G}
    {π : ↥X →* (↥X ⧸ pPrimeCore 2 ↥X)} {tX : ↥X} {tbar : ↥X ⧸ pPrimeCore 2 ↥X}
    (htX : (tX : G) = t) (htbar : tbar = π tX)
    {EX : Subgroup ↥X} (hEX : EX = (V ⊔ zpowers t).subgroupOf X)
    {S Kbar : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    (hS : S = EX.map π)
    {L : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    (hc : L ≤ Subgroup.centralizer ((L.map (MulAut.conj tbar).toMonoidHom) : Set _))
    (hLperf : Group.IsPerfect ↥L)
    (hEt : V ⊔ zpowers t ≤ Subgroup.centralizer ({t} : Set G))
    (hKbar_range : Kbar = (HarrisLit.swapDiag L tbar hc).range)
    (hScent : ∀ s ∈ S, ∀ k ∈ Kbar, s * k = k * s) :
    ∀ s ∈ S, L.map (MulAut.conj s).toMonoidHom = L →
      s ∈ Subgroup.centralizer (L : Set _) := by
  intro s hs hfix
  refine HarrisLit.mem_centralizer_of_map_conj_eq hc hLperf hfix ?_ ?_
  · rw [hS, hEX] at hs
    obtain ⟨e, heEX, rfl⟩ := Subgroup.mem_map.mp hs
    have heE : (e : G) ∈ V ⊔ zpowers t := Subgroup.mem_subgroupOf.mp heEX
    have het : (e : G) * t = t * (e : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hEt heE)
    have hetX : e * tX = tX * e := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, htX]
      exact het)
    rw [htbar, ← map_mul, ← map_mul, hetX]
  · rw [← hKbar_range]
    exact Subgroup.mem_centralizer_iff.mpr (fun k hk => (hScent s hs k hk).symm)

omit [Finite G]
  in
private theorem pairLift_swap_fixes {X : Subgroup G}
    {tbar : ↥X ⧸ pPrimeCore 2 ↥X}
    {S : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    (hSexp : ∀ s ∈ S, s * s = 1)
    {L : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)} :
    ∀ s ∈ S, L.map (MulAut.conj s).toMonoidHom = L.map (MulAut.conj tbar).toMonoidHom →
      L.map (MulAut.conj (s * tbar)).toMonoidHom = L := by
  intro s hs hswap
  have hswap' : L.map (MulAut.conj s).toMonoidHom =
      L.map (MulAut.conj tbar).toMonoidHom := hswap
  have hs2 : s * s = 1 := hSexp s hs
  have hcomp : ∀ x : ↥X ⧸ pPrimeCore 2 ↥X,
      MulAut.conj (s * tbar) x = MulAut.conj s (MulAut.conj tbar x) := by
    intro x
    simp only [MulAut.conj_apply]
    group
  have hmap : L.map (MulAut.conj (s * tbar)).toMonoidHom =
      (L.map (MulAut.conj tbar).toMonoidHom).map (MulAut.conj s).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    exact hcomp x
  rw [hmap, ← hswap']
  have hsq : (MulAut.conj s).toMonoidHom.comp (MulAut.conj s).toMonoidHom =
      MonoidHom.id _ := by
    ext x
    change (MulAut.conj s) ((MulAut.conj s) x) = x
    rw [MulAut.conj_apply, MulAut.conj_apply]
    calc s * (s * (x : _) * s⁻¹) * s⁻¹ = (s * s) * (x : _) * (s * s)⁻¹ := by group
      _ = x := by rw [hs2]; group
  rw [Subgroup.map_map, hsq, Subgroup.map_id]

private theorem pairLift_tbar2 (hS : L34SuzOddSetting A t) {X : Subgroup G}
    {π : ↥X →* (↥X ⧸ pPrimeCore 2 ↥X)} {tX : ↥X} (htX : (tX : G) = t)
    {tbar : ↥X ⧸ pPrimeCore 2 ↥X} (htbar : tbar = π tX) :
    tbar * tbar = 1 := by
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← hS.orderOf_t]
    exact pow_orderOf_eq_one t
  have htX2 : tX * tX = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_one, htX, ht2])
  rw [htbar, ← map_mul, htX2, map_one]

omit [Finite G]
  in
private theorem pairLift_Ktil_facts {X : Subgroup G}
    {S : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)} (hS8 : Nat.card ↥S = 8)
    {L : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    {tbar : ↥X ⧸ pPrimeCore 2 ↥X}
    (hLtne : L.map (MulAut.conj tbar).toMonoidHom ≠ L)
    (hclass : ∀ s ∈ S, L.map (MulAut.conj s).toMonoidHom = L ∨
      L.map (MulAut.conj s).toMonoidHom = L.map (MulAut.conj tbar).toMonoidHom)
    (hfix_centralizes : ∀ s ∈ S, L.map (MulAut.conj s).toMonoidHom = L →
      s ∈ Subgroup.centralizer (L : Set _))
    (hswap_fixes : ∀ s ∈ S, L.map (MulAut.conj s).toMonoidHom =
        L.map (MulAut.conj tbar).toMonoidHom →
      L.map (MulAut.conj (s * tbar)).toMonoidHom = L)
    (htbarS : tbar ∈ S) :
    tbar ∉ Subgroup.centralizer (L : Set _) ∧
      ((S ⊓ Subgroup.centralizer (L : Set _)).subgroupOf S).index = 2 ∧
      Nat.card ↥(S ⊓ Subgroup.centralizer (L : Set _)) = 4 := by
  have htbar_not_cent : tbar ∉ Subgroup.centralizer (L : Set _) := by
    intro hcent
    have hfix : L.map (MulAut.conj tbar).toMonoidHom = L := by
      ext x
      constructor
      · rintro ⟨l, hl, rfl⟩
        change tbar * l * tbar⁻¹ ∈ L
        rw [show tbar * l * tbar⁻¹ = l by
          rw [show tbar * l = l * tbar from (Subgroup.mem_centralizer_iff.mp hcent l hl).symm]
          group]
        exact hl
      · intro hx
        refine ⟨x, hx, ?_⟩
        change tbar * x * tbar⁻¹ = x
        rw [show tbar * x = x * tbar from (Subgroup.mem_centralizer_iff.mp hcent x hx).symm]
        group
    exact hLtne hfix
  have hindex : ((S ⊓ Subgroup.centralizer (L : Set _)).subgroupOf S).index = 2 := by
    rw [Subgroup.index_eq_two_iff_exists_notMem_and]
    refine ⟨⟨tbar, htbarS⟩, ?_, ?_⟩
    · intro htK
      exact htbar_not_cent (Subgroup.mem_subgroupOf.mp htK).2
    · intro b
      rcases hclass b.1 b.2 with hfix | hswap
      · exact Or.inr (Subgroup.mem_subgroupOf.mpr ⟨b.2, hfix_centralizes b.1 b.2 hfix⟩)
      · refine Or.inl (Subgroup.mem_subgroupOf.mpr ⟨S.mul_mem b.2 htbarS, ?_⟩)
        exact hfix_centralizes (b.1 * tbar) (S.mul_mem b.2 htbarS)
          (hswap_fixes b.1 b.2 hswap)
  have hKtil_card : Nat.card ↥(S ⊓ Subgroup.centralizer (L : Set _)) = 4 := by
    have h := ((S ⊓ Subgroup.centralizer (L : Set _)).subgroupOf S).card_mul_index
    rw [hindex, hS8] at h
    have h4 : Nat.card ↥((S ⊓ Subgroup.centralizer (L : Set _)).subgroupOf S) = 4 := by omega
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show S ⊓ Subgroup.centralizer (L : Set _) ≤ S from inf_le_left)).toEquiv] at h4
  exact ⟨htbar_not_cent, hindex, hKtil_card⟩

omit [Finite G]
  in
private theorem pairLift_x2_facts {X : Subgroup G}
    {tbar : ↥X ⧸ pPrimeCore 2 ↥X} (htbar2 : tbar * tbar = 1)
    {L : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    {x₁ : ↥X ⧸ pPrimeCore 2 ↥X} (hx₁L : x₁ ∈ L) (hx₁2 : x₁ * x₁ = 1)
    (hx₁ne1 : x₁ ≠ 1) (hx₁nc : x₁ ∉ Subgroup.centralizer (L : Set _))
    (hc : L ≤ Subgroup.centralizer ((L.map (MulAut.conj tbar).toMonoidHom) : Set _)) :
    MulAut.conj tbar x₁ ∈ L.map (MulAut.conj tbar).toMonoidHom ∧
      (MulAut.conj tbar x₁) * (MulAut.conj tbar x₁) = 1 ∧
      MulAut.conj tbar x₁ ≠ 1 ∧
      MulAut.conj tbar x₁ ∉ Subgroup.centralizer
        ((L.map (MulAut.conj tbar).toMonoidHom) : Set _) ∧
      x₁ * MulAut.conj tbar x₁ = MulAut.conj tbar x₁ * x₁ ∧
      x₁ ≠ MulAut.conj tbar x₁ := by
  set x₂ : ↥X ⧸ pPrimeCore 2 ↥X := MulAut.conj tbar x₁ with hx₂
  have hx₂Lt : x₂ ∈ L.map (MulAut.conj tbar).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨x₁, hx₁L, rfl⟩
  have hx₂2 : x₂ * x₂ = 1 := by
    rw [hx₂, ← map_mul, hx₁2, map_one]
  have hx₂ne1 : x₂ ≠ 1 := by
    intro h
    have hc2 := congrArg (MulAut.conj tbar) h
    rw [hx₂] at hc2
    rw [CFSG.ComponentClassification.HarrisLit.conj_conj_of_sq_eq_one
      (by rw [pow_two]; exact htbar2) x₁, map_one] at hc2
    exact hx₁ne1 hc2
  have hx₂nc : x₂ ∉ Subgroup.centralizer
      ((L.map (MulAut.conj tbar).toMonoidHom) : Set _) := by
    intro hx₂c
    apply hx₁nc
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyLt : MulAut.conj tbar y ∈ L.map (MulAut.conj tbar).toMonoidHom := by
      exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp hx₂c _ hyLt
    have hconj := congrArg (MulAut.conj tbar) hcomm
    rw [hx₂] at hconj
    rw [map_mul, map_mul,
      CFSG.ComponentClassification.HarrisLit.conj_conj_of_sq_eq_one
        (by rw [pow_two]; exact htbar2) y,
      CFSG.ComponentClassification.HarrisLit.conj_conj_of_sq_eq_one
        (by rw [pow_two]; exact htbar2) x₁] at hconj
    exact hconj
  have hx₁x₂comm : x₁ * x₂ = x₂ * x₁ := by
    have h := Subgroup.mem_centralizer_iff.mp (hc hx₁L) x₂ hx₂Lt
    exact h.symm
  have hx₁x₂ne : x₁ ≠ x₂ := by
    intro h
    have hx₁Lt : x₁ ∈ L.map (MulAut.conj tbar).toMonoidHom := by rw [h]; exact hx₂Lt
    apply hx₁nc
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hc hy) x₁ hx₁Lt).symm
  exact ⟨hx₂Lt, hx₂2, hx₂ne1, hx₂nc, hx₁x₂comm, hx₁x₂ne⟩

private theorem pairLift_R_facts {X : Subgroup G}
    {x₁ x₂ : ↥X ⧸ pPrimeCore 2 ↥X}
    (hx₁2 : x₁ * x₁ = 1) (hx₂2 : x₂ * x₂ = 1)
    (hx₁ne1 : x₁ ≠ 1) (hx₂ne1 : x₂ ≠ 1) (hx₁x₂ne : x₁ ≠ x₂)
    (hx₁x₂comm : x₁ * x₂ = x₂ * x₁) :
    x₁ ∉ zpowers x₂ ∧ Nat.card ↥(zpowers x₁ ⊔ zpowers x₂) = 4 := by
  have hx₁notR2 : x₁ ∉ zpowers x₂ := by
    intro h
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h
    have hx₁x₂ : x₁ = x₂ := by
      rcases CFSG.GroupTheory.zpow_eq_one_or_self_of_mul_self_eq_one hx₂2 i with h1 | h2
      · exact False.elim (hx₁ne1 (hi.symm.trans h1))
      · exact hi.symm.trans h2
    exact hx₁x₂ne hx₁x₂
  have hR4 : Nat.card ↥(zpowers x₁ ⊔ zpowers x₂) = 4 := by
    have hres := CFSG.ComponentClassification.GrSLit.GrS5.elemTwo_zpowers_sup
      (x := x₁) (H := zpowers x₂) hx₁2
      (CFSG.ComponentClassification.GrSLit.isElemTwo_zpowers hx₂2)
      (fun y hy => by
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hy
        rcases CFSG.GroupTheory.zpow_eq_one_or_self_of_mul_self_eq_one hx₂2 j with h1 | h2
        · rw [← hj, h1, mul_one, one_mul]
        · rw [← hj, h2, hx₁x₂comm]) hx₁notR2
    rw [hres.2]
    have hx₂ord : orderOf x₂ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx₂2) hx₂ne1
    rw [Nat.card_zpowers, hx₂ord]
  exact ⟨hx₁notR2, hR4⟩

private theorem pairLift_E1_exists {X : Subgroup G}
    {π : ↥X →* (↥X ⧸ pPrimeCore 2 ↥X)}
    {EX : Subgroup ↥X} (hEX : EX = (V ⊔ zpowers t).subgroupOf X)
    (hEXle : V ⊔ zpowers t ≤ X)
    {Ktil : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    (hEXdisj : EX ⊓ π.ker = ⊥)
    (hKtil_le : Ktil ≤ EX.map π) (hKtil_card : Nat.card ↥Ktil = 4) :
    ∃ E₁ : Subgroup G, E₁.subgroupOf X = EX ⊓ Ktil.comap π ∧ E₁ ≤ V ⊔ zpowers t ∧
      Nat.card E₁ = 4 ∧ (E₁.subgroupOf X).map π = Ktil ∧ E₁ ≤ X ∧
      E₁ = (EX ⊓ Ktil.comap π).map X.subtype := by
  have hmap_inf : (EX ⊓ Ktil.comap π).map π = Ktil := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Subgroup.mem_comap.mp hx.2
    · intro hq
      have hq' : q ∈ EX.map π := hKtil_le hq
      obtain ⟨x, hxEX, hxq⟩ := Subgroup.mem_map.mp hq'
      exact ⟨x, Subgroup.mem_inf.mpr ⟨hxEX, Subgroup.mem_comap.mpr (hxq ▸ hq)⟩, hxq⟩
  have hHdisj : (EX ⊓ Ktil.comap π) ⊓ π.ker = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right π.ker (inf_le_left : EX ⊓ Ktil.comap π ≤ EX)).trans
      (le_of_eq hEXdisj))
  have hHcard : Nat.card ↥(EX ⊓ Ktil.comap π) = Nat.card ↥Ktil := by
    have h := CFSG.GorensteinWalter.card_map_eq_card_mul_card_ker π (EX ⊓ Ktil.comap π)
    rw [hHdisj, Subgroup.card_bot, mul_one, hmap_inf] at h
    exact h
  refine ⟨(EX ⊓ Ktil.comap π).map X.subtype, ?_, ?_, ?_, ?_, Subgroup.map_subtype_le _, rfl⟩
  · exact Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
  · refine (Subgroup.map_mono inf_le_left).trans ?_
    rw [hEX]
    exact le_of_eq (Subgroup.map_subgroupOf_eq_of_le hEXle)
  · rw [Subgroup.card_map_of_injective X.subtype_injective, hHcard, hKtil_card]
  · have hsub : ((EX ⊓ Ktil.comap π).map X.subtype).subgroupOf X = EX ⊓ Ktil.comap π :=
      Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
    rw [hsub, hmap_inf]

omit [Finite G]
  in
private theorem pairLift_E1_centralizesSection {X : Subgroup G}
    {π : ↥X →* (↥X ⧸ pPrimeCore 2 ↥X)}
    {EX : Subgroup ↥X} {Ktil : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    {L : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    {E₁ P : Subgroup G} (hE₁ : E₁ = (EX ⊓ Ktil.comap π).map X.subtype)
    (hPcent : ∀ x : ↥X, π x ∈ Subgroup.centralizer
        (L : Set (↥X ⧸ pPrimeCore 2 ↥X)) →
      (x : G) ∈ GH74.GLS.centralizerSection P (GH74.GLS.pPrimeCoreOf 2 P))
    (hKtil : Ktil ≤ Subgroup.centralizer (L : Set _)) :
    ∀ e ∈ E₁, e ∈ GH74.GLS.centralizerSection P (GH74.GLS.pPrimeCoreOf 2 P) := by
  intro e he
  rw [hE₁] at he
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp he
  exact hPcent x (hKtil (Subgroup.mem_comap.mp hx.2))

omit [Finite G]
  in
private theorem pairLift_E1_norm_comm {P E₁ : Subgroup G}
    (hE₁cent : ∀ e ∈ E₁,
      e ∈ GH74.GLS.centralizerSection P (GH74.GLS.pPrimeCoreOf 2 P)) :
    E₁ ≤ Subgroup.normalizer (P : Set G) ∧
      ∀ e ∈ E₁, ∀ l ∈ P, e * l * e⁻¹ * l⁻¹ ∈ oddIn P := by
  refine ⟨fun e he => (hE₁cent e he).1, ?_⟩
  intro e he l hl
  have hmem : ⁅l, e⁆ ∈ GH74.GLS.pPrimeCoreOf 2 P := (hE₁cent e he).2.2 l hl
  have hinv : ⁅l, e⁆⁻¹ ∈ GH74.GLS.pPrimeCoreOf 2 P := Subgroup.inv_mem _ hmem
  have hEq : e * l * e⁻¹ * l⁻¹ = ⁅l, e⁆⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [hEq]
  exact hinv

private theorem pairLift_P_map_ne {X : Subgroup G}
    {π : ↥X →* (↥X ⧸ pPrimeCore 2 ↥X)} {tX : ↥X} {tbar : ↥X ⧸ pPrimeCore 2 ↥X}
    (htX : (tX : G) = t) (htbar : tbar = π tX)
    {P : Subgroup G} {L : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    (hPmap : (P.subgroupOf X).map π = L)
    (hLtne : L.map (MulAut.conj tbar).toMonoidHom ≠ L) :
    P.map (MulAut.conj t).toMonoidHom ≠ P := by
  intro hPeq
  apply hLtne
  have hsub : L.map (MulAut.conj tbar).toMonoidHom ≤ L := by
    rintro z ⟨l, hl, rfl⟩
    have hl' : l ∈ (P.subgroupOf X).map π := by rw [hPmap]; exact hl
    obtain ⟨x, hxP, hxl⟩ := Subgroup.mem_map.mp hl'
    have hxG : (x : G) ∈ P := Subgroup.mem_subgroupOf.mp hxP
    have hconj : (MulAut.conj t) (x : G) ∈ P := by
      rw [← hPeq]
      exact Subgroup.mem_map.mpr ⟨(x : G), hxG, rfl⟩
    have hxP' : tX * x * tX⁻¹ ∈ P.subgroupOf X := by
      rw [Subgroup.mem_subgroupOf]
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, htX, MulAut.conj_apply] using hconj
    change tbar * l * tbar⁻¹ ∈ L
    rw [← hxl]
    have hz : tbar * π x * tbar⁻¹ = π (tX * x * tX⁻¹) := by
      rw [htbar]
      simp only [map_mul, map_inv]
    rw [hz, ← hPmap]
    exact Subgroup.mem_map.mpr ⟨tX * x * tX⁻¹, hxP', rfl⟩
  have hcardLt : Nat.card ↥(L.map (MulAut.conj tbar).toMonoidHom) = Nat.card ↥L :=
    Subgroup.card_map_of_injective (f := (MulAut.conj tbar).toMonoidHom)
      (MulAut.conj tbar).injective
  exact Subgroup.eq_of_le_of_card_ge hsub (by rw [hcardLt])

omit [Finite G]
  in
private theorem pairLift_S_comm {X : Subgroup G}
    {π : ↥X →* (↥X ⧸ pPrimeCore 2 ↥X)}
    {EX : Subgroup ↥X} (hEX : EX = (V ⊔ zpowers t).subgroupOf X)
    {S : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)} (hS : S = EX.map π)
    (hEelem : IsElemTwo (V ⊔ zpowers t))
    {tbar : ↥X ⧸ pPrimeCore 2 ↥X} (htbar2 : tbar * tbar = 1)
    {L : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    (hc : L ≤ Subgroup.centralizer ((L.map (MulAut.conj tbar).toMonoidHom) : Set _))
    {x₂ : ↥X ⧸ pPrimeCore 2 ↥X} (hx₂Lt : x₂ ∈ L.map (MulAut.conj tbar).toMonoidHom)
    (htbarS : tbar ∈ S) :
    (∀ s ∈ S, ∀ s' ∈ S, s * s' = s' * s) ∧
      (∀ k ∈ S ⊓ Subgroup.centralizer (L : Set _), k * tbar = tbar * k) ∧
      (S ⊓ Subgroup.centralizer (L : Set _) ≤
        Subgroup.centralizer ((L.map (MulAut.conj tbar).toMonoidHom) : Set _)) ∧
      x₂ ∈ Subgroup.centralizer (L : Set _) := by
  have hScomm : ∀ s ∈ S, ∀ s' ∈ S, s * s' = s' * s := by
    intro s hs s' hs'
    rw [hS, hEX] at hs hs'
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hs
    obtain ⟨e', he', rfl⟩ := Subgroup.mem_map.mp hs'
    have heE : (e : G) ∈ V ⊔ zpowers t := Subgroup.mem_subgroupOf.mp he
    have he'E : (e' : G) ∈ V ⊔ zpowers t := Subgroup.mem_subgroupOf.mp he'
    have hcommG : (e : G) * (e' : G) = (e' : G) * (e : G) :=
      hEelem.1 (e : G) heE (e' : G) he'E
    have hcommX : e * e' = e' * e := Subtype.ext hcommG
    rw [← map_mul, ← map_mul, hcommX]
  have htinv : tbar⁻¹ = tbar := by
    calc tbar⁻¹ = (tbar * tbar) * tbar⁻¹ := by rw [htbar2, one_mul]
      _ = tbar * (tbar * tbar⁻¹) := by rw [mul_assoc]
      _ = tbar := by rw [mul_inv_cancel, mul_one]
  have hKtil_cent_tbar : ∀ k ∈ S ⊓ Subgroup.centralizer (L : Set _), k * tbar = tbar * k :=
    fun k hk => hScomm k (Subgroup.mem_inf.mp hk).1 tbar htbarS
  have hKtil_centLt : S ⊓ Subgroup.centralizer (L : Set _) ≤
      Subgroup.centralizer ((L.map (MulAut.conj tbar).toMonoidHom) : Set _) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hy
    have hkl : k * l = l * k :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hk).2 l hl).symm
    have hcomm : k * (tbar * l * tbar⁻¹) = (tbar * l * tbar⁻¹) * k := by
      calc k * (tbar * l * tbar⁻¹) = (k * tbar) * l * tbar⁻¹ := by group
        _ = (tbar * k) * l * tbar⁻¹ := by rw [hKtil_cent_tbar k hk]
        _ = tbar * (k * l) * tbar⁻¹ := by group
        _ = tbar * (l * k) * tbar⁻¹ := by rw [hkl]
        _ = (tbar * l) * (k * tbar⁻¹) := by group
        _ = (tbar * l) * (tbar⁻¹ * k) := by
              rw [show k * tbar⁻¹ = tbar⁻¹ * k from by
                rw [htinv, hKtil_cent_tbar k hk]]
        _ = (tbar * l * tbar⁻¹) * k := by group
    exact hcomm.symm
  have hx₂_centL : x₂ ∈ Subgroup.centralizer (L : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_iff.mp (hc hl) x₂ hx₂Lt).symm
  exact ⟨hScomm, hKtil_cent_tbar, hKtil_centLt, hx₂_centL⟩

omit [Finite G]
  in
private theorem pairLift_R_mem {X : Subgroup G}
    {x₁ x₂ : ↥X ⧸ pPrimeCore 2 ↥X}
    (hx₁2 : x₁ * x₁ = 1) (hx₂2 : x₂ * x₂ = 1) (hx₁x₂comm : x₁ * x₂ = x₂ * x₁) :
    ∀ z ∈ zpowers x₁ ⊔ zpowers x₂, z = 1 ∨ z = x₁ ∨ z = x₂ ∨ z = x₁ * x₂ := by
  intro z hz
  obtain ⟨i, h, hh, hzh⟩ := CFSG.ComponentClassification.GrSLit.GrS5.mem_zpowers_sup
    (z := x₁) (H := zpowers x₂)
    (fun y hy => by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_right (show Commute x₁ x₂ from hx₁x₂comm) j).eq) hz
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  rcases CFSG.GroupTheory.zpow_eq_one_or_self_of_mul_self_eq_one hx₁2 i with h1 | h1 <;>
    rcases CFSG.GroupTheory.zpow_eq_one_or_self_of_mul_self_eq_one hx₂2 j with h2 | h2
  · left; rw [hzh, h1, h2, one_mul]
  · right; right; left; rw [hzh, h1, h2, one_mul]
  · right; left; rw [hzh, h1, h2, mul_one]
  · right; right; right; rw [hzh, h1, h2]

omit [Finite G]
  in
private theorem pairLift_KtilR {X : Subgroup G}
    {S : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    {L : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)} {tbar : ↥X ⧸ pPrimeCore 2 ↥X}
    {x₁ x₂ : ↥X ⧸ pPrimeCore 2 ↥X}
    (hx₁L : x₁ ∈ L) (hx₂Lt : x₂ ∈ L.map (MulAut.conj tbar).toMonoidHom)
    (hx₁nc : x₁ ∉ Subgroup.centralizer (L : Set _))
    (hx₂nc : x₂ ∉ Subgroup.centralizer
      ((L.map (MulAut.conj tbar).toMonoidHom) : Set _))
    (hx₂2 : x₂ * x₂ = 1)
    (hx₂_centL : x₂ ∈ Subgroup.centralizer (L : Set _))
    (hKtil_centLt : S ⊓ Subgroup.centralizer (L : Set _) ≤
      Subgroup.centralizer ((L.map (MulAut.conj tbar).toMonoidHom) : Set _))
    (hRmem : ∀ z ∈ zpowers x₁ ⊔ zpowers x₂,
      z = 1 ∨ z = x₁ ∨ z = x₂ ∨ z = x₁ * x₂) :
    (S ⊓ Subgroup.centralizer (L : Set _)) ⊓ (zpowers x₁ ⊔ zpowers x₂) = ⊥ ∧
      ∀ k ∈ S ⊓ Subgroup.centralizer (L : Set _),
        ∀ r ∈ zpowers x₁ ⊔ zpowers x₂, k * r = r * k := by
  have hKtilRbot : (S ⊓ Subgroup.centralizer (L : Set _)) ⊓ (zpowers x₁ ⊔ zpowers x₂) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzK : z ∈ S ⊓ Subgroup.centralizer (L : Set _) := (Subgroup.mem_inf.mp hz).1
    have hzR : z ∈ zpowers x₁ ⊔ zpowers x₂ := (Subgroup.mem_inf.mp hz).2
    rcases hRmem z hzR with rfl | rfl | rfl | rfl
    · exact Subgroup.mem_bot.mpr rfl
    · exfalso; exact hx₁nc (Subgroup.mem_inf.mp hzK).2
    · exfalso; exact hx₂nc (hKtil_centLt hzK)
    · exfalso
      apply hx₁nc
      have h1 : x₁ * x₂ ∈ Subgroup.centralizer (L : Set _) := (Subgroup.mem_inf.mp hzK).2
      have heq : x₁ = (x₁ * x₂) * x₂ := by rw [mul_assoc, hx₂2, mul_one]
      rw [heq]
      exact Subgroup.mul_mem _ h1 hx₂_centL
  have hKtilRcomm : ∀ k ∈ S ⊓ Subgroup.centralizer (L : Set _),
      ∀ r ∈ zpowers x₁ ⊔ zpowers x₂, k * r = r * k := by
    intro k hk r hr
    have hcent : zpowers x₁ ⊔ zpowers x₂ ≤ Subgroup.centralizer ({k} : Set _) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hk).2 x₁ hx₁L
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp (hKtil_centLt hk) x₂ hx₂Lt
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hcent hr)).symm
  exact ⟨hKtilRbot, hKtilRcomm⟩

omit [Finite G]
  in
private theorem pairLift_Qbar {X : Subgroup G}
    {S : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    {L : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)} {x₁ x₂ : ↥X ⧸ pPrimeCore 2 ↥X}
    (hKtil_card : Nat.card ↥(S ⊓ Subgroup.centralizer (L : Set _)) = 4)
    (hR4 : Nat.card ↥(zpowers x₁ ⊔ zpowers x₂) = 4)
    (hKtilRcomm : ∀ k ∈ S ⊓ Subgroup.centralizer (L : Set _),
      ∀ r ∈ zpowers x₁ ⊔ zpowers x₂, k * r = r * k)
    (hKtilRbot : (S ⊓ Subgroup.centralizer (L : Set _)) ⊓
      (zpowers x₁ ⊔ zpowers x₂) = ⊥) :
    Nat.card ↥((S ⊓ Subgroup.centralizer (L : Set _)) ⊔
        (zpowers x₁ ⊔ zpowers x₂)) = 16 ∧
      IsPGroup 2 ↥((S ⊓ Subgroup.centralizer (L : Set _)) ⊔
        (zpowers x₁ ⊔ zpowers x₂)) := by
  have hQbarCard : Nat.card ↥((S ⊓ Subgroup.centralizer (L : Set _)) ⊔
      (zpowers x₁ ⊔ zpowers x₂)) = 16 := by
    have h := CFSG.LocalAnalysis.UniquenessCase.UCK.card_sup_eq_mul_of_commute_of_inf_eq_bot
      (H := S ⊓ Subgroup.centralizer (L : Set _)) (K := zpowers x₁ ⊔ zpowers x₂)
      hKtilRcomm hKtilRbot
    calc Nat.card ↥((S ⊓ Subgroup.centralizer (L : Set _)) ⊔ (zpowers x₁ ⊔ zpowers x₂))
        = Nat.card ↥(S ⊓ Subgroup.centralizer (L : Set _)) *
          Nat.card ↥(zpowers x₁ ⊔ zpowers x₂) := h
      _ = 4 * 4 := by rw [hKtil_card, hR4]
      _ = 16 := by norm_num
  exact ⟨hQbarCard, IsPGroup.of_card (n := 4) (by rw [hQbarCard]; norm_num)⟩

omit [Finite G]
  in
private theorem pairLift_R_map {X : Subgroup G}
    {tbar : ↥X ⧸ pPrimeCore 2 ↥X} (htbar2 : tbar * tbar = 1)
    {x₁ x₂ : ↥X ⧸ pPrimeCore 2 ↥X} (hx₂ : x₂ = MulAut.conj tbar x₁) :
    (zpowers x₁ ⊔ zpowers x₂).map (MulAut.conj tbar).toMonoidHom ≤
      zpowers x₁ ⊔ zpowers x₂ := by
  rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  have h2 : (MulAut.conj tbar).toMonoidHom x₂ = x₁ := by
    rw [hx₂]
    exact CFSG.ComponentClassification.HarrisLit.conj_conj_of_sq_eq_one
      (by rw [pow_two]; exact htbar2) x₁
  rw [show (MulAut.conj tbar).toMonoidHom x₁ = x₂ from hx₂.symm, h2]
  exact sup_le le_sup_right le_sup_left

omit [Finite G]
  in
private theorem pairLift_Ktil_map {X : Subgroup G}
    {S : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    {L : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)} {tbar : ↥X ⧸ pPrimeCore 2 ↥X}
    (hKtil_cent_tbar : ∀ k ∈ S ⊓ Subgroup.centralizer (L : Set _), k * tbar = tbar * k) :
    (S ⊓ Subgroup.centralizer (L : Set _)).map (MulAut.conj tbar).toMonoidHom =
      S ⊓ Subgroup.centralizer (L : Set _) := by
  ext k
  constructor
  · rintro ⟨k', hk', rfl⟩
    have hfix : (MulAut.conj tbar).toMonoidHom k' = k' := by
      change (MulAut.conj tbar) k' = k'
      rw [MulAut.conj_apply, ← hKtil_cent_tbar k' hk']
      group
    rwa [hfix]
  · intro hk
    exact ⟨k, hk, by
      change (MulAut.conj tbar) k = k
      rw [MulAut.conj_apply, ← hKtil_cent_tbar k hk]
      group⟩

omit [Finite G]
  in
private theorem pairLift_Ktil_le_norm {X : Subgroup G}
    {S : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    {L : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)} {tbar : ↥X ⧸ pPrimeCore 2 ↥X}
    {x₁ x₂ : ↥X ⧸ pPrimeCore 2 ↥X} {Ktil Qbar : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    (hKtil : Ktil = S ⊓ Subgroup.centralizer (L : Set _))
    (hQbar : Qbar = Ktil ⊔ (zpowers x₁ ⊔ zpowers x₂))
    (hScomm : ∀ s ∈ S, ∀ s' ∈ S, s * s' = s' * s)
    (hKtil_centLt : S ⊓ Subgroup.centralizer (L : Set _) ≤
      Subgroup.centralizer ((L.map (MulAut.conj tbar).toMonoidHom) : Set _))
    (hx₁L : x₁ ∈ L) (hx₂Lt : x₂ ∈ L.map (MulAut.conj tbar).toMonoidHom) :
    Ktil ≤ Subgroup.normalizer (Qbar : Set _) := by
  intro k hk
  rw [hKtil] at hk
  refine Subgroup.centralizer_le_normalizer (Qbar : Set (↥X ⧸ pPrimeCore 2 ↥X)) ?_
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hcent : Qbar ≤ Subgroup.centralizer ({k} : Set _) := by
    rw [hQbar]
    refine sup_le ?_ ?_
    · intro k' hk'
      rw [hKtil] at hk'
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hScomm k' (Subgroup.mem_inf.mp hk').1 k (Subgroup.mem_inf.mp hk).1
    · refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hk).2 x₁ hx₁L
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact Subgroup.mem_centralizer_iff.mp (hKtil_centLt hk) x₂ hx₂Lt
  exact Subgroup.mem_centralizer_singleton_iff.mp (hcent hq)

omit [Finite G]
  in
private theorem pairLift_Qbar_map {X : Subgroup G}
    {Ktil Qbar : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)} {tbar : ↥X ⧸ pPrimeCore 2 ↥X}
    {x₁ x₂ : ↥X ⧸ pPrimeCore 2 ↥X}
    (hQbar : Qbar = Ktil ⊔ (zpowers x₁ ⊔ zpowers x₂))
    (hKtil_map : Ktil.map (MulAut.conj tbar).toMonoidHom = Ktil)
    (hRmap : (zpowers x₁ ⊔ zpowers x₂).map (MulAut.conj tbar).toMonoidHom ≤
      zpowers x₁ ⊔ zpowers x₂) :
    Qbar.map (MulAut.conj tbar).toMonoidHom ≤ Qbar := by
  rw [hQbar, Subgroup.map_sup, hKtil_map]
  exact sup_le le_sup_left (hRmap.trans le_sup_right)

omit [Finite G]
  in
private theorem pairLift_htbar_norm {X : Subgroup G}
    {Qbar : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)} {tbar : ↥X ⧸ pPrimeCore 2 ↥X}
    (hQmap : Qbar.map (MulAut.conj tbar).toMonoidHom ≤ Qbar)
    (htbar2 : tbar * tbar = 1) :
    tbar ∈ Subgroup.normalizer (Qbar : Set _) := by
  have htbar_conj_mem : ∀ q ∈ Qbar, tbar * q * tbar⁻¹ ∈ Qbar := by
    intro q hq
    have hmem : MulAut.conj tbar q ∈ Qbar.map (MulAut.conj tbar).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨q, hq, rfl⟩
    simpa only [MulAut.conj_apply] using hQmap hmem
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · intro hq
    simpa only [MulAut.conj_apply] using htbar_conj_mem q hq
  · intro hq
    have h2 : tbar * (tbar * q * tbar⁻¹) * tbar⁻¹ ∈ Qbar := htbar_conj_mem _ hq
    have hcomp : tbar * (tbar * q * tbar⁻¹) * tbar⁻¹ = q := by
      have hc := CFSG.ComponentClassification.HarrisLit.conj_conj_of_sq_eq_one
        (by rw [pow_two]; exact htbar2) q
      simpa only [MulAut.conj_apply] using hc
    rwa [hcomp] at h2

omit [Finite G]
  in
private theorem pairLift_SQbar {X : Subgroup G}
    {S : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    {Qbar : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    {L : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)} {tbar : ↥X ⧸ pPrimeCore 2 ↥X}
    (hclass : ∀ s ∈ S, L.map (MulAut.conj s).toMonoidHom = L ∨
      L.map (MulAut.conj s).toMonoidHom = L.map (MulAut.conj tbar).toMonoidHom)
    (hfix_centralizes : ∀ s ∈ S, L.map (MulAut.conj s).toMonoidHom = L →
      s ∈ Subgroup.centralizer (L : Set _))
    (hswap_fixes : ∀ s ∈ S, L.map (MulAut.conj s).toMonoidHom =
        L.map (MulAut.conj tbar).toMonoidHom →
      L.map (MulAut.conj (s * tbar)).toMonoidHom = L)
    (htbarS : tbar ∈ S) (htbar2 : tbar * tbar = 1)
    (hKtil_le_norm : S ⊓ Subgroup.centralizer (L : Set _) ≤
      Subgroup.normalizer (Qbar : Set _))
    (htbar_norm : tbar ∈ Subgroup.normalizer (Qbar : Set _)) :
    S ≤ Subgroup.normalizer (Qbar : Set _) := by
  have hcase : ∀ s ∈ S, s ∈ S ⊓ Subgroup.centralizer (L : Set _) ∨
      s * tbar ∈ S ⊓ Subgroup.centralizer (L : Set _) := by
    intro s hs
    rcases hclass s hs with hfix | hswap
    · exact Or.inl (Subgroup.mem_inf.mpr ⟨hs, hfix_centralizes s hs hfix⟩)
    · exact Or.inr (Subgroup.mem_inf.mpr ⟨S.mul_mem hs htbarS,
        hfix_centralizes (s * tbar) (S.mul_mem hs htbarS) (hswap_fixes s hs hswap)⟩)
  intro s hs
  rcases hcase s hs with hsK | hstK
  · exact hKtil_le_norm hsK
  · have hseq : s = (s * tbar) * tbar := by rw [mul_assoc, htbar2, mul_one]
    rw [hseq]
    exact Subgroup.mul_mem _ (hKtil_le_norm hstK) htbar_norm

private theorem pairLift_T'_exists {X : Subgroup G}
    {EX : Subgroup ↥X} (hEXcard : Nat.card ↥EX = 8)
    {S Qbar : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    (hS : S = EX.map (QuotientGroup.mk' (pPrimeCore 2 ↥X)))
    (hS2 : IsPGroup 2 ↥S) (hQbar2 : IsPGroup 2 ↥Qbar)
    (hSQbar : S ≤ Subgroup.normalizer (Qbar : Set _)) :
    ∃ T' : Subgroup ↥X, IsPGroup 2 ↥T' ∧ EX ≤ T' ∧
      ∀ g : ↥X ⧸ pPrimeCore 2 ↥X, g ∈ Qbar ⊔ S →
        ∃ t ∈ T', (QuotientGroup.mk' (pPrimeCore 2 ↥X)) t = g := by
  set π : ↥X →* (↥X ⧸ pPrimeCore 2 ↥X) := QuotientGroup.mk' (pPrimeCore 2 ↥X)
  let Shat : Subgroup (↥X ⧸ pPrimeCore 2 ↥X) := Qbar ⊔ S
  have hShat2 : IsPGroup 2 ↥Shat := by
    have h := IsPGroup.to_sup_of_normal_right' (p := 2) hS2 hQbar2 hSQbar
    have h' : IsPGroup 2 ↥(Qbar ⊔ S) := by
      rw [sup_comm]
      exact h
    exact h'
  let Y : Subgroup ↥X := Shat.comap π
  let f : ↥Y →* ↥Shat := (π.comp Y.subtype).codRestrict Shat (fun y => y.2)
  have hf : Function.Surjective f := by
    intro g
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥X) (g : ↥X ⧸ pPrimeCore 2 ↥X)
    refine ⟨⟨x, ?_⟩, ?_⟩
    · rw [Subgroup.mem_comap, hx]
      exact g.2
    · exact Subtype.ext hx
  have hEXY : EX ≤ Y := by
    intro x hx
    rw [show Y = Shat.comap π from rfl, Subgroup.mem_comap]
    exact Subgroup.mem_sup_right (by rw [hS]; exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hEXsub2 : IsPGroup 2 ↥(EX.subgroupOf Y) := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEXY).toEquiv, hEXcard]
    norm_num
  obtain ⟨T, hT2, hEXsubT, hTsurj⟩ :=
    CFSG.RankThree.PartTwo.Sec21.Hering2119S.sylow_surj f hShat2 hf (EX.subgroupOf Y) hEXsub2
  let T' : Subgroup ↥X := T.map Y.subtype
  have hT'2 : IsPGroup 2 ↥T' := IsPGroup.map hT2 Y.subtype
  have hEXT' : EX ≤ T' := by
    have h := Subgroup.map_mono hEXsubT (f := Y.subtype)
    rwa [Subgroup.map_subgroupOf_eq_of_le hEXY] at h
  have hsurj' : ∀ g : ↥X ⧸ pPrimeCore 2 ↥X, g ∈ Qbar ⊔ S →
      ∃ t ∈ T', π t = g := by
    intro g hg
    obtain ⟨t, ht, hft⟩ := hTsurj ⟨g, hg⟩
    refine ⟨Y.subtype t, Subgroup.mem_map.mpr ⟨t, ht, rfl⟩, ?_⟩
    have h := congrArg Subtype.val hft
    change π (Y.subtype t) = g at h
    exact h
  exact ⟨T', hT'2, hEXT', hsurj'⟩

omit [Finite G]
  in
private theorem pairLift_T'_disj {X : Subgroup G} {T' : Subgroup ↥X}
    (hT'2 : IsPGroup 2 ↥T') (hNodd : Odd (Nat.card ↥(pPrimeCore 2 ↥X))) :
    T' ⊓ (QuotientGroup.mk' (pPrimeCore 2 ↥X)).ker = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx1 : x = 1 :=
    CFSG.ComponentClassification.AschbacherTheorem3.mk_eq_one_of_odd hNodd hT'2 hx.1
      (MonoidHom.mem_ker.mp hx.2)
  exact Subgroup.mem_bot.mpr hx1

omit [Finite G]
  in
private theorem pairLift_Tinj_comm {X : Subgroup G}
    {T' : Subgroup ↥X} (hT'2 : IsPGroup 2 ↥T')
    (hNodd : Odd (Nat.card ↥(pPrimeCore 2 ↥X))) :
    (∀ b ∈ T', ∀ c ∈ T', (QuotientGroup.mk' (pPrimeCore 2 ↥X)) b =
        (QuotientGroup.mk' (pPrimeCore 2 ↥X)) c → b = c) ∧
      ∀ b ∈ T', ∀ c ∈ T', (QuotientGroup.mk' (pPrimeCore 2 ↥X)) b *
          (QuotientGroup.mk' (pPrimeCore 2 ↥X)) c =
          (QuotientGroup.mk' (pPrimeCore 2 ↥X)) c *
            (QuotientGroup.mk' (pPrimeCore 2 ↥X)) b → b * c = c * b := by
  set π : ↥X →* (↥X ⧸ pPrimeCore 2 ↥X) := QuotientGroup.mk' (pPrimeCore 2 ↥X)
  have hTinj : ∀ b ∈ T', ∀ c ∈ T', π b = π c → b = c := by
    intro b hb c hc hbc
    have hmem : b⁻¹ * c ∈ T' := T'.mul_mem (T'.inv_mem hb) hc
    have hker : π (b⁻¹ * c) = 1 := by rw [map_mul, map_inv, hbc, inv_mul_cancel]
    have h1 : b⁻¹ * c = 1 :=
      CFSG.ComponentClassification.AschbacherTheorem3.mk_eq_one_of_odd hNodd hT'2 hmem hker
    exact inv_mul_eq_one.mp h1
  refine ⟨hTinj, ?_⟩
  intro b hb c hc hcomm
  refine hTinj (b * c) (T'.mul_mem hb hc) (c * b) (T'.mul_mem hc hb) ?_
  rw [map_mul, map_mul]
  exact hcomm

private theorem pairLift_a_exists {X : Subgroup G}
    {tX : ↥X} {tbar : ↥X ⧸ pPrimeCore 2 ↥X}
    (htX : (tX : G) = t) (htbar : tbar = (QuotientGroup.mk' (pPrimeCore 2 ↥X)) tX)
    {P : Subgroup G} (hPpc : IsPComponent 2 (P.subgroupOf X))
    {L : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    (hPmap : (P.subgroupOf X).map (QuotientGroup.mk' (pPrimeCore 2 ↥X)) = L)
    {EX : Subgroup ↥X} {S Qbar : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    {T' : Subgroup ↥X} (hEXT' : EX ≤ T')
    (hTsurj : ∀ g : ↥X ⧸ pPrimeCore 2 ↥X, g ∈ Qbar ⊔ S →
      ∃ t ∈ T', (QuotientGroup.mk' (pPrimeCore 2 ↥X)) t = g)
    (hTinj : ∀ b ∈ T', ∀ c ∈ T', (QuotientGroup.mk' (pPrimeCore 2 ↥X)) b =
      (QuotientGroup.mk' (pPrimeCore 2 ↥X)) c → b = c)
    {x₁ x₂ : ↥X ⧸ pPrimeCore 2 ↥X}
    (hx₁L : x₁ ∈ L) (hx₁2 : x₁ * x₁ = 1) (hx₂ : x₂ = MulAut.conj tbar x₁)
    (hx₁Q : x₁ ∈ Qbar) (htXEX : tX ∈ EX) :
    ∃ (a : G) (a₀ b₀ : ↥X), a ∈ P ∧ a * a = 1 ∧ a₀ ∈ T' ∧ (a₀ : G) = a ∧
      (QuotientGroup.mk' (pPrimeCore 2 ↥X)) a₀ = x₁ ∧ b₀ ∈ T' ∧
      (QuotientGroup.mk' (pPrimeCore 2 ↥X)) b₀ = x₂ ∧
      (b₀ : G) = t * a * t⁻¹ := by
  have hx₁Shat : x₁ ∈ Qbar ⊔ S := Subgroup.mem_sup_left hx₁Q
  obtain ⟨a₀, ha₀T, ha₀π⟩ := hTsurj x₁ hx₁Shat
  have ha₀sq : a₀ * a₀ = 1 := by
    refine hTinj (a₀ * a₀) (T'.mul_mem ha₀T ha₀T) 1 T'.one_mem ?_
    rw [map_mul, ha₀π, hx₁2, map_one]
  have haP : (a₀ : G) ∈ P := by
    have ha₀P : a₀ ∈ P.subgroupOf X := by
      refine CFSG.GH74.Generic.BProg.mem_of_two_pow_eq_one_of_map_mem hPpc (g := a₀)
        (e := 1) ?_ ?_
      · simpa only [pow_two, pow_one] using ha₀sq
      · rw [ha₀π, hPmap]
        exact hx₁L
    exact Subgroup.mem_subgroupOf.mp ha₀P
  have ha2 : (a₀ : G) * (a₀ : G) = 1 := congrArg Subtype.val ha₀sq
  have htXT : tX ∈ T' := hEXT' htXEX
  let b₀ : ↥X := tX * a₀ * tX⁻¹
  have hb₀T : b₀ ∈ T' := T'.mul_mem (T'.mul_mem htXT ha₀T) (T'.inv_mem htXT)
  have hb₀π : (QuotientGroup.mk' (pPrimeCore 2 ↥X)) b₀ = x₂ := by
    change (QuotientGroup.mk' (pPrimeCore 2 ↥X)) (tX * a₀ * tX⁻¹) = x₂
    rw [map_mul, map_mul, map_inv, ha₀π, hx₂, ← htbar, MulAut.conj_apply]
  have hb₀G : (b₀ : G) = t * (a₀ : G) * t⁻¹ := by
    change ((tX * a₀ * tX⁻¹ : ↥X) : G) = t * (a₀ : G) * t⁻¹
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, htX]
  exact ⟨(a₀ : G), a₀, b₀, haP, ha2, ha₀T, rfl, ha₀π, hb₀T, hb₀π, hb₀G⟩

omit [Finite G]
  in
private theorem pairLift_comm {X : Subgroup G}
    {π : ↥X →* (↥X ⧸ pPrimeCore 2 ↥X)}
    {EX : Subgroup ↥X} {Ktil S : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    {L : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    {E₁ : Subgroup G} (hE₁eq : E₁ = (EX ⊓ Ktil.comap π).map X.subtype)
    (hKtil : Ktil = S ⊓ Subgroup.centralizer (L : Set _))
    {T' : Subgroup ↥X} (hEXT' : EX ≤ T')
    (hTcomm : ∀ b ∈ T', ∀ c ∈ T', π b * π c = π c * π b → b * c = c * b)
    {x₁ x₂ : ↥X ⧸ pPrimeCore 2 ↥X} (hx₁L : x₁ ∈ L)
    {a : G} {a₀ b₀ : ↥X} (ha : (a₀ : G) = a) (ha₀T : a₀ ∈ T')
    (hb₀T : b₀ ∈ T') (ha₀π : π a₀ = x₁) (hb₀π : π b₀ = x₂)
    (hx₁x₂comm : x₁ * x₂ = x₂ * x₁) (hb₀G : (b₀ : G) = t * a * t⁻¹) :
    (∀ e ∈ E₁, a * e = e * a) ∧ a * (t * a * t⁻¹) = t * a * t⁻¹ * a := by
  have hcommE : ∀ e ∈ E₁, a * e = e * a := by
    intro e he
    rw [hE₁eq] at he
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp he
    have hxT : x ∈ T' := hEXT' hx.1
    have hπx : π x ∈ Ktil := Subgroup.mem_comap.mp hx.2
    rw [hKtil] at hπx
    have hxcent : x₁ * π x = π x * x₁ :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hπx).2 x₁ hx₁L
    have hπcomm : π x * π a₀ = π a₀ * π x := by rw [ha₀π]; exact hxcent.symm
    have h := congrArg Subtype.val (hTcomm x hxT a₀ ha₀T hπcomm)
    simpa only [Subgroup.coe_mul, Subgroup.coe_subtype, ha] using h.symm
  have hcommConj : a * (t * a * t⁻¹) = t * a * t⁻¹ * a := by
    have hπcomm : π a₀ * π b₀ = π b₀ * π a₀ := by
      rw [ha₀π, hb₀π]
      exact hx₁x₂comm
    have h := congrArg Subtype.val (hTcomm a₀ ha₀T b₀ hb₀T hπcomm)
    simp only [Subgroup.coe_mul] at h
    rw [ha, hb₀G] at h
    exact h
  exact ⟨hcommE, hcommConj⟩

omit [Finite G]
  in
private theorem pairLift_M_le {X : Subgroup G}
    {E₁ : Subgroup G} (hE₁X : E₁ ≤ X)
    {T' : Subgroup ↥X} (hE₁subT : E₁.subgroupOf X ≤ T')
    {a : G} {a₀ b₀ : ↥X} (ha : (a₀ : G) = a) (hb₀G : (b₀ : G) = t * a * t⁻¹)
    (htX' : t ∈ X) (haX : a ∈ X) (ha₀T : a₀ ∈ T') (hb₀T : b₀ ∈ T') :
    E₁ ⊔ Subgroup.closure ({a, t * a * t⁻¹} : Set G) ≤ X ∧
      (E₁ ⊔ Subgroup.closure ({a, t * a * t⁻¹} : Set G)).subgroupOf X =
        E₁.subgroupOf X ⊔
          (Subgroup.closure ({a, t * a * t⁻¹} : Set G)).subgroupOf X ∧
      Subgroup.closure ({a, t * a * t⁻¹} : Set G) ≤ X ∧
      (E₁ ⊔ Subgroup.closure ({a, t * a * t⁻¹} : Set G)).subgroupOf X ≤ T' := by
  have hbX : t * a * t⁻¹ ∈ X := X.mul_mem (X.mul_mem htX' haX) (X.inv_mem htX')
  have hclosureX : Subgroup.closure ({a, t * a * t⁻¹} : Set G) ≤ X := by
    refine (Subgroup.closure_le X).mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact haX
    · exact hbX
  have hMX : E₁ ⊔ Subgroup.closure ({a, t * a * t⁻¹} : Set G) ≤ X := sup_le hE₁X hclosureX
  have hMsub_eq : (E₁ ⊔ Subgroup.closure ({a, t * a * t⁻¹} : Set G)).subgroupOf X =
      E₁.subgroupOf X ⊔
        (Subgroup.closure ({a, t * a * t⁻¹} : Set G)).subgroupOf X :=
    Subgroup.subgroupOf_sup hE₁X hclosureX
  have hclosureT : (Subgroup.closure ({a, t * a * t⁻¹} : Set G)).subgroupOf X ≤ T' := by
    rw [CFSG.subgroupOf_le_iff_le_map_subtype hclosureX]
    refine (Subgroup.closure_le (T'.map X.subtype)).mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Subgroup.mem_map.mpr ⟨a₀, ha₀T, ha⟩
    · exact Subgroup.mem_map.mpr ⟨b₀, hb₀T, hb₀G⟩
  exact ⟨hMX, hMsub_eq, hclosureX, by rw [hMsub_eq]; exact sup_le hE₁subT hclosureT⟩

omit [Finite G]
  in
private theorem pairLift_M_map {X : Subgroup G}
    {π : ↥X →* (↥X ⧸ pPrimeCore 2 ↥X)}
    {EX : Subgroup ↥X} {Ktil Qbar : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    {E₁ : Subgroup G} (hE₁ : E₁.subgroupOf X = EX ⊓ Ktil.comap π)
    (hE₁subXmap : (E₁.subgroupOf X).map π = Ktil)
    {a : G} {a₀ b₀ : ↥X} {x₁ x₂ : ↥X ⧸ pPrimeCore 2 ↥X}
    (hQbar : Qbar = Ktil ⊔ (zpowers x₁ ⊔ zpowers x₂))
    (hMsub_eq : (E₁ ⊔ Subgroup.closure ({a, t * a * t⁻¹} : Set G)).subgroupOf X =
      E₁.subgroupOf X ⊔
        (Subgroup.closure ({a, t * a * t⁻¹} : Set G)).subgroupOf X)
    (hclosureX : Subgroup.closure ({a, t * a * t⁻¹} : Set G) ≤ X)
    (ha : (a₀ : G) = a) (hb₀G : (b₀ : G) = t * a * t⁻¹)
    (ha₀π : π a₀ = x₁) (hb₀π : π b₀ = x₂)
    (hx₁Q : x₁ ∈ Qbar) (hx₂Q : x₂ ∈ Qbar)
    (haM : a ∈ E₁ ⊔ Subgroup.closure ({a, t * a * t⁻¹} : Set G))
    (hbM : t * a * t⁻¹ ∈ E₁ ⊔ Subgroup.closure ({a, t * a * t⁻¹} : Set G)) :
    ((E₁ ⊔ Subgroup.closure ({a, t * a * t⁻¹} : Set G)).subgroupOf X).map π = Qbar := by
  rw [hQbar] at hx₁Q hx₂Q
  have hmapM_le : ((E₁ ⊔ Subgroup.closure ({a, t * a * t⁻¹} : Set G)).subgroupOf X).map π ≤
      Qbar := by
    rw [Subgroup.map_le_iff_le_comap, hQbar, hMsub_eq]
    refine sup_le ?_ ?_
    · rw [hE₁]
      intro x hx
      rw [Subgroup.mem_comap]
      exact Subgroup.mem_sup_left (Subgroup.mem_inf.mp hx).2
    · rw [CFSG.subgroupOf_le_iff_le_map_subtype hclosureX]
      refine (Subgroup.closure_le
        (((Ktil ⊔ (zpowers x₁ ⊔ zpowers x₂)).comap π).map X.subtype)).mpr ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_map.mpr ⟨a₀, Subgroup.mem_comap.mpr (by rw [ha₀π]; exact hx₁Q),
          by simpa only [Subgroup.coe_subtype] using ha⟩
      · exact Subgroup.mem_map.mpr ⟨b₀, Subgroup.mem_comap.mpr (by rw [hb₀π]; exact hx₂Q),
          hb₀G⟩
  have hmapM_ge : Qbar ≤
      ((E₁ ⊔ Subgroup.closure ({a, t * a * t⁻¹} : Set G)).subgroupOf X).map π := by
    have hK : Ktil ≤
        ((E₁ ⊔ Subgroup.closure ({a, t * a * t⁻¹} : Set G)).subgroupOf X).map π := by
      rw [← hE₁subXmap]
      exact Subgroup.map_mono (by rw [hMsub_eq]; exact le_sup_left)
    rw [hQbar]
    refine sup_le hK ?_
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_map.mpr ⟨a₀, Subgroup.mem_subgroupOf.mpr (by rw [ha]; exact haM),
        ha₀π⟩
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_map.mpr ⟨b₀, Subgroup.mem_subgroupOf.mpr (by rw [hb₀G]; exact hbM),
        hb₀π⟩
  exact le_antisymm hmapM_le hmapM_ge

private theorem pairLift_M_card {X : Subgroup G}
    {π : ↥X →* (↥X ⧸ pPrimeCore 2 ↥X)}
    {M : Subgroup G} {Qbar : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    {T' : Subgroup ↥X} (hMX : M ≤ X) (hMsubT : M.subgroupOf X ≤ T')
    (hT'disj : T' ⊓ π.ker = ⊥) (hmapM : (M.subgroupOf X).map π = Qbar)
    (hQbarCard : Nat.card ↥Qbar = 16) :
    M.subgroupOf X ⊓ π.ker = ⊥ ∧ Nat.card ↥M = 16 := by
  have hMdisj : M.subgroupOf X ⊓ π.ker = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right π.ker hMsubT).trans (le_of_eq hT'disj))
  have hMcard : Nat.card ↥M = 16 := by
    have h1 : Nat.card ↥M = Nat.card ↥(M.subgroupOf X) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMX).toEquiv).symm
    have h2 : Nat.card ↥(M.subgroupOf X) = Nat.card ↥Qbar := by
      have h := CFSG.GorensteinWalter.card_map_eq_card_mul_card_ker π (M.subgroupOf X)
      rw [hMdisj, Subgroup.card_bot, mul_one, hmapM] at h
      exact h
    rw [h1, h2, hQbarCard]
  exact ⟨hMdisj, hMcard⟩



private theorem pairLift_action (hSodd : L34SuzOddSetting A t) {X : Subgroup G}
    {π : ↥X →* (↥X ⧸ pPrimeCore 2 ↥X)} {tX : ↥X} {tbar : ↥X ⧸ pPrimeCore 2 ↥X}
    {EX : Subgroup ↥X} {S Kbar : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    {L : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    (hEX : EX = (V ⊔ zpowers t).subgroupOf X)
    (hS : S = EX.map π)
    (hL : IsComponent L) (hLt : L.map (MulAut.conj tbar).toMonoidHom ≠ L)
    (hdiag : ((Kbar : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)) : Set (↥X ⧸ pPrimeCore 2 ↥X)) =
      {g | ∃ k ∈ L, k * (tbar * k * tbar⁻¹) = g})
    (hsupp : ∀ L' : Subgroup (↥X ⧸ pPrimeCore 2 ↥X), IsComponent L' →
      (⁅Kbar, L'⁆ ≠ ⊥ ↔ L' = L ∨ L' = L.map (MulAut.conj tbar).toMonoidHom))
    (hEelem : IsElemTwo (V ⊔ zpowers t))
    (hEt : V ⊔ zpowers t ≤ Subgroup.centralizer ({t} : Set G))
    (hScent : ∀ s ∈ S, ∀ k ∈ Kbar, s * k = k * s)
    (hS8 : Nat.card ↥S = 8) (htX : (tX : G) = t) (htbar : tbar = π tX) :
    L ≤ Subgroup.centralizer ((L.map (MulAut.conj tbar).toMonoidHom) : Set _) ∧
      (∀ s ∈ S, L.map (MulAut.conj s).toMonoidHom = L ∨
        L.map (MulAut.conj s).toMonoidHom = L.map (MulAut.conj tbar).toMonoidHom) ∧
      tbar ∈ S ∧ tbar * tbar = 1 ∧
      (∀ s ∈ S, L.map (MulAut.conj s).toMonoidHom = L →
        s ∈ Subgroup.centralizer (L : Set _)) ∧
      (∀ s ∈ S, L.map (MulAut.conj s).toMonoidHom =
          L.map (MulAut.conj tbar).toMonoidHom →
        L.map (MulAut.conj (s * tbar)).toMonoidHom = L) ∧
      Nat.card ↥(S ⊓ Subgroup.centralizer (L : Set _)) = 4 := by
  obtain ⟨-, hc⟩ := pairLift_Lt_facts (X := X) (tbar := tbar) hL hLt
  have hKbar_range : Kbar = (HarrisLit.swapDiag L tbar hc).range :=
    pairLift_Kbar_range (X := X) (Kbar := Kbar) (tbar := tbar) hc hdiag
  have hclass := pairLift_class (X := X) (tbar := tbar) (S := S) (Kbar := Kbar) hL hScent hsupp
  obtain ⟨htbarS, hSexp⟩ := pairLift_tbarS_exp (X := X) (π := π) (tX := tX) (tbar := tbar)
    htX htbar (EX := EX) hEX (S := S) hS hEelem
  have htbar2 : tbar * tbar = 1 :=
    pairLift_tbar2 hSodd (X := X) (π := π) (tX := tX) htX (tbar := tbar) htbar
  have hfix_centralizes := pairLift_fix_centralizes (X := X) (π := π) (tX := tX) (tbar := tbar)
    htX htbar (EX := EX) hEX (S := S) (Kbar := Kbar) hS hc hL.1.1 hEt hKbar_range hScent
  have hswap_fixes := pairLift_swap_fixes (X := X) (tbar := tbar) (S := S) hSexp (L := L)
  obtain ⟨-, -, hKtil_card⟩ := pairLift_Ktil_facts (X := X) (S := S) hS8 (L := L)
    (tbar := tbar) hLt hclass hfix_centralizes hswap_fixes htbarS
  exact ⟨hc, hclass, htbarS, htbar2, hfix_centralizes, hswap_fixes, hKtil_card⟩

omit [Finite G]
  in
private theorem pairLift_Qbar_norm {X : Subgroup G}
    {L S : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    {tbar x₁ x₂ : ↥X ⧸ pPrimeCore 2 ↥X}
    (hS : S = ((V ⊔ zpowers t).subgroupOf X).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥X)))
    (hx₂ : x₂ = MulAut.conj tbar x₁)
    (hEelem : IsElemTwo (V ⊔ zpowers t))
    (htbar2 : tbar * tbar = 1)
    (hc : L ≤ Subgroup.centralizer ((L.map (MulAut.conj tbar).toMonoidHom) : Set _))
    (hx₂Lt : x₂ ∈ L.map (MulAut.conj tbar).toMonoidHom)
    (htbarS : tbar ∈ S)
    (hx₁2 : x₁ * x₁ = 1) (hx₂2 : x₂ * x₂ = 1) (hx₁x₂comm : x₁ * x₂ = x₂ * x₁)
    (hx₁L : x₁ ∈ L) (hx₁nc : x₁ ∉ Subgroup.centralizer (L : Set _))
    (hx₂nc : x₂ ∉ Subgroup.centralizer
      ((L.map (MulAut.conj tbar).toMonoidHom) : Set _))
    (hKtil_card : Nat.card ↥(S ⊓ Subgroup.centralizer (L : Set _)) = 4)
    (hR4 : Nat.card ↥(zpowers x₁ ⊔ zpowers x₂) = 4)
    (hclass : ∀ s ∈ S, L.map (MulAut.conj s).toMonoidHom = L ∨
      L.map (MulAut.conj s).toMonoidHom = L.map (MulAut.conj tbar).toMonoidHom)
    (hfix_centralizes : ∀ s ∈ S, L.map (MulAut.conj s).toMonoidHom = L →
      s ∈ Subgroup.centralizer (L : Set _))
    (hswap_fixes : ∀ s ∈ S, L.map (MulAut.conj s).toMonoidHom =
        L.map (MulAut.conj tbar).toMonoidHom →
      L.map (MulAut.conj (s * tbar)).toMonoidHom = L) :
    let Ktil : Subgroup (↥X ⧸ pPrimeCore 2 ↥X) := S ⊓ Subgroup.centralizer (L : Set _)
    let Qbar : Subgroup (↥X ⧸ pPrimeCore 2 ↥X) := Ktil ⊔ (zpowers x₁ ⊔ zpowers x₂)
    Nat.card ↥Qbar = 16 ∧ IsPGroup 2 ↥Qbar ∧ S ≤ Subgroup.normalizer (Qbar : Set _) := by
  dsimp only
  set Ktil : Subgroup (↥X ⧸ pPrimeCore 2 ↥X) := S ⊓ Subgroup.centralizer (L : Set _)
  set Qbar : Subgroup (↥X ⧸ pPrimeCore 2 ↥X) := Ktil ⊔ (zpowers x₁ ⊔ zpowers x₂)
  obtain ⟨hScomm, hKtil_cent_tbar, hKtil_centLt, hx₂_centL⟩ :=
    pairLift_S_comm (X := X) (π := QuotientGroup.mk' (pPrimeCore 2 ↥X))
      (EX := (V ⊔ zpowers t).subgroupOf X) rfl (S := S) hS hEelem (tbar := tbar) htbar2
      (L := L) hc (x₂ := x₂) hx₂Lt htbarS
  have hRmem := pairLift_R_mem (X := X) (x₁ := x₁) (x₂ := x₂) hx₁2 hx₂2 hx₁x₂comm
  obtain ⟨hKtilRbot, hKtilRcomm⟩ := pairLift_KtilR (X := X) (S := S) (L := L) (tbar := tbar)
    (x₁ := x₁) (x₂ := x₂) hx₁L hx₂Lt hx₁nc hx₂nc hx₂2 hx₂_centL hKtil_centLt hRmem
  obtain ⟨hQbarCard, hQbar2⟩ := pairLift_Qbar (X := X) (S := S) (L := L) (x₁ := x₁) (x₂ := x₂)
    hKtil_card hR4 hKtilRcomm hKtilRbot
  have hRmap := pairLift_R_map (X := X) (tbar := tbar) htbar2 (x₁ := x₁) (x₂ := x₂) hx₂
  have hKtil_map :=
    pairLift_Ktil_map (X := X) (S := S) (L := L) (tbar := tbar) hKtil_cent_tbar
  have hKtil_le_norm := pairLift_Ktil_le_norm (X := X) (S := S) (L := L) (tbar := tbar)
    (x₁ := x₁) (x₂ := x₂) (Ktil := Ktil) (Qbar := Qbar) rfl rfl hScomm hKtil_centLt
    hx₁L hx₂Lt
  have hQmap := pairLift_Qbar_map (X := X) (Ktil := Ktil) (Qbar := Qbar) (tbar := tbar)
    (x₁ := x₁) (x₂ := x₂) rfl hKtil_map hRmap
  have htbar_norm := pairLift_htbar_norm (X := X) (Qbar := Qbar) (tbar := tbar) hQmap htbar2
  have hSQbar := pairLift_SQbar (X := X) (S := S) (Qbar := Qbar) (L := L) (tbar := tbar)
    hclass hfix_centralizes hswap_fixes htbarS htbar2 hKtil_le_norm htbar_norm
  exact ⟨hQbarCard, hQbar2, hSQbar⟩


private theorem pairLift_finish {X : Subgroup G} {u : G}
    (hX : X = centralizer ({u} : Set G))
    {tX : ↥X} (htX : (tX : G) = t)
    {L : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    {P E₁ : Subgroup G}
    {EX : Subgroup ↥X} {S Ktil Qbar : Subgroup (↥X ⧸ pPrimeCore 2 ↥X)}
    {x₁ x₂ : ↥X ⧸ pPrimeCore 2 ↥X}
    (hEX : EX = (V ⊔ zpowers t).subgroupOf X)
    (hKtil : Ktil = S ⊓ Subgroup.centralizer (L : Set _))
    (hQbar : Qbar = Ktil ⊔ (zpowers x₁ ⊔ zpowers x₂))
    (hS : S = EX.map (QuotientGroup.mk' (pPrimeCore 2 ↥X)))
    (hPpc : IsPComponent 2 (P.subgroupOf X))
    (hPmap : (P.subgroupOf X).map (QuotientGroup.mk' (pPrimeCore 2 ↥X)) = L)
    (hPX : P ≤ X) (hmap_ne : P.map (MulAut.conj t).toMonoidHom ≠ P)
    (hE₁le : E₁ ≤ V ⊔ zpowers t) (hE₁card : Nat.card E₁ = 4)
    (hE₁norm : E₁ ≤ Subgroup.normalizer (P : Set G))
    (hE₁comm : ∀ e ∈ E₁, ∀ l ∈ P, e * l * e⁻¹ * l⁻¹ ∈ oddIn P)
    (hE₁subX : E₁.subgroupOf X = EX ⊓ Ktil.comap (QuotientGroup.mk' (pPrimeCore 2 ↥X)))
    (hE₁subXmap : (E₁.subgroupOf X).map (QuotientGroup.mk' (pPrimeCore 2 ↥X)) = Ktil)
    (hE₁X : E₁ ≤ X)
    (hE₁eq : E₁ = (EX ⊓ Ktil.comap (QuotientGroup.mk' (pPrimeCore 2 ↥X))).map X.subtype)
    (hEXcard : Nat.card ↥EX = 8)
    (hπodd : Odd (Nat.card ↥(pPrimeCore 2 ↥X)))
    (hS2 : IsPGroup 2 ↥S) (hQbar2 : IsPGroup 2 ↥Qbar)
    (hSQbar : S ≤ Subgroup.normalizer (Qbar : Set _))
    (hQbarCard : Nat.card ↥Qbar = 16)
    (hx₁L : x₁ ∈ L) (hx₁2 : x₁ * x₁ = 1) (hx₁Q : x₁ ∈ Qbar)
    (htXEX : tX ∈ EX)
    (hx₁x₂comm : x₁ * x₂ = x₂ * x₁)
    (hx₂ : x₂ = MulAut.conj ((QuotientGroup.mk' (pPrimeCore 2 ↥X)) tX) x₁)
    (htX' : t ∈ X) :
    ∃ a : G, L34SuzOddPairData t u V P E₁ a ∧
      (P.subgroupOf X).map (QuotientGroup.mk' (pPrimeCore 2 ↥X)) = L := by
  obtain ⟨T', hT'2, hEXT', hTsurj⟩ :=
    pairLift_T'_exists (X := X) (EX := EX) hEXcard (S := S) (Qbar := Qbar) hS hS2 hQbar2
      hSQbar
  have hNodd : Odd (Nat.card ↥(pPrimeCore 2 ↥X)) := hπodd
  have hT'disj := pairLift_T'_disj (X := X) (T' := T') hT'2 hNodd
  obtain ⟨hTinj, hTcomm⟩ := pairLift_Tinj_comm (X := X) (T' := T') hT'2 hNodd
  obtain ⟨a, a₀, b₀, haP, ha2, ha₀T, ha, ha₀π, hb₀T, hb₀π, hb₀G⟩ :=
    pairLift_a_exists (X := X) (tX := tX)
      (tbar := (QuotientGroup.mk' (pPrimeCore 2 ↥X)) tX) htX rfl (P := P) hPpc
      (L := L) hPmap (EX := EX) (S := S) (Qbar := Qbar) (T' := T') hEXT' hTsurj hTinj
      hx₁L hx₁2 rfl hx₁Q htXEX
  have hcomm := pairLift_comm (X := X) (π := QuotientGroup.mk' (pPrimeCore 2 ↥X))
    (EX := EX) (Ktil := Ktil) (S := S) (L := L) (E₁ := E₁) hE₁eq hKtil (T' := T') hEXT'
    hTcomm (x₁ := x₁) (x₂ := x₂) hx₁L (a := a) (a₀ := a₀) (b₀ := b₀) ha ha₀T hb₀T ha₀π
    (hx₂.symm ▸ hb₀π) hx₁x₂comm hb₀G
  have hE₁subT : E₁.subgroupOf X ≤ T' := by
    rw [hE₁subX]
    exact (inf_le_left : EX ⊓ Ktil.comap _ ≤ EX).trans hEXT'
  obtain ⟨hMX, hMsub_eq, hclosureX, hMsubT⟩ :=
    pairLift_M_le (X := X) (E₁ := E₁) hE₁X (T' := T') hE₁subT (a := a) (a₀ := a₀)
      (b₀ := b₀) ha hb₀G (htX.symm ▸ htX') (hPX haP) ha₀T hb₀T
  have hmapM := pairLift_M_map (X := X) (π := QuotientGroup.mk' (pPrimeCore 2 ↥X))
    (EX := EX) (Ktil := Ktil) (Qbar := Qbar) (E₁ := E₁) hE₁subX hE₁subXmap (a := a)
    (a₀ := a₀) (b₀ := b₀) (x₁ := x₁) (x₂ := x₂) hQbar hMsub_eq hclosureX ha hb₀G ha₀π
    (hx₂.symm ▸ hb₀π) hx₁Q (hQbar.symm ▸
      (Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers x₂))))
    (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
    (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
  obtain ⟨-, hMcard⟩ := pairLift_M_card (X := X)
    (π := QuotientGroup.mk' (pPrimeCore 2 ↥X))
    (M := E₁ ⊔ Subgroup.closure ({a, t * a * t⁻¹} : Set G)) (Qbar := Qbar) (T' := T')
    hMX hMsubT hT'disj hmapM hQbarCard
  refine ⟨a, ⟨hX ▸ hPX, hX ▸ hPpc, hmap_ne, hE₁le, hE₁card, hE₁norm, hE₁comm, haP, ha2,
    hcomm.1, hcomm.2, htX ▸ hMcard⟩, hX ▸ hPmap⟩

theorem exists_l34SuzOddPairData (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y)
    {u : G} (hu : u ∈ V) (_hu1 : u ≠ 1) (ht : t ∈ centralizer ({u} : Set G))
    {L : Subgroup (↥(centralizer ({u} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({u} : Set G)))}
    (hL : IsComponent L)
    (hLt : L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({u} : Set G)))
      ⟨t, ht⟩)).toMonoidHom ≠ L)
    (hLtype : IsL34Type (↥L ⧸ center ↥L))
    (hdiag : (((K.subgroupOf (centralizer ({u} : Set G))).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({u} : Set G)))) :
        Subgroup (↥(centralizer ({u} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({u} : Set G)))) :
        Set (↥(centralizer ({u} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({u} : Set G)))) =
      {g | ∃ k ∈ L, k * (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({u} : Set G))) ⟨t, ht⟩ *
        k * (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({u} : Set G))) ⟨t, ht⟩)⁻¹) = g})
    (hsupp : ∀ L' : Subgroup (↥(centralizer ({u} : Set G)) ⧸
      pPrimeCore 2 ↥(centralizer ({u} : Set G))), IsComponent L' →
      (⁅(K.subgroupOf (centralizer ({u} : Set G))).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({u} : Set G)))), L'⁆ ≠ ⊥ ↔
        L' = L ∨ L' = L.map (MulAut.conj (QuotientGroup.mk'
          (pPrimeCore 2 ↥(centralizer ({u} : Set G))) ⟨t, ht⟩)).toMonoidHom)) :
    ∃ (P E₁ : Subgroup G) (a : G), L34SuzOddPairData t u V P E₁ a ∧
      (P.subgroupOf (centralizer ({u} : Set G))).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({u} : Set G)))) = L := by
  classical
  let X : Subgroup G := centralizer ({u} : Set G)
  let π : ↥X →* (↥X ⧸ pPrimeCore 2 ↥X) := QuotientGroup.mk' (pPrimeCore 2 ↥X)
  let tX : ↥X := ⟨t, ht⟩
  let tbar : ↥X ⧸ pPrimeCore 2 ↥X := π tX
  let EX : Subgroup ↥X := (V ⊔ zpowers t).subgroupOf X
  let S : Subgroup (↥X ⧸ pPrimeCore 2 ↥X) := EX.map π
  let Ktil : Subgroup (↥X ⧸ pPrimeCore 2 ↥X) := S ⊓ Subgroup.centralizer (L : Set _)
  obtain ⟨hEXle, hEelem, hEXcard⟩ := pairLift_E_facts hS hD hu ht
  obtain ⟨hEXdisj, hS8, hS2, hπsurj, hπodd⟩ := pairLift_S_facts (X := X) hEXcard
  obtain ⟨P, hPX, hPpc, hPmap, hPcent⟩ :=
    pairLift_P_exists (X := X) (π := π) hπsurj hπodd hL
  obtain ⟨-, hEt, hScent⟩ := pairLift_Kbar_facts hS hD (X := X) (π := π)
  obtain ⟨hc, hclass, htbarS, htbar2, hfix_centralizes, hswap_fixes, hKtil_card⟩ :=
    pairLift_action hS (X := X) (π := π) (tX := tX) (tbar := tbar) (EX := EX) (S := S)
      (Kbar := (K.subgroupOf X).map π) (L := L) rfl rfl hL hLt hdiag hsupp hEelem hEt
      hScent hS8 rfl rfl
  obtain ⟨x₁, hx₁L, hx₁2, hx₁nc⟩ :=
    exists_noncentral_involution_of_l34 hL hLtype
      (pPrimeCore_quotient_pPrimeCore_eq_bot 2)
  obtain ⟨hx₂Lt, hx₂2, hx₂ne1, hx₂nc, hx₁x₂comm, hx₁x₂ne⟩ :=
    pairLift_x2_facts (X := X) (tbar := tbar) htbar2 (L := L) hx₁L hx₁2
      (fun h => hx₁nc (h ▸ Subgroup.one_mem _)) hx₁nc hc
  let x₂ : ↥X ⧸ pPrimeCore 2 ↥X := MulAut.conj tbar x₁
  obtain ⟨-, hR4⟩ := pairLift_R_facts (X := X) (x₁ := x₁) (x₂ := x₂)
    hx₁2 hx₂2 (fun h => hx₁nc (h ▸ Subgroup.one_mem _)) hx₂ne1 hx₁x₂ne hx₁x₂comm
  obtain ⟨E₁, hE₁subX, hE₁le, hE₁card, hE₁subXmap, hE₁X, hE₁eq⟩ :=
    pairLift_E1_exists (X := X) (π := π) (EX := EX) rfl hEXle (Ktil := Ktil) hEXdisj
      (inf_le_left : Ktil ≤ EX.map π) hKtil_card
  obtain ⟨hE₁norm, hE₁comm⟩ := pairLift_E1_norm_comm (P := P) (E₁ := E₁)
    (pairLift_E1_centralizesSection (X := X) (π := π) (EX := EX) (Ktil := Ktil)
      (L := L) (E₁ := E₁) (P := P) hE₁eq hPcent (inf_le_right : Ktil ≤ _))
  have hmap_ne := pairLift_P_map_ne (X := X) (π := π) (tX := tX) (tbar := tbar) rfl rfl
    (P := P) (L := L) hPmap hLt
  obtain ⟨hQbarCard, hQbar2, hSQbar⟩ :=
    pairLift_Qbar_norm (X := X) (L := L) (S := S) (tbar := tbar) (x₁ := x₁) (x₂ := x₂)
      rfl rfl hEelem htbar2 hc hx₂Lt htbarS hx₁2 hx₂2 hx₁x₂comm hx₁L hx₁nc hx₂nc
      hKtil_card hR4 hclass hfix_centralizes hswap_fixes
  obtain ⟨a, hdata, hPmap'⟩ :=
    pairLift_finish (X := X) (u := u) rfl (tX := tX) rfl (L := L) (P := P) (E₁ := E₁)
      (EX := EX) (S := S) (Ktil := Ktil) (Qbar := Ktil ⊔ (zpowers x₁ ⊔ zpowers x₂))
      (x₁ := x₁) (x₂ := x₂) rfl rfl rfl rfl hPpc hPmap hPX hmap_ne hE₁le hE₁card hE₁norm
      hE₁comm hE₁subX hE₁subXmap hE₁X hE₁eq hEXcard
      (by simpa only [π, QuotientGroup.ker_mk'] using hπodd) hS2 hQbar2 hSQbar hQbarCard hx₁L
      hx₁2 (Subgroup.mem_sup_right (Subgroup.mem_sup_left (Subgroup.mem_zpowers x₁)))
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)))
      hx₁x₂comm rfl ht
  exact ⟨P, E₁, a, hdata, hPmap'⟩

end Certified

end CFSG.ComponentClassification.GrSLit.L34Sec5S
