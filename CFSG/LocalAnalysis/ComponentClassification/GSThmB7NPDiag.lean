module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7NoPump
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7OS1U
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516PumpQuot
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.GH74.GLS.Stage12.McLCover
public import CFSG.GH74.Generic.Shapes
public import CFSG.GH74.Statements
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma513
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7OS1
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S3c
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S3d
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S3e
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S3f
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S3g
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S4h
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7SecL
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHypB2
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBSections
public import CFSG.LocalAnalysis.ComponentClassification.TBLitAssembly
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.OddStandard.Solomon75Inputs
public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Defs
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate8033
public import Certificates.Certificate9130

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped MatrixGroups

namespace Seven

section General

variable {X : Type} [Group X] [Finite X]

local notation "π" => QuotientGroup.mk' (pPrimeCore 2 X)

theorem le_pLayer_of_isPComponent_centralizer_pGroup (hX : LBalance.SchreierSections X)
    {P : Subgroup X} (hP : IsPGroup 2 P) {M : Subgroup X} (hMC : M ≤ centralizer (P : Set X))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer (P : Set X)))) : M ≤ pLayer X 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := LBalance.lBalancePLayer_centralizer_le hX P hP
  rw [LBalance.Asm.lBalancePLayer_top] at h1
  exact le_trans (le_sSup ((CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance 2 _ M
    hMC).mp hM)) h1

theorem isPComponent_pLayer_of_isSimpleGroup {C : Type*} [Group C] [Finite C]
    (hs : IsSimpleGroup (↥(pLayer C 2) ⧸ pPrimeCore 2 ↥(pLayer C 2))) :
    IsPComponent 2 (pLayer C 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK⟩ : ∃ K : Subgroup C, IsPComponent 2 K := by
    by_contra hno
    push Not at hno
    have hbot : pLayer C 2 = ⊥ := le_antisymm (sSup_le fun K hK => (hno K hK).elim) bot_le
    have : Subsingleton ↥(pLayer C 2) := by
      rw [hbot]
      infer_instance
    obtain ⟨u, v, huv⟩ := hs.toNontrivial.exists_pair_ne
    apply huv
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
    rw [Subsingleton.elim u v]
  have hKL : K ≤ pLayer C 2 := le_sSup hK
  obtain ⟨-, -, hKs, -⟩ := id hK
  have hsn : (K.subgroupOf (pLayer C 2)).IsSubnormal := hKs.subgroupOf
  have hsn' : ((K.subgroupOf (pLayer C 2)).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥(pLayer C 2)))).IsSubnormal :=
    hsn.map (QuotientGroup.mk'_surjective _)
  have hKp : ⁅K.subgroupOf (pLayer C 2), K.subgroupOf (pLayer C 2)⁆ =
      K.subgroupOf (pLayer C 2) := by
    have h1 : ⁅K, K⁆ = K :=
      Subgroup.isPerfect_iff.mp (CatalogueBHeldSmallCore.pComponent_perfect 2 K hK)
    apply map_injective (pLayer C 2).subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hKL, h1]
  rcases hsn'.eq_bot_or_top_of_isSimpleGroup hs with hb | ht
  · exfalso
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hb
    have h1 := Pump516.eq_bot_of_perfect_of_le_odd hKp hb OddQuot.odd_card_pPrimeCore
    have h2 : K = ⊥ := by
      rw [← map_subgroupOf_eq_of_le hKL, h1, Subgroup.map_bot]
    apply Pump516.not_le_coreActionKernel_of_isPComponent hK
    rw [h2]
    exact bot_le
  · have h1 : ((K.subgroupOf (pLayer C 2)).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥(pLayer C 2)))).comap
          (QuotientGroup.mk' (pPrimeCore 2 ↥(pLayer C 2))) =
        K.subgroupOf (pLayer C 2) ⊔ pPrimeCore 2 ↥(pLayer C 2) := by
      rw [comap_map_eq, QuotientGroup.ker_mk']
    have hle : (⊤ : Subgroup ↥(pLayer C 2)) ≤
        K.subgroupOf (pLayer C 2) ⊔ pPrimeCore 2 ↥(pLayer C 2) := by
      rw [← h1, ht, comap_top]
    have hsol : Group.IsSolvable (pPrimeCore 2 ↥(pLayer C 2)) :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ OddQuot.odd_card_pPrimeCore
    have hΛp : Group.IsPerfect ↥(pLayer C 2) := by
      have h2 := LBalance.pLayer_perfect 2 (⊤ : Subgroup C)
      rwa [LBalance.Asm.lBalancePLayer_top] at h2
    have h2 := RankThree.GroupTheory.le_of_isPerfect_of_le_sup_of_isSubnormal hsol hsn
      (Group.IsPerfect.top_iff.mpr hΛp) hle
    have hLK : pLayer C 2 ≤ K := fun x hx =>
      mem_subgroupOf.mp (h2 (mem_top (⟨x, hx⟩ : ↥(pLayer C 2))))
    rwa [le_antisymm hKL hLK] at hK

omit [Finite X] in
theorem le_sup_pPrimeCore_of_map_le {M N : Subgroup X} (h : M.map π ≤ N.map π) :
    M ≤ N ⊔ pPrimeCore 2 X := by
  rw [← QuotientGroup.ker_mk' (pPrimeCore 2 X), ← comap_map_eq]
  exact (le_comap_map π M).trans (comap_mono h)

theorem exists_pComponent_le_sup_of_map_le {L₀ : Subgroup (X ⧸ pPrimeCore 2 X)}
    (hL₀ : IsComponent L₀) {K : Subgroup X} (hKL : K.map π ≤ L₀) :
    ∃ M : Subgroup X, IsPComponent 2 M ∧ M.map π = L₀ ∧ K ≤ M ⊔ pPrimeCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hM, hMm⟩ := CatalogueBPrimeJoin.canonicalPrimeLift_isPComponent 2 L₀ hL₀
  exact ⟨_, hM, hMm, le_sup_pPrimeCore_of_map_le (hKL.trans hMm.ge)⟩

theorem exists_isComponent_le_of_inner (hX : LBalance.SchreierSections X) {P : Subgroup X}
    (hP : IsPGroup 2 P) {a b : X} (ha2 : a * a = 1) (hbZ : b ∈ center X)
    {K J JB : Subgroup X} (hKC : K ≤ centralizer (P : Set X))
    (hK : IsPComponent 2 (K.subgroupOf (centralizer (P : Set X))))
    (hJC : J ≤ centralizer ({a} : Set X))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set X))))
    (habK : a * b ∈ K) (hJBK : JB ≤ K) (hJBJ : JB ≤ J) (hJBp : ⁅JB, JB⁆ = JB)
    (hJB1 : JB ≠ ⊥) :
    ∃ L₀ : Subgroup (X ⧸ pPrimeCore 2 X), IsComponent L₀ ∧ K.map π ≤ L₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Xb := X ⧸ pPrimeCore 2 X
  have hker := OddQuot.not_two_dvd_card_ker (H := X)
  have ha : ∃ n : ℕ, a ^ 2 ^ n = 1 := ⟨1, by rw [pow_one, pow_two, ha2]⟩
  obtain ⟨hJbC, hJb⟩ := Pump516.isPComponent_map_centralizer ha hJC hJ
  have hKE : K.map π ≤ layer Xb :=
    (map_mono (le_pLayer_of_isPComponent_centralizer_pGroup hX hP hKC hK)).trans
      Pump516.map_pLayer_le_layer
  have hJE : J.map π ≤ layer Xb :=
    (map_mono (Pump516.le_pLayer_of_isPComponent_centralizer hX ha hJC hJ)).trans
      Pump516.map_pLayer_le_layer
  have hbZ' : ∀ w : Xb, w * π b = π b * w := by
    intro w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 X) w
    rw [← map_mul, ← map_mul, (mem_center_iff.mp hbZ x)]
  have hbN : ∀ L : Subgroup Xb, π b ∈ normalizer (L : Set Xb) := fun L =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun w _ => hbZ' w)
  have haN : ∀ L : Subgroup Xb, IsComponent L → π a ∈ normalizer (L : Set Xb) := by
    intro L hL
    have h1 : π (a * b) ∈ normalizer (L : Set Xb) :=
      Pump516.layer_le_normalizer hL (hKE (mem_map_of_mem π habK))
    have h2 : π a = π (a * b) * (π b)⁻¹ := by rw [map_mul, mul_inv_cancel_right]
    rw [h2]
    exact mul_mem h1 (inv_mem (hbN L))
  obtain ⟨L₀, hL₀, hJL₀⟩ := Pump516.exists_isComponent_le haN hJbC hJb hJE
  have hKb := OddQuot.isPComponent_map π hker hKC hK
  have hJBb : ¬ JB.map π ≤ (pPrimeCore 2 ↥(K.map π)).map (K.map π).subtype := by
    intro hle
    have hodd : Odd (Nat.card ↥((pPrimeCore 2 ↥(K.map π)).map (K.map π).subtype)) := by
      rw [card_map_of_injective (K.map π).subtype_injective]
      exact OddQuot.odd_card_pPrimeCore
    have h1 := Pump516.eq_bot_of_perfect_of_le_odd (by rw [← map_commutator, hJBp]) hle hodd
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h1
    exact hJB1 (Pump516.eq_bot_of_perfect_of_le_odd hJBp h1 OddQuot.odd_card_pPrimeCore)
  exact ⟨L₀, hL₀, Pump516.le_of_isPComponent_of_perfect (map_mono hKC) hKb hL₀.2
    (map_mono hJBK) ((map_mono hJBJ).trans hJL₀) (by rw [← map_commutator, hJBp]) hJBb⟩

end General

variable {X : Type} [Group X] [Finite X]

theorem Setting.isPComponent_Lay (s : Setting X) :
    IsPComponent 2 ((Lay s.h s.y).subgroupOf (centralizer (B0 s.h s.y : Set X))) := by
  set C := centralizer (B0 s.h s.y : Set X) with hC
  have hLC : (Lay s.h s.y).subgroupOf C = pLayer ↥C 2 :=
    comap_map_eq_self_of_injective C.subtype_injective _
  rw [hLC]
  apply isPComponent_pLayer_of_isSimpleGroup
  have : IsSimpleGroup (↥(Lay s.h s.y) ⧸ pPrimeCore 2 ↥(Lay s.h s.y)) :=
    isSimpleGroup_of_lieModel_psp s.hLLie
  let e : ↥(pLayer ↥C 2) ≃* ↥(Lay s.h s.y) :=
    (pLayer ↥C 2).equivMapOfInjective C.subtype C.subtype_injective
  exact (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e).isSimpleGroup

theorem Setting.exists_pComponent_le_sup (hS : SchreierFor Blueprint.Catalog)
    (hConj : CFSp4Conj) (hComp : CFSp4Comp) (hOut : CFSp4Outer) (hCent : CFL2Cent)
    [IsSimpleGroup X] (hnonab : ∃ u v : X, u * v ≠ v * u)
    (hK : Assembly.KProper Blueprint.Catalog X) (s : Setting X)
    (hNS : normalizer (s.h.S : Set X) ≤ centralizer ({s.h.a} : Set X)) {b : X}
    (hb : Lemma61Case2 s.h s.y b) :
    ∃ M : Subgroup X, M ≤ centralizer ({b} : Set X) ∧
      IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set X))) ∧
      Lay s.h s.y ≤ M ⊔ oddCoreIn (centralizer ({b} : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb0 := hb
  set d := s.toData hConj hComp hOut hCent with hd
  obtain ⟨hb1, hbx, hb3, hb4, hb5, hb6, hb7⟩ := hb
  have hb' : d.Case2 b := ⟨hb1, hbx, hb3, hb4, hb5, hb6, hb7⟩
  have hbB0 : b ∈ B0 s.h s.y := hb4
  have habL : s.h.a * b ∈ Lay s.h s.y := by
    have h1 := hb'.ab_mem_L hNS
    rwa [hd, Setting.toData_h, Setting.toData_y] at h1
  have hbb : b * b = 1 := by rw [← pow_two, ← hb1, pow_orderOf_eq_one]
  set Y := centralizer ({b} : Set X) with hYdef
  have hbne : b ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hb1
    exact absurd hb1 (by norm_num)
  have hYne : Y ≠ ⊤ := by
    intro htop
    apply hbne
    have hcen : b ∈ center X := by
      rw [mem_center_iff]
      intro w
      have hw : w ∈ Y := by
        rw [htop]
        exact mem_top w
      exact mem_centralizer_singleton_iff.mp hw
    have hbot : center X = ⊥ := by
      rcases (inferInstance : (center X).Normal).eq_bot_or_eq_top with h1 | h1
      · exact h1
      · exfalso
        obtain ⟨u, v, huv⟩ := hnonab
        exact huv ((mem_center_iff.mp (h1 ▸ mem_top v : v ∈ center X)) u)
    rw [hbot] at hcen
    exact mem_bot.mp hcen
  have hYS := schreierSections_of_isKGroupCat hS (isKGroupCat_of_ne_top' hK hYne)
  have hB0Y : B0 s.h s.y ≤ Y := fun c hc =>
    normalizer_B0_le_U hb0 (mem_inf.mpr ⟨s.B0_le_S hc, le_normalizer hc⟩)
  have hCB0Y : centralizer (B0 s.h s.y : Set X) ≤ Y :=
    centralizer_le (Set.singleton_subset_iff.mpr hbB0)
  have hLY : Lay s.h s.y ≤ Y := s.L_le_centralizer.trans hCB0Y
  have haY : s.h.a ∈ Y :=
    mem_centralizer_singleton_iff.mpr (s.h.comm_a (s.B0_le_S hbB0)).symm
  have hbY : b ∈ Y := mem_centralizer_singleton_iff.mpr rfl
  have hJq := B5a.isQuasisimple_J s.h
  have hbJ : zpowers b ≤ coreActionKernel s.h.J := (zpowers_le.mpr hbB0).trans s.B0_le_kernel
  have hb2g : IsPGroup 2 (zpowers b) :=
    Pump516.isPGroup_zpowers_of_pow ⟨1, by rw [pow_one, pow_two, hbb]⟩
  have hbCa : zpowers b ≤ centralizer ({s.h.a} : Set X) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (s.h.comm_a (s.B0_le_S hbB0)))
  obtain ⟨-, -, hJs, -, -⟩ := id s.h.isPComponent_J
  set Jb := GSLit.fixedLayer s.h.J (zpowers b) with hJbdef
  have hJb : IsPComponent 2 (Jb.subgroupOf (centralizer ({s.h.a} : Set X) ⊓ Y)) := by
    have h1 := GSLit.fixedLayer_isPComponent s.h.J_le hJs hbCa hbJ hb2g hJq
    rwa [centralizer_zpowers_eq] at h1
  have hJbC : Jb ≤ centralizer ({s.h.a} : Set X) ⊓ Y := by
    refine le_inf (((GSLit.fixedLayer_le_inf _ _).trans inf_le_left).trans s.h.J_le) ?_
    have h1 := (GSLit.fixedLayer_le_inf s.h.J (zpowers b)).trans inf_le_right
    rwa [centralizer_zpowers_eq] at h1
  have hJ0Jb : J0 s.h s.y ≤ Jb :=
    (GSLit.fixedLayer_nested hJq s.B0_le_kernel s.isPGroup_B0 (zpowers_le.mpr hbB0)).1
  have hJ0C : J0 s.h s.y ≤ centralizer ({s.h.a} : Set X) ⊓ centralizer (B0 s.h s.y : Set X) :=
    le_inf s.J0_le_centralizer_a s.J0_le_centralizer_B0
  have hJ0p : ⁅J0 s.h s.y, J0 s.h s.y⁆ = J0 s.h s.y := Subgroup.isPerfect_iff.mp
    (B5a.isPerfect_of_isPComponent_subgroupOf hJ0C s.isPComponent_J0)
  have hJ01 : J0 s.h s.y ≠ ⊥ := by
    intro hbot
    have := B5a.nontrivial_of_isPComponent_subgroupOf hJ0C s.isPComponent_J0
    rw [hbot] at this
    exact not_nontrivial _ this
  set a' : Y := ⟨s.h.a, haY⟩ with ha'
  set b' : Y := ⟨b, hbY⟩ with hb'def
  have ha2 : a' * a' = 1 := Subtype.ext s.a_mul_a
  have hbZ : b' ∈ center Y := mem_center_iff.mpr fun w => Subtype.ext
    (mem_centralizer_singleton_iff.mp w.2)
  set P : Subgroup Y := (B0 s.h s.y).subgroupOf Y with hPdef
  have hP : IsPGroup 2 P := s.isPGroup_B0.comap_subtype
  have hCP : centralizer (P : Set Y) = (centralizer (B0 s.h s.y : Set X)).subgroupOf Y :=
    B5a.centralizer_subgroupOf hB0Y
  set K : Subgroup Y := (Lay s.h s.y).subgroupOf Y with hKdef
  have hKC : K ≤ centralizer (P : Set Y) := by
    rw [hCP]
    exact fun w hw => s.L_le_centralizer hw
  have hKpc : IsPComponent 2 (K.subgroupOf (centralizer (P : Set Y))) := by
    rw [hCP]
    exact (isPComponent_subgroupOf_subgroupOf_iff' hCB0Y 2 Nat.prime_two).mpr s.isPComponent_Lay
  set J : Subgroup Y := Jb.subgroupOf Y with hJdef
  have hCaY : (centralizer ({s.h.a} : Set X) ⊓ Y).subgroupOf Y = centralizer ({a'} : Set Y) := by
    ext w
    simp only [mem_subgroupOf, mem_inf, SetLike.coe_mem, and_true,
      mem_centralizer_singleton_iff]
    exact ⟨fun h1 => Subtype.ext h1, fun h1 => congrArg Subtype.val h1⟩
  have hJC : J ≤ centralizer ({a'} : Set Y) := by
    rw [← hCaY]
    exact fun w hw => hJbC hw
  have hJpc : IsPComponent 2 (J.subgroupOf (centralizer ({a'} : Set Y))) := by
    rw [← hCaY]
    exact (isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2 Nat.prime_two).mpr hJb
  set JB : Subgroup Y := (J0 s.h s.y).subgroupOf Y with hJBdef
  have hJ0Y : J0 s.h s.y ≤ Y := s.J0_le_L.trans hLY
  have hJBK : JB ≤ K := fun w hw => s.J0_le_L hw
  have hJBJ : JB ≤ J := fun w hw => hJ0Jb hw
  have hJBp : ⁅JB, JB⁆ = JB := by
    apply map_injective Y.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hJ0Y, hJ0p]
  have hJB1 : JB ≠ ⊥ := by
    intro hbot
    apply hJ01
    have h1 : JB.map Y.subtype = J0 s.h s.y := map_subgroupOf_eq_of_le hJ0Y
    rw [← h1, hbot, Subgroup.map_bot]
  have habK : a' * b' ∈ K := habL
  obtain ⟨L₀, hL₀, hKL₀⟩ := exists_isComponent_le_of_inner hYS hP ha2 hbZ hKC hKpc hJC hJpc
    habK hJBK hJBJ hJBp hJB1
  obtain ⟨M', hM', -, hKM'⟩ := exists_pComponent_le_sup_of_map_le hL₀ hKL₀
  refine ⟨M'.map Y.subtype, map_subtype_le _, ?_, ?_⟩
  · rwa [show (M'.map Y.subtype).subgroupOf Y = M' from
      comap_map_eq_self_of_injective Y.subtype_injective M']
  · have h1 := map_mono (f := Y.subtype) hKM'
    rw [map_subgroupOf_eq_of_le hLY, Subgroup.map_sup] at h1
    exact h1

end Seven

@[expose] def QuasisimplePumpUpStatement71 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ u v : X, u * v ≠ v * u) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ h : Hyp52 X, GSMaximalUnbalancingTriple h.a h.x h.J →
      GSIsoAt h.a h.J →
      ¬ ConclusionB1 h.J → ¬ ConclusionB2a h.a h.J → h.Table517 → conjugate h.K h.a ≠ h.K →
      ∀ s : Seven.Setting X, h.IsX0Min s.y → Seven.Prop62Output h s.h s.y →
      normalizer (s.h.S : Set X) ≤ centralizer ({s.h.a} : Set X) →
      ∀ b : X, Seven.Lemma61Case2 s.h s.y b →
      ∀ M : Subgroup X, M ≤ centralizer ({b} : Set X) →
        IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set X))) →
        Seven.Lay s.h s.y ≤ M ⊔ oddCoreIn (centralizer ({b} : Set X)) →
        ¬ ((Seven.Lay s.h s.y).subgroupOf (centralizer ({b} : Set X))).IsSubnormal →
      ∀ z : X, z ∈ s.h.D → (∀ t ∈ s.h.S, t * z = z * t) → orderOf z = 2 →
      ∃ N : Subgroup X, N ≤ centralizer ({b} : Set X) ⊓ centralizer ({s.h.a * b * z} : Set X) ∧
        IsPComponent 2 (N.subgroupOf (centralizer ({b} : Set X) ⊓
          centralizer ({s.h.a * b * z} : Set X))) ∧ s.h.a * b * z ∈ N ∧
        ∃ p' n : ℕ, ∃ _ : Fact p'.Prime, p' ≠ 2 ∧ 0 < n ∧
          Nonempty (↥N ⧸ pPrimeCore 2 ↥N ≃* SL(2, GaloisField p' n))

theorem weakNoPumpStatement71_of_quasisimplePumpUp (hS : SchreierFor Blueprint.Catalog)
    (hConj : CFSp4Conj) (hComp : CFSp4Comp) (hOut : CFSp4Outer) (hCent : CFL2Cent)
    (hQ : QuasisimplePumpUpStatement71) : WeakNoPumpStatement71 := by
  intro X _ _ _ hnonab hK hz hU h hmax hiso hnB1 hnB2a hTab hKa s hy hrel hNS b hb z hzD hzS hz2
  by_cases hsub : ((Seven.Lay s.h s.y).subgroupOf (centralizer ({b} : Set X))).IsSubnormal
  · exact s.exists_sl2_inf_of_isSubnormal hConj hComp hOut hCent hNS hb hsub hzD hzS hz2
  · obtain ⟨M, hMC, hMpc, hLM⟩ :=
      s.exists_pComponent_le_sup hS hConj hComp hOut hCent hnonab hK hNS hb
    exact hQ X hnonab hK hz hU h hmax hiso hnB1 hnB2a hTab hKa s hy hrel hNS b hb M hMC hMpc hLM
      hsub z hzD hzS hz2

theorem classicalInvolutionStatement71_of_quasisimplePumpUp (hS : SchreierFor Blueprint.Catalog)
    (hConj : CFSp4Conj) (hComp : CFSp4Comp) (hOut : CFSp4Outer) (hCent : CFL2Cent)
    (hQ : QuasisimplePumpUpStatement71) : ClassicalInvolutionStatement71 :=
  classicalInvolutionStatement71_of_weakNoPump hS hConj hComp hOut hCent
    (weakNoPumpStatement71_of_quasisimplePumpUp hS hConj hComp hOut hCent hQ)

end CFSG.ComponentClassification.GSThmB
