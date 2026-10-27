module

public import CFSG.LocalAnalysis.ComponentClassification.GS82HConfigQuot
public import CFSG.Adapters.QiuzhenLegacy.Compat.G6.CentralizerControl
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Core
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open scoped commutatorElement

section Lift

variable {X : Type} [Group X] [Finite X]

private theorem le_normalizer_canonicalPrimeLift {K : Subgroup X}
    {Kb : Subgroup (X ⧸ pPrimeCore 2 X)}
    (hKb : IsComponent Kb) (hKmap : K.map (QuotientGroup.mk' (pPrimeCore 2 X)) = Kb)
    {C : Subgroup X} (hC : C ≤ Subgroup.centralizer (K : Set X)) :
    C ≤ Subgroup.normalizer
        (CatalogueBPrimeJoin.canonicalPrimeLift 2 Kb : Set X) ∧
      ∀ e ∈ C, QuotientGroup.mk' (pPrimeCore 2 X) e ∈
        Subgroup.centralizer (Kb : Set (X ⧸ pPrimeCore 2 X)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : X →* (X ⧸ pPrimeCore 2 X) := QuotientGroup.mk' (pPrimeCore 2 X)
  obtain ⟨hMcomp, hMmap, -, huniq⟩ :=
    (CatalogueBPrimeJoin.canonical_prime_component_lift (X := X) 2).1 Kb hKb
  have hpi_cent : ∀ e ∈ C, π e ∈
      Subgroup.centralizer (Kb : Set (X ⧸ pPrimeCore 2 X)) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp (hKmap.ge hy)
    have hek : e * k = k * e := (Subgroup.mem_centralizer_iff.mp (hC he) k hk).symm
    calc y * π e = π k * π e := by rw [hky]
      _ = π (k * e) := by rw [map_mul]
      _ = π (e * k) := by rw [← hek]
      _ = π e * π k := by rw [map_mul]
      _ = π e * y := by rw [hky]
  refine ⟨?_, hpi_cent⟩
  intro e he
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine huniq _ ?_ ?_
  · exact LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2
      (MulAut.conj e) hMcomp
  · have hcomp : π.comp (MulAut.conj e).toMonoidHom =
        (MulAut.conj (π e)).toMonoidHom.comp π := by
      ext x
      simp [MulAut.conj_apply, map_mul]
    calc ((CatalogueBPrimeJoin.canonicalPrimeLift 2 Kb).map
          (MulAut.conj e).toMonoidHom).map π
        = (CatalogueBPrimeJoin.canonicalPrimeLift 2 Kb).map
            (π.comp (MulAut.conj e).toMonoidHom) := by rw [Subgroup.map_map]
      _ = (CatalogueBPrimeJoin.canonicalPrimeLift 2 Kb).map
            ((MulAut.conj (π e)).toMonoidHom.comp π) := by rw [hcomp]
      _ = ((CatalogueBPrimeJoin.canonicalPrimeLift 2 Kb).map π).map
            (MulAut.conj (π e)).toMonoidHom := by rw [Subgroup.map_map]
      _ = Kb.map (MulAut.conj (π e)).toMonoidHom := by rw [hMmap]
      _ = Kb := Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((Subgroup.centralizer_le_normalizer (Kb : Set (X ⧸ pPrimeCore 2 X)))
          (hpi_cent e he))

private theorem canonicalPrimeLift_le_sup_and_inf {K : Subgroup X}
    {Kb : Subgroup (X ⧸ pPrimeCore 2 X)} (hKb : IsComponent Kb)
    (hKmap : K.map (QuotientGroup.mk' (pPrimeCore 2 X)) = Kb) :
    CatalogueBPrimeJoin.canonicalPrimeLift 2 Kb ≤ K ⊔ pPrimeCore 2 X ∧
      CatalogueBPrimeJoin.canonicalPrimeLift 2 Kb ⊓ pPrimeCore 2 X ≤
        (pPrimeCore 2 (CatalogueBPrimeJoin.canonicalPrimeLift 2 Kb)).map
          (CatalogueBPrimeJoin.canonicalPrimeLift 2 Kb).subtype := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMmap : (CatalogueBPrimeJoin.canonicalPrimeLift 2 Kb).map
      (QuotientGroup.mk' (pPrimeCore 2 X)) = Kb :=
    ((CatalogueBPrimeJoin.canonical_prime_component_lift (X := X) 2).1 Kb hKb).2.1
  refine ⟨?_, ?_⟩
  · intro p hp
    have hpbar : QuotientGroup.mk' (pPrimeCore 2 X) p ∈ Kb := by
      rw [← hMmap]
      exact Subgroup.mem_map_of_mem _ hp
    obtain ⟨k, hk, hkp⟩ := Subgroup.mem_map.mp (hKmap.ge hpbar)
    have hmemN : k⁻¹ * p ∈ pPrimeCore 2 X := by
      rw [← QuotientGroup.eq_one_iff]
      change QuotientGroup.mk' (pPrimeCore 2 X) (k⁻¹ * p) = 1
      rw [map_mul, map_inv, hkp, inv_mul_cancel]
    have hprod : k * (k⁻¹ * p) = p := by group
    rw [← hprod]
    exact Subgroup.mul_mem_sup hk hmemN
  · have hnorm : ((CatalogueBPrimeJoin.canonicalPrimeLift 2 Kb ⊓
        pPrimeCore 2 X).subgroupOf (CatalogueBPrimeJoin.canonicalPrimeLift 2 Kb)).Normal := by
      rw [Subgroup.inf_subgroupOf_left]
      infer_instance
    have hoddN : Odd (Nat.card (pPrimeCore 2 X)) :=
      Nat.coprime_two_left.mp pPrimeCore_coprime_card
    have hoddMN : Odd (Nat.card ↥(CatalogueBPrimeJoin.canonicalPrimeLift 2 Kb ⊓
        pPrimeCore 2 X)) :=
      hoddN.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
    exact CFSG.subgroupOf_le_pPrimeCore_map (p := 2)
      (K := CatalogueBPrimeJoin.canonicalPrimeLift 2 Kb ⊓ pPrimeCore 2 X)
      (H := CatalogueBPrimeJoin.canonicalPrimeLift 2 Kb) inf_le_left
      (Nat.coprime_two_left.mpr hoddMN)

private theorem centralizes_pPrimeCore_canonicalPrimeLift
    {Kb : Subgroup (X ⧸ pPrimeCore 2 X)} (hKb : IsComponent Kb) {C : Subgroup X}
    (hCN : C ≤ Subgroup.normalizer
      (CatalogueBPrimeJoin.canonicalPrimeLift 2 Kb : Set X))
    (hpiC : ∀ e ∈ C, QuotientGroup.mk' (pPrimeCore 2 X) e ∈
      Subgroup.centralizer (Kb : Set (X ⧸ pPrimeCore 2 X)))
    (hinf : CatalogueBPrimeJoin.canonicalPrimeLift 2 Kb ⊓ pPrimeCore 2 X ≤
      (pPrimeCore 2 (CatalogueBPrimeJoin.canonicalPrimeLift 2 Kb)).map
        (CatalogueBPrimeJoin.canonicalPrimeLift 2 Kb).subtype) :
    ∀ e ∈ C, ∀ l ∈ CatalogueBPrimeJoin.canonicalPrimeLift 2 Kb,
      e * l * e⁻¹ * l⁻¹ ∈ (pPrimeCore 2 (CatalogueBPrimeJoin.canonicalPrimeLift 2 Kb)).map
        (CatalogueBPrimeJoin.canonicalPrimeLift 2 Kb).subtype := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMmap : (CatalogueBPrimeJoin.canonicalPrimeLift 2 Kb).map
      (QuotientGroup.mk' (pPrimeCore 2 X)) = Kb :=
    ((CatalogueBPrimeJoin.canonical_prime_component_lift (X := X) 2).1 Kb hKb).2.1
  intro e he l hl
  have hcommM : e * l * e⁻¹ * l⁻¹ ∈ CatalogueBPrimeJoin.canonicalPrimeLift 2 Kb := by
    have h1 : e * l * e⁻¹ ∈ CatalogueBPrimeJoin.canonicalPrimeLift 2 Kb :=
      (Subgroup.mem_normalizer_iff.mp (hCN he) l).mp hl
    exact (CatalogueBPrimeJoin.canonicalPrimeLift 2 Kb).mul_mem h1
      ((CatalogueBPrimeJoin.canonicalPrimeLift 2 Kb).inv_mem hl)
  have hcommN : e * l * e⁻¹ * l⁻¹ ∈ pPrimeCore 2 X := by
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (pPrimeCore 2 X) (e * l * e⁻¹ * l⁻¹) = 1
    simp only [map_mul, map_inv]
    have hpi_l : QuotientGroup.mk' (pPrimeCore 2 X) l ∈ Kb := by
      rw [← hMmap]
      exact Subgroup.mem_map_of_mem _ hl
    have hcent := hpiC e he _ hpi_l
    rw [hcent.symm]
    group
  exact hinf (Subgroup.mem_inf.mpr ⟨hcommM, hcommN⟩)

end Lift

section Ambient

variable {G : Type} [Group G]

private theorem map_subtype_facts {X : Subgroup G} {M : Subgroup ↥X}
    (hM : IsPComponent 2 M) {C : Subgroup ↥X}
    (hCN : C ≤ Subgroup.normalizer (M : Set ↥X))
    (hCcen : ∀ e ∈ C, ∀ l ∈ M, e * l * e⁻¹ * l⁻¹ ∈ (pPrimeCore 2 M).map M.subtype) :
    IsPComponent 2 ((M.map X.subtype).subgroupOf X) ∧
      ((pPrimeCore 2 M).map M.subtype).map X.subtype =
        (pPrimeCore 2 (M.map X.subtype)).map (M.map X.subtype).subtype ∧
      C.map X.subtype ≤ Subgroup.normalizer (M.map X.subtype : Set G) ∧
      ∀ e ∈ C.map X.subtype, ∀ l ∈ (M.map X.subtype : Subgroup G),
        e * l * e⁻¹ * l⁻¹ ∈ (pPrimeCore 2 (M.map X.subtype)).map
          (M.map X.subtype).subtype := by
  have hX_le : M.map X.subtype ≤ X := Subgroup.map_subtype_le M
  have hsub : (M.map X.subtype).subgroupOf X = M := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.mp hx
      have hxm : x = (m : ↥X) := Subtype.ext hmx.symm
      simpa [hxm] using hm
    · intro hx
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_map_of_mem X.subtype hx
  have hpc : ((pPrimeCore 2 M).map M.subtype).map X.subtype =
      (pPrimeCore 2 (M.map X.subtype)).map (M.map X.subtype).subtype := by
    have h := CFSG.pPrimeCore_map_subgroupOf (p := 2) (M.map X.subtype) X hX_le
    rwa [hsub] at h
  refine ⟨?_, hpc, ?_, ?_⟩
  · rw [hsub]
    exact hM
  · exact (Subgroup.map_mono hCN).trans (Subgroup.le_normalizer_map X.subtype)
  · intro e he l hl
    obtain ⟨e0, he0, rfl⟩ := Subgroup.mem_map.mp he
    obtain ⟨l0, hl0, rfl⟩ := Subgroup.mem_map.mp hl
    have h := hCcen e0 he0 l0 hl0
    have hmap := Subgroup.mem_map_of_mem X.subtype h
    rw [hpc] at hmap
    simpa using hmap

end Ambient

section Component

variable {Y : Type} [Group Y] [Finite Y]

private theorem eq_of_isPComponent_of_le_sup {L P N : Subgroup Y} [N.Normal]
    (hL : IsPComponent 2 L) (hPL : P ≤ L) (hsup : L ≤ P ⊔ N)
    (hLN : L ⊓ N ≤ (pPrimeCore 2 L).map L.subtype)
    (hO : ∀ x ∈ (pPrimeCore 2 L).map L.subtype, ∀ l ∈ L, x * l = l * x) :
    L = P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A : Subgroup ↥L := P.subgroupOf L
  let B : Subgroup ↥L := pPrimeCore 2 ↥L
  have hBcenter : B ≤ Subgroup.center ↥L := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    exact (hO (z : Y) (Subgroup.mem_map_of_mem L.subtype hz) (x : Y) x.2).symm
  have hA_top : A ⊔ B = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hxPN : (x : Y) ∈ P ⊔ N := hsup x.2
    obtain ⟨k, hkP, n, hnN, hkn⟩ := Subgroup.mem_sup_of_normal_right.mp hxPN
    have hkL : k ∈ L := hPL hkP
    have hnL : n ∈ L := by
      have hn_eq : n = k⁻¹ * (x : Y) := by rw [← hkn]; group
      rw [hn_eq]
      exact L.mul_mem (L.inv_mem hkL) x.2
    have hkA : (⟨k, hkL⟩ : ↥L) ∈ A := by
      rw [Subgroup.mem_subgroupOf]
      exact hkP
    have hnO : n ∈ (pPrimeCore 2 L).map L.subtype :=
      hLN (Subgroup.mem_inf.mpr ⟨hnL, hnN⟩)
    obtain ⟨n', hn'B, hn'eq⟩ := Subgroup.mem_map.mp hnO
    have hn_eq : (⟨n, hnL⟩ : ↥L) = n' := Subtype.ext hn'eq.symm
    have hnB : (⟨n, hnL⟩ : ↥L) ∈ B := by simpa [hn_eq] using hn'B
    have hprod : (⟨k, hkL⟩ : ↥L) * ⟨n, hnL⟩ = x := Subtype.ext hkn
    rw [← hprod]
    exact Subgroup.mul_mem_sup hkA hnB
  have hLperf : Group.IsPerfect ↥L :=
    ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hL
  have hcomm_le : ⁅A ⊔ B, A ⊔ B⁆ ≤ ⁅A, A⁆ :=
    le_of_eq (CFSG.ComponentClassification.CentralExtensions.commutator_sup_central A B hBcenter)
  rw [hA_top] at hcomm_le
  have htop : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⊤ := by
    rw [← _root_.commutator_def]
    exact Group.isPerfect_def.mp hLperf
  rw [htop] at hcomm_le
  have hA_top' : A = ⊤ := by
    rw [eq_top_iff]
    exact hcomm_le.trans (commutator_le_self A)
  have hmapA : A.map L.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPL
  calc L = (⊤ : Subgroup ↥L).map L.subtype := by
        rw [Subgroup.map_top, Subgroup.range_subtype]
    _ = A.map L.subtype := by rw [← hA_top']
    _ = P := hmapA

end Component

variable {G : Type} [Group G] [Finite G]

theorem isComponent_of_isComponent_map_of_l34
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hG : L34BaseSetting G) {b : G} (hb : orderOf b = 2) {P : Subgroup G}
    (hPb : P ≤ centralizer ({b} : Set G)) (hPq : IsQuasisimple ↥P)
    (hP : IsComponent ((P.subgroupOf (centralizer ({b} : Set G))).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({b} : Set G))))))
    {F : Subgroup G} (hFP : F ≤ centralizer (P : Set G)) (hFb : F ≤ centralizer ({b} : Set G))
    (hF : Open.IsElemAbelian 2 F) (hF8 : 8 ≤ Nat.card F) (hW : wGroup F = ⊥) :
    IsComponent (P.subgroupOf (centralizer ({b} : Set G))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let X : Subgroup G := centralizer ({b} : Set G)
  let Px : Subgroup ↥X := P.subgroupOf X
  let N : Subgroup ↥X := pPrimeCore 2 ↥X
  let Pb : Subgroup (↥X ⧸ pPrimeCore 2 ↥X) :=
    Px.map (QuotientGroup.mk' (pPrimeCore 2 ↥X))
  let M : Subgroup ↥X := CatalogueBPrimeJoin.canonicalPrimeLift 2 Pb
  let Mbig : Subgroup G := M.map X.subtype
  have hPbc : IsComponent Pb := hP
  have hMcomp : IsPComponent 2 M :=
    ((CatalogueBPrimeJoin.canonical_prime_component_lift (X := ↥X) 2).1 Pb hPbc).1
  have hPx_quasi : IsQuasisimple Px :=
    (IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hPb)).mpr hPq
  have hPx_perf : Group.IsPerfect ↥Px := hPx_quasi.1
  have hPx_le_M : Px ≤ M :=
    CFSG.ComponentClassification.GSThmB.HConfig.le_canonicalPrimeLift_of_isPerfect
      (H := ↥X) Pb hPx_perf (Subgroup.map_le_iff_le_comap.mp (le_of_eq rfl))
  have hFsub : F ≤ X := hFb
  let FX : Subgroup ↥X := F.subgroupOf X
  have hFX_C : FX ≤ Subgroup.centralizer (Px : Set ↥X) := by
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hFP (Subgroup.mem_subgroupOf.mp hf)) (p : G)
      (Subgroup.mem_subgroupOf.mp hp)
  obtain ⟨hFN, hpiC⟩ :=
    le_normalizer_canonicalPrimeLift (K := Px) (C := FX) hPbc rfl hFX_C
  obtain ⟨hM_sup, hM_inf⟩ :=
    canonicalPrimeLift_le_sup_and_inf (X := ↥X) (K := Px) (Kb := Pb) hPbc rfl
  have hFX_cen :=
    centralizes_pPrimeCore_canonicalPrimeLift hPbc hFN hpiC hM_inf
  obtain ⟨hMbig_comp, hpc_eq, hFM, hFcenG⟩ :=
    map_subtype_facts (X := X) (M := M) hMcomp hFN hFX_cen
  have hmapF : FX.map X.subtype = F := Subgroup.map_subgroupOf_eq_of_le hFsub
  have hFM' : F ≤ Subgroup.normalizer (Mbig : Set G) := by
    rw [← hmapF]
    exact hFM
  have hFcenG' : ∀ e ∈ F, ∀ l ∈ Mbig,
      e * l * e⁻¹ * l⁻¹ ∈ (pPrimeCore 2 Mbig).map Mbig.subtype := by
    intro e he l hl
    have he' : e ∈ FX.map X.subtype := by rw [hmapF]; exact he
    exact hFcenG e he' l hl
  have hMbig_le_X : Mbig ≤ X := Subgroup.map_subtype_le M
  obtain ⟨hsimple, hnonab, hKproper, -⟩ := hG
  have : IsSimpleGroup G := hsimple
  have hbal : ∀ e ∈ F, e ≠ 1 →
      ⁅(pPrimeCore 2 Mbig).map Mbig.subtype ⊓ Subgroup.centralizer ({e} : Set G),
        (pLayer ↥(Mbig ⊓ Subgroup.centralizer ({e} : Set G)) 2).map
          (Mbig ⊓ Subgroup.centralizer ({e} : Set G)).subtype⁆ ≤
      (pPrimeCore 2 (Subgroup.centralizer ({e} : Set G))).map
        (Subgroup.centralizer ({e} : Set G)).subtype := by
    intro e he he1
    have hnotmem : e ∉ Subgroup.center G :=
      CFSG.ComponentClassification.GrSLit.GrS5.not_mem_center_of_ne_one hnonab he1
    have htop : Subgroup.centralizer ({e} : Set G) ≠ ⊤ :=
      CFSG.ComponentClassification.GrSLit.GrS5.centralizer_ne_top_of_not_mem_center hnotmem
    exact CFSG.ComponentClassification.GrSLit.GrS5.commutator_oddCore_pLayer_le
      hSch hU hheld hKproper hb hMbig_le_X hMbig_comp
      (Subgroup.mem_centralizer_singleton_iff.mp (hFsub he)).symm htop
  have hOcenG : ∀ x ∈ (pPrimeCore 2 Mbig).map Mbig.subtype, ∀ l ∈ Mbig, x * l = l * x :=
    oddCore_le_center_of_wGroup_eq_bot hMbig_le_X hMbig_comp hFsub
      (fun x hx y hy => hF.comm hx hy)
      (fun x hx => by rw [← pow_two]; exact hF.2 x hx)
      (by omega) hFM' hFcenG' hW hbal (Or.inr hF8)
  have hOcenX : ∀ x ∈ (pPrimeCore 2 M).map M.subtype, ∀ l ∈ M, x * l = l * x := by
    intro x hx l hl
    apply Subtype.ext
    have hxG : (x : G) ∈ (pPrimeCore 2 Mbig).map Mbig.subtype := by
      rw [← hpc_eq]
      exact Subgroup.mem_map_of_mem X.subtype hx
    have hlG : (l : G) ∈ Mbig := Subgroup.mem_map_of_mem X.subtype hl
    exact hOcenG (x : G) hxG (l : G) hlG
  have hM_eq_Px : M = Px :=
    eq_of_isPComponent_of_le_sup hMcomp hPx_le_M hM_sup hM_inf hOcenX
  have hPx_sub : Px.IsSubnormal := by
    rw [← hM_eq_Px]
    exact hMcomp.choose_spec.2.1
  exact ⟨hPx_quasi, hPx_sub⟩

end CFSG.ComponentClassification.GrSLit.L34Sec5S
