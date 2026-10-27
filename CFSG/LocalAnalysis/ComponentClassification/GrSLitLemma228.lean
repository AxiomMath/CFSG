module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitLayerTools
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitInputs
public import CFSG.LocalAnalysis.SignalizerFunctor.Maximality

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_pLayer_inf_centralizer_sup {C L F : Subgroup G} (hLC : L ≤ C)
    (hL : IsPComponent 2 (L.subgroupOf C)) (hFC : F ≤ C) (hF : IsPGroup 2 F)
    (hFL : F ≤ normalizer (L : Set G))
    (hFcen : ∀ f ∈ F, ∀ l ∈ L, f * l * f⁻¹ * l⁻¹ ∈ (pPrimeCore 2 L).map L.subtype) :
    L ≤ (pLayer ↥(L ⊓ centralizer (F : Set G)) 2).map (L ⊓ centralizer (F : Set G)).subtype ⊔
      (pPrimeCore 2 L).map L.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set LC : Subgroup C := L.subgroupOf C with hLCdef
  set FC : Subgroup C := F.subgroupOf C with hFCdef
  set XC : Subgroup C := (pPrimeCore 2 LC).map LC.subtype with hXC
  have hFC2 : IsPGroup 2 FC := hF.comap_of_injective C.subtype C.subtype_injective
  have hXCL : XC ≤ LC := map_subtype_le _
  have hXCn : (XC.subgroupOf LC).Normal := by
    have h : XC.subgroupOf LC = pPrimeCore 2 LC :=
      comap_map_eq_self_of_injective LC.subtype_injective _
    rw [h]
    infer_instance
  have hXCodd : Odd (Nat.card XC) := odd_card_map_pPrimeCore LC
  have hFCN : FC ≤ normalizer (LC : Set C) := by
    intro f hf
    rw [mem_normalizer_iff]
    intro y
    have hfN := hFL (show (f : G) ∈ F from hf)
    rw [hLCdef, mem_subgroupOf, mem_subgroupOf]
    simpa using mem_normalizer_iff.mp hfN (y : G)
  have hFCX : FC ≤ normalizer (XC : Set C) := fun f hf => by
    have := pPrimeCore_characteristic (p := 2) (G := LC)
    refine mem_normalizer_iff.mpr fun x => ⟨fun hx => CFSG.Walter.conj_mem_map_of_characteristic
      (hFCN hf) hx, fun hx => ?_⟩
    have h := CFSG.Walter.conj_mem_map_of_characteristic (inv_mem (hFCN hf)) hx
    rwa [show f⁻¹ * (f * x * f⁻¹) * f⁻¹⁻¹ = x by group] at h
  have hcommC : ⁅LC, FC⁆ ≤ XC := by
    rw [commutator_le]
    intro l hl f hf
    rw [← inv_mem_iff]
    have h := hFcen (f : G) hf (l : G) hl
    obtain ⟨x, hx, hxe⟩ := h
    have hxL : (x : G) ∈ L := x.2
    refine ⟨⟨⟨(x : G), hLC hxL⟩, hxL⟩, ?_, ?_⟩
    · have h1 : (⟨⟨(x : G), hLC hxL⟩, hxL⟩ : LC) = (subgroupOfEquivOfLe hLC).symm x := rfl
      rw [h1]
      have h2 := (pPrimeCore_map_iso 2 (subgroupOfEquivOfLe hLC).symm).le ⟨x, hx, rfl⟩
      exact h2
    · apply Subtype.ext
      simp only [coe_subtype, commutatorElement_def, coe_mul, coe_inv, mul_inv_rev, inv_inv]
      rw [show (x : G) = f * l * f⁻¹ * l⁻¹ from hxe]
      simp only [mul_assoc]
      rfl
  have hcov := ClassicalInvolution.LBalanceProof.exists_centralizer_mul_of_commutator_le
    LC FC XC hFC2 hXCL hXCn hXCodd hFCX hcommC
  have hcomp : IsPComponent 2 LC := hL
  have hle := le_pLayer_sup_of_cover hcomp (inf_le_left : LC ⊓ centralizer (FC : Set C) ≤ LC)
    (fun l hl => by
      obtain ⟨c, hc, m, hm, rfl⟩ := hcov l hl
      obtain ⟨m', hm', rfl⟩ := hm
      exact ⟨c, hc, m', ⟨m', hm', rfl⟩, rfl⟩)
  set R : Subgroup C := LC ⊓ centralizer (FC : Set C) with hR
  have hRmap : R.map C.subtype = L ⊓ centralizer (F : Set G) := by
    ext x
    constructor
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨hr1, hr2⟩ := mem_inf.mp hr
      refine mem_inf.mpr ⟨hr1, mem_centralizer_iff.mpr fun f hf => ?_⟩
      exact congrArg Subtype.val (mem_centralizer_iff.mp hr2 ⟨f, hFC hf⟩ hf)
    · intro hx
      obtain ⟨hxL, hxC⟩ := mem_inf.mp hx
      refine ⟨⟨x, hLC hxL⟩, mem_inf.mpr ⟨hxL, mem_centralizer_iff.mpr fun f hf => ?_⟩, rfl⟩
      exact Subtype.ext (mem_centralizer_iff.mp hxC (f : G) hf)
  let eR : ↥R ≃* ↥(L ⊓ centralizer (F : Set G)) :=
    (R.equivMapOfInjective C.subtype C.subtype_injective).trans (MulEquiv.subgroupCongr hRmap)
  have hlayer := UnbalancedGS.FixedLayerPComponent.map_pLayer_mulEquiv 2 eR
  have hkey1 : ((pLayer ↥R 2).map R.subtype).map C.subtype =
      (pLayer ↥(L ⊓ centralizer (F : Set G)) 2).map (L ⊓ centralizer (F : Set G)).subtype := by
    rw [← hlayer, map_map, map_map]
    congr 1
  have hkey2 : XC.map C.subtype = (pPrimeCore 2 L).map L.subtype := by
    rw [hXC, map_map, ← pPrimeCore_map_iso 2 (subgroupOfEquivOfLe hLC), map_map]
    congr 1
  intro x hx
  have hxC : (⟨x, hLC hx⟩ : C) ∈ LC := hx
  have h1 := hle hxC
  have h2 := mem_map_of_mem C.subtype h1
  rw [Subgroup.map_sup, hkey1, hkey2] at h2
  exact h2

theorem pLayer_eq_self_of_isPComponent {C L : Subgroup G} (hLC : L ≤ C)
    (hL : IsPComponent 2 (L.subgroupOf C)) : (pLayer ↥L 2).map L.subtype = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hgen, hq⟩ :=
    (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 _).mp hL
  let e : ↥(L.subgroupOf C) ≃* ↥(⊤ : Subgroup ↥L) :=
    (subgroupOfEquivOfLe hLC).trans Subgroup.topEquiv.symm
  have htop : IsPComponent 2 (⊤ : Subgroup ↥L) :=
    (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 _).mpr
      ⟨Subgroup.IsSubnormal.top, CatalogueBPrimeJoin.primeResidual_eq_top_of_equiv 2 e hgen,
        CatalogueBPrimeJoin.quasisimple_primeCore_quotient_of_equiv 2 e hq⟩
  have hle : (⊤ : Subgroup ↥L) ≤ pLayer ↥L 2 := le_sSup htop
  rw [top_le_iff.mp hle, ← MonoidHom.range_eq_map, range_subtype]

omit [Finite G] in
theorem commutator_mem_oddCore_of_mem_fusionZStar {L : Subgroup G} (hL : Group.IsPerfect L)
    {e : G} (he : e ∈ normalizer (L : Set G))
    (hcen : ∀ l ∈ L, e * l * e⁻¹ * l⁻¹ ∈ (Open.fusionZStar L).map L.subtype) :
    ∀ l ∈ L, e * l * e⁻¹ * l⁻¹ ∈ (pPrimeCore 2 L).map L.subtype := by
  set N := Open.fusionOddCore ↥L with hN
  set π := QuotientGroup.mk' N with hπ
  have hconj : ∀ l : L, e * (l : G) * e⁻¹ ∈ L := fun l => (mem_normalizer_iff.mp he l).mp l.2
  let c : L → L := fun l => ⟨e * l * e⁻¹, hconj l⟩
  have hc : ∀ a b : L, c (a * b) = c a * c b := fun a b => Subtype.ext (by
    simp only [c, coe_mul]
    group)
  have hz : ∀ l : L, π (l⁻¹ * c l) ∈ center (L ⧸ N) := by
    intro l
    obtain ⟨y, hy, hye⟩ := hcen l l.2
    have h1 : l⁻¹ * c l = l⁻¹ * y * l⁻¹⁻¹ := Subtype.ext (by
      simp only [c, coe_mul, coe_inv, inv_inv]
      rw [show (y : G) = e * l * e⁻¹ * (l : G)⁻¹ from hye]
      group)
    rw [h1]
    exact (Open.fusionZStar_normal ↥L).conj_mem y hy l⁻¹
  let f : ↥L →* center (↥L ⧸ N) :=
    { toFun := fun l => ⟨π (l⁻¹ * c l), hz l⟩
      map_one' := Subtype.ext (by
        change π (1⁻¹ * c 1) = 1
        have : c 1 = 1 := Subtype.ext (by simp [c])
        rw [this, inv_one, one_mul, map_one])
      map_mul' := fun a b => Subtype.ext (by
        change π ((a * b)⁻¹ * c (a * b)) = π (a⁻¹ * c a) * π (b⁻¹ * c b)
        have h2 := mem_center_iff.mp (hz a) (π b⁻¹)
        rw [hc]
        calc π ((a * b)⁻¹ * (c a * c b)) = π b⁻¹ * π (a⁻¹ * c a) * π (c b) := by
              simp only [map_mul, map_inv, mul_inv_rev]
              group
          _ = π (a⁻¹ * c a) * π b⁻¹ * π (c b) := by rw [h2]
          _ = π (a⁻¹ * c a) * π (b⁻¹ * c b) := by
              simp only [map_mul, map_inv]
              group) }
  have hf : commutator ↥L ≤ f.ker := Abelianization.commutator_subset_ker f
  rw [Group.isPerfect_def.mp hL] at hf
  intro l hl
  have h3 := hf (mem_top (⟨l, hl⟩ : L))
  rw [MonoidHom.mem_ker] at h3
  have h4 : π ((⟨l, hl⟩ : L)⁻¹ * c ⟨l, hl⟩) = 1 := congrArg Subtype.val h3
  have h4' : (⟨l, hl⟩ : L)⁻¹ * c ⟨l, hl⟩ ∈ N := (QuotientGroup.eq_one_iff _).mp h4
  rw [hN, UnbalancingLocal.fusionOddCore_eq_pPrimeCore] at h4'
  have h5 := (inferInstance : (pPrimeCore 2 ↥L).Normal).conj_mem _ h4' ⟨l, hl⟩
  refine ⟨_, h5, ?_⟩
  simp only [c, coe_subtype, coe_mul, coe_inv]
  group

theorem oddCore_le_center_of_wGroup_eq_bot {t : G} {L E : Subgroup G}
    (hLt : L ≤ centralizer ({t} : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set G))))
    (hEt : E ≤ centralizer ({t} : Set G)) (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hE2 : ∀ x ∈ E, x * x = 1) (hE4 : 4 ≤ Nat.card E)
    (hEL : E ≤ normalizer (L : Set G))
    (hEcen : ∀ e ∈ E, ∀ l ∈ L, e * l * e⁻¹ * l⁻¹ ∈ (pPrimeCore 2 L).map L.subtype)
    (hW : wGroup E = ⊥)
    (hbal : ∀ e ∈ E, e ≠ 1 →
      ⁅(pPrimeCore 2 L).map L.subtype ⊓ centralizer ({e} : Set G),
        (pLayer ↥(L ⊓ centralizer ({e} : Set G)) 2).map
          (L ⊓ centralizer ({e} : Set G)).subtype⁆ ≤
      (pPrimeCore 2 (centralizer ({e} : Set G))).map (centralizer ({e} : Set G)).subtype)
    (hcase : E ≤ centralizer (L : Set G) ∨ 8 ≤ Nat.card E) :
    ∀ x ∈ (pPrimeCore 2 L).map L.subtype, ∀ l ∈ L, x * l = l * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := (pPrimeCore 2 L).map L.subtype with hXdef
  have hXL : X ≤ L := map_subtype_le _
  have hpg : ∀ F : Subgroup G, F ≤ E → IsPGroup 2 F := by
    intro F hFE f
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, coe_pow, OneMemClass.coe_one]
    rw [pow_two]
    exact hE2 f (hFE f.2)
  have hlay : ∀ F : Subgroup G, F ≤ E → ∀ e ∈ F,
      (pLayer ↥(L ⊓ centralizer (F : Set G)) 2).map (L ⊓ centralizer (F : Set G)).subtype ≤
        (pLayer ↥(L ⊓ centralizer ({e} : Set G)) 2).map
          (L ⊓ centralizer ({e} : Set G)).subtype := by
    intro F hFE e heF
    have hFe : F ≤ centralizer ({e} : Set G) := fun f hf =>
      mem_centralizer_singleton_iff.mpr (hEab f (hFE hf) e (hFE heF))
    have hFN : F ≤ normalizer ((L ⊓ centralizer ({e} : Set G) : Subgroup G) : Set G) := by
      intro f hf
      have hfL := hEL (hFE hf)
      have hfe : Commute f e := mem_centralizer_singleton_iff.mp (hFe hf)
      refine mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩
      · obtain ⟨hyL, hyC⟩ := mem_inf.mp hy
        have hye : Commute y e := mem_centralizer_singleton_iff.mp hyC
        exact mem_inf.mpr ⟨(mem_normalizer_iff.mp hfL y).mp hyL,
          mem_centralizer_singleton_iff.mpr ((hfe.mul_left hye).mul_left hfe.inv_left).eq⟩
      · obtain ⟨hyL, hyC⟩ := mem_inf.mp hy
        have hye : Commute (f * y * f⁻¹) e := mem_centralizer_singleton_iff.mp hyC
        have hy' : y = f⁻¹ * (f * y * f⁻¹) * f := by group
        refine mem_inf.mpr ⟨(mem_normalizer_iff.mp hfL y).mpr hyL, ?_⟩
        rw [hy', mem_centralizer_singleton_iff]
        exact ((hfe.inv_left.mul_left hye).mul_left hfe).eq
    have h := pLayer_inf_centralizer_le_of_normalizes (hpg F hFE) hFN
    have heq : L ⊓ centralizer ({e} : Set G) ⊓ centralizer (F : Set G) =
        L ⊓ centralizer (F : Set G) := by
      rw [inf_assoc]
      congr 1
      exact inf_eq_right.mpr (centralizer_le (by
        intro x hx
        rw [Set.mem_singleton_iff.mp hx]
        exact heF))
    rwa [heq] at h
  have hkey : ∀ F : Subgroup G, F ≤ E → 4 ≤ Nat.card F → ∀ M : Subgroup G,
      (∀ e ∈ F, e ≠ 1 → M ≤ (pLayer ↥(L ⊓ centralizer ({e} : Set G)) 2).map
        (L ⊓ centralizer ({e} : Set G)).subtype) →
      ⁅X ⊓ centralizer (F : Set G), M⁆ = ⊥ := by
    intro F hFE hF4 M hM
    rw [eq_bot_iff, ← hW]
    refine le_trans ?_ (le_iSup_of_le F (le_iSup_of_le hFE (le_iSup_of_le hF4
      (le_iSup_of_le (fun b hb => hE2 b (hFE hb)) le_rfl))))
    refine le_iInf fun e => le_iInf fun he => le_iInf fun he1 => ?_
    refine le_trans (Subgroup.commutator_mono ?_ (hM e he he1)) (hbal e (hFE he) he1)
    exact inf_le_inf_left _ (centralizer_le (by
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      exact he))
  rcases hcase with hEC | hE8
  ·
    have hLE : L ⊓ centralizer (E : Set G) = L := inf_eq_left.mpr (le_centralizer_iff.mp hEC)
    have hXE : X ⊓ centralizer (E : Set G) = X :=
      inf_eq_left.mpr (hXL.trans (le_centralizer_iff.mp hEC))
    have hLay : (pLayer ↥(L ⊓ centralizer (E : Set G)) 2).map
        (L ⊓ centralizer (E : Set G)).subtype = L := by
      rw [hLE]
      exact pLayer_eq_self_of_isPComponent hLt hL
    have h := hkey E le_rfl hE4 L (fun e he _ => (le_of_eq hLay.symm).trans (hlay E le_rfl e he))
    rw [hXE] at h
    intro x hx l hl
    have hc := commutator_mem_commutator hx hl
    rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc
  ·
    set LE := (pLayer ↥(L ⊓ centralizer (E : Set G)) 2).map
      (L ⊓ centralizer (E : Set G)).subtype with hLEdef
    have hF : ∀ F ∈ Open.signalizerFunctorEk 2 2 E, ⁅X ⊓ centralizer (F : Set G), LE⁆ = ⊥ := by
      rintro F ⟨hFE, hF4⟩
      exact hkey F hFE (by rw [hF4]; norm_num) LE fun e he he1 => hlay E le_rfl e (hFE he)
    have hEel : Open.IsElemAbelian 2 E := by
      refine ⟨⟨⟨fun x y => Subtype.ext (hEab x x.2 y y.2)⟩⟩, fun x hx => ?_⟩
      rw [pow_two]
      exact hE2 x hx
    have hEX : E ≤ normalizer (X : Set G) := fun e he => by
      have := pPrimeCore_characteristic (p := 2) (G := L)
      exact mem_normalizer_iff.mpr fun x => ⟨fun hx => CFSG.Walter.conj_mem_map_of_characteristic
        (hEL he) hx, fun hx => by
          have h := CFSG.Walter.conj_mem_map_of_characteristic (inv_mem (hEL he)) hx
          rwa [show e⁻¹ * (e * x * e⁻¹) * e⁻¹⁻¹ = x by group] at h⟩
    have hXcop : Nat.Coprime 2 (Nat.card X) :=
      Nat.coprime_two_left.mpr (odd_card_map_pPrimeCore L)
    have hgen := SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
      Nat.prime_two E X hEel (by simpa using hE8) hEX hXcop
    have hLEX : LE ≤ centralizer (X : Set G) := by
      intro y hy
      rw [mem_centralizer_iff]
      intro x hx
      have hxle : X ≤ centralizer ({y} : Set G) := by
        rw [← hgen]
        refine iSup₂_le fun F hFm => ?_
        intro z hz
        have hc := commutator_mem_commutator hz hy
        rw [hF F hFm, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
        exact mem_centralizer_singleton_iff.mpr hc
      exact mem_centralizer_singleton_iff.mp (hxle hx)
    have hcov := le_pLayer_inf_centralizer_sup hLt hL hEt (hpg E le_rfl) hEL hEcen
    set CL : Subgroup L := (centralizer (X : Set G)).subgroupOf L with hCL
    have hCLn : CL.Normal := by
      constructor
      intro c hc g
      rw [hCL, mem_subgroupOf, mem_centralizer_iff] at hc ⊢
      intro x hx
      have hx' : (g : G)⁻¹ * x * (g : G) ∈ X := by
        have := pPrimeCore_characteristic (p := 2) (G := L)
        have h := CFSG.Walter.conj_mem_map_of_characteristic (inv_mem (le_normalizer g.2)) hx
        rwa [inv_inv] at h
      have h1 := hc _ hx'
      simp only [coe_mul, coe_inv]
      calc x * ((g : G) * c * (g : G)⁻¹) =
          (g : G) * (((g : G)⁻¹ * x * (g : G)) * c) * (g : G)⁻¹ := by group
        _ = (g : G) * (c * ((g : G)⁻¹ * x * (g : G))) * (g : G)⁻¹ := by rw [h1]
        _ = (g : G) * c * (g : G)⁻¹ * x := by group
    set XL : Subgroup L := X.subgroupOf L with hXLdef
    have hXLsolv : Group.IsSolvable XL := by
      have hodd : Odd (Nat.card XL) := by
        rw [Nat.card_congr (subgroupOfEquivOfLe hXL).toEquiv]
        exact odd_card_map_pPrimeCore L
      exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    have hLperf : Group.IsPerfect (⊤ : Subgroup L) := by
      have h := ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hL
      exact Group.IsPerfect.ofSurjective
        (f := ((subgroupOfEquivOfLe hLt).trans Subgroup.topEquiv.symm).toMonoidHom)
        ((subgroupOfEquivOfLe hLt).trans Subgroup.topEquiv.symm).surjective
    have htop : (⊤ : Subgroup L) ≤ CL ⊔ XL := by
      intro l _
      have hl : (l : G) ∈ X ⊔ LE := by
        rw [sup_comm]
        exact hcov l.2
      have hLEN : LE ≤ normalizer (X : Set G) := fun a ha => by
        obtain ⟨a', -, rfl⟩ := ha
        have haL : (a' : G) ∈ L := (mem_inf.mp a'.2).1
        have := pPrimeCore_characteristic (p := 2) (G := L)
        exact mem_normalizer_iff.mpr fun x => ⟨fun hx =>
          CFSG.Walter.conj_mem_map_of_characteristic (le_normalizer haL) hx, fun hx => by
            have h := CFSG.Walter.conj_mem_map_of_characteristic (inv_mem (le_normalizer haL)) hx
            rwa [coe_subtype, show (a' : G)⁻¹ * ((a' : G) * x * (a' : G)⁻¹) * (a' : G)⁻¹⁻¹ = x
              by group] at h⟩
      obtain ⟨b, hb, a, ha, hba⟩ := exists_mul_of_mem_sup_of_le_normalizer hLEN hl
      have haL : a ∈ L := by
        obtain ⟨a', -, rfl⟩ := ha
        exact (mem_inf.mp a'.2).1
      have hbL : b ∈ L := hXL hb
      have hla : l = ⟨b, hbL⟩ * ⟨a, haL⟩ := Subtype.ext hba.symm
      rw [hla]
      exact mul_mem (mem_sup_right (show (⟨b, hbL⟩ : L) ∈ XL from hb))
        (mem_sup_left (show (⟨a, haL⟩ : L) ∈ CL from hLEX ha))
    have hLC := ClassicalInvolution.LBalanceProof.perfect_le_of_le_sup_solvable
      (⊤ : Subgroup L) CL XL htop
    intro x hx l hl
    have h1 : (⟨l, hl⟩ : L) ∈ CL := hLC (mem_top _)
    rw [hCL, mem_subgroupOf, mem_centralizer_iff] at h1
    exact h1 x hx

theorem oddCore_le_center_of_wGroup_eq_bot_of_fusionZStar {t : G} {L E : Subgroup G}
    (hLt : L ≤ centralizer ({t} : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set G))))
    (hEt : E ≤ centralizer ({t} : Set G)) (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hE2 : ∀ x ∈ E, x * x = 1) (hE4 : 4 ≤ Nat.card E)
    (hEL : E ≤ normalizer (L : Set G))
    (hEcen : ∀ e ∈ E, ∀ l ∈ L, e * l * e⁻¹ * l⁻¹ ∈ (Open.fusionZStar L).map L.subtype)
    (hW : wGroup E = ⊥)
    (hbal : ∀ e ∈ E, e ≠ 1 →
      ⁅(pPrimeCore 2 L).map L.subtype ⊓ centralizer ({e} : Set G),
        (pLayer ↥(L ⊓ centralizer ({e} : Set G)) 2).map
          (L ⊓ centralizer ({e} : Set G)).subtype⁆ ≤
      (pPrimeCore 2 (centralizer ({e} : Set G))).map (centralizer ({e} : Set G)).subtype)
    (hcase : E ≤ centralizer (L : Set G) ∨ 8 ≤ Nat.card E) :
    ∀ x ∈ (pPrimeCore 2 L).map L.subtype, ∀ l ∈ L, x * l = l * x := by
  have hperf : Group.IsPerfect L := by
    have h := ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hL
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hLt).toMonoidHom)
      (subgroupOfEquivOfLe hLt).surjective
  exact oddCore_le_center_of_wGroup_eq_bot hLt hL hEt hEab hE2 hE4 hEL
    (fun e he => commutator_mem_oddCore_of_mem_fusionZStar hperf (hEL he) (hEcen e he)) hW hbal
    hcase

end CFSG.ComponentClassification.GrSLit
