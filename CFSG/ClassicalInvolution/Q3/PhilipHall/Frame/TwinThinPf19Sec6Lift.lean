module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf19Sec6Split
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf19Sec6Yu

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups

set_option linter.unusedSectionVars false

namespace TwinThin

theorem sl2_split_dec : ∃ g : SL(2, ZMod 3), g ^ 3 = 1 ∧
    ∃ q : SL(2, ZMod 3), q ^ 4 = 1 ∧ g * q ≠ q * g := by decide +kernel

theorem mem_iff_pow_four_of_card_eight (S : Subgroup SL(2, ZMod 3)) (hS : Nat.card S = 8)
    (g : SL(2, ZMod 3)) : g ∈ S ↔ g ^ 4 = 1 := by
  classical
  have hsub : ∀ g ∈ S, g ^ 4 = 1 := by
    intro g hg
    have h1 : (⟨g, hg⟩ : S) ^ Nat.card S = 1 := pow_card_eq_one'
    rw [hS] at h1
    apply TwinSecXg.sl2_pow_eight_imp_pow_four
    simpa using congrArg Subtype.val h1
  refine ⟨hsub g, fun hg => ?_⟩
  have hle : (Set.toFinset (S : Set SL(2, ZMod 3))) ⊆
      Finset.univ.filter (fun g : SL(2, ZMod 3) => g ^ 4 = 1) := by
    intro x hx
    simp only [Set.mem_toFinset, SetLike.mem_coe] at hx
    simp [hsub x hx]
  have hcard : (Finset.univ.filter (fun g : SL(2, ZMod 3) => g ^ 4 = 1)).card ≤
      (Set.toFinset (S : Set SL(2, ZMod 3))).card := by
    rw [TwinSecXg.sl2_card_pow_four, Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact hS.ge
  have := Finset.eq_of_subset_of_card_le hle hcard
  have hg' : g ∈ Finset.univ.filter (fun g : SL(2, ZMod 3) => g ^ 4 = 1) := by simp [hg]
  rw [← this] at hg'
  simpa using hg'

section Generic

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_split_of_exact {R R' L L' : Subgroup Y} {t : Y} (hR8 : Nat.card R = 8) (hRL : R ≤ L)
    (hL : IsClassicalMember3 L t) (hLO : classicalInvolutionOddCore ↥L = ⊥) (hR'L' : R' ≤ L')
    (hcomm : ∀ x ∈ L, ∀ y ∈ L', x * y = y * x) :
    ∃ w : Y, w ∈ L ∧ w ∈ Subgroup.centralizer ({t} : Set Y) ∧ w ^ 3 = 1 ∧
      (∀ r ∈ R, w * r * w⁻¹ ∈ R) ∧ (∃ r ∈ R, w * r ≠ r * w) ∧ (∀ y ∈ R', w * y = y * w) := by
  classical
  obtain ⟨e0⟩ := hL.nonempty_equiv_sl2 hLO
  set e : ↥L ≃* SL(2, ZMod 3) := e0 with he
  obtain ⟨g₀, hg₀, q₀, hq₀, hgq⟩ := sl2_split_dec
  set RL : Subgroup ↥L := R.subgroupOf L with hRL'
  have hRLcard : Nat.card RL = 8 := by
    rw [hRL', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRL).toEquiv]
    exact hR8
  set E : Subgroup SL(2, ZMod 3) := RL.map e.toMonoidHom with hE
  have hEcard : Nat.card E = 8 := by
    rw [← Nat.card_congr (RL.equivMapOfInjective e.toMonoidHom e.injective).toEquiv]
    exact hRLcard
  have hmemE := mem_iff_pow_four_of_card_eight E hEcard
  set w₀ : ↥L := e.symm g₀ with hw₀
  have hRmem : ∀ (r : Y) (hr : r ∈ R), (⟨r, hRL hr⟩ : ↥L) ∈ RL := fun r hr =>
    Subgroup.mem_subgroupOf.mpr hr
  refine ⟨(w₀ : Y), w₀.2, ?_, ?_, ?_, ?_, ?_⟩
  · exact CFSG.RankThreeEvenClassification.Helpers.subnormal_le hL.subnormal w₀.2
  · have : w₀ ^ 3 = 1 := by
      apply e.injective
      rw [map_pow, hw₀, MulEquiv.apply_symm_apply, hg₀, map_one]
    have h2 := congrArg Subtype.val this
    simpa using h2
  · intro r hr
    have h1 : e ⟨r, hRL hr⟩ ∈ E := ⟨⟨r, hRL hr⟩, hRmem r hr, rfl⟩
    have h2 : (g₀ * e ⟨r, hRL hr⟩ * g₀⁻¹) ∈ E := by
      rw [hmemE] at h1 ⊢
      calc (g₀ * e ⟨r, hRL hr⟩ * g₀⁻¹) ^ 4 = g₀ * (e ⟨r, hRL hr⟩ ^ 4) * g₀⁻¹ := by
            rw [conj_pow]
        _ = 1 := by rw [h1]; group
    obtain ⟨a, ha, hae⟩ := h2
    have hae1 : e a = g₀ * e ⟨r, hRL hr⟩ * g₀⁻¹ := hae
    have hae' : a = w₀ * ⟨r, hRL hr⟩ * w₀⁻¹ := by
      apply e.injective
      rw [hae1, map_mul, map_mul, map_inv, hw₀, MulEquiv.apply_symm_apply]
    have := Subgroup.mem_subgroupOf.mp ha
    rw [hae'] at this
    simpa using this
  ·
    have hq₀E : q₀ ∈ E := (hmemE q₀).mpr hq₀
    obtain ⟨a, ha, haq⟩ := hq₀E
    have haq' : e a = q₀ := haq
    refine ⟨(a : Y), Subgroup.mem_subgroupOf.mp ha, fun hc => ?_⟩
    apply hgq
    have hc' : w₀ * a = a * w₀ := Subtype.ext hc
    have := congrArg e hc'
    rw [map_mul, map_mul, hw₀, MulEquiv.apply_symm_apply, haq'] at this
    exact this
  · intro y hy
    exact hcomm _ w₀.2 y (hR'L' hy)

theorem oddCore_eq_bot_of_classicalMember3 {L : Subgroup Y} {t : Y} (hL : IsClassicalMember3 L t)
    (hC : classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)) = ⊥) :
    classicalInvolutionOddCore ↥L = ⊥ := by
  have h := TwinExact.oddCoreOf_le_of_isSubnormal hL.subnormal
  have h2 : oddCoreOf (Subgroup.centralizer ({t} : Set Y)) = ⊥ := by
    unfold oddCoreOf
    rw [hC, Subgroup.map_bot]
  have h3 : oddCoreOf L = ⊥ := le_bot_iff.mp (h.trans h2.le)
  unfold oddCoreOf at h3
  exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp h3

end Generic

section Balance

variable {G : Type} [Group G] [Finite G]

theorem oddCoreOf_inf_centralizer_eq_bot {t s : G}
    (hO : classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set G)) = ⊥)
    {P : Subgroup G} (hP2 : IsPGroup 2 ↥P) (hPt : P ≤ Subgroup.centralizer ({t} : Set G))
    (hPn : ∀ c ∈ Subgroup.centralizer ({t} : Set G), ∀ p ∈ P, c * p * c⁻¹ ∈ P) (hs : s ∈ P) :
    oddCoreOf (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({s} : Set G)) = ⊥ := by
  classical
  set C : Subgroup G := Subgroup.centralizer ({t} : Set G) with hCdef
  set s' : ↥C := ⟨s, hPt hs⟩ with hs'
  set P' : Subgroup ↥C := P.subgroupOf C with hP'def
  have hP'n : P'.Normal := by
    refine ⟨fun p hp c => ?_⟩
    rw [hP'def, Subgroup.mem_subgroupOf] at hp ⊢
    exact hPn c c.2 p hp
  have hP'2 : IsPGroup 2 ↥P' := hP2.comap_of_injective C.subtype Subtype.val_injective
  have hsP' : s' ∈ P' := by
    rw [hP'def, Subgroup.mem_subgroupOf]
    exact hs
  have key := CFSG.ClassicalInvolution.Q3.TC.oddCoreImg_centralizer_eq_bot hO hP'n hP'2 hsP'
  set D : Subgroup ↥C := Subgroup.centralizer ({s'} : Set ↥C) with hD
  have hDbot : classicalInvolutionOddCore ↥D = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective).mp key
  have hE : D.map C.subtype = C ⊓ Subgroup.centralizer ({s} : Set G) :=
    TwinSecXg.map_centralizer_subtype_singleton (hPt hs)
  let e : ↥D ≃* ↥(C ⊓ Subgroup.centralizer ({s} : Set G)) :=
    (D.equivMapOfInjective C.subtype C.subtype_injective).trans (MulEquiv.subgroupCongr hE)
  have hbot := classicalInvolutionOddCore_eq_bot_of_mulEquiv e hDbot
  unfold oddCoreOf
  rw [hbot, Subgroup.map_bot]

end Balance

section Conj

variable {G : Type} [Group G] [Finite G]

theorem conjSub_eq_of_le_fin {n : G} {H : Subgroup G} (h : conjSub n H ≤ H) :
    conjSub n H = H := by
  refine Subgroup.eq_of_le_of_card_ge h ?_
  have : Nat.card ↥(conjSub n H) = Nat.card ↥H :=
    Subgroup.card_map_of_injective (f := (MulAut.conj n).toMonoidHom) (MulAut.conj n).injective
  exact this.ge

end Conj

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem zg_mem_centLayer {u : G} (hX : ∀ x ∈ piGen π, x * u = u * x) :
    g * z * g⁻¹ ∈ centLayer (CoreAssembly.conjClass K₀) u :=
  le_centLayer (S.mem_centMembers_of_pi hX S.hg) (S.hz.conj g).mem

theorem oddCore_centralizer_Yu_eq_bot
    (hodd : ∀ L ∈ CoreAssembly.conjClass K₀, ∀ t : G, IsUniqueInvolution L t →
      classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set G)) = ⊥)
    {u : G} (huO : u ∈ pCoreOf 2 (conjSub g (piGen π)))
    (hzY : g * z * g⁻¹ ∈ centLayer (CoreAssembly.conjClass K₀) u) :
    classicalInvolutionOddCore ↥(Subgroup.centralizer
      ({(⟨g * z * g⁻¹, hzY⟩ : ↥(centLayer (CoreAssembly.conjClass K₀) u))} :
        Set ↥(centLayer (CoreAssembly.conjClass K₀) u))) = ⊥ := by
  classical
  set Yu := centLayer (CoreAssembly.conjClass K₀) u with hYu
  set C₁ : Subgroup G := Yu ⊓ Subgroup.centralizer ({g * z * g⁻¹} : Set G) with hC₁
  set C₂ : Subgroup G := Subgroup.centralizer ({g * z * g⁻¹} : Set G) ⊓
    Subgroup.centralizer ({u} : Set G) with hC₂
  have hN := isNormalTwoIn_pCore S.le_cent S.normal_cent
  have hbal : oddCoreOf C₂ = ⊥ :=
    oddCoreOf_inf_centralizer_eq_bot
      (hodd _ (S.hos.graph.conjMem K S.hK g) _ (S.hz.conj g)) hN.2.1 hN.1 hN.2.2 huO
  have hYuC : Yu ≤ Subgroup.centralizer ({u} : Set G) := centLayer_le fun L hL => hL.2
  have hle : C₁ ≤ C₂ := fun x hx =>
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).2, hYuC (Subgroup.mem_inf.mp hx).1⟩
  have hnorm : (C₁.subgroupOf C₂).Normal := by
    refine ⟨fun n hn c => ?_⟩
    have hn' : (n : G) ∈ C₁ := Subgroup.mem_subgroupOf.mp hn
    obtain ⟨hnY, hnz⟩ := Subgroup.mem_inf.mp hn'
    obtain ⟨hcz, hcu⟩ := Subgroup.mem_inf.mp c.2
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · have h1 : (c : G) * n * (c : G)⁻¹ ∈ conjSub (c : G) Yu := conj_mem_conjSub hnY
      have h2 : conjSub (c : G) Yu = Yu := by
        rw [hYu, conjSub_centLayer S.hs.hyp.conjInvariant (c : G) u]
        congr 1
        rw [Subgroup.mem_centralizer_singleton_iff] at hcu
        rw [hcu, mul_inv_cancel_right]
      rw [h2] at h1
      simpa using h1
    · rw [Subgroup.mem_centralizer_singleton_iff] at hcz hnz ⊢
      have hc' : Commute (c : G) (g * z * g⁻¹) := hcz
      have hn' : Commute (n : G) (g * z * g⁻¹) := hnz
      exact ((hc'.mul_left hn').mul_left hc'.inv_left).eq
  have h1 : oddCoreOf C₁ ≤ oddCoreOf C₂ := TwinExact.oddCoreOf_le_of_normal_sub hle hnorm
  have h2 : oddCoreOf C₁ = ⊥ := le_bot_iff.mp (h1.trans hbal.le)
  have h3 : classicalInvolutionOddCore ↥C₁ = ⊥ := by
    unfold oddCoreOf at h2
    exact (Subgroup.map_eq_bot_iff_of_injective _ C₁.subtype_injective).mp h2
  have hE : (Subgroup.centralizer ({(⟨g * z * g⁻¹, hzY⟩ : ↥Yu)} : Set ↥Yu)).map Yu.subtype = C₁ :=
    TwinSecXg.map_centralizer_subtype_singleton hzY
  let e : ↥(Subgroup.centralizer ({(⟨g * z * g⁻¹, hzY⟩ : ↥Yu)} : Set ↥Yu)) ≃* ↥C₁ :=
    ((Subgroup.centralizer ({(⟨g * z * g⁻¹, hzY⟩ : ↥Yu)} : Set ↥Yu)).equivMapOfInjective
      Yu.subtype Yu.subtype_injective).trans (MulEquiv.subgroupCongr hE)
  exact classicalInvolutionOddCore_eq_bot_of_mulEquiv e.symm h3

theorem false_of_split_Yu {m : ℕ} (hm : 5 ≤ m) (hAut : TwinThinPf8.AEAut m)
    (htw : S.TwinLab m) (J : AEIdent (fam K (conjSub g (piGen π))) m) {w : G}
    (hw3 : w ^ 3 = 1) (hwz : w * (g * z * g⁻¹) = (g * z * g⁻¹) * w)
    (hwKg : conjSub w (conjSub g K) = conjSub g K)
    (hwK' : ∀ y ∈ conjSub g K', w * y = y * w)
    (hnt : ∃ r ∈ conjSub g K, w * r ≠ r * w) : False := by
  have hc : g⁻¹ * w * g ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * w * g * z = g⁻¹ * (w * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * w) * g := by rw [hwz]
      _ = z * (g⁻¹ * w * g) := by group
  have hcK : conjSub (g⁻¹ * w * g) K = K := by
    rw [conjSub_mul, conjSub_mul, hwKg, conjSub_inv_conjSub]
  have hcK' : ∀ k ∈ K', (g⁻¹ * w * g) * k = k * (g⁻¹ * w * g) := by
    intro k hk
    have hk' : g * k * g⁻¹ ∈ conjSub g K' := conj_mem_conjSub hk
    have := hwK' _ hk'
    calc g⁻¹ * w * g * k = g⁻¹ * (w * (g * k * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * k * g⁻¹) * w) * g := by rw [this]
      _ = k * (g⁻¹ * w * g) := by group
  have hc3 : ∃ k ∈ K, (g⁻¹ * w * g) * k * (g⁻¹ * w * g)⁻¹ ≠ k := by
    obtain ⟨r, hr, hwr⟩ := hnt
    refine ⟨g⁻¹ * r * g, mem_conjSub_iff.mp hr, fun hh => hwr ?_⟩
    have e : w * r * w⁻¹ = r := by
      calc w * r * w⁻¹ = g * ((g⁻¹ * w * g) * (g⁻¹ * r * g) * (g⁻¹ * w * g)⁻¹) * g⁻¹ := by group
        _ = g * (g⁻¹ * r * g) * g⁻¹ := by rw [hh]
        _ = r := by group
    calc w * r = (w * r * w⁻¹) * w := by group
      _ = r * w := by rw [e]
  exact S.no_split hm hAut htw J hc hcK hcK' hc3 ⟨1, by
    have : (g⁻¹ * w * g) ^ 3 = g⁻¹ * w ^ 3 * g := by
      have h := conj_pow (a := g⁻¹) (b := w) (i := 3)
      rwa [inv_inv] at h
    rw [pow_one, this, hw3]
    group⟩

theorem false_of_longFundSetE3 {m : ℕ} (hm : 5 ≤ m) (hAut : TwinThinPf8.AEAut m)
    (htw : S.TwinLab m) (J : AEIdent (fam K (conjSub g (piGen π))) m)
    (hodd : ∀ L ∈ CoreAssembly.conjClass K₀, ∀ t : G, IsUniqueInvolution L t →
      classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set G)) = ⊥)
    {u : G} (hu : PairInv K K' z π g u)
    (horb : ∀ L ∈ centMembers (CoreAssembly.conjClass K₀) u,
      ∃ x ∈ centLayer (CoreAssembly.conjClass K₀) u, conjSub x (conjSub g K) = L)
    (hnb : conjSub g K' ∈ π) (hzY : g * z * g⁻¹ ∈ centLayer (CoreAssembly.conjClass K₀) u)
    (h : LongFundSetE3 ((conjSub g K).subgroupOf (centLayer (CoreAssembly.conjClass K₀) u))
      (⟨g * z * g⁻¹, hzY⟩ : ↥(centLayer (CoreAssembly.conjClass K₀) u))) : False := by
  classical
  set Yu := centLayer (CoreAssembly.conjClass K₀) u with hYu
  have hX := S.pairInv_commute hu
  have hKgΩ : conjSub g K ∈ CoreAssembly.conjClass K₀ := S.hos.graph.conjMem K S.hK g
  have hKgY : conjSub g K ≤ Yu := le_centLayer (S.mem_centMembers_of_pi hX S.hg)
  have hKg'Y : conjSub g K' ≤ Yu := le_centLayer (S.mem_centMembers_of_pi hX hnb)
  set R : Subgroup ↥Yu := (conjSub g K).subgroupOf Yu with hR
  set R' : Subgroup ↥Yu := (conjSub g K').subgroupOf Yu with hR'
  have hR2 : IsPGroup 2 ↥R := (S.hs.two _ hKgΩ).comap_subtype
  have htc : tightCore R = R := tightCore_eq_self_of_isPGroup hR2
  have ht : IsUniqueInvolution R (⟨g * z * g⁻¹, hzY⟩ : ↥Yu) :=
    isUniqueInvolution_subgroupOf (S.hz.conj g) hKgY
  have ht' : IsUniqueInvolution R' (⟨g * z * g⁻¹, hzY⟩ : ↥Yu) :=
    isUniqueInvolution_subgroupOf (S.hz'.conj g) hKg'Y
  have hR'conj : R' ∈ CoreAssembly.conjClass R := by
    obtain ⟨x, hx, hxe⟩ := horb _ (S.mem_centMembers_of_pi hX hnb)
    refine ⟨⟨x, hx⟩, ?_⟩
    show conjSub (⟨x, hx⟩ : ↥Yu) R = R'
    rw [hR, conjSub_subgroupOf, hxe]
  have hRtw : R ∈ twinSet (CoreAssembly.conjClass R) R :=
    ⟨CoreAssembly.mem_conjClass_self R, _, ht, ht⟩
  have hR'tw : R' ∈ twinSet (CoreAssembly.conjClass R) R := ⟨hR'conj, _, ht, ht'⟩
  have hne : R' ≠ R := by
    refine subgroupOf_ne_of_ne hKgY hKg'Y ?_
    intro hh
    apply S.hne
    have := congrArg (conjSub g⁻¹) hh
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  obtain ⟨Λ, hΛ, hcomm, -⟩ := h
  rw [htc] at hΛ hcomm
  obtain ⟨hRΛ, hLmem⟩ := hΛ R hRtw
  obtain ⟨hR'Λ, -⟩ := hΛ R' hR'tw
  have hO' := S.oddCore_centralizer_Yu_eq_bot hodd hu.2.1 hzY
  have hLO := oddCore_eq_bot_of_classicalMember3 hLmem hO'
  have hR8 : Nat.card R = 8 := by
    rw [hR, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKgY).toEquiv]
    exact S.card8 _ hKgΩ
  obtain ⟨w, hwL, hwt, hw3, hwR, ⟨r, hr, hwr⟩, hwR'⟩ :=
    exists_split_of_exact hR8 hRΛ hLmem hLO hR'Λ (hcomm R hRtw R' hR'tw hne.symm)
  have hwz : (w : G) * (g * z * g⁻¹) = (g * z * g⁻¹) * (w : G) :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hwt)
  have hw3' : (w : G) ^ 3 = 1 := by
    have := congrArg Subtype.val hw3
    simpa using this
  have hwKg_le : conjSub (w : G) (conjSub g K) ≤ conjSub g K := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := hx
    have hk' : (⟨k, hKgY hk⟩ : ↥Yu) ∈ R := Subgroup.mem_subgroupOf.mpr hk
    have := Subgroup.mem_subgroupOf.mp (hwR _ hk')
    simpa using this
  have hwKg : conjSub (w : G) (conjSub g K) = conjSub g K := conjSub_eq_of_le_fin hwKg_le
  have hwK' : ∀ y ∈ conjSub g K', (w : G) * y = y * (w : G) := by
    intro y hy
    have hyR : (⟨y, hKg'Y hy⟩ : ↥Yu) ∈ R' := Subgroup.mem_subgroupOf.mpr hy
    have := congrArg Subtype.val (hwR' _ hyR)
    simpa using this
  have hnt : ∃ r' ∈ conjSub g K, (w : G) * r' ≠ r' * (w : G) := by
    refine ⟨(r : G), Subgroup.mem_subgroupOf.mp hr, fun hh => hwr ?_⟩
    exact Subtype.ext (by simpa using hh)
  exact S.false_of_split_Yu hm hAut htw J hw3' hwz hwKg hwK' hnt

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
