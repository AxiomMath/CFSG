module

public import CFSG.GH74.GLS.LU.Local.KStepY
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Final19A
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseOneComponent
public import CFSG.GH74.GLS.IVK.Statements.Sec9
public import CFSG.GH74.GLS.LU.Local.Core2
public import CFSG.GH74.GLS.LU.Local.L3Facts
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Cited

public section

namespace CFSG.GH74.GLS.LU.Local

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.ComponentClassification
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank
open scoped commutatorElement MatrixGroups

variable {Y : Type} [Group Y] [Finite Y] {s : Y} {K : Subgroup Y}

theorem KComp.layer_le (h : KComp Y s K) :
    CFSG.layer ↥(centralizer ({barMk Y s} : Set (barQ Y))) ≤
      (K.map (barMk Y)).subgroupOf (centralizer ({barMk Y s} : Set (barQ Y))) := by
  set C := centralizer ({s} : Set Y) with hC
  set Cb := centralizer ({barMk Y s} : Set (barQ Y)) with hCb
  have hφs := barMkCentralizer_surjective h.ord
  have hφo := odd_card_ker_barMkCentralizer h.ord
  have h1 : CFSG.layer ↥Cb ≤ CFSG.pLayer ↥Cb 2 :=
    CFSG.GH74.GLS.Stage2.Final.Thm4.layer_le_pLayer
  rw [CFSG.ComponentClassification.LocalBFailure.pLayer_two_eq_twoLayer] at h1
  rw [← TwoLayerTransport.image_of_odd_kernel _ hφs hφo] at h1
  refine h1.trans ?_
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun Λ' hΛ' => ?_
  have hΛC : Λ'.map C.subtype ≤ C := Subgroup.map_subtype_le _
  have hsub : (Λ'.map C.subtype).subgroupOf C = Λ' :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective Λ'
  have hΛ'' : TwoComponents.IsTwoComponent ((Λ'.map C.subtype).subgroupOf C) := by
    rw [hsub]; exact hΛ'
  have heq := h.only _ hΛC hΛ''
  have : Λ' = K.subgroupOf C := by rw [← hsub, heq]
  rw [this]
  intro x hx
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, barMkCentralizer_apply h.ord]
  exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mp hx)

variable {Y : Type} [Group Y] [Finite Y] {s : Y} {K : Subgroup Y}

@[expose] noncomputable def KComp.equivMap (h : KComp Y s K) : ↥K ≃* ↥(K.map (barMk Y)) := by
  let f : ↥K →* barQ Y := (barMk Y).comp K.subtype
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : (a : Y) ∈ pPrimeCore 2 Y := by
      rw [← ker_barMk, MonoidHom.mem_ker]; exact ha
    have h2 : (a : Y) ∈ K ⊓ pPrimeCore 2 Y := ⟨a.2, h1⟩
    rw [h.inf_bot, mem_bot] at h2
    exact Subtype.ext h2
  have hrange : f.range = K.map (barMk Y) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨a, a.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩; exact ⟨⟨a, ha⟩, rfl⟩
  exact (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)

theorem KComp.equivMap_apply (h : KComp Y s K) (a : ↥K) :
    ((h.equivMap a : ↥(K.map (barMk Y))) : barQ Y) = barMk Y (a : Y) := rfl

theorem KComp.isQuasisimple_map (h : KComp Y s K) : IsQuasisimple (K.map (barMk Y)) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv h.equivMap h.quasi


theorem KComp.map_conj_mem (h : KComp Y s K) {c : barQ Y}
    (hc : c ∈ centralizer ({barMk Y s} : Set (barQ Y))) {x : barQ Y} (hx : x ∈ K.map (barMk Y)) :
    c * x * c⁻¹ ∈ K.map (barMk Y) := by
  rw [← map_centralizer_barMk h.ord] at hc
  obtain ⟨y, hy, rfl⟩ := hc
  obtain ⟨k, hk, rfl⟩ := hx
  refine ⟨y * k * y⁻¹, h.norm y hy k hk, ?_⟩
  simp

omit [Finite Y] in
theorem not_le_centralizer_self_of_native {G : Type*} [Group G] {L : Subgroup G}
    (hL : CFSG.IsQuasisimple L) : ¬ L ≤ centralizer (L : Set G) :=
  not_le_centralizer_self_of_isQuasisimple ((AssemblyBPredicates.isQuasisimple_iff_native L).2 hL)

theorem KComp.mem_normalizer (h : KComp Y s K) {L : Subgroup (barQ Y)} (hL : CFSG.IsComponent L)
    (hKL : K.map (barMk Y) ≤ L) {c : barQ Y}
    (hc : c ∈ centralizer ({barMk Y s} : Set (barQ Y))) :
    c ∈ Subgroup.normalizer (L : Set (barQ Y)) := by
  have hL' : CFSG.IsComponent (conjSub c L) := isComponent_conjSub hL c
  have hKL' : K.map (barMk Y) ≤ conjSub c L := by
    intro x hx
    have hc' : c⁻¹ ∈ centralizer ({barMk Y s} : Set (barQ Y)) := inv_mem hc
    have h1 := hKL (h.map_conj_mem hc' hx)
    exact ⟨c⁻¹ * x * c, by simpa using h1, by
      show c * (c⁻¹ * x * c) * c⁻¹ = x
      group⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  have hcomm : ⁅conjSub c L, L⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hL' hL).resolve_left hne
  have hle : K.map (barMk Y) ≤ centralizer ((K.map (barMk Y) : Subgroup (barQ Y)) : Set (barQ Y)) := by
    have h1 : L ≤ centralizer ((conjSub c L : Subgroup (barQ Y)) : Set (barQ Y)) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]; exact hcomm
    exact (hKL.trans h1).trans (Subgroup.centralizer_le hKL')
  exact not_le_centralizer_self_of_native h.isQuasisimple_map hle


theorem KComp.Ez_eq (h : KComp Y s K) {L : Subgroup (barQ Y)} (hL : CFSG.IsComponent L)
    (hKL : K.map (barMk Y) ≤ L) (hsL : barMk Y s ∈ L) :
    Ez (⟨barMk Y s, hsL⟩ : ↥L) = (K.map (barMk Y)).subgroupOf L := by
  set zJ : ↥L := ⟨barMk Y s, hsL⟩ with hzJ
  set X := centralizer ({zJ} : Set ↥L) with hX
  set Cb := centralizer ({barMk Y s} : Set (barQ Y)) with hCb
  have hmemX : ∀ x : ↥L, x ∈ X ↔ ((x : barQ Y)) ∈ Cb := by
    intro x
    rw [hX, hCb, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · intro hx; exact congrArg Subtype.val hx
    · intro hx; exact Subtype.ext hx
  have hKCb : K.map (barMk Y) ≤ Cb := by
    rintro _ ⟨k, hk, rfl⟩
    rw [hCb, mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    rw [(mem_centralizer_singleton_iff.mp (h.le hk))]
  have hKX : (K.map (barMk Y)).subgroupOf L ≤ X := by
    intro x hx
    rw [hmemX]
    exact hKCb (Subgroup.mem_subgroupOf.mp hx)
  apply le_antisymm
  ·
    rintro _ ⟨y, hy, rfl⟩
    let ι : ↥X →* ↥Cb :=
      { toFun := fun y => ⟨((y : ↥L) : barQ Y), (hmemX y.1).mp y.2⟩
        map_one' := rfl
        map_mul' := fun a b => rfl }
    have hιinj : Function.Injective ι := by
      intro a b hab
      apply Subtype.ext; apply Subtype.ext
      exact congrArg (fun x : ↥Cb => (x : barQ Y)) hab
    have hrange : ι.range.Normal := by
      refine ⟨fun n hn c => ?_⟩
      obtain ⟨a, rfl⟩ := hn
      have hcn : (c : barQ Y) ∈ Subgroup.normalizer (L : Set (barQ Y)) :=
        h.mem_normalizer hL hKL c.2
      have h1 : (c : barQ Y) * ((a : ↥L) : barQ Y) * (c : barQ Y)⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp hcn _).mp (a : ↥L).2
      have h2 : (c : barQ Y) * ((a : ↥L) : barQ Y) * (c : barQ Y)⁻¹ ∈ Cb :=
        mul_mem (mul_mem c.2 ((hmemX a.1).mp a.2)) (inv_mem c.2)
      refine ⟨⟨⟨_, h1⟩, (hmemX _).mpr h2⟩, ?_⟩
      apply Subtype.ext
      rfl
    have hlayer : CFSG.layer ↥X ≤ ((K.map (barMk Y)).subgroupOf L).subgroupOf X := by
      refine sSup_le fun Λ hΛ => ?_
      have hq : IsQuasisimple (Λ.map ι) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv (Λ.equivMapOfInjective ι hιinj) hΛ.1
      have hsn : (Λ.map ι).IsSubnormal := by
        let ι' : ↥X →* ↥ι.range := ι.rangeRestrict
        have hsurj : Function.Surjective ι' := ι.rangeRestrict_surjective
        have h1 : (Λ.map ι').IsSubnormal := Subgroup.IsSubnormal.map hsurj hΛ.2
        have h2 : Λ.map ι' = (Λ.map ι).subgroupOf ι.range := by
          ext x
          constructor
          · rintro ⟨a, ha, rfl⟩
            exact ⟨a, ha, rfl⟩
          · intro hx
            obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
            exact ⟨a, ha, Subtype.ext hax⟩
        rw [h2] at h1
        exact Subgroup.IsSubnormal.trans (Subgroup.map_le_range ι Λ) h1 hrange.isSubnormal
      have hcomp : CFSG.IsComponent (Λ.map ι) := ⟨hq, hsn⟩
      have hle := (CFSG.LocalCores.component_le_layer hcomp).trans h.layer_le
      intro a ha
      have := hle ⟨a, ha, rfl⟩
      rw [Subgroup.mem_subgroupOf] at this
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact this
    have := hlayer hy
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at this
    exact this
  ·
    intro x hx
    have hxX : x ∈ X := hKX hx
    have hnorm : (((K.map (barMk Y)).subgroupOf L).subgroupOf X).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hn ⊢
      have hg : ((g : ↥L) : barQ Y) ∈ Cb := (hmemX g.1).mp g.2
      exact h.map_conj_mem hg hn
    have hqs : IsQuasisimple (((K.map (barMk Y)).subgroupOf L).subgroupOf X) := by
      have e1 := Subgroup.subgroupOfEquivOfLe hKX
      have e2 := Subgroup.subgroupOfEquivOfLe hKL
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (e1.trans e2).symm h.isQuasisimple_map
    have hcomp : CFSG.IsComponent (((K.map (barMk Y)).subgroupOf L).subgroupOf X) :=
      ⟨hqs, hnorm.isSubnormal⟩
    have := CFSG.LocalCores.component_le_layer hcomp (show (⟨x, hxX⟩ : ↥X) ∈ _ from hx)
    exact ⟨⟨x, hxX⟩, this, rfl⟩

structure KPair (Y : Type) [Group Y] (s s' : Y) (K K' : Subgroup Y) : Prop where
  K1 : KComp Y s K
  K2 : KComp Y s' K'
  ne : s ≠ s'
  comm : s * s' = s' * s
  nc : ∃ k ∈ K', s * k ≠ k * s

namespace KPair

variable {s' : Y} {K' : Subgroup Y}

omit [Finite Y] in
theorem norm' (h : KPair Y s s' K K') {k : Y} (hk : k ∈ K') : s * k * s⁻¹ ∈ K' :=
  h.K2.norm s (mem_centralizer_singleton_iff.mpr h.comm) k hk

theorem comm_of_barMk_comm (h : KPair Y s s' K K') {k : Y} (hk : k ∈ K')
    (hc : barMk Y s * barMk Y k = barMk Y k * barMk Y s) : s * k = k * s := by
  have h1 : s * k * s⁻¹ * k⁻¹ ∈ K' := mul_mem (h.norm' hk) (inv_mem hk)
  have h2 : s * k * s⁻¹ * k⁻¹ ∈ pPrimeCore 2 Y := by
    rw [← ker_barMk, MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hc]; group
  have h3 : s * k * s⁻¹ * k⁻¹ ∈ K' ⊓ pPrimeCore 2 Y := ⟨h1, h2⟩
  rw [h.K2.inf_bot, mem_bot] at h3
  calc s * k = (s * k * s⁻¹ * k⁻¹) * (k * s) := by group
    _ = k * s := by rw [h3, one_mul]

theorem exists_component (h : KPair Y s s' K K') :
    ∃ L : Subgroup (barQ Y), CFSG.IsComponent L ∧ K.map (barMk Y) ≤ L ∧ K'.map (barMk Y) ≤ L ∧
      barMk Y s ∈ L := by
  obtain ⟨L, hL, hKL, hsL⟩ := h.K1.exists_component
  obtain ⟨L', hL', hKL', -⟩ := h.K2.exists_component
  refine ⟨L, hL, hKL, ?_, hsL⟩
  by_cases hLL : L = L'
  · rw [hLL]; exact hKL'
  · exfalso
    have hc : ⁅L, L'⁆ = ⊥ := (CFSG.LocalCores.distinct_components_commute hL hL').resolve_left hLL
    obtain ⟨k, hk, hsk⟩ := h.nc
    apply hsk
    refine h.comm_of_barMk_comm hk ?_
    have h1 : barMk Y s ∈ L := hsL
    have h2 : barMk Y k ∈ L' := hKL' (Subgroup.mem_map_of_mem _ hk)
    have h3 := Subgroup.commutator_mem_commutator h1 h2
    rw [hc, Subgroup.mem_bot, commutatorElement_def] at h3
    calc barMk Y s * barMk Y k = (barMk Y s * barMk Y k * (barMk Y s)⁻¹ * (barMk Y k)⁻¹) *
          (barMk Y k * barMk Y s) := by group
      _ = barMk Y k * barMk Y s := by rw [h3, one_mul]

theorem pPrimeCore_barQ_eq_bot : pPrimeCore 2 (barQ Y) = ⊥ := by
  have := oddCore_barQ (Y := Y)
  rwa [← CatalogueBAlternating.primeCore_two_eq_oddCore] at this

theorem center_bot (h : KPair Y s s' K K')
    (hcyc : ∀ T : Sylow 2 ↥(centralizer (K : Set Y)), IsCyclic ↥T)
    {L : Subgroup (barQ Y)} (hL : CFSG.IsComponent L) (hKL : K.map (barMk Y) ≤ L)
    (hK'L : K'.map (barMk Y) ≤ L) : Subgroup.center ↥L = ⊥ := by
  by_contra hne
  have h2 := (CFSG.ProperTwoGeneratedCore.Assembly.component_center_le_twoCore
    (pPrimeCore_barQ_eq_bot (Y := Y)) hL).1
  have hnt : Nontrivial (Subgroup.center ↥L) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact (Finite.one_lt_card_iff_nontrivial.mpr hnt).ne' hn
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 (hn ▸ dvd_pow_self 2 hn0)
  have hwL : ((w : ↥L) : barQ Y) ∈ L := (w : ↥L).2
  have hw2 : orderOf (((w : ↥L) : barQ Y)) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
  have hwc : ∀ x ∈ L, x * ((w : ↥L) : barQ Y) = ((w : ↥L) : barQ Y) * x := by
    intro x hx
    have := Subgroup.mem_center_iff.mp w.2 ⟨x, hx⟩
    exact congrArg Subtype.val this
  have hwK : ((w : ↥L) : barQ Y) ∈
      centralizer ((K.map (barMk Y) : Subgroup (barQ Y)) : Set (barQ Y)) := by
    rw [mem_centralizer_iff]
    intro x hx
    exact hwc x (hKL hx)
  have heq := eq_barMk_of_involution h.K1.ord h.K1.mem h.K1.perfect h.K1.le h.K1.norm h.K1.inf_bot
    hcyc hwK hw2
  obtain ⟨k, hk, hsk⟩ := h.nc
  apply hsk
  refine h.comm_of_barMk_comm hk ?_
  have := hwc (barMk Y k) (hK'L (Subgroup.mem_map_of_mem _ hk))
  rw [heq] at this
  exact this.symm

end KPair


theorem cyclic_sylow_of_surjective {C D : Type*} [Group C] [Group D] [Finite C] [Finite D]
    (f : C →* D) (hf : Function.Surjective f) (hC : ∀ T : Sylow 2 C, IsCyclic ↥T)
    (P : Sylow 2 D) : IsCyclic ↥P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := Sylow.mapSurjective_surjective hf 2 P
  have hPT : (P : Subgroup D) = (T : Subgroup C).map f := by
    rw [← hT, Sylow.coe_mapSurjective]
  have := hC T
  let g : ↥(T : Subgroup C) →* D := f.comp (T : Subgroup C).subtype
  have hcyc : IsCyclic ↥g.range := isCyclic_of_surjective g.rangeRestrict g.rangeRestrict_surjective
  have e : g.range = (T : Subgroup C).map f := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨a, a.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩; exact ⟨⟨a, ha⟩, rfl⟩
  let e2 : ↥(P : Subgroup D) ≃* ↥g.range := MulEquiv.subgroupCongr (hPT.trans e.symm)
  exact isCyclic_of_surjective e2.symm.toMonoidHom e2.symm.surjective

theorem isCyclic_of_injective_of_cyclic_sylow {S D : Type*} [Group S] [Group D] [Finite D]
    (hS : IsPGroup 2 S) (g : S →* D) (hg : Function.Injective g)
    (hD : ∀ P : Sylow 2 D, IsCyclic ↥P) : IsCyclic S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpr : IsPGroup 2 ↥g.range := hS.of_surjective g.rangeRestrict g.rangeRestrict_surjective
  obtain ⟨P, hP⟩ := hpr.exists_le_sylow
  have := hD P
  have hc : IsCyclic ↥g.range := by
    have : IsCyclic ↥(g.range.subgroupOf (P : Subgroup D)) := inferInstance
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hP).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hP).surjective
  exact isCyclic_of_injective g.rangeRestrict (by
    intro a b hab; apply hg; exact congrArg Subtype.val hab)

theorem isSimpleGroup_of_center_bot {X : Type*} [Group X] {L : Subgroup X}
    (hL : CFSG.IsQuasisimple L) (hc : Subgroup.center ↥L = ⊥) : IsSimpleGroup ↥L := by
  obtain ⟨-, hs, -⟩ := hL
  let e : (↥L ⧸ Subgroup.center ↥L) ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  have := hs
  exact e.symm.isSimpleGroup

theorem KComp.cyclic_sylow_bar (h : KComp Y s K)
    (hcyc : ∀ T : Sylow 2 ↥(centralizer (K : Set Y)), IsCyclic ↥T) :
    ∀ P : Sylow 2 ↥(centralizer ((K.map (barMk Y) : Subgroup (barQ Y)) : Set (barQ Y))),
      IsCyclic ↥P := by
  have hceq := centralizer_map_barMk h.ord h.mem h.perfect h.le h.norm h.inf_bot
  let f : ↥(centralizer (K : Set Y)) →* ↥(centralizer ((K.map (barMk Y) : Subgroup (barQ Y)) : Set (barQ Y))) :=
    ((barMk Y).comp (centralizer (K : Set Y)).subtype).codRestrict _ (fun c => by
      rw [hceq]; exact ⟨c, c.2, rfl⟩)
  have hf : Function.Surjective f := by
    intro x
    have hx : (x : barQ Y) ∈ (centralizer (K : Set Y)).map (barMk Y) := by
      rw [← hceq]; exact x.2
    obtain ⟨c, hc, hcx⟩ := hx
    exact ⟨⟨c, hc⟩, Subtype.ext hcx⟩
  exact cyclic_sylow_of_surjective f hf hcyc


theorem isFourSubgroup_zpowers_sup {J : Type} [Group J] [Finite J] {a b : J} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (hab : a ≠ b) (hc : a * b = b * a) :
    IsFourSubgroup (zpowers a ⊔ zpowers b) := by
  have hcomm : ∀ x ∈ zpowers a, ∀ y ∈ zpowers b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute a b from hc) m n).eq
  have ha2 : a * a = 1 := by
    have := pow_orderOf_eq_one a; rwa [ha, pow_two] at this
  have hb2 : b * b = 1 := by
    have := pow_orderOf_eq_one b; rwa [hb, pow_two] at this
  have hsq : ∀ x ∈ zpowers a, x * x = 1 := by
    intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, ha2, one_zpow]
  have hsq' : ∀ x ∈ zpowers b, x * x = 1 := by
    intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hb2, one_zpow]
  have hinf : zpowers a ⊓ zpowers b = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxa, hxb⟩
    have h1 : orderOf x ∣ 2 := ha ▸ orderOf_dvd_of_mem_zpowers hxa
    by_contra hx
    have hx1 : x ≠ 1 := fun h => hx (by rw [h]; exact one_mem _)
    have hx2 : orderOf x = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hx1
      · exact h
    have e1 := eq_of_mem_zpowers_of_orderOf_two ha hx2 hxa
    have e2 := eq_of_mem_zpowers_of_orderOf_two hb hx2 hxb
    exact hab (e1.symm.trans e2)
  have hcard : Nat.card ↥(zpowers a ⊔ zpowers b) = 4 := by
    have := card_sup_mul_card_inf_of_commute hcomm
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, ha, hb] at this
    exact this
  refine ⟨?_, hcard⟩
  have hel : ∀ x ∈ zpowers a ⊔ zpowers b, ∀ y ∈ zpowers a ⊔ zpowers b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨h₁, hh₁, k₁, hk₁, rfl⟩ := mem_sup_of_commute hcomm hx
    obtain ⟨h₂, hh₂, k₂, hk₂, rfl⟩ := mem_sup_of_commute hcomm hy
    have hha : h₁ * h₂ = h₂ * h₁ := by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh₁
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh₂
      exact (Commute.zpow_zpow_self a m n).eq
    have hkb : k₁ * k₂ = k₂ * k₁ := by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk₁
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk₂
      exact (Commute.zpow_zpow_self b m n).eq
    have hhk1 := hcomm h₂ hh₂ k₁ hk₁
    calc h₁ * k₁ * (h₂ * k₂) = h₁ * (k₁ * h₂) * k₂ := by group
      _ = h₁ * (h₂ * k₁) * k₂ := by rw [← hhk1]
      _ = (h₁ * h₂) * (k₁ * k₂) := by group
      _ = (h₂ * h₁) * (k₂ * k₁) := by rw [hha, hkb]
      _ = h₂ * (h₁ * k₂) * k₁ := by group
      _ = h₂ * (k₂ * h₁) * k₁ := by rw [hcomm h₁ hh₁ k₂ hk₂]
      _ = h₂ * k₂ * (h₁ * k₁) := by group
  have hel2 : ∀ x ∈ zpowers a ⊔ zpowers b, x * x = 1 := by
    intro x hx
    obtain ⟨h₁, hh₁, k₁, hk₁, rfl⟩ := mem_sup_of_commute hcomm hx
    calc h₁ * k₁ * (h₁ * k₁) = (h₁ * h₁) * (k₁ * k₁) := by
          rw [mul_assoc, ← mul_assoc k₁, ← hcomm h₁ hh₁ k₁ hk₁]; group
      _ = 1 := by rw [hsq h₁ hh₁, hsq' k₁ hk₁, one_mul]
  refine { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hel _ a.2 _ b.2)⟩⟩, exponent_dvd_p := ?_ }
  rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
  intro a'
  apply Subtype.ext
  have := hel2 _ a'.2
  simpa [pow_two] using this


theorem KComp.cyclic_sylow_J (h : KComp Y s K)
    (hcyc : ∀ T : Sylow 2 ↥(centralizer (K : Set Y)), IsCyclic ↥T)
    {L : Subgroup (barQ Y)} (hKL : K.map (barMk Y) ≤ L) :
    ∀ S : Sylow 2 ↥(centralizer (((K.map (barMk Y)).subgroupOf L : Subgroup ↥L) : Set ↥L)),
      IsCyclic ↥S := by
  intro S
  let CJ := centralizer (((K.map (barMk Y)).subgroupOf L : Subgroup ↥L) : Set ↥L)
  let g : ↥CJ →* ↥(centralizer ((K.map (barMk Y) : Subgroup (barQ Y)) : Set (barQ Y))) :=
    { toFun := fun x => ⟨((x : ↥L) : barQ Y), by
        rw [mem_centralizer_iff]
        intro k hk
        have := (mem_centralizer_iff.mp x.2) ⟨k, hKL hk⟩ (Subgroup.mem_subgroupOf.mpr hk)
        exact congrArg Subtype.val this⟩
      map_one' := rfl
      map_mul' := fun a b => rfl }
  have hginj : Function.Injective g := by
    intro a b hab
    apply Subtype.ext; apply Subtype.ext
    have h1 := congrArg Subtype.val hab
    exact h1
  have hS : IsPGroup 2 ↥(S : Subgroup ↥CJ) := S.isPGroup'
  have := isCyclic_of_injective_of_cyclic_sylow hS (g.comp (S : Subgroup ↥CJ).subtype)
    (hginj.comp (S : Subgroup ↥CJ).subtype_injective) (h.cyclic_sylow_bar hcyc)
  exact this

theorem eq_of_barMk_eq {s s' : Y} (hs : orderOf s = 2) (hs' : orderOf s' = 2)
    (hc : s * s' = s' * s) (h : barMk Y s = barMk Y s') : s = s' := by
  have hss : s * s = 1 := by have := pow_orderOf_eq_one s; rwa [hs, pow_two] at this
  have hss' : s' * s' = 1 := by have := pow_orderOf_eq_one s'; rwa [hs', pow_two] at this
  have hx : s * s' ∈ pPrimeCore 2 Y := by
    rw [← ker_barMk, MonoidHom.mem_ker, map_mul, ← h, ← map_mul, hss, map_one]
  have hx2 : (s * s') * (s * s') = 1 := by
    calc (s * s') * (s * s') = s * (s' * s) * s' := by group
      _ = s * (s * s') * s' := by rw [← hc]
      _ = (s * s) * (s' * s') := by group
      _ = 1 := by rw [hss, hss', one_mul]
  have h1 : orderOf (s * s') ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx2)
  have h2 : orderOf (s * s') ∣ Nat.card (pPrimeCore 2 Y) := Subgroup.orderOf_dvd_natCard _ hx
  have h3 : orderOf (s * s') ∣ Nat.gcd 2 (Nat.card (pPrimeCore 2 Y)) := Nat.dvd_gcd h1 h2
  rw [pPrimeCore_coprime_card, Nat.dvd_one, orderOf_eq_one_iff] at h3
  have : s' = s⁻¹ := by
    have : s * s' = 1 := h3
    exact (eq_inv_of_mul_eq_one_right this)
  rw [this]
  exact (inv_eq_of_mul_eq_one_right hss).symm

@[expose] def IVK_9_5At (q : ℕ) : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsSimpleGroup J → IsKGroupNative J →
    ∀ z : J, orderOf z = 2 → Odd q →
      HasSL2Model ↥(Ez z) (fun r => r = q) →
      (∀ S : Sylow 2 ↥(centralizer ((Ez z : Subgroup J) : Set J)), IsCyclic ↥S) →
        ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ IsLnEps 3 J ε q

theorem IVK_9_5At_of (h : IVK_9_5) {q : ℕ} (hq : 5 < q) : IVK_9_5At q :=
  fun J _ _ hJ hK z hz hodd hsl hcyc => h J hJ hK z hz q hodd hq hsl hcyc

theorem kstep_main {p n : ℕ} (h95 : IVK_9_5At (p ^ n)) (h44a : IVK_4_4a)
    (hY : IsKGroupNative Y) (hp : p.Prime) (hp2 : p ≠ 2) (hq5 : 5 ≤ p ^ n)
    {s s' : Y} {K K' : Subgroup Y} (h : KPair Y s s' K K')
    (hsl : HasSL2Model ↥K (fun r => r = p ^ n))
    (hcyc : ∀ T : Sylow 2 ↥(centralizer (K : Set Y)), IsCyclic ↥T) :
    ∃ L : Subgroup (barQ Y), CFSG.IsComponent L ∧ K.map (barMk Y) ≤ L ∧ K'.map (barMk Y) ≤ L ∧
      Subgroup.center ↥L = ⊥ ∧ K.map (barMk Y) ⊔ K'.map (barMk Y) = L ∧
      ∃ δ : ℤ, (δ = 1 ∨ δ = -1) ∧ IsLnEps 3 ↥L δ (p ^ n) := by
  obtain ⟨L, hL, hKL, hK'L, hsL⟩ := h.exists_component
  have hs'L : barMk Y s' ∈ L := hK'L (Subgroup.mem_map_of_mem _ h.K2.mem)
  have hc := h.center_bot hcyc hL hKL hK'L
  have hsimple := isSimpleGroup_of_center_bot hL.1 hc
  have hKg : IsKGroupNative ↥L := by
    have h1 : SectionRank.IsKGroupCat (barQ Y) := SectionRank.IsKGroupCat.quotient hY _
    exact SectionRank.IsKGroupCat.subgroup h1 L
  set zJ : ↥L := ⟨barMk Y s, hsL⟩ with hzJ
  set uJ : ↥L := ⟨barMk Y s', hs'L⟩ with huJ
  have hz2 : orderOf zJ = 2 := by
    rw [← Subgroup.orderOf_coe]; exact orderOf_barMk h.K1.ord
  have hu2 : orderOf uJ = 2 := by
    rw [← Subgroup.orderOf_coe]; exact orderOf_barMk h.K2.ord
  have hEz : Ez zJ = (K.map (barMk Y)).subgroupOf L := h.K1.Ez_eq hL hKL hsL
  have hEu : Ez uJ = (K'.map (barMk Y)).subgroupOf L := h.K2.Ez_eq hL hK'L hs'L
  have hsl' : HasSL2Model ↥(Ez zJ) (fun r => r = p ^ n) := by
    obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ := hsl
    refine ⟨F, hF, hFin, hcard, ⟨?_⟩⟩
    rw [hEz]
    exact ((Subgroup.subgroupOfEquivOfLe hKL).trans h.K1.equivMap.symm).trans e
  have hcycJ : ∀ S : Sylow 2 ↥(centralizer ((Ez zJ : Subgroup ↥L) : Set ↥L)), IsCyclic ↥S := by
    rw [hEz]
    exact h.K1.cyclic_sylow_J hcyc hKL
  have hodd : Odd (p ^ n) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  obtain ⟨δ, hδ, hLn⟩ := h95 ↥L hsimple hKg zJ hz2 hodd hsl' hcycJ
  have hne : zJ ≠ uJ := by
    intro heq
    have h1 : barMk Y s = barMk Y s' := congrArg Subtype.val heq
    exact h.ne (eq_of_barMk_eq h.K1.ord h.K2.ord h.comm h1)
  have hcomm : zJ * uJ = uJ * zJ := Subtype.ext (by
    show barMk Y s * barMk Y s' = barMk Y s' * barMk Y s
    rw [← map_mul, ← map_mul, h.comm])
  have hU := isFourSubgroup_zpowers_sup hz2 hu2 hne hcomm
  have h4 := (h44a ↥L δ p n hp hp2 hLn _ hU zJ (Subgroup.mem_sup_left (mem_zpowers zJ)) uJ
    (Subgroup.mem_sup_right (mem_zpowers uJ)) hz2 hu2 hne).1 (by omega)
  rw [hEz, hEu, Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq] at h4
  have hgen : K.map (barMk Y) ⊔ K'.map (barMk Y) = L := by
    have h5 := congrArg (Subgroup.map L.subtype) h4
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hKL,
      Subgroup.map_subgroupOf_eq_of_le hK'L, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h5
    exact h5
  exact ⟨L, hL, hKL, hK'L, hc, hgen, δ, hδ, hLn⟩


omit [Finite Y] in
theorem mem_zpowers_sup_iff {s s' : Y} (hs : orderOf s = 2) (hs' : orderOf s' = 2)
    (hc : s * s' = s' * s) {v : Y} :
    v ∈ zpowers s ⊔ zpowers s' → v = 1 ∨ v = s ∨ v = s' ∨ v = s * s' := by
  intro hv
  have hcomm : ∀ x ∈ zpowers s, ∀ y ∈ zpowers s', x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute s s' from hc) m n).eq
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hcomm hv
  have key : ∀ {t : Y}, orderOf t = 2 → ∀ x ∈ zpowers t, x = 1 ∨ x = t := by
    intro t ht x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h1 : t ^ m = t ^ (m % (orderOf t : ℤ)) := (zpow_mod_orderOf t m).symm
    rw [ht] at h1
    have h2 : m % ((2 : ℕ) : ℤ) = 0 ∨ m % ((2 : ℕ) : ℤ) = 1 := by omega
    rcases h2 with h2 | h2
    · left; rw [h1, h2]; simp
    · right; rw [h1, h2]; simp
  rcases key hs a ha with rfl | rfl <;> rcases key hs' b hb with rfl | rfl <;> simp

theorem KPair.pPrimeCore_centralizes {s' : Y} {K' : Subgroup Y} (h : KPair Y s s' K K')
    (hD1 : ∀ d ∈ pPrimeCore 2 Y, d ∈ centralizer ({s} : Set Y) → s' * d = d * s')
    (hD2 : ∀ d ∈ pPrimeCore 2 Y, d ∈ centralizer ({s'} : Set Y) → s * d = d * s)
    (hg : ∃ g : Y, g * s * g⁻¹ = s * s') :
    ∀ n ∈ pPrimeCore 2 Y, ∀ k ∈ K ⊔ K', n * k = k * n := by
  intro n hn k hk
  set N := pPrimeCore 2 Y with hN
  have hNn : N.Normal := pPrimeCore_normal
  set V := zpowers s ⊔ zpowers s' with hV
  have hV4 : IsFourSubgroup V := isFourSubgroup_zpowers_sup h.K1.ord h.K2.ord h.ne h.comm
  have hVn : V ≤ Subgroup.normalizer (N : Set Y) := by
    intro v _
    exact Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => hNn.conj_mem x hx v,
      fun hx => by
        have h1 := hNn.conj_mem _ hx v⁻¹
        convert h1 using 1; group⟩
  have hcop : Nat.Coprime 2 (Nat.card N) := pPrimeCore_coprime_card
  have hcardV : Nat.card V = 2 ^ 2 := by rw [hV4.2]; norm_num
  have hIG := CFSG.GH74.GLS.Stage2.Bender.Thm1.ig_11_23_thm Y 2 Nat.prime_two V N hV4.1 hcardV hcop hVn
  have hmem : ∀ {x v : Y}, x ∈ centralizer ({v} : Set Y) ↔ x * v = v * x := by
    intro x v
    exact mem_centralizer_singleton_iff
  set A : Subgroup Y := N ⊓ centralizer ({s} : Set Y) with hA
  set D₀ : Subgroup Y := N ⊓ centralizer ({s} : Set Y) ⊓ centralizer ({s'} : Set Y) with hD₀
  have hAD : A = D₀ := by
    refine le_antisymm (fun x hx => ⟨hx, hmem.mpr (hD1 x hx.1 hx.2).symm⟩) inf_le_left
  obtain ⟨g, hg⟩ := hg
  set A' : Subgroup Y := N ⊓ centralizer ({s * s'} : Set Y) with hA'
  have hmapA : A.map (MulAut.conj g).toMonoidHom = A' := by
    ext y
    constructor
    · rintro ⟨a, ⟨haN, has⟩, rfl⟩
      refine ⟨hNn.conj_mem a haN g, ?_⟩
      show g * a * g⁻¹ ∈ centralizer ({s * s'} : Set Y)
      rw [hmem]
      have h1 : a * s = s * a := hmem.mp has
      rw [← hg]
      calc g * a * g⁻¹ * (g * s * g⁻¹) = g * (a * s) * g⁻¹ := by group
        _ = g * (s * a) * g⁻¹ := by rw [h1]
        _ = g * s * g⁻¹ * (g * a * g⁻¹) := by group
    · rintro ⟨hyN, hys⟩
      refine ⟨g⁻¹ * y * g, ⟨by simpa using hNn.conj_mem y hyN g⁻¹, ?_⟩, by
        show g * (g⁻¹ * y * g) * g⁻¹ = y
        group⟩
      show g⁻¹ * y * g ∈ centralizer ({s} : Set Y)
      rw [hmem]
      have h1 : y * (s * s') = (s * s') * y := hmem.mp hys
      rw [← hg] at h1
      calc g⁻¹ * y * g * s = g⁻¹ * (y * (g * s * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * s * g⁻¹) * y) * g := by rw [h1]
        _ = s * (g⁻¹ * y * g) := by group
  have hDA' : D₀ ≤ A' := by
    rintro x ⟨⟨hxN, hxs⟩, hxs'⟩
    refine ⟨hxN, ?_⟩
    have h1 : x * s = s * x := hmem.mp hxs
    have h2 : x * s' = s' * x := hmem.mp hxs'
    show x ∈ centralizer ({s * s'} : Set Y)
    rw [hmem]
    calc x * (s * s') = (x * s) * s' := by group
      _ = (s * x) * s' := by rw [h1]
      _ = s * (x * s') := by group
      _ = s * (s' * x) := by rw [h2]
      _ = (s * s') * x := by group
  have hcardA' : Nat.card A' = Nat.card D₀ := by
    rw [← hmapA, card_map_conj, hAD]
  have hD₀A' : D₀ = A' := Subgroup.eq_of_le_of_card_ge hDA' (by rw [hcardA'])
  have hNle : N ≤ D₀ := by
    refine hIG.trans (iSup₂_le fun v hv => ?_)
    obtain ⟨hvV, hv1⟩ := hv
    rcases mem_zpowers_sup_iff h.K1.ord h.K2.ord h.comm hvV with rfl | rfl | rfl | rfl
    · exact absurd rfl hv1
    · rw [← hAD]
    · intro x hx
      have hxN := hx.1
      have hxs' := hx.2
      refine ⟨⟨hxN, hmem.mpr (hD2 x hxN hxs').symm⟩, hxs'⟩
    · rw [hD₀A']
  have hnD := hNle hn
  have hnN : n ∈ N := hn
  obtain ⟨⟨-, hns⟩, hns'⟩ := hnD
  have hK1 : K ≤ centralizer ({n} : Set Y) := by
    intro k' hk'
    rw [mem_centralizer_singleton_iff]
    exact (comm_of_mem_pPrimeCore_of_mem_centralizer h.K1.norm h.K1.inf_bot hnN hns hk').symm
  have hK2 : K' ≤ centralizer ({n} : Set Y) := by
    intro k' hk'
    rw [mem_centralizer_singleton_iff]
    exact (comm_of_mem_pPrimeCore_of_mem_centralizer h.K2.norm h.K2.inf_bot hnN hns' hk').symm
  have := (sup_le hK1 hK2) hk
  rw [mem_centralizer_singleton_iff] at this
  exact this.symm

theorem KPair.card_centralizer_bar {s' : Y} {K' : Subgroup Y} (h : KPair Y s s' K K')
    {L : Subgroup (barQ Y)} (hKL : K.map (barMk Y) ≤ L) (hs'L : barMk Y s' ∈ L) :
    Nat.card ↥(K ⊓ centralizer ({s'} : Set Y)) =
      Nat.card ↥(centralizer ({(⟨barMk Y s', hs'L⟩ : ↥L)} : Set ↥L) ⊓
        (K.map (barMk Y)).subgroupOf L) := by
  have hmemK : ∀ k : ↥(K ⊓ centralizer ({s'} : Set Y)),
      (k : Y) ∈ K ∧ (k : Y) * s' = s' * (k : Y) := fun k =>
    ⟨(Subgroup.mem_inf.mp k.2).1, mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp k.2).2⟩
  let f : ↥(K ⊓ centralizer ({s'} : Set Y)) →
      ↥(centralizer ({(⟨barMk Y s', hs'L⟩ : ↥L)} : Set ↥L) ⊓ (K.map (barMk Y)).subgroupOf L) :=
    fun k => ⟨⟨barMk Y (k : Y), hKL (Subgroup.mem_map_of_mem _ (hmemK k).1)⟩,
      Subgroup.mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr (Subtype.ext (by
        show barMk Y (k : Y) * barMk Y s' = barMk Y s' * barMk Y (k : Y)
        rw [← map_mul, ← map_mul, (hmemK k).2])),
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem _ (hmemK k).1)⟩⟩
  refine Nat.card_eq_of_bijective f ⟨?_, ?_⟩
  · intro a b hab
    have h1 : barMk Y (a : Y) = barMk Y (b : Y) := congrArg (fun x => ((x.1 : ↥L) : barQ Y)) hab
    apply Subtype.ext
    have h3 : ((a : Y)⁻¹ * (b : Y)) ∈ pPrimeCore 2 Y := by
      rw [← ker_barMk]
      exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, h1, inv_mul_cancel])
    have h2 : ((a : Y)⁻¹ * (b : Y)) ∈ K ⊓ pPrimeCore 2 Y :=
      Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (hmemK a).1) (hmemK b).1, h3⟩
    rw [h.K1.inf_bot, mem_bot] at h2
    exact (inv_mul_eq_one.mp h2)
  · rintro ⟨⟨x, hxL⟩, hx⟩
    obtain ⟨hxc, hxK⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hxK)
    have hxc' : x * barMk Y s' = barMk Y s' * x := by
      have := mem_centralizer_singleton_iff.mp hxc
      exact congrArg Subtype.val this
    have hks : k * s' = s' * k := by
      have h1 : barMk Y k * barMk Y s' = barMk Y s' * barMk Y k := by rw [hkx]; exact hxc'
      have h2 : s' * k * s'⁻¹ * k⁻¹ ∈ K :=
        mul_mem (h.K1.norm s' (mem_centralizer_singleton_iff.mpr h.comm.symm) k hk) (inv_mem hk)
      have h3 : s' * k * s'⁻¹ * k⁻¹ ∈ pPrimeCore 2 Y := by
        rw [← ker_barMk, MonoidHom.mem_ker]
        simp only [map_mul, map_inv]
        rw [← h1]; group
      have h4 : s' * k * s'⁻¹ * k⁻¹ ∈ K ⊓ pPrimeCore 2 Y := ⟨h2, h3⟩
      rw [h.K1.inf_bot, mem_bot] at h4
      calc k * s' = (k * s' * k⁻¹ * s'⁻¹) * (s' * k) := by group
        _ = s' * k := by
          have : k * s' * k⁻¹ * s'⁻¹ = (s' * k * s'⁻¹ * k⁻¹)⁻¹ := by group
          rw [this, h4, inv_one, one_mul]
    refine ⟨⟨k, Subgroup.mem_inf.mpr ⟨hk, mem_centralizer_singleton_iff.mpr hks⟩⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hkx

omit [Finite Y] in
theorem KPair.perfect_sup {s' : Y} {K' : Subgroup Y} (h : KPair Y s s' K K') :
    Group.IsPerfect ↥(K ⊔ K') := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm (Subgroup.commutator_le_self _) (sup_le ?_ ?_)
  · calc K = ⁅K, K⁆ := h.K1.perfect.symm
      _ ≤ ⁅K ⊔ K', K ⊔ K'⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
  · calc K' = ⁅K', K'⁆ := h.K2.perfect.symm
      _ ≤ ⁅K ⊔ K', K ⊔ K'⁆ := Subgroup.commutator_mono le_sup_right le_sup_right

omit [Finite Y] in
theorem KPair.central_extension {K' : Subgroup Y}
    (hcen : ∀ n ∈ pPrimeCore 2 Y, ∀ k ∈ K ⊔ K', n * k = k * n)
    {L : Subgroup (barQ Y)} (hgen : K.map (barMk Y) ⊔ K'.map (barMk Y) = L) :
    ∃ φ : ↥(K ⊔ K') →* ↥L, Function.Surjective φ ∧ φ.ker ≤ Subgroup.center ↥(K ⊔ K') := by
  have hmap : (K ⊔ K').map (barMk Y) = L := by rw [Subgroup.map_sup, hgen]
  let φ : ↥(K ⊔ K') →* ↥L :=
    ((barMk Y).comp (K ⊔ K').subtype).codRestrict L (fun g => by
      rw [← hmap]; exact Subgroup.mem_map_of_mem _ g.2)
  refine ⟨φ, ?_, ?_⟩
  · rintro ⟨x, hx⟩
    rw [← hmap] at hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨⟨g, hg⟩, rfl⟩
  · intro g hg
    have h1 : barMk Y (g : Y) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hg)
    have h2 : (g : Y) ∈ pPrimeCore 2 Y := by
      rw [← ker_barMk]; exact MonoidHom.mem_ker.mpr h1
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    exact (hcen _ h2 k k.2).symm


open scoped MatrixGroups in
theorem kstep_final {p n : ℕ} (h95 : IVK_9_5At (p ^ n)) (h44a : IVK_4_4a) (hM3 : L3InvTorus)
    (hCov : L3Cover) (hY : IsKGroupNative Y) (hp : p.Prime) (hp2 : p ≠ 2) (hq5 : 5 ≤ p ^ n)
    {s s' : Y} {K K' : Subgroup Y} (h : KPair Y s s' K K')
    (hsl : HasSL2Model ↥K (fun r => r = p ^ n))
    (hcyc : ∀ T : Sylow 2 ↥(centralizer (K : Set Y)), IsCyclic ↥T)
    (hD1 : ∀ d ∈ pPrimeCore 2 Y, d ∈ centralizer ({s} : Set Y) → s' * d = d * s')
    (hD2 : ∀ d ∈ pPrimeCore 2 Y, d ∈ centralizer ({s'} : Set Y) → s * d = d * s)
    (hg : ∃ g : Y, g * s * g⁻¹ = s * s') {ε : ℤ}
    (hcard : (Nat.card ↥(K ⊓ centralizer ({s'} : Set Y)) : ℤ) = ((p ^ n : ℕ) : ℤ) - ε) :
    (ε = 1 → ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ n ∧
      ∃ α : SL(3, F) →* ↥(K ⊔ K'), Function.Surjective α) ∧
    (ε = -1 → ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (p ^ n) ^ 2 ∧
      ∃ α : ↥(StatedSU 3 (p ^ n) F) →* ↥(K ⊔ K'), Function.Surjective α) := by
  obtain ⟨L, hL, hKL, hK'L, hc, hgen, δ, hδ, hLn⟩ := kstep_main h95 h44a hY hp hp2 hq5 h hsl hcyc
  have hs'L : barMk Y s' ∈ L := hK'L (Subgroup.mem_map_of_mem _ h.K2.mem)
  have hsL : barMk Y s ∈ L := hKL (Subgroup.mem_map_of_mem _ h.K1.mem)
  set zJ : ↥L := ⟨barMk Y s, hsL⟩ with hzJ
  set uJ : ↥L := ⟨barMk Y s', hs'L⟩ with huJ
  have hz2 : orderOf zJ = 2 := by
    rw [← Subgroup.orderOf_coe]; exact orderOf_barMk h.K1.ord
  have hu2 : orderOf uJ = 2 := by
    rw [← Subgroup.orderOf_coe]; exact orderOf_barMk h.K2.ord
  have hne : zJ ≠ uJ := by
    intro heq
    have h1 : barMk Y s = barMk Y s' := congrArg Subtype.val heq
    exact h.ne (eq_of_barMk_eq h.K1.ord h.K2.ord h.comm h1)
  have hcomm : zJ * uJ = uJ * zJ := Subtype.ext (by
    show barMk Y s * barMk Y s' = barMk Y s' * barMk Y s
    rw [← map_mul, ← map_mul, h.comm])
  have hodd : Odd (p ^ n) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hEz : Ez zJ = (K.map (barMk Y)).subgroupOf L := h.K1.Ez_eq hL hKL hsL
  have hM := hM3 ↥L δ (p ^ n) hδ hodd (by omega) hLn zJ uJ hz2 hu2 hne hcomm
  rw [hEz, ← h.card_centralizer_bar hKL hs'L, hcard] at hM
  have hδε : δ = ε := by omega
  have hcen := h.pPrimeCore_centralizes hD1 hD2 hg
  obtain ⟨φ, hφs, hφk⟩ := KPair.central_extension hcen hgen
  have hperf := h.perfect_sup
  have hcov := hCov ↥L δ p n hp hp2 hδ (by omega) hLn ↥(K ⊔ K') hperf φ hφs hφk
  refine ⟨fun he => ?_, fun he => ?_⟩
  · exact hcov.1 (hδε ▸ he)
  · exact hcov.2 (hδε ▸ he)

end CFSG.GH74.GLS.LU.Local
