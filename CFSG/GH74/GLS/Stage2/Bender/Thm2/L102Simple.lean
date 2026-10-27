module

public import CFSG.GH74.GLS.C3.Layer1.BkB2G4Def
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Der10Basic

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L102

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.GH74.GLS.Stage2.Bender.Thm2
open scoped commutatorElement

section Setup

variable {G : Type} [Group G] {z t : G}

abbrev XU (z t : G) : Subgroup G := centralizer ((zpowers z ⊔ zpowers t : Subgroup G) : Set G)

theorem mem_sup_left' : z ∈ (zpowers z ⊔ zpowers t : Subgroup G) := Subgroup.mem_sup_left (mem_zpowers z)

theorem mem_sup_right' : t ∈ (zpowers z ⊔ zpowers t : Subgroup G) := Subgroup.mem_sup_right (mem_zpowers t)

theorem XU_le_Cen : XU z t ≤ Cen z := fun x hx => by
  have := Subgroup.mem_centralizer_iff.mp hx z mem_sup_left'
  exact Subgroup.mem_centralizer_singleton_iff.mpr this.symm

theorem XU_eq (hzt : z * t = t * z) : XU z t = centralizer {t} ⊓ centralizer {z} := by
  ext x
  constructor
  · intro hx
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    · exact (Subgroup.mem_centralizer_iff.mp hx t mem_sup_right').symm
    · exact (Subgroup.mem_centralizer_iff.mp hx z mem_sup_left').symm
  · rintro ⟨hxt, hxz⟩
    refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
    have h1 : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hxt
    have h2 : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp hxz
    exact comm_of_mem_zpowers_sup h2 h1 hzt hu

end Setup

section FXY

abbrev YU {G : Type} [Group G] (z t : G) (htC : t ∈ Cen z) : Subgroup (CentralizerBar z) :=
  centralizer ({toBar z ⟨t, htC⟩} : Set (CentralizerBar z))

variable {G : Type} [Group G] [Finite G] {z t : G}

theorem exists_fXY (hzt : z * t = t * z) (ht2 : t * t = 1) (htC : t ∈ Cen z) :
    ∃ f : ↥(XU z t) →* ↥(YU z t htC),
      Function.Surjective f ∧ Odd (Nat.card f.ker) ∧
      ∀ (x : ↥(XU z t)) (hx : (x : G) ∈ Cen z),
        ((f x : ↥(YU z t htC)) : CentralizerBar z) = toBar z ⟨x, hx⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X : Subgroup G := XU z t with hX
  have hXC : X ≤ Cen z := XU_le_Cen
  set tC : ↥(Cen z) := ⟨t, htC⟩ with htCdef
  have htC2 : ∃ n : ℕ, tC ^ 2 ^ n = 1 := ⟨1, by
    apply Subtype.ext
    simpa [pow_two] using ht2⟩
  have hcen : (centralizer ({tC} : Set ↥(Cen z))).map (toBar z) =
      centralizer ({toBar z tC} : Set (CentralizerBar z)) :=
    CFSG.ComponentClassification.LBalance.Quot.map_centralizer_eq (H := ↥(Cen z)) (p := 2) htC2
  set tb : CentralizerBar z := toBar z tC with htb
  set Y : Subgroup (CentralizerBar z) := centralizer ({tb} : Set (CentralizerBar z)) with hY
  have hXcen : ∀ y : ↥X, (⟨(y : G), hXC y.2⟩ : ↥(Cen z)) ∈ centralizer ({tC} : Set ↥(Cen z)) := by
    intro y
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp y.2 t mem_sup_right').symm
  let f0 : ↥X →* CentralizerBar z := (toBar z).comp (Subgroup.inclusion hXC)
  have hf0Y : ∀ y : ↥X, f0 y ∈ Y := by
    intro y
    have hmem : f0 y ∈ (centralizer ({tC} : Set ↥(Cen z))).map (toBar z) := ⟨_, hXcen y, rfl⟩
    rw [hcen] at hmem
    exact hmem
  let f : ↥X →* ↥Y := f0.codRestrict Y hf0Y
  have hfsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    have hmem : y ∈ (centralizer ({tC} : Set ↥(Cen z))).map (toBar z) := by rw [hcen]; exact hy
    obtain ⟨c, hc, rfl⟩ := hmem
    have hcz : (c : G) * z = z * (c : G) := Subgroup.mem_centralizer_singleton_iff.mp c.2
    have hct : (c : G) * t = t * (c : G) :=
      congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc)
    have hcX : (c : G) ∈ X :=
      Subgroup.mem_centralizer_iff.mpr fun u hu => comm_of_mem_zpowers_sup hcz hct hzt hu
    exact ⟨⟨(c : G), hcX⟩, Subtype.ext rfl⟩
  have hker : Odd (Nat.card f.ker) := by
    have hle : f.ker.map (Subgroup.inclusion hXC) ≤ (toBar z).ker := by
      rintro _ ⟨y, hy, rfl⟩
      have : f y = 1 := hy
      have h2 : f0 y = 1 := congrArg Subtype.val this
      exact h2
    have hcard : Nat.card f.ker = Nat.card (f.ker.map (Subgroup.inclusion hXC)) :=
      (Subgroup.card_map_of_injective (Subgroup.inclusion_injective hXC)).symm
    have hdvd : Nat.card f.ker ∣ Nat.card (toBar z).ker := by
      rw [hcard]
      exact Subgroup.card_dvd_of_le hle
    exact Odd.of_dvd_nat (odd_card_ker_toBar z) hdvd
  exact ⟨f, hfsurj, hker, fun x hx => rfl⟩

end FXY


section Facts

open CFSG.GH74.GLS.TwoThin CFSG.ComponentClassification

variable {G : Type} [Group G] [Finite G] {z t : G}

theorem cenBar_facts (hG : IsKProperSimple G) (hgen4 : CFSG.GH74.Gen4 G) (hz2 : orderOf z = 2) :
    IsKGroupNative (CentralizerBar z) ∧ CFSG.GH74.Gen4 (CentralizerBar z) ∧
      pPrimeCore 2 (CentralizerBar z) = ⊥ := by
  set Y' := centralizer ({z} : Set G) with hY'
  have hY'ne : Y' ≠ ⊤ := centralizer_involution_ne_top hG.1 hG.2.1 hz2
  have hX : IsKGroupNative (barQ ↥Y') :=
    isKGroupNative_of_surjective (X := ↥Y') (isKGroupNative_of_kProper hG.2.2 hY'ne) ⊤
      ((barMk ↥Y').comp (⊤ : Subgroup ↥Y').subtype)
      (barMk_surjective.comp fun m => ⟨⟨m, trivial⟩, rfl⟩)
  have hcore : pPrimeCore 2 (barQ ↥Y') = ⊥ := by
    have := oddCore_barQ (Y := ↥Y')
    rwa [← CatalogueBAlternating.primeCore_two_eq_oddCore] at this
  have hg4 : CFSG.GH74.Gen4 (barQ ↥Y') :=
    CFSG.GH74.Gen4.quotient _ (CFSG.GH74.Gen4.subgroup Y' hgen4)
  exact ⟨hX, hg4, hcore⟩

theorem isComponent_of_B2' {X : Type} [Group X] [Finite X] (hB2 : B_B2_g4) (hg : CFSG.GH74.Gen4 X)
    (hX : IsKGroupNative X) (hcore : pPrimeCore 2 X = ⊥) {y : X} (hy : orderOf y = 2) :
    ∀ J : Subgroup ↥(centralizer ({y} : Set X)), IsPComponent 2 J → IsComponent J := by
  intro J hJ
  have hKJ : (J.map (centralizer ({y} : Set X)).subtype).subgroupOf (centralizer ({y} : Set X)) = J :=
    Subgroup.comap_map_eq_self_of_injective (centralizer ({y} : Set X)).subtype_injective J
  have h1 : IsPCompIn 2 (centralizer ({y} : Set X)) (J.map (centralizer ({y} : Set X)).subtype) :=
    ⟨Subgroup.map_subtype_le J, by rw [hKJ]; exact hJ⟩
  have h2 := hB2 X hg hX hcore y hy _ h1
  have := h2.2
  rwa [hKJ] at this

theorem barOf_le_layer {K : Subgroup G} (hzt : z * t = t * z) (ht2 : orderOf t = 2)
    (hK : IsPCompIn 2 (centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G)) K) :
    barOf z K ≤ layer (CentralizerBar z) := by
  have htC : t ∈ Cen z := Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm
  have hs : orderOf (⟨t, htC⟩ : ↥(Cen z)) = 2 := orderOf_mk_centralizer htC ht2
  exact map_barMk_le_layer hs (le_centralizer_mk (isPCompIn_two_iff.mp hK).1 htC)
    (isTwoComponent_centralizer_mk hK htC)

end Facts

section Swaps

variable {G : Type} [Group G] [Finite G] {z t : G}

omit [Finite G] in
theorem swaps_symm {L₁ L₂ : Subgroup (CentralizerBar z)} (h : Swaps z t L₁ L₂) : Swaps z t L₂ L₁ := by
  obtain ⟨ht, h1, h2⟩ := h
  exact ⟨ht, h2, h1⟩

theorem swaps_of_swapsComps {S : Subgroup G} {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hpair : Stage1Pair G z S q L₁ L₂) (h : SwapsComps z t) : Swaps z t L₁ L₂ := by
  obtain ⟨L₁', L₂', hne, hcomp, hsw⟩ := h
  have hset : ({L₁', L₂'} : Set (Subgroup (CentralizerBar z))) = {L₁, L₂} :=
    hcomp.symm.trans hpair.comps
  have h1 : L₁' ∈ ({L₁, L₂} : Set (Subgroup (CentralizerBar z))) := by
    rw [← hset]
    exact Set.mem_insert _ _
  have h2 : L₂' ∈ ({L₁, L₂} : Set (Subgroup (CentralizerBar z))) := by
    rw [← hset]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · rw [h1, h2] at hsw
    exact hsw
  · rw [h1, h2] at hsw
    exact swaps_symm hsw
  · exact absurd (h1.trans h2.symm) hne

end Swaps


section LayerFacts

variable {A : Type} [Group A]

theorem isComponent_map_subtype {W : Subgroup A} [W.Normal] {K : Subgroup ↥W} (hK : IsComponent K) :
    IsComponent (K.map W.subtype) :=
  ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (K.equivMapOfInjective W.subtype W.subtype_injective) hK.1,
    hK.2.trans' (inferInstance : W.Normal).isSubnormal⟩

theorem map_layer_le_layer_of_normal {W : Subgroup A} [W.Normal] : (layer ↥W).map W.subtype ≤ layer A := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun K hK => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact CFSG.LocalCores.component_le_layer (isComponent_map_subtype hK)

theorem isComponent_subgroupOf {K W : Subgroup A} (hKW : K ≤ W) (hK : IsComponent K) :
    IsComponent (K.subgroupOf W) :=
  ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKW).symm hK.1,
    hK.2.comap W.subtype⟩

end LayerFacts


section Main

open CFSG.GH74.GLS.TwoThin CFSG.ComponentClassification

theorem isSimple_of_isL2 {K : Type} [Group K] {q : ℕ} (hq : 3 < q)
    (h : IVK.IsL2 K (fun r => r = q)) : IsSimpleGroup K := by
  obtain ⟨F₀, _, _, hF₀, ⟨e⟩⟩ := h
  have hF₀' : Nat.card F₀ = q := hF₀
  have h4 : 4 ≤ Nat.card F₀ := by omega
  have : IsSimpleGroup (CFSG.GorensteinWalter.PSL2 F₀) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  exact (IVK.toPSL e).isSimpleGroup

theorem exists_noncomm_of_layer_ne_bot {A : Type} [Group A] (h : layer A ≠ ⊥) :
    ∃ a b : ↥(layer A), a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  have hex : ∃ K : Subgroup A, IsComponent K := by
    by_contra hno
    push Not at hno
    exact h (CFSG.LocalCores.layer_eq_bot_of_forall hno)
  obtain ⟨K, hK⟩ := hex
  have hKle : K ≤ layer A := CFSG.LocalCores.component_le_layer hK
  obtain ⟨-, -, a, b, hab⟩ := hK.1
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  have h1 := hcomm ⟨a, hKle a.2⟩ ⟨b, hKle b.2⟩
  have h2 : (a : A) * b = b * a := congrArg Subtype.val h1
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext h2


section Aux

variable {C : Type} [Group C] [Finite C]

theorem pPrimeCore_eq_bot_of_simple {A : Type} [Group A] [Finite A] (hs : IsSimpleGroup A)
    (hn : ∃ a b : A, a * b ≠ b * a) : pPrimeCore 2 A = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (pPrimeCore 2 A) with h | h
  · exact h
  · exfalso
    have hodd : Odd (Nat.card A) := by
      have := TwoThin.odd_card_pPrimeCore A
      rwa [h, Subgroup.card_top] at this
    have hsolv : Group.IsSolvable A := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    have hperf : Group.IsPerfect A := by
      rcases hs.eq_bot_or_eq_top_of_normal (commutator A) with h' | h'
      · exfalso
        obtain ⟨a, b, hab⟩ := hn
        apply hab
        have hm : ⁅a, b⁆ ∈ commutator A := Subgroup.commutator_mem_commutator (mem_top a) (mem_top b)
        rw [h', Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
        exact hm
      · exact ⟨h'⟩
    exact Group.IsPerfect.not_isSolvable A hsolv

theorem quotient_equiv_of_map {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y] (I' : Subgroup X)
    (f : X →* Y) (Λ : Subgroup Y) (hΛ : I'.map f = Λ) (hker : ¬ 2 ∣ Nat.card f.ker)
    (hcore : pPrimeCore 2 ↥Λ = ⊥) : Nonempty (↥I' ⧸ pPrimeCore 2 ↥I' ≃* ↥Λ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let g0 : ↥I' →* Y := f.comp I'.subtype
  have hg0 : ∀ i : ↥I', g0 i ∈ Λ := fun i => by
    rw [← hΛ]
    exact ⟨i, i.2, rfl⟩
  let g : ↥I' →* ↥Λ := g0.codRestrict Λ hg0
  have hgsurj : Function.Surjective g := by
    rintro ⟨y, hy⟩
    rw [← hΛ] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    exact ⟨⟨i, hi⟩, rfl⟩
  have hgker : ¬ 2 ∣ Nat.card g.ker := by
    have hk : g.ker = f.ker.comap I'.subtype := by
      rw [MonoidHom.ker_codRestrict]
      rfl
    intro h2
    apply hker
    rw [hk] at h2
    exact h2.trans (Subgroup.card_comap_dvd_of_injective f.ker I'.subtype I'.subtype_injective)
  obtain ⟨-, e, -⟩ := CFSG.ComponentClassification.UnbalancingLocal.Correspondence.exists_quotient_equiv_of_coprime_kernel
    (p := 2) g hgsurj hgker hcore
  exact ⟨e⟩

theorem pLayer_eq_map_layer {Y W : Subgroup C} (hn : (W.subgroupOf Y).Normal)
    (hle : pLayer ↥Y 2 ≤ layer ↥Y) (hW : pLayer ↥Y 2 ≤ W.subgroupOf Y) :
    pLayer ↥Y 2 = (layer ↥(W.subgroupOf Y)).map (W.subgroupOf Y).subtype := by
  set W' : Subgroup ↥Y := W.subgroupOf Y with hW'
  have hl : layer ↥Y ≤ W' := (CFSG.GH74.GLS.Stage2.Final.Thm4.layer_le_pLayer).trans hW
  have hEq : layer ↥Y = (layer ↥W').map W'.subtype := by
    apply le_antisymm
    · refine sSup_le fun K hK => ?_
      have hKW : K ≤ W' := (CFSG.LocalCores.component_le_layer hK).trans hl
      have hKc : IsComponent (K.subgroupOf W') := isComponent_subgroupOf hKW hK
      have h := CFSG.LocalCores.component_le_layer hKc
      rw [← Subgroup.map_subgroupOf_eq_of_le hKW]
      exact Subgroup.map_mono h
    · have : W'.Normal := hn
      exact map_layer_le_layer_of_normal
  apply le_antisymm (hle.trans hEq.le)
  rw [← hEq]
  exact CFSG.GH74.GLS.Stage2.Final.Thm4.layer_le_pLayer

theorem simple_pLayer {Y W : Subgroup C} (hWY : W ≤ Y) (hn : (W.subgroupOf Y).Normal)
    (hle : pLayer ↥Y 2 ≤ layer ↥Y) (hW : pLayer ↥Y 2 ≤ W.subgroupOf Y)
    (hs : IsSimpleGroup ↥(layer ↥W)) (hnc : ∃ a b : ↥(layer ↥W), a * b ≠ b * a) :
    IsSimpleGroup ↥(pLayer ↥Y 2) ∧ ∃ a b : ↥(pLayer ↥Y 2), a * b ≠ b * a := by
  have hΛ := pLayer_eq_map_layer hn hle hW
  set W' : Subgroup ↥Y := W.subgroupOf Y with hW'
  let e1 : ↥(pLayer ↥Y 2) ≃* ↥(layer ↥W') :=
    (MulEquiv.subgroupCongr hΛ).trans
      ((layer ↥W').equivMapOfInjective W'.subtype W'.subtype_injective).symm
  let e : ↥W' ≃* ↥W := Subgroup.subgroupOfEquivOfLe hWY
  have hlayer : (layer ↥W').map e.toMonoidHom = layer ↥W := layer_map_mulEquiv e
  let e2 : ↥(layer ↥W') ≃* ↥(layer ↥W) :=
    ((layer ↥W').equivMapOfInjective e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr hlayer)
  let eΛ : ↥(pLayer ↥Y 2) ≃* ↥(layer ↥W) := e1.trans e2
  refine ⟨eΛ.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hnc
  exact ⟨eΛ.symm a, eΛ.symm b, fun h => hab (by simpa using congrArg eΛ h)⟩

end Aux

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem Iof_quotient_simple (hB2 : B_B2_g4) (ctx : Stage2Ctx G z k S) {q : ℕ}
    {L₁ L₂ : Subgroup (CentralizerBar z)} {x : G} (hpair : Stage1Pair G z S q L₁ L₂)
    (htwo : TwoClassData G z S L₁ L₂ q x) {t : G} (htS : t ∈ S) (htc : IsConj z t)
    (hts : Swaps z t L₁ L₂) (hU : IVK.IsFourSubgroup (zpowers z ⊔ zpowers t)) :
    IsSimpleGroup (↥(Iof (zpowers z ⊔ zpowers t)) ⧸ pPrimeCore 2 ↥(Iof (zpowers z ⊔ zpowers t))) ∧
      ∃ a b : ↥(Iof (zpowers z ⊔ zpowers t)) ⧸ pPrimeCore 2 ↥(Iof (zpowers z ⊔ zpowers t)),
        a * b ≠ b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : orderOf z = 2 := ctx.orderOf_z
  have hSC : S ≤ Cen z := ctx.S_le_Cen
  have htC : t ∈ Cen z := hSC htS
  have hzU : z ∈ (zpowers z ⊔ zpowers t : Subgroup G) := mem_sup_left'
  have htU : t ∈ (zpowers z ⊔ zpowers t : Subgroup G) := mem_sup_right'
  have hzt : z * t = t * z := mul_comm_of_isFour hU hzU htU
  have ht2 : t * t = 1 := sq_eq_one_of_isFour hU htU
  have ht2o : orderOf t = 2 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 htc
    rw [← hc, orderOf_conj_eq]
    exact hz2
  obtain ⟨f, hfsurj, hker, hfx⟩ := exists_fXY hzt ht2 htC
  have hker' : ¬ 2 ∣ Nat.card f.ker := fun h2 =>
    (Nat.not_even_iff_odd.mpr hker) (even_iff_two_dvd.mpr h2)
  have hmap : (pLayer ↥(XU z t) 2).map f = pLayer ↥(YU z t htC) 2 :=
    CFSG.ComponentClassification.UnbalancingLocal.Correspondence.map_pLayer_of_coprime_kernel
      (p := 2) f hfsurj hker'
  obtain ⟨hKC, hg4C, hcoreC⟩ := cenBar_facts ctx.std.kps ctx.std.gen4 hz2
  have hs : orderOf (toBar z ⟨t, htC⟩) = 2 := orderOf_barMk (orderOf_mk_centralizer htC ht2o)
  have hΛle : pLayer ↥(YU z t htC) 2 ≤ layer ↥(YU z t htC) := by
    refine sSup_le fun J hJ => ?_
    exact CFSG.LocalCores.component_le_layer (isComponent_of_B2' hB2 hg4C hKC hcoreC hs J hJ)
  have hlayerCb : layer (CentralizerBar z) = LBar z := by
    simp only [CFSG.layer.eq_sSup]
    rw [hpair.comps, sSup_pair]
    exact hpair.prod.1
  have hKX : ∀ K : Subgroup G, IsPCompIn 2 (XU z t) K →
      IsPCompIn 2 (centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G)) K := fun K hK => by
    rwa [XU_eq hzt] at hK
  have hbal : (pLayer ↥(XU z t) 2).map (((YU z t htC).subtype).comp f) ≤ LBar z := by
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun L hL => ?_
    have hKJ : (L.map (XU z t).subtype).subgroupOf (XU z t) = L :=
      Subgroup.comap_map_eq_self_of_injective (XU z t).subtype_injective L
    have hK := hKX _ ⟨Subgroup.map_subtype_le L, by rw [hKJ]; exact hL⟩
    have hb := barOf_le_layer hzt ht2o hK
    rw [hlayerCb] at hb
    intro l hl
    show ((f l : ↥(YU z t htC)) : CentralizerBar z) ∈ LBar z
    rw [hfx l (XU_le_Cen l.2)]
    exact hb ⟨⟨l, XU_le_Cen l.2⟩, ⟨l, hl, rfl⟩, rfl⟩
  have hbarmem : toBar z ⟨t, htC⟩ ∈ barOf z (zpowers t) :=
    ⟨⟨t, htC⟩, Subgroup.mem_subgroupOf.mpr (mem_zpowers t), rfl⟩
  have hcentbar : centralizer ((barOf z (zpowers t) : Subgroup (CentralizerBar z)) : Set (CentralizerBar z)) =
      YU z t htC := by
    ext c
    constructor
    · intro hc
      exact Subgroup.mem_centralizer_singleton_iff.mpr ((Subgroup.mem_centralizer_iff.mp hc _ hbarmem).symm)
    · intro hc
      refine Subgroup.mem_centralizer_iff.mpr fun b hb => ?_
      obtain ⟨n, rfl⟩ := exists_zpow_of_mem_barOf htC hb
      have hc' : c * toBar z ⟨t, htC⟩ = toBar z ⟨t, htC⟩ * c := Subgroup.mem_centralizer_singleton_iff.mp hc
      exact ((Commute.zpow_left (show Commute (toBar z ⟨t, htC⟩) c from hc'.symm) n).eq)
  have hCL : CL z t = LBar z ⊓ YU z t htC := by
    unfold CL
    rw [hcentbar]
  have hWY : CL z t ≤ YU z t htC := by rw [hCL]; exact inf_le_right
  have hnorm : ((CL z t).subgroupOf (YU z t htC)).Normal := by
    rw [hCL, Subgroup.inf_subgroupOf_right]
    exact (LBar_normal z).subgroupOf _
  have hW : pLayer ↥(YU z t htC) 2 ≤ (CL z t).subgroupOf (YU z t htC) := by
    intro y hy
    rw [← hmap] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    show ((f i : ↥(YU z t htC)) : CentralizerBar z) ∈ CL z t
    rw [hCL]
    exact ⟨hbal ⟨i, hi, rfl⟩, (f i).2⟩
  obtain ⟨-, hL2, -⟩ := htwo.swap_conseq t htS htc hts
  have hsimple : IsSimpleGroup ↥(layer ↥(CL z t)) := isSimple_of_isL2 hpair.gt3 hL2
  have hneW : layer ↥(CL z t) ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).mp hsimple.toNontrivial
  have hΛsimp := simple_pLayer hWY hnorm hΛle hW hsimple (exists_noncomm_of_layer_ne_bot hneW)
  have hcore : pPrimeCore 2 ↥(pLayer ↥(YU z t htC) 2) = ⊥ :=
    pPrimeCore_eq_bot_of_simple hΛsimp.1 hΛsimp.2
  have hI : Iof (zpowers z ⊔ zpowers t) = (pLayer ↥(XU z t) 2).map (XU z t).subtype :=
    CFSG.GH74.GLS.Stage2.Final.Thm4.pLayerOf_eq_map 2 (XU z t)
  let eI : ↥(Iof (zpowers z ⊔ zpowers t)) ≃* ↥(pLayer ↥(XU z t) 2) :=
    (MulEquiv.subgroupCongr hI).trans
      ((pLayer ↥(XU z t) 2).equivMapOfInjective (XU z t).subtype (XU z t).subtype_injective).symm
  let ePC := CFSG.ComponentClassification.UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 eI
  obtain ⟨eQ⟩ := quotient_equiv_of_map (pLayer ↥(XU z t) 2) f (pLayer ↥(YU z t htC) 2) hmap hker' hcore
  let E := ePC.trans eQ
  have := hΛsimp.1
  refine ⟨E.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := hΛsimp.2
  exact ⟨E.symm a, E.symm b, fun h => hab (by simpa using congrArg E h)⟩

end Main

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L102
