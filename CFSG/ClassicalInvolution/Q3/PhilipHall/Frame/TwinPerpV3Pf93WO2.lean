module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf46WO2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf11Twin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf8Class
public import CFSG.ClassicalInvolution.SmallCases.A7T22Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

namespace Pf93



section Gen

variable {G : Type} [Group G]

theorem map_mem_RSet_equiv (φ : G ≃* G) {Ω : Set (Subgroup G)}
    (hφ : ∀ J ∈ Ω, J.map φ.toMonoidHom ∈ Ω) {R : Subgroup G} (hR : R ∈ RSet Ω) :
    R.map φ.toMonoidHom ∈ RSet Ω := by
  obtain ⟨J, hJ, hRJ, hR2, hmax⟩ := mem_RSet_iff.mp hR
  refine mem_RSet_iff.mpr ⟨J.map φ.toMonoidHom, hφ J hJ, Subgroup.map_mono hRJ,
    hR2.map _, fun R' hR'J hR'2 hle => ?_⟩
  have h1 : R'.comap φ.toMonoidHom ≤ J := by
    intro x hx
    have := hR'J hx
    obtain ⟨z, hz, hzx⟩ := this
    have : z = x := φ.injective (by simpa using hzx)
    rwa [← this]
  have h2 : IsPGroup 2 (R'.comap φ.toMonoidHom) := hR'2.comap_of_injective _ φ.injective
  have h3 : R ≤ R'.comap φ.toMonoidHom := by
    intro x hx
    exact hle (Subgroup.mem_map_of_mem _ hx)
  have h4 := hmax _ h1 h2 h3
  calc R' = (R'.comap φ.toMonoidHom).map φ.toMonoidHom :=
        (Subgroup.map_comap_eq_self_of_surjective φ.surjective R').symm
    _ = R.map φ.toMonoidHom := by rw [h4]

theorem map_mem_USet_equiv (φ : G ≃* G) {Ω : Set (Subgroup G)}
    (hφ : ∀ J ∈ Ω, J.map φ.toMonoidHom ∈ Ω) {U : Subgroup G} (hU : U ∈ USet Ω) :
    U.map φ.toMonoidHom ∈ USet Ω := by
  obtain ⟨R, hR, hUR, hcyc, hidx⟩ := hU
  refine ⟨R.map φ.toMonoidHom, map_mem_RSet_equiv φ hφ hR, Subgroup.map_mono hUR, ?_, ?_⟩
  · let e := Subgroup.equivMapOfInjective U φ.toMonoidHom φ.injective
    exact (MulEquiv.isCyclic e).mp hcyc
  · rw [Subgroup.relIndex_map_map_of_injective _ _ φ.injective]
    exact hidx

theorem inDistinctMembers_image_equiv (φ : G ≃* G) {Ω : Set (Subgroup G)}
    (hφ' : ∀ J ∈ Ω, J.map φ.symm.toMonoidHom ∈ Ω) {η : Set (Subgroup G)}
    (h : InDistinctMembers Ω η) :
    InDistinctMembers Ω ((fun U => U.map φ.toMonoidHom) '' η) := by
  rintro _ ⟨U, hU, rfl⟩ _ ⟨U', hU', rfl⟩ hne J hJ ⟨h1, h2⟩
  have hne' : U ≠ U' := fun h' => hne (by rw [h'])
  refine h U hU U' hU' hne' (J.map φ.symm.toMonoidHom) (hφ' J hJ) ⟨?_, ?_⟩
  · have := Subgroup.map_mono (f := φ.symm.toMonoidHom) h1
    simpa [Subgroup.map_map] using this
  · have := Subgroup.map_mono (f := φ.symm.toMonoidHom) h2
    simpa [Subgroup.map_map] using this


theorem map_map_symm_equiv (φ : G ≃* G) (U : Subgroup G) :
    (U.map φ.symm.toMonoidHom).map φ.toMonoidHom = U := by
  rw [Subgroup.map_map]
  have : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id G := by
    ext x; simp
  rw [this, Subgroup.map_id]

theorem map_map_equiv_symm (φ : G ≃* G) (U : Subgroup G) :
    (U.map φ.toMonoidHom).map φ.symm.toMonoidHom = U := by
  rw [Subgroup.map_map]
  have : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id G := by
    ext x; simp
  rw [this, Subgroup.map_id]

theorem map_mem_etaSet_equiv (φ : G ≃* G) {Ω : Set (Subgroup G)}
    (hφ : ∀ J ∈ Ω, J.map φ.toMonoidHom ∈ Ω) (hφ' : ∀ J ∈ Ω, J.map φ.symm.toMonoidHom ∈ Ω)
    {S : Subgroup G} {η : Set (Subgroup G)} (h : η ∈ etaSet Ω S) :
    ((fun U => U.map φ.toMonoidHom) '' η) ∈ etaSet Ω (S.map φ.toMonoidHom) := by
  have hinj : Function.Injective (fun U : Subgroup G => U.map φ.toMonoidHom) :=
    Subgroup.map_injective φ.injective
  have hinj' : Function.Injective (fun U : Subgroup G => U.map φ.symm.toMonoidHom) :=
    Subgroup.map_injective φ.symm.injective
  refine ⟨?_, inDistinctMembers_image_equiv φ hφ' h.2.1, fun η' hη' hd => ?_⟩
  · rintro _ ⟨U, hU, rfl⟩
    exact ⟨map_mem_USet_equiv φ hφ (h.1 hU).1, Subgroup.map_mono (h.1 hU).2⟩
  · set η'' : Set (Subgroup G) := (fun U => U.map φ.symm.toMonoidHom) '' η' with hη''
    have hsub : η'' ⊆ {U | U ∈ USet Ω ∧ U ≤ S} := by
      rintro _ ⟨U, hU, rfl⟩
      refine ⟨map_mem_USet_equiv φ.symm hφ' (hη' hU).1, ?_⟩
      have := Subgroup.map_mono (f := φ.symm.toMonoidHom) (hη' hU).2
      rwa [map_map_equiv_symm] at this
    have hd'' : InDistinctMembers Ω η'' :=
      inDistinctMembers_image_equiv φ.symm (by simpa using hφ) hd
    have hle := h.2.2 η'' hsub hd''
    have himg : (fun U => U.map φ.toMonoidHom) '' η'' = η' := by
      ext U
      constructor
      · rintro ⟨_, ⟨V, hV, rfl⟩, rfl⟩
        show (V.map φ.symm.toMonoidHom).map φ.toMonoidHom ∈ η'
        rw [map_map_symm_equiv]
        exact hV
      · intro hU
        exact ⟨_, ⟨U, hU, rfl⟩, map_map_symm_equiv φ U⟩
    have h1 : η'.ncard = η''.ncard := by
      rw [← himg, Set.ncard_image_of_injective _ hinj]
    rw [Set.ncard_image_of_injective _ hinj, h1]
    exact hle


theorem map_mem_WSet_equiv [Finite G] (φ : G ≃* G) {Ω : Set (Subgroup G)}
    (hφ : ∀ J ∈ Ω, J.map φ.toMonoidHom ∈ Ω) (hφ' : ∀ J ∈ Ω, J.map φ.symm.toMonoidHom ∈ Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) : W.map φ.toMonoidHom ∈ WSet Ω := by
  obtain ⟨η, ⟨S, hS, hinv⟩, rfl⟩ := hW
  let S' : Sylow 2 G := Sylow.mapSurjective (f := φ.toMonoidHom) φ.surjective S
  have hS' : (S' : Subgroup G) = (S : Subgroup G).map φ.toMonoidHom :=
    Sylow.coe_mapSurjective (f := φ.toMonoidHom) φ.surjective S
  refine ⟨(fun U => U.map φ.toMonoidHom) '' η, ⟨S', ?_, ?_⟩, ?_⟩
  · rw [hS']
    exact map_mem_etaSet_equiv φ hφ hφ' hS
  · intro s hs U hU
    rw [hS'] at hs
    obtain ⟨s₀, hs₀, rfl⟩ := hs
    obtain ⟨U₀, hU₀, rfl⟩ := hU
    refine ⟨conjSub s₀ U₀, hinv s₀ hs₀ U₀ hU₀, ?_⟩
    exact (conjSub_map φ.toMonoidHom s₀ U₀).symm
  · simp only [Subgroup.map_iSup, iSup_image]


end Gen


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem normal_coreHull (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c)) :
    (coreHull Ω c).Normal :=
  ⟨fun x hx g => by
    have := conj_mem_conjSub (n := g) hx
    rwa [conjSub_coreHull hΩ hc2 g] at this⟩


theorem map_conjNormal_subgroupOf (hΩ : HypOmegaGen Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (g : ↥(Subgroup.centralizer ({c} : Set G))) (L : Subgroup ↥(Subgroup.centralizer ({c} : Set G))) :
    haveI := normal_coreHull hΩ hc2
    (L.subgroupOf (coreHull Ω c)).map (MulAut.conjNormal g : ↥(coreHull Ω c) ≃* ↥(coreHull Ω c)).toMonoidHom =
      (conjSub g L).subgroupOf (coreHull Ω c) := by
  haveI := normal_coreHull hΩ hc2
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    have hx' : (x : ↥(Subgroup.centralizer ({c} : Set G))) ∈ L := hx
    have := conj_mem_conjSub (n := g) hx'
    simpa using this
  · intro hy
    rw [Subgroup.mem_subgroupOf, mem_conjSub_iff] at hy
    have hmem : g⁻¹ * (y : ↥(Subgroup.centralizer ({c} : Set G))) * g ∈ coreHull Ω c := by
      have := (inferInstance : (coreHull Ω c).Normal).conj_mem _ y.2 g⁻¹
      simpa using this
    refine ⟨⟨_, hmem⟩, ?_, ?_⟩
    · exact hy
    · apply Subtype.ext
      show ((MulAut.conjNormal g (⟨_, hmem⟩ : ↥(coreHull Ω c)) : ↥(coreHull Ω c)) : ↥(Subgroup.centralizer ({c} : Set G))) = _
      rw [MulAut.conjNormal_apply]
      simp [mul_assoc]


theorem exists_secAut (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (g : ↥(Subgroup.centralizer ({c} : Set G))) :
    ∃ φ : (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) ≃*
        (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)),
      (∀ x y : ↥(coreHull Ω c),
        (y : ↥(Subgroup.centralizer ({c} : Set G))) =
          g * (x : ↥(Subgroup.centralizer ({c} : Set G))) * g⁻¹ →
        φ (QuotientGroup.mk x) = QuotientGroup.mk y) ∧
      ∀ J ∈ TwinDisc.secFam Ω c, J.map φ.toMonoidHom ∈ TwinDisc.secFam Ω c := by
  haveI := normal_coreHull hΩ hc2
  have hN : (classicalInvolutionOddCore ↥(coreHull Ω c)).map
      ((MulAut.conjNormal g : ↥(coreHull Ω c) ≃* ↥(coreHull Ω c)) :
        ↥(coreHull Ω c) →* ↥(coreHull Ω c)) =
      classicalInvolutionOddCore ↥(coreHull Ω c) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant _
  refine ⟨QuotientGroup.congr _ _ (MulAut.conjNormal g) hN, ?_, ?_⟩
  · intro x y hxy
    rw [QuotientGroup.congr_mk]
    congr 1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    exact hxy.symm
  · intro J hJ
    obtain ⟨M, hM, rfl⟩ := TwinDisc.exists_of_mem_secFam hJ
    have hgC : ((g : ↥(Subgroup.centralizer ({c} : Set G))) : G) ∈ Subgroup.centralizer ({c} : Set G) := g.2
    have hM' : conjSub (g : G) M ∈ Q3NL.tqMembers3 Ω c :=
      Q3NL.conjSub_mem_tqMembers3 hΩ.conjInvariant hgC hM
    suffices h : (TwinDisc.secImg Ω c M).map
        (QuotientGroup.congr _ _ (MulAut.conjNormal g) hN).toMonoidHom = TwinDisc.secImg Ω c (conjSub (g : G) M) from
      h ▸ TwinDisc.secImg_mem_secFam hM'
    unfold TwinDisc.secImg
    rw [Subgroup.map_map]
    have hcomp : (QuotientGroup.congr (classicalInvolutionOddCore ↥(coreHull Ω c))
        (classicalInvolutionOddCore ↥(coreHull Ω c)) (MulAut.conjNormal g) hN).toMonoidHom.comp
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c))) =
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c))).comp
          (MulAut.conjNormal g : ↥(coreHull Ω c) ≃* ↥(coreHull Ω c)).toMonoidHom := by
      ext x
      simp [QuotientGroup.congr_mk]
    rw [hcomp, ← Subgroup.map_map, map_conjNormal_subgroupOf hΩ hc2, conjSub_subgroupOf,
      TwinADescent.conjSub_coreAt hgC]


theorem sec_invariant_of_unique (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {V : Subgroup (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c))}
    (hV : WSet (TwinDisc.secFam Ω c) = {V}) (g : ↥(Subgroup.centralizer ({c} : Set G)))
    (x y : ↥(coreHull Ω c))
    (hy : (y : ↥(Subgroup.centralizer ({c} : Set G))) =
      g * (x : ↥(Subgroup.centralizer ({c} : Set G))) * g⁻¹)
    (hx : (QuotientGroup.mk x : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) ∈ V) :
    (QuotientGroup.mk y : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) ∈ V := by
  obtain ⟨φ, hφ1, hφ2⟩ := exists_secAut hΩ hc2 g
  obtain ⟨φ', hφ1', hφ2'⟩ := exists_secAut hΩ hc2 g⁻¹
  haveI := normal_coreHull hΩ hc2
  have hsymm : φ.symm = φ' := by
    ext z
    obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective z
    rw [MulEquiv.symm_apply_eq]
    set z₁ : ↥(coreHull Ω c) := (MulAut.conjNormal g⁻¹ : ↥(coreHull Ω c) ≃* ↥(coreHull Ω c)) x₀ with hz₁
    have hz₁C : (z₁ : ↥(Subgroup.centralizer ({c} : Set G))) =
        g⁻¹ * (x₀ : ↥(Subgroup.centralizer ({c} : Set G))) * g⁻¹⁻¹ := by
      rw [hz₁, MulAut.conjNormal_apply]
    have h1 : φ' (QuotientGroup.mk x₀) = QuotientGroup.mk z₁ := hφ1' x₀ z₁ hz₁C
    have h2 : φ (QuotientGroup.mk z₁) = QuotientGroup.mk x₀ := by
      refine hφ1 z₁ x₀ ?_
      rw [hz₁C]
      group
    rw [h1, h2]
  have hVW : V ∈ WSet (TwinDisc.secFam Ω c) := by rw [hV]; exact Set.mem_singleton V
  have hmap := map_mem_WSet_equiv φ hφ2 (by rw [hsymm]; exact hφ2') hVW
  rw [hV] at hmap
  have hmap' : V.map φ.toMonoidHom = V := hmap
  have : φ (QuotientGroup.mk x) = QuotientGroup.mk y := hφ1 x y hy
  rw [← this, ← hmap']
  exact Subgroup.mem_map_of_mem _ hx


section Grp

theorem isPGroup_zpowers_of_mul_self {T : Type*} [Group T] {x : T} (h : x * x = 1) :
    IsPGroup 2 (Subgroup.zpowers x) := by
  intro g
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
  refine ⟨1, ?_⟩
  apply Subtype.ext
  show (g : T) ^ 2 ^ 1 = 1
  rw [← hm, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
  have : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact h
  rw [show ((2 : ℕ) : ℤ) = 2 from rfl, this, one_zpow]

theorem isPGroup_two_of_nilpotent_gen {T : Type*} [Group T] [Finite T] [Group.IsNilpotent T]
    (S : Set T) (hS : ∀ x ∈ S, x * x = 1) (hgen : Subgroup.closure S = ⊤) : IsPGroup 2 T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 T) := inferInstance
  have hP : ∀ x ∈ S, x ∈ (P : Subgroup T) := by
    intro x hx
    have h2 : IsPGroup 2 (Subgroup.zpowers x) := isPGroup_zpowers_of_mul_self (hS x hx)
    obtain ⟨Q, hQ⟩ := h2.exists_le_sylow
    haveI : Unique (Sylow 2 T) := Sylow.unique_of_normal P inferInstance
    have : Q = P := Subsingleton.elim _ _
    subst this
    exact hQ (Subgroup.mem_zpowers x)
  have hle : (⊤ : Subgroup T) ≤ P := by
    rw [← hgen, Subgroup.closure_le]
    exact hP
  intro g
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨g, hle (Subgroup.mem_top g)⟩
  exact ⟨k, congrArg Subtype.val hk⟩


theorem isPGroup_two_of_central_ker {T Q : Type*} [Group T] [Finite T] [Group Q] (ρ : T →* Q)
    (hQ : IsPGroup 2 ρ.range) (hker : ρ.ker ≤ Subgroup.center T)
    (S : Set T) (hS : ∀ x ∈ S, x * x = 1) (hgen : Subgroup.closure S = ⊤) : IsPGroup 2 T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ρ.range := Finite.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  haveI : Group.IsNilpotent ρ.range := hQ.isNilpotent
  have hnil : Group.IsNilpotent T := by
    refine isNilpotent_of_ker_le_center ρ.rangeRestrict ?_
    simpa [MonoidHom.ker_rangeRestrict] using hker
  haveI := hnil
  exact isPGroup_two_of_nilpotent_gen S hS hgen


end Grp


theorem conjNormal_mem_oddCore (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (g : ↥(Subgroup.centralizer ({c} : Set G))) {n : ↥(coreHull Ω c)}
    (hn : n ∈ classicalInvolutionOddCore ↥(coreHull Ω c)) :
    haveI := normal_coreHull hΩ hc2
    (MulAut.conjNormal g : ↥(coreHull Ω c) ≃* ↥(coreHull Ω c)) n ∈
      classicalInvolutionOddCore ↥(coreHull Ω c) := by
  haveI := normal_coreHull hΩ hc2
  have hN : (classicalInvolutionOddCore ↥(coreHull Ω c)).map
      ((MulAut.conjNormal g : ↥(coreHull Ω c) ≃* ↥(coreHull Ω c)) :
        ↥(coreHull Ω c) →* ↥(coreHull Ω c)) =
      classicalInvolutionOddCore ↥(coreHull Ω c) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant _
  rw [← hN]
  exact Subgroup.mem_map_of_mem _ hn



end Pf93

section Main

open Pf93

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}


theorem inO2C_of_unique_W (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {J : Subgroup G} {t : G} (hJ : J ∈ Q3NL.tqMembers3 Ω c) (ht : IsUniqueInvolution J t)
    (hcent : ∀ n ∈ oddCoreOf (Subgroup.centralizer ({c} : Set G)), n * t = t * n)
    (hVex : ∃ V₀, WSet (TwinDisc.secFam Ω c) = {V₀}) :
    TwinPerpV3.InO2C t c := by
  obtain ⟨htC, htY, hinv⟩ := TwinDisc.isUniqueInvolution_secImg hΩ hc2 hJ ht
  haveI := normal_coreHull hΩ hc2
  set C := Subgroup.centralizer ({c} : Set G) with hCdef
  set X := coreHull Ω c with hXdef
  set N₀ := classicalInvolutionOddCore ↥X with hN₀def
  obtain ⟨V, hV⟩ := hVex
  set t₁ : ↥C := ⟨t, htC⟩ with ht₁
  set t₂ : ↥X := ⟨t₁, htY⟩ with ht₂
  have htV : (QuotientGroup.mk t₂ : ↥X ⧸ N₀) ∈ V := by
    obtain ⟨W, hW, htW⟩ := TwinPerp.wz_of_hypOmegaGen (TwinDisc.hypOmegaGen_secFam hΩ hc2)
      (TwinDisc.secImg_mem_secFam hJ) hinv
    rw [hV] at hW
    have : W = V := hW
    rwa [this] at htW
  have ht₂sq : t₂ * t₂ = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact ht.sq
  set S₀ : Set ↥X := Set.range (fun g : ↥C => (MulAut.conjNormal g : ↥X ≃* ↥X) t₂) with hS₀
  set T₀ : Subgroup ↥X := Subgroup.closure S₀ with hT₀
  have hS₀sq : ∀ x ∈ S₀, x * x = 1 := by
    rintro _ ⟨g, rfl⟩
    rw [← map_mul, ht₂sq, map_one]
  have hT₀V : ∀ x ∈ T₀, (QuotientGroup.mk x : ↥X ⧸ N₀) ∈ V := by
    intro x hx
    have : T₀ ≤ V.comap (QuotientGroup.mk' N₀) := by
      rw [hT₀, Subgroup.closure_le]
      rintro _ ⟨g, rfl⟩
      exact sec_invariant_of_unique hΩ hc2 hV g t₂ _ (by rw [MulAut.conjNormal_apply]) htV
    exact this hx
  have hcentN : ∀ g : ↥C, ∀ n ∈ N₀,
      (MulAut.conjNormal g : ↥X ≃* ↥X) t₂ * n = n * (MulAut.conjNormal g : ↥X ≃* ↥X) t₂ := by
    intro g n hn
    set n' : ↥X := (MulAut.conjNormal g⁻¹ : ↥X ≃* ↥X) n with hn'
    have hn'N : n' ∈ N₀ := conjNormal_mem_oddCore hΩ hc2 g⁻¹ hn
    have hnn' : (MulAut.conjNormal g : ↥X ≃* ↥X) n' = n := by
      rw [hn', ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    have h1 : n' * t₂ = t₂ * n' := by
      have h0 := hcent _ (TwinDisc.oddCore_coreHull_le hΩ hc2 hn'N)
      apply Subtype.ext
      apply Subtype.ext
      exact h0
    rw [← hnn', ← map_mul, ← map_mul, h1]
  have hT₀cent : T₀ ≤ Subgroup.centralizer (N₀ : Set ↥X) := by
    rw [hT₀, Subgroup.closure_le]
    rintro _ ⟨g, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro n hn
    exact (hcentN g n hn).symm
  have hT₀inv : ∀ h : ↥C, ∀ x ∈ T₀, (MulAut.conjNormal h : ↥X ≃* ↥X) x ∈ T₀ := by
    intro h x hx
    have : T₀ ≤ T₀.comap ((MulAut.conjNormal h : ↥X ≃* ↥X) : ↥X →* ↥X) := by
      rw [hT₀, Subgroup.closure_le]
      rintro _ ⟨g, rfl⟩
      show (MulAut.conjNormal h : ↥X ≃* ↥X) ((MulAut.conjNormal g : ↥X ≃* ↥X) t₂) ∈ T₀
      rw [← MulAut.mul_apply, ← map_mul]
      exact Subgroup.subset_closure ⟨h * g, rfl⟩
    exact this hx
  let ρ : ↥T₀ →* (↥X ⧸ N₀) := (QuotientGroup.mk' N₀).comp T₀.subtype
  have hρV : ρ.range ≤ V := by
    rintro _ ⟨y, rfl⟩
    exact hT₀V y y.2
  have hV2 : IsPGroup 2 V := Thompson.isPGroup_of_mem_WSet (by rw [hV]; exact Set.mem_singleton V)
  have hρ2 : IsPGroup 2 ρ.range := hV2.to_le hρV
  have hker : ρ.ker ≤ Subgroup.center ↥T₀ := by
    intro y hy
    have hyN : (y : ↥X) ∈ N₀ := (QuotientGroup.eq_one_iff _).mp hy
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hT₀cent z.2) (y : ↥X) hyN).symm
  have hS : ∀ x ∈ (Subtype.val ⁻¹' S₀ : Set ↥T₀), x * x = 1 := by
    intro x hx
    apply Subtype.ext
    exact hS₀sq _ hx
  have hgen : Subgroup.closure (Subtype.val ⁻¹' S₀ : Set ↥T₀) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  have hT2 : IsPGroup 2 ↥T₀ := isPGroup_two_of_central_ker ρ hρ2 hker _ hS hgen
  have ht₂T : t₂ ∈ T₀ := Subgroup.subset_closure ⟨1, by simp⟩
  refine ⟨(T₀.map X.subtype).map C.subtype, Subgroup.map_subtype_le _, ?_,
    (hT2.map X.subtype).map C.subtype, ⟨t₁, ⟨t₂, ht₂T, rfl⟩, rfl⟩⟩
  have hsub : ((T₀.map X.subtype).map C.subtype).subgroupOf C = T₀.map X.subtype :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  rw [hsub]
  refine ⟨fun a ha h => ?_⟩
  obtain ⟨x, hx, rfl⟩ := ha
  exact ⟨_, hT₀inv h x hx, by simp [MulAut.conjNormal_apply]⟩



theorem v3ExitWO2Core_proved (n : ℕ) : V3ExitWO2Core n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ hin hV
  obtain ⟨hStd, -, hα, -, -⟩ := hin
  have hd := hStd.datum
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.sq_12
  have hcent : ∀ m ∈ oddCoreOf (Subgroup.centralizer ({u₁ * u₂} : Set Y)), m * t = t * m := by
    intro m hm
    have hne : u₁ * u₂ ≠ 1 := hd.mul_ne_one
    have hle : ⁅oddCoreOf (Subgroup.centralizer ({u₁ * u₂} : Set Y)),
        Subgroup.closure ({u₁ * u₂, t} : Set Y)⁆ ≤
        alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set Y)) :=
      le_sup_of_le_left (le_iSup₂_of_le (u₁ * u₂) (Subgroup.subset_closure (by simp))
        (le_iSup_of_le hne le_rfl))
    have h1 : ⁅m, t⁆ ∈ alphaOf (Subgroup.closure ({u₁ * u₂, t} : Set Y)) :=
      hle (Subgroup.commutator_mem_commutator hm (Subgroup.subset_closure (by simp)))
    rw [hα, Subgroup.mem_bot, commutatorElement_def] at h1
    calc m * t = (m * t * m⁻¹ * t⁻¹) * (t * m) := by group
      _ = t * m := by rw [h1, one_mul]
  exact inO2C_of_unique_W hd.hyp hc2 (tq_of_hyp22G hd) hd.hzK₃ hcent hV

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
