module

public import CFSG.CGT.PushingUpLit.Section6
public import CFSG.CGT.PushingUp.TwoLocals
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBaumannTools
public import CFSG.Quasithin.SteinbergBQThompsonSeedBaumannCentralizer
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalBridge
import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp

section Iso

variable {L L' : Type*} [Group L] [Group L']

theorem map_shortU_mulEquiv (e : L ≃* L') : (shortU L).map e.toMonoidHom = shortU L' := by
  unfold shortU
  rw [Subgroup.map_commutator, CFSG.pCore_map_iso 2 e,
    Subgroup.map_top_of_surjective _ e.surjective]

theorem map_shortC_mulEquiv (e : L ≃* L') : (shortC L).map e.toMonoidHom = shortC L' := by
  unfold shortC
  rw [Subgroup.map_inf_eq _ _ e.toMonoidHom e.injective, map_shortU_mulEquiv]
  congr 1
  exact Subgroup.map_center_eq e

theorem mem_shortU_iff (e : L ≃* L') (x : L) : e x ∈ shortU L' ↔ x ∈ shortU L := by
  rw [← map_shortU_mulEquiv e]
  exact Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective

theorem mem_shortC_iff (e : L ≃* L') (x : L) : e x ∈ shortC L' ↔ x ∈ shortC L := by
  rw [← map_shortC_mulEquiv e]
  exact Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective

theorem map_generalizedFitting_mulEquiv (e : L ≃* L') :
    (generalizedFitting L).map e.toMonoidHom = generalizedFitting L' :=
  CFSG.WholeGroup.generalizedFitting_map_mulEquiv e

theorem map_center_subtype_mulEquiv (e : L ≃* L') {P : Subgroup L} {P' : Subgroup L'}
    (hP : P.map e.toMonoidHom = P') :
    ((Subgroup.center ↥P).map P.subtype).map e.toMonoidHom =
      (Subgroup.center ↥P').map P'.subtype := by
  let eP : ↥P ≃* ↥P' := (e.subgroupMap P).trans (MulEquiv.subgroupCongr hP)
  have hcomp : e.toMonoidHom.comp P.subtype = P'.subtype.comp eP.toMonoidHom := by
    ext x
    rfl
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map]
  congr 1
  exact Subgroup.map_center_eq eP

theorem oResidualTwo_eq_top_of_mulEquiv (e : L ≃* L') (h : oResidualTwo L = ⊤) :
    oResidualTwo L' = ⊤ := by
  unfold oResidualTwo at h ⊢
  rw [sInf_eq_top] at h ⊢
  rintro N' ⟨hN', hq'⟩
  have hN : (N'.comap e.toMonoidHom).Normal := hN'.comap _
  have hmc : (N'.comap e.toMonoidHom).map e.toMonoidHom = N' :=
    Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective N'
  let q : L ⧸ N'.comap e.toMonoidHom ≃* L' ⧸ N' := QuotientGroup.congr _ _ e hmc
  have hq : IsPGroup 2 (L ⧸ N'.comap e.toMonoidHom) := hq'.of_equiv q.symm
  have h1 := h _ ⟨hN, hq⟩
  rw [← hmc, h1, Subgroup.map_top_of_surjective _ e.surjective]

@[expose] def quotPCoreEquiv (e : L ≃* L') : (L ⧸ pCore 2 L) ≃* (L' ⧸ pCore 2 L') :=
  QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)

theorem quotPCoreEquiv_mk (e : L ≃* L') (l : L) :
    quotPCoreEquiv e (l : L ⧸ pCore 2 L) = ((e l : L') : L' ⧸ pCore 2 L') := rfl

@[expose] def shortUEquiv (e : L ≃* L') : ↥(shortU L) ≃* ↥(shortU L') :=
  (e.subgroupMap (shortU L)).trans (MulEquiv.subgroupCongr (map_shortU_mulEquiv e))

@[simp] theorem coe_shortUEquiv (e : L ≃* L') (x : ↥(shortU L)) :
    ((shortUEquiv e x : ↥(shortU L')) : L') = e (x : L) := rfl

@[simp] theorem coe_shortUEquiv_symm (e : L ≃* L') (x : ↥(shortU L')) :
    (((shortUEquiv e).symm x : ↥(shortU L)) : L) = e.symm (x : L') := rfl

theorem ker_comp_shortUEquiv_symm {M : Type*} [Group M] (e : L ≃* L') (ψ : ↥(shortU L) →* M)
    (h : ψ.ker = (shortC L).subgroupOf (shortU L)) :
    (ψ.comp (shortUEquiv e).symm.toMonoidHom).ker = (shortC L').subgroupOf (shortU L') := by
  ext x
  have h1 : ψ ((shortUEquiv e).symm x) = 1 ↔ ((shortUEquiv e).symm x : L) ∈ shortC L := by
    rw [← MonoidHom.mem_ker, h, Subgroup.mem_subgroupOf]
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    h1, coe_shortUEquiv_symm]
  have h2 := mem_shortC_iff e (e.symm (x : L'))
  rw [MulEquiv.apply_symm_apply] at h2
  exact h2.symm

theorem transport_equivariance {A M : Type*} [Group A] [Group M] (e : L ≃* L')
    (φ : (L ⧸ pCore 2 L) ≃* A) (ψ : ↥(shortU L) →* M) (act : A → M → M)
    (h : ∀ (l u : L) (hu : u ∈ shortU L) (hu' : l * u * l⁻¹ ∈ shortU L),
      ψ ⟨l * u * l⁻¹, hu'⟩ = act (φ (l : L ⧸ pCore 2 L)) (ψ ⟨u, hu⟩)) :
    ∀ (l u : L') (hu : u ∈ shortU L') (hu' : l * u * l⁻¹ ∈ shortU L'),
      (ψ.comp (shortUEquiv e).symm.toMonoidHom) ⟨l * u * l⁻¹, hu'⟩ =
        act (((quotPCoreEquiv e).symm.trans φ) (l : L' ⧸ pCore 2 L'))
          ((ψ.comp (shortUEquiv e).symm.toMonoidHom) ⟨u, hu⟩) := by
  intro l u hu hu'
  have hu₀ : e.symm u ∈ shortU L := by
    have := mem_shortU_iff e (e.symm u)
    rw [MulEquiv.apply_symm_apply] at this
    exact this.mp hu
  have hu₀' : e.symm l * e.symm u * (e.symm l)⁻¹ ∈ shortU L := by
    have := mem_shortU_iff e (e.symm l * e.symm u * (e.symm l)⁻¹)
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply] at this
    exact this.mp hu'
  have hl : (quotPCoreEquiv e).symm (l : L' ⧸ pCore 2 L') = ((e.symm l : L) : L ⧸ pCore 2 L) := by
    apply (quotPCoreEquiv e).injective
    rw [MulEquiv.apply_symm_apply, quotPCoreEquiv_mk, MulEquiv.apply_symm_apply]
  have e1 : (shortUEquiv e).symm ⟨l * u * l⁻¹, hu'⟩ =
      ⟨e.symm l * e.symm u * (e.symm l)⁻¹, hu₀'⟩ :=
    Subtype.ext (by simp)
  have e2 : (shortUEquiv e).symm ⟨u, hu⟩ = ⟨e.symm u, hu₀⟩ := Subtype.ext rfl
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e1, e2, MulEquiv.trans_apply, hl]
  exact h _ _ hu₀ hu₀'

end Iso

section IsoFinite

variable {L L' : Type} [Group L] [Group L']

theorem IsNaturalAltModule.of_mulEquiv (e : L ≃* L') {n : ℕ} (h : IsNaturalAltModule L n) :
    IsNaturalAltModule L' n := by
  obtain ⟨φ, ψ, h1, h2, h3, h4⟩ := h
  refine ⟨(quotPCoreEquiv e).symm.trans φ, ψ.comp (shortUEquiv e).symm.toMonoidHom,
    fun u => h1 _, ?_, ker_comp_shortUEquiv_symm e ψ h3, ?_⟩
  · intro v hv
    obtain ⟨u, hu⟩ := h2 v hv
    exact ⟨shortUEquiv e u, by simpa using hu⟩
  · exact transport_equivariance e φ ψ
      (fun g m => Multiplicative.ofAdd (permActionTwo (g : Equiv.Perm (Fin (2 * n + 1)))
        (Multiplicative.toAdd m))) h4

theorem IsNaturalSLTwoModule.of_mulEquiv (e : L ≃* L') {n : ℕ} (h : IsNaturalSLTwoModule L n) :
    IsNaturalSLTwoModule L' n := by
  obtain ⟨φ, ψ, h1, h2, h3⟩ := h
  refine ⟨(quotPCoreEquiv e).symm.trans φ, ψ.comp (shortUEquiv e).symm.toMonoidHom,
    h1.comp (shortUEquiv e).symm.surjective, ker_comp_shortUEquiv_symm e ψ h2, ?_⟩
  exact transport_equivariance e φ ψ
    (fun g m => Multiplicative.ofAdd
      ((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (Multiplicative.toAdd m))) h3

variable [Finite L] [Finite L']

theorem IsShortGroup.of_mulEquiv (e : L ≃* L') (h : IsShortGroup L) : IsShortGroup L' where
  fitting_eq := by
    have := congrArg (Subgroup.map e.toMonoidHom) h.fitting_eq
    rwa [map_generalizedFitting_mulEquiv, CFSG.pCore_map_iso] at this
  residual_eq := oResidualTwo_eq_top_of_mulEquiv e h.residual_eq
  quotient_type := by
    rcases h.quotient_type with hq | hp
    · exact Or.inl (CFSG.LocalCores.isQuasisimple_of_mulEquiv (quotPCoreEquiv e) hq)
    · exact Or.inr (by rwa [← Nat.card_congr (quotPCoreEquiv e).toEquiv])
  U_le_center := by
    rw [← map_center_subtype_mulEquiv e (CFSG.pCore_map_iso 2 e), ← map_shortU_mulEquiv e]
    exact Subgroup.map_mono h.U_le_center
  nonzero := by
    rw [← map_shortC_mulEquiv e, ← map_shortU_mulEquiv e]
    exact (Subgroup.map_lt_map_iff_of_injective (f := e.toMonoidHom) e.injective).mpr h.nonzero
  irreducible := by
    intro N' hN' hNU hCN
    have hN : (N'.comap e.toMonoidHom).Normal := hN'.comap _
    have h1 : N'.comap e.toMonoidHom ≤ shortU L := fun x hx => (mem_shortU_iff e x).mp (hNU hx)
    have h2 : shortC L ≤ N'.comap e.toMonoidHom := fun x hx =>
      hCN ((mem_shortC_iff e x).mpr hx)
    rcases h.irreducible _ hN h1 h2 with h3 | h3
    · left
      ext y
      obtain ⟨x, rfl⟩ := e.surjective y
      have hx : x ∈ N'.comap e.toMonoidHom ↔ x ∈ shortC L := by rw [h3]
      exact Subgroup.mem_comap.symm.trans (hx.trans (mem_shortC_iff e x).symm)
    · right
      ext y
      obtain ⟨x, rfl⟩ := e.surjective y
      have hx : x ∈ N'.comap e.toMonoidHom ↔ x ∈ shortU L := by rw [h3]
      exact Subgroup.mem_comap.symm.trans (hx.trans (mem_shortU_iff e x).symm)

theorem InClassX.of_mulEquiv (e : L ≃* L') (h : InClassX L) : InClassX L' :=
  ⟨IsShortGroup.of_mulEquiv e h.1,
    h.2.imp (fun ⟨n, hn, hm⟩ => ⟨n, hn, IsNaturalAltModule.of_mulEquiv e hm⟩)
      (fun ⟨n, hn, hm⟩ => ⟨n, hn, IsNaturalSLTwoModule.of_mulEquiv e hm⟩)⟩

theorem inClassX_iff_of_mulEquiv (e : L ≃* L') : InClassX L ↔ InClassX L' :=
  ⟨InClassX.of_mulEquiv e, InClassX.of_mulEquiv e.symm⟩

end IsoFinite

section SubgroupOf

variable {G : Type} [Group G] [Finite G] {A K L : Subgroup G}

theorem inClassX_subgroupOf_iff (hLK : L ≤ K) :
    InClassX ↥(L.subgroupOf K) ↔ InClassX ↥L :=
  inClassX_iff_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLK)

theorem isBlockInX_subgroupOf_iff (hLK : L ≤ K) :
    IsBlockInX (L.subgroupOf K) ↔ IsBlockOfInX K L :=
  ⟨fun h => ⟨hLK, h.1, (inClassX_subgroupOf_iff hLK).mp h.2⟩,
    fun h => ⟨h.2.1, (inClassX_subgroupOf_iff hLK).mpr h.2.2⟩⟩

theorem map_inSubgroup_subgroupOf (F : ∀ (X : Type) [Group X], Subgroup X)
    (hF : ∀ {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y] (e : X ≃* Y),
      (F X).map e.toMonoidHom = F Y)
    (hAK : A ≤ K) :
    (inSubgroup F (A.subgroupOf K)).map K.subtype = inSubgroup F A := by
  unfold inSubgroup
  rw [Subgroup.map_map]
  have hcomp : K.subtype.comp (A.subgroupOf K).subtype =
      A.subtype.comp (Subgroup.subgroupOfEquivOfLe hAK).toMonoidHom := by
    ext x
    rfl
  rw [hcomp, ← Subgroup.map_map, hF (Subgroup.subgroupOfEquivOfLe hAK)]

theorem map_oTwoIn_subgroupOf (hAK : A ≤ K) :
    (oTwoIn (A.subgroupOf K)).map K.subtype = oTwoIn A :=
  map_inSubgroup_subgroupOf (fun X _ => pCore 2 X) (fun e => CFSG.pCore_map_iso 2 e) hAK

theorem map_jIn_subgroupOf (hAK : A ≤ K) :
    (jIn (A.subgroupOf K)).map K.subtype = jIn A :=
  map_inSubgroup_subgroupOf (fun X _ => elemThompson X 2)
    (fun e => CFSG.Quasithin.SteinbergBQ.map_elemThompson_mulEquiv e 2) hAK

theorem map_omegaOneCenterIn_subgroupOf (hAK : A ≤ K) :
    (omegaOneCenterIn (A.subgroupOf K)).map K.subtype = omegaOneCenterIn A := by
  have hZ : ((Subgroup.center ↥(A.subgroupOf K)).map (A.subgroupOf K).subtype).map K.subtype =
      (Subgroup.center ↥A).map A.subtype :=
    map_inSubgroup_subgroupOf (fun X _ => Subgroup.center X)
      (fun e => Subgroup.map_center_eq e) hAK
  unfold omegaOneCenterIn
  rw [Sec9B.map_omegaOne K.subtype_injective, hZ]

omit [Finite G] in
theorem coe_mem_centralizer_map {X : Subgroup ↥K} {x : ↥K}
    (hx : x ∈ Subgroup.centralizer (X : Set ↥K)) :
    (x : G) ∈ Subgroup.centralizer ((X.map K.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx y hy)

omit [Finite G] in
theorem map_subtype_centralizer (X : Subgroup ↥K) :
    (Subgroup.centralizer (X : Set ↥K)).map K.subtype =
      Subgroup.centralizer ((X.map K.subtype : Subgroup G) : Set G) ⊓ K := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Subgroup.mem_inf.2 ⟨coe_mem_centralizer_map hx, x.2⟩
  · intro hg
    obtain ⟨hgc, hgK⟩ := Subgroup.mem_inf.1 hg
    refine ⟨⟨g, hgK⟩, Subgroup.mem_centralizer_iff.2 fun y hy => ?_, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hgc (y : G) ⟨y, hy, rfl⟩)

omit [Finite G] in
theorem coe_mem_normalizer_map {X : Subgroup ↥K} {x : ↥K}
    (hx : x ∈ Subgroup.normalizer (X : Set ↥K)) :
    (x : G) ∈ Subgroup.normalizer ((X.map K.subtype : Subgroup G) : Set G) := by
  have h1 : Subgroup.zpowers x ≤ Subgroup.normalizer (X : Set ↥K) :=
    Subgroup.zpowers_le.mpr hx
  exact (Sec9B.map_le_normalizer_map_iff K.subtype_injective).mpr h1
    ⟨x, Subgroup.mem_zpowers x, rfl⟩

theorem map_pushingUpS_subgroupOf (hAK : A ≤ K) :
    (pushingUpS (A.subgroupOf K)).map K.subtype = pushingUpS A := by
  have hE := map_inSubgroup_subgroupOf (fun X _ => elemThompsonCenterTorsion X 2)
    (fun e => CFSG.QuasithinUnique.Setup.Campbell.elemThompsonCenterTorsion_map_mulEquiv e 2) hAK
  unfold pushingUpS
  rw [Subgroup.map_inf_eq _ _ K.subtype K.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hAK, map_subtype_centralizer]
  have hE' : ((inSubgroup (fun X _ => elemThompsonCenterTorsion X 2) (A.subgroupOf K) :
      Subgroup ↥K).map K.subtype : Subgroup G) =
      inSubgroup (fun X _ => elemThompsonCenterTorsion X 2) A := hE
  rw [hE', inf_left_comm, inf_of_le_left hAK, inf_comm]

theorem characteristic_map_mulEquiv_iff {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    {N : Subgroup X} : (N.map e.toMonoidHom).Characteristic ↔ N.Characteristic := by
  refine ⟨fun h => ?_, Sec9B.characteristic_map_mulEquiv e⟩
  have h' := Sec9B.characteristic_map_mulEquiv e.symm h
  rwa [CFSG.LocalCores.map_map_symm e N] at h'

theorem characteristic_pushingUpS_subgroupOf_iff (hAK : A ≤ K) {B : Subgroup G}
    (_hB : B ≤ pushingUpS A) :
    ((B.subgroupOf K).subgroupOf (pushingUpS (A.subgroupOf K))).Characteristic ↔
      (B.subgroupOf (pushingUpS A)).Characteristic := by
  let e : ↥(pushingUpS (A.subgroupOf K)) ≃* ↥(pushingUpS A) :=
    ((pushingUpS (A.subgroupOf K)).equivMapOfInjective K.subtype K.subtype_injective).trans
      (MulEquiv.subgroupCongr (map_pushingUpS_subgroupOf hAK))
  have hmap : ((B.subgroupOf K).subgroupOf (pushingUpS (A.subgroupOf K))).map e.toMonoidHom =
      B.subgroupOf (pushingUpS A) := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    exact (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).trans Iff.rfl
  rw [← hmap]
  exact (characteristic_map_mulEquiv_iff e).symm

omit [Finite G] in
theorem mem_centralizerModCore_iff {X : Subgroup G} {g : G} :
    g ∈ centralizerModCore X ↔
      g ∈ Subgroup.normalizer (X : Set G) ∧ ∀ x ∈ X, g * x * g⁻¹ * x⁻¹ ∈ oTwoIn X :=
  Iff.rfl

theorem map_centralizerModCore_subgroupOf (hAK : A ≤ K) :
    (centralizerModCore (A.subgroupOf K)).map K.subtype = centralizerModCore A ⊓ K := by
  have hO := map_oTwoIn_subgroupOf hAK
  have hA : (A.subgroupOf K).map K.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAK
  ext y
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨hkN, hk'⟩ := mem_centralizerModCore_iff.1 hk
    refine Subgroup.mem_inf.2 ⟨mem_centralizerModCore_iff.2 ⟨?_, ?_⟩, k.2⟩
    · have := coe_mem_normalizer_map hkN
      rwa [hA] at this
    · intro a ha
      rw [← hA] at ha
      obtain ⟨x, hx, rfl⟩ := ha
      rw [← hO]
      exact ⟨k * x * k⁻¹ * x⁻¹, hk' x hx, rfl⟩
  · intro hy
    obtain ⟨hy1, hyK⟩ := Subgroup.mem_inf.1 hy
    obtain ⟨hyN, hy'⟩ := mem_centralizerModCore_iff.1 hy1
    refine ⟨⟨y, hyK⟩, mem_centralizerModCore_iff.2 ⟨?_, ?_⟩, rfl⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro h
      exact Subgroup.mem_normalizer_iff.1 hyN (h : G)
    · intro x hx
      have h1 := hy' (x : G) hx
      rw [← hO] at h1
      obtain ⟨z, hz, hzz⟩ := h1
      have hz' : z = ⟨y, hyK⟩ * x * ⟨y, hyK⟩⁻¹ * x⁻¹ := Subtype.ext hzz
      rwa [← hz']

end SubgroupOf

section Sylow

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem sylow_of_isSylowOf {S H : Subgroup G} (hS : IsSylowOf 2 S H) :
    ∃ T : Sylow 2 ↥H, (T : Subgroup ↥H) = S.subgroupOf H := by
  obtain ⟨hSH, hp, hidx⟩ := hS
  have hp' : IsPGroup 2 (S.subgroupOf H) :=
    hp.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
  exact ⟨hp'.toSylow hidx, IsPGroup.toSylow_coe hp' hidx⟩

omit [Finite G] in
theorem isTwoLocal_iff_isPLocal {H : Subgroup G} :
    CFSG.Assembly.IsTwoLocal H ↔ CFSG.IsPLocal 2 H :=
  Iff.rfl

export CFSG.CGT.PushingUp (isCharacteristicP_of_isPLocal)

end Sylow

section Relative

open CFSG.Assembly (KProper InCatalog)

theorem AschbacherLocalFactorization.relative (h : AschbacherLocalFactorization)
    {G : Type} [Group G] [Finite G] {H S M : Subgroup G}
    (hK : KProper InCatalog ↥H) (hH : CFSG.IsCharacteristicP 2 ↥H) (hS : IsSylowOf 2 S H)
    (hC : Subgroup.centralizer (omegaOneCenterIn S : Set G) ⊓ H ≤ M)
    (hN : ∀ B : Subgroup G, B ≠ ⊥ → B ≤ pushingUpS S →
      (B.subgroupOf (pushingUpS S)).Characteristic → Subgroup.normalizer (B : Set G) ⊓ H ≤ M)
    (hHM : ¬ H ≤ M) :
    ∃ Y : Subgroup G, IsBlockOfInX H Y ∧ ¬ Y ≤ M := by
  obtain ⟨T, hT⟩ := sylow_of_isSylowOf hS
  have hSH : S ≤ H := hS.1
  have hM' : M.subgroupOf H ≠ ⊤ := fun htop => hHM (Subgroup.subgroupOf_eq_top.mp htop)
  have hcore : characteristicCoreStar (T : Subgroup ↥H) ≤ M.subgroupOf H := by
    rw [hT]
    refine sup_le ?_ (iSup_le fun B' => iSup_le fun hB' => ?_)
    · intro x hx
      have hx' := coe_mem_centralizer_map hx
      rw [map_omegaOneCenterIn_subgroupOf hSH] at hx'
      exact hC (Subgroup.mem_inf.2 ⟨hx', x.2⟩)
    · intro x hx
      obtain ⟨hB'0, hB'S, hB'c⟩ := hB'
      have hBS : B'.map H.subtype ≤ pushingUpS S := by
        rw [← map_pushingUpS_subgroupOf hSH]
        exact Subgroup.map_mono hB'S
      have hsub : (B'.map H.subtype).subgroupOf H = B' :=
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective B'
      have hBc : ((B'.map H.subtype).subgroupOf (pushingUpS S)).Characteristic := by
        refine (characteristic_pushingUpS_subgroupOf_iff hSH hBS).mp ?_
        rw [hsub]
        exact hB'c
      have hB0 : B'.map H.subtype ≠ ⊥ := fun hb =>
        hB'0 ((Subgroup.map_eq_bot_iff_of_injective B' H.subtype_injective).mp hb)
      exact hN _ hB0 hBS hBc (Subgroup.mem_inf.2 ⟨coe_mem_normalizer_map hx, x.2⟩)
  obtain ⟨Y', hY', hYM⟩ := h.exists_not_le hK hH T hcore hM'
  have hsub : (Y'.map H.subtype).subgroupOf H = Y' :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective Y'
  refine ⟨Y'.map H.subtype, (isBlockInX_subgroupOf_iff (Subgroup.map_subtype_le Y')).mp ?_, ?_⟩
  · rw [hsub]
    exact hY'.1
  · intro hle
    exact hYM (hsub.symm.le.trans (Subgroup.comap_mono hle))

end Relative

end CFSG.CGT.PushingUpLit
