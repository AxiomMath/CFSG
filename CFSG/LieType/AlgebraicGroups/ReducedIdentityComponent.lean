module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Vanishing
public import CFSG.ThirdParty.TauCeti.HopfIdealNormalRationalPoint
public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import Mathlib.RingTheory.HopkinsLevitzki

public noncomputable section

open WithConv
open CategoryTheory
open scoped TensorProduct

universe u

namespace CFSG.LieType.AlgebraicGroups.ReductiveDescent

variable {k : Type u} [Field k] [IsAlgClosed k]

theorem map_identityComponentHopfIdeal_eq_self
    {R : Type u} [CommRing R] [HopfAlgebra k R] [Algebra.FiniteType k R]
    (E : R ≃ₐc[k] R) :
    Ideal.map (E.toAlgEquiv.toRingEquiv : R →+* R)
      (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := R)).toIdeal =
      (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := R)).toIdeal := by
  let _ : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let _ : LocallyConnectedSpace (PrimeSpectrum R) := inferInstance
  let z : PrimeSpectrum R := TauCeti.AlgHom.kernelPoint (Bialgebra.counitAlgHom k R)
  rw [TauCeti.HopfAlgebra.identityComponentHopfIdeal_toIdeal]
  change Ideal.map (E.toAlgEquiv.toRingEquiv : R →+* R)
      (PrimeSpectrum.connectedComponentIdeal z) =
    PrimeSpectrum.connectedComponentIdeal z
  have hfix : PrimeSpectrum.comap (E.symm.toAlgEquiv.toRingEquiv : R →+* R) z = z := by
    have h := TauCeti.AlgHom.comap_kernelPoint (Bialgebra.counitAlgHom k R)
      (E.symm.toAlgEquiv : R →ₐ[k] R)
    have hcomp : (Bialgebra.counitAlgHom k R).comp (E.symm.toAlgEquiv : R →ₐ[k] R) =
        Bialgebra.counitAlgHom k R := by
      ext x
      exact CoalgHomClass.counit_comp_apply E.symm x
    have hfix' : PrimeSpectrum.comap (E.symm.toAlgEquiv.toRingEquiv : R →+* R)
        (TauCeti.AlgHom.kernelPoint (Bialgebra.counitAlgHom k R)) =
        TauCeti.AlgHom.kernelPoint (Bialgebra.counitAlgHom k R) :=
      h.trans (congrArg _ hcomp)
    exact hfix'
  calc Ideal.map (E.toAlgEquiv.toRingEquiv : R →+* R)
        (PrimeSpectrum.connectedComponentIdeal z)
      = PrimeSpectrum.connectedComponentIdeal
          (PrimeSpectrum.comap (E.symm.toAlgEquiv.toRingEquiv : R →+* R) z) :=
        PrimeSpectrum.map_connectedComponentIdeal _ _
    _ = PrimeSpectrum.connectedComponentIdeal z := congrArg _ hfix

theorem conjugate_vanishingIdeal_identityComponentPoints_eq
    {R : Type u} [CommRing R] [HopfAlgebra k R] [Algebra.FiniteType k R]
    (E : R ≃ₐc[k] R) :
    let S : Subgroup (WithConv (R →ₐ[k] k)) :=
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k R)
        (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := R))
        (CommAlgCat.of k k)
    (TauCeti.HopfIdeal.vanishingIdeal S).comapOfSurjective E.toBialgHom
        (by
          simpa only [BialgEquiv.toBialgHom_eq_coe, BialgEquiv.coe_toBialgHom] using
            EquivLike.surjective E) =
      TauCeti.HopfIdeal.vanishingIdeal S := by
  intro S
  let IC := TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := R)
  have hmap : Ideal.map (E.toAlgEquiv.toRingEquiv : R →+* R) IC.toIdeal = IC.toIdeal :=
    map_identityComponentHopfIdeal_eq_self E
  have hmap_symm : Ideal.map (E.symm.toAlgEquiv.toRingEquiv : R →+* R) IC.toIdeal =
      IC.toIdeal := map_identityComponentHopfIdeal_eq_self E.symm
  have hS : ∀ g : WithConv (R →ₐ[k] k),
      WithConv.toConv (g.ofConv.comp E.toBialgHom.toAlgHom) ∈ S ↔ g ∈ S := by
    intro g
    rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff,
      TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    constructor
    · intro h y hy
      have hy' : (E.symm.toAlgEquiv.toRingEquiv : R →+* R) y ∈ IC.toIdeal := by
        rw [← hmap_symm]
        exact Ideal.mem_map_of_mem _ hy
      have := h _ hy'
      simpa using this
    · intro h y hy
      have hy' : (E.toAlgEquiv.toRingEquiv : R →+* R) y ∈ IC.toIdeal := by
        rw [← hmap]
        exact Ideal.mem_map_of_mem _ hy
      exact h _ hy'
  have hS_symm : ∀ g : WithConv (R →ₐ[k] k),
      WithConv.toConv (g.ofConv.comp E.symm.toBialgHom.toAlgHom) ∈ S ↔ g ∈ S := by
    intro g
    rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff,
      TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    constructor
    · intro h y hy
      have hy' : (E.toAlgEquiv.toRingEquiv : R →+* R) y ∈ IC.toIdeal := by
        rw [← hmap]
        exact Ideal.mem_map_of_mem _ hy
      have := h _ hy'
      simpa using this
    · intro h y hy
      have hy' : (E.symm.toAlgEquiv.toRingEquiv : R →+* R) y ∈ IC.toIdeal := by
        rw [← hmap_symm]
        exact Ideal.mem_map_of_mem _ hy
      exact h _ hy'
  apply le_antisymm
  · intro x hx
    rw [TauCeti.HopfIdeal.mem_comapOfSurjective] at hx
    rw [TauCeti.HopfIdeal.mem_vanishingIdeal]
    intro g
    have hg' : WithConv.toConv (g.val.ofConv.comp E.symm.toBialgHom.toAlgHom) ∈ S :=
      (hS_symm g.val).mpr g.property
    have h := (TauCeti.HopfIdeal.mem_vanishingIdeal S (E x)).mp hx ⟨_, hg'⟩
    simpa using h
  · intro x hx
    rw [TauCeti.HopfIdeal.mem_comapOfSurjective]
    rw [TauCeti.HopfIdeal.mem_vanishingIdeal]
    intro g
    have hg' : WithConv.toConv (g.val.ofConv.comp E.toBialgHom.toAlgHom) ∈ S :=
      (hS g.val).mpr g.property
    exact (TauCeti.HopfIdeal.mem_vanishingIdeal S x).mp hx ⟨_, hg'⟩

noncomputable local instance componentGroupPointsGroup
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) :
    Group ↑(TauCeti.FiniteTypeCommHopfAlgCat.componentGroupPoints H) :=
  (TauCeti.FiniteTypeCommHopfAlgCat.componentGroupPoints H).str

theorem exists_reduced_identityComponent_of_isReduced
    (P : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsReduced P]
    (J₀ : TauCeti.HopfIdeal k P) (hJ₀ : J₀.IsNormal) :
    ∃ J : TauCeti.HopfIdeal k P, J.IsNormal ∧
      ConnectedSpace (PrimeSpectrum (TauCeti.FiniteTypeCommHopfAlgCat.quotient P J)) ∧
      IsReduced (TauCeti.FiniteTypeCommHopfAlgCat.quotient P J) ∧
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup P.obj J (CommAlgCat.of k k) ≤
        TauCeti.CommHopfAlgCat.quotientPointsSubgroup P.obj J₀ (CommAlgCat.of k k) ∧
      ((TauCeti.CommHopfAlgCat.quotientPointsSubgroup P.obj J (CommAlgCat.of k k)).subgroupOf
        (TauCeti.CommHopfAlgCat.quotientPointsSubgroup P.obj J₀
          (CommAlgCat.of k k))).FiniteIndex := by
  classical
  let Q : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k :=
    TauCeti.FiniteTypeCommHopfAlgCat.quotient P J₀
  let IC : TauCeti.HopfIdeal k Q :=
    TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := Q)
  let S : Subgroup (WithConv (Q →ₐ[k] k)) :=
    TauCeti.CommHopfAlgCat.quotientPointsSubgroup Q.obj IC (CommAlgCat.of k k)
  let JQ : TauCeti.HopfIdeal k Q := TauCeti.HopfIdeal.vanishingIdeal S
  let q₀ : P ⟶ Q := TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient P J₀
  have hq₀ : Function.Surjective (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom q₀) :=
    TauCeti.CommHopfAlgCat.mkQuotient_surjective P.obj J₀
  let J : TauCeti.HopfIdeal k P := JQ.comapOfSurjective
    (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom q₀) hq₀
  have hker : TauCeti.HopfIdeal.kerOfSurjective
      (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom q₀) hq₀ = J₀ := by
    apply TauCeti.HopfIdeal.ext
    intro x
    rw [TauCeti.HopfIdeal.mem_kerOfSurjective, ← TauCeti.HopfIdeal.mem_toIdeal]
    exact TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient_eq_zero_iff P J₀ x
  have hJ₀J : J₀ ≤ J := by
    have h : (⊥ : TauCeti.HopfIdeal k Q).comapOfSurjective
        (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom q₀) hq₀ ≤ J :=
      TauCeti.HopfIdeal.comapOfSurjective_mono
        (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom q₀) hq₀
        (bot_le : (⊥ : TauCeti.HopfIdeal k Q) ≤ JQ)
    rwa [TauCeti.HopfIdeal.comapOfSurjective_bot, hker] at h
  have hle : IC ≤ JQ := (TauCeti.HopfIdeal.le_vanishingIdeal_iff S IC).mpr le_rfl
  have hQred : IsReduced (Q ⧸ JQ.toIdeal) :=
    TauCeti.HopfIdeal.isReduced_quotient_vanishingIdeal S
  let e : TauCeti.CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k P) J ≅
      TauCeti.CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k Q) JQ :=
    TauCeti.CommHopfAlgCat.quotientIsoOfSurjective
      (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient P J₀).hom hq₀ JQ
  have hPred : IsReduced (P ⧸ J.toIdeal) := by
    let E := _root_.CommHopfAlgCat.isoEquivBialgEquiv e
    exact isReduced_of_injective
      (E.toAlgEquiv.toRingEquiv : (P ⧸ J.toIdeal) →+* (Q ⧸ JQ.toIdeal))
      E.toAlgEquiv.injective
  have hJnorm : J.IsNormal := by
    have hchar : ∀ e' : TauCeti.CommHopfAlgCat.quotient
        (_root_.CommHopfAlgCat.of k P) J₀ ≅
        TauCeti.CommHopfAlgCat.quotient (_root_.CommHopfAlgCat.of k P) J₀,
        JQ.comapOfSurjective e'.hom.hom
          (ConcreteCategory.bijective_of_isIso e'.hom).2 = JQ := by
      intro e'
      let E : (P ⧸ J₀.toIdeal) ≃ₐc[k] (P ⧸ J₀.toIdeal) :=
        _root_.CommHopfAlgCat.isoEquivBialgEquiv e'
      have h := conjugate_vanishingIdeal_identityComponentPoints_eq (k := k) E
      convert h using 2
      exact (rfl : CommHopfAlgCat.Hom.hom e'.hom = E.toBialgHom)
    have : IsReduced ((P : Type u) ⧸
        (JQ.comapOfSurjective
          (TauCeti.CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of k P) J₀).hom
          (TauCeti.CommHopfAlgCat.mkQuotient_surjective _ _)).toIdeal) := hPred
    exact CFSG.ThirdParty.TauCeti.HopfIdeal.IsNormal.comapOfSurjective_of_forall_iso
      (H := (P : Type u)) (I := J₀) hJ₀ JQ hchar
  have hconnQ : ConnectedSpace (PrimeSpectrum (Q ⧸ JQ.toIdeal)) := by
    have hnil : ∀ x : Q, x ∈ JQ.toIdeal →
        IsNilpotent (Ideal.Quotient.mk IC.toIdeal x) := by
      intro x hx
      rw [← TauCeti.forall_algHom_apply_eq_zero_iff_isNilpotent (k := k) (K := k)]
      intro f
      let g : WithConv (Q →ₐ[k] k) := WithConv.toConv
        (f.comp (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
          (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient Q IC)))
      have hg : g ∈ S := by
        rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
        intro y hy
        have hy0 : TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
            (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient Q IC) y = 0 := by
          rw [TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient_eq_zero_iff]
          exact hy
        show f ((TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
          (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient Q IC)) y) = 0
        rw [hy0, map_zero]
      have hx0 : ((g : WithConv (Q →ₐ[k] k)).ofConv) x = 0 :=
        (TauCeti.HopfIdeal.mem_vanishingIdeal S x).mp hx ⟨g, hg⟩
      exact hx0
    have hker_le : RingHom.ker
        ((TauCeti.FiniteTypeCommHopfAlgCat.quotientMapOfLe Q hle).hom.hom.toAlgHom.toRingHom) ≤
        nilradical (Q ⧸ IC.toIdeal) := by
      intro y hy
      rw [mem_nilradical]
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      have hxJ : x ∈ JQ.toIdeal := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        simpa [TauCeti.FiniteTypeCommHopfAlgCat.quotientMapOfLe_mk] using hy
      exact hnil x hxJ
    have hsurj : Function.Surjective
        ((TauCeti.FiniteTypeCommHopfAlgCat.quotientMapOfLe Q hle).hom.hom.toAlgHom.toRingHom) :=
      fun y =>
        TauCeti.FiniteTypeCommHopfAlgCat.quotientMapOfLe_surjective Q hle y
    have hiso : IsHomeomorph (PrimeSpectrum.comap
        ((TauCeti.FiniteTypeCommHopfAlgCat.quotientMapOfLe Q hle).hom.hom.toAlgHom.toRingHom)) :=
      PrimeSpectrum.isHomeomorph_comap _
        (fun x => ⟨1, Nat.one_pos, by simpa using hsurj x⟩) hker_le
    have hconnA : ConnectedSpace (PrimeSpectrum (Q ⧸ IC.toIdeal)) := by
      let _ : ConnectedSpace
          (PrimeSpectrum (↑(TauCeti.FiniteTypeCommHopfAlgCat.identityComponent Q))) :=
        TauCeti.FiniteTypeCommHopfAlgCat.connectedSpace_identityComponent Q
      change ConnectedSpace
        (PrimeSpectrum (↑(TauCeti.FiniteTypeCommHopfAlgCat.identityComponent Q)))
      infer_instance
    let eH : PrimeSpectrum (Q ⧸ JQ.toIdeal) ≃ₜ PrimeSpectrum (Q ⧸ IC.toIdeal) :=
      IsHomeomorph.homeomorph _ hiso
    exact eH.connectedSpace_iff.mpr hconnA
  have hconnP : ConnectedSpace (PrimeSpectrum (P ⧸ J.toIdeal)) := by
    let E := _root_.CommHopfAlgCat.isoEquivBialgEquiv e
    let eRing : (P ⧸ J.toIdeal) ≃+* (Q ⧸ JQ.toIdeal) := E.toAlgEquiv.toRingEquiv
    exact (PrimeSpectrum.homeomorphOfRingEquiv eRing).connectedSpace_iff.mpr hconnQ
  refine ⟨J, hJnorm, ?_, ?_, ?_, ?_⟩
  · exact hconnP
  · exact hPred
  · intro g hg
    rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hg ⊢
    intro x hx
    exact hg x (hJ₀J hx)
  · let W : Subgroup (WithConv (P →ₐ[k] k)) :=
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup P.obj J₀ (CommAlgCat.of k k)
    let Y : Subgroup (WithConv (P →ₐ[k] k)) :=
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup P.obj J (CommAlgCat.of k k)
    let q : WithConv (Q →ₐ[k] k) →* WithConv (P →ₐ[k] k) :=
      (TauCeti.CommHopfAlgCat.quotientPointsHom P.obj J₀ (CommAlgCat.of k k)).hom
    have hq_inj : Function.Injective q :=
      TauCeti.CommHopfAlgCat.quotientPointsHom_injective P.obj J₀ (CommAlgCat.of k k)
    let e' : WithConv (Q →ₐ[k] k) ≃* W := MonoidHom.ofInjective hq_inj
    have hqs : ∀ s : WithConv (Q →ₐ[k] k), q s ∈ Y ↔ s ∈ S := by
      intro s
      rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff,
        TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
      constructor
      · intro h y hy
        obtain ⟨x, rfl⟩ := hq₀ y
        exact h x (TauCeti.HopfIdeal.mem_comapOfSurjective.mpr (hle hy))
      · intro h x hx
        exact (TauCeti.HopfIdeal.mem_vanishingIdeal S _).mp
          (TauCeti.HopfIdeal.mem_comapOfSurjective.mp hx)
          ⟨s, (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff
            Q.obj IC (CommAlgCat.of k k) s).mpr h⟩
    have hY : Y = S.map q := by
      ext g
      constructor
      · intro hg
        have hgW : g ∈ W := by
          rw [TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hg ⊢
          intro x hx
          exact hg x (hJ₀J hx)
        obtain ⟨s, rfl⟩ := hgW
        exact Subgroup.mem_map.mpr ⟨s, (hqs s).mp hg, rfl⟩
      · rintro ⟨s, hs, rfl⟩
        exact (hqs s).mpr hs
    have hSnorm : S.Normal :=
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup_normal Q.obj IC
        (TauCeti.FiniteTypeCommHopfAlgCat.isNormal_identityComponentHopfIdeal Q)
        (CommAlgCat.of k k)
    have : Finite (WithConv (Q →ₐ[k] k) ⧸ S) :=
      TauCeti.FiniteTypeCommHopfAlgCat.instFiniteComponentGroupPoints Q
    have hSfi : S.FiniteIndex := by
      let ψ : WithConv (Q →ₐ[k] k) →* (WithConv (Q →ₐ[k] k) ⧸ S) :=
        QuotientGroup.mk' S
      have hψ : ψ.ker = S := QuotientGroup.ker_mk' S
      rw [← hψ]
      exact Subgroup.finiteIndex_ker ψ
    let φ : W →* (WithConv (Q →ₐ[k] k) ⧸ S) :=
      (QuotientGroup.mk' S).comp (e'.symm : W →* WithConv (Q →ₐ[k] k))
    have hφker : φ.ker = Y.subgroupOf W := by
      ext w
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      show QuotientGroup.mk' S (e'.symm w) = 1 ↔ (w : WithConv (P →ₐ[k] k)) ∈ Y
      rw [show (QuotientGroup.mk' S (e'.symm w) = 1) ↔ e'.symm w ∈ S from
        QuotientGroup.eq_one_iff (e'.symm w)]
      constructor
      · intro hs
        rw [hY]
        refine Subgroup.mem_map.mpr ⟨e'.symm w, hs, ?_⟩
        exact congrArg Subtype.val (e'.apply_symm_apply w)
      · intro hwY
        rw [hY] at hwY
        obtain ⟨s, hs, hqsw⟩ := Subgroup.mem_map.mp hwY
        have hthis : e'.symm w = s := by
          apply e'.injective
          rw [e'.apply_symm_apply]
          exact Subtype.ext hqsw.symm
        rwa [hthis]
    have : Finite φ.range :=
      Finite.of_injective
        (fun x : φ.range => (x : WithConv (Q →ₐ[k] k) ⧸ S))
        Subtype.coe_injective
    have hfin : (Y.subgroupOf W).FiniteIndex := by
      rw [← hφker]
      exact Subgroup.finiteIndex_ker φ
    exact hfin

end CFSG.LieType.AlgebraicGroups.ReductiveDescent
