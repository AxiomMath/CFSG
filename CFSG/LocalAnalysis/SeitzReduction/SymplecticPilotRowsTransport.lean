module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRows
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOddCore

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Overgroup

variable {K K' : Type} [Group K] [Group K']

@[expose] noncomputable def centerQuotientCongr (ψ : K ≃* K') : K ⧸ center K ≃* K' ⧸ center K' :=
  QuotientGroup.congr (center K) (center K') ψ (Subgroup.map_center_eq ψ)

theorem centerQuotientCongr_mk (ψ : K ≃* K') (x : K) :
    centerQuotientCongr ψ (QuotientGroup.mk' (center K) x) =
      QuotientGroup.mk' (center K') (ψ x) :=
  rfl

theorem centerQuotientAut_centerQuotientCongr (ψ : K ≃* K') {τ : MulAut K} {τ' : MulAut K'}
    (h : ∀ x, τ' (ψ x) = ψ (τ x)) (x : K ⧸ center K) :
    F4Pilot.centerQuotientAut τ' (centerQuotientCongr ψ x) =
      centerQuotientCongr ψ (F4Pilot.centerQuotientAut τ x) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center K) x
  rw [centerQuotientCongr_mk, F4Pilot.centerQuotientAut_mk, F4Pilot.centerQuotientAut_mk,
    centerQuotientCongr_mk, h]

theorem sp2mOvergroup_of_mulEquiv (ψ : K ≃* K') {τ : MulAut K} {τ' : MulAut K'}
    (h : ∀ x, τ' (ψ x) = ψ (τ x)) {m f : ℕ} (hov : Sp2mOvergroup K τ m f) :
    Sp2mOvergroup K' τ' m f := by
  obtain ⟨hout, hodd, htype, hfix⟩ := hov
  refine ⟨?_, ?_, sp2mOvergroupType_of_mulEquiv (centerQuotientCongr ψ) htype, ?_⟩
  · rintro ⟨k', hk'⟩
    apply hout
    refine ⟨ψ.symm k', ?_⟩
    ext x
    apply ψ.injective
    rw [← h, ← hk', MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
  · rwa [← Nat.card_congr (Subgroup.centerCongr ψ).toEquiv]
  · have hmap := map_fixedSubgroup_of_apply_comm (centerQuotientCongr ψ)
      (centerQuotientAut_centerQuotientCongr ψ h)
    exact LieType.CurtisTits.lieModel_of_mulEquiv
      (((fixedSubgroup (F4Pilot.centerQuotientAut τ)).equivMapOfInjective
        (centerQuotientCongr ψ).toMonoidHom (centerQuotientCongr ψ).injective).trans
        (MulEquiv.subgroupCongr hmap)) hfix

end Overgroup

section Neighbour

variable {Y Y' : Type} [Group Y] [Group Y']

theorem map_map_conj_mulEquiv (γ : Y ≃* Y') (s : Y) (A : Subgroup Y) :
    (A.map (MulAut.conj s).toMonoidHom).map γ.toMonoidHom =
      (A.map γ.toMonoidHom).map (MulAut.conj (γ s)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulAut.conj_apply, map_mul, map_inv]

theorem NeighbourOvergroupSp2mKind.map_mulEquiv (γ : Y ≃* Y') {s : Y} {D : Subgroup Y}
    {m f : ℕ} {κ : Sp2mKind} (h : NeighbourOvergroupSp2mKind s D m f κ) :
    NeighbourOvergroupSp2mKind (γ s) (D.map γ.toMonoidHom) m f κ := by
  obtain ⟨Kc, hKc, hDKK, h1 | h2⟩ := h
  · obtain ⟨hκ, hKt, hDK, hsK, hsN, hov, hty⟩ := h1
    have hKt' : (Kc.map γ.toMonoidHom).map (MulAut.conj (γ s)).toMonoidHom =
        Kc.map γ.toMonoidHom := by
      rw [← map_map_conj_mulEquiv, hKt]
    have hsN' : γ s ∈ normalizer ((Kc.map γ.toMonoidHom : Subgroup Y') : Set Y') :=
      mem_normalizer_iff_map_conj_eq.2 hKt'
    set ψ : Kc ≃* Kc.map γ.toMonoidHom := Kc.equivMapOfInjective γ.toMonoidHom γ.injective
      with hψ
    have hcomm : ∀ x : Kc, (Kc.map γ.toMonoidHom).normalizerMonoidHom ⟨γ s, hsN'⟩ (ψ x) =
        ψ (Kc.normalizerMonoidHom ⟨s, hsN⟩ x) := by
      intro x
      apply Subtype.ext
      rw [F4Pilot.coe_normalizerMonoidHom_mk_apply]
      change γ s * γ x * (γ s)⁻¹ = γ ((Kc.normalizerMonoidHom ⟨s, hsN⟩ x : Kc) : Y)
      rw [F4Pilot.coe_normalizerMonoidHom_mk_apply, map_mul, map_mul, map_inv]
    refine ⟨Kc.map γ.toMonoidHom, CFSG.LocalCores.isComponent_map_mulEquiv γ hKc, ?_,
      .inl ⟨hκ, hKt', ?_, ?_, hsN', sp2mOvergroup_of_mulEquiv ψ hcomm hov,
        sp2mKindType_of_mulEquiv (centerQuotientCongr ψ) hty⟩⟩
    · rw [← map_map_conj_mulEquiv, ← Subgroup.map_sup]
      exact map_mono hDKK
    · exact (map_lt_map_iff_of_injective γ.injective).2 hDK
    · rintro ⟨x, hx, hxs⟩
      exact hsK (γ.injective hxs ▸ hx)
  · obtain ⟨hκ, hKt, hcomm, ⟨φ⟩⟩ := h2
    refine ⟨Kc.map γ.toMonoidHom, CFSG.LocalCores.isComponent_map_mulEquiv γ hKc, ?_,
      .inr ⟨hκ, ?_, ?_, ⟨?_⟩⟩⟩
    · rw [← map_map_conj_mulEquiv, ← Subgroup.map_sup]
      exact map_mono hDKK
    · rw [← map_map_conj_mulEquiv]
      exact fun h' => hKt (map_injective γ.injective h')
    · rw [← map_map_conj_mulEquiv, ← map_commutator, hcomm, Subgroup.map_bot]
    · exact (centerQuotientCongr (Kc.equivMapOfInjective γ.toMonoidHom γ.injective)).symm.trans
        (φ.trans (D.equivMapOfInjective γ.toMonoidHom γ.injective))

end Neighbour

section Ambient

theorem map_oddCore_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (φ : A ≃* B) : (oddCore A).map φ.toMonoidHom = oddCore B := by
  refine le_antisymm (LinearPilot.map_oddCore_le_oddCore_of_mulEquiv φ) fun y hy => ?_
  exact ⟨φ.symm y, LinearPilot.map_oddCore_le_oddCore_of_mulEquiv φ.symm ⟨y, hy, rfl⟩,
    φ.apply_symm_apply y⟩

@[expose] noncomputable def quotientOddCoreCongr {A B : Type*} [Group A] [Group B] [Finite A]
    [Finite B] (φ : A ≃* B) : A ⧸ oddCore A ≃* B ⧸ oddCore B :=
  QuotientGroup.congr _ _ φ (map_oddCore_mulEquiv φ)

variable {G G' : Type} [Group G] [Group G']

@[expose] noncomputable def centralizerCongr (α : G ≃* G') (X : Subgroup G) :
    centralizer (X : Set G) ≃* centralizer ((X.map α.toMonoidHom : Subgroup G') : Set G') :=
  ((centralizer (X : Set G)).equivMapOfInjective α.toMonoidHom α.injective).trans
    (MulEquiv.subgroupCongr (F4Pilot.map_centralizer_mulEquiv α X))

theorem coe_centralizerCongr_apply (α : G ≃* G') (X : Subgroup G) (x : centralizer (X : Set G)) :
    ((centralizerCongr α X x : centralizer ((X.map α.toMonoidHom : Subgroup G') : Set G')) : G') =
      α x :=
  rfl

theorem map_subgroupOf_centralizerCongr (α : G ≃* G') (X D : Subgroup G) :
    (D.subgroupOf (centralizer (X : Set G))).map (centralizerCongr α X).toMonoidHom =
      (D.map α.toMonoidHom).subgroupOf
        (centralizer ((X.map α.toMonoidHom : Subgroup G') : Set G')) := by
  ext y
  rw [mem_map_equiv, mem_subgroupOf, mem_subgroupOf, mem_map_equiv]
  have h : (((centralizerCongr α X).symm y : centralizer (X : Set G)) : G) = α.symm y := by
    apply α.injective
    rw [MulEquiv.apply_symm_apply, ← coe_centralizerCongr_apply, MulEquiv.apply_symm_apply]
  rw [h]

theorem HR8KindAtSp.map_mulEquiv [Finite G] [Finite G'] (α : G ≃* G') {t : G} {m f : ℕ}
    {X D : Subgroup G} {κ : Sp2mKind} (h : HR8KindAtSp t m f X D κ) :
    HR8KindAtSp (α t) m f (X.map α.toMonoidHom) (D.map α.toMonoidHom) κ := by
  obtain ⟨htX, hK⟩ := h
  have htX' : α t ∈ centralizer ((X.map α.toMonoidHom : Subgroup G') : Set G') :=
    (centralizerCongr α X ⟨t, htX⟩).2
  refine ⟨htX', ?_⟩
  have h1 := hK.map_mulEquiv (quotientOddCoreCongr (centralizerCongr α X))
  have hs : quotientOddCoreCongr (centralizerCongr α X)
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩) =
      QuotientGroup.mk' (oddCore (centralizer ((X.map α.toMonoidHom : Subgroup G') : Set G')))
        ⟨α t, htX'⟩ := rfl
  have hD : ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).map
        (quotientOddCoreCongr (centralizerCongr α X)).toMonoidHom =
      ((D.map α.toMonoidHom).subgroupOf
          (centralizer ((X.map α.toMonoidHom : Subgroup G') : Set G'))).map
        (QuotientGroup.mk'
          (oddCore (centralizer ((X.map α.toMonoidHom : Subgroup G') : Set G')))) := by
    rw [← map_subgroupOf_centralizerCongr, Subgroup.map_map, Subgroup.map_map]
    rfl
  rw [hs, hD] at h1
  exact h1

end Ambient

section Planes

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}

theorem rootKindSp_perm (e : L ≃* StatedSp n K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (f : ℕ) (π : Equiv.Perm (Fin n)) {k : Fin n} {κ : Sp2mKind} (h : RootKindSp e t f k κ) :
    RootKindSp e t f (π k) κ := by
  have h1 := HR8KindAtSp.map_mulEquiv (MulAut.conj ((e.symm (permSp K π) : L) : G)) h
  have hwt : MulAut.conj ((e.symm (permSp K π) : L) : G) t = t := by
    rw [MulAut.conj_apply, mem_centralizer_iff.mp htC _ (e.symm (permSp K π)).2,
      mul_inv_cancel_right]
  have hX : (modelToG e (rootTorusSp K k)).map
      (MulAut.conj ((e.symm (permSp K π) : L) : G)).toMonoidHom =
      modelToG e (rootTorusSp K (π k)) := by
    rw [← UnitaryPilot.modelToG_map_conj, map_conj_permSp_rootTorusSp]
  have hD : (modelToG e (complSp K k)).map
      (MulAut.conj ((e.symm (permSp K π) : L) : G)).toMonoidHom =
      modelToG e (complSp K (π k)) := by
    rw [← UnitaryPilot.modelToG_map_conj, map_conj_permSp_complSp]
  rw [hwt, hX, hD] at h1
  exact h1

theorem rootKindSp_iff (e : L ≃* StatedSp n K) {t : G} (htC : t ∈ centralizer (L : Set G))
    (f : ℕ) (k l : Fin n) (κ : Sp2mKind) : RootKindSp e t f k κ ↔ RootKindSp e t f l κ := by
  constructor
  · intro h
    have h' := rootKindSp_perm e htC f (Equiv.swap k l) h
    rwa [Equiv.swap_apply_left] at h'
  · intro h
    have h' := rootKindSp_perm e htC f (Equiv.swap k l) h
    rwa [Equiv.swap_apply_right] at h'

end Planes

end CFSG.SeitzReduction.SymplecticPilot
