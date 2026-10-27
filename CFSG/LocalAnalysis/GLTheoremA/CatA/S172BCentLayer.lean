module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172Trans
import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremA.S172X

private theorem layerIs_of_normal_solvable_aux1 {G : Type} [Group G] (X H : Subgroup G) (hHX : H ≤ X)
    [hn : (H.subgroupOf X).Normal] (hsol : Group.IsSolvable (↥X ⧸ H.subgroupOf X))
    {E : Subgroup G} (hE : CFSG.Open.IsComponentOf E X) : E ≤ H := by
  have hEX : E ≤ X := hE.1
  have hperf : ⁅E.subgroupOf X, E.subgroupOf X⁆ = E.subgroupOf X := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hEX,
      I142N.comm_self_eq_of_commutator_top hE.2.2.1]
  have hds : ∀ n : ℕ, E.subgroupOf X ≤ derivedSeries ↥X n := by
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih =>
      rw [derivedSeries_succ]
      calc E.subgroupOf X = ⁅E.subgroupOf X, E.subgroupOf X⁆ := hperf.symm
        _ ≤ ⁅derivedSeries ↥X n, derivedSeries ↥X n⁆ := Subgroup.commutator_mono ih ih
  have hsub : E.subgroupOf X ≤ H.subgroupOf X := by
    obtain ⟨n, hn⟩ := hsol.solvable
    intro y hy
    have h1 := map_derivedSeries_le_derivedSeries (QuotientGroup.mk' (H.subgroupOf X)) n
    rw [hn] at h1
    have h2 : (QuotientGroup.mk' (H.subgroupOf X)) y = 1 := by
      have := h1 ⟨y, hds n hy, rfl⟩
      simpa using this
    exact (QuotientGroup.eq_one_iff y).mp h2
  calc E = (E.subgroupOf X).map X.subtype := (Subgroup.map_subgroupOf_eq_of_le hEX).symm
    _ ≤ (H.subgroupOf X).map X.subtype := Subgroup.map_mono hsub
    _ = H := Subgroup.map_subgroupOf_eq_of_le hHX

private theorem layerIs_of_normal_solvable_aux2 {G : Type} [Group G] {A B : Subgroup G} (h : A = B)
    {p : ℕ} {Qq : TauCeti.CFSGIndex → Prop} :
    catalogIs (PSimple p A) Qq ↔ catalogIs (PSimple p B) Qq := by
  cases h
  exact Iff.rfl

theorem layerIs_of_normal_solvable {G : Type} [Group G] [Finite G] {X H : Subgroup G} (hHX : H ≤ X)
    [hn : (H.subgroupOf X).Normal] (hsol : Group.IsSolvable (↥X ⧸ H.subgroupOf X)) {p : ℕ}
    {Qq : TauCeti.CFSGIndex → Prop} (h : LayerIs p H Qq) : LayerIs p X Qq := by
  have hHXsn : IsSubnormal H X := IsSubnormal.step hHX hn (IsSubnormal.refl X)
  have hle : GLALayer H ≤ GLALayer X := I142N.GLALayer_mono_of_isSubnormal hHXsn
  have hge : GLALayer X ≤ GLALayer H :=
    I142N.GLALayer_le_of fun K hK =>
      I142N.le_GLALayer (I142N.isComponentOf_of_le hK
        (layerIs_of_normal_solvable_aux1 X H hHX hsol hK) hHX)
  have hEq : GLALayer X = GLALayer H := le_antisymm hge hle
  refine ⟨?_, ?_⟩
  · rw [hEq]
    exact I142N.isComponentOf_trans h.1 hHXsn
  · exact (layerIs_of_normal_solvable_aux2 hEq).2 h.2

private noncomputable def catalogIs_pSimple_congr_mulEquiv_aux1 {G G' : Type} [Group G] [Group G']
    {J : Subgroup G} {J' : Subgroup G'} (e : ↥J ≃* ↥J') (p : ℕ) :
    PSimple p J ≃* PSimple p J' := by
  have hPC : (GLAPPrimeCore p ↥J).map (e : ↥J →* ↥J') = GLAPPrimeCore p ↥J' := by
    exact CFSG.pPrimeCore_map_iso p e
  let φ : PQuot p J ≃* PQuot p J' :=
    QuotientGroup.congr (GLAPPrimeCore p ↥J) (GLAPPrimeCore p ↥J') e hPC
  exact QuotientGroup.congr (Subgroup.center (PQuot p J)) (Subgroup.center (PQuot p J')) φ
    (Subgroup.map_center_eq φ)

theorem catalogIs_pSimple_congr_mulEquiv {G G' : Type} [Group G] [Group G'] {J : Subgroup G}
    {J' : Subgroup G'} (e : ↥J ≃* ↥J') (p : ℕ) (Qq : TauCeti.CFSGIndex → Prop) :
    catalogIs (PSimple p J) Qq ↔ catalogIs (PSimple p J') Qq := by
  exact CFSG.LocalAnalysis.GLTheoremA.catalogIs_congr (catalogIs_pSimple_congr_mulEquiv_aux1 e p)

private theorem layerIs_congr_mulEquiv_aux1 {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (p : ℕ) (Qq : TauCeti.CFSGIndex → Prop) :
    LayerIs p X Qq ↔ LayerIs p (⊤ : Subgroup ↥X) Qq := by
  have hX : (⊤ : Subgroup ↥X).map X.subtype = X := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hι : Function.Injective X.subtype := X.subtype_injective
  have hL : GLALayer X = (GLALayer (⊤ : Subgroup ↥X)).map X.subtype :=
    (congrArg GLALayer hX).symm.trans (Y10F.glaLayer_map hι (⊤ : Subgroup ↥X))
  have hc : IsComponentOf (GLALayer X) X ↔
      IsComponentOf (GLALayer (⊤ : Subgroup ↥X)) (⊤ : Subgroup ↥X) := by
    have h := Y10F.isComponentOf_map_iff hι (L := GLALayer (⊤ : Subgroup ↥X)) (H := ⊤)
    rw [← hL, hX] at h
    exact h
  have hcat : catalogIs (PSimple p (GLALayer X)) Qq ↔
      catalogIs (PSimple p (GLALayer (⊤ : Subgroup ↥X))) Qq :=
    (catalogIs_pSimple_congr_mulEquiv (MulEquiv.subgroupCongr hL) p Qq).trans
      (S172.catalogIs_pSimple_map_iff (GLALayer (⊤ : Subgroup ↥X)) Qq)
  unfold LayerIs
  exact and_congr hc hcat

private theorem layerIs_congr_mulEquiv_aux2 {G G' : Type} [Group G] [Group G']
    {X : Subgroup G} {X' : Subgroup G'} (e : ↥X ≃* ↥X') (p : ℕ) (Qq : TauCeti.CFSGIndex → Prop) :
    LayerIs p (⊤ : Subgroup ↥X) Qq ↔ LayerIs p (⊤ : Subgroup ↥X') Qq := by
  have hι : Function.Injective e.toMonoidHom := e.injective
  have htop : (⊤ : Subgroup ↥X).map e.toMonoidHom = (⊤ : Subgroup ↥X') :=
    Subgroup.map_top_of_surjective e.toMonoidHom e.surjective
  have hL : GLALayer (⊤ : Subgroup ↥X') =
      (GLALayer (⊤ : Subgroup ↥X)).map e.toMonoidHom :=
    (congrArg GLALayer htop).symm.trans (Y10F.glaLayer_map hι (⊤ : Subgroup ↥X))
  have hc : IsComponentOf (GLALayer (⊤ : Subgroup ↥X)) (⊤ : Subgroup ↥X) ↔
      IsComponentOf (GLALayer (⊤ : Subgroup ↥X')) (⊤ : Subgroup ↥X') := by
    have h := Y10F.isComponentOf_map_iff hι (L := GLALayer (⊤ : Subgroup ↥X)) (H := ⊤)
    rw [← hL, htop] at h
    exact h.symm
  have hcat : catalogIs (PSimple p (GLALayer (⊤ : Subgroup ↥X))) Qq ↔
      catalogIs (PSimple p (GLALayer (⊤ : Subgroup ↥X'))) Qq :=
    catalogIs_pSimple_congr_mulEquiv
      ((Subgroup.equivMapOfInjective (GLALayer (⊤ : Subgroup ↥X)) e.toMonoidHom hι).trans
        (MulEquiv.subgroupCongr hL.symm)) p Qq
  unfold LayerIs
  exact and_congr hc hcat

theorem layerIs_congr_mulEquiv {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G']
    {X : Subgroup G} {X' : Subgroup G'} (e : ↥X ≃* ↥X') {p : ℕ} {Qq : TauCeti.CFSGIndex → Prop} :
    LayerIs p X Qq ↔ LayerIs p X' Qq :=
  (layerIs_congr_mulEquiv_aux1 (X := X) p Qq).trans
    ((layerIs_congr_mulEquiv_aux2 (X := X) (X' := X') e p Qq).trans
      (layerIs_congr_mulEquiv_aux1 (X := X') p Qq).symm)

end CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

end
