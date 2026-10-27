module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTSwapBasic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotTwist

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore)

local instance f4PilotCTSwapPiecesNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

theorem commute_mul_right_iff_of_commute {M : Type*} [Group M] {a b c : M} (hc : Commute a c) :
    Commute a (c * b) ↔ Commute a b := by
  constructor
  · intro h
    have h' := hc.inv_right.mul_right h
    rwa [inv_mul_cancel_left] at h'
  · exact hc.mul_right

theorem commute_subtype_coe_iff {M : Type*} [Group M] {H : Subgroup M} {a b : H} :
    Commute (a : M) b ↔ Commute a b :=
  ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

section Prod

open CFSG.Quasithin (derivedSeriesOf)

variable {M₁ M₂ : Type*} [Group M₁] [Group M₂]

theorem derivedSeriesOf_subgroupProd (H : Subgroup M₁) (H' : Subgroup M₂) (n : ℕ) :
    derivedSeriesOf (H.prod H') n = (derivedSeriesOf H n).prod (derivedSeriesOf H' n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [CFSG.Quasithin.derivedSeriesOf_succ, CFSG.Quasithin.derivedSeriesOf_succ,
      CFSG.Quasithin.derivedSeriesOf_succ, ih, commutator_prod_prod]

theorem perfectCore_subgroupProd (H : Subgroup M₁) (H' : Subgroup M₂) :
    perfectCore (H.prod H') = (perfectCore H).prod (perfectCore H') := by
  ext x
  simp only [perfectCore, derivedSeriesOf_subgroupProd, mem_iInf, mem_prod, forall_and]

end Prod

section Equivariance


variable {K : Type} [Field K] {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .F4 K} {t : G}

theorem SwapNeighbourIso.commute_iff [Finite K] [CharP K 2] {N : AmalgamNeighbour}
    (h : SwapNeighbourIso e t N) {d : adjointGroup .F4 K}
    (hd : (d : ModGL .F4 K) ∈ leviTorus K ∅) (x y : N.levi K) :
    Commute ((h.Φ (x, y) : neighbourCore e N) : G) ((e.symm d : L) : G) ↔
      Commute ((x : adjointGroup .F4 K) : ModGL .F4 K) (d : ModGL .F4 K) ∧
        Commute ((y : adjointGroup .F4 K) : ModGL .F4 K) (d : ModGL .F4 K) := by
  obtain ⟨b, -, hb⟩ := mem_leviTorus.1 hd
  obtain ⟨d₁, hd₁, d₂, ⟨x₂, hx₂, rfl⟩, he⟩ := exists_eq_mul_of_rootDiagUnit N b
  rw [hb] at he
  simp only [Subgroup.coe_subtype] at he
  have hdd : d = ⟨d₁, N.torus_le_adjointGroup hd₁⟩ * x₂ := Subtype.ext he
  have hd₁G := symm_mem_modelToG e (x := ⟨d₁, N.torus_le_adjointGroup hd₁⟩) hd₁
  have hc₂ : Commute ((h.Φ (x, y) : neighbourCore e N) : G)
      ((e.symm ⟨d₁, N.torus_le_adjointGroup hd₁⟩ : L) : G) :=
    (mem_centralizer_iff.1 (centralizerPerfectCore_le_centralizer _ (h.Φ (x, y)).2) _ hd₁G).symm
  have hc₁ : ∀ z : N.levi K, Commute ((z : adjointGroup .F4 K) : ModGL .F4 K) d₁ := by
    intro z
    have hz : ((z : adjointGroup .F4 K) : ModGL .F4 K) ∈
        (N.levi K).map (adjointGroup .F4 K).subtype := ⟨z, z.2, rfl⟩
    exact (show Commute d₁ ((z : adjointGroup .F4 K) : ModGL .F4 K) from
      mem_centralizer_iff.1 (levi_le_centralizer_torus N hz) _ hd₁).symm
  have hdiag : ((e.symm x₂ : L) : G) =
      ((h.Φ (⟨x₂, hx₂⟩, ⟨x₂, hx₂⟩) : neighbourCore e N) : G) := (h.diag ⟨x₂, hx₂⟩).symm
  rw [he, commute_mul_right_iff_of_commute (hc₁ x), commute_mul_right_iff_of_commute (hc₁ y), hdd,
    map_mul, L.coe_mul, commute_mul_right_iff_of_commute hc₂, hdiag, commute_subtype_coe_iff]
  constructor
  · intro hc
    have hc' := hc.map h.Φ.symm.toMonoidHom
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at hc'
    exact ⟨congrArg (fun z : N.levi K × N.levi K => ((z.1 : adjointGroup .F4 K) : ModGL .F4 K))
      hc', congrArg (fun z : N.levi K × N.levi K => ((z.2 : adjointGroup .F4 K) : ModGL .F4 K))
      hc'⟩
  · rintro ⟨hxc, hyc⟩
    have hc : Commute ((x, y) : N.levi K × N.levi K) (⟨x₂, hx₂⟩, ⟨x₂, hx₂⟩) :=
      Prod.ext (Subtype.ext (Subtype.ext hxc)) (Subtype.ext (Subtype.ext hyc))
    exact hc.map h.Φ.toMonoidHom

end Equivariance

section Pieces


variable (K : Type) [Field K]

@[expose] noncomputable def leviTorusCentralizer (N : AmalgamNeighbour)
    (J : Finset (Fin (Tag.rank .F4))) : Subgroup (N.levi K) :=
  (centralizer (leviTorus K J : Set (ModGL .F4 K))).comap
    ((adjointGroup .F4 K).subtype.comp (N.levi K).subtype)

variable {K}

theorem mem_leviTorusCentralizer {N : AmalgamNeighbour} {J : Finset (Fin (Tag.rank .F4))}
    {x : N.levi K} : x ∈ leviTorusCentralizer K N J ↔
      ∀ d ∈ leviTorus K J, Commute d ((x : adjointGroup .F4 K) : ModGL .F4 K) := by
  simp only [leviTorusCentralizer, mem_comap, mem_centralizer_iff, MonoidHom.coe_comp,
    coe_subtype, Function.comp_apply, SetLike.mem_coe]
  rfl

end Pieces

section PiecesMain


variable {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* adjointGroup .F4 K} {t : G} {N : AmalgamNeighbour}

theorem SwapNeighbourIso.map_centralizer_prod (h : SwapNeighbourIso e t N)
    (J : Finset (Fin (Tag.rank .F4))) :
    ((leviTorusCentralizer K N J).prod (leviTorusCentralizer K N J)).map
        ((neighbourCore e N).subtype.comp h.Φ.toMonoidHom) =
      neighbourCore e N ⊓ centralizer (modelToG e (leviTorus K J) : Set G) := by
  ext g
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    refine mem_inf.2 ⟨(h.Φ (x, y)).2, mem_centralizer_iff.2 fun g' hg' => ?_⟩
    obtain ⟨d, hdT, rfl⟩ := (mem_modelToG e).1 hg'
    have hd : ((d : adjointGroup .F4 K) : ModGL .F4 K) ∈ leviTorus K ∅ :=
      leviTorus_anti (Finset.empty_subset J) hdT
    have hc := (h.commute_iff hd x y).2 ⟨(mem_leviTorusCentralizer.1 hx _ hdT).symm,
      (mem_leviTorusCentralizer.1 hy _ hdT).symm⟩
    exact hc.symm.eq
  · intro hg
    obtain ⟨hgE, hgC⟩ := mem_inf.1 hg
    refine ⟨h.Φ.symm ⟨g, hgE⟩, ⟨?_, ?_⟩, by simp⟩
    all_goals
      refine mem_leviTorusCentralizer.2 fun d₀ hd₀ => ?_
      have hd₀C : d₀ ∈ adjointGroup .F4 K := leviTorus_le_adjointGroup J hd₀
      have hd : ((⟨d₀, hd₀C⟩ : adjointGroup .F4 K) : ModGL .F4 K) ∈ leviTorus K ∅ :=
        leviTorus_anti (Finset.empty_subset J) hd₀
      have hgd := mem_centralizer_iff.1 hgC _ (symm_mem_modelToG e (x := ⟨d₀, hd₀C⟩) hd₀)
      have hc : Commute ((h.Φ (h.Φ.symm ⟨g, hgE⟩) : neighbourCore e N) : G)
          ((e.symm ⟨d₀, hd₀C⟩ : L) : G) := by
        rw [MulEquiv.apply_symm_apply]
        exact hgd.symm
      have hc' := (h.commute_iff hd _ _).1 hc
    · exact hc'.1.symm
    · exact hc'.2.symm

theorem SwapNeighbourIso.map_leviPiece [Finite G] (h : SwapNeighbourIso e t N)
    (hq : 4 ≤ Nat.card K) {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ N.nodes)
    (hJ2 : J.card ≤ 2) :
    ((leviPiece K N J).prod (leviPiece K N J)).map
        ((neighbourCore e N).subtype.comp h.Φ.toMonoidHom) = pieceCore e J := by
  have : Finite (N.levi K) := finite_levi K N
  have : Finite (ModGL .F4 K) := CFSG.LieType.Chevalley.finite_modGL
  set j : N.levi K →* ModGL .F4 K := (adjointGroup .F4 K).subtype.comp (N.levi K).subtype with hj
  have hjinj : Function.Injective j := Subtype.val_injective.comp Subtype.val_injective
  have hrange : (⊤ : Subgroup (N.levi K)).map j = (N.levi K).map (adjointGroup .F4 K).subtype := by
    rw [hj, ← map_map, ← MonoidHom.range_eq_map, range_subtype]
  have hmapC : (leviTorusCentralizer K N J).map j = (N.levi K).map (adjointGroup .F4 K).subtype ⊓
      centralizer (leviTorus K J : Set (ModGL .F4 K)) := by
    rw [leviTorusCentralizer, ← hj, map_comap_eq, MonoidHom.range_eq_map, hrange, inf_comm]
  have hpiece : (leviPiece K N J).map j = rootSpan .F4 K (amalgamRoots J) := by
    have hle : rootSpan .F4 K (amalgamRoots J) ≤ (N.levi K).map (adjointGroup .F4 K).subtype := by
      rw [← map_subtype_levi_f4Datum J]
      exact map_mono (levi_le_neighbourLevi hJ)
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hg
      obtain ⟨y, hy, rfl⟩ := hle hg
      exact ⟨⟨y, hy⟩, hg, rfl⟩
  have hP : perfectCore (leviTorusCentralizer K N J) = leviPiece K N J := by
    apply map_injective hjinj
    rw [CFSG.Quasithin.map_perfectCore, hmapC, hpiece]
    exact perfectCore_levi_inf_centralizer_leviTorus hq hJ2 N hJ
  rw [pieceCore_eq e N hJ, ← h.map_centralizer_prod J, ← CFSG.Quasithin.map_perfectCore,
    perfectCore_subgroupProd, hP]

theorem SwapNeighbourIso.exists_eq_of_mem_pieceCore [Finite G] (h : SwapNeighbourIso e t N)
    (hq : 4 ≤ Nat.card K) {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ N.nodes)
    (hJ2 : J.card ≤ 2) {g : G} (hg : g ∈ pieceCore e J) :
    ∃ x y : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J,
      g = h.fst hJ x * h.snd hJ y := by
  rw [← h.map_leviPiece hq hJ hJ2] at hg
  obtain ⟨⟨z₁, z₂⟩, ⟨hz₁, hz₂⟩, rfl⟩ := hg
  have hx : (z₁ : adjointGroup .F4 K) ∈
      CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J := by
    rw [levi_f4Datum_eq, mem_subgroupOf]
    exact mem_leviPiece.1 hz₁
  have hy : (z₂ : adjointGroup .F4 K) ∈
      CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J := by
    rw [levi_f4Datum_eq, mem_subgroupOf]
    exact mem_leviPiece.1 hz₂
  exact ⟨⟨_, hx⟩, ⟨_, hy⟩, h.coe_apply_eq_mul z₁ z₂⟩

omit [Finite K] [CharP K 2]
  in
theorem SwapNeighbourIso.range_fst_sup_range_snd_le (h : SwapNeighbourIso e t N)
    {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ N.nodes) :
    (h.fst hJ).range ⊔ (h.snd hJ).range ≤ ((leviPiece K N J).prod (leviPiece K N J)).map
        ((neighbourCore e N).subtype.comp h.Φ.toMonoidHom) := by
  have hmem : ∀ x : CFSG.LieType.CurtisTits.levi (Adjoint.f4Datum K).rootGroup J,
      (⟨x, levi_le_neighbourLevi hJ x.2⟩ : N.levi K) ∈ leviPiece K N J := fun x =>
    mem_leviPiece.2 (mem_subgroupOf.1 ((levi_f4Datum_eq (K := K) J).le x.2))
  refine sup_le ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact ⟨(⟨x, levi_le_neighbourLevi hJ x.2⟩, 1), ⟨hmem x, one_mem _⟩, rfl⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨(1, ⟨x, levi_le_neighbourLevi hJ x.2⟩), ⟨one_mem _, hmem x⟩, rfl⟩

theorem SwapNeighbourIso.range_fst_sup_range_snd [Finite G] (h : SwapNeighbourIso e t N)
    (hq : 4 ≤ Nat.card K) {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ N.nodes)
    (hJ2 : J.card ≤ 2) : (h.fst hJ).range ⊔ (h.snd hJ).range = pieceCore e J := by
  refine le_antisymm ((h.range_fst_sup_range_snd_le hJ).trans (h.map_leviPiece hq hJ hJ2).le)
    fun g hg => ?_
  obtain ⟨x, y, rfl⟩ := h.exists_eq_of_mem_pieceCore hq hJ hJ2 hg
  exact mul_mem (mem_sup_left ⟨x, rfl⟩) (mem_sup_right ⟨y, rfl⟩)

theorem SwapNeighbourIso.range_fst_le_pieceCore [Finite G] (h : SwapNeighbourIso e t N)
    (hq : 4 ≤ Nat.card K) {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ N.nodes)
    (hJ2 : J.card ≤ 2) : (h.fst hJ).range ≤ pieceCore e J :=
  le_sup_left.trans (h.range_fst_sup_range_snd hq hJ hJ2).le

theorem SwapNeighbourIso.range_snd_le_pieceCore [Finite G] (h : SwapNeighbourIso e t N)
    (hq : 4 ≤ Nat.card K) {J : Finset (Fin (Tag.rank .F4))} (hJ : J ⊆ N.nodes)
    (hJ2 : J.card ≤ 2) : (h.snd hJ).range ≤ pieceCore e J :=
  le_sup_right.trans (h.range_fst_sup_range_snd hq hJ hJ2).le

end PiecesMain

end CFSG.SeitzReduction.F4Pilot
