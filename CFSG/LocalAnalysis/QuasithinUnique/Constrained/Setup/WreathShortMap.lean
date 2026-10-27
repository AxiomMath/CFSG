module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellAlt3
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell

section Map

variable {H G : Type*} [Group H] [Group G] (f : H →* G) (hf : Function.Injective f)

include hf

theorem blockQ_map_injective (L : Subgroup H) : blockQ (L.map f) = (blockQ L).map f := by
  let φ : ↥L ≃* ↥(L.map f) := L.equivMapOfInjective f hf
  rw [blockQ_eq_map, blockQ_eq_map, ← CFSG.pCore_map_iso 2 φ, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem blockU_map_injective (L : Subgroup H) : blockU (L.map f) = (blockU L).map f := by
  unfold blockU
  rw [blockQ_map_injective f hf, Subgroup.map_commutator]

theorem map_inf_centralizer_map {U L : Subgroup H} :
    U.map f ⊓ Subgroup.centralizer ((L.map f : Subgroup G) : Set G) =
      (U ⊓ Subgroup.centralizer (L : Set H)).map f := by
  ext x
  constructor
  · rintro ⟨⟨u, hu, rfl⟩, hc⟩
    refine ⟨u, ⟨hu, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hc (f l) ⟨l, hl, rfl⟩
    apply hf
    simpa using this
  · rintro ⟨u, ⟨hu, hc⟩, rfl⟩
    refine ⟨⟨u, hu, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨l, hl, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg f (Subgroup.mem_centralizer_iff.mp hc l hl)

theorem blockZ_map_injective (L : Subgroup H) : blockZ (L.map f) = (blockZ L).map f := by
  unfold blockZ
  rw [blockU_map_injective f hf, map_inf_centralizer_map f hf]

theorem card_quot_pCore_map_injective (L : Subgroup H) :
    Nat.card (↥(L.map f) ⧸ CFSG.pCore 2 ↥(L.map f)) = Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  let φ : ↥L ≃* ↥(L.map f) := L.equivMapOfInjective f hf
  let e : (L ⧸ CFSG.pCore 2 L) ≃* ((L.map f : Subgroup G) ⧸
      CFSG.pCore 2 (L.map f : Subgroup G)) :=
    QuotientGroup.congr _ _ φ (CFSG.pCore_map_iso 2 φ)
  exact (Nat.card_congr e.toEquiv).symm

theorem IsShort2.map_of_injective {L : Subgroup H} (hL : IsShort2 L) : IsShort2 (L.map f) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hL
  let φ : ↥L ≃* ↥(L.map f) := L.equivMapOfInjective f hf
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro N' _ hN'
    have hcomap : (N'.comap φ.toMonoidHom).map φ.toMonoidHom = N' :=
      Subgroup.map_comap_eq_self_of_surjective φ.surjective N'
    have e : (↥L ⧸ N'.comap φ.toMonoidHom) ≃* (↥(L.map f) ⧸ N') :=
      QuotientGroup.congr _ _ φ hcomap
    have hN := h1 (N'.comap φ.toMonoidHom) (hN'.of_equiv e.symm)
    rw [← hcomap, hN, Subgroup.map_top, MonoidHom.range_eq_top_of_surjective _ φ.surjective]
  · intro x hx
    obtain ⟨⟨y, hy, rfl⟩, hxc⟩ := hx
    have hQ : pCoreOf 2 (L.map f) = (pCoreOf 2 L).map f := blockQ_map_injective f hf L
    rw [hQ] at hxc ⊢
    refine ⟨y, h2 ⟨hy, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hxc (f q) ⟨q, hq, rfl⟩
    apply hf
    simpa using this
  · have hQ := blockQ_map_injective f hf L
    have hU := blockU_map_injective f hf L
    have hQc := map_inf_centralizer_map f hf (U := blockQ L) (L := blockQ L)
    refine ⟨?_, ?_⟩
    · rw [hU, hQ, hQc]
      exact Subgroup.map_mono h3.1
    · intro x hx
      rw [hU] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      simpa using congrArg f (h3.2 y hy)
  · let e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* (↥(L.map f) ⧸ CFSG.pCore 2 ↥(L.map f)) :=
      QuotientGroup.congr _ _ φ (CFSG.pCore_map_iso 2 φ)
    rcases h4 with h | h
    · exact Or.inl ((CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).mp h)
    · exact Or.inr (by rw [← Nat.card_congr e.toEquiv]; exact h)
  · rw [blockZ_map_injective f hf, blockU_map_injective f hf]
    refine ⟨(Subgroup.map_lt_map_iff_of_injective hf).mpr h5.1, ?_⟩
    intro W' hW1 hW2 hW3
    set W : Subgroup H := W'.comap f with hW
    have hWmap : W.map f = W' := by
      rw [hW, Subgroup.map_comap_eq]
      exact inf_eq_right.mpr (hW2.trans (Subgroup.map_le_range f _))
    have hW1' : blockZ L ≤ W := by
      rw [← Subgroup.map_le_map_iff_of_injective hf, hWmap]
      exact hW1
    have hW2' : W ≤ blockU L := by
      rw [← Subgroup.map_le_map_iff_of_injective hf, hWmap]
      exact hW2
    have hW3' : L ≤ normalizer (W : Set H) := by
      intro l hl
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hn := Subgroup.mem_normalizer_iff.mp (hW3 ⟨l, hl, rfl⟩) (f x)
      simpa [hW, Subgroup.mem_comap] using hn
    rcases h5.2 W hW1' hW2' hW3' with h | h
    · left
      rw [← hWmap, h]
    · right
      rw [← hWmap, h]

theorem isSubnormal_map_injective {X L : Subgroup H}
    (h : (L.subgroupOf X).IsSubnormal) : ((L.map f).subgroupOf (X.map f)).IsSubnormal := by
  let e : ↥X ≃* ↥(X.map f) := X.equivMapOfInjective f hf
  have h1 := h.map (f := e.toMonoidHom) e.surjective
  have h2 : (L.subgroupOf X).map e.toMonoidHom = (L.map f).subgroupOf (X.map f) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · intro hy
      obtain ⟨l, hl, hly⟩ := hy
      obtain ⟨x, hx, rfl⟩ : ∃ x : ↥X, e x = y := e.surjective y
      refine ⟨x, ?_, rfl⟩
      have : (x : H) = l := hf (show f (x : H) = f l from hly.symm)
      exact Subgroup.mem_subgroupOf.mpr (by rw [this]; exact hl)
  rw [h2] at h1
  exact h1

end Map

end CFSG.QuasithinUnique.Setup.Wreath
