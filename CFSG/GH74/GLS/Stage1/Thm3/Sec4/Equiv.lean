module

public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Basic
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec4

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

variable {G : Type} [Group G]

abbrev cmap (c : G) (H : Subgroup G) : Subgroup G := H.map (MulAut.conj c).toMonoidHom

theorem mem_cmap {c x : G} {H : Subgroup G} : x ∈ cmap c H ↔ c⁻¹ * x * c ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : c⁻¹ * (c * y * c⁻¹) * c = y := by group
    simpa [MulAut.conj_apply, e] using hy
  · intro h
    exact ⟨c⁻¹ * x * c, h, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩

theorem cmap_cmap (c d : G) (H : Subgroup G) : cmap c (cmap d H) = cmap (c * d) H := by
  ext x
  simp only [mem_cmap]
  rw [show (c * d)⁻¹ * x * (c * d) = d⁻¹ * (c⁻¹ * x * c) * d by group]

theorem cmap_inv_cancel (c : G) (H : Subgroup G) : cmap c⁻¹ (cmap c H) = H := by
  rw [cmap_cmap, inv_mul_cancel]
  ext x
  simp

theorem cmap_cancel (c : G) (H : Subgroup G) : cmap c (cmap c⁻¹ H) = H := by
  have := cmap_inv_cancel c⁻¹ H
  rwa [inv_inv] at this

section Fin

variable [Finite G]

theorem isPCompIn_cmap {X K : Subgroup G} (h : IsPCompIn 2 X K) (c : G) :
    IsPCompIn 2 (cmap c X) (cmap c K) :=
  isPCompIn_map_conj h c

theorem pRank_cmap (c : G) (H : Subgroup G) : pRank 2 ↥(cmap c H) = pRank 2 ↥H :=
  (pRank_eq_of_mulEquiv' ((MulAut.conj c).subgroupMap H)).symm

omit [Finite G] in
theorem pPrimeCoreOf_cmap (c : G) (K : Subgroup G) :
    pPrimeCoreOf 2 (cmap c K) = cmap c (pPrimeCoreOf 2 K) := by
  show pPrimeCoreOf 2 (K.map (MulAut.conj c).toMonoidHom) =
    (pPrimeCoreOf 2 K).map (MulAut.conj c).toMonoidHom
  unfold pPrimeCoreOf
  let ψ : ↥K ≃* ↥(K.map (MulAut.conj c).toMonoidHom) := (MulAut.conj c).subgroupMap K
  rw [← pPrimeCore_map_iso 2 ψ, Subgroup.map_map, Subgroup.map_map]
  congr 1

omit [Finite G] in
theorem cmap_mem_centralizerSection {K M : Subgroup G} {x : G}
    (hx : x ∈ centralizerSection K M) (c : G) :
    c * x * c⁻¹ ∈ centralizerSection (cmap c K) (cmap c M) := by
  obtain ⟨hxK, hxM, hxc⟩ := hx
  have hnorm : ∀ (A : Subgroup G), x ∈ normalizer (A : Set G) →
      c * x * c⁻¹ ∈ normalizer (cmap c A : Set G) := by
    intro A hA
    rw [Subgroup.mem_normalizer_iff] at hA ⊢
    intro y
    have h1 := hA (c⁻¹ * y * c)
    rw [mem_cmap, mem_cmap]
    rw [show c⁻¹ * (c * x * c⁻¹ * y * (c * x * c⁻¹)⁻¹) * c = x * (c⁻¹ * y * c) * x⁻¹ by group]
    exact h1
  refine ⟨hnorm K hxK, hnorm M hxM, fun k hk => ?_⟩
  rw [mem_cmap] at hk
  rw [mem_cmap]
  have h2 := hxc (c⁻¹ * k * c) hk
  have e : c⁻¹ * ⁅k, c * x * c⁻¹⁆ * c = ⁅c⁻¹ * k * c, x⁆ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact h2

theorem pLayerOf_cmap (c : G) (X : Subgroup G) :
    pLayerOf 2 (cmap c X) = cmap c (pLayerOf 2 X) := by
  have hset : {L | IsPCompIn 2 (cmap c X) L} = (cmap c) '' {L | IsPCompIn 2 X L} := by
    ext L
    constructor
    · intro hL
      refine ⟨cmap c⁻¹ L, ?_, cmap_cancel c L⟩
      have := isPCompIn_cmap hL c⁻¹
      rwa [cmap_inv_cancel] at this
    · rintro ⟨L', hL', rfl⟩
      exact isPCompIn_cmap hL' c
  unfold pLayerOf
  rw [hset, sSup_image]
  exact ((Subgroup.gc_map_comap (MulAut.conj c).toMonoidHom).l_sSup).symm

theorem pumpUp_cmap (c : G) (K : Subgroup G) (y : G) :
    pumpUp 2 (cmap c K) (c * y * c⁻¹) = cmap c (pumpUp 2 K y) := by
  have h1 : centralizer ({c * y * c⁻¹} : Set G) = cmap c (centralizer ({y} : Set G)) :=
    (map_centralizer_singleton_conj y c).symm
  have h2 : cmap c K ⊓ centralizer ({c * y * c⁻¹} : Set G) =
      cmap c (K ⊓ centralizer ({y} : Set G)) := by
    rw [h1]
    exact (Subgroup.map_inf K _ (MulAut.conj c).toMonoidHom (MulAut.conj c).injective).symm
  unfold pumpUp
  rw [h2, h1, pLayerOf_cmap, pLayerOf_cmap]
  apply le_antisymm
  · refine iSup₂_le fun g hg => ?_
    rintro x ⟨w, hw, rfl⟩
    rw [mem_cmap]
    have hg' : c⁻¹ * g * c ∈ pLayerOf 2 (centralizer ({y} : Set G)) := mem_cmap.1 hg
    have hw' : c⁻¹ * w * c ∈ pLayerOf 2 (K ⊓ centralizer ({y} : Set G)) := mem_cmap.1 hw
    have e : c⁻¹ * ((MulAut.conj g).toMonoidHom w) * c =
        (MulAut.conj (c⁻¹ * g * c)).toMonoidHom (c⁻¹ * w * c) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
    rw [e]
    exact Subgroup.mem_iSup_of_mem (c⁻¹ * g * c) (Subgroup.mem_iSup_of_mem hg' ⟨_, hw', rfl⟩)
  · rw [show cmap c (⨆ g ∈ pLayerOf 2 (centralizer ({y} : Set G)),
        (pLayerOf 2 (K ⊓ centralizer ({y} : Set G))).map (MulAut.conj g).toMonoidHom) =
      (⨆ g ∈ pLayerOf 2 (centralizer ({y} : Set G)),
        (pLayerOf 2 (K ⊓ centralizer ({y} : Set G))).map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj c).toMonoidHom from rfl]
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun g' hg' => ?_
    rintro x ⟨w, hw, rfl⟩
    rw [Subgroup.mem_comap]
    have e : (MulAut.conj c).toMonoidHom ((MulAut.conj g').toMonoidHom w) =
        (MulAut.conj (c * g' * c⁻¹)).toMonoidHom ((MulAut.conj c).toMonoidHom w) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
    rw [e]
    have hg : c * g' * c⁻¹ ∈ cmap c (pLayerOf 2 (centralizer ({y} : Set G))) := by
      rw [mem_cmap]
      simpa [mul_assoc] using hg'
    exact Subgroup.mem_iSup_of_mem (c * g' * c⁻¹) (Subgroup.mem_iSup_of_mem hg
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hw)))

theorem isILo_cmap {x : G} {K : Subgroup G} (h : IsILo 2 x K) (c : G) :
    IsILo 2 (c * x * c⁻¹) (cmap c K) := by
  obtain ⟨hord, hrk, hK⟩ := h
  have hC : centralizer ({c * x * c⁻¹} : Set G) = cmap c (centralizer ({x} : Set G)) :=
    (map_centralizer_singleton_conj x c).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [orderOf_conj_eq]; exact hord
  · rw [hC, pRank_cmap]; exact hrk
  · rw [hC]; exact isPCompIn_cmap hK c

theorem pumpUpLT_cmap {x x' : G} {K K' : Subgroup G} (h : PumpUpLT 2 x K x' K') (c : G) :
    PumpUpLT 2 (c * x * c⁻¹) (cmap c K) (c * x' * c⁻¹) (cmap c K') := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨isILo_cmap h1 c, isILo_cmap h2 c, ?_, ?_, ?_⟩
  · have hC : centralizer ({c * x * c⁻¹} : Set G) = cmap c (centralizer ({x} : Set G)) :=
      (map_centralizer_singleton_conj x c).symm
    rw [hC, mem_cmap]
    simpa [mul_assoc] using h3
  · rw [pPrimeCoreOf_cmap]
    exact cmap_mem_centralizerSection h4 c
  · have := isPCompIn_cmap h5 c
    rwa [← pumpUp_cmap] at this

theorem longPumpUp_cmap {x x' : G} {K K' : Subgroup G} (h : LongPumpUp 2 x K x' K') (c : G) :
    LongPumpUp 2 (c * x * c⁻¹) (cmap c K) (c * x' * c⁻¹) (cmap c K') := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨isILo_cmap h1 c, ?_⟩
  exact Relation.ReflTransGen.lift (fun p : G × Subgroup G => (c * p.1 * c⁻¹, cmap c p.2))
    (fun a b hab => pumpUpLT_cmap hab c) _ _ h2

omit [Finite G] in
theorem nonempty_quot_cmap (c : G) (K : Subgroup G) :
    Nonempty ((↥(cmap c K) ⧸ pPrimeCore 2 ↥(cmap c K)) ≃* (↥K ⧸ pPrimeCore 2 ↥K)) := by
  let e : ↥K ≃* ↥(K.map (MulAut.conj c).toMonoidHom) := (MulAut.conj c).subgroupMap K
  exact ⟨(QuotientGroup.congr (pPrimeCore 2 ↥K) (pPrimeCore 2 ↥(K.map (MulAut.conj c).toMonoidHom))
    e (pPrimeCore_map_iso 2 e)).symm⟩

theorem isPRigid_cmap {x : G} {K : Subgroup G} (h : IsPRigid 2 x K) (c : G) :
    IsPRigid 2 (c * x * c⁻¹) (cmap c K) := by
  refine ⟨isILo_cmap h.1 c, fun x' K' hl => ?_⟩
  obtain ⟨K'', rfl⟩ : ∃ K'', K' = cmap c K'' := ⟨cmap c⁻¹ K', (cmap_cancel c K').symm⟩
  have hl' := longPumpUp_cmap hl c⁻¹
  have e1 : c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x := by group
  rw [e1, cmap_inv_cancel, cmap_inv_cancel] at hl'
  obtain ⟨e⟩ := h.2 _ K'' hl'
  obtain ⟨eA⟩ := nonempty_quot_cmap c K''
  obtain ⟨eB⟩ := nonempty_quot_cmap c K
  exact ⟨(eA.trans e).trans eB.symm⟩

end Fin

theorem conj_fix_of_mem_centralizer {z c : G} (hc : c ∈ centralizer ({z} : Set G)) :
    c * z * c⁻¹ = z := by
  have : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.1 hc
  rw [this]; group

theorem isRigidRankOneComp_cmap [Finite G] {z : G} {K : Subgroup G} (h : IsRigidRankOneComp z K)
    {c : G} (hc : c ∈ centralizer ({z} : Set G)) : IsRigidRankOneComp z (cmap c K) := by
  refine ⟨?_, ?_⟩
  · have := isPRigid_cmap h.1 c
    rwa [conj_fix_of_mem_centralizer hc] at this
  · rw [pRank_cmap]; exact h.2

end CFSG.GH74.GLS.Stage1.Thm3.Sec4
