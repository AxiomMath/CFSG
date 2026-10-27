module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerSemidihedralTwoComponents

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Eight

@[expose] noncomputable def oddBarAut (Y : Type*) [Group Y] :
    MulAut Y →* MulAut (Y ⧸ pPrimeCore 2 Y) where
  toFun φ := QuotientGroup.congr (pPrimeCore 2 Y) (pPrimeCore 2 Y) φ (pPrimeCore_map_iso 2 φ)
  map_one' := by
    ext y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rfl
  map_mul' φ ψ := by
    ext y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rfl

theorem oddBarAut_apply_mk (Y : Type*) [Group Y] (φ : MulAut Y) (y : Y) :
    oddBarAut Y φ (y : Y ⧸ pPrimeCore 2 Y) = ((φ y : Y) : Y ⧸ pPrimeCore 2 Y) := rfl

variable {G : Type*} [Group G]

@[expose] noncomputable def oddBarAction (L : Subgroup G) :
    normalizer (L : Set G) →* MulAut (L ⧸ pPrimeCore 2 L) :=
  (oddBarAut L).comp L.normalizerMonoidHom

theorem oddBarAction_apply_mk (L : Subgroup G) (g : normalizer (L : Set G)) (l : L) :
    oddBarAction L g (l : L ⧸ pPrimeCore 2 L) =
      ((⟨(g : G) * l * (g : G)⁻¹, (mem_normalizer_iff.mp g.2 l).mp l.2⟩ : L) :
        L ⧸ pPrimeCore 2 L) := rfl

theorem mem_ker_oddBarAction {L : Subgroup G} {g : normalizer (L : Set G)} :
    g ∈ (oddBarAction L).ker ↔ (g : G) ∈ coreActionKernel L := by
  have hON : (g : G) ∈ normalizer ((pPrimeCore 2 L).map L.subtype : Set G) :=
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic L (pPrimeCore 2 L) g.2
  rw [MonoidHom.mem_ker, mem_coreActionKernel]
  have key : ∀ l : L, (oddBarAction L g (l : L ⧸ pPrimeCore 2 L) = (l : L ⧸ pPrimeCore 2 L)) ↔
      (l : G)⁻¹ * (g : G)⁻¹ * l * g ∈ (pPrimeCore 2 L).map L.subtype := by
    intro l
    rw [oddBarAction_apply_mk, eq_comm, QuotientGroup.eq]
    rw [← mem_map_iff_mem L.subtype_injective]
    simp only [map_mul, map_inv, Subgroup.coe_subtype]
    constructor
    · intro h1
      have h2 := (mem_normalizer_iff.mp (inv_mem hON) _).mp (inv_mem h1)
      rw [show (g : G)⁻¹ * ((l : G)⁻¹ * ((g : G) * l * (g : G)⁻¹))⁻¹ * (g : G)⁻¹⁻¹ =
        (l : G)⁻¹ * (g : G)⁻¹ * l * g by group] at h2
      exact h2
    · intro h1
      have h2 := (mem_normalizer_iff.mp hON _).mp (inv_mem h1)
      rw [show (g : G) * ((l : G)⁻¹ * (g : G)⁻¹ * l * g)⁻¹ * (g : G)⁻¹ =
        (l : G)⁻¹ * ((g : G) * l * (g : G)⁻¹) by group] at h2
      exact h2
  constructor
  · intro h1
    refine ⟨g.2, fun j hj => (key ⟨j, hj⟩).mp ?_⟩
    rw [h1]
    rfl
  · rintro ⟨-, h1⟩
    ext y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    exact (key l).mpr (h1 l l.2)

theorem oddBarAction_of_mem {L : Subgroup G} (l : L) :
    oddBarAction L ⟨l, le_normalizer l.2⟩ =
      MulAut.conj ((l : L) : L ⧸ pPrimeCore 2 L) := by
  ext y
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
  rw [oddBarAction_apply_mk, MulAut.conj_apply]
  rfl

theorem mem_fixedPoints_oddBarAction {L : Subgroup G} (g : normalizer (L : Set G)) {l : L}
    (hl : (g : G) * l = l * g) :
    oddBarAction L g (l : L ⧸ pPrimeCore 2 L) = (l : L ⧸ pPrimeCore 2 L) := by
  rw [oddBarAction_apply_mk]
  congr 1
  apply Subtype.ext
  change (g : G) * l * (g : G)⁻¹ = l
  rw [hl, mul_inv_cancel_right]

end Eight

end CFSG.ComponentClassification.GSThmB
