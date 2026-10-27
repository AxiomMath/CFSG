module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A6Clause

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.FFModules CFSG.AGLEmbedding
  CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open scoped commutatorElement

variable {X : Type} [Group X] {T : Subgroup X} (hV : IsElemAbelian 2 (gnV T))
  [Module (ZMod 2) (Additive (IntMod (gnV T) hV))]

theorem card_modOf {U : Subgroup X} (hUV : U ≤ gnV T) :
    Nat.card (modOf hV U) = Nat.card U := by
  rw [← card_subOf hV (modOf hV U), subOf_modOf hV hUV]

theorem isInvariant_modOf_of_conj (L : Subgroup (X ⧸ gnC T)) {U : Subgroup X}
    (hU : ∀ k ∈ L.comap (QuotientGroup.mk' (gnC T)), ∀ u ∈ U, k * u * k⁻¹ ∈ U) :
    CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant (gnRep hV) L (modOf hV U) := by
  refine isInvariant_modOf hV L fun k hk => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => by simpa using hU k hk h hh, fun hh => ?_⟩
  have hk' : k⁻¹ ∈ L.comap (QuotientGroup.mk' (gnC T)) := Subgroup.inv_mem _ hk
  have := hU k⁻¹ hk' _ hh
  simpa [mul_assoc] using this

theorem sub_mem_modOf_of_commutator_le (L : Subgroup (X ⧸ gnC T)) {W' U : Subgroup X}
    (hWV : W' ≤ gnV T)
    (hWU : ⁅W', L.comap (QuotientGroup.mk' (gnC T))⁆ ≤ U)
    {l : X ⧸ gnC T} (hl : l ∈ L) {w : Additive (IntMod (gnV T) hV)} (hw : w ∈ modOf hV W') :
    gnRep hV l w - w ∈ modOf hV U := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective l
  have hg : g ∈ L.comap (QuotientGroup.mk' (gnC T)) := hl
  change elt hV (gnRep hV (QuotientGroup.mk g) w - w) ∈ U
  rw [elt_sub, elt_gnRep]
  have hc := Subgroup.commutator_mem_commutator (show elt hV w ∈ W' from hw) hg
  rw [commutatorElement_def] at hc
  have := U.inv_mem (hWU hc)
  simpa [mul_assoc] using this

theorem mem_gnImg_inf_centralizer_iff (ℓ : Submodule (ZMod 2) (Additive (IntMod (gnV T) hV)))
    (s : X ⧸ gnC T) :
    s ∈ gnImg T (T ⊓ Subgroup.centralizer (subOf hV ℓ : Set X)) ↔
      s ∈ gnImg T T ∧ ∀ w ∈ ℓ, gnRep hV s w = w := by
  constructor
  · rintro ⟨x, ⟨hxT, hxc⟩, rfl⟩
    refine ⟨⟨x, hxT, rfl⟩, fun w hw => ?_⟩
    apply elt_injective hV
    have hmem : elt hV w ∈ subOf hV ℓ := (elt_mem_subOf hV).mpr hw
    have h1 := Subgroup.mem_centralizer_iff.mp hxc _ hmem
    change elt hV (gnRep hV (QuotientGroup.mk x) w) = elt hV w
    rw [elt_gnRep, ← h1]
    group
  · rintro ⟨⟨x, hxT, rfl⟩, hfix⟩
    refine ⟨x, ⟨hxT, ?_⟩, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    rintro _ ⟨w, hw, rfl⟩
    have h1 := congrArg (elt hV) (hfix w hw)
    change elt hV (gnRep hV (QuotientGroup.mk x) w) = elt hV w at h1
    rw [elt_gnRep] at h1
    calc elt hV w * x = x * elt hV w * x⁻¹ * x := by rw [h1]
      _ = x * elt hV w := by group

end CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
