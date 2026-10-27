module

public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LieType.Multipliers.U62SylowInputs
public import Certificates.Certificate10018
public meta import CFSG.LieType.Multipliers.ProductKernel
public meta import CFSG.Certificates.CosetTableCompactColumns
public meta import CFSG.Certificates.WordSubgroup
public import CFSG.LieType.Multipliers.U62Action

public section

namespace CFSG.LieType.Multipliers.U62

open CFSG.CosetTable CFSG.Certificates.CosetEnumeration

theorem sylow_card_le :
    Finite (PG 2 sylowRels) ∧ Nat.card (PG 2 sylowRels) ≤ 81 :=
  Certificates.certificate10018.1

theorem sylow_relations_eq_one :
    ∀ u ∈ sylowRels.map (substWord sylowWordsAB),
      PresentedGroup.mk {r : FreeGroup (Fin 2) | r ∈ coverAB.map FreeGroup.mk} (FreeGroup.mk u) = 1 :=
  Certificates.certificate10018.2

private theorem lift_includeAB :
    FreeGroup.lift (fun i => (PresentedGroup.of (includeAB i) : PG 4 cover₁)) =
      (PresentedGroup.mk _).comp (FreeGroup.map includeAB) := by
  apply FreeGroup.ext_hom
  intro i
  simp
  rfl

private theorem coverAB_relations :
    ∀ r ∈ wordSet coverAB,
      FreeGroup.lift (fun i => (PresentedGroup.of (includeAB i) : PG 4 cover₁)) r = 1 := by
  have hin : ∀ w ∈ coverAB, w.map (fun l => (includeAB l.1, l.2)) ∈ cover₁ := by decide
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
  rw [lift_includeAB, MonoidHom.comp_apply, FreeGroup.map.mk]
  exact PresentedGroup.one_of_mem (List.mem_map_of_mem (hin w hw))

private noncomputable def includeCover : PG 2 coverAB →* PG 4 cover₁ :=
  PresentedGroup.toGroup coverAB_relations

private theorem includeCover_mk (w : List (Fin 2 × Bool)) :
    includeCover (PresentedGroup.mk _ (FreeGroup.mk w)) =
      PresentedGroup.mk _ (FreeGroup.mk (w.map fun l => (includeAB l.1, l.2))) := by
  have he : includeCover.comp (PresentedGroup.mk _) =
      (PresentedGroup.mk _).comp (FreeGroup.map includeAB) := by
    apply FreeGroup.ext_hom
    intro i
    change includeCover (PresentedGroup.of i) = PresentedGroup.of (includeAB i)
    exact PresentedGroup.toGroup.of coverAB_relations
  change (includeCover.comp (PresentedGroup.mk _)) (FreeGroup.mk w) = _
  rw [he, MonoidHom.comp_apply, FreeGroup.map.mk]

private theorem sylow_relations :
    ∀ u ∈ sylowRels.map (substWord sylowWords),
      PresentedGroup.mk {r | r ∈ cover₁.map FreeGroup.mk} (FreeGroup.mk u) = 1 := by
  have hcompat : ∀ r ∈ sylowRels, substWord sylowWords r =
      (substWord sylowWordsAB r).map (fun l => (includeAB l.1, l.2)) := by decide
  intro u hu
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hu
  rw [hcompat r hr, ← includeCover_mk]
  rw [sylow_relations_eq_one _ (List.mem_map_of_mem hr), map_one]

private theorem card_le_of_word_index {m : ℕ} (ws hs : List (List (Fin m × Bool)))
    (R : List (List (Fin hs.length × Bool)))
    (hR : ∀ u ∈ R.map (substWord hs),
      PresentedGroup.mk {r | r ∈ ws.map FreeGroup.mk} (FreeGroup.mk u) = 1)
    {k cap n : ℕ} (hidx : checkHLT (colParamsShort ws hs k) cap n = true)
    [Finite (PG hs.length R)] :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n * Nat.card (PG hs.length R) := by
  let H : Subgroup (PG m ws) := Subgroup.closure
    {g | ∃ s ∈ hs, g = PresentedGroup.mk {r | r ∈ ws.map FreeGroup.mk} (FreeGroup.mk s)}
  obtain ⟨hfi, hidx'⟩ := index_le_of_checkHLT
    (goodColParamsShort ws hs k H (fun w hw => Subgroup.subset_closure ⟨w, hw, rfl⟩))
    (by simpa [colParamsShort, mkParams] using closure_colLetter ws) hidx
  obtain ⟨φ, hrange⟩ := exists_hom_range ws hs R hR
  change φ.range = H at hrange
  have hsurj : Function.Surjective (fun g => (⟨φ g, g, rfl⟩ : φ.range)) :=
    fun ⟨_, g, hg⟩ => ⟨g, Subtype.ext hg⟩
  have hfinH : Finite H := hrange ▸ Finite.of_surjective _ hsurj
  have hcardH : Nat.card H ≤ Nat.card (PG hs.length R) := by
    rw [← hrange]
    exact Nat.card_le_card_of_surjective _ hsurj
  have hfin : Finite (PG m ws) := by
    have : Finite (PG m ws ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
    exact Finite.of_subgroup_quotient H
  refine ⟨hfin, ?_⟩
  rw [← H.index_mul_card]
  exact Nat.mul_le_mul hidx' hcardH

theorem cover_card_le_of_sylow_index
    {k cap : ℕ}
    (h : checkHLT (colParamsShort cover₁ sylowWords k) cap 168960 = true) :
    Finite (PG 5 coverWs) ∧ Nat.card (PG 5 coverWs) ≤ 12 * 9196830720 := by
  obtain ⟨f₃, c₃⟩ := sylow_card_le
  have : Finite (PG sylowWords.length sylowRels) := f₃
  obtain ⟨f₁, c₁⟩ := card_le_of_word_index cover₁ sylowWords sylowRels sylow_relations h
  have c₁' : Nat.card (PG 4 cover₁) ≤ 13685760 :=
    (c₁.trans (Nat.mul_le_mul_left 168960 c₃)).trans (by norm_num)
  have : Finite (PG (subsetOf 5 [0, 1, 2, 3]).length
      (restrictWords (subsetOf 5 [0, 1, 2, 3]) coverWs)) := f₁
  obtain ⟨f₀, c₀⟩ := card_le_of_genSub_index coverWs (subsetOf 5 [0, 1, 2, 3])
    kernel_index.1 kernel_index.2
  exact ⟨f₀, (c₀.trans (Nat.mul_le_mul_left 8064 c₁')).trans (by norm_num)⟩

end CFSG.LieType.Multipliers.U62
