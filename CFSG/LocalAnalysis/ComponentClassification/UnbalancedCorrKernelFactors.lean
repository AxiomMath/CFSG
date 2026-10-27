module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrKernelTools
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerIsoCorrSylowGrowth

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G]

theorem mem_coreActionKernel_subgroupOf_iff {Y V : Subgroup G} (hVY : V ≤ Y) (h : Y) :
    h ∈ UnbalancedLayer.coreActionKernel (V.subgroupOf Y) ↔
      (h : G) ∈ UnbalancedLayer.coreActionKernel V := by
  have hO : ∀ y : Y, y ∈ (pPrimeCore 2 ↥(V.subgroupOf Y)).map (V.subgroupOf Y).subtype ↔
      (y : G) ∈ (pPrimeCore 2 ↥V).map V.subtype := by
    intro y
    rw [← pPrimeCore_map_subgroupOf 2 V Y hVY]
    exact (mem_map_iff_mem Y.subtype_injective).symm
  rw [UnbalancedLayer.mem_coreActionKernel, UnbalancedLayer.mem_coreActionKernel]
  constructor
  · rintro ⟨hN, hk⟩
    refine ⟨UnbalancedLayer.mem_normalizer_of_subgroupOf hVY hN, fun v hv => ?_⟩
    have h1 := (hO _).mp (hk ⟨v, hVY hv⟩ (show (⟨v, hVY hv⟩ : Y) ∈ V.subgroupOf Y from hv))
    exact h1
  · rintro ⟨hN, hk⟩
    refine ⟨UnbalancedLayer.mem_normalizer_subgroupOf_of_mem hN, fun v hv => ?_⟩
    exact (hO _).mpr (hk (v : G) hv)

theorem mem_coreActionKernel_iff_mem_fusionZStar {V : Subgroup G} (v : V) :
    (v : G) ∈ UnbalancedLayer.coreActionKernel V ↔ v ∈ CFSG.Open.fusionZStar ↥V := by
  set O := CFSG.Open.fusionOddCore ↥V
  have hOeq : O = pPrimeCore 2 ↥V := UnbalancingLocal.fusionOddCore_eq_pPrimeCore ↥V
  have hmem : ∀ u : V, (u : G) ∈ (pPrimeCore 2 ↥V).map V.subtype ↔ u ∈ O := by
    intro u
    rw [hOeq]
    exact mem_map_iff_mem V.subtype_injective
  show _ ↔ QuotientGroup.mk' O v ∈ center (↥V ⧸ O)
  rw [UnbalancedLayer.mem_coreActionKernel, mem_center_iff]
  constructor
  · rintro ⟨-, hk⟩ q
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective O q
    apply (quotient_commute_iff u v).mpr
    apply (hmem _).mp
    exact hk (u : G) u.2
  · intro hc
    refine ⟨le_normalizer v.2, fun u hu => ?_⟩
    have h1 := (quotient_commute_iff (N := O) ⟨u, hu⟩ v).mp (hc _)
    exact (hmem (⟨u, hu⟩⁻¹ * v⁻¹ * ⟨u, hu⟩ * v)).mpr h1

theorem center_eq_bot_of_sup_centerless {S₁ S₂ W : Subgroup G} (hW : S₁ ⊔ S₂ = W)
    (hZ : W ⊓ centralizer (W : Set G) = ⊥) (hc : S₁ = S₂ ∨ ∀ x ∈ S₁, ∀ y ∈ S₂, x * y = y * x) :
    center ↥S₁ = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [mem_bot]
  have hzS : ∀ x ∈ S₁, x * (z : G) = z * x := fun x hx =>
    congrArg Subtype.val (mem_center_iff.mp hz ⟨x, hx⟩)
  have hle : W ≤ centralizer ({(z : G)} : Set G) := by
    rw [← hW]
    refine sup_le (fun x hx => mem_centralizer_singleton_iff.mpr (hzS x hx)) fun y hy => ?_
    rw [mem_centralizer_singleton_iff]
    rcases hc with h | h
    · exact hzS y (h ▸ hy)
    · exact (h z z.2 y hy).symm
  have hzW : (z : G) ∈ W := hW ▸ mem_sup_left z.2
  have hzC : (z : G) ∈ centralizer (W : Set G) :=
    mem_centralizer_iff.mpr fun w hw => mem_centralizer_singleton_iff.mp (hle hw)
  have h1 : (z : G) ∈ W ⊓ centralizer (W : Set G) := mem_inf.mpr ⟨hzW, hzC⟩
  rw [hZ, mem_bot] at h1
  exact Subtype.ext h1

theorem isSimpleGroup_of_isQuasisimple_of_center_eq_bot {Q : Type*} [Group Q]
    (hQ : IsQuasisimple Q) (hZ : center Q = ⊥) : IsSimpleGroup Q := by
  have := hQ.2.1
  exact ((QuotientGroup.quotientBot (G := Q)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hZ.symm)).isSimpleGroup

theorem exists_ne_of_isQuasisimple {Q : Type*} [Group Q] (hQ : IsQuasisimple Q) :
    ∃ u v : Q, u * v ≠ v * u := by
  obtain ⟨u, v, huv⟩ := hQ.2.2
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (center Q) u
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (center Q) v
  refine ⟨u, v, fun h => huv ?_⟩
  rw [← map_mul, ← map_mul, h]

theorem isSimpleGroup_of_sup_centerless {S₁ S₂ W : Subgroup G} (h₁ : IsQuasisimple ↥S₁)
    (hW : S₁ ⊔ S₂ = W) (hZ : W ⊓ centralizer (W : Set G) = ⊥)
    (hc : S₁ = S₂ ∨ ∀ x ∈ S₁, ∀ y ∈ S₂, x * y = y * x) : IsSimpleGroup ↥S₁ :=
  isSimpleGroup_of_isQuasisimple_of_center_eq_bot h₁ (center_eq_bot_of_sup_centerless hW hZ hc)

theorem exists_simple_factors_of_sup {S₁ S₂ W : Subgroup G} (h₁ : IsQuasisimple ↥S₁)
    (h₂ : IsQuasisimple ↥S₂) (hW : S₁ ⊔ S₂ = W) (hZ : W ⊓ centralizer (W : Set G) = ⊥)
    (hc : S₁ = S₂ ∨ ∀ x ∈ S₁, ∀ y ∈ S₂, x * y = y * x) :
    ∃ (ι : Type) (_ : Finite ι) (S : ι → Subgroup G), (Nat.card ι = 1 ∨ Nat.card ι = 2) ∧
      (∀ i, IsSimpleGroup ↥(S i)) ∧ (∀ i, ∃ u v : ↥(S i), u * v ≠ v * u) ∧
      (Pairwise fun i j => ∀ u v : G, u ∈ S i → v ∈ S j → Commute u v) ∧ iSupIndep S ∧
      ⨆ i, S i = W := by
  have hc' : S₂ = S₁ ∨ ∀ x ∈ S₂, ∀ y ∈ S₁, x * y = y * x := by
    rcases hc with h | h
    · exact Or.inl h.symm
    · exact Or.inr fun x hx y hy => (h y hy x hx).symm
  have hs₁ := isSimpleGroup_of_sup_centerless h₁ hW hZ hc
  have hs₂ := isSimpleGroup_of_sup_centerless h₂ ((sup_comm S₂ S₁).trans hW) hZ hc'
  by_cases h12 : S₁ = S₂
  · refine ⟨Unit, inferInstance, fun _ => S₁, Or.inl Nat.card_unique, fun _ => hs₁,
      fun _ => exists_ne_of_isQuasisimple h₁, fun i j hij => absurd (Subsingleton.elim i j) hij,
      ?_, ?_⟩
    · intro i
      have h1 : (⨆ (j : Unit) (_ : j ≠ i), S₁) = ⊥ := by
        refine le_bot_iff.mp (iSup₂_le fun j hj => absurd (Subsingleton.elim j i) hj)
      rw [h1]
      exact disjoint_bot_right
    · rw [iSup_const, ← hW, ← h12, sup_idem]
  · have hcomm := hc.resolve_left h12
    have hdisj : Disjoint S₁ S₂ := by
      rw [disjoint_iff, eq_bot_iff]
      intro x hx
      obtain ⟨hx₁, hx₂⟩ := mem_inf.mp hx
      have hZ₁ := center_eq_bot_of_sup_centerless hW hZ hc
      have hxc : (⟨x, hx₁⟩ : S₁) ∈ center ↥S₁ := mem_center_iff.mpr fun y =>
        Subtype.ext (hcomm y y.2 x hx₂)
      rw [hZ₁, mem_bot] at hxc
      exact mem_bot.mpr (congrArg Subtype.val hxc)
    refine ⟨Bool, inferInstance, fun t => cond t S₁ S₂, Or.inr ?_, fun t => ?_, fun t => ?_,
      ?_, ?_, ?_⟩
    · rw [Nat.card_eq_fintype_card, Fintype.card_bool]
    · cases t
      · exact hs₂
      · exact hs₁
    · cases t
      · exact exists_ne_of_isQuasisimple h₂
      · exact exists_ne_of_isQuasisimple h₁
    · intro i j hij u v hu hv
      cases i <;> cases j
      · exact absurd rfl hij
      · exact (hcomm v hv u hu).symm
      · exact hcomm u hu v hv
      · exact absurd rfl hij
    · rw [iSupIndep_pair (i := true) (j := false) (by decide) (fun k => by cases k <;> simp)]
      exact hdisj
    · rw [iSup_bool_eq]
      exact hW

end CFSG.ComponentClassification.UnbalancedCorr
