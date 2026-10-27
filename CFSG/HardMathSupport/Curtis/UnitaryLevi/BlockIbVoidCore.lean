module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIbThreeDefs
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReduceTypes
public import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ToralReduce CFSG.Open
open scoped commutatorElement

section Generic

variable {X : Type*} [Group X]

theorem le_of_perfect_of_isSolvable {P C D : Subgroup X}
    (hPC : P ≤ Subgroup.normalizer (C : Set X)) (hP : Group.IsSolvable P) (hD : ⁅D, D⁆ = D)
    (hDle : D ≤ P ⊔ C) : D ≤ C := by
  set N : Subgroup X := P ⊔ C with hN
  have hCN : C ≤ N := le_sup_right
  have hPN : P ≤ N := le_sup_left
  have hnorm : N ≤ Subgroup.normalizer (C : Set X) :=
    sup_le hPC Subgroup.le_normalizer
  have : (C.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).mpr hnorm
  let π : ↥N →* ↥N ⧸ C.subgroupOf N := QuotientGroup.mk' (C.subgroupOf N)
  let f : ↥P →* ↥N ⧸ C.subgroupOf N := π.comp (Subgroup.inclusion hPN)
  have hf : Function.Surjective f := by
    have hsup : P.subgroupOf N ⊔ C.subgroupOf N = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hPN hCN, ← hN]
      exact Subgroup.subgroupOf_self (H := N)
    rintro q
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf N) q
    have hn : n ∈ P.subgroupOf N ⊔ C.subgroupOf N := by rw [hsup]; trivial
    obtain ⟨a, ha, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hn
    refine ⟨⟨a.1, ha⟩, ?_⟩
    show π a = π (a * c)
    have h1 : π c = 1 := (QuotientGroup.eq_one_iff c).mpr hc
    rw [map_mul, h1, mul_one]
  have : Group.IsSolvable (↥N ⧸ C.subgroupOf N) := Group.isSolvable_of_surjective hf
  set D' : Subgroup ↥N := D.subgroupOf N with hD'
  have hD'p : ⁅D', D'⁆ = D' := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator, hD', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hDle, hD]
  set D'' : Subgroup (↥N ⧸ C.subgroupOf N) := D'.map π with hD''
  have hD''p : ⁅D'', D''⁆ = D'' := by rw [hD'', ← Subgroup.map_commutator, hD'p]
  have hbot : D'' = ⊥ := by
    obtain ⟨n, hn⟩ := (inferInstance : Group.IsSolvable (↥N ⧸ C.subgroupOf N)).solvable
    have : ∀ k, D'' ≤ derivedSeries (↥N ⧸ C.subgroupOf N) k := by
      intro k
      induction k with
      | zero => rw [derivedSeries_zero]; exact le_top
      | succ k ih =>
        rw [derivedSeries_succ, ← hD''p]
        exact Subgroup.commutator_mono ih ih
    exact le_bot_iff.mp (hn ▸ this n)
  intro d hd
  have hdN : d ∈ N := hDle hd
  have hmem : (⟨d, hdN⟩ : ↥N) ∈ D' := hd
  have : π ⟨d, hdN⟩ ∈ D'' := ⟨_, hmem, rfl⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp this))

end Generic

section Void

variable {G : Type} [Group G] [Finite G] {M S L : Subgroup G}
  {D : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} {x : ↥M ⧸ CFSG.pCore 2 ↥M}

omit [Finite G] in
theorem blockPL_le_normalizer_centralizer (M S L : Subgroup G) :
    blockPL M S L ≤ Subgroup.normalizer
      (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Set _) := by
  have hle : blockPL M S L ≤ barM M L :=
    barM_mono inf_le_right
  intro p hp c
  have hp' : p ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    Subgroup.le_normalizer (hle hp)
  have key : ∀ q ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
      ∀ c ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)),
        q * c * q⁻¹ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro q hq c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro a ha
    have hqa : q⁻¹ * a * q ∈ barM M L := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hq) a).mp ha
      simpa using this
    have h1 := hc _ hqa
    calc a * (q * c * q⁻¹) = q * ((q⁻¹ * a * q) * c) * q⁻¹ := by group
      _ = q * (c * (q⁻¹ * a * q)) * q⁻¹ := by rw [h1]
      _ = q * c * q⁻¹ * a := by group
  exact ⟨fun hc => key p hp' c hc, fun hc => by
    have := key p⁻¹ (inv_mem hp') _ hc
    simpa [mul_assoc] using this⟩


theorem false_of_isSolvable_blockPL (h : BlockThreeIbHyp M S L D x)
    (hP : Group.IsSolvable (blockPL M S L)) : False := by
  obtain ⟨-, -, -, -, -, -, -, -, hDp, hDle, -, -, hxD, -, hxC, -⟩ := h
  exact hxC (le_of_perfect_of_isSolvable (blockPL_le_normalizer_centralizer M S L) hP hDp hDle hxD)

theorem false_of_nineThreeFour (h : BlockThreeIbHyp M S L D x) (h4 : NineThreeFour M S L) :
    False := by
  obtain ⟨-, -, -, -, -, hZ, -⟩ := h
  rw [h4.2.1] at hZ
  exact absurd hZ (by norm_num)

theorem false_of_nineThreeEight (h : BlockThreeIbHyp M S L D x) (h8 : NineThreeEight M S L) :
    False := by
  obtain ⟨-, -, -, -, -, -, -, hcyc, -⟩ := h
  obtain ⟨-, N, r, ⟨m, hm⟩, hr, h0, h2, h4, -, φ, -⟩ := h8
  obtain ⟨hp, hE⟩ := alternatingGroup_perfect_hasE9 (m := N - 2 * r) (by omega)
  exact false_of_cyc_of_surjective (hcyc : CycPerfect 3 (blockPL M S L))
    ((MonoidHom.snd _ _).comp (φ.toMonoidHom.comp (QuotientGroup.mk' _)))
    (Prod.snd_surjective.comp (φ.surjective.comp (QuotientGroup.mk'_surjective _)))
    (B := alternatingGroup (Fin (N - 2 * r))) hp hE

end Void

end CFSG.HardMathSupport.Curtis.UnitaryLevi
