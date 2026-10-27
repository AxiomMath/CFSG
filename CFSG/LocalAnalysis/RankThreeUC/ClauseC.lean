module

public import CFSG.LocalAnalysis.RankThreeUC.Focal
import CFSG.LocalAnalysis.RankThreeUC.WreathQuotient

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem wreathIndexThree :
    ∀ (X : Type) [Group X] [Finite X], Odd (Nat.card X) → Group.IsSolvable X →
      ∀ S : Sylow 3 X, (S : Subgroup X) ≠ ⊥ →
        (∃ f : (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)) →* (S : Subgroup X),
          Function.Surjective f) →
        ∃ N : Subgroup X, N.Normal ∧ N.index = 3 :=
  fun X _ _ hodd hsolv S hS hf => exists_normal_index_three_of_wreath X hodd hsolv S hS hf

private theorem exists_normal_index_three_of_odd_quotient {H : Type} [Group H] [Finite H]
    (hsolv : Group.IsSolvable H) {K : Subgroup H} [K.Normal]
    (hodd : Odd K.index) (Q : Sylow 3 H) (hQK : ¬ (Q : Subgroup H) ≤ K)
    (f : (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)) →* (Q : Subgroup H))
    (hf : Function.Surjective f) :
    ∃ N : Subgroup H, N.Normal ∧ N.index = 3 := by
  have hW := wreathIndexThree
  have hπ : Function.Surjective (QuotientGroup.mk' K) := QuotientGroup.mk'_surjective K
  let S : Sylow 3 (H ⧸ K) := Q.mapSurjective hπ
  have hSeq : (S : Subgroup (H ⧸ K)) = (Q : Subgroup H).map (QuotientGroup.mk' K) := rfl
  have hS1 : (S : Subgroup (H ⧸ K)) ≠ ⊥ := by
    intro h
    apply hQK
    rw [hSeq, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  have hsurj : Function.Surjective ((QuotientGroup.mk' K).subgroupMap (Q : Subgroup H)) :=
    (QuotientGroup.mk' K).subgroupMap_surjective _
  obtain ⟨N, hN, hNi⟩ := hW (H ⧸ K) hodd (Group.isSolvable_of_surjective hπ) S hS1
    ⟨((QuotientGroup.mk' K).subgroupMap (Q : Subgroup H)).comp f, hsurj.comp hf⟩
  refine ⟨N.comap (QuotientGroup.mk' K), hN.comap _, ?_⟩
  rw [Subgroup.index_comap_of_surjective _ hπ, hNi]

private theorem commutator_le_of_index_three {H : Type} [Group H] {N : Subgroup H} [N.Normal]
    (hN : N.index = 3) : _root_.commutator H ≤ N := by
  have : IsCyclic (H ⧸ N) := isCyclic_of_prime_card (p := 3) hN
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance

theorem IsWitness.false_of_clauseC_of_odd_index (hS : Standing G) (hUC : rankThreeUC G)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hw : IsWitness 3 P M)
    (hc : rankThreeClauseC M (P : Subgroup G)) {C : Subgroup G} (hCM : C ≤ M)
    (hMC : M ≤ normalizer (C : Set G)) (hodd : Odd (C.relIndex M))
    (hPC : ¬ (P : Subgroup G) ≤ C) : False := by
  have hPM : (P : Subgroup G) ≤ M := hw.sylow_le hS hp
  obtain ⟨hsolv, ⟨e⟩, -⟩ := hc
  have : (C.subgroupOf M).Normal := (normal_subgroupOf_iff_le_normalizer hCM).mpr hMC
  let Q : Sylow 3 M := P.subtype hPM
  have hQK : ¬ (Q : Subgroup M) ≤ C.subgroupOf M := fun h =>
    hPC fun x hx => h (show (⟨x, hPM hx⟩ : M) ∈ (Q : Subgroup M) from hx)
  let φ := e.symm.trans (subgroupOfEquivOfLe hPM).symm
  obtain ⟨N, hN, hNi⟩ := exists_normal_index_three_of_odd_quotient hsolv hodd Q hQK
    φ.toMonoidHom φ.surjective
  have hN₂M : N.map M.subtype ≤ M := Subgroup.map_subtype_le N
  have hcomm : ⁅M, M⁆ ≤ N.map M.subtype := by
    calc ⁅M, M⁆ = (_root_.commutator M).map M.subtype := by
          rw [_root_.commutator, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
      _ ≤ N.map M.subtype := Subgroup.map_mono (commutator_le_of_index_three hNi)
  have hrel : (N.map M.subtype).relIndex M = 3 := by
    rw [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    exact hNi
  exact hw.not_dvd_relIndex_of_commutator_le hS hUC hp hN₂M hcomm (by rw [hrel])

end CFSG.LocalAnalysis.RankThreeUC
