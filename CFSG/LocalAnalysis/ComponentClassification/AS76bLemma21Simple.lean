module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma21Quot
import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.ComponentClassification.AS76b

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

theorem layer_map_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (CFSG.layer A).map e.toMonoidHom = CFSG.layer B :=
  CFSG.WholeGroup.layer_map_mulEquiv e

theorem comap_layer_quotient_of_eq_bot {H : Type*} [Group H] (N : Subgroup H) [N.Normal]
    (hN : N = ⊥) : (CFSG.layer (H ⧸ N)).comap (QuotientGroup.mk' N) = CFSG.layer H := by
  subst hN
  rw [← layer_map_mulEquiv (QuotientGroup.quotientBot (G := H))]
  ext x
  constructor
  · intro hx
    exact ⟨QuotientGroup.mk' ⊥ x, hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (⊥ : Subgroup H) y
    exact hy

variable {G : Type} [Group G]

theorem twoPrimeLayerIn_top_eq_layer (hO : CFSG.Assembly.oddCore (⊤ : Subgroup G) = ⊥) :
    twoPrimeLayerIn (⊤ : Subgroup G) = CFSG.layer G := by
  rw [twoPrimeLayerIn, comap_layer_quotient_of_eq_bot _ hO]
  exact layer_map_mulEquiv (Subgroup.topEquiv (G := G))

theorem generalizedFitting_normal : (CFSG.generalizedFitting G).Normal :=
  (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2

variable [Finite G]

theorem isSolvable_of_generalizedFitting_comm (hF : IsSimpleGroup (CFSG.generalizedFitting G))
    (hc : ∀ a b : CFSG.generalizedFitting G, a * b = b * a) : Group.IsSolvable G := by
  set S := CFSG.generalizedFitting G with hS
  have : S.Normal := generalizedFitting_normal
  have hScyc : IsCyclic S := by
    obtain ⟨s, hs⟩ := exists_ne (1 : S)
    have hz : (zpowers s).Normal := ⟨fun n hn g => by rw [hc g n, mul_inv_cancel_right]; exact hn⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (zpowers s) with h | h
    · exact absurd (h ▸ mem_zpowers s : s ∈ (⊥ : Subgroup S)) (by simpa using hs)
    · exact ⟨⟨s, fun x => (eq_top_iff' _).mp h x⟩⟩
  have hAut : ∀ σ τ : MulAut S, σ * τ = τ * σ := by
    intro σ τ
    obtain ⟨m, hm⟩ := MonoidHom.map_cyclic σ.toMonoidHom
    obtain ⟨k, hk⟩ := MonoidHom.map_cyclic τ.toMonoidHom
    have hm' : ∀ y, σ y = y ^ m := hm
    have hk' : ∀ y, τ y = y ^ k := hk
    ext x
    rw [MulAut.mul_apply, MulAut.mul_apply, hm' (τ x), hk' x, hk' (σ x), hm' x, ← zpow_mul,
      ← zpow_mul, mul_comm]
  have : Group.IsSolvable (MulAut S) := Group.isSolvable_of_comm hAut
  have : Group.IsSolvable S := Group.isSolvable_of_comm hc
  refine Group.isSolvable_of_ker_le_range S.subtype (MulAut.conjNormal : G →* MulAut S) ?_
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have hgC : g ∈ centralizer (S : Set G) := by
    rw [mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun φ : MulAut S => ((φ ⟨x, hx⟩ : S) : G)) hg
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc x * g = g * x * g⁻¹ * g := by rw [h1]
      _ = g * x := by group
  rw [range_subtype]
  exact CFSG.centralizer_generalizedFitting_le G hgC

theorem not_isSolvable_of_isSimpleGroup {S : Type*} [Group S] [IsSimpleGroup S]
    (hnc : ¬ ∀ a b : S, a * b = b * a) : ¬ Group.IsSolvable S :=
  fun h => hnc (IsSimpleGroup.comm_iff_isSolvable.mpr h)

theorem even_card_of_isSimpleGroup {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hnc : ¬ ∀ a b : S, a * b = b * a) : Even (Nat.card S) := by
  by_contra h
  exact not_isSolvable_of_isSimpleGroup hnc
    (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.not_even_iff_odd.mp h))

theorem eq_bot_of_normal_of_odd (hF : IsSimpleGroup (CFSG.generalizedFitting G))
    (hnc : ¬ ∀ a b : CFSG.generalizedFitting G, a * b = b * a) {N : Subgroup G} [hN : N.Normal]
    (hodd : Odd (Nat.card N)) : N = ⊥ := by
  set S := CFSG.generalizedFitting G with hS
  have : S.Normal := generalizedFitting_normal
  have := hN.subgroupOf S
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf S) with h | h
  · have hNS : N ⊓ S = ⊥ := disjoint_iff.mp (subgroupOf_eq_bot.mp h)
    have hcomm : ⁅N, S⁆ = ⊥ := le_bot_iff.mp (hNS ▸ commutator_le_inf N S)
    have hNS' : N ≤ S := (commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
      (CFSG.centralizer_generalizedFitting_le G)
    rw [eq_bot_iff, ← hNS]
    exact le_inf le_rfl hNS'
  · exfalso
    have hSN : S ≤ N := fun x hx => by
      have : (⟨x, hx⟩ : S) ∈ N.subgroupOf S := h ▸ mem_top _
      exact this
    exact (Nat.not_even_iff_odd.mpr (hodd.of_dvd_nat (card_dvd_of_le hSN)))
      (even_card_of_isSimpleGroup hnc)

theorem layer_eq_generalizedFitting (hF : IsSimpleGroup (CFSG.generalizedFitting G))
    (hnc : ¬ ∀ a b : CFSG.generalizedFitting G, a * b = b * a) :
    CFSG.layer G = CFSG.generalizedFitting G := by
  set S := CFSG.generalizedFitting G with hS
  have hLS : CFSG.layer G ≤ S := le_sup_right
  have : (CFSG.layer G).Normal := by
    have := CFSG.LocalCores.layer_characteristic (G := G)
    infer_instance
  have := Subgroup.Normal.subgroupOf (inferInstance : (CFSG.layer G).Normal) S
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.layer G).subgroupOf S) with h | h
  · exfalso
    have hL : CFSG.layer G = ⊥ := by
      rw [eq_bot_iff, ← disjoint_iff.mp (subgroupOf_eq_bot.mp h)]
      exact le_inf le_rfl hLS
    have hSF : CFSG.fittingSubgroup G = S := by rw [hS, CFSG.generalizedFitting, hL, sup_bot_eq]
    have hnil : Group.IsNilpotent (CFSG.fittingSubgroup G) := inferInstance
    rw [hSF] at hnil
    have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal (G := S) (H := ⊤) top_ne_bot
    rw [top_inf_eq] at hZ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center S) with hc | hc
    · exact hZ hc
    · exact hnc fun a b => (mem_center_iff.mp (hc ▸ mem_top b) a)
  · refine le_antisymm hLS fun x hx => ?_
    have : (⟨x, hx⟩ : S) ∈ (CFSG.layer G).subgroupOf S := h ▸ mem_top _
    exact this

theorem false_of_normalIn_twoPrimeLayerIn_top {K : Subgroup G} (hK : TightlyEmbedded K)
    (hKn : ¬ K.Normal) (hF : IsSimpleGroup (CFSG.generalizedFitting G))
    (hne : twoPrimeLayerIn K ≠ oddCoreIn K)
    (hB : NormalIn (twoPrimeLayerIn K) (twoPrimeLayerIn (⊤ : Subgroup G))) : False := by
  set S := CFSG.generalizedFitting G with hS
  have hSn : S.Normal := generalizedFitting_normal
  by_cases hc : ∀ a b : S, a * b = b * a
  ·
    have hG := isSolvable_of_generalizedFitting_comm hF hc
    apply hne
    rw [twoPrimeLayerIn_eq_oddCoreIn_iff]
    have : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective K.subtype_injective
    have : Group.IsSolvable (K ⧸ CFSG.Assembly.oddCore K) := inferInstance
    have : Group.IsSolvable (CFSG.layer (K ⧸ CFSG.Assembly.oddCore K)) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective _)
    have : Group.IsPerfect (CFSG.layer (K ⧸ CFSG.Assembly.oddCore K)) :=
      CFSG.LocalCores.layer_isPerfect
    have := CFSG.ComponentClassification.SolvableKernelContainment.perfect_solvable_subsingleton
      (G := CFSG.layer (K ⧸ CFSG.Assembly.oddCore K))
    exact Subgroup.eq_bot_of_subsingleton _
  ·
    have hO : CFSG.Assembly.oddCore (⊤ : Subgroup G) = ⊥ := by
      set N := (CFSG.Assembly.oddCore (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype with hNdef
      have hNn : N.Normal := (CFSG.Assembly.oddCore_normal _).map _
        fun x => ⟨⟨x, mem_top x⟩, rfl⟩
      have hNodd : Odd (Nat.card N) := by
        rw [hNdef, card_map_of_injective (Subgroup.subtype_injective _)]
        exact odd_card_assemblyOddCore _
      have hN1 := eq_bot_of_normal_of_odd hF hc hNodd
      exact (map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp hN1
    have hM : twoPrimeLayerIn (⊤ : Subgroup G) = S :=
      (twoPrimeLayerIn_top_eq_layer hO).trans (layer_eq_generalizedFitting hF hc)
    rw [hM] at hB
    obtain ⟨hle, hn⟩ := hB
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((twoPrimeLayerIn K).subgroupOf S) with h | h
    ·
      have hK'1 : twoPrimeLayerIn K = ⊥ := by
        rw [eq_bot_iff, ← disjoint_iff.mp (subgroupOf_eq_bot.mp h)]
        exact le_inf le_rfl hle
      apply hne
      rw [hK'1]
      exact (le_bot_iff.mp (hK'1 ▸ oddCoreIn_le_twoPrimeLayerIn K)).symm
    ·
      have hSK : S ≤ K := fun x hx => by
        have : (⟨x, hx⟩ : S) ∈ (twoPrimeLayerIn K).subgroupOf S := h ▸ mem_top _
        exact twoPrimeLayerIn_le K this
      apply hKn
      rw [← normalizer_eq_top_iff, eq_top_iff]
      intro x _
      by_contra hx
      have hSKx : S ≤ K ⊓ rightConjugate K x := le_inf hSK fun s hs =>
        (mem_rightConjugate_iff _ _ _).mpr (hSK (hSn.conj_mem s hs x))
      exact (Nat.not_even_iff_odd.mpr ((hK.2 x hx).of_dvd_nat (card_dvd_of_le hSKx)))
        (even_card_of_isSimpleGroup hc)

end CFSG.ComponentClassification.AS76b
