module

public import CFSG.ClassicalInvolution.LBalance.Proof.Tools
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerTwoLayerOrbitLocation
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCorollaryC
public import CFSG.LocalAnalysis.ComponentClassification.GSLitTripleBranch

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.GSLit

theorem uOutcome_of_mulEquiv_alternating {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {n : ℕ} (hodd : Odd n) (h7 : 7 ≤ n) (h3 : n % 4 = 3) (e : X ≃* alternatingGroup (Fin n)) :
    OutcomeLocal.UOutcome X :=
  Or.inr (Or.inl ⟨n, hodd, h7, ⟨generalizedFittingEquivOfSimple.trans e⟩, fun h => by omega⟩)

theorem false_of_corollaryC (hCorC : GSThmB.CorollaryCStatement)
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {a : X} {J E : Subgroup X} (ha : orderOf a = 2)
    (hJa : J ≤ centralizer ({a} : Set X))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set X))))
    (h7 : Nonempty (J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 7)))
    (hE : E ≤ centralizer ({a} : Set X) ⊓ normalizer (J : Set X))
    (hE4 : Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
    (hcomm : ⁅J, centralizer ({a} : Set X) ⊓ ⨅ (e : X) (_ : e ∈ E) (_ : e ≠ 1),
        (pPrimeCore 2 (centralizer ({e} : Set X))).map (centralizer ({e} : Set X)).subtype⁆ =
      J) : False := by
  obtain ⟨n, hodd, h11, ⟨e⟩⟩ := hCorC X hnonab hK hz hU a J ha hJa hJ h7 E hE hE4 hcomm
  have h3 := GSLit.mod_four_eq_three_of_mulEquiv_alternating hnonab (by omega) e hz
  exact hU (uOutcome_of_mulEquiv_alternating hodd (by omega) h3 e)

theorem commutator_le_oddCore_of_alternating_seven (hCorC : GSThmB.CorollaryCStatement)
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {a : X} {J E : Subgroup X} (ha : orderOf a = 2)
    (hJa : J ≤ centralizer ({a} : Set X))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set X))))
    (h7 : Nonempty (J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 7)))
    (hE : E ≤ centralizer ({a} : Set X) ⊓ normalizer (J : Set X))
    (hE4 : Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))
    (hΔ : centralizer ({a} : Set X) ⊓ ⨅ (e : X) (_ : e ∈ E) (_ : e ≠ 1),
        (pPrimeCore 2 (centralizer ({e} : Set X))).map (centralizer ({e} : Set X)).subtype ≤
      normalizer (J : Set X)) :
    ⁅J, centralizer ({a} : Set X) ⊓ ⨅ (e : X) (_ : e ∈ E) (_ : e ≠ 1),
        (pPrimeCore 2 (centralizer ({e} : Set X))).map (centralizer ({e} : Set X)).subtype⁆ ≤
      (pPrimeCore 2 J).map J.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Δ := centralizer ({a} : Set X) ⊓ ⨅ (e : X) (_ : e ∈ E) (_ : e ≠ 1),
    (pPrimeCore 2 (centralizer ({e} : Set X))).map (centralizer ({e} : Set X)).subtype with hΔdef
  set N := ⁅J, Δ⁆ with hNdef
  have hNJ : N ≤ J := le_normalizer_iff_commutator_le_left.mp hΔ
  have hJN : J ≤ normalizer (N : Set X) := normalizer_commutator_ge_left J Δ
  have hNn : (N.subgroupOf J).Normal := (normal_subgroupOf_iff_le_normalizer hNJ).mpr hJN
  obtain ⟨e7⟩ := h7
  have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 7))
  have hs : IsSimpleGroup (J ⧸ pPrimeCore 2 J) := e7.isSimpleGroup
  let π := QuotientGroup.mk' (pPrimeCore 2 J)
  have himgn : ((N.subgroupOf J).map π).Normal := Subgroup.Normal.map hNn π
    (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf J).map π) with hbot | htop
  ·
    have hle : N.subgroupOf J ≤ pPrimeCore 2 J := by
      intro n hn
      have h1 : π n ∈ (N.subgroupOf J).map π := mem_map_of_mem π hn
      rw [hbot, mem_bot] at h1
      exact (QuotientGroup.eq_one_iff n).mp h1
    intro y hy
    exact ⟨⟨y, hNJ hy⟩, hle hy, rfl⟩
  ·
    refine (false_of_corollaryC hCorC hnonab hK hz hU ha hJa hJ ⟨e7⟩ hE hE4 ?_).elim
    have hCperf := ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hJ
    have hJperf : Group.IsPerfect (⊤ : Subgroup J) :=
      Group.IsPerfect.ofSurjective
        (f := ((subgroupOfEquivOfLe hJa).trans Subgroup.topEquiv.symm).toMonoidHom)
        ((subgroupOfEquivOfLe hJa).trans Subgroup.topEquiv.symm).surjective
    have hsup : (⊤ : Subgroup J) ≤ N.subgroupOf J ⊔ pPrimeCore 2 J := by
      have h1 := Subgroup.comap_map_eq π (N.subgroupOf J)
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at h1
      rw [h1]
    have hodd : Odd (Nat.card (pPrimeCore 2 J)) := by
      rw [← GSLit.oddCore_eq_pPrimeCore_two]
      exact UnbalancedCatalog.EvenCatalog.odd_card_oddCore
    have hRN : pPrimeCore 2 J ≤ normalizer ((N.subgroupOf J : Subgroup J) : Set J) := by
      rw [normalizer_eq_top_iff.mpr hNn]
      exact le_top
    have htopN := UnbalancedLayer.le_of_perfect_le_sup_of_odd hodd hRN hJperf hsup
    apply le_antisymm hNJ
    intro j hj
    exact htopN (mem_top (⟨j, hj⟩ : J))

end CFSG.ComponentClassification.GrSLit
