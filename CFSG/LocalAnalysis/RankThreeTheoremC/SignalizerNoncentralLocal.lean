module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerMinimalIrreducible
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeRankTwo

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem signalizer_le_of_plane_centralizers {p : ℕ} (hp : p.Prime) {U K M' : Subgroup G}
    (hU : IsElemAbelian p U) (hUc : Nat.card U = p ^ 2) (hK : Nat.Coprime p (Nat.card K))
    (hUK : U ≤ normalizer (K : Set G))
    (h : ∀ a ∈ U, a ≠ 1 → K ⊓ centralizer ({a} : Set G) ≤ M') : K ≤ M' := by
  have hrank : 2 ≤ CFSG.Open.pRank p U := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hU hUc
  obtain ⟨e, he, heU⟩ := rank_two_has_coordinate_embedding p hp U hrank
  refine embedded_rank_two_signalizer_le_of_line_centralizers p hp e K M' (heU.trans hUK) hK ?_
  intro v hv
  set w := e (Multiplicative.ofAdd v) with hw
  have hwmem : w ∈ (e.comp (coordinatePairLineHom v)).range := by
    refine ⟨Multiplicative.ofAdd 1, ?_⟩
    rw [MonoidHom.comp_apply, hw]
    congr 1
    change Multiplicative.ofAdd ((1 : ZMod p) • v) = Multiplicative.ofAdd v
    rw [one_smul]
  have hwU : w ∈ U := heU ⟨_, rfl⟩
  have hw1 : w ≠ 1 := by
    intro h1
    have h' : Multiplicative.ofAdd v = 1 := he (by rw [map_one]; exact h1)
    exact hv (by simpa using congrArg Multiplicative.toAdd h')
  have hCw : centralizer ((e.comp (coordinatePairLineHom v)).range : Set G) ≤
      centralizer ({w} : Set G) := centralizer_le (Set.singleton_subset_iff.mpr hwmem)
  exact (inf_le_inf_left K hCw).trans (h w hwU hw1)

@[expose] def SignalizerNoncentralLocal (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M D : Subgroup G), ExtremalObstruction p P M D →
    (P : Subgroup G) ≤ normalizer (D : Set G) → ∀ z ∈ (center D).map D.subtype, z ≠ 1 →
      ∀ K : Subgroup G, Nat.Coprime p (Nat.card K) →
        (P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)) ≤ normalizer (K : Set G) →
        ¬ K ≤ centralizer ({z} : Set G) →
        ∀ q : ℕ, q.Prime → q ≠ p → IsPGroup q K →
        (∀ K' : Subgroup G, K' < K →
          (P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)) ≤ normalizer (K' : Set G) → K' ≤ M) →
        ⁅K, (P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G))⁆ = K →
        (frattini K).map K.subtype < K →
        (∀ K' : Subgroup G, K' < K →
          (P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)) ≤ normalizer (K' : Set G) →
          K' ≤ (frattini K).map K.subtype) →
        (∀ a ∈ (P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)),
          (∀ k ∈ K, (a * k * a⁻¹)⁻¹ * k ∈ (frattini K).map K.subtype) → a = 1) →
        ¬ (P : Subgroup G) ≤ normalizer (K : Set G) →
        ∀ U : Subgroup G, U < D → (P : Subgroup G) ≤ normalizer (U : Set G) →
          IsElemAbelian p U → Nat.card U = p ^ 2 →
          3 ≤ CFSG.Open.pRank p ((P : Subgroup G) ⊓ centralizer (U : Set G)) →
          normalizer (U : Set G) ≤ M →
          ∀ u ∈ U, u ≠ 1 → u ∉ (center D).map D.subtype → ¬ centralizer ({u} : Set G) ≤ M →
            K ⊓ centralizer ({u} : Set G) ≤ M

theorem signalizerNoncentralIrreducible_of_local (hS : Setting G)
    (h : SignalizerNoncentralLocal G) : SignalizerNoncentralIrreducible G := by
  intro p hp P M D hext hPD z hzZ hz1 K hK hAK hKz q hq hqp hqK hproper hcomm hΦ hfr hfaith hPK
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hDna, U, hUD, hPU, hUe, hUc, hU3, hNU⟩ := hext.exists_normal_plane hS hp hPD
  have hDP := hext.obstruction.2.1
  have hZc := hext.card_center_eq hprime hodd hDna
  refine signalizer_le_of_plane_centralizers hprime hUe hUc hK ?_ ?_
  ·
    exact (hUD.le.trans (le_inf hDP le_sup_left)).trans hAK
  · intro a haU ha1
    by_cases haZ : a ∈ (center D).map D.subtype
    ·
      have hap : a ^ p = 1 :=
        (hext.pow_eq_one_and_commutator_mem hprime hodd).1 a (map_subtype_le _ haZ)
      have hzy : zpowers a = (center D).map D.subtype := by
        refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr haZ) ?_
        rw [hZc, Nat.card_zpowers, orderOf_eq_prime hap ha1]
      have hAa : (P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)) ≤
          centralizer ({a} : Set G) := by
        obtain ⟨w, hw, rfl⟩ := haZ
        intro x hx
        have hD' : D ≤ centralizer ({(w : G)} : Set G) := fun d hd =>
          mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (mem_center_iff.mp hw ⟨d, hd⟩))
        have hC' : centralizer (D : Set G) ≤ centralizer ({(w : G)} : Set G) :=
          centralizer_le (Set.singleton_subset_iff.mpr (map_subtype_le _ ⟨w, hw, rfl⟩))
        exact (sup_le hD' hC') hx.2
      have hlt : K ⊓ centralizer ({a} : Set G) < K := by
        refine lt_of_le_of_ne inf_le_left fun heq => hKz ?_
        have hKa : K ≤ centralizer ({a} : Set G) := inf_eq_left.mp heq
        have haC : a ∈ centralizer (K : Set G) := mem_centralizer_iff.mpr fun k hk =>
          mem_centralizer_singleton_iff.mp (hKa hk)
        have hzC : z ∈ centralizer (K : Set G) := (zpowers_le.mpr haC) (hzy ▸ hzZ)
        intro k hk
        exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hzC k hk)
      exact hproper _ hlt (le_inf hAK (hAa.trans le_normalizer) |>.trans
        inf_normalizer_le_normalizer_inf)
    · by_cases hC : centralizer ({a} : Set G) ≤ M
      · exact inf_le_right.trans hC
      · exact h p hp P M D hext hPD z hzZ hz1 K hK hAK hKz q hq hqp hqK hproper hcomm hΦ hfr hfaith
          hPK U hUD hPU hUe hUc hU3 hNU a haU ha1 haZ hC

end CFSG.LocalAnalysis.RankThreeTheoremC
