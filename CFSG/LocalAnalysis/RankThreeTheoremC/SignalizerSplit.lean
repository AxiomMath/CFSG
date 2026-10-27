module

public import CFSG.LocalAnalysis.RankThreeTheoremC.FullCoreCases
public import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionCentre
public import CFSG.LocalAnalysis.AGLEmbedding.Signalizer
import CFSG.LocalAnalysis.RankThreeTheoremC.Signalizers

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def SignalizerCentralNonConstrained (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M D : Subgroup G), ExtremalObstruction p P M D →
    (P : Subgroup G) ≤ normalizer (D : Set G) → ∀ z ∈ (center D).map D.subtype, z ≠ 1 →
      ¬ CFSG.RankThreeCoreUniqueness.Helpers.HasPrimeConstraint (G := centralizer ({z} : Set G)) p →
        ∀ K : Subgroup G, Nat.Coprime p (Nat.card K) →
          (P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)) ≤ normalizer (K : Set G) →
          K ≤ centralizer ({z} : Set G) → K ≤ M

@[expose] def SignalizerNoncentralPart (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M D : Subgroup G), ExtremalObstruction p P M D →
    (P : Subgroup G) ≤ normalizer (D : Set G) → ∀ z ∈ (center D).map D.subtype, z ≠ 1 →
      ∀ K : Subgroup G, Nat.Coprime p (Nat.card K) →
        (P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)) ≤ normalizer (K : Set G) →
        ¬ K ≤ centralizer ({z} : Set G) → K ≤ M

theorem ExtremalObstruction.le_of_le_centralizer_of_hasPrimeConstraint (hS : Setting G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hPD : (P : Subgroup G) ≤ normalizer (D : Set G))
    (hD : ¬ IsMulCommutative D) {z : G} (hzZ : z ∈ (center D).map D.subtype)
    (hcon : CFSG.RankThreeCoreUniqueness.Helpers.HasPrimeConstraint
      (G := centralizer ({z} : Set G)) p)
    {K : Subgroup G} (hK : Nat.Coprime p (Nat.card K)) (hDK : D ≤ normalizer (K : Set G))
    (hKz : K ≤ centralizer ({z} : Set G)) : K ≤ M := by
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hM, hDP, -, -⟩ := hext.obstruction
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  obtain ⟨w, hw, rfl⟩ := hzZ
  have hDC : D ≤ centralizer ({(w : G)} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (mem_center_iff.mp hw ⟨d, hd⟩))
  have hzc := hext.center_le_centralizer hprime hodd hD ⟨w, hw, rfl⟩
  have hPC : (P : Subgroup G) ≤ centralizer ({(w : G)} : Set G) := fun g hg =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hzc g hg)
  have hKO := CFSG.AGLEmbedding.signalizer_le_glbPrimeCore_of_contains hprime hodd hcon
    (P.isPGroup'.to_le hDP) hDC
    (fun y _ hyC hyo => map_subtype_le _ (hext.mem_center_of_mem_centralizer_of_le_normalizer
      hprime hodd hD hPD hyC (by rw [← hyo]; exact pow_orderOf_eq_one y)))
    hKz hK hDK
  obtain ⟨E, hEP, hE, hEc⟩ := pRank_attained p (P : Subgroup G) (by omega)
  rw [hP3] at hEc
  refine hKO.trans (le_of_elemAbelian_normalizes hS hp hM hEP hE hEc
    ((Nat.Prime.coprime_iff_not_dvd hprime).1
      (CFSG.AGLEmbedding.glbPrimeCore_coprime p _))
    ((hEP.trans hPC).trans (CFSG.AGLEmbedding.le_normalizer_glbPrimeCore p _)))

theorem signalizerCase_of_parts (hS : Setting G) (hI : SignalizerCentralNonConstrained G)
    (hII : SignalizerNoncentralPart G) : SignalizerCase G := by
  intro p hp P M D hext hPD K hK hD₁K
  have hprime := sigmaA_prime p hp
  have hodd := sigmaA_odd p hp
  have hD := (hext.exists_normal_plane hS hp hPD).1
  have hDK : D ≤ normalizer (K : Set G) :=
    (le_inf hext.obstruction.2.1 le_sup_left).trans hD₁K
  have hZne : (center D).map D.subtype ≠ ⊥ := by
    intro h
    have hc := hext.card_center_eq hprime hodd hD
    rw [h, card_bot] at hc
    exact hprime.one_lt.ne hc
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  by_cases hKz : K ≤ centralizer ({z} : Set G)
  · by_cases hcon : CFSG.RankThreeCoreUniqueness.Helpers.HasPrimeConstraint
      (G := centralizer ({z} : Set G)) p
    · exact hext.le_of_le_centralizer_of_hasPrimeConstraint hS hp hPD hD hzZ hcon hK hDK hKz
    · exact hI p hp P M D hext hPD z hzZ hz1' hcon K hK hD₁K hKz
  · exact hII p hp P M D hext hPD z hzZ hz1' K hK hD₁K hKz

end CFSG.LocalAnalysis.RankThreeTheoremC
