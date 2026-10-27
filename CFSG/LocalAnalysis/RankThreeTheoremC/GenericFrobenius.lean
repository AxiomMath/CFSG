module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericAbelian
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.LayerNormal
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem rankThreeFrobeniusProduct_of_fixedPointFree {W K V : Subgroup G} (hKW : K ≤ W)
    (hKne : K ≠ ⊥) (hVne : V ≠ ⊥) (hVK : V ≤ normalizer (K : Set G)) (hKV : K ⊓ V = ⊥)
    (hfpf : ∀ v ∈ V, v ≠ 1 → ∀ k ∈ K, k * v = v * k → k = 1) (hWKV : W ≤ K ⊔ V) :
    rankThreeFrobeniusProduct W K V := by
  have hprod : ∀ y, y ∈ K ⊔ V ↔ ∃ a ∈ K, ∃ b ∈ V, y = a * b := by
    intro y
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left K V hVK, Set.mem_mul]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩
  refine ⟨K ⊔ V, fun y => ?_, hprod, hKne, hVne, le_sup_left, ?_, hKV, hfpf⟩
  · rw [hprod]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, hKW ha, b, hb, rfl⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      obtain ⟨a', ha', b', hb', rfl⟩ := (hprod a).1 (hWKV ha)
      exact ⟨a', ha', b' * b, V.mul_mem hb' hb, by rw [mul_assoc]⟩
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    exact sup_le Subgroup.le_normalizer hVK

omit [Finite G] in
theorem normal_subgroupOf_pCoreOf_two (M : Subgroup G) : ((pCoreOf 2 M).subgroupOf M).Normal := by
  have : (CFSG.Open.pCore 2 M).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  unfold pCoreOf
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  exact this

theorem pCoreOf_two_le_rankThreePrimeCore {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (M : Subgroup G) : pCoreOf 2 M ≤ rankThreePrimeCore p M := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
  exact le_sSup ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 M, normal_subgroupOf_pCoreOf_two M, by
    rw [hn]; exact ((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_right n⟩

theorem pCoreOf_two_ne_bot {M : Subgroup G} (hM : IsTwoLocal M) : pCoreOf 2 M ≠ ⊥ := by
  obtain ⟨Q, hQne, hQ, rfl⟩ := hM
  exact fun h => hQne (le_bot_iff.mp (h ▸ CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 Q hQ))

theorem rankThreeFrobeniusProduct_of_generic (hS : Setting G) (hD1 : TheoremD1 G)
    (hU0 : FullCoreLocal G) {p : ℕ} [Fact p.Prime] (hp : p ∈ rankThreeSigmaA G)
    {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M) {x : G}
    (hx : IsGenericPoint p P M x) {m : ℕ} (hm : 2 ≤ m)
    (e : rankThreeLayer (centralizer ({x} : Set G)) ≃* PSL(2, GaloisField p m))
    (hfpf : ∀ v ∈ centralizer ((rankThreeLayer (centralizer ({x} : Set G)) : Subgroup G) :
      Set G), v ≠ 1 → ∀ k ∈ pCoreOf 2 M, k * v = v * k → k = 1)
    (hpc : rankThreePrimeCore p M ≤ pCoreOf 2 M ⊔
      centralizer ((rankThreeLayer (centralizer ({x} : Set G)) : Subgroup G) : Set G)) :
    rankThreeFrobeniusProduct (rankThreePrimeCore p M) (pCoreOf 2 M)
      (centralizer ((rankThreeLayer (centralizer ({x} : Set G)) : Subgroup G) : Set G)) := by
  obtain ⟨-, hVM, hKV, -, -⟩ := generic_layer_facts hS hD1 hU0 hp hM hx hm e
  obtain ⟨-, ⟨-, hx1, -, -, -⟩, -, -⟩ := id hx
  have hxV : x ∈ centralizer ((rankThreeLayer (centralizer ({x} : Set G)) : Subgroup G) :
      Set G) := mem_centralizer_iff.mpr fun l hl =>
    mem_centralizer_singleton_iff.mp (rankThreeLayer_le _ hl)
  exact rankThreeFrobeniusProduct_of_fixedPointFree
    (pCoreOf_two_le_rankThreePrimeCore (Fact.out) (sigmaA_odd p hp) M)
    (pCoreOf_two_ne_bot hM.1.1)
    (fun h => hx1 (by have h' : x ∈ (⊥ : Subgroup G) := h ▸ hxV; simpa using h'))
    (hVM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)) hKV hfpf hpc

@[expose] def GL83GenericStructureMin (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M : Subgroup G), IsCoreMaxLocal p P M →
    ¬ rankThreeGamma 1 p (P : Subgroup G) ≤ M → LargerPrimesUnique G p →
      ∀ x : G, IsGenericPoint p P M x →
        (∀ y : G, IsGenericPoint p P M y → zpowers y = zpowers x) ∧ Group.IsSolvable M ∧
          (∀ v ∈ centralizer ((rankThreeLayer (centralizer ({x} : Set G)) : Subgroup G) :
            Set G), v ≠ 1 → ∀ k ∈ pCoreOf 2 M, k * v = v * k → k = 1) ∧
          rankThreePrimeCore p M ≤ pCoreOf 2 M ⊔
            centralizer ((rankThreeLayer (centralizer ({x} : Set G)) : Subgroup G) : Set G)

theorem gl83GenericStructureCore_of_min (hS : Setting G) (hD1 : TheoremD1 G)
    (hU0 : FullCoreLocal G) (hL : GL83GenericLayer G) (h : GL83GenericStructureMin G) :
    GL83GenericStructureCore G := by
  intro p hp P M hM hfail hIH x hgen
  have hfact : Fact p.Prime := ⟨sigmaA_prime p hp⟩
  obtain ⟨hU, hsol, hfpf, hpc⟩ := h p hp P M hM hfail hIH x hgen
  obtain ⟨-, hf, m, hm2, ⟨e⟩⟩ := hL p hp P M hM hfail hIH x hgen
  exact ⟨hU, hsol, rankThreeFrobeniusProduct_of_generic hS hD1 hU0 hp hM hgen hm2 e hfpf hpc⟩

theorem gl83GenericStructure_of_min (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hL : GL83GenericLayer G) (h : GL83GenericStructureMin G) : GL83GenericStructure G :=
  gl83GenericStructure_of_core hS hL (gl83GenericStructureCore_of_min hS hD1 hU0 hL h)

end CFSG.LocalAnalysis.RankThreeTheoremC
