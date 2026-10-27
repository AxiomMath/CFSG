module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.Omega8Cover
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.Open
open scoped commutatorElement

structure CoverOk {Y : Type*} [Group Y] (C : Subgroup Y) : Prop where
  perfFree : ∀ V : Subgroup Y, V ≤ C → ⁅V, V⁆ = V → ¬ 3 ∣ Nat.card V
  noE9 : ∀ E : Subgroup Y, E ≤ C → IsElemAbelian 3 E → Nat.card E ≠ 9

section Nodes

variable {K Y : Type*} [Group K] [Group Y] {D : UniversalRootDatum K} {π : K →* Y}

theorem exists_order_three_map {i : Fin D.rank} (h3 : HasOrderThree D i)
    (hker : π.ker ≤ Subgroup.center K) :
    ∃ u ∈ (rankOne D.rootGroup i).map π, orderOf u = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx, y, hy, h3', c, hc⟩ := h3
  have hxy : x * y ∈ rankOne D.rootGroup i :=
    mul_mem (le_sup_left (b := D.rootGroup (-Pi.single i 1)) hx)
      (le_sup_right (a := D.rootGroup (Pi.single i 1)) hy)
  have hne1 : π (x * y) ≠ 1 := by
    intro h1
    exact hc (Subgroup.mem_center_iff.1 (hker h1) c).symm
  exact ⟨π (x * y), ⟨x * y, hxy, rfl⟩,
    orderOf_eq_prime (by rw [← map_pow, h3', map_one]) hne1⟩

theorem false_of_node_perfect [Finite Y] {C : Subgroup Y} (hC : CoverOk C) {i : Fin D.rank}
    (h3 : HasOrderThree D i) (hker : π.ker ≤ Subgroup.center K)
    (hperf : ⁅rankOne D.rootGroup i, rankOne D.rootGroup i⁆ = rankOne D.rootGroup i)
    (hle : (rankOne D.rootGroup i).map π ≤ C) : False := by
  obtain ⟨u, hu, hord⟩ := exists_order_three_map h3 hker
  refine hC.perfFree _ hle (map_commutator_self_eq (A := rankOne D.rootGroup i) π hperf) ?_
  have := Subgroup.orderOf_dvd_natCard _ hu
  rwa [hord] at this

theorem false_of_pair_perfect [Finite Y] {C : Subgroup Y} (hC : CoverOk C) {i j : Fin D.rank}
    (h3 : HasOrderThree D i) (hker : π.ker ≤ Subgroup.center K)
    (hperf : ⁅rankOne D.rootGroup i ⊔ rankOne D.rootGroup j,
      rankOne D.rootGroup i ⊔ rankOne D.rootGroup j⁆ = rankOne D.rootGroup i ⊔ rankOne D.rootGroup j)
    (hi : (rankOne D.rootGroup i).map π ≤ C) (hj : (rankOne D.rootGroup j).map π ≤ C) :
    False := by
  obtain ⟨u, hu, hord⟩ := exists_order_three_map h3 hker
  have hV : (rankOne D.rootGroup i ⊔ rankOne D.rootGroup j).map π ≤ C := by
    rw [Subgroup.map_sup]
    exact sup_le hi hj
  refine hC.perfFree _ hV (map_commutator_self_eq π hperf) ?_
  have hu' : u ∈ (rankOne D.rootGroup i ⊔ rankOne D.rootGroup j).map π :=
    Subgroup.map_mono le_sup_left hu
  have := Subgroup.orderOf_dvd_natCard _ hu'
  rwa [hord] at this

theorem false_of_pair_exc [Finite Y] {C : Subgroup Y} (hC : CoverOk C) {i j : Fin D.rank}
    {V : Subgroup K} (hVle : V ≤ rankOne D.rootGroup i ⊔ rankOne D.rootGroup j)
    (hVp : ⁅V, V⁆ = V) (hV3 : 3 ∣ Nat.card (V.map π))
    (hi : (rankOne D.rootGroup i).map π ≤ C) (hj : (rankOne D.rootGroup j).map π ≤ C) :
    False := by
  have hV : V.map π ≤ C := by
    have := Subgroup.map_mono (f := π) hVle
    rw [Subgroup.map_sup] at this
    exact this.trans (sup_le hi hj)
  exact hC.perfFree _ hV (map_commutator_self_eq π hVp) hV3

end Nodes

section Orth

variable {G : Type} [Group G] [Finite G]

theorem exists_elemAbelian_card_nine {L₁ L₂ : Subgroup G} (h₁ : Nat.card L₁ = 6)
    (hnc₁ : ∃ a ∈ L₁, ∃ b ∈ L₁, a * b ≠ b * a) (h12 : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    {c₁ c₂ : G} (hc₁ : c₁ ∈ L₁) (hc₂ : c₂ ∈ L₂) (h1 : c₁ ≠ 1) (h2 : c₂ ≠ 1)
    (h1' : c₁ ^ 3 = 1) (h2' : c₂ ^ 3 = 1) :
    ∃ E : Subgroup G, E ≤ L₁ ⊔ L₂ ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz : ∀ c : G, c ≠ 1 → c ^ 3 = 1 → Nat.card (Subgroup.zpowers c) = 3 := fun c hc hc3 => by
    rw [Nat.card_zpowers, orderOf_eq_prime hc3 hc]
  have hZ₁ : Subgroup.zpowers c₁ ≤ L₁ := (Subgroup.zpowers_le).mpr hc₁
  have hZ₂ : Subgroup.zpowers c₂ ≤ L₂ := (Subgroup.zpowers_le).mpr hc₂
  have c12 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (Lie.le_normalizer_of_commute (A := Subgroup.zpowers c₁) (B := Subgroup.zpowers c₂)
      fun a ha b hb => h12 a (hZ₁ ha) b (hZ₂ hb))
  have hi12 : Subgroup.zpowers c₁ ⊓ Subgroup.zpowers c₂ = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf hZ₁ hZ₂).trans (Lie.inf_eq_bot_of_commutes_of_card_six h₁ hnc₁ h12).le)
  rw [hi12, Subgroup.card_bot, mul_one, hz _ h1 h1', hz _ h2 h2'] at c12
  refine ⟨Subgroup.zpowers c₁ ⊔ Subgroup.zpowers c₂, sup_le_sup hZ₁ hZ₂, ?_, by rw [c12]⟩
  have hcl : Subgroup.zpowers c₁ ⊔ Subgroup.zpowers c₂ = Subgroup.closure {c₁, c₂} := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union,
      Set.singleton_union]
  rw [hcl]
  refine CFSG.AGLEmbedding.isElemAbelian_three_closure_of_pairwise ?_ ?_
  · have k12 : Commute c₁ c₂ := h12 _ hc₁ _ hc₂
    intro a ha b hb _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      first
      | exact Commute.refl _
      | assumption
      | exact Commute.symm (by assumption)
  · intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl <;> assumption

end Orth

section Three

variable {K Y : Type} [Group K] [Finite K] [Group Y] [Finite Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem exists_order_three_rankOne {i : Fin D.rank} (h3 : HasOrderThree D i) :
    ∃ c ∈ rankOne D.rootGroup i, c ≠ 1 ∧ c ^ 3 = 1 := by
  obtain ⟨x, hx, y, hy, h3', c, hc⟩ := h3
  have hxy : x * y ∈ rankOne D.rootGroup i :=
    mul_mem (le_sup_left (b := D.rootGroup (-Pi.single i 1)) hx)
      (le_sup_right (a := D.rootGroup (Pi.single i 1)) hy)
  refine ⟨x * y, hxy, fun h1 => hc ?_, h3'⟩
  rw [h1, one_mul, mul_one]

theorem false_of_pair_same
    (h : BorelQuotient D n H π M) {exc : Fin D.rank → Fin D.rank → Prop} (hL : TwoLevi D exc)
    (h3 : ∀ i, HasOrderThree D i)
    (hS3 : ∀ i, Nat.card (rankOne D.rootGroup i) = 6 ∧
      ∃ a ∈ rankOne D.rootGroup i, ∃ b ∈ rankOne D.rootGroup i, a * b ≠ b * a)
    (hexc : ∀ i j, exc i j → ∃ V : Subgroup K,
      V ≤ rankOne D.rootGroup i ⊔ rankOne D.rootGroup j ∧ ⁅V, V⁆ = V ∧
        3 ∣ Nat.card (V.map π))
    (hinj : Function.Injective π) {C : Subgroup Y} (hC : CoverOk C) {a b : Fin D.rank}
    (hab : a ≠ b) (ha : (rankOne D.rootGroup a).map π ≤ C)
    (hb : (rankOne D.rootGroup b).map π ≤ C) : False := by
  have hker : π.ker ≤ Subgroup.center K := fun z hz => h.ker_central z hz
  by_cases hA : D.cartan a b = 0
  · have hc := commutes_rankOne_of_cartan_eq_zero h.extras hab hA
    obtain ⟨c₁, hc₁, h1, h1'⟩ := exists_order_three_rankOne (h3 a)
    obtain ⟨c₂, hc₂, h2, h2'⟩ := exists_order_three_rankOne (h3 b)
    obtain ⟨E, hE, hEel, hE9⟩ := exists_elemAbelian_card_nine (hS3 a).1 (hS3 a).2 hc hc₁ hc₂ h1 h2
      h1' h2'
    have hEC : E.map π ≤ C := by
      have := Subgroup.map_mono (f := π) hE
      rw [Subgroup.map_sup] at this
      exact this.trans (sup_le ha hb)
    refine hC.noE9 _ hEC
      (CFSG.RankThreeCoreUniqueness.Helpers.elementary_map_injective 3 E π hinj hEel) ?_
    rw [Subgroup.card_map_of_injective hinj, hE9]
  · have hna : ⁅rankOne D.rootGroup a, rankOne D.rootGroup a⁆ ≠ rankOne D.rootGroup a :=
      Lie.commutator_ne_self_of_card_six (hS3 a).1
    have hnb : ⁅rankOne D.rootGroup b, rankOne D.rootGroup b⁆ ≠ rankOne D.rootGroup b :=
      Lie.commutator_ne_self_of_card_six (hS3 b).1
    rcases hL.pair a b hab hA hna hnb with hperf | hexcab
    · exact false_of_pair_perfect hC (h3 a) hker hperf ha hb
    · obtain ⟨V, hVle, hVp, hV3⟩ := hexc a b hexcab
      exact false_of_pair_exc hC hVle hVp hV3 ha hb

theorem false_of_three_nodes
    (h : BorelQuotient D n H π M) {exc : Fin D.rank → Fin D.rank → Prop} (hL : TwoLevi D exc)
    (h3 : ∀ i, HasOrderThree D i)
    (hS3 : ∀ i, Nat.card (rankOne D.rootGroup i) = 6 ∧
      ∃ a ∈ rankOne D.rootGroup i, ∃ b ∈ rankOne D.rootGroup i, a * b ≠ b * a)
    (hexc : ∀ i j, exc i j → ∃ V : Subgroup K,
      V ≤ rankOne D.rootGroup i ⊔ rankOne D.rootGroup j ∧ ⁅V, V⁆ = V ∧
        3 ∣ Nat.card (V.map π))
    (hinj : Function.Injective π) {C₁ C₂ : Subgroup Y} (h₁ : CoverOk C₁) (h₂ : CoverOk C₂)
    (hcov : ∀ i, (rankOne D.rootGroup i).map π ≤ C₁ ∨ (rankOne D.rootGroup i).map π ≤ C₂)
    {i j l : Fin D.rank} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) : False := by
  have p₁ := fun {a b : Fin D.rank} (hab : a ≠ b) (ha : (rankOne D.rootGroup a).map π ≤ C₁)
    (hb : (rankOne D.rootGroup b).map π ≤ C₁) => false_of_pair_same h hL h3 hS3 hexc hinj h₁ hab ha hb
  have p₂ := fun {a b : Fin D.rank} (hab : a ≠ b) (ha : (rankOne D.rootGroup a).map π ≤ C₂)
    (hb : (rankOne D.rootGroup b).map π ≤ C₂) => false_of_pair_same h hL h3 hS3 hexc hinj h₂ hab ha hb
  rcases hcov i with hi | hi <;> rcases hcov j with hj | hj <;> rcases hcov l with hl | hl
  · exact p₁ hij hi hj
  · exact p₁ hij hi hj
  · exact p₁ hil hi hl
  · exact p₂ hjl hj hl
  · exact p₁ hjl hj hl
  · exact p₂ hil hi hl
  · exact p₂ hij hi hj
  · exact p₂ hij hi hj

end Three

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
