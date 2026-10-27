module

public import CFSG.LocalAnalysis.SectionRank.Monster

public section

namespace CFSG.QuasithinUnique.SQTK.Coxeter

open CFSG.Open CFSG.SectionRank
open scoped commutatorElement

section Graph

abbrev edgeGraph {n : ℕ} (edges : List (Fin n × Fin n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j => (i, j) ∈ edges

theorem edgeGraph_adj_iff {n : ℕ} {edges : List (Fin n × Fin n)} {i j : Fin n} :
    (edgeGraph edges).Adj i j ↔ i ≠ j ∧ ((i, j) ∈ edges ∨ (j, i) ∈ edges) := Iff.rfl

theorem edgeGraph_cliqueFree_three {n : ℕ} {edges : List (Fin n × Fin n)}
    (h : ∀ e ∈ edges, ∀ c : Fin n,
      ¬ ((edgeGraph edges).Adj e.1 c ∧ (edgeGraph edges).Adj e.2 c)) :
    (edgeGraph edges).CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨a, b, c, -, -, -, rfl⟩ := Finset.card_eq_three.1 ht.card_eq
  obtain ⟨hab, hac, hbc⟩ := SimpleGraph.is3Clique_triple_iff.1 ht
  rcases (edgeGraph_adj_iff.1 hab).2 with h1 | h1
  · exact h (a, b) h1 c ⟨hac, hbc⟩
  · exact h (b, a) h1 c ⟨hbc, hac⟩

@[expose] def reachedBy {V : Type*} [DecidableEq V] (root : V) (l : List (V × V)) : List V :=
  l.foldl (fun S e => if e.1 ∈ S then e.2 :: S else S) [root]

theorem reachable_of_mem_foldl {V : Type*} [DecidableEq V] (Γ : SimpleGraph V) (root : V)
    (l : List (V × V)) (hl : ∀ e ∈ l, Γ.Adj e.1 e.2) (S : List V)
    (hS : ∀ w ∈ S, Γ.Reachable root w) :
    ∀ w ∈ l.foldl (fun S e => if e.1 ∈ S then e.2 :: S else S) S, Γ.Reachable root w := by
  induction l generalizing S with
  | nil => exact hS
  | cons e l ih =>
    rw [List.foldl_cons]
    refine ih (fun e' he' => hl e' (List.mem_cons_of_mem _ he')) _ fun w hw => ?_
    by_cases he : e.1 ∈ S
    · rw [ite_eq_left he] at hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact (hS e.1 he).trans (hl e List.mem_cons_self).reachable
      · exact hS w hw
    · rw [ite_eq_right he] at hw
      exact hS w hw

theorem connected_of_reachedBy {V : Type*} [DecidableEq V] (Γ : SimpleGraph V) (root : V)
    (l : List (V × V)) (hl : ∀ e ∈ l, Γ.Adj e.1 e.2) (h : ∀ w, w ∈ reachedBy root l) :
    Γ.Connected := by
  have hr : ∀ w, Γ.Reachable root w := fun w =>
    reachable_of_mem_foldl Γ root l hl [root] (by simp) w (h w)
  exact (SimpleGraph.connected_iff Γ).2 ⟨fun u w => (hr u).symm.trans (hr w), ⟨root⟩⟩

theorem edgeGraph_connected {n : ℕ} {edges : List (Fin n × Fin n)} (root : Fin n)
    (hne : ∀ e ∈ edges, e.1 ≠ e.2) (h : ∀ w, w ∈ reachedBy root edges) :
    (edgeGraph edges).Connected :=
  connected_of_reachedBy _ root edges (fun e he => ⟨hne e he, Or.inl (by simpa using he)⟩) h

end Graph

section Relations

theorem coxeter_relations_of_matrix {n : ℕ} (edges : List (Fin n × Fin n))
    (M : CoxeterMatrix (Fin n))
    (hM : ∀ i j, M i j = if i = j then 1 else if (i, j) ∈ edges ∨ (j, i) ∈ edges then 3 else 2)
    {Y : Type*} [Group Y] (s : Fin n → Y) (hrel : ∀ i j, (s i * s j) ^ M i j = 1) :
    (∀ i, s i ^ 2 = 1) ∧ (∀ i j, (edgeGraph edges).Adj i j → (s i * s j) ^ 3 = 1) ∧
      ∀ i j, i ≠ j → ¬ (edgeGraph edges).Adj i j → Commute (s i) (s j) := by
  have hsq : ∀ i, s i ^ 2 = 1 := fun i => by
    have h := hrel i i
    rw [hM i i, ite_eq_left (rfl : i = i), pow_one] at h
    rw [sq]
    exact h
  refine ⟨hsq, fun i j hij => ?_, fun i j hne hnadj => ?_⟩
  · obtain ⟨hne, he⟩ := hij
    have h := hrel i j
    rwa [hM i j, ite_eq_right hne, ite_eq_left he] at h
  · have h := hrel i j
    have hn : ¬ ((i, j) ∈ edges ∨ (j, i) ∈ edges) := fun he => hnadj ⟨hne, he⟩
    rw [hM i j, ite_eq_right hne, ite_eq_right hn] at h
    exact commute_of_sq_mul_eq_one (hsq i) (hsq j) h

theorem presentedGroup_coxeter_pow_eq_one {n : ℕ} (M : CoxeterMatrix (Fin n))
    (extra : Set (FreeGroup (Fin n))) (i j : Fin n) :
    (PresentedGroup.of i * PresentedGroup.of j : PresentedGroup (M.relationsSet ∪ extra)) ^
      M i j = 1 := by
  have hmem : M.relation i j ∈ Subgroup.normalClosure (M.relationsSet ∪ extra) :=
    Subgroup.subset_normalClosure (Or.inl ⟨(i, j), rfl⟩)
  have key := PresentedGroup.mk_eq_one_iff.mpr hmem
  rw [CoxeterMatrix.relation, map_pow, map_mul] at key
  exact key

end Relations

section Rank

theorem exists_isElemAbelian_three_of_separated_edges {V : Type*} (Γ : SimpleGraph V)
    (hconn : Γ.Connected) (htri : Γ.CliqueFree 3) {Y : Type*} [Group Y] (s : V → Y)
    (hgen : Subgroup.closure (Set.range s) = ⊤) (hs : ∀ v, s v ^ 2 = 1)
    (hedge : ∀ u v, Γ.Adj u v → (s u * s v) ^ 3 = 1)
    (hnon : ∀ u v, u ≠ v → ¬ Γ.Adj u v → Commute (s u) (s v)) (hY : commutator Y ≠ ⊥)
    {r : ℕ} (a b : Fin r → V) (hab : ∀ i, Γ.Adj (a i) (b i))
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ [a i, b i], ∀ y ∈ [a j, b j], ¬ Γ.Adj x y) :
    ∃ E : Subgroup Y, E ≤ commutator Y ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ r := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : ∀ x y : V, ¬ Γ.Adj x y → Commute (s x) (s y) := fun x y h => by
    by_cases hxy : x = y
    · subst hxy
      exact Commute.refl _
    · exact hnon x y hxy h
  exact exists_isElemAbelian_of_dihedral (p := 3) (by norm_num) (fun i => s (a i))
    (fun i => s (b i)) (fun i => hs _) (fun i => hs _)
    (fun i => orderOf_mul_eq_three_of_adj Γ hconn htri s hgen hs hedge hnon hY (hab i))
    (fun i j hij => hc _ _ (hsep i j hij (a i) (by simp) (a j) (by simp)))
    (fun i j hij => hc _ _ (hsep i j hij (a i) (by simp) (b j) (by simp)))
    (fun i j hij => hc _ _ (hsep i j hij (b i) (by simp) (b j) (by simp)))

theorem exists_isElemAbelian_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) {p k : ℕ}
    (h : ∃ E : Subgroup H, IsElemAbelian p E ∧ Nat.card E = p ^ k) :
    ∃ E : Subgroup G, IsElemAbelian p E ∧ Nat.card E = p ^ k := by
  obtain ⟨E, hE, hcard⟩ := h
  refine ⟨E.map e.symm.toMonoidHom, isElemAbelian_map hE e.symm.toMonoidHom, ?_⟩
  rw [Subgroup.card_map_of_injective e.symm.injective, hcard]

theorem exists_isElemAbelian_subgroup_of_le {Y : Type*} [Group Y] {K E : Subgroup Y} (hEK : E ≤ K)
    {p k : ℕ} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ k) :
    ∃ F : Subgroup K, IsElemAbelian p F ∧ Nat.card F = p ^ k := by
  refine ⟨E.subgroupOf K, ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · have hcomm := hE.1
    have h := congrArg Subtype.val (mul_comm' (⟨((x : K) : Y), x.2⟩ : E) ⟨((y : K) : Y), y.2⟩)
    apply Subtype.ext
    apply Subtype.ext
    simpa using h
  · apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hE.2 (x : Y) hx
  · rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv

theorem commutator_ne_bot_of_mulEquiv {G Y : Type*} [Group G] [Group Y] {K : Subgroup Y}
    (e : G ≃* K) (hG : ∃ g h : G, g * h ≠ h * g) : commutator Y ≠ ⊥ := by
  intro h
  obtain ⟨g, g', hgg⟩ := hG
  apply hgg
  apply e.injective
  have hc : ⁅(e g : Y), (e g' : Y)⁆ ∈ commutator Y :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  apply Subtype.ext
  rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
  exact hc

theorem exists_isElemAbelian_three_of_coxeterRelations {n : ℕ} (edges : List (Fin n × Fin n))
    (M : CoxeterMatrix (Fin n))
    (hM : ∀ i j, M i j = if i = j then 1 else if (i, j) ∈ edges ∨ (j, i) ∈ edges then 3 else 2)
    (hconn : (edgeGraph edges).Connected) (htri : (edgeGraph edges).CliqueFree 3)
    {Y : Type*} [Group Y] (s : Fin n → Y) (hgen : Subgroup.closure (Set.range s) = ⊤)
    (hrel : ∀ i j, (s i * s j) ^ M i j = 1) {K : Subgroup Y} (hK : commutator Y ≤ K)
    {G : Type*} [Group G] (e : G ≃* K) (hG : ∃ g h : G, g * h ≠ h * g) {r r' : ℕ} (hr : r' ≤ r)
    (a b : Fin r → Fin n) (hab : ∀ i, (edgeGraph edges).Adj (a i) (b i))
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ [a i, b i], ∀ y ∈ [a j, b j], ¬ (edgeGraph edges).Adj x y) :
    ∃ E : Subgroup G, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ r' := by
  obtain ⟨hs, hedge, hnon⟩ := coxeter_relations_of_matrix edges M hM s hrel
  obtain ⟨E, hEc, hE, hcard⟩ := exists_isElemAbelian_three_of_separated_edges (edgeGraph edges)
    hconn htri s hgen hs hedge hnon (commutator_ne_bot_of_mulEquiv e hG)
    (fun i : Fin r' => a (Fin.castLE hr i)) (fun i => b (Fin.castLE hr i)) (fun i => hab _)
    (fun i j hij => hsep _ _ (fun h => hij (Fin.castLE_injective hr h)))
  obtain ⟨F, hF, hFcard⟩ := exists_isElemAbelian_subgroup_of_le (hEc.trans hK) hE hcard
  exact exists_isElemAbelian_of_mulEquiv e ⟨F, hF, hFcard⟩

end Rank

end CFSG.QuasithinUnique.SQTK.Coxeter
