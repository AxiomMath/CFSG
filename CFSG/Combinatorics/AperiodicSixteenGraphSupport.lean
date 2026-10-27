module

public import CFSG.Combinatorics.AperiodicSixteenGraph
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

public section

open Finset

namespace CFSG.Combinatorics.AperiodicSixteenGraph

theorem reachable_and_dist_eq_of_level {V : Type*} {G : SimpleGraph V} {o : V} (f : V → ℕ)
    (h0 : f o = 0) (hlip : ∀ u v, G.Adj u v → f v ≤ f u + 1)
    (hdown : ∀ v, v ≠ o → ∃ u, G.Adj u v ∧ f u + 1 = f v) (v : V) :
    G.Reachable o v ∧ G.dist o v = f v := by
  have hwalk : ∀ n v, f v = n → ∃ p : G.Walk o v, p.length = n := by
    intro n
    induction n with
    | zero =>
      intro v hv
      by_cases hvo : v = o
      · subst hvo
        exact ⟨SimpleGraph.Walk.nil, rfl⟩
      · obtain ⟨u, -, hu⟩ := hdown v hvo
        omega
    | succ n ih =>
      intro v hv
      have hvo : v ≠ o := by
        rintro rfl
        omega
      obtain ⟨u, huv, hu⟩ := hdown v hvo
      obtain ⟨p, hp⟩ := ih u (by omega)
      exact ⟨p.concat huv, by rw [SimpleGraph.Walk.length_concat, hp]⟩
  have hlow : ∀ {a b : V} (p : G.Walk a b), f b ≤ f a + p.length := by
    intro a b p
    induction p with
    | nil => simp
    | cons h p ih =>
      have := hlip _ _ h
      rw [SimpleGraph.Walk.length_cons]
      omega
  obtain ⟨p, hp⟩ := hwalk (f v) v rfl
  have hr : G.Reachable o v := ⟨p⟩
  refine ⟨hr, le_antisymm ((SimpleGraph.dist_le p).trans hp.le) ?_⟩
  obtain ⟨q, hq⟩ := hr.exists_walk_length_eq_dist
  have := hlow q
  omega

private def level (g : K) : ℕ :=
  if (g.vec 0).val + (g.vec 1).val + (g.vec 2).val = 0 then 4 * g.cen.val
  else if (g.vec 0).val + (g.vec 1).val + (g.vec 2).val = 1 then 1 + 2 * g.cen.val
  else (g.vec 0).val + (g.vec 1).val + (g.vec 2).val

private theorem level_one : level 1 = 0 := by
  decide

private theorem level_mul_s_le : ∀ (g : K) (i : Fin 3), level (g * s i) ≤ level g + 1 := by
  decide

private theorem exists_level_mul_s :
    ∀ g : K, g ≠ 1 → ∃ i : Fin 3, level (g * s i) + 1 = level g := by
  decide

private theorem level_eq_four_iff : ∀ g : K, level g = 4 ↔ g = z := by
  decide

private theorem level_le_four : ∀ g : K, level g ≤ 4 := by
  decide

private theorem reachable_and_dist_eq (g h : K) :
    T.Reachable g h ∧ T.dist g h = level (g⁻¹ * h) := by
  refine reachable_and_dist_eq_of_level (G := T) (o := g) (fun h => level (g⁻¹ * h))
    (by rw [inv_mul_cancel, level_one]) ?_ ?_ h
  · rintro u v ⟨i, rfl⟩
    rw [← mul_assoc]
    exact level_mul_s_le _ i
  · intro v hv
    obtain ⟨i, hi⟩ := exists_level_mul_s (g⁻¹ * v) fun h => hv (inv_mul_eq_one.mp h).symm
    exact ⟨v * s i, ⟨i, by rw [mul_assoc, s_mul_self, mul_one]⟩, by rw [← mul_assoc]; exact hi⟩

theorem connected : T.Connected :=
  ⟨fun g h => (reachable_and_dist_eq g h).1⟩

theorem dist_eq_four_iff (g h : K) : T.dist g h = 4 ↔ h = τ g := by
  rw [(reachable_and_dist_eq g h).2, level_eq_four_iff, inv_mul_eq_iff_eq_mul, τ]

theorem card_sphere :
    (univ.filter fun g => T.dist o g = 0).card = 1 ∧
      (univ.filter fun g => T.dist o g = 1).card = 3 ∧
      (univ.filter fun g => T.dist o g = 2).card = 6 ∧
      (univ.filter fun g => T.dist o g = 3).card = 5 ∧
      (univ.filter fun g => T.dist o g = 4).card = 1 ∧ ∀ g, T.dist o g ≤ 4 := by
  have hd : ∀ g, T.dist o g = level g := fun g => by
    rw [(reachable_and_dist_eq o g).2, o, inv_one, one_mul]
  have e : ∀ n, (univ.filter fun g => T.dist o g = n) = univ.filter fun g => level g = n :=
    fun n => Finset.filter_congr fun g _ => by rw [hd g]
  rw [e 0, e 1, e 2, e 3, e 4]
  exact ⟨by decide, by decide, by decide, by decide, by decide, fun g => (hd g).symm ▸
    level_le_four g⟩

private theorem parity_mul_s : ∀ (g : K) (i : Fin 3),
    decide (g.vec 0 + g.vec 1 + g.vec 2 = 1) ≠
      decide ((g * s i).vec 0 + (g * s i).vec 1 + (g * s i).vec 2 = 1) := by
  decide

def parity : T.Coloring Bool :=
  SimpleGraph.Coloring.mk (fun g => decide (g.vec 0 + g.vec 1 + g.vec 2 = 1)) fun {g _} hgh => by
    obtain ⟨i, rfl⟩ := hgh
    exact parity_mul_s g i

theorem isBipartite : T.IsBipartite := by
  simpa using parity.colorable

private theorem no_square_word :
    ∀ a b c d : Fin 3, s a * s b * s c * s d = 1 → s a * s b = 1 ∨ s b * s c = 1 := by
  decide

theorem six_le_length_of_isCycle {g : K} (p : T.Walk g g) (hp : p.IsCycle) : 6 ≤ p.length := by
  have heven : Even p.length := (parity.even_length_iff_congr p).mpr Iff.rfl
  have h3 := hp.three_le_length
  by_contra hlt
  have h4 : p.length = 4 := by
    obtain ⟨m, hm⟩ := heven
    omega
  have hnd := hp.support_nodup
  rcases p with _ | ⟨h₁, _ | ⟨h₂, _ | ⟨h₃, _ | ⟨h₄, _ | ⟨h₅, p⟩⟩⟩⟩⟩ <;>
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil] at h4 <;> try omega
  rw [SimpleGraph.Walk.support_cons, List.tail_cons, SimpleGraph.Walk.support_cons,
    SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_cons,
    SimpleGraph.Walk.support_nil] at hnd
  obtain ⟨a, rfl⟩ := h₁
  obtain ⟨b, rfl⟩ := h₂
  obtain ⟨c, rfl⟩ := h₃
  obtain ⟨d, hd⟩ := h₄
  have n20 : g * s a * s b ≠ g := fun h => by
    rw [h] at hnd
    simp at hnd
  have n13 : g * s a ≠ g * s a * s b * s c := fun h => by
    rw [← h] at hnd
    simp at hnd
  have e : s a * s b * s c * s d = 1 :=
    mul_left_cancel (a := g) (by simpa only [mul_assoc, mul_one] using hd.symm)
  rcases no_square_word a b c d e with h | h
  · exact n20 (by rw [mul_assoc, h, mul_one])
  · exact n13 (by rw [mul_assoc (g * s a), h, mul_one])

theorem τ_τ (g : K) : τ (τ g) = g := by
  rw [τ, τ, mul_assoc, z_mul_self, mul_one]

theorem τ_mul_s (g : K) (i : Fin 3) : τ (g * s i) = τ g * s i := by
  rw [τ, τ, mul_assoc, mul_assoc, z_mul]

theorem adj_τ_iff {g h : K} : T.Adj (τ g) (τ h) ↔ T.Adj g h := by
  simp only [adj_iff, τ]
  refine exists_congr fun i => ?_
  rw [mul_assoc g z, z_mul, ← mul_assoc, mul_left_inj]

private theorem nodup_word :
    ∀ a b c : Fin 3, a ≠ b → b ≠ c → [1, s a, s a * s b, s a * s b * s c].Nodup := by
  decide

theorem path_iff {x₀ x₁ x₂ x₃ : K} :
    (T.Adj x₀ x₁ ∧ T.Adj x₁ x₂ ∧ T.Adj x₂ x₃ ∧ [x₀, x₁, x₂, x₃].Nodup) ↔
      ∃ a b c, a ≠ b ∧ b ≠ c ∧ x₁ = x₀ * s a ∧ x₂ = x₀ * s a * s b ∧
        x₃ = x₀ * s a * s b * s c := by
  constructor
  · rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩, hnd⟩
    refine ⟨a, b, c, ?_, ?_, rfl, rfl, rfl⟩
    · rintro rfl
      simp [mul_assoc, s_mul_self] at hnd
    · rintro rfl
      simp [mul_assoc, s_mul_self] at hnd
  · rintro ⟨a, b, c, hab, hbc, rfl, rfl, rfl⟩
    refine ⟨⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩, ?_⟩
    simpa [mul_assoc] using (nodup_word a b c hab hbc).map (mul_right_injective x₀)

private theorem s_mul_s_mul_s : ∀ i j : Fin 3, i ≠ j → s i * s j * s i = s j * z := by
  decide

private theorem word_eq_s_mul_z : ∀ i j k a b c : Fin 3, i ≠ j → j ≠ k → i ≠ k → a ≠ b →
    b ≠ c → s a * s b * s c = s j * z → (a = i ∧ b = j) ∨ (a = k ∧ b = j) := by
  decide

private theorem cyclic_words : ∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k →
    s j * s k * s i = s i * s j * s k ∧ s k * s i * s j = s i * s j * s k := by
  decide

private theorem reverse_words : ∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k →
    s i * s k * s j = s k * s j * s i ∧ s j * s i * s k = s k * s j * s i ∧
      s k * s j * s i ≠ s i * s j * s k := by
  decide

private theorem word_eq_cyclic : ∀ i j k a b c : Fin 3, i ≠ j → j ≠ k → i ≠ k → a ≠ b →
    b ≠ c → s a * s b * s c = s i * s j * s k →
      (a = i ∧ b = j) ∨ (a = j ∧ b = k) ∨ (a = k ∧ b = i) := by
  decide

private theorem endpoint_eq (g : K) {a b c d e f : Fin 3}
    (h : s a * s b * s c = s d * s e * s f) : g * s a * s b * s c = g * s d * s e * s f := by
  simp only [mul_assoc] at h ⊢
  rw [h]

theorem endpoint_τ (g : K) {i j : Fin 3} (hij : i ≠ j) : g * s i * s j * s i = τ (g * s j) := by
  rw [τ, mul_assoc g (s j) z, ← s_mul_s_mul_s i j hij]
  simp only [mul_assoc]

theorem endpoint_cyclic (g : K) {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    g * s j * s k * s i = g * s i * s j * s k ∧ g * s k * s i * s j = g * s i * s j * s k :=
  ⟨endpoint_eq g (cyclic_words i j k hij hjk hik).1,
    endpoint_eq g (cyclic_words i j k hij hjk hik).2⟩

theorem endpoint_reverse (g : K) {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    g * s i * s k * s j = g * s k * s j * s i ∧ g * s j * s i * s k = g * s k * s j * s i ∧
      g * s k * s j * s i ≠ g * s i * s j * s k := by
  obtain ⟨h1, h2, h3⟩ := reverse_words i j k hij hjk hik
  refine ⟨endpoint_eq g h1, endpoint_eq g h2, fun h => h3 ?_⟩
  simp only [mul_assoc] at h ⊢
  exact mul_left_cancel h

theorem paths_to_τ (g : K) {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    {m : K × K | T.Adj g m.1 ∧ T.Adj m.1 m.2 ∧ T.Adj m.2 (τ (g * s j)) ∧
      [g, m.1, m.2, τ (g * s j)].Nodup} = {(g * s i, g * s i * s j), (g * s k, g * s k * s j)} := by
  ext ⟨x₁, x₂⟩
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  rw [path_iff]
  constructor
  · rintro ⟨a, b, c, hab, hbc, rfl, rfl, he⟩
    have he' : s a * s b * s c = s j * z :=
      mul_left_cancel (a := g) (by simpa only [τ, mul_assoc] using he.symm)
    rcases word_eq_s_mul_z i j k a b c hij hjk hik hab hbc he' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨i, j, i, hij, hij.symm, rfl, rfl, (endpoint_τ g hij).symm⟩
    · exact ⟨k, j, k, hjk.symm, hjk, rfl, rfl, (endpoint_τ g hjk.symm).symm⟩

theorem paths_cyclic (g : K) {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    {m : K × K | T.Adj g m.1 ∧ T.Adj m.1 m.2 ∧ T.Adj m.2 (g * s i * s j * s k) ∧
      [g, m.1, m.2, g * s i * s j * s k].Nodup} =
      {(g * s i, g * s i * s j), (g * s j, g * s j * s k), (g * s k, g * s k * s i)} := by
  ext ⟨x₁, x₂⟩
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  rw [path_iff]
  constructor
  · rintro ⟨a, b, c, hab, hbc, rfl, rfl, he⟩
    have he' : s a * s b * s c = s i * s j * s k :=
      mul_left_cancel (a := g) (by simpa only [mul_assoc] using he.symm)
    rcases word_eq_cyclic i j k a b c hij hjk hik hab hbc he' with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · obtain ⟨h1, h2⟩ := endpoint_cyclic g hij hjk hik
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨i, j, k, hij, hjk, rfl, rfl, rfl⟩
    · exact ⟨j, k, i, hjk, hik.symm, rfl, rfl, h1.symm⟩
    · exact ⟨k, i, j, hik.symm, hij, rfl, rfl, h2.symm⟩

end CFSG.Combinatorics.AperiodicSixteenGraph
