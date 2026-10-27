module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2FoldChain

public section

open CFSG.GH74.BNPair
open scoped Pointwise

namespace CFSG.GH74.GLS.SP

variable {X : Type*} [Group X] {n : ℕ} {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X}
  {root : ℤ → Subgroup X}

theorem cardU_prod_update {k : ℤ} {l : List ℤ} (hk : k ∉ l) (f : ℤ → X) (a : X) :
    ((k :: l).map (Function.update f k a)).prod = a * (l.map f).prod := by
  rw [List.map_cons, List.prod_cons, Function.update_self]
  congr 2
  exact List.map_congr_left fun k' hk' =>
    Function.update_of_ne (fun h : k' = k => hk (h ▸ hk')) _ _

theorem cardU_update_mem {A : ℤ → Subgroup X} {k : ℤ} {l : List ℤ} (hk : k ∉ l) {f : ℤ → X}
    (hf : ∀ k' ∈ l, f k' ∈ A k') {a : X} (ha : a ∈ A k) :
    ∀ k' ∈ k :: l, Function.update f k a k' ∈ A k' := by
  intro k' hk'
  rcases List.mem_cons.1 hk' with rfl | hk'
  · simpa using ha
  · rw [Function.update_of_ne (fun e : k' = k => hk (e ▸ hk'))]
    exact hf k' hk'

theorem cardU_card_chainProd (A : ℤ → Subgroup X) :
    ∀ l : List ℤ, l.Nodup →
      (∀ f g : ℤ → X, (∀ k ∈ l, f k ∈ A k) → (∀ k ∈ l, g k ∈ A k) →
        (l.map f).prod = (l.map g).prod → ∀ k ∈ l, f k = g k) →
      Nat.card (chainProd A l) = (l.map fun k => Nat.card (A k)).prod
  | [], _, _ => by simp [chainProd]
  | k :: l, hnd, hinj => by
    rw [List.nodup_cons] at hnd
    have hinj' : ∀ f g : ℤ → X, (∀ k' ∈ l, f k' ∈ A k') → (∀ k' ∈ l, g k' ∈ A k') →
        (l.map f).prod = (l.map g).prod → ∀ k' ∈ l, f k' = g k' := by
      intro f g hf hg hfg k' hk'
      have := hinj _ _ (cardU_update_mem hnd.1 hf (A k).one_mem)
        (cardU_update_mem hnd.1 hg (A k).one_mem)
        (by rw [cardU_prod_update hnd.1, cardU_prod_update hnd.1, one_mul, one_mul]; exact hfg) k'
        (List.mem_cons_of_mem _ hk')
      rwa [Function.update_of_ne (fun e : k' = k => hnd.1 (e ▸ hk')),
        Function.update_of_ne (fun e : k' = k => hnd.1 (e ▸ hk'))] at this
    simp only [chainProd_cons, List.map_cons, List.prod_cons]
    rw [← cardU_card_chainProd A l hnd.2 hinj']
    let F : A k × chainProd A l → ↥((A k : Set X) * chainProd A l) :=
      fun p => ⟨p.1.1 * p.2.1, Set.mul_mem_mul p.1.2 p.2.2⟩
    have hF : Function.Bijective F := by
      refine ⟨?_, ?_⟩
      · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
        have h' : a * b = a' * b' := congrArg Subtype.val h
        obtain ⟨g, hg, rfl⟩ := (chain_mem_chainProd_iff A l hnd.2 b).1 hb
        obtain ⟨g', hg', rfl⟩ := (chain_mem_chainProd_iff A l hnd.2 b').1 hb'
        have key := hinj _ _ (cardU_update_mem hnd.1 hg ha) (cardU_update_mem hnd.1 hg' ha')
          (by rw [cardU_prod_update hnd.1, cardU_prod_update hnd.1]; exact h')
        have h1 : a = a' := by simpa using key k (List.mem_cons_self ..)
        subst h1
        simpa using h'
      · rintro ⟨x, hx⟩
        obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hx
        exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
    rw [← Nat.card_eq_of_bijective F hF, Nat.card_prod]

theorem cardU_length_intList_one (n : ℕ) : (intList 1 (n : ℤ)).length = n := by
  simp [intList]

theorem cardU_prod_isPow {p : ℕ} (L : List ℕ) (h : ∀ a ∈ L, ∃ m : ℕ, a = p ^ m) :
    ∃ m : ℕ, L.prod = p ^ m := by
  induction L with
  | nil => exact ⟨0, by simp⟩
  | cons a L ih =>
    obtain ⟨m, hm⟩ := h a (List.mem_cons_self ..)
    obtain ⟨m', hm'⟩ := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    exact ⟨m + m', by rw [List.prod_cons, hm, hm', pow_add]⟩

namespace RGD2

theorem card_U (R : RGD2 n H r₁ r₂ U root) :
    Nat.card U = ((intList 1 (n : ℤ)).map fun k => Nat.card (root k)).prod := by
  rw [← cardU_card_chainProd root (intList 1 n) (chain_intList_nodup 1 n) R.unique, ← R.carrier_eq]
  rfl

theorem card_U_of_card_root (R : RGD2 n H r₁ r₂ U root) {q : ℕ}
    (hq : ∀ k : ℤ, 1 ≤ k → k ≤ n → Nat.card (root k) = q) : Nat.card U = q ^ n := by
  rw [R.card_U, List.map_congr_left (g := fun _ => q) fun k hk =>
    hq k (mem_intList_iff.1 hk).1 (mem_intList_iff.1 hk).2, List.map_const', List.prod_replicate,
    cardU_length_intList_one]

end RGD2

end CFSG.GH74.GLS.SP
