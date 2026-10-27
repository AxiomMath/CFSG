module

public import CFSG.ClassicalInvolution.Q3.Q3WSides
public import CFSG.ClassicalInvolution.WeakCT.Tree

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

abbrev cs {X : Type} [Group X] (θ : SL(3, F3) →* X) (s : Fin 2) : Set X :=
  (θ.comp (blk F3 s)) '' coordSet F3

variable {X : Type} [Group X] {r : ℕ} {adj : Fin r → Fin r → Prop} {par : Fin r → Fin r}
  {dep : Fin r → ℕ} {k₀ : Fin r}

theorem exists_frame_of_tree3 (hT : RootedTree adj par dep k₀)
    (hroot : ∃ c, adj k₀ c ∨ adj c k₀) {U : Fin r → Subgroup X}
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hpair : ∀ i j, adj i j → ∃ W, LinearBlockStandardPair F3 W (U i) (U j)) :
    ∃ ρ : Fin r → SL(2, F3) →* X, (∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k) ∧
      ∀ i j, adj i j → ∃ ψ : SL(3, F3) →* X, ψ.comp (blk F3 0) = ρ i ∧ ψ.comp (blk F3 1) = ρ j := by
  classical
  have hnorm : ∀ i j, adj i j → ∃ θ : SL(3, F3) →* X, θ.ker ≤ Subgroup.center SL(3, F3) ∧
      (Bs F3 0).map θ = U i ∧ (Bs F3 1).map θ = U j := by
    intro i j h
    obtain ⟨W, hW⟩ := hpair i j h
    obtain ⟨θ, -, hker, h0, h1⟩ := pair_normalize hW
    exact ⟨θ, hker, h0, h1⟩
  choose θ hθk hθ0 hθ1 using hnorm
  have hnb : ∀ k a b, (adj k a ∨ adj a k) → (adj k b ∨ adj b k) → a ≠ b →
      ∀ x ∈ U a, ∀ y ∈ U b, x * y = y * x := by
    intro k a b hka hkb hab x hx y hy
    refine hcomm a b hab (fun h => hT.no_triangle hka hkb (Or.inl h) hab) (fun h =>
      hT.no_triangle hka hkb (Or.inr h) hab) x hx y hy
  have agree : ∀ k, (∀ a b (ha : adj k a) (hb : adj k b), cs (θ k a ha) 0 = cs (θ k b hb) 0) ∧
      (∀ a b (ha : adj k a) (hb : adj b k), cs (θ k a ha) 0 = cs (θ b k hb) 1) ∧
      (∀ a b (ha : adj a k) (hb : adj b k), cs (θ a k ha) 1 = cs (θ b k hb) 1) := by
    intro k
    refine ⟨fun a b ha hb => ?_, fun a b ha hb => ?_, fun a b ha hb => ?_⟩
    · by_cases hab : a = b
      · subst hab; rfl
      · exact coord_agree_gen 0 0 (hθk k a ha) (hθk k b hb)
          (by rw [hθ0, hθ0])
          (fun x hx y hy => by
            rw [show (0 : Fin 2).rev = 1 from rfl, hθ1] at hx hy
            exact hnb k a b (Or.inl ha) (Or.inl hb) hab x hx y hy)
    · have hab : a ≠ b := fun h => by subst h; exact hT.asymm _ _ ha hb
      exact coord_agree_gen 0 1 (hθk k a ha) (hθk b k hb)
        (by rw [hθ0, hθ1])
        (fun x hx y hy => by
          rw [show (0 : Fin 2).rev = 1 from rfl, hθ1] at hx
          rw [show (1 : Fin 2).rev = 0 from rfl, hθ0] at hy
          exact hnb k a b (Or.inl ha) (Or.inr hb) hab x hx y hy)
    · by_cases hab : a = b
      · subst hab; rfl
      · exact coord_agree_gen 1 1 (hθk a k ha) (hθk b k hb)
          (by rw [hθ1, hθ1])
          (fun x hx y hy => by
            rw [show (1 : Fin 2).rev = 0 from rfl, hθ0] at hx hy
            exact hnb k a b (Or.inr ha) (Or.inr hb) hab x hx y hy)
  let CoordGood : Fin r → Set X → Prop := fun k T =>
    (∀ q (h : adj k q), cs (θ k q h) 0 = T) ∧ (∀ q (h : adj q k), cs (θ q k h) 1 = T)
  have good_first : ∀ k a (ha : adj k a), CoordGood k (cs (θ k a ha) 0) := fun k a ha =>
    ⟨fun q h => (agree k).1 q a h ha, fun q h => ((agree k).2.1 a q ha h).symm⟩
  have good_second : ∀ k a (ha : adj a k), CoordGood k (cs (θ a k ha) 1) := fun k a ha =>
    ⟨fun q h => (agree k).2.1 q a h ha, fun q h => (agree k).2.2 q a h ha⟩
  let N : Fin r → (SL(2, F3) →* X) → Prop := fun k ρ =>
    Function.Injective ρ ∧ ρ.range = U k ∧ ∀ T, CoordGood k T → ρ '' coordSet F3 = T
  let E : Fin r → (SL(2, F3) →* X) → (SL(2, F3) →* X) → Prop := fun k ρp ρc =>
    (adj (par k) k → ∃ ψ : SL(3, F3) →* X, ψ.comp (blk F3 0) = ρp ∧ ψ.comp (blk F3 1) = ρc) ∧
      (adj k (par k) → ∃ ψ : SL(3, F3) →* X, ψ.comp (blk F3 0) = ρc ∧ ψ.comp (blk F3 1) = ρp)
  have h₀ : ∃ ρ₀, N k₀ ρ₀ := by
    obtain ⟨c, hc | hc⟩ := hroot
    · refine ⟨(θ k₀ c hc).comp (blk F3 0), comp_blk_injective (hθk _ _ hc) 0, ?_, fun T hT' => ?_⟩
      · rw [← map_Bs, hθ0]
      · exact hT'.1 c hc
    · refine ⟨(θ c k₀ hc).comp (blk F3 1), comp_blk_injective (hθk _ _ hc) 1, ?_, fun T hT' => ?_⟩
      · rw [← map_Bs, hθ1]
      · exact hT'.2 c hc
  obtain ⟨ρ₀, hρ₀⟩ := h₀
  have hf : ∀ k, k ≠ k₀ → ∀ ρp, N (par k) ρp → ∃ ρc, N k ρc ∧ E k ρp ρc := by
    intro k hk ρp ⟨hinj, hrange, htor⟩
    rcases hT.adj_par k hk with h | h
    ·
      obtain ⟨θ', hθ'k, hθ'0, hθ'1, hθ'D⟩ := exists_adjust_side3 0 (hθk _ _ h) hinj
        (by rw [hrange, ← hθ0 _ _ h]) (htor _ (good_first _ _ h))
      refine ⟨θ'.comp (blk F3 1), ⟨comp_blk_injective hθ'k 1, ?_, fun T hT' => ?_⟩,
        fun _ => ⟨θ', hθ'0, rfl⟩, fun h' => absurd h (hT.asymm _ _ h')⟩
      · rw [← map_Bs]
        exact hθ'1.trans (hθ1 _ _ h)
      · exact hθ'D.trans (hT'.2 _ h)
    ·
      obtain ⟨θ', hθ'k, hθ'1, hθ'0, hθ'D⟩ := exists_adjust_side3 1 (hθk _ _ h) hinj
        (by rw [hrange, ← hθ1 _ _ h]) (htor _ (good_second _ _ h))
      refine ⟨θ'.comp (blk F3 0), ⟨comp_blk_injective hθ'k 0, ?_, fun T hT' => ?_⟩,
        fun h' => absurd h (hT.asymm _ _ h'), fun _ => ⟨θ', rfl, hθ'1⟩⟩
      · rw [← map_Bs]
        exact hθ'0.trans (hθ0 _ _ h)
      · exact hθ'D.trans (hT'.1 _ h)
  obtain ⟨ρ, -, hρN, hρE⟩ := exists_tree_family N E par dep k₀ hT.lt hf hρ₀
  refine ⟨ρ, fun k => ⟨(hρN k).1, (hρN k).2.1⟩, fun i j hij => ?_⟩
  rcases hT.par_of_adj i j hij with ⟨hj, hpj⟩ | ⟨hi, hpi⟩
  · have := (hρE j hj).1
    rw [hpj] at this
    exact this hij
  · have := (hρE i hi).2
    rw [hpi] at this
    exact this hij

end CFSG.ClassicalInvolution.Q3.Q3W
