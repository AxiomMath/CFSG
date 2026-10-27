module

public import CFSG.ClassicalInvolution.WeakCT.Tree

public section

namespace CFSG.ClassicalInvolution.WeakCT

open scoped MatrixGroups

section Frame

variable {K : Type} [Field K] [Finite K] {X : Type} [Group X] {r : ℕ}
  {adj : Fin r → Fin r → Prop} {par : Fin r → Fin r} {dep : Fin r → ℕ} {k₀ : Fin r}

theorem exists_frame_of_tree_root (hK : 4 ≤ Nat.card K) (hT : RootedTree adj par dep k₀)
    (hroot : ∃ c, adj k₀ c ∨ adj c k₀) {U : Fin r → Subgroup X}
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hpair : ∀ i j, adj i j → ∃ W, LinearBlockStandardPair K W (U i) (U j))
    {ρ₀ : SL(2, K) →* X} (hinj₀ : Function.Injective ρ₀) (hrange₀ : ρ₀.range = U k₀)
    (htor₀ : ∀ q, adj k₀ q → ∀ θ : SL(3, K) →* X, θ.ker ≤ Subgroup.center SL(3, K) →
      (Bs K 0).map θ = U k₀ → (Bs K 1).map θ = U q →
        (Ds K 0).map θ = (diagTorus2 K).map ρ₀)
    (htor₁ : ∀ q, adj q k₀ → ∀ θ : SL(3, K) →* X, θ.ker ≤ Subgroup.center SL(3, K) →
      (Bs K 1).map θ = U k₀ → (Bs K 0).map θ = U q →
        (Ds K 1).map θ = (diagTorus2 K).map ρ₀) :
    ∃ ρ : Fin r → SL(2, K) →* X, ρ k₀ = ρ₀ ∧
      (∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k) ∧
      ∀ i j, adj i j → ∃ ψ : SL(3, K) →* X, ψ.comp (blk K 0) = ρ i ∧ ψ.comp (blk K 1) = ρ j := by
  classical
  have hK3 : 3 ≤ Nat.card K := by omega
  have hnorm : ∀ i j, adj i j → ∃ θ : SL(3, K) →* X, θ.ker ≤ Subgroup.center SL(3, K) ∧
      (Bs K 0).map θ = U i ∧ (Bs K 1).map θ = U j := by
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
  have agree : ∀ k, (∀ a b (ha : adj k a) (hb : adj k b),
        (Ds K 0).map (θ k a ha) = (Ds K 0).map (θ k b hb)) ∧
      (∀ a b (ha : adj k a) (hb : adj b k), (Ds K 0).map (θ k a ha) = (Ds K 1).map (θ b k hb)) ∧
      (∀ a b (ha : adj a k) (hb : adj b k), (Ds K 1).map (θ a k ha) = (Ds K 1).map (θ b k hb)) := by
    intro k
    refine ⟨fun a b ha hb => ?_, fun a b ha hb => ?_, fun a b ha hb => ?_⟩
    · by_cases hab : a = b
      · subst hab; rfl
      · exact torus_agree_gen hK3 0 0 (hθk k a ha) (hθk k b hb)
          (by rw [hθ0, hθ0])
          (fun x hx y hy => by
            rw [show (0 : Fin 2).rev = 1 from rfl, hθ1] at hx hy
            exact hnb k a b (Or.inl ha) (Or.inl hb) hab x hx y hy)
    · have hab : a ≠ b := fun h => by subst h; exact hT.asymm _ _ ha hb
      exact torus_agree_gen hK3 0 1 (hθk k a ha) (hθk b k hb)
        (by rw [hθ0, hθ1])
        (fun x hx y hy => by
          rw [show (0 : Fin 2).rev = 1 from rfl, hθ1] at hx
          rw [show (1 : Fin 2).rev = 0 from rfl, hθ0] at hy
          exact hnb k a b (Or.inl ha) (Or.inr hb) hab x hx y hy)
    · by_cases hab : a = b
      · subst hab; rfl
      · exact torus_agree_gen hK3 1 1 (hθk a k ha) (hθk b k hb)
          (by rw [hθ1, hθ1])
          (fun x hx y hy => by
            rw [show (1 : Fin 2).rev = 0 from rfl, hθ0] at hx hy
            exact hnb k a b (Or.inr ha) (Or.inr hb) hab x hx y hy)
  let TorGood : Fin r → Subgroup X → Prop := fun k T =>
    (∀ q (h : adj k q), (Ds K 0).map (θ k q h) = T) ∧
      (∀ q (h : adj q k), (Ds K 1).map (θ q k h) = T)
  have torGood_first : ∀ k a (ha : adj k a), TorGood k ((Ds K 0).map (θ k a ha)) := fun k a ha =>
    ⟨fun q h => (agree k).1 q a h ha, fun q h => ((agree k).2.1 a q ha h).symm⟩
  have torGood_second : ∀ k a (ha : adj a k), TorGood k ((Ds K 1).map (θ a k ha)) := fun k a ha =>
    ⟨fun q h => (agree k).2.1 q a h ha, fun q h => (agree k).2.2 q a h ha⟩
  let N : Fin r → (SL(2, K) →* X) → Prop := fun k ρ =>
    Function.Injective ρ ∧ ρ.range = U k ∧ ∀ T, TorGood k T → (diagTorus2 K).map ρ = T
  let E : Fin r → (SL(2, K) →* X) → (SL(2, K) →* X) → Prop := fun k ρp ρc =>
    (adj (par k) k → ∃ ψ : SL(3, K) →* X, ψ.comp (blk K 0) = ρp ∧ ψ.comp (blk K 1) = ρc) ∧
      (adj k (par k) → ∃ ψ : SL(3, K) →* X, ψ.comp (blk K 0) = ρc ∧ ψ.comp (blk K 1) = ρp)
  have h₀ : N k₀ ρ₀ := by
    refine ⟨hinj₀, hrange₀, fun T hT' => ?_⟩
    obtain ⟨c, hc | hc⟩ := hroot
    · rw [← hT'.1 c hc]
      exact (htor₀ c hc (θ k₀ c hc) (hθk _ _ hc) (hθ0 _ _ hc) (hθ1 _ _ hc)).symm
    · rw [← hT'.2 c hc]
      exact (htor₁ c hc (θ c k₀ hc) (hθk _ _ hc) (hθ1 _ _ hc) (hθ0 _ _ hc)).symm
  have hf : ∀ k, k ≠ k₀ → ∀ ρp, N (par k) ρp → ∃ ρc, N k ρc ∧ E k ρp ρc := by
    intro k hk ρp ⟨hinj, hrange, htor⟩
    rcases hT.adj_par k hk with h | h
    ·
      obtain ⟨θ', hθ'k, hθ'0, hθ'1, hθ'D⟩ := exists_adjust_side hK 0 (hθk _ _ h) hinj
        (by rw [hrange, ← hθ0 _ _ h]) (htor _ (torGood_first _ _ h))
      refine ⟨θ'.comp (blk K 1), ⟨comp_blk_injective hθ'k 1, ?_, fun T hT' => ?_⟩,
        fun _ => ⟨θ', hθ'0, rfl⟩, fun h' => absurd h (hT.asymm _ _ h')⟩
      · rw [← map_Bs]
        exact hθ'1.trans (hθ1 _ _ h)
      · rw [← map_Ds]
        exact hθ'D.trans (hT'.2 _ h)
    ·
      obtain ⟨θ', hθ'k, hθ'1, hθ'0, hθ'D⟩ := exists_adjust_side hK 1 (hθk _ _ h) hinj
        (by rw [hrange, ← hθ1 _ _ h]) (htor _ (torGood_second _ _ h))
      refine ⟨θ'.comp (blk K 0), ⟨comp_blk_injective hθ'k 0, ?_, fun T hT' => ?_⟩,
        fun h' => absurd h (hT.asymm _ _ h'), fun _ => ⟨θ', rfl, hθ'1⟩⟩
      · rw [← map_Bs]
        exact hθ'0.trans (hθ0 _ _ h)
      · rw [← map_Ds]
        exact hθ'D.trans (hT'.1 _ h)
  obtain ⟨ρ, hρ₀, hρN, hρE⟩ := exists_tree_family N E par dep k₀ hT.lt hf h₀
  refine ⟨ρ, hρ₀, fun k => ⟨(hρN k).1, (hρN k).2.1⟩, fun i j hij => ?_⟩
  rcases hT.par_of_adj i j hij with ⟨hj, hpj⟩ | ⟨hi, hpi⟩
  · have := (hρE j hj).1
    rw [hpj] at this
    exact this hij
  · have := (hρE i hi).2
    rw [hpi] at this
    exact this hij

end Frame

end CFSG.ClassicalInvolution.WeakCT
