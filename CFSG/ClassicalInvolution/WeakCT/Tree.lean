module

public import CFSG.ClassicalInvolution.WeakCT.Sides

public section

namespace CFSG.ClassicalInvolution.WeakCT

open scoped MatrixGroups

section Propagation

theorem exists_tree_family {T : Type*} {r : ℕ} (N : Fin r → T → Prop) (E : Fin r → T → T → Prop)
    (par : Fin r → Fin r) (dep : Fin r → ℕ) (k₀ : Fin r) (hlt : ∀ k, k ≠ k₀ → dep (par k) < dep k)
    (hf : ∀ k, k ≠ k₀ → ∀ t, N (par k) t → ∃ t', N k t' ∧ E k t t') {t₀ : T} (h₀ : N k₀ t₀) :
    ∃ ρ : Fin r → T, ρ k₀ = t₀ ∧ (∀ k, N k (ρ k)) ∧ ∀ k, k ≠ k₀ → E k (ρ (par k)) (ρ k) := by
  classical
  choose g hg using hf
  have key : ∀ d : ℕ, ∃ ρ : Fin r → T, ρ k₀ = t₀ ∧ ∀ k, (k = k₀ ∨ dep k < d) →
      N k (ρ k) ∧ (k ≠ k₀ → E k (ρ (par k)) (ρ k)) := by
    intro d
    induction d with
    | zero =>
      refine ⟨fun _ => t₀, rfl, fun k hk => ?_⟩
      rcases hk with rfl | hk
      · exact ⟨h₀, fun h => absurd rfl h⟩
      · exact absurd hk (Nat.not_lt_zero _)
    | succ d ih =>
      obtain ⟨ρ, hρ0, hρ⟩ := ih
      have hpar : ∀ k, k ≠ k₀ → dep k = d → N (par k) (ρ (par k)) := by
        intro k hk hd
        by_cases hp : par k = k₀
        · exact (hρ _ (Or.inl hp)).1
        · exact (hρ _ (Or.inr (hd ▸ hlt k hk))).1
      let ρ' : Fin r → T := fun k =>
        if h : k ≠ k₀ ∧ dep k = d then g k h.1 (ρ (par k)) (hpar k h.1 h.2) else ρ k
      have hold : ∀ k, ¬ (k ≠ k₀ ∧ dep k = d) → ρ' k = ρ k := fun k h =>
        dite_eq_right_of_eq_false (eq_false h)
      have hnew : ∀ k (h : k ≠ k₀ ∧ dep k = d),
          ρ' k = g k h.1 (ρ (par k)) (hpar k h.1 h.2) := fun k h =>
        dite_eq_left_of_eq_true (eq_true h)
      have hpold : ∀ k, k ≠ k₀ → dep k ≤ d → ρ' (par k) = ρ (par k) := by
        intro k hk0 hkd
        apply hold
        rintro ⟨-, hpd⟩
        have := hlt k hk0
        omega
      refine ⟨ρ', by rw [hold k₀ (fun h => h.1 rfl)]; exact hρ0, fun k hk => ?_⟩
      by_cases hk' : k ≠ k₀ ∧ dep k = d
      · rw [hnew k hk', hpold k hk'.1 hk'.2.le]
        exact ⟨(hg k hk'.1 _ _).1, fun _ => (hg k hk'.1 _ _).2⟩
      · rw [hold k hk']
        have hk'' : k = k₀ ∨ dep k < d := by
          by_cases hk0 : k = k₀
          · exact Or.inl hk0
          · right
            have hne : dep k ≠ d := fun e => hk' ⟨hk0, e⟩
            rcases hk with h | h
            · exact absurd h hk0
            · omega
        refine ⟨(hρ k hk'').1, fun hk0 => ?_⟩
        rw [hpold k hk0 (hk''.resolve_left hk0).le]
        exact (hρ k hk'').2 hk0
  obtain ⟨ρ, hρ0, hρ⟩ := key (Finset.univ.sup dep + 1)
  have hall : ∀ k, k = k₀ ∨ dep k < Finset.univ.sup dep + 1 := fun k =>
    Or.inr (Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ k)))
  exact ⟨ρ, hρ0, fun k => (hρ k (hall k)).1, fun k hk => (hρ k (hall k)).2 hk⟩

end Propagation

section RootedTree

structure RootedTree {r : ℕ} (adj : Fin r → Fin r → Prop) (par : Fin r → Fin r)
    (dep : Fin r → ℕ) (k₀ : Fin r) : Prop where
  lt : ∀ k, k ≠ k₀ → dep (par k) < dep k
  adj_par : ∀ k, k ≠ k₀ → adj (par k) k ∨ adj k (par k)
  asymm : ∀ i j, adj i j → ¬ adj j i
  par_of_adj : ∀ i j, adj i j → (j ≠ k₀ ∧ par j = i) ∨ (i ≠ k₀ ∧ par i = j)

variable {r : ℕ} {adj : Fin r → Fin r → Prop} {par : Fin r → Fin r} {dep : Fin r → ℕ}
  {k₀ : Fin r}

namespace RootedTree

theorem dep_ne (hT : RootedTree adj par dep k₀) {x y : Fin r} (h : adj x y ∨ adj y x) :
    dep x ≠ dep y := by
  rcases h with h | h
  · rcases hT.par_of_adj x y h with ⟨hy, hp⟩ | ⟨hx, hp⟩
    · have := hT.lt y hy
      rw [hp] at this
      omega
    · have := hT.lt x hx
      rw [hp] at this
      omega
  · rcases hT.par_of_adj y x h with ⟨hx, hp⟩ | ⟨hy, hp⟩
    · have := hT.lt x hx
      rw [hp] at this
      omega
    · have := hT.lt y hy
      rw [hp] at this
      omega

theorem par_eq_of_dep_lt (hT : RootedTree adj par dep k₀) {x y : Fin r}
    (h : adj x y ∨ adj y x) (hd : dep x < dep y) : par y = x := by
  rcases h with h | h
  · rcases hT.par_of_adj x y h with ⟨-, hp⟩ | ⟨hx, hp⟩
    · exact hp
    · have := hT.lt x hx
      rw [hp] at this
      omega
  · rcases hT.par_of_adj y x h with ⟨hx, hp⟩ | ⟨-, hp⟩
    · have := hT.lt x hx
      rw [hp] at this
      omega
    · exact hp

theorem no_triangle (hT : RootedTree adj par dep k₀) {x y z : Fin r} (hxy : adj x y ∨ adj y x)
    (hxz : adj x z ∨ adj z x) (hyz : adj y z ∨ adj z y) (hy : y ≠ z) : False := by
  have dxy := hT.dep_ne hxy
  have dxz := hT.dep_ne hxz
  have dyz := hT.dep_ne hyz
  have hx1 : x ≠ y := fun h => by
    subst h
    rcases hxy with h | h <;> exact hT.asymm _ _ h h
  have hx2 : x ≠ z := fun h => by
    subst h
    rcases hxz with h | h <;> exact hT.asymm _ _ h h
  have hcases : (dep x < dep y ∧ dep z < dep y) ∨ (dep x < dep z ∧ dep y < dep z) ∨
      (dep y < dep x ∧ dep z < dep x) := by omega
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hx2 ((hT.par_eq_of_dep_lt hxy h1).symm.trans (hT.par_eq_of_dep_lt
      (by rcases hyz with h | h <;> [exact Or.inr h; exact Or.inl h]) h2))
  · exact hx1 ((hT.par_eq_of_dep_lt hxz h1).symm.trans (hT.par_eq_of_dep_lt hyz h2))
  · exact hy ((hT.par_eq_of_dep_lt
      (by rcases hxy with h | h <;> [exact Or.inr h; exact Or.inl h]) h1).symm.trans
      (hT.par_eq_of_dep_lt (by rcases hxz with h | h <;> [exact Or.inr h; exact Or.inl h]) h2))

end RootedTree

end RootedTree

section Frame

variable {K : Type} [Field K] [Finite K] {X : Type} [Group X] {r : ℕ}
  {adj : Fin r → Fin r → Prop} {par : Fin r → Fin r} {dep : Fin r → ℕ} {k₀ : Fin r}

theorem exists_frame_of_tree (hK : 4 ≤ Nat.card K) (hT : RootedTree adj par dep k₀)
    (hroot : ∃ c, adj k₀ c ∨ adj c k₀) {U : Fin r → Subgroup X}
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hpair : ∀ i j, adj i j → ∃ W, LinearBlockStandardPair K W (U i) (U j)) :
    ∃ ρ : Fin r → SL(2, K) →* X, (∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k) ∧
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
  have h₀ : ∃ ρ₀, N k₀ ρ₀ := by
    obtain ⟨c, hc | hc⟩ := hroot
    · refine ⟨(θ k₀ c hc).comp (blk K 0), comp_blk_injective (hθk _ _ hc) 0, ?_, fun T hT' => ?_⟩
      · rw [← map_Bs, hθ0]
      · rw [← (hT'.1 c hc), ← map_Ds]
    · refine ⟨(θ c k₀ hc).comp (blk K 1), comp_blk_injective (hθk _ _ hc) 1, ?_, fun T hT' => ?_⟩
      · rw [← map_Bs, hθ1]
      · rw [← (hT'.2 c hc), ← map_Ds]
  obtain ⟨ρ₀, hρ₀⟩ := h₀
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
  obtain ⟨ρ, -, hρN, hρE⟩ := exists_tree_family N E par dep k₀ hT.lt hf hρ₀
  refine ⟨ρ, fun k => ⟨(hρN k).1, (hρN k).2.1⟩, fun i j hij => ?_⟩
  rcases hT.par_of_adj i j hij with ⟨hj, hpj⟩ | ⟨hi, hpi⟩
  · have := (hρE j hj).1
    rw [hpj] at this
    exact this hij
  · have := (hρE i hi).2
    rw [hpi] at this
    exact this hij

end Frame

end CFSG.ClassicalInvolution.WeakCT
