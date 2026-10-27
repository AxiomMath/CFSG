module

public import CFSG.Combinatorics.AperiodicOppositeComponentsSupport
public import CFSG.Combinatorics.HexagonLayers

public section

open Finset CFSG.Combinatorics.CubicBipartiteMoore CFSG.Combinatorics.HexagonLayers
  CFSG.Combinatorics.HexagonFourEdgePath CFSG.Combinatorics.AperiodicSixteenGraph
  CFSG.Combinatorics.HexagonPeriodicPropagation

namespace CFSG.Combinatorics.AperiodicOppositeComponents

section Def

variable {V : Type*}

open scoped Classical in
noncomputable def sigmaMap (G : SimpleGraph V) (col : G.Coloring Bool)
    (w x : {v : V // col v = false}) : {v : V // col v = false} :=
  if h : ∃ (hx : x ∈ oppSet G col w) (y : {v : V // col v = false}) (hy : y ∈ oppSet G col w),
      (oppGraph G col w).dist ⟨x, hx⟩ ⟨y, hy⟩ = 4 then Classical.choose h.snd else x

theorem sigmaMap_spec {G : SimpleGraph V} {col : G.Coloring Bool}
    {w x : {v : V // col v = false}}
    (h : ∃ (hx : x ∈ oppSet G col w) (y : {v : V // col v = false}) (hy : y ∈ oppSet G col w),
      (oppGraph G col w).dist ⟨x, hx⟩ ⟨y, hy⟩ = 4) :
    ∃ hy : sigmaMap G col w x ∈ oppSet G col w,
      (oppGraph G col w).dist ⟨x, h.fst⟩ ⟨sigmaMap G col w x, hy⟩ = 4 := by
  rw [sigmaMap, dite_eq_left h]
  exact Classical.choose_spec h.snd

end Def

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {col : G.Coloring Bool} {w : {v : V // col v = false}} {ℓ : Fin 3 → V}
  {p : Fin 3 → Fin 2 → {v : V // col v = false}}
  {z q : {v : V // col v = false} → {v : V // col v = false} → {v : V // col v = false}}
  {c : {v : V // col v = false} → {v : V // col v = false} → Fin 3}
  {ε : {v : V // col v = false} → {v : V // col v = false} → Fin 2}
  {r : Fin 3 → {v : V // col v = false} → {v : V // col v = false}}
  (F : IsFrame G col w ℓ p z q c ε)
  (hr : ∀ i x, (pointGraph G col).dist w x = 3 → (pointGraph G col).dist w (r i x) = 3 ∧
    (pointGraph G col).Adj x (r i x) ∧ c x (r i x) = i)
  (haper : ∀ x : Fin 6 → {v : V // col v = false}, IsHex G col w x → ¬ IsPeriodic c x)

include F hr in
theorem sigmaMap_equiv {Q : (oppGraph G col w).ConnectedComponent} (φ : K ≃ compSet Q)
    (hφ : ∀ g i, (φ (g * s i) : {v : V // col v = false}) = r i (φ g)) (g : K) :
    sigmaMap G col w (φ g) = φ (τ g) := by
  have hex : ∃ (hx : (φ g : {v : V // col v = false}) ∈ oppSet G col w)
      (y : {v : V // col v = false}) (hy : y ∈ oppSet G col w),
      (oppGraph G col w).dist ⟨φ g, hx⟩ ⟨y, hy⟩ = 4 :=
    ⟨(φ g).2.1, φ (τ g), (φ (τ g)).2.1, by
      rw [dist_eq_of_equiv F hr φ hφ]
      exact (dist_eq_four_iff g (τ g)).mpr rfl⟩
  obtain ⟨hy, hd⟩ := sigmaMap_spec hex
  exact eq_of_dist_four F hr φ hφ g hy hd

include F hr haper in
theorem exists_equiv_eq {x : {v : V // col v = false}} (hx : x ∈ oppSet G col w) :
    ∃ (φ : K ≃ compSet ((oppGraph G col w).connectedComponentMk ⟨x, hx⟩))
      (_ : ∀ g i, (φ (g * s i) : {v : V // col v = false}) = r i (φ g)) (g : K),
      (φ g : {v : V // col v = false}) = x := by
  obtain ⟨⟨φ, hφ⟩, -⟩ := exists_equiv F hr haper ((oppGraph G col w).connectedComponentMk ⟨x, hx⟩)
  obtain ⟨g, hg⟩ := φ.surjective ⟨x, hx, rfl⟩
  exact ⟨φ, hφ, g, congrArg Subtype.val hg⟩

include F hr haper in
theorem sigmaMap_dist {x : {v : V // col v = false}} (hx : x ∈ oppSet G col w) :
    ∃ hσ : sigmaMap G col w x ∈ oppSet G col w,
      (oppGraph G col w).connectedComponentMk ⟨sigmaMap G col w x, hσ⟩ =
        (oppGraph G col w).connectedComponentMk ⟨x, hx⟩ ∧
      ∀ y (hy : y ∈ oppSet G col w),
        (oppGraph G col w).dist ⟨x, hx⟩ ⟨y, hy⟩ = 4 ↔ y = sigmaMap G col w x := by
  obtain ⟨φ, hφ, g, hxg⟩ := exists_equiv_eq F hr haper hx
  have hσ := sigmaMap_equiv F hr φ hφ g
  rw [hxg] at hσ
  rw [hσ]
  have hpt : (⟨x, hx⟩ : oppSet G col w) = ⟨φ g, (φ g).2.1⟩ := Subtype.ext hxg.symm
  refine ⟨(φ (τ g)).2.1, (φ (τ g)).2.2, fun y hy => ?_⟩
  rw [show (oppGraph G col w).dist ⟨x, hx⟩ ⟨y, hy⟩ =
      (oppGraph G col w).dist ⟨φ g, (φ g).2.1⟩ ⟨y, hy⟩ from
    congrArg (fun a => (oppGraph G col w).dist a ⟨y, hy⟩) hpt]
  refine ⟨eq_of_dist_four F hr φ hφ g hy, fun h => ?_⟩
  subst h
  rw [dist_eq_of_equiv F hr φ hφ]
  exact (dist_eq_four_iff g (τ g)).mpr rfl

include F hr haper in
theorem sigmaMap_sigmaMap {x : {v : V // col v = false}} (hx : x ∈ oppSet G col w) :
    sigmaMap G col w (sigmaMap G col w x) = x := by
  obtain ⟨φ, hφ, g, hxg⟩ := exists_equiv_eq F hr haper hx
  rw [← hxg, sigmaMap_equiv F hr φ hφ, sigmaMap_equiv F hr φ hφ, τ_τ]

include F hr haper in
theorem sigmaMap_r {x : {v : V // col v = false}} (hx : x ∈ oppSet G col w) (i : Fin 3) :
    sigmaMap G col w (r i x) = r i (sigmaMap G col w x) := by
  obtain ⟨φ, hφ, g, hxg⟩ := exists_equiv_eq F hr haper hx
  rw [← hxg, ← hφ, sigmaMap_equiv F hr φ hφ, sigmaMap_equiv F hr φ hφ, τ_mul_s, hφ]

include F hr haper in
theorem sigmaMap_mem {x : {v : V // col v = false}} (hx : x ∈ oppSet G col w) :
    sigmaMap G col w x ∈ oppSet G col w :=
  (sigmaMap_dist F hr haper hx).1

include F hr haper in
theorem adj_sigmaMap_of_adj {x y : {v : V // col v = false}} (hx : x ∈ oppSet G col w)
    (hy : y ∈ oppSet G col w) (hxy : (pointGraph G col).Adj x y) :
    (pointGraph G col).Adj (sigmaMap G col w x) (sigmaMap G col w y) := by
  rw [← F.r_eq hr hx hy hxy rfl, sigmaMap_r F hr haper hx]
  exact (hr _ _ (sigmaMap_mem F hr haper hx)).2.1

include F hr haper in
theorem adj_sigmaMap_iff {x y : {v : V // col v = false}} (hx : x ∈ oppSet G col w)
    (hy : y ∈ oppSet G col w) :
    (pointGraph G col).Adj (sigmaMap G col w x) (sigmaMap G col w y) ↔
      (pointGraph G col).Adj x y := by
  refine ⟨fun h => ?_, adj_sigmaMap_of_adj F hr haper hx hy⟩
  have := adj_sigmaMap_of_adj F hr haper (sigmaMap_mem F hr haper hx) (sigmaMap_mem F hr haper hy) h
  rwa [sigmaMap_sigmaMap F hr haper hx, sigmaMap_sigmaMap F hr haper hy] at this

include F hr haper in
theorem colour_sigmaMap {x y : {v : V // col v = false}} (hx : x ∈ oppSet G col w)
    (hy : y ∈ oppSet G col w) (hxy : (pointGraph G col).Adj x y) :
    c (sigmaMap G col w x) (sigmaMap G col w y) = c x y := by
  obtain ⟨i, hi⟩ : ∃ i, c x y = i := ⟨_, rfl⟩
  rw [hi, ← F.r_eq hr hx hy hxy hi, sigmaMap_r F hr haper hx]
  exact (hr i _ (sigmaMap_mem F hr haper hx)).2.2

include F hr haper in
theorem card_components : Nat.card (oppGraph G col w).ConnectedComponent = 2 := by
  classical
  have hlay := (order_two_hexagon_layers_and_opposite_edge_coordinates G F.moore.card
    F.moore.conn F.moore.deg col F.moore.cyc w ℓ F.inj F.root p F.line F.ne F.label).1.1 3
  have h32 : (univ.filter fun x => (pointGraph G col).dist w x = 3).card = 32 := by
    simpa using hlay
  have hO : Nat.card (oppSet G col w) = 32 := by
    rw [Nat.card_eq_card_toFinset, Set.toFinset_ofPred]
    exact h32
  have : Fintype (oppGraph G col w).ConnectedComponent := Fintype.ofFinite _
  have hfib : ∀ Q, Nat.card {x : oppSet G col w // (oppGraph G col w).connectedComponentMk x = Q}
      = 16 := fun Q => by
    rw [← (exists_equiv F hr haper Q).2]
    exact Nat.card_congr ⟨fun x => ⟨x.1.1, x.1.2, x.2⟩, fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩,
      fun _ => rfl, fun _ => rfl⟩
  have h := Nat.card_congr (Equiv.sigmaFiberEquiv (oppGraph G col w).connectedComponentMk)
  rw [Nat.card_sigma, hO] at h
  simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  rw [Nat.card_eq_fintype_card]
  omega

include F hr haper in
theorem paths_to_sigmaMap {γ : {v : V // col v = false}} (hγ : γ ∈ oppSet G col w)
    {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    r i (r j (r i (r j γ))) = sigmaMap G col w γ ∧ r k (r j (r k (r j γ))) = sigmaMap G col w γ ∧
      r i (r j γ) ≠ r k (r j γ) ∧
      {m : {v : V // col v = false} × {v : V // col v = false} |
        r j γ ∈ oppSet G col w ∧ m.1 ∈ oppSet G col w ∧ m.2 ∈ oppSet G col w ∧
          sigmaMap G col w γ ∈ oppSet G col w ∧ (pointGraph G col).Adj (r j γ) m.1 ∧
          (pointGraph G col).Adj m.1 m.2 ∧ (pointGraph G col).Adj m.2 (sigmaMap G col w γ) ∧
          [r j γ, m.1, m.2, sigmaMap G col w γ].Nodup} =
        {(r i (r j γ), r j (r i (r j γ))), (r k (r j γ), r j (r k (r j γ)))} := by
  obtain ⟨φ, hφ, g, hxg⟩ := exists_equiv_eq F hr haper hγ
  rw [← hxg, sigmaMap_equiv F hr φ hφ g, ← hφ g j]
  have hτ : τ g = τ (g * s j * s j) := by rw [mul_assoc, s_mul_self, mul_one]
  rw [hτ]
  generalize g * s j = h
  simp only [← hφ]
  refine ⟨by rw [endpoint_τ h hij], by rw [endpoint_τ h hjk.symm],
    fun e => hik (s_injective (mul_left_cancel (φ.injective (Subtype.ext e)))), ?_⟩
  rw [paths_eq_image F hr φ hφ h (τ (h * s j)), paths_to_τ h hij hjk hik, Set.image_insert_eq,
    Set.image_singleton]

include F hr haper in
theorem paths_cyclic_opp {x : {v : V // col v = false}} (hx : x ∈ oppSet G col w)
    {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    r i (r k (r j x)) = r k (r j (r i x)) ∧ r j (r i (r k x)) = r k (r j (r i x)) ∧
      r i x ≠ r j x ∧ r j x ≠ r k x ∧ r i x ≠ r k x ∧
      {m : {v : V // col v = false} × {v : V // col v = false} |
        x ∈ oppSet G col w ∧ m.1 ∈ oppSet G col w ∧ m.2 ∈ oppSet G col w ∧
          r k (r j (r i x)) ∈ oppSet G col w ∧ (pointGraph G col).Adj x m.1 ∧
          (pointGraph G col).Adj m.1 m.2 ∧ (pointGraph G col).Adj m.2 (r k (r j (r i x))) ∧
          [x, m.1, m.2, r k (r j (r i x))].Nodup} =
        {(r i x, r j (r i x)), (r j x, r k (r j x)), (r k x, r i (r k x))} ∧
      r j (r k (r i x)) = r i (r j (r k x)) ∧ r k (r i (r j x)) = r i (r j (r k x)) ∧
      r i (r j (r k x)) ≠ r k (r j (r i x)) := by
  obtain ⟨φ, hφ, g, hxg⟩ := exists_equiv_eq F hr haper hx
  rw [← hxg]
  simp only [← hφ]
  obtain ⟨e1, e2⟩ := endpoint_cyclic g hij hjk hik
  obtain ⟨f1, f2, f3⟩ := endpoint_reverse g hij hjk hik
  have hne : ∀ {a b : Fin 3}, a ≠ b →
      (φ (g * s a) : {v : V // col v = false}) ≠ φ (g * s b) :=
    fun hab e => hab (s_injective (mul_left_cancel (φ.injective (Subtype.ext e))))
  refine ⟨by rw [e1], by rw [e2], hne hij, hne hjk, hne hik, ?_, by rw [f1], by rw [f2],
    fun e => f3 (φ.injective (Subtype.ext e))⟩
  rw [paths_eq_image F hr φ hφ g (g * s i * s j * s k), paths_cyclic g hij hjk hik,
    Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]

include F hr haper in
theorem path_dichotomy {x₀ x₁ x₂ x₃ : {v : V // col v = false}}
    (hpath : x₀ ∈ oppSet G col w ∧ x₁ ∈ oppSet G col w ∧ x₂ ∈ oppSet G col w ∧
      x₃ ∈ oppSet G col w ∧ (pointGraph G col).Adj x₀ x₁ ∧ (pointGraph G col).Adj x₁ x₂ ∧
      (pointGraph G col).Adj x₂ x₃ ∧ [x₀, x₁, x₂, x₃].Nodup) :
    ∃ a b d : Fin 3, x₁ = r a x₀ ∧ x₂ = r b x₁ ∧ x₃ = r d x₂ ∧ a ≠ b ∧ b ≠ d ∧
      ((a ≠ d ∧ {m : {v : V // col v = false} × {v : V // col v = false} |
          x₀ ∈ oppSet G col w ∧ m.1 ∈ oppSet G col w ∧ m.2 ∈ oppSet G col w ∧
            x₃ ∈ oppSet G col w ∧ (pointGraph G col).Adj x₀ m.1 ∧
            (pointGraph G col).Adj m.1 m.2 ∧ (pointGraph G col).Adj m.2 x₃ ∧
            [x₀, m.1, m.2, x₃].Nodup} =
          {(r a x₀, r b (r a x₀)), (r b x₀, r d (r b x₀)), (r d x₀, r a (r d x₀))}) ∨
        (a = d ∧ ∃ e, e ≠ a ∧ e ≠ b ∧ x₃ = sigmaMap G col w (r b x₀) ∧
          {m : {v : V // col v = false} × {v : V // col v = false} |
            x₀ ∈ oppSet G col w ∧ m.1 ∈ oppSet G col w ∧ m.2 ∈ oppSet G col w ∧
              x₃ ∈ oppSet G col w ∧ (pointGraph G col).Adj x₀ m.1 ∧
              (pointGraph G col).Adj m.1 m.2 ∧ (pointGraph G col).Adj m.2 x₃ ∧
              [x₀, m.1, m.2, x₃].Nodup} =
            {(r a x₀, r b (r a x₀)), (r e x₀, r b (r e x₀))})) := by
  obtain ⟨h₀, h₁, h₂, h₃, a01, a12, a23, hnd⟩ := hpath
  obtain ⟨a, ha⟩ : ∃ a, c x₀ x₁ = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, c x₁ x₂ = b := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, c x₂ x₃ = d := ⟨_, rfl⟩
  have e1 : r a x₀ = x₁ := F.r_eq hr h₀ h₁ a01 ha
  have e2 : r b x₁ = x₂ := F.r_eq hr h₁ h₂ a12 hb
  have e3 : r d x₂ = x₃ := F.r_eq hr h₂ h₃ a23 hd
  have n02 : x₀ ≠ x₂ := fun e => by simp [e] at hnd
  have n13 : x₁ ≠ x₃ := fun e => by simp [e] at hnd
  have hab : a ≠ b := fun e => n02 (by rw [← e2, ← e, ← e1, F.r_invol hr h₀])
  have hbd : b ≠ d := fun e => n13 (by rw [← e3, ← e, ← e2, F.r_invol hr h₁])
  have hx₃ : x₃ = r d (r b (r a x₀)) := by rw [e1, e2, e3]
  refine ⟨a, b, d, e1.symm, e2.symm, e3.symm, hab, hbd, ?_⟩
  by_cases had : a = d
  · subst had
    obtain ⟨e, hea, heb⟩ := (by decide : ∀ a b : Fin 3, a ≠ b → ∃ e, e ≠ a ∧ e ≠ b) a b hab
    have hP := paths_to_sigmaMap F hr haper (hr b x₀ h₀).1 hab heb.symm hea.symm
    rw [F.r_invol hr h₀] at hP
    have hσ : x₃ = sigmaMap G col w (r b x₀) := hx₃.trans hP.1
    refine Or.inr ⟨rfl, e, hea, heb, hσ, ?_⟩
    rw [hσ]
    exact hP.2.2.2
  · refine Or.inl ⟨had, ?_⟩
    rw [hx₃]
    exact (paths_cyclic_opp F hr haper h₀ hab hbd had).2.2.2.2.2.1

end CFSG.Combinatorics.AperiodicOppositeComponents
