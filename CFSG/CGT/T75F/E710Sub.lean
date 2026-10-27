module

public import CFSG.CGT.T75F.E710Defs

public section

namespace CFSG.CGT.T75F

open CFSG.CGT.Timmesfeld75

structure EndgameData {G : Type} [Group G] (X' : Subgroup G) (D : Set G) (M L : Subgroup G)
    (q : ℕ) : Prop where
  conj_mem : ∀ d ∈ D, ∀ g ∈ X', g * d * g⁻¹ ∈ D
  sq_eq_one : ∀ d ∈ D, d * d = 1
  ne_one : ∀ d ∈ D, d ≠ 1
  order : ∀ d ∈ D, d ∈ X' → ∀ e ∈ D, e ∈ X' → orderOf (d * e) = 4 ∨ Odd (orderOf (d * e)) ∨
    ∃ k : ℕ, Odd k ∧ orderOf (d * e) = 2 * k
  four : ∀ d ∈ D, d ∈ X' → ∀ e ∈ D, e ∈ X' → orderOf (d * e) = 4 → (d * e) ^ 2 ∈ D
  M_le : M ≤ X'
  M_comm : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a
  M_sq : ∀ a ∈ M, a * a = 1
  M_gen : Subgroup.closure (D ∩ (M : Set G)) = M
  M_card : Nat.card M = q ^ 4
  gen : ∀ e ∈ D, e ∈ X' → e ∉ M → Subgroup.closure ((M : Set G) ∪ {e}) = X'
  exists_out : ∃ y ∈ D, y ∈ X' ∧ y ∉ M
  H3 : ∀ β ∈ D, β ∈ M → ∀ d ∈ D, d ∈ X' → d * β = β * d → d ∈ M
  q_pow : ∃ m : ℕ, 2 ≤ m ∧ q = 2 ^ m
  card_Delta : Nat.card (D ∩ (M : Set G) : Set G) = (q + 1) * (q ^ 2 - 1)
  L_le : L ≤ M
  L_card : Nat.card L = q ^ 2
  L_D : ∀ l ∈ L, l ≠ 1 → l ∈ D
  L_TI : ∀ g ∈ X', ∀ l ∈ L, l ≠ 1 → g * l * g⁻¹ ∈ L → ∀ l' ∈ L, g * l' * g⁻¹ ∈ L
  count65 : ∀ e ∈ D, e ∈ M → e ∉ L → Nat.card {l : G | l ∈ L ∧ e * l ∈ D} ≤ q

variable {G : Type} [Group G] [Finite G] {X' : Subgroup G} {D : Set G} {M L : Subgroup G}
  {q : ℕ}

namespace EndgameData

variable (h : EndgameData X' D M L q)

include h in
theorem toEndgame710 :
    Endgame710 {a : ↥X' | (a : G) ∈ D} (M.subgroupOf X') (L.subgroupOf X') q := by
  have hL : L ≤ X' := h.L_le.trans h.M_le
  have hsub : ∀ S : Set G, S ⊆ X' → X'.subtype '' {a : ↥X' | (a : G) ∈ S} = S := by
    intro S hS
    ext g
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hg
      exact ⟨⟨g, hS hg⟩, hg, rfl⟩
  refine
    { conj_mem := fun d hd g => h.conj_mem d hd g g.2
      sq_eq_one := fun d hd => Subtype.ext (h.sq_eq_one d hd)
      ne_one := fun d hd hd1 => h.ne_one d hd (congrArg Subtype.val hd1)
      order := ?_
      four := ?_
      M_comm := ?_
      M_sq := ?_
      M_gen := ?_
      M_card := ?_
      gen := ?_
      exists_out := ?_
      H3 := ?_
      q_pow := h.q_pow
      card_Delta := ?_
      L_le := Subgroup.subgroupOf_mono X' h.L_le
      L_card := ?_
      L_D := ?_
      L_TI := ?_
      count65 := ?_ }
  · intro d hd e he
    have := h.order d hd d.2 e he e.2
    rw [← Subgroup.orderOf_coe (d * e)]
    exact this
  · intro d hd e he ho
    have h1 : orderOf ((d : G) * (e : G)) = 4 := by
      rw [← Subgroup.orderOf_coe (d * e)] at ho
      exact ho
    exact h.four d hd d.2 e he e.2 h1
  · intro a ha b hb
    exact Subtype.ext (h.M_comm a ha b hb)
  · intro a ha
    exact Subtype.ext (h.M_sq a ha)
  · apply Subgroup.map_injective X'.subtype_injective
    rw [MonoidHom.map_closure, Subgroup.map_subgroupOf_eq_of_le h.M_le]
    have : X'.subtype '' ({a : ↥X' | (a : G) ∈ D} ∩ ((M.subgroupOf X' : Subgroup ↥X') : Set ↥X')) =
        D ∩ (M : Set G) := by
      ext g
      constructor
      · rintro ⟨a, ⟨haD, haM⟩, rfl⟩
        exact ⟨haD, haM⟩
      · rintro ⟨hgD, hgM⟩
        exact ⟨⟨g, h.M_le hgM⟩, ⟨hgD, hgM⟩, rfl⟩
    rw [this]
    exact h.M_gen
  · have := h.M_card
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.M_le).toEquiv] at this
    exact this
  · intro e he heM
    apply Subgroup.map_injective X'.subtype_injective
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hMe : (e : G) ∉ M := fun h' => heM h'
    have : X'.subtype '' (((M.subgroupOf X' : Subgroup ↥X') : Set ↥X') ∪ {e}) =
        (M : Set G) ∪ {(e : G)} := by
      ext g
      constructor
      · rintro ⟨a, ha | ha, rfl⟩
        · exact Or.inl ha
        · rw [Set.mem_singleton_iff] at ha
          subst ha
          exact Or.inr rfl
      · rintro (hg | hg)
        · exact ⟨⟨g, h.M_le hg⟩, Or.inl hg, rfl⟩
        · rw [Set.mem_singleton_iff] at hg
          subst hg
          exact ⟨e, Or.inr rfl, rfl⟩
    rw [this]
    exact h.gen e he e.2 hMe
  · obtain ⟨y, hy, hyX, hyM⟩ := h.exists_out
    exact ⟨⟨y, hyX⟩, hy, fun h' => hyM h'⟩
  · intro β hβ hβM d hd hdβ
    exact h.H3 β hβ hβM d hd d.2 (congrArg Subtype.val hdβ)
  · have hset : X'.subtype '' ({a : ↥X' | (a : G) ∈ D} ∩
        ((M.subgroupOf X' : Subgroup ↥X') : Set ↥X')) = D ∩ (M : Set G) := by
      ext g
      constructor
      · rintro ⟨a, ⟨haD, haM⟩, rfl⟩
        exact ⟨haD, haM⟩
      · rintro ⟨hgD, hgM⟩
        exact ⟨⟨g, h.M_le hgM⟩, ⟨hgD, hgM⟩, rfl⟩
    have h1 := h.card_Delta
    rw [← hset, Nat.card_coe_set_eq, Set.ncard_image_of_injective _ X'.subtype_injective,
      ← Nat.card_coe_set_eq] at h1
    exact h1
  · have := h.L_card
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL).toEquiv] at this
    exact this
  · intro l hl hl1
    exact h.L_D l hl (fun h' => hl1 (Subtype.ext h'))
  · intro g l hl hl1 hgl l' hl'
    exact h.L_TI g g.2 l hl (fun h' => hl1 (Subtype.ext h')) hgl l' hl'
  · intro e he heM heL
    have hinj : Function.Injective (fun l : {l : ↥X' | l ∈ L.subgroupOf X' ∧ e * l ∈
        {a : ↥X' | (a : G) ∈ D}} => (l : ↥X')) := Subtype.val_injective
    have h1 : Nat.card {l : ↥X' | l ∈ L.subgroupOf X' ∧ e * l ∈ {a : ↥X' | (a : G) ∈ D}} ≤
        Nat.card {l : G | l ∈ L ∧ (e : G) * l ∈ D} := by
      refine Nat.card_le_card_of_injective
        (fun l => (⟨(l.1 : G), l.2.1, l.2.2⟩ : {l : G | l ∈ L ∧ (e : G) * l ∈ D})) ?_
      intro a b hab
      have h2 := congrArg (fun z : {l : G | l ∈ L ∧ (e : G) * l ∈ D} => (z : G)) hab
      exact Subtype.ext (Subtype.ext h2)
    exact h1.trans (h.count65 e he heM (fun h' => heL h'))

end EndgameData

end CFSG.CGT.T75F
