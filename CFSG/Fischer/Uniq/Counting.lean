module

public import CFSG.Fischer.Uniq.MuSets

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

theorem ncard_mul_eq_ncard_mul {α β : Type*} [Finite α] [Finite β] (r : α → β → Prop)
    {s : Set α} {t : Set β} {m n : ℕ} (hm : ∀ a ∈ s, {b | b ∈ t ∧ r a b}.ncard = m)
    (hn : ∀ b ∈ t, {a | a ∈ s ∧ r a b}.ncard = n) : s.ncard * m = t.ncard * n := by
  classical
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  rw [Set.ncard_eq_toFinset_card' s, Set.ncard_eq_toFinset_card' t]
  refine Finset.card_mul_eq_card_mul r (fun a ha => ?_) (fun b hb => ?_)
  · rw [← hm a (Set.mem_toFinset.1 ha), Set.ncard_eq_toFinset_card']
    congr 1
    ext b
    simp [Finset.mem_bipartiteAbove]
  · rw [← hn b (Set.mem_toFinset.1 hb), Set.ncard_eq_toFinset_card']
    congr 1
    ext a
    simp [Finset.mem_bipartiteBelow]

variable {X : Type} [Group X] {E : Set X}

theorem Pair.card_eq_add (hP : Pair X E) {d : X} (hd : d ∈ E) :
    Nat.card E = 1 + Nat.card (LocalClass E d) + Nat.card {c | c ∈ E ∧ c * d ≠ d * c} := by
  have := Pair.finite hP
  have hE : E = insert d (LocalClass E d ∪ {c | c ∈ E ∧ c * d ≠ d * c}) := by
    ext c
    constructor
    · intro hc
      by_cases hcd : c = d
      · exact Or.inl hcd
      · by_cases hcom : c * d = d * c
        · exact Or.inr (Or.inl ⟨hc, hcd, hcom⟩)
        · exact Or.inr (Or.inr ⟨hc, hcom⟩)
    · rintro (rfl | h | h)
      · exact hd
      · exact h.1
      · exact h.1
  have hd' : d ∉ LocalClass E d ∪ {c | c ∈ E ∧ c * d ≠ d * c} := by
    rintro (h | h)
    · exact h.2.1 rfl
    · exact h.2 rfl
  have hdisj : Disjoint (LocalClass E d) {c | c ∈ E ∧ c * d ≠ d * c} :=
    Set.disjoint_left.2 fun c hc hc' => hc'.2 hc.2.2
  have h := congrArg Set.ncard hE
  rw [Set.ncard_insert_of_notMem hd', Set.ncard_union_eq hdisj] at h
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq, h]
  ring

theorem localClass_eq_insert {d f : X} (hd : d ∈ E) (hf : f ∈ LocalClass E d) :
    LocalClass E f = insert d (LocalClass E d ∩ LocalClass E f ∪
      {c | c ∈ {c | c ∈ E ∧ c * d ≠ d * c} ∧ c * f = f * c}) := by
  ext g
  constructor
  · intro hg
    by_cases hgd : g = d
    · exact Or.inl hgd
    · by_cases hcom : g * d = d * g
      · exact Or.inr (Or.inl ⟨⟨hg.1, hgd, hcom⟩, hg⟩)
      · exact Or.inr (Or.inr ⟨⟨hg.1, hcom⟩, hg.2.2⟩)
  · rintro (rfl | h | ⟨⟨hg, hgd⟩, hgf⟩)
    · exact ⟨hd, hf.2.1.symm, hf.2.2.symm⟩
    · exact h.2
    · refine ⟨hg, ?_, hgf⟩
      rintro rfl
      exact hgd hf.2.2

theorem Pair.card_A (hP : Pair X E) {d : X} (hd : d ∈ E) {k l m : ℕ}
    (hk : Nat.card (LocalClass E d) = k)
    (hk' : ∀ f ∈ LocalClass E d, Nat.card (LocalClass E f) = k)
    (hl : ∀ f ∈ LocalClass E d, Nat.card ↥(LocalClass E d ∩ LocalClass E f) = l)
    (hm : ∀ c ∈ E, c * d ≠ d * c → Nat.card (muSet E d c) = m) :
    Nat.card {c | c ∈ E ∧ c * d ≠ d * c} * m = k * (k - 1 - l) := by
  have := Pair.finite hP
  rw [Nat.card_coe_set_eq] at hk ⊢
  rw [← hk]
  refine ncard_mul_eq_ncard_mul (fun c f => c * f = f * c) (fun c hc => ?_) (fun f hf => ?_)
  · rw [← hm c hc.1 hc.2, Nat.card_coe_set_eq]
    congr 1
    ext f
    constructor
    · rintro ⟨hf, hcf⟩
      refine ⟨hf, hf.1, ?_, hcf.symm⟩
      rintro rfl
      exact hc.2 hf.2.2
    · rintro ⟨hf, hfc⟩
      exact ⟨hf, hfc.2.2.symm⟩
  · have h := hk' f hf
    have h2 := hl f hf
    rw [Nat.card_coe_set_eq] at h h2
    have hd' : d ∉ LocalClass E d ∩ LocalClass E f ∪
        {c | c ∈ {c | c ∈ E ∧ c * d ≠ d * c} ∧ c * f = f * c} := by
      rintro (h | h)
      · exact h.1.2.1 rfl
      · exact h.1.2 rfl
    have hdisj : Disjoint (LocalClass E d ∩ LocalClass E f)
        {c | c ∈ {c | c ∈ E ∧ c * d ≠ d * c} ∧ c * f = f * c} :=
      Set.disjoint_left.2 fun c hc hc' => hc'.1.2 hc.1.2.2
    rw [localClass_eq_insert hd hf, Set.ncard_insert_of_notMem hd', Set.ncard_union_eq hdisj,
      h2] at h
    omega

theorem Pair.card_A_of_forall (hP : Pair X E) {d : X} (hd : d ∈ E) {k l m : ℕ}
    (hk : ∀ e ∈ E, Nat.card (LocalClass E e) = k)
    (hl : ∀ e ∈ E, ∀ f ∈ LocalClass E e, Nat.card ↥(LocalClass E e ∩ LocalClass E f) = l)
    (hm : ∀ e ∈ E, ∀ c ∈ E, c * e ≠ e * c → Nat.card (muSet E e c) = m) :
    Nat.card {c | c ∈ E ∧ c * d ≠ d * c} * m = k * (k - 1 - l) :=
  Pair.card_A hP hd (hk d hd) (fun f hf => hk f hf.1) (hl d hd) (hm d hd)

theorem Pair.card_A_eq_div (hP : Pair X E) {d : X} (hd : d ∈ E) {k l m : ℕ} (hm0 : 0 < m)
    (hk : Nat.card (LocalClass E d) = k)
    (hk' : ∀ f ∈ LocalClass E d, Nat.card (LocalClass E f) = k)
    (hl : ∀ f ∈ LocalClass E d, Nat.card ↥(LocalClass E d ∩ LocalClass E f) = l)
    (hm : ∀ c ∈ E, c * d ≠ d * c → Nat.card (muSet E d c) = m) :
    Nat.card {c | c ∈ E ∧ c * d ≠ d * c} = k * (k - 1 - l) / m :=
  (Nat.div_eq_of_eq_mul_left hm0 (Pair.card_A hP hd hk hk' hl hm).symm).symm

end CFSG.Fischer
