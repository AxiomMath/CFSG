module

public import Certificates.Data.ONanF2Tools

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup F2

section Closure

variable {G : Type*} [Group G] [DecidableEq G]

theorem bfs_sound (gens : List G) : ∀ (n : ℕ) (vis fr : List G),
    (∀ x ∈ vis, x ∈ closure {g | g ∈ gens}) → (∀ x ∈ fr, x ∈ vis) →
    ∀ x ∈ bfs gens n vis fr, x ∈ closure {g | g ∈ gens} := by
  intro n
  induction n with
  | zero =>
    intro vis fr hv _ x hx
    exact hv x (by simpa [bfs] using hx)
  | succ n ih =>
    intro vis fr hv hf x hx
    simp only [bfs] at hx
    split_ifs at hx with hnew
    · exact hv x hx
    · refine ih _ _ ?_ ?_ x hx
      · intro y hy
        rcases List.mem_append.1 hy with hy | hy
        · exact hv y hy
        · simp only [List.mem_filter, List.mem_dedup, List.mem_flatMap, List.mem_map] at hy
          obtain ⟨⟨a, ha, g, hg, rfl⟩, -⟩ := hy
          exact mul_mem (hv a (hf a ha)) (subset_closure hg)
      · intro y hy
        exact List.mem_append_right _ hy

theorem mem_bfs_of_mem (gens : List G) : ∀ (n : ℕ) (vis fr : List G) (x : G), x ∈ vis →
    x ∈ bfs gens n vis fr := by
  intro n
  induction n with
  | zero => intro vis fr x hx; simpa [bfs] using hx
  | succ n ih =>
    intro vis fr x hx
    simp only [bfs]
    split_ifs with hnew
    · exact hx
    · exact ih _ _ x (List.mem_append_left _ hx)

theorem mem_bfs_of_mem_C (gens : List G) : ∀ (n : ℕ) (vis fr : List G) (x : G), x ∈ vis →
    x ∈ bfsC gens n vis fr := by
  intro n
  induction n with
  | zero => intro vis fr x hx; simpa [bfsC] using hx
  | succ n ih =>
    intro vis fr x hx
    simp only [bfsC]
    split_ifs with hnew
    · exact hx
    · exact ih _ _ x (List.mem_append_left _ hx)

theorem mem_closure_of_mem_ballFix (gens : List G) {x : G} (hx : x ∈ ballFix gens) :
    x ∈ closure {g | g ∈ gens} :=
  bfs_sound gens 64 [1] [1] (by simp [one_mem]) (by simp) x hx

theorem one_mem_ballFix (gens : List G) : (1 : G) ∈ ballFix gens :=
  mem_bfs_of_mem gens 64 [1] [1] 1 (by simp)

omit [DecidableEq G] in
theorem mem_of_mem_closure_of_closed [Finite G] (gens L : List G) (h1 : (1 : G) ∈ L)
    (hc : ∀ x ∈ L, ∀ g ∈ gens, x * g ∈ L) {y : G} (hy : y ∈ closure {g | g ∈ gens}) : y ∈ L := by
  let T : Subgroup G :=
    { carrier := {y | ∀ x ∈ L, x * y ∈ L}
      one_mem' := fun x hx => by simpa using hx
      mul_mem' := fun {a b} ha hb x hx => by
        have := hb _ (ha x hx)
        simpa [mul_assoc] using this
      inv_mem' := fun {a} ha x hx => by
        have hpow : ∀ k : ℕ, ∀ x ∈ L, x * a ^ k ∈ L := by
          intro k
          induction k with
          | zero => intro x hx; simpa using hx
          | succ k ih =>
            intro x hx
            have := ha _ (ih x hx)
            simpa [pow_succ, mul_assoc] using this
        have hord : 0 < orderOf a := orderOf_pos a
        have hinv : a⁻¹ = a ^ (orderOf a - 1) := by
          have h2 : a ^ (orderOf a - 1) * a = 1 := by
            rw [← pow_succ, Nat.sub_add_cancel hord, pow_orderOf_eq_one]
          exact (eq_inv_of_mul_eq_one_left h2).symm
        rw [hinv]
        exact hpow _ x hx }
  have hT : closure {g | g ∈ gens} ≤ T := (closure_le T).2 fun g hg x hx => hc x hx g hg
  simpa using hT hy 1 h1

theorem SubOK.mem_closure_iff [Finite G] {gens L : List G} {n : ℕ} (h : SubOK gens L n) (x : G) :
    x ∈ closure {g | g ∈ gens} ↔ x ∈ L := by
  obtain ⟨hL, -, -, hc⟩ := h
  constructor
  · intro hx
    refine mem_of_mem_closure_of_closed gens L ?_ hc hx
    rw [hL]
    exact one_mem_ballFix gens
  · intro hx
    rw [hL] at hx
    exact mem_closure_of_mem_ballFix gens hx

theorem SubOK.card_closure [Finite G] {gens L : List G} {n : ℕ} (h : SubOK gens L n) :
    Nat.card (closure {g | g ∈ gens}) = n := by
  have hset : ∀ x : G, x ∈ closure {g | g ∈ gens} ↔ x ∈ L := SubOK.mem_closure_iff h
  have e : (closure {g | g ∈ gens}) ≃ {x : G // x ∈ L.toFinset} :=
    Equiv.subtypeEquivRight fun x => by rw [hset x, List.mem_toFinset]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup h.2.2.1, h.2.1]

theorem bfsC_sound (gens : List G) (r : G) : ∀ (n : ℕ) (vis fr : List G),
    (∀ x ∈ vis, ∃ c ∈ closure {g | g ∈ gens}, c⁻¹ * r * c = x) → (∀ x ∈ fr, x ∈ vis) →
    ∀ x ∈ bfsC gens n vis fr, ∃ c ∈ closure {g | g ∈ gens}, c⁻¹ * r * c = x := by
  intro n
  induction n with
  | zero =>
    intro vis fr hv _ x hx
    exact hv x (by simpa [bfsC] using hx)
  | succ n ih =>
    intro vis fr hv hf x hx
    simp only [bfsC] at hx
    split_ifs at hx with hnew
    · exact hv x hx
    · refine ih _ _ ?_ ?_ x hx
      · intro y hy
        rcases List.mem_append.1 hy with hy | hy
        · exact hv y hy
        · simp only [List.mem_filter, List.mem_dedup, List.mem_flatMap, List.mem_cons,
            List.not_mem_nil, or_false] at hy
          obtain ⟨⟨a, ha, g, hg, rfl | rfl⟩, -⟩ := hy
          · obtain ⟨c, hc, rfl⟩ := hv a (hf a ha)
            refine ⟨c * g, mul_mem hc (subset_closure hg), ?_⟩
            simp only [mul_inv_rev, mul_assoc]
          · obtain ⟨c, hc, rfl⟩ := hv a (hf a ha)
            refine ⟨c * g⁻¹, mul_mem hc (inv_mem (subset_closure hg)), ?_⟩
            simp only [mul_inv_rev, inv_inv, mul_assoc]
      · intro y hy
        exact List.mem_append_right _ hy

omit [DecidableEq G] in
theorem conj_mem_of_closed (gens L : List G)
    (hc : ∀ x ∈ L, ∀ g ∈ gens, g⁻¹ * x * g ∈ L ∧ g * x * g⁻¹ ∈ L) {c : G}
    (hcl : c ∈ closure {g | g ∈ gens}) : ∀ x ∈ L, c⁻¹ * x * c ∈ L ∧ c * x * c⁻¹ ∈ L := by
  let T : Subgroup G :=
    { carrier := {c | ∀ x ∈ L, c⁻¹ * x * c ∈ L ∧ c * x * c⁻¹ ∈ L}
      one_mem' := fun x hx => by simpa using hx
      mul_mem' := fun {a b} ha hb x hx => by
        obtain ⟨h1, h2⟩ := ha x hx
        obtain ⟨h3, h4⟩ := hb _ h1
        obtain ⟨h5, h6⟩ := hb _ hx
        obtain ⟨h7, h8⟩ := ha _ h6
        constructor
        · simpa [mul_assoc] using h3
        · simpa [mul_assoc] using h8
      inv_mem' := fun {a} ha x hx => by
        obtain ⟨h1, h2⟩ := ha x hx
        simpa using And.intro h2 h1 }
  have hT : closure {g | g ∈ gens} ≤ T := (closure_le T).2 fun g hg x hx => hc x hx g hg
  exact hT hcl

theorem ClassOK.mem_iff [Finite G] {gens : List G} {r : G} {L : List G} {n : ℕ}
    (h : ClassOK gens r L n) (x : G) :
    x ∈ L ↔ ∃ c ∈ closure {g | g ∈ gens}, c⁻¹ * r * c = x := by
  obtain ⟨hL, -, -, hc⟩ := h
  have hr : r ∈ L := by
    rw [hL]
    exact mem_bfs_of_mem_C gens 64 [r] [r] r (by simp)
  constructor
  · intro hx
    rw [hL] at hx
    exact bfsC_sound gens r 64 [r] [r] (by
      intro y hy
      rw [List.mem_singleton] at hy
      subst hy
      exact ⟨1, one_mem _, by simp⟩) (by simp) x hx
  · rintro ⟨c, hcl, rfl⟩
    exact (conj_mem_of_closed gens L hc hcl r hr).1

theorem commute_closure_iff {G : Type*} [Group G] (gens : List G) (t : G) :
    (∀ y ∈ Subgroup.closure {g | g ∈ gens}, t * y = y * t) ↔ ∀ y ∈ gens, t * y = y * t := by
  constructor
  · intro H y hy
    exact H y (Subgroup.subset_closure hy)
  · intro H y hy
    have hle : Subgroup.closure {g | g ∈ gens} ≤ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.closure_le]
      intro g hg
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (H g hg).symm
    have := Subgroup.mem_centralizer_singleton_iff.1 (hle hy)
    exact this.symm

end Closure

end CFSG.OddStandard.ONanRec
