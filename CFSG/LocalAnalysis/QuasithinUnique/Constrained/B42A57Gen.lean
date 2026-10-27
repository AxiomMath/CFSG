module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57GenData7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57GenData5
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.QuasithinUnique.B42A57

open Equiv Equiv.Perm

theorem isPGroup_two_of_sq {G : Type*} [Group G] (A : Subgroup G) (hA : ∀ a ∈ A, a * a = 1) :
    IsPGroup 2 A := by
  refine IsPGroup.iff_orderOf.2 fun a => ?_
  have h2 : (a : G) ^ 2 = 1 := by rw [pow_two]; exact hA a a.2
  have : orderOf (a : G) ∣ 2 ^ 1 := by simpa using orderOf_dvd_of_pow_eq_one h2
  obtain ⟨k, -, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 this
  exact ⟨k, by rw [← Subgroup.orderOf_coe]; exact hk'⟩

theorem exists_conj_mem {n : ℕ} (P : Subgroup (Perm (Fin n)))
    (hP : Nat.card P = 2 ^ (Nat.card (Perm (Fin n))).factorization 2) {B : Subgroup (Perm (Fin n))}
    (hB : IsPGroup 2 B) : ∃ σ : Perm (Fin n), ∀ b ∈ B, σ⁻¹ * b * σ ∈ P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let PS : Sylow 2 (Perm (Fin n)) := Sylow.ofCard P hP
  obtain ⟨Q, hBQ⟩ := IsPGroup.exists_le_sylow hB
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin n)) PS Q
  refine ⟨g, fun b hb => ?_⟩
  have hbQ : b ∈ (Q : Subgroup (Perm (Fin n))) := hBQ hb
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hbQ
  have h1 : (MulAut.conj g)⁻¹ • b = g⁻¹ * b * g := by
    simp [MulAut.smul_def]
  rw [h1] at hbQ
  exact hbQ

theorem gen_of_sel {n : ℕ} (hn : 3 ≤ n) (P : Subgroup (Perm (Fin n)))
    (hP : Nat.card P = 2 ^ (Nat.card (Perm (Fin n))).factorization 2)
    (Lt : List (List ℕ)) (hI : ∀ x ∈ P, x * x = 1 → tab x ∈ Lt)
    (entries : List (GenEntry n)) (hok : ∀ e ∈ entries, e.Ok) (N : ℕ)
    (hsel : ∀ T : Finset (Perm (Fin n)), (∀ x ∈ T, tab x ∈ Lt) → 1 ∈ T →
      (∀ x ∈ T, ∀ y ∈ T, x * y ∈ T ∧ x * y = y * x) → (∃ k, T.card = 2 ^ k) → T.card ≠ 1 →
      ∃ e ∈ entries, (∀ t ∈ e.T, t ∈ T) ∧ T.card ^ e.cs.length ≤ N)
    {B : Subgroup (Perm (Fin n))} (hB1 : B ≠ ⊥) (hc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (h2 : ∀ a ∈ B, a * a = 1) :
    ∃ cs : List (Perm (Fin n)), (∀ c ∈ cs, c ∈ alternatingGroup (Fin n)) ∧
      Nat.card B ^ cs.length ≤ N ∧
      alternatingGroup (Fin n) ≤ Subgroup.closure {x | ∃ c ∈ cs, ∃ b ∈ B, x = c * b * c⁻¹} := by
  classical
  have hB2 : IsPGroup 2 B := isPGroup_two_of_sq B h2
  obtain ⟨σ, hσ⟩ := exists_conj_mem P hP hB2
  set T : Finset (Perm (Fin n)) := Finset.univ.filter (fun x => σ * x * σ⁻¹ ∈ B) with hT
  have hmemT : ∀ x, x ∈ T ↔ σ * x * σ⁻¹ ∈ B := fun x => by simp [hT]
  have hsq' : ∀ b ∈ B, σ⁻¹ * b * σ * (σ⁻¹ * b * σ) = 1 := by
    intro b hb
    calc σ⁻¹ * b * σ * (σ⁻¹ * b * σ) = σ⁻¹ * (b * b) * σ := by group
      _ = 1 := by rw [h2 b hb]; group
  have hsq : ∀ x, x ∈ T → x * x = 1 := by
    intro x hx
    have h := h2 _ ((hmemT x).1 hx)
    have : σ * (x * x) * σ⁻¹ = 1 := by
      calc σ * (x * x) * σ⁻¹ = (σ * x * σ⁻¹) * (σ * x * σ⁻¹) := by group
        _ = 1 := h
    simpa using this
  have hLT : ∀ x ∈ T, tab x ∈ Lt := by
    intro x hx
    have hxP : x ∈ P := by simpa [mul_assoc] using hσ _ ((hmemT x).1 hx)
    exact hI x hxP (hsq x hx)
  have hcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    intro x hx y hy
    have h := hc _ ((hmemT x).1 hx) _ ((hmemT y).1 hy)
    have : σ * (x * y) * σ⁻¹ = σ * (y * x) * σ⁻¹ := by
      calc σ * (x * y) * σ⁻¹ = (σ * x * σ⁻¹) * (σ * y * σ⁻¹) := by group
        _ = (σ * y * σ⁻¹) * (σ * x * σ⁻¹) := h
        _ = σ * (y * x) * σ⁻¹ := by group
    simpa using this
  have hmulT : ∀ x ∈ T, ∀ y ∈ T, x * y ∈ T := by
    intro x hx y hy
    refine (hmemT _).2 ?_
    have e : σ * (x * y) * σ⁻¹ = (σ * x * σ⁻¹) * (σ * y * σ⁻¹) := by group
    rw [e]
    exact B.mul_mem ((hmemT x).1 hx) ((hmemT y).1 hy)
  have h1T : (1 : Perm (Fin n)) ∈ T := by
    refine (hmemT _).2 ?_
    simp
  have hcard : Nat.card B = T.card := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr
      { toFun := fun b => ⟨σ⁻¹ * (b : Perm (Fin n)) * σ, ?_⟩
        invFun := fun x => ⟨σ * (x : Perm (Fin n)) * σ⁻¹, (hmemT x).1 x.2⟩
        left_inv := fun b => Subtype.ext (by simp [mul_assoc])
        right_inv := fun x => Subtype.ext (by simp [mul_assoc]) }
    rw [hmemT]
    simp [mul_assoc]
  have hne : T.card ≠ 1 := by
    intro h
    obtain ⟨b, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB1
    have hbT : σ⁻¹ * (b : Perm (Fin n)) * σ ∈ T := by
      rw [hmemT]
      simp [mul_assoc]
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h
    have e1 : (1 : Perm (Fin n)) = a := by rw [ha] at h1T; simpa using h1T
    have e2 : σ⁻¹ * (b : Perm (Fin n)) * σ = a := by rw [ha] at hbT; simpa using hbT
    apply hb1
    apply Subtype.ext
    have : σ⁻¹ * (b : Perm (Fin n)) * σ = 1 := by rw [e2, ← e1]
    calc (b : Perm (Fin n)) = σ * (σ⁻¹ * (b : Perm (Fin n)) * σ) * σ⁻¹ := by group
      _ = 1 := by rw [this]; group
  have hk : ∃ k, T.card = 2 ^ k := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hB2.exists_card_eq
    exact ⟨k, by rw [← hcard]; exact hk⟩
  obtain ⟨e, he, hTe, hbound⟩ :=
    hsel T hLT h1T (fun x hx y hy => ⟨hmulT x hx y hy, hcomm x hx y hy⟩) hk hne
  have heok := hok e he
  refine ⟨e.conjugators.map fun c => σ * c * σ⁻¹, ?_, ?_, ?_⟩
  · intro c hc'
    obtain ⟨c', hc'', rfl⟩ := List.mem_map.1 hc'
    exact (alternatingGroup.normal (α := Fin n)).conj_mem _ (e.conjugators_mem heok c' hc'') σ
  · rw [List.length_map, hcard]
    unfold GenEntry.conjugators
    rw [List.length_map]
    exact hbound
  · set X : Set (Perm (Fin n)) :=
      {x | ∃ c ∈ e.conjugators.map (fun c => σ * c * σ⁻¹), ∃ b ∈ B, x = c * b * c⁻¹} with hX
    have hcl : Subgroup.closure
        {x | ∃ c ∈ e.conjugators, ∃ t ∈ e.T, x = c * t * c⁻¹} ≤
        (Subgroup.closure X).comap (MulAut.conj σ).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro _ ⟨c', hc', t, ht, rfl⟩
      show σ * (c' * t * c'⁻¹) * σ⁻¹ ∈ Subgroup.closure X
      apply Subgroup.subset_closure
      refine ⟨σ * c' * σ⁻¹, List.mem_map.2 ⟨c', hc', rfl⟩, σ * t * σ⁻¹,
        (hmemT t).1 (hTe t ht), ?_⟩
      group
    intro a ha
    have ha' : σ⁻¹ * a * σ ∈ alternatingGroup (Fin n) :=
      (alternatingGroup.normal (α := Fin n)).conj_mem _ ha σ⁻¹ |> fun h => by simpa using h
    have := hcl (e.alt_le_closure hn heok ha')
    have h3 : σ * (σ⁻¹ * a * σ) * σ⁻¹ ∈ Subgroup.closure X := this
    simpa [mul_assoc] using h3

theorem entry_single {n : ℕ} {e : GenEntry n} (he : e.Ok) {b : Perm (Fin n)}
    (h : e.Tt = [tab b]) : ∀ t ∈ e.T, t = b := by
  intro t ht
  have h1 : tab t ∈ e.T.map tab := List.mem_map.2 ⟨t, ht, rfl⟩
  rw [he.1, h] at h1
  exact tab_inj (List.mem_singleton.1 h1)

theorem entry_pair {n : ℕ} {e : GenEntry n} (he : e.Ok) {x y : Perm (Fin n)}
    (h : ∀ t ∈ e.Tt, t = tab x ∨ t = tab y ∨ t = tmul (tab x) (tab y)) :
    ∀ t ∈ e.T, t = x ∨ t = y ∨ t = x * y := by
  intro t ht
  have h1 : tab t ∈ e.T.map tab := List.mem_map.2 ⟨t, ht, rfl⟩
  rw [he.1] at h1
  rcases h _ h1 with h | h | h
  · exact Or.inl (tab_inj h)
  · exact Or.inr (Or.inl (tab_inj h))
  · exact Or.inr (Or.inr (tab_inj (by rw [tab_mul]; exact h)))

theorem exists_family {n N : ℕ} {B : Subgroup (Perm (Fin n))}
    (h : ∃ cs : List (Perm (Fin n)), (∀ c ∈ cs, c ∈ alternatingGroup (Fin n)) ∧
      Nat.card B ^ cs.length ≤ N ∧
      alternatingGroup (Fin n) ≤ Subgroup.closure {x | ∃ c ∈ cs, ∃ b ∈ B, x = c * b * c⁻¹}) :
    ∃ (r : ℕ) (f : Fin r → Perm (Fin n)), (∀ i, f i ∈ alternatingGroup (Fin n)) ∧
      Nat.card B ^ r ≤ N ∧
      alternatingGroup (Fin n) ≤ Subgroup.closure {x | ∃ i, ∃ b ∈ B, x = f i * b * (f i)⁻¹} := by
  obtain ⟨cs, hcs, hN, hcl⟩ := h
  refine ⟨cs.length, fun i => cs.get i, fun i => hcs _ (List.get_mem _ _), hN, ?_⟩
  refine hcl.trans (Subgroup.closure_mono ?_)
  rintro _ ⟨c, hc, b, hb, rfl⟩
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hc
  exact ⟨i, b, hb, rfl⟩

theorem card_le_of_tab {n : ℕ} (T : Finset (Perm (Fin n))) (Lt : List (List ℕ))
    (h : ∀ x ∈ T, tab x ∈ Lt) : T.card ≤ Lt.length := by
  classical
  calc T.card = (T.image tab).card := (Finset.card_image_of_injective _ tab_inj).symm
    _ ≤ Lt.toFinset.card := Finset.card_le_card (fun a ha => by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
        exact List.mem_toFinset.2 (h x hx))
    _ ≤ Lt.length := List.toFinset_card_le _

theorem tab_ne_range {n : ℕ} {b : Perm (Fin n)} (h : b ≠ 1) : tab b ≠ List.range n := by
  intro h'
  exact h (tab_inj (by rw [h', tab_one]))

theorem mul_ne_one_of_ne {n : ℕ} {x y : Perm (Fin n)} (hx : x * x = 1) (hxy : x ≠ y) :
    x * y ≠ 1 := by
  intro h
  apply hxy
  have h1 : x⁻¹ = y := inv_eq_of_mul_eq_one_right h
  have h2 : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  rw [← h2, h1]

def p7t : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 5, 4, 6], [0, 3, 2, 1, 4, 5, 6], [0, 3, 2, 1, 5, 4, 6], [1, 0, 3, 2, 4, 5, 6], [1, 0, 3, 2, 5, 4, 6], [1, 2, 3, 0, 4, 5, 6], [1, 2, 3, 0, 5, 4, 6], [2, 1, 0, 3, 4, 5, 6], [2, 1, 0, 3, 5, 4, 6], [2, 3, 0, 1, 4, 5, 6], [2, 3, 0, 1, 5, 4, 6], [3, 0, 1, 2, 4, 5, 6], [3, 0, 1, 2, 5, 4, 6], [3, 2, 1, 0, 4, 5, 6], [3, 2, 1, 0, 5, 4, 6]]

def p7l : List (Perm (Fin 7)) :=
  [1,
    swap 4 5,
    swap 1 3,
    swap 1 3 * swap 4 5,
    swap 0 1 * swap 2 3,
    swap 0 1 * swap 2 3 * swap 4 5,
    swap 0 1 * swap 1 2 * swap 2 3,
    swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5,
    swap 0 2,
    swap 0 2 * swap 4 5,
    swap 0 2 * swap 1 3,
    swap 0 2 * swap 1 3 * swap 4 5,
    swap 0 3 * swap 3 2 * swap 2 1,
    swap 0 3 * swap 3 2 * swap 2 1 * swap 4 5,
    swap 0 3 * swap 1 2,
    swap 0 3 * swap 1 2 * swap 4 5]

def l7t : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 5, 4, 6], [0, 3, 2, 1, 4, 5, 6], [0, 3, 2, 1, 5, 4, 6], [1, 0, 3, 2, 4, 5, 6], [1, 0, 3, 2, 5, 4, 6], [2, 1, 0, 3, 4, 5, 6], [2, 1, 0, 3, 5, 4, 6], [2, 3, 0, 1, 4, 5, 6], [2, 3, 0, 1, 5, 4, 6], [3, 2, 1, 0, 4, 5, 6], [3, 2, 1, 0, 5, 4, 6]]

def trans7t : List (List ℕ) :=
  [[0, 1, 2, 3, 5, 4, 6], [0, 3, 2, 1, 4, 5, 6], [2, 1, 0, 3, 4, 5, 6]]

def nt7t : List (List ℕ) :=
  [[0, 3, 2, 1, 5, 4, 6], [1, 0, 3, 2, 4, 5, 6], [1, 0, 3, 2, 5, 4, 6], [2, 1, 0, 3, 5, 4, 6], [2, 3, 0, 1, 4, 5, 6], [2, 3, 0, 1, 5, 4, 6], [3, 2, 1, 0, 4, 5, 6], [3, 2, 1, 0, 5, 4, 6]]

set_option maxRecDepth 100000 in
theorem p7t_mul : ∀ a ∈ p7t, ∀ b ∈ p7t, tmul a b ∈ p7t := by decide +kernel

set_option maxRecDepth 100000 in
theorem p7t_pow : ∀ a ∈ p7t, tmul (tmul (tmul a a) a) a = List.range 7 := by decide +kernel

theorem p7t_one : List.range 7 ∈ p7t := by decide

set_option maxRecDepth 100000 in
theorem p7l_tab : p7l.map tab = p7t := by decide +kernel

theorem p7t_nodup : p7t.Nodup := by decide

set_option maxRecDepth 100000 in
theorem l7t_sub : ∀ a ∈ p7t, tmul a a = List.range 7 → a ∈ l7t := by decide +kernel

def P7 : Subgroup (Perm (Fin 7)) where
  carrier := {x | tab x ∈ p7t}
  mul_mem' := fun {x y} hx hy => by
    show tab (x * y) ∈ p7t
    rw [tab_mul]
    exact p7t_mul _ hx _ hy
  one_mem' := by
    show tab (1 : Perm (Fin 7)) ∈ p7t
    rw [tab_one]
    exact p7t_one
  inv_mem' := fun {x} hx => by
    have hx' : tab x ∈ p7t := hx
    have h4 : x * x * x * x = 1 := by
      apply tab_inj
      rw [tab_mul, tab_mul, tab_mul, tab_one]
      exact p7t_pow _ hx'
    have hinv : x⁻¹ = x * x * x := inv_eq_of_mul_eq_one_right (by rw [← h4]; group)
    show tab x⁻¹ ∈ p7t
    rw [hinv, tab_mul, tab_mul]
    exact p7t_mul _ (p7t_mul _ hx' _ hx') _ hx'

theorem mem_P7 {x : Perm (Fin 7)} : x ∈ P7 ↔ tab x ∈ p7t := Iff.rfl

theorem card_P7 : Nat.card P7 = 2 ^ (Nat.card (Perm (Fin 7))).factorization 2 := by
  have hnd : p7l.Nodup := List.Nodup.of_map tab (by rw [p7l_tab]; exact p7t_nodup)
  have hset : (P7 : Set (Perm (Fin 7))) = ↑p7l.toFinset := by
    ext x
    simp only [SetLike.mem_coe, mem_P7, List.mem_toFinset]
    rw [← p7l_tab]
    constructor
    · intro h
      obtain ⟨y, hy, hyx⟩ := List.mem_map.1 h
      rw [← tab_inj hyx]
      exact hy
    · intro h
      exact List.mem_map.2 ⟨x, h, rfl⟩
  have h1 : Nat.card P7 = p7l.toFinset.card := by
    have h := congrArg Set.ncard hset
    rw [Set.ncard_coe_finset] at h
    rw [← h, ← Nat.card_coe_set_eq]
    rfl
  have h2 : Nat.card (Perm (Fin 7)) = 5040 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]; simp [Nat.factorial]
  have h3 : (5040 : ℕ).factorization 2 = 4 := by
    rw [Nat.factorization_def _ Nat.prime_two]
    decide +kernel
  have h4 : p7l.length = 16 := by decide
  rw [h1, List.toFinset_card_of_nodup hnd, h4, h2, h3]
  norm_num

set_option maxRecDepth 100000 in
theorem d1_7 : ∀ a ∈ l7t, a ≠ List.range 7 → ∃ e ∈ table7, e.Tt = [a] ∧ e.cs.length ≤ 6 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem dC_7 : ∀ a ∈ nt7t, ∃ e ∈ table7, e.Tt = [a] ∧ e.cs.length ≤ 3 := by decide +kernel

set_option maxRecDepth 100000 in
theorem dA_7 : ∀ a ∈ l7t, a ≠ List.range 7 → a ∈ trans7t ∨ a ∈ nt7t := by decide +kernel

set_option maxRecDepth 100000 in
theorem dB_7 : ∀ a ∈ trans7t, ∀ b ∈ trans7t, a ≠ b → tmul a b ∉ trans7t := by decide +kernel

set_option maxRecDepth 100000 in
theorem dD_7 : ∀ a ∈ nt7t, ∀ b ∈ nt7t, a ≠ b → tmul a b = tmul b a →
    ∃ e ∈ pairs7, (∀ t ∈ e.Tt, t = a ∨ t = b ∨ t = tmul a b) ∧ e.cs.length ≤ 2 := by decide +kernel

theorem trans7t_len : trans7t.length = 3 := by decide

theorem l7t_len : l7t.length = 12 := by decide

def entries7 : List (GenEntry 7) := table7 ++ pairs7

theorem entries7_ok : ∀ e ∈ entries7, e.Ok := by
  intro e he
  rcases List.mem_append.1 he with h | h
  · exact table7_ok e h
  · exact pairs7_ok e h

set_option maxRecDepth 100000 in
theorem l7t_sq : ∀ a ∈ l7t, tmul a a = List.range 7 := by decide +kernel

theorem hsel7 : ∀ T : Finset (Perm (Fin 7)), (∀ x ∈ T, tab x ∈ l7t) → 1 ∈ T →
    (∀ x ∈ T, ∀ y ∈ T, x * y ∈ T ∧ x * y = y * x) → (∃ k, T.card = 2 ^ k) → T.card ≠ 1 →
    ∃ e ∈ entries7, (∀ t ∈ e.T, t ∈ T) ∧ T.card ^ e.cs.length ≤ 2 ^ 6 := by
  classical
  intro T hL h1 hcl hk hne
  have hsq : ∀ x ∈ T, x * x = 1 := by
    intro x hx
    apply tab_inj
    rw [tab_mul, tab_one]
    exact l7t_sq _ (hL x hx)
  obtain ⟨k, hk⟩ := hk
  have hle : T.card ≤ 12 := (card_le_of_tab T l7t hL).trans (by rw [l7t_len])
  have hk3 : k ≤ 3 := by
    by_contra h
    push Not at h
    have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
    omega
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne (by simpa using hk)
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
  interval_cases k
  ·
    have hcard : T.card = 2 := by simpa using hk
    obtain ⟨b, hbT, hb1⟩ := Finset.exists_mem_ne (by omega : 1 < T.card) 1
    obtain ⟨e, he, hTt, hlen⟩ := d1_7 (tab b) (hL b hbT) (tab_ne_range hb1)
    refine ⟨e, List.mem_append_left _ he, ?_, ?_⟩
    · intro t ht
      rw [entry_single (table7_ok e he) hTt t ht]
      exact hbT
    · rw [hcard]
      exact Nat.pow_le_pow_right (by norm_num) hlen
  ·
    have hcard : T.card = 4 := by simpa using hk
    have h3 : 1 < (T.erase 1).card := by rw [Finset.card_erase_of_mem h1]; omega
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 h3
    have hxT : x ∈ T := Finset.mem_of_mem_erase hx
    have hyT : y ∈ T := Finset.mem_of_mem_erase hy
    have hx1 : x ≠ 1 := Finset.ne_of_mem_erase hx
    have hy1 : y ≠ 1 := Finset.ne_of_mem_erase hy
    have hz : ∃ z ∈ T, tab z ∈ nt7t := by
      rcases dA_7 (tab x) (hL x hxT) (tab_ne_range hx1) with hx_t | hx_n
      · rcases dA_7 (tab y) (hL y hyT) (tab_ne_range hy1) with hy_t | hy_n
        · have hxy' : x * y ∈ T := (hcl x hxT y hyT).1
          have hne1 : x * y ≠ 1 := mul_ne_one_of_ne (hsq x hxT) hxy
          have hnt : tab (x * y) ∉ trans7t := by
            rw [tab_mul]
            exact dB_7 _ hx_t _ hy_t (fun h => hxy (tab_inj h))
          exact ⟨x * y, hxy', (dA_7 _ (hL _ hxy') (tab_ne_range hne1)).resolve_left hnt⟩
        · exact ⟨y, hyT, hy_n⟩
      · exact ⟨x, hxT, hx_n⟩
    obtain ⟨z, hzT, hzn⟩ := hz
    obtain ⟨e, he, hTt, hlen⟩ := dC_7 (tab z) hzn
    refine ⟨e, List.mem_append_left _ he, ?_, ?_⟩
    · intro t ht
      rw [entry_single (table7_ok e he) hTt t ht]
      exact hzT
    · rw [hcard]
      calc 4 ^ e.cs.length ≤ 4 ^ 3 := Nat.pow_le_pow_right (by norm_num) hlen
        _ = 2 ^ 6 := by norm_num
  ·
    have hcard : T.card = 8 := by simpa using hk
    have hTc : (T.erase 1).card = 7 := by rw [Finset.card_erase_of_mem h1]; omega
    set S := (T.erase 1).filter (fun x => tab x ∈ nt7t) with hS
    set R := (T.erase 1).filter (fun x => ¬ tab x ∈ nt7t) with hR
    have hSR := Finset.card_filter_add_card_filter_not (s := T.erase 1) (fun x => tab x ∈ nt7t)
    rw [← hS, ← hR] at hSR
    have hRc : R.card ≤ 3 := by
      have h5 : R.card ≤ trans7t.toFinset.card := by
        refine Finset.card_le_card_of_injOn tab (fun x hx => ?_) (fun x _ y _ h => tab_inj h)
        rw [hR, Finset.coe_filter] at hx
        obtain ⟨hx1, hxn⟩ := hx
        have hxT : x ∈ T := Finset.mem_of_mem_erase hx1
        have hxne : x ≠ 1 := Finset.ne_of_mem_erase hx1
        have := (dA_7 (tab x) (hL x hxT) (tab_ne_range hxne)).resolve_right hxn
        simpa using this
      exact h5.trans ((List.toFinset_card_le _).trans (by rw [trans7t_len]))
    have hS2 : 1 < S.card := by omega
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 hS2
    rw [hS, Finset.mem_filter] at hx hy
    have hxT : x ∈ T := Finset.mem_of_mem_erase hx.1
    have hyT : y ∈ T := Finset.mem_of_mem_erase hy.1
    obtain ⟨e, he, hTt, hlen⟩ := dD_7 (tab x) hx.2 (tab y) hy.2 (fun h => hxy (tab_inj h))
      (by rw [← tab_mul, ← tab_mul, (hcl x hxT y hyT).2])
    refine ⟨e, List.mem_append_right _ he, ?_, ?_⟩
    · intro t ht
      rcases entry_pair (pairs7_ok e he) hTt t ht with rfl | rfl | rfl
      · exact hxT
      · exact hyT
      · exact (hcl x hxT y hyT).1
    · rw [hcard]
      calc 8 ^ e.cs.length ≤ 8 ^ 2 := Nat.pow_le_pow_right (by norm_num) hlen
        _ = 2 ^ 6 := by norm_num

theorem gen7 {B : Subgroup (Perm (Fin 7))} (hB1 : B ≠ ⊥) (hc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (h2 : ∀ a ∈ B, a * a = 1) :
    ∃ (r : ℕ) (f : Fin r → Perm (Fin 7)), (∀ i, f i ∈ alternatingGroup (Fin 7)) ∧
      Nat.card B ^ r ≤ 2 ^ 6 ∧
      alternatingGroup (Fin 7) ≤ Subgroup.closure {x | ∃ i, ∃ b ∈ B, x = f i * b * (f i)⁻¹} :=
  exists_family (gen_of_sel (by norm_num) P7 card_P7 l7t
    (fun x hx hx2 => by
      have hx' : tab x ∈ p7t := hx
      apply l7t_sub _ hx'
      rw [← tab_mul, hx2, tab_one]) entries7 entries7_ok (2 ^ 6) hsel7 hB1 hc h2)

def p5t : List (List ℕ) :=
  [[0, 1, 2, 3, 4], [0, 3, 2, 1, 4], [1, 0, 3, 2, 4], [1, 2, 3, 0, 4], [2, 1, 0, 3, 4], [2, 3, 0, 1, 4], [3, 0, 1, 2, 4], [3, 2, 1, 0, 4]]

def p5l : List (Perm (Fin 5)) :=
  [1,
    swap 1 3,
    swap 0 1 * swap 2 3,
    swap 0 1 * swap 1 2 * swap 2 3,
    swap 0 2,
    swap 0 2 * swap 1 3,
    swap 0 3 * swap 3 2 * swap 2 1,
    swap 0 3 * swap 1 2]

def l5t : List (List ℕ) :=
  [[0, 1, 2, 3, 4], [0, 3, 2, 1, 4], [1, 0, 3, 2, 4], [2, 1, 0, 3, 4], [2, 3, 0, 1, 4], [3, 2, 1, 0, 4]]

set_option maxRecDepth 100000 in
theorem p5t_mul : ∀ a ∈ p5t, ∀ b ∈ p5t, tmul a b ∈ p5t := by decide +kernel

set_option maxRecDepth 100000 in
theorem p5t_pow : ∀ a ∈ p5t, tmul (tmul (tmul a a) a) a = List.range 5 := by decide +kernel

theorem p5t_one : List.range 5 ∈ p5t := by decide

set_option maxRecDepth 100000 in
theorem p5l_tab : p5l.map tab = p5t := by decide +kernel

theorem p5t_nodup : p5t.Nodup := by decide

set_option maxRecDepth 100000 in
theorem l5t_sub : ∀ a ∈ p5t, tmul a a = List.range 5 → a ∈ l5t := by decide +kernel

def P5 : Subgroup (Perm (Fin 5)) where
  carrier := {x | tab x ∈ p5t}
  mul_mem' := fun {x y} hx hy => by
    show tab (x * y) ∈ p5t
    rw [tab_mul]
    exact p5t_mul _ hx _ hy
  one_mem' := by
    show tab (1 : Perm (Fin 5)) ∈ p5t
    rw [tab_one]
    exact p5t_one
  inv_mem' := fun {x} hx => by
    have hx' : tab x ∈ p5t := hx
    have h4 : x * x * x * x = 1 := by
      apply tab_inj
      rw [tab_mul, tab_mul, tab_mul, tab_one]
      exact p5t_pow _ hx'
    have hinv : x⁻¹ = x * x * x := inv_eq_of_mul_eq_one_right (by rw [← h4]; group)
    show tab x⁻¹ ∈ p5t
    rw [hinv, tab_mul, tab_mul]
    exact p5t_mul _ (p5t_mul _ hx' _ hx') _ hx'

theorem mem_P5 {x : Perm (Fin 5)} : x ∈ P5 ↔ tab x ∈ p5t := Iff.rfl

theorem card_P5 : Nat.card P5 = 2 ^ (Nat.card (Perm (Fin 5))).factorization 2 := by
  have hnd : p5l.Nodup := List.Nodup.of_map tab (by rw [p5l_tab]; exact p5t_nodup)
  have hset : (P5 : Set (Perm (Fin 5))) = ↑p5l.toFinset := by
    ext x
    simp only [SetLike.mem_coe, mem_P5, List.mem_toFinset]
    rw [← p5l_tab]
    constructor
    · intro h
      obtain ⟨y, hy, hyx⟩ := List.mem_map.1 h
      rw [← tab_inj hyx]
      exact hy
    · intro h
      exact List.mem_map.2 ⟨x, h, rfl⟩
  have h1 : Nat.card P5 = p5l.toFinset.card := by
    have h := congrArg Set.ncard hset
    rw [Set.ncard_coe_finset] at h
    rw [← h, ← Nat.card_coe_set_eq]
    rfl
  have h2 : Nat.card (Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]; simp [Nat.factorial]
  have h3 : (120 : ℕ).factorization 2 = 3 := by
    rw [Nat.factorization_def _ Nat.prime_two]
    decide +kernel
  have h4 : p5l.length = 8 := by decide
  rw [h1, List.toFinset_card_of_nodup hnd, h4, h2, h3]
  norm_num

set_option maxRecDepth 100000 in
theorem d1_5 : ∀ a ∈ l5t, a ≠ List.range 5 → ∃ e ∈ table5, e.Tt = [a] ∧ e.cs.length ≤ 4 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem dP_5 : ∀ a ∈ l5t, ∀ b ∈ l5t, a ≠ List.range 5 → b ≠ List.range 5 → a ≠ b →
    tmul a b = tmul b a → ∃ e ∈ pairs5, (∀ t ∈ e.Tt, t = a ∨ t = b ∨ t = tmul a b) ∧
      e.cs.length ≤ 2 := by decide +kernel

theorem l5t_len : l5t.length = 6 := by decide

def entries5 : List (GenEntry 5) := table5 ++ pairs5

theorem entries5_ok : ∀ e ∈ entries5, e.Ok := by
  intro e he
  rcases List.mem_append.1 he with h | h
  · exact table5_ok e h
  · exact pairs5_ok e h

theorem hsel5 : ∀ T : Finset (Perm (Fin 5)), (∀ x ∈ T, tab x ∈ l5t) → 1 ∈ T →
    (∀ x ∈ T, ∀ y ∈ T, x * y ∈ T ∧ x * y = y * x) → (∃ k, T.card = 2 ^ k) → T.card ≠ 1 →
    ∃ e ∈ entries5, (∀ t ∈ e.T, t ∈ T) ∧ T.card ^ e.cs.length ≤ 2 ^ 4 := by
  classical
  intro T hL h1 hcl hk hne
  obtain ⟨k, hk⟩ := hk
  have hle : T.card ≤ 6 := (card_le_of_tab T l5t hL).trans (by rw [l5t_len])
  have hk2 : k ≤ 2 := by
    by_contra h
    push Not at h
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
    omega
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne (by simpa using hk)
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
  interval_cases k
  ·
    have hcard : T.card = 2 := by simpa using hk
    obtain ⟨b, hbT, hb1⟩ := Finset.exists_mem_ne (by omega : 1 < T.card) 1
    obtain ⟨e, he, hTt, hlen⟩ := d1_5 (tab b) (hL b hbT) (tab_ne_range hb1)
    refine ⟨e, List.mem_append_left _ he, ?_, ?_⟩
    · intro t ht
      rw [entry_single (table5_ok e he) hTt t ht]
      exact hbT
    · rw [hcard]
      exact Nat.pow_le_pow_right (by norm_num) hlen
  ·
    have hcard : T.card = 4 := by simpa using hk
    have h3 : 1 < (T.erase 1).card := by rw [Finset.card_erase_of_mem h1]; omega
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 h3
    have hxT : x ∈ T := Finset.mem_of_mem_erase hx
    have hyT : y ∈ T := Finset.mem_of_mem_erase hy
    have hx1 : x ≠ 1 := Finset.ne_of_mem_erase hx
    have hy1 : y ≠ 1 := Finset.ne_of_mem_erase hy
    obtain ⟨e, he, hTt, hlen⟩ := dP_5 (tab x) (hL x hxT) (tab y) (hL y hyT) (tab_ne_range hx1)
      (tab_ne_range hy1) (fun h => hxy (tab_inj h))
      (by rw [← tab_mul, ← tab_mul, (hcl x hxT y hyT).2])
    refine ⟨e, List.mem_append_right _ he, ?_, ?_⟩
    · intro t ht
      rcases entry_pair (pairs5_ok e he) hTt t ht with rfl | rfl | rfl
      · exact hxT
      · exact hyT
      · exact (hcl x hxT y hyT).1
    · rw [hcard]
      calc 4 ^ e.cs.length ≤ 4 ^ 2 := Nat.pow_le_pow_right (by norm_num) hlen
        _ = 2 ^ 4 := by norm_num

theorem gen5 {B : Subgroup (Perm (Fin 5))} (hB1 : B ≠ ⊥) (hc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (h2 : ∀ a ∈ B, a * a = 1) :
    ∃ (r : ℕ) (f : Fin r → Perm (Fin 5)), (∀ i, f i ∈ alternatingGroup (Fin 5)) ∧
      Nat.card B ^ r ≤ 2 ^ 4 ∧
      alternatingGroup (Fin 5) ≤ Subgroup.closure {x | ∃ i, ∃ b ∈ B, x = f i * b * (f i)⁻¹} :=
  exists_family (gen_of_sel (by norm_num) P5 card_P5 l5t
    (fun x hx hx2 => by
      have hx' : tab x ∈ p5t := hx
      apply l5t_sub _ hx'
      rw [← tab_mul, hx2, tab_one]) entries5 entries5_ok (2 ^ 4) hsel5 hB1 hc h2)

end CFSG.QuasithinUnique.B42A57
