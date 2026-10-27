module

public import Certificates.Data.E27Table
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.HardMathSupport.Foote.E27

open Subgroup

variable {G : Type*} [Group G]

@[expose] def tabElt (g : ℕ → G) (par : Array (ℕ × ℕ)) (i : ℕ) : G :=
  if _h : (par[i]!).1 < i then g (par[i]!).2 * tabElt g par (par[i]!).1 else 1
termination_by i
decreasing_by exact _h

theorem tabElt_zero (g : ℕ → G) (par : Array (ℕ × ℕ)) : tabElt g par 0 = 1 := by
  rw [tabElt]; simp

theorem tabElt_succ (g : ℕ → G) (par : Array (ℕ × ℕ)) {i : ℕ} (h : (par[i]!).1 < i) :
    tabElt g par i = g (par[i]!).2 * tabElt g par (par[i]!).1 := by
  rw [tabElt]; simp [h]

theorem tabMul_zero (par : Array (ℕ × ℕ)) (L : Array (Array ℕ)) (b : ℕ) :
    tabMul par L 0 b = b := by
  rw [tabMul]; simp

theorem tabMul_succ (par : Array (ℕ × ℕ)) (L : Array (Array ℕ)) {a : ℕ} (b : ℕ)
    (h : (par[a]!).1 < a) :
    tabMul par L a b = (L[(par[a]!).2]!)[tabMul par L (par[a]!).1 b]! := by
  rw [tabMul]; simp [h]

structure TabData (g : ℕ → G) (par : Array (ℕ × ℕ)) (L : Array (Array ℕ)) (n m : ℕ) : Prop where
  par_lt : ∀ i, 0 < i → i < n → (par[i]!).1 < i ∧ (par[i]!).2 < m
  left : ∀ j < m, ∀ i < n, (L[j]!)[i]! < n ∧ g j * tabElt g par i = tabElt g par (L[j]!)[i]!
  inj : ∀ i < n, ∀ k < n, tabElt g par i = tabElt g par k → i = k

variable {g : ℕ → G} {par : Array (ℕ × ℕ)} {L : Array (Array ℕ)} {n m : ℕ}

theorem TabData.mul (h : TabData g par L n m) :
    ∀ a < n, ∀ b < n, tabMul par L a b < n ∧
      tabElt g par a * tabElt g par b = tabElt g par (tabMul par L a b) := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro ha b hb
    by_cases h0 : a = 0
    · subst h0
      rw [tabMul_zero, tabElt_zero, one_mul]
      exact ⟨hb, rfl⟩
    · obtain ⟨hp, hj⟩ := h.par_lt a (Nat.pos_of_ne_zero h0) ha
      obtain ⟨hlt, heq⟩ := ih _ hp (by omega) b hb
      obtain ⟨hL1, hL2⟩ := h.left _ hj _ hlt
      rw [tabMul_succ par L b hp, tabElt_succ g par hp, mul_assoc, heq]
      exact ⟨hL1, hL2⟩

theorem TabData.exists_subgroup [Finite G] (h : TabData g par L n m) (hn : 0 < n) :
    ∃ T : Subgroup G, (∀ x, x ∈ T ↔ ∃ i < n, tabElt g par i = x) ∧
      T = Subgroup.closure (Set.range fun j : Fin m => g j) := by
  let X : Set G := {x | ∃ i < n, tabElt g par i = x}
  have hmulX : ∀ x ∈ X, ∀ y ∈ X, x * y ∈ X := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨h1, h2⟩ := h.mul a ha b hb
    exact ⟨_, h1, h2.symm⟩
  have hone : (1 : G) ∈ X := ⟨0, hn, tabElt_zero g par⟩
  have hpowX : ∀ x ∈ X, ∀ k : ℕ, x ^ k ∈ X := by
    intro x hx k
    induction k with
    | zero => simpa using hone
    | succ k ih => rw [pow_succ]; exact hmulX _ ih _ hx
  let S : Subgroup G :=
    { carrier := X
      mul_mem' := fun {x y} hx hy => hmulX x hx y hy
      one_mem' := hone
      inv_mem' := fun {x} hx => by
        have hpos : 0 < orderOf x := orderOf_pos x
        have : x⁻¹ = x ^ (orderOf x - 1) := by
          rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
        rw [this]
        exact hpowX x hx _ }
  refine ⟨S, fun x => Iff.rfl, le_antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := hx
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      by_cases h0 : i = 0
      · subst h0; rw [tabElt_zero]; exact one_mem _
      · obtain ⟨hp, hj⟩ := h.par_lt i (Nat.pos_of_ne_zero h0) hi
        rw [tabElt_succ g par hp]
        refine mul_mem (subset_closure ⟨⟨_, hj⟩, rfl⟩) (ih _ hp (by omega))
  · rw [Subgroup.closure_le]
    rintro _ ⟨⟨j, hj⟩, rfl⟩
    obtain ⟨hlt, heq⟩ := h.left j hj 0 hn
    rw [tabElt_zero, mul_one] at heq
    exact ⟨_, hlt, heq.symm⟩

theorem TabData.card_inf_centralizer (h : TabData g par L n m) {T : Subgroup G}
    (hT : ∀ x, x ∈ T ↔ ∃ i < n, tabElt g par i = x) {a : ℕ} (ha : a < n) :
    Nat.card ↥(T ⊓ centralizer ({tabElt g par a} : Set G)) = tabComm par L n a := by
  set s := (Finset.range n).filter fun b => tabMul par L a b = tabMul par L b a with hs
  have hmem : ∀ b : {b // b ∈ s}, tabElt g par b.1 ∈ T ⊓ centralizer ({tabElt g par a} : Set G) := by
    intro b
    have hb := Finset.mem_filter.mp b.2
    have hbn := Finset.mem_range.mp hb.1
    refine ⟨(hT _).2 ⟨b.1, hbn, rfl⟩, ?_⟩
    refine mem_centralizer_singleton_iff.mpr ?_
    obtain ⟨-, h1⟩ := h.mul b.1 hbn a ha
    obtain ⟨-, h2⟩ := h.mul a ha b.1 hbn
    rw [h1, h2, hb.2]
  have hbij : Function.Bijective fun b : {b // b ∈ s} =>
      (⟨tabElt g par b.1, hmem b⟩ : ↥(T ⊓ centralizer ({tabElt g par a} : Set G))) := by
    constructor
    · intro b1 b2 e
      have := congrArg Subtype.val e
      exact Subtype.ext (h.inj _ (Finset.mem_range.mp (Finset.mem_filter.mp b1.2).1) _
        (Finset.mem_range.mp (Finset.mem_filter.mp b2.2).1) this)
    · rintro ⟨x, hxT, hxC⟩
      obtain ⟨b, hbn, rfl⟩ := (hT x).1 hxT
      have hxC' := mem_centralizer_singleton_iff.mp hxC
      obtain ⟨hlt1, h1⟩ := h.mul b hbn a ha
      obtain ⟨hlt2, h2⟩ := h.mul a ha b hbn
      refine ⟨⟨b, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hbn, ?_⟩⟩, rfl⟩
      rw [h1, h2] at hxC'
      exact (h.inj _ hlt2 _ hlt1 hxC'.symm)
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_coe]
  unfold tabComm
  rw [List.countP_eq_length_filter, hs]
  simp only [Finset.card, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
    Multiset.coe_card]
  congr 1

theorem TabData.card_subgroup (h : TabData g par L n m) {T : Subgroup G}
    (hT : ∀ x, x ∈ T ↔ ∃ i < n, tabElt g par i = x) : Nat.card T = n := by
  have hbij : Function.Bijective fun i : Fin n =>
      (⟨tabElt g par i, (hT _).2 ⟨i, i.isLt, rfl⟩⟩ : T) := by
    constructor
    · intro i1 i2 e
      exact Fin.ext (h.inj _ i1.isLt _ i2.isLt (congrArg Subtype.val e))
    · rintro ⟨x, hx⟩
      obtain ⟨i, hi, rfl⟩ := (hT x).1 hx
      exact ⟨⟨i, hi⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem TabData.sylow_kill [Finite G] (h : TabData g par L n m) {T : Subgroup G}
    (hT : ∀ x, x ∈ T ↔ ∃ i < n, tabElt g par i = x)
    (hn : n = 3 ^ (Nat.card G).factorization 3)
    (hcheck : ∀ a < n, a ≠ 0 → tabMul par L a (tabMul par L a a) = 0 → 81 ≤ tabComm par L n a) :
    Nat.card T = 3 ^ (Nat.card G).factorization 3 ∧
      ∀ s ∈ T, orderOf s = 3 → 81 ∣ Nat.card ↥(T ⊓ centralizer ({s} : Set G)) := by
  have hcT := h.card_subgroup hT
  refine ⟨hcT.trans hn, fun s hs hs3 => ?_⟩
  obtain ⟨a, ha, rfl⟩ := (hT s).1 hs
  have hs1 : tabElt g par a ≠ 1 := by
    intro h1
    rw [h1] at hs3
    simp at hs3
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hs1 (tabElt_zero g par)
  have hcube : tabMul par L a (tabMul par L a a) = 0 := by
    obtain ⟨hl1, e1⟩ := h.mul a ha a ha
    obtain ⟨hl2, e2⟩ := h.mul a ha _ hl1
    have hpow : tabElt g par a ^ 3 = 1 := by rw [← hs3]; exact pow_orderOf_eq_one _
    have : tabElt g par (tabMul par L a (tabMul par L a a)) = tabElt g par 0 := by
      rw [tabElt_zero, ← e2, ← e1, ← hpow, pow_three', mul_assoc]
    exact h.inj _ hl2 0 (by omega) this
  have h81 := hcheck a ha ha0 hcube
  rw [← h.card_inf_centralizer hT ha] at h81
  have hdvd : Nat.card ↥(T ⊓ centralizer ({tabElt g par a} : Set G)) ∣ 3 ^ (Nat.card G).factorization 3 := by
    rw [← hcT.trans hn]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  rw [hkeq] at h81 ⊢
  have : 4 ≤ k := by
    by_contra hlt
    have : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨j, rfl⟩ : ∃ j, k = 4 + j := ⟨k - 4, by omega⟩
  exact ⟨3 ^ j, by rw [pow_add]; norm_num⟩

end CFSG.HardMathSupport.Foote.E27
