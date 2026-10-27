module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.QuasithinUnique

namespace L246C127

namespace C127Block

private theorem perm_inv_apply_self {α : Type*} (f : Equiv.Perm α) (x : α) : f⁻¹ (f x) = x :=
  Equiv.symm_apply_apply f x

private theorem perm_apply_inv_self {α : Type*} (f : Equiv.Perm α) (x : α) : f (f⁻¹ x) = x :=
  Equiv.apply_symm_apply f x

theorem perm_commutes_all_eq_one {n : ℕ} (hn : 3 ≤ n) (g : Equiv.Perm (Fin n))
    (hg : ∀ σ : Equiv.Perm (Fin n), g * σ = σ * g) : g = 1 := by
  have hconj : ∀ p q : Fin n, Equiv.swap (g p) (g q) = Equiv.swap p q := by
    intro p q
    rw [Equiv.swap_apply_apply, hg (Equiv.swap p q), mul_inv_cancel_right]
  have hfix : ∀ i : Fin n, g i = i := by
    intro i
    obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.1 (show 1 < (Finset.univ.erase i).card by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      omega)
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    have h1 := hconj i j
    have h2 := hconj i k
    by_contra hx
    by_cases hgj : g i = j
    · rw [hgj] at h2
      have h3 := congrArg (fun p : Equiv.Perm (Fin n) => p j) h2
      simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hji hjk] at h3
      exact hki (g.injective (h3.trans hgj.symm))
    · have h3 := congrArg (fun p : Equiv.Perm (Fin n) => p (g i)) h1
      simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hx hgj] at h3
      exact hji (g.injective h3)
  refine Equiv.ext fun i => ?_
  simpa using hfix i

theorem perm_map_stab_inner {n : ℕ} (hn : 3 ≤ n) (a : Fin n)
    (φ : Equiv.Perm (Fin n) → Equiv.Perm (Fin n))
    (hmul : ∀ σ τ : Equiv.Perm (Fin n), φ (σ * τ) = φ σ * φ τ)
    (h0 : ∀ σ : Equiv.Perm (Fin n), φ σ a = a ↔ σ a = a) :
    ∃ f : Equiv.Perm (Fin n), ∀ σ : Equiv.Perm (Fin n), φ σ = f * σ * f⁻¹ := by
  have hφ1 : φ 1 = 1 := by
    have h := hmul 1 1
    rw [mul_one] at h
    have h' : φ 1 * φ 1 = φ 1 * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel h'
  have hinv : ∀ σ : Equiv.Perm (Fin n), φ σ⁻¹ = (φ σ)⁻¹ := by
    intro σ
    have h : φ σ * φ σ⁻¹ = 1 := by rw [← hmul, mul_inv_cancel, hφ1]
    exact (inv_eq_of_mul_eq_one_right h).symm
  obtain ⟨F, hF⟩ : ∃ F : Fin n → Fin n, ∀ p, F p = φ (Equiv.swap a p) a :=
    ⟨fun p => φ (Equiv.swap a p) a, fun p => rfl⟩
  have hinj : Function.Injective F := by
    intro p q hpq
    rw [hF, hF] at hpq
    have hσ : φ ((Equiv.swap a q)⁻¹ * Equiv.swap a p) a = a := by
      rw [hmul, hinv, Equiv.Perm.mul_apply, hpq, perm_inv_apply_self]
    have h2 : ((Equiv.swap a q)⁻¹ * Equiv.swap a p) a = a := (h0 _).mp hσ
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left] at h2
    have h3 : Equiv.swap a q ((Equiv.swap a q)⁻¹ p) = p := perm_apply_inv_self _ _
    rw [h2, Equiv.swap_apply_left] at h3
    exact h3.symm
  have hbij : Function.Bijective F := Finite.injective_iff_bijective.mp hinj
  have hkey : ∀ (σ : Equiv.Perm (Fin n)) (p : Fin n), φ σ (F p) = F (σ p) := by
    intro σ p
    rw [hF, hF]
    have hτ : ((Equiv.swap a (σ p))⁻¹ * (σ * Equiv.swap a p)) a = a := by
      have hs : Equiv.swap a (σ p) a = σ p := Equiv.swap_apply_left a (σ p)
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
      calc (Equiv.swap a (σ p))⁻¹ (σ p) = (Equiv.swap a (σ p))⁻¹ (Equiv.swap a (σ p) a) := by
            rw [hs]
        _ = a := perm_inv_apply_self _ _
    have hτa : φ ((Equiv.swap a (σ p))⁻¹ * (σ * Equiv.swap a p)) a = a := (h0 _).mpr hτ
    rw [hmul, hinv, Equiv.Perm.mul_apply] at hτa
    calc φ σ (φ (Equiv.swap a p) a) = φ (σ * Equiv.swap a p) a := by
          rw [hmul, Equiv.Perm.mul_apply]
      _ = φ (Equiv.swap a (σ p)) ((φ (Equiv.swap a (σ p)))⁻¹ (φ (σ * Equiv.swap a p) a)) :=
          (perm_apply_inv_self _ _).symm
      _ = φ (Equiv.swap a (σ p)) a := by rw [hτa]
  refine ⟨Equiv.ofBijective F hbij, fun σ => ?_⟩
  refine Equiv.ext fun x => ?_
  obtain ⟨p, rfl⟩ := hbij.2 x
  have hinvF : (Equiv.ofBijective F hbij)⁻¹ (F p) = p :=
    perm_inv_apply_self (Equiv.ofBijective F hbij) p
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hinvF]
  exact hkey σ p

theorem perm_two_subgroup_dichotomy {n : ℕ} (hodd : Odd n) (h5 : 5 ≤ n)
    (S : Subgroup (Equiv.Perm (Fin n))) (hS : IsPGroup 2 S) :
    (∃ O : Finset (Fin n), (∀ s ∈ S, ∀ x ∈ O, s x ∈ O) ∧ 2 ≤ O.card ∧ O.card + 2 ≤ n) ∨
      ∃ j : ℕ, n = 2 ^ j + 1 := by
  classical
  have hcong : Nat.card (Fin n) ≡ Nat.card (MulAction.fixedPoints S (Fin n)) [MOD 2] :=
    hS.card_modEq_card_fixedPoints (Fin n)
  have hn : Nat.card (Fin n) = n := by simp
  rw [hn] at hcong
  have hc_odd : Nat.card (MulAction.fixedPoints S (Fin n)) % 2 = 1 := by
    unfold Nat.ModEq at hcong
    rw [← hcong]
    exact Nat.odd_iff.1 hodd
  have hfixS : ∀ y : Fin n, (∀ g : S, g • y = y) → ∀ s ∈ S, s y = y :=
    fun y hy s hs => hy ⟨s, hs⟩
  rcases (show Nat.card (MulAction.fixedPoints S (Fin n)) = 1 ∨
      2 ≤ Nat.card (MulAction.fixedPoints S (Fin n)) by omega) with hc1 | hc2
  ·
    obtain ⟨ω, hωfix, huniq⟩ : ∃ ω : Fin n, (∀ g : S, g • ω = ω) ∧
        ∀ y : Fin n, (∀ g : S, g • y = y) → y = ω := by
      obtain ⟨ω0, hω0⟩ := Nat.card_eq_one_iff_exists.1 hc1
      exact ⟨ω0.1, MulAction.mem_fixedPoints.1 ω0.2, fun y hy =>
        congrArg Subtype.val (hω0 ⟨y, MulAction.mem_fixedPoints.2 hy⟩)⟩
    obtain ⟨x, hxω⟩ : ∃ x : Fin n, x ≠ ω :=
      Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) ω
    obtain ⟨O, hO⟩ : ∃ O : Finset (Fin n), ∀ y, y ∈ O ↔ ∃ g : S, g • x = y :=
      ⟨Finset.univ.filter (fun y => ∃ g : S, g • x = y), fun y => by simp⟩
    have hinv : ∀ s ∈ S, ∀ y ∈ O, s y ∈ O := by
      intro s hs y hy
      obtain ⟨g, rfl⟩ := (hO y).1 hy
      refine (hO _).2 ⟨⟨s, hs⟩ * g, ?_⟩
      exact mul_smul _ _ _
    obtain ⟨m, hm⟩ := hS.card_orbit x
    have hOset : (O : Set (Fin n)) = MulAction.orbit S x := by
      ext y
      rw [Finset.mem_coe, hO, MulAction.mem_orbit_iff]
    have hOcard : O.card = 2 ^ m := by
      rw [← hm, ← hOset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
    have hxO : x ∈ O := (hO x).2 ⟨1, by simp⟩
    have hm0 : m ≠ 0 := by
      intro hm0
      rw [hm0, pow_zero] at hOcard
      have hxfix : ∀ g : S, g • x = x := fun g =>
        Finset.card_le_one.1 (le_of_eq hOcard) (g • x) ((hO _).2 ⟨g, rfl⟩) x hxO
      exact hxω (huniq x hxfix)
    have hyω : ∀ y ∈ O, y ≠ ω := by
      intro y hy hyeq
      obtain ⟨g, hg⟩ := (hO y).1 hy
      apply hxω
      calc x = g⁻¹ • g • x := (inv_smul_smul g x).symm
        _ = g⁻¹ • ω := by rw [hg, hyeq]
        _ = ω := hωfix g⁻¹
    have hsub : O ⊆ Finset.univ.erase ω := fun y hy =>
      Finset.mem_erase.2 ⟨hyω y hy, Finset.mem_univ y⟩
    have hle : O.card + 1 ≤ n := by
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.mem_univ ω), Finset.card_univ, Fintype.card_fin] at h1
      omega
    have h2 : 2 ≤ O.card := by
      rw [hOcard]
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hm0)
    by_cases hfin : O.card + 2 ≤ n
    · exact Or.inl ⟨O, hinv, h2, hfin⟩
    · exact Or.inr ⟨m, by omega⟩
  ·
    have hnt : Nontrivial (MulAction.fixedPoints S (Fin n)) :=
      Finite.one_lt_card_iff_nontrivial.1 (by omega)
    obtain ⟨a, b, hab⟩ := exists_pair_ne (MulAction.fixedPoints S (Fin n))
    have hne : (a : Fin n) ≠ (b : Fin n) := fun h => hab (Subtype.ext h)
    have hfa : ∀ s ∈ S, s (a : Fin n) = a := fun s hs =>
      hfixS _ (MulAction.mem_fixedPoints.1 a.2) s hs
    have hfb : ∀ s ∈ S, s (b : Fin n) = b := fun s hs =>
      hfixS _ (MulAction.mem_fixedPoints.1 b.2) s hs
    have hcard : ({(a : Fin n), (b : Fin n)} : Finset (Fin n)).card = 2 :=
      Finset.card_pair hne
    refine Or.inl ⟨{(a : Fin n), (b : Fin n)}, ?_, ?_, ?_⟩
    · intro s hs x hx
      rcases Finset.mem_insert.1 hx with rfl | hx'
      · rw [hfa s hs]
        exact Finset.mem_insert_self _ _
      · rw [Finset.mem_singleton.1 hx', hfb s hs]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · omega
    · omega

@[expose] def young {n : ℕ} (O : Finset (Fin n)) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {σ | ∀ x, σ x ∈ O ↔ x ∈ O}
  one_mem' := by
    intro x
    first
    | exact Iff.rfl
    | simp
  mul_mem' := by
    intro σ τ hσ hτ x
    rw [Equiv.Perm.mul_apply]
    exact (hσ (τ x)).trans (hτ x)
  inv_mem' := by
    intro σ hσ x
    have h := hσ (σ⁻¹ x)
    have hx : σ (σ⁻¹ x) = x := by
      first
      | (rw [Equiv.Perm.inv_def]; exact Equiv.apply_symm_apply σ x)
      | simp
    rw [hx] at h
    exact h.symm

theorem mem_young_iff {n : ℕ} {O : Finset (Fin n)} {σ : Equiv.Perm (Fin n)} :
    σ ∈ young O ↔ ∀ x, σ x ∈ O ↔ x ∈ O := Iff.rfl

theorem mem_young_of_forall_mem {n : ℕ} (O : Finset (Fin n)) {s : Equiv.Perm (Fin n)}
    (hs : ∀ x ∈ O, s x ∈ O) : s ∈ young O := by
  rw [mem_young_iff]
  intro x
  refine ⟨fun hx => ?_, hs x⟩
  have hsub : O.image s ⊆ O := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    exact hs z hz
  have hcard : (O.image s).card = O.card := Finset.card_image_of_injective O s.injective
  have heq : O.image s = O := Finset.eq_of_subset_of_card_le hsub hcard.symm.le
  have hx' : s x ∈ O.image s := by
    rw [heq]
    exact hx
  obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hx'
  have hzx' : z = x := s.injective hzx
  rw [← hzx']
  exact hz

theorem bt_swap_mem_young {n : ℕ} {O : Finset (Fin n)} {a b : Fin n}
    (h : a ∈ O ↔ b ∈ O) : Equiv.swap a b ∈ young O := by
  rw [mem_young_iff]
  intro z
  rw [Equiv.swap_apply_def]
  by_cases h1 : z = a
  · rw [if_pos h1, h1]
    exact h.symm
  · by_cases h2 : z = b
    · rw [if_neg h1, if_pos h2, h2]
      exact h
    · rw [if_neg h1, if_neg h2]

theorem bt_exists_ne_mem {n : ℕ} (O : Finset (Fin n)) (h2 : 2 ≤ O.card) (a : Fin n) :
    ∃ x ∈ O, x ≠ a := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < O.card)
  by_cases h : x = a
  · exact ⟨y, hy, fun h' => hxy (h.trans h'.symm)⟩
  · exact ⟨x, hx, h⟩

theorem bt_exists_notMem_ne {n : ℕ} (O : Finset (Fin n)) (hO : O.card + 2 ≤ n) (a : Fin n) :
    ∃ y, y ∉ O ∧ y ≠ a := by
  by_contra hc
  push Not at hc
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ insert a O := by
    intro z _
    by_cases hz : z ∈ O
    · exact Finset.mem_insert_of_mem hz
    · exact Finset.mem_insert.mpr (Or.inl (hc z hz))
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at h1
  have h2 := Finset.card_insert_le a O
  omega

theorem bt_exists_ne_two {n : ℕ} (a b : Fin n) (h : 3 ≤ n) :
    ∃ q : Fin n, q ≠ a ∧ q ≠ b := by
  by_contra hc
  push Not at hc
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ insert a {b} := by
    intro z _
    by_cases hz : z = a
    · exact Finset.mem_insert.mpr (Or.inl hz)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (hc z hz)))
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at h1
  have h2 := Finset.card_insert_le a ({b} : Finset (Fin n))
  rw [Finset.card_singleton] at h2
  omega

theorem exists_even_not_mem_young {n : ℕ} (O : Finset (Fin n)) (h2 : 2 ≤ O.card)
    (hO : O.card + 2 ≤ n) : ∃ σ ∈ alternatingGroup (Fin n), σ ∉ young O := by
  obtain ⟨a, ha⟩ : O.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p, hp, -⟩ := bt_exists_notMem_ne O hO a
  obtain ⟨q, hqa, hqp⟩ := bt_exists_ne_two a p (by omega)
  have hap : a ≠ p := fun h => hp (by rw [← h]; exact ha)
  have hpq : p ≠ q := fun h => hqp h.symm
  have haq : a ≠ q := fun h => hqa h.symm
  refine ⟨Equiv.swap a p * Equiv.swap p q, ?_, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hap,
      Equiv.Perm.sign_swap hpq]
    all_goals first | rfl | decide | norm_num | simp
  · intro hmem
    have h1 := (mem_young_iff.mp hmem) a
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hap haq,
      Equiv.swap_apply_left] at h1
    exact hp (h1.mpr ha)

theorem exists_mem_young_moves {n : ℕ} (O : Finset (Fin n)) (h2 : 2 ≤ O.card)
    (hO : O.card + 2 ≤ n) (a : Fin n) : ∃ σ ∈ young O, σ a ≠ a := by
  by_cases ha : a ∈ O
  · obtain ⟨x, hx, hxa⟩ := bt_exists_ne_mem O h2 a
    refine ⟨Equiv.swap a x, bt_swap_mem_young (iff_of_true ha hx), ?_⟩
    rw [Equiv.swap_apply_left]
    exact hxa
  · obtain ⟨y, hy, hya⟩ := bt_exists_notMem_ne O hO a
    refine ⟨Equiv.swap a y, bt_swap_mem_young (iff_of_false ha hy), ?_⟩
    rw [Equiv.swap_apply_left]
    exact hya

theorem exists_involution_mem_young {n : ℕ} (O : Finset (Fin n)) (h2 : 2 ≤ O.card) :
    ∃ σ ∈ young O, σ ≠ 1 ∧ σ * σ = 1 := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < O.card)
  refine ⟨Equiv.swap x y, bt_swap_mem_young (iff_of_true hx hy), ?_, Equiv.swap_mul_self x y⟩
  intro h
  have h' : Equiv.swap x y x = (1 : Equiv.Perm (Fin n)) x := by rw [h]
  rw [Equiv.swap_apply_left, Equiv.Perm.one_apply] at h'
  exact hxy h'.symm

end C127Block

end L246C127

end CFSG.QuasithinUnique
