module

public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Module

variable (F : Type*) [Field F] (V : Type*) [AddCommGroup V] [Module F V]

@[expose] def altHom : Submodule F (Dual F V →ₗ[F] V) where
  carrier := {T | ∀ f : Dual F V, f (T f) = 0}
  add_mem' := fun {T T'} hT hT' f => by
    rw [LinearMap.add_apply, map_add, hT f, hT' f, add_zero]
  zero_mem' := fun f => by rw [LinearMap.zero_apply, map_zero]
  smul_mem' := fun c T hT f => by
    rw [LinearMap.smul_apply, map_smul, hT f, smul_zero]

variable {F V}

theorem mem_altHom {T : Dual F V →ₗ[F] V} : T ∈ altHom F V ↔ ∀ f : Dual F V, f (T f) = 0 :=
  Iff.rfl

theorem card_lt_pairs (n : ℕ) :
    Fintype.card {p : Fin n × Fin n // p.1 < p.2} = n * (n - 1) / 2 := by
  classical
  have hsplit : (Finset.univ : Finset (Fin n)).offDiag =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2) ∪
        (Finset.univ.filter fun p : Fin n × Fin n => p.2 < p.1) := by
    ext p
    simp only [Finset.mem_offDiag, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_filter]
    exact ⟨fun h => lt_or_gt_of_ne h, fun h => h.elim ne_of_lt ne_of_gt⟩
  have hdisj : Disjoint (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2)
      (Finset.univ.filter fun p : Fin n × Fin n => p.2 < p.1) := by
    rw [Finset.disjoint_filter]
    intro p _ h1 h2
    exact lt_asymm h1 h2
  have hswap : (Finset.univ.filter fun p : Fin n × Fin n => p.2 < p.1).card =
      (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2).card := by
    refine Finset.card_bij (fun p _ => p.swap) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact hp
    · intro p _ q _ h
      exact Prod.swap_injective h
    · intro q hq
      refine ⟨q.swap, ?_, Prod.swap_swap q⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      exact hq
  have hcard := Finset.offDiag_card (Finset.univ : Finset (Fin n))
  rw [hsplit, Finset.card_union_of_disjoint hdisj, hswap, Finset.card_univ, Fintype.card_fin]
    at hcard
  rw [Fintype.card_subtype]
  have h1 : n * n - n = n * (n - 1) := by
    rcases n with _ | n
    · rfl
    · rw [Nat.add_sub_cancel, Nat.mul_succ, Nat.add_sub_cancel]
  omega

section Basis

variable {n : ℕ} (b : Basis (Fin n) F V)

theorem mem_altHom_iff {T : Dual F V →ₗ[F] V} :
    T ∈ altHom F V ↔ (∀ i, b.dualBasis i (T (b.dualBasis i)) = 0) ∧
      ∀ i j, b.dualBasis i (T (b.dualBasis j)) + b.dualBasis j (T (b.dualBasis i)) = 0 := by
  constructor
  · intro hT
    refine ⟨fun i => hT _, fun i j => ?_⟩
    have h := hT (b.dualBasis i + b.dualBasis j)
    have hi := hT (b.dualBasis i)
    have hj := hT (b.dualBasis j)
    simp only [map_add, LinearMap.add_apply] at h
    linear_combination h - hi - hj
  · rintro ⟨hdiag, hanti⟩ f
    have hf : f = ∑ j, f (b j) • b.dualBasis j := by
      rw [Basis.coe_dualBasis]
      exact (b.sum_dual_apply_smul_coord f).symm
    set c : Fin n → F := fun j => f (b j) with hc
    have hfT : f (T f) = ∑ p : Fin n × Fin n,
        c p.1 * c p.2 * b.dualBasis p.2 (T (b.dualBasis p.1)) := by
      conv_lhs => rw [hf]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hfT]
    refine Finset.sum_ninvolution (fun p => p.swap) (fun p => ?_) (fun p hp => ?_)
      (fun p => Finset.mem_univ _) (fun p => Prod.swap_swap p)
    · simp only [Prod.fst_swap, Prod.snd_swap]
      have := hanti p.2 p.1
      linear_combination c p.1 * c p.2 * this
    · intro h
      apply hp
      have h1 : p.1 = p.2 := by
        have := congrArg Prod.snd h
        exact this
      rw [h1, hdiag, mul_zero]

@[expose] noncomputable def altCoords :
    altHom F V →ₗ[F] ({p : Fin n × Fin n // p.1 < p.2} → F) where
  toFun T p := b.dualBasis p.1.1 ((T : Dual F V →ₗ[F] V) (b.dualBasis p.1.2))
  map_add' T T' := by
    funext p
    simp only [Submodule.coe_add, LinearMap.add_apply, map_add, Pi.add_apply]
  map_smul' c T := by
    funext p
    simp only [Submodule.coe_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, Pi.smul_apply,
      RingHom.id_apply]

theorem altCoords_bijective : Function.Bijective (altCoords b) := by
  classical
  constructor
  · intro T T' h
    have hTT' : ∀ i j, b.dualBasis i ((T : Dual F V →ₗ[F] V) (b.dualBasis j)) =
        b.dualBasis i ((T' : Dual F V →ₗ[F] V) (b.dualBasis j)) := by
      have hT := (mem_altHom_iff b).mp T.2
      have hT' := (mem_altHom_iff b).mp T'.2
      intro i j
      rcases lt_trichotomy i j with hij | rfl | hij
      · exact congrFun h ⟨(i, j), hij⟩
      · rw [hT.1, hT'.1]
      · have h1 := congrFun h ⟨(j, i), hij⟩
        simp only [altCoords, LinearMap.coe_mk, AddHom.coe_mk] at h1
        have h2 := hT.2 i j
        have h3 := hT'.2 i j
        linear_combination h2 - h3 - h1
    apply Subtype.ext
    refine b.dualBasis.ext fun j => ?_
    refine b.ext_elem fun i => ?_
    rw [← Basis.dualBasis_apply, ← Basis.dualBasis_apply]
    exact hTT' i j
  · intro g
    set M : Fin n → Fin n → F := fun i j =>
      if h : i < j then g ⟨(i, j), h⟩ else if h' : j < i then -g ⟨(j, i), h'⟩ else 0 with hM
    set T : Dual F V →ₗ[F] V := b.dualBasis.constr F fun j => ∑ i, M i j • b i with hTdef
    have hTM : ∀ i j, b.dualBasis i (T (b.dualBasis j)) = M i j := by
      intro i j
      rw [hTdef, Basis.constr_basis, map_sum]
      simp only [map_smul, Basis.dualBasis_apply_self, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have hTmem : T ∈ altHom F V := by
      rw [mem_altHom_iff b]
      refine ⟨fun i => by rw [hTM, hM]; simp, fun i j => ?_⟩
      rw [hTM, hTM, hM]
      rcases lt_trichotomy i j with hij | rfl | hij
      · simp [hij, not_lt_of_gt hij]
      · simp
      · simp [hij, not_lt_of_gt hij]
    refine ⟨⟨T, hTmem⟩, funext fun p => ?_⟩
    change b.dualBasis p.1.1 (T (b.dualBasis p.1.2)) = g p
    rw [hTM, hM]
    simp [p.2]

end Basis

theorem finrank_altHom [FiniteDimensional F V] :
    finrank F (altHom F V) = finrank F V * (finrank F V - 1) / 2 := by
  rw [LinearEquiv.finrank_eq (LinearEquiv.ofBijective _ (altCoords_bijective (finBasis F V))),
    Module.finrank_pi, card_lt_pairs]

end CFSG.LocalAnalysis.GorensteinLyons
