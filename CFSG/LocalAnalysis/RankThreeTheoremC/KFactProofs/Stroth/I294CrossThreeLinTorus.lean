module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeLinRCF

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

namespace LinThree

open Module

theorem fin_two_cases (e : Fin 2) : e = 0 ∨ e = 1 := by
  fin_cases e <;> simp

section Shift

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {ι : Type*}
  (b : Basis ((Fin 3 × Fin 2) ⊕ ι) K V)

@[expose] noncomputable def planeTri (j : Fin 3) (k : ZMod 3) : V :=
  tri (b (Sum.inl (j, 0))) (b (Sum.inl (j, 1))) k

@[expose] noncomputable def shiftOp (a : Fin 3 → ZMod 3) : Module.End K V :=
  b.constr K (Sum.elim
    (fun x : Fin 3 × Fin 2 => planeTri b x.1 (a x.1 + ((x.2 : ℕ) : ZMod 3)))
    (fun k => b (Sum.inr k)))

theorem shiftOp_inl_zero (a : Fin 3 → ZMod 3) (j : Fin 3) :
    shiftOp b a (b (Sum.inl (j, 0))) = planeTri b j (a j) := by
  simp [shiftOp, Basis.constr_basis]

theorem shiftOp_inl_one (a : Fin 3 → ZMod 3) (j : Fin 3) :
    shiftOp b a (b (Sum.inl (j, 1))) = planeTri b j (a j + 1) := by
  simp [shiftOp, Basis.constr_basis]

theorem shiftOp_inr (a : Fin 3 → ZMod 3) (k : ι) :
    shiftOp b a (b (Sum.inr k)) = b (Sum.inr k) := by
  simp [shiftOp, Basis.constr_basis]

theorem shiftOp_tri (a : Fin 3 → ZMod 3) (j : Fin 3) (k : ZMod 3) :
    shiftOp b a (planeTri b j k) = planeTri b j (k + a j) :=
  map_tri (shiftOp b a) (shiftOp_inl_zero b a j) (shiftOp_inl_one b a j) k

theorem shiftOp_fix (a : Fin 3 → ZMod 3) {w : V}
    (hw : w ∈ Submodule.span K (Set.range fun k : ι => b (Sum.inr k))) : shiftOp b a w = w := by
  refine LinearMap.eqOn_span' (f := shiftOp b a) (g := LinearMap.id) ?_ hw
  rintro _ ⟨k, rfl⟩
  exact shiftOp_inr b a k

theorem shiftOp_zero : shiftOp b (0 : Fin 3 → ZMod 3) = 1 := by
  refine b.ext fun i => ?_
  rcases i with ⟨j, e⟩ | k
  · rcases fin_two_cases e with rfl | rfl
    · rw [shiftOp_inl_zero]
      simp [planeTri]
    · rw [shiftOp_inl_one]
      simp [planeTri]
  · rw [shiftOp_inr]
    rfl

theorem shiftOp_add (a a' : Fin 3 → ZMod 3) :
    shiftOp b (a + a') = shiftOp b a * shiftOp b a' := by
  refine b.ext fun i => ?_
  rcases i with ⟨j, e⟩ | k
  · rcases fin_two_cases e with rfl | rfl
    · rw [Module.End.mul_apply, shiftOp_inl_zero, shiftOp_inl_zero, shiftOp_tri, Pi.add_apply,
        add_comm]
    · rw [Module.End.mul_apply, shiftOp_inl_one, shiftOp_inl_one, shiftOp_tri, Pi.add_apply]
      congr 1
      ring
  · rw [Module.End.mul_apply, shiftOp_inr, shiftOp_inr, shiftOp_inr]

@[expose] noncomputable def shiftHom : Multiplicative (Fin 3 → ZMod 3) →* Module.End K V where
  toFun a := shiftOp b (Multiplicative.toAdd a)
  map_one' := shiftOp_zero b
  map_mul' a a' := shiftOp_add b _ _

theorem basis_pair_indep {ι' : Type*} (b' : Basis ι' K V) {x y : ι'} (hxy : x ≠ y) :
    ∀ α β : K, α • b' x + β • b' y = 0 → α = 0 ∧ β = 0 := by
  have hinj : Function.Injective ![x, y] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have hli : LinearIndependent K ![b' x, b' y] := by
    have := b'.linearIndependent.comp ![x, y] hinj
    convert this using 1
    funext i
    fin_cases i <;> rfl
  exact LinearIndependent.pair_iff.1 hli

theorem tri_injective {s t : V} (h : ∀ α β : K, α • s + β • t = 0 → α = 0 ∧ β = 0) :
    Function.Injective (tri s t) := by
  have hA : s ≠ t := by
    intro hst
    have := (h 1 (-1) (by rw [one_smul, neg_smul, one_smul, hst]; abel)).1
    exact one_ne_zero this
  have hB : s ≠ -s - t := by
    intro hst
    have := (h 2 1 (by
      calc (2 : K) • s + (1 : K) • t = s + s + t := by module
        _ = s + (-s - t) + t := by rw [← hst]
        _ = 0 := by abel)).2
    exact one_ne_zero this
  have hC : t ≠ -s - t := by
    intro hst
    have := (h 1 2 (by
      calc (1 : K) • s + (2 : K) • t = s + t + t := by module
        _ = s + t + (-s - t) := by rw [← hst]
        _ = 0 := by abel)).1
    exact one_ne_zero this
  intro k k' hkk'
  rcases zmod3_cases k with rfl | rfl | rfl <;> rcases zmod3_cases k' with rfl | rfl | rfl
  all_goals first
    | rfl
    | (exfalso
       simp at hkk'
       first
         | exact hA hkk' | exact hA hkk'.symm
         | exact hB hkk' | exact hB hkk'.symm
         | exact hC hkk' | exact hC hkk'.symm)

end Shift

section Main

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {ι : Type*}
  (b : Basis ((Fin 3 × Fin 2) ⊕ ι) K V)

theorem shiftOp_inj {a a' : Fin 3 → ZMod 3} (h : shiftOp b a = shiftOp b a') : a = a' := by
  funext j
  have h1 := congrArg (fun T : Module.End K V => T (b (Sum.inl (j, 0)))) h
  simp only [shiftOp_inl_zero] at h1
  have hind := basis_pair_indep b (x := Sum.inl (j, (0 : Fin 2)))
    (y := Sum.inl (j, (1 : Fin 2))) (by simp)
  exact tri_injective hind h1

theorem shiftOp_comm (g : Module.End K V)
    (hgood : ∀ j : Fin 3, GoodRel g (b (Sum.inl (j, 0))) (b (Sum.inl (j, 1))))
    (hW : ∀ k : ι, g (b (Sum.inr k)) ∈ Submodule.span K (Set.range fun k : ι => b (Sum.inr k)))
    (a : Fin 3 → ZMod 3) : shiftOp b a * g = g * shiftOp b a := by
  refine b.ext fun i => ?_
  rcases i with ⟨j, e⟩ | k
  · obtain ⟨c, hs, ht⟩ := hgood j
    have hs' : g (b (Sum.inl (j, 0))) = planeTri b j c := hs
    have ht' : g (b (Sum.inl (j, 1))) = planeTri b j (c + 1) := ht
    have hg : ∀ k, g (planeTri b j k) = planeTri b j (k + c) := map_tri g hs ht
    rcases fin_two_cases e with rfl | rfl
    · rw [Module.End.mul_apply, Module.End.mul_apply, hs', shiftOp_inl_zero, shiftOp_tri, hg,
        add_comm]
    · rw [Module.End.mul_apply, Module.End.mul_apply, ht', shiftOp_inl_one, shiftOp_tri, hg]
      congr 1
      ring
  · rw [Module.End.mul_apply, Module.End.mul_apply, shiftOp_inr, shiftOp_fix b a (hW k)]

end Main

theorem exists_torus_hom {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (g : Module.End K V) (hg3 : g ^ 3 = 1) (h3 : (3 : K) ≠ 0)
    (hroot : ∀ x : K, x ^ 2 + x + 1 ≠ 0) (hdim : 6 ≤ finrank K V) :
    ∃ E : Multiplicative (Fin 3 → ZMod 3) →* Module.End K V,
      Function.Injective E ∧ ∀ a, E a * g = g * E a := by
  obtain ⟨ι, _, b, hgood, hW⟩ := exists_adapted_basis g hg3 h3 hroot hdim
  refine ⟨shiftHom b, ?_, fun a => shiftOp_comm b g hgood hW _⟩
  intro a a' h
  exact Multiplicative.toAdd.injective (shiftOp_inj b h)

end LinThree

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
