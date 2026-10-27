module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.Cocode
public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.GolayEven

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.Wong77.Module

open CFSG.Blueprint

@[expose] def elA : NativeSporadic.Carrier .M23 :=
  (⟨genA, Subgroup.subset_closure (Set.mem_insert _ _)⟩ : NativeSporadic.M23)

@[expose] def elB : NativeSporadic.Carrier .M23 :=
  (⟨genB, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩ : NativeSporadic.M23)

@[expose] def elX : NativeSporadic.Carrier .M23 := elB * elB * elA * elB * elB

@[expose] def elY : NativeSporadic.Carrier .M23 :=
  elB * elB * elB * elA * elB * elA * elB * elA * elB

@[expose] def tabX : Fin 23 → Fin 23 :=
  ![0, 17, 14, 6, 4, 12, 3, 15, 8, 11, 20, 9, 5, 13, 2, 7, 16, 1, 19, 18, 10, 21, 22]

@[expose] def tabY : Fin 23 → Fin 23 :=
  ![0, 5, 1, 4, 7, 2, 10, 11, 18, 19, 6, 14, 21, 8, 15, 3, 22, 20, 13, 17, 16, 12, 9]

@[expose] def tabP : Fin 23 → Fin 23 :=
  ![11, 2, 22, 10, 3, 17, 4, 6, 9, 1, 15, 20, 21, 19, 0, 16, 14, 13, 12, 18, 5, 8, 7]

@[expose] def tabQ : Fin 23 → Fin 23 :=
  ![14, 20, 9, 6, 22, 1, 3, 0, 19, 13, 7, 16, 12, 21, 10, 4, 2, 11, 17, 5, 15, 18, 8]

theorem toPermHom_elA : toPermHom elA = genA := rfl

theorem toPermHom_elB : toPermHom elB = genB := rfl

theorem toPerm_elX : toPerm elX = genB * genB * genA * genB * genB := by
  simp only [elX, toPerm, map_mul, toPermHom_elA, toPermHom_elB]

theorem toPerm_elY :
    toPerm elY = (genB * genB * genB * genA) * (genB * genA * genB * genA * genB) := by
  simp only [elY, toPerm, map_mul, toPermHom_elA, toPermHom_elB, mul_assoc]

theorem elX_apply : ∀ i, toPerm elX i = tabX i := by
  intro i
  rw [toPerm_elX]
  repeat rw [Equiv.Perm.mul_apply]
  repeat first | rw [genA_apply] | rw [genB_apply]
  revert i
  decide

theorem tabP_apply : ∀ i, (genB * genB * genB * genA) i = tabP i := by
  intro i
  repeat rw [Equiv.Perm.mul_apply]
  repeat first | rw [genA_apply] | rw [genB_apply]
  revert i
  decide

theorem tabQ_apply : ∀ i, (genB * genA * genB * genA * genB) i = tabQ i := by
  intro i
  repeat rw [Equiv.Perm.mul_apply]
  repeat first | rw [genA_apply] | rw [genB_apply]
  revert i
  decide

theorem elY_apply : ∀ i, toPerm elY i = tabY i := by
  intro i
  rw [toPerm_elY, Equiv.Perm.mul_apply, tabQ_apply, tabP_apply]
  revert i
  decide

@[expose] def depth : Fin 23 → ℕ :=
  ![0, 0, 1, 4, 5, 1, 4, 4, 4, 3, 3, 3, 2, 4, 2, 3, 3, 1, 3, 2, 2, 3, 4]

theorem depth_step : ∀ i : Fin 23, i ≠ 0 → i ≠ 1 → ∃ p : Fin 23, p ≠ 0 ∧ depth p < depth i ∧
    (tabX p = i ∨ tabX i = p ∨ tabY p = i ∨ tabY i = p) := by
  decide

theorem const_of_fixed {v : Word} (hX : ∀ i, v (tabX i) = v i) (hY : ∀ i, v (tabY i) = v i) :
    ∀ i, i ≠ 0 → v i = v 1 := by
  suffices h : ∀ n, ∀ i : Fin 23, depth i = n → i ≠ 0 → v i = v 1 from fun i hi => h _ i rfl hi
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hi hi0
    by_cases h1 : i = 1
    · rw [h1]
    · obtain ⟨p, hp0, hpd, hp⟩ := depth_step i hi0 h1
      have hvp : v i = v p := by
        rcases hp with h | h | h | h
        · rw [← h, hX]
        · rw [← h, hX]
        · rw [← h, hY]
        · rw [← h, hY]
      rw [hvp]
      exact ih (depth p) (hi ▸ hpd) p rfl hp0

theorem eq_zero_of_fixed {u : Word} (hu : u ∈ golayEven) (hX : permLin (toPerm elX) u = u)
    (hY : permLin (toPerm elY) u = u) : u = 0 := by
  have hX' : ∀ i, u (tabX i) = u i := fun i => by
    have := congrFun hX (toPerm elX i)
    simp only [permLin_apply] at this
    rw [← elX_apply]
    simpa using this.symm
  have hY' : ∀ i, u (tabY i) = u i := fun i => by
    have := congrFun hY (toPerm elY i)
    simp only [permLin_apply] at this
    rw [← elY_apply]
    simpa using this.symm
  have hconst := const_of_fixed hX' hY'
  have hu_eq : u = fun i => if i = 0 then u 0 else u 1 := by
    funext i
    by_cases h : i = 0
    · simp [h]
    · simp [h, hconst i h]
  by_contra hne
  have hw := golayEven_weight u hu hne
  have h0 : u 0 = 0 ∨ u 0 = 1 := by
    generalize u 0 = t
    revert t
    decide
  have h1 : u 1 = 0 ∨ u 1 = 1 := by
    generalize u 1 = t
    revert t
    decide
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · apply hne
    rw [hu_eq, h0, h1]
    funext i
    simp
  · rw [hu_eq, h0, h1] at hw
    revert hw
    decide
  · rw [hu_eq, h0, h1] at hw
    revert hw
    decide
  · rw [hu_eq, h0, h1] at hw
    revert hw
    decide

theorem not_equivariant_equiv :
    ¬ ∃ f : Cocode ≃ₗ[ZMod 2] ↥golayEven,
      ∀ (g : NativeSporadic.Carrier .M23) (v : Cocode), f (cocodeRep g v) = golayRep g (f v) := by
  rintro ⟨f, hf⟩
  have hfix : ∀ g : NativeSporadic.Carrier .M23, toPerm g 0 = 0 →
      wordRep g ((f (pt 0) : ↥golayEven) : Word) = ((f (pt 0) : ↥golayEven) : Word) := by
    intro g hg
    have h := hf g (pt 0)
    rw [cocodeRep_pt, hg] at h
    exact congrArg Subtype.val h.symm
  have hne : ((f (pt 0) : ↥golayEven) : Word) ≠ 0 := by
    intro h
    exact pt_ne_zero 0 (f.map_eq_zero_iff.1 (Subtype.ext h))
  refine hne (eq_zero_of_fixed (f (pt 0)).2 ?_ ?_)
  · exact hfix elX (by rw [elX_apply]; rfl)
  · exact hfix elY (by rw [elY_apply]; rfl)

end CFSG.EvenSporadicStandard.Wong77.Module
