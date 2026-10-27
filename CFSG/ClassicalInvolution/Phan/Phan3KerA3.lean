module

public import CFSG.ClassicalInvolution.Phan.Phan3AKernel

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

@[expose] noncomputable def assignHom {X : Type} [Group X] (g : Fin 6 → X)
    (hrel : ∀ w ∈ phanA3Rels, wordVal g w = 1) : PhanA3Group →* X :=
  PresentedGroup.toGroup (f := g) (by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    rw [FreeGroup.lift_mk]
    exact hrel w hw)

theorem assignHom_mk {X : Type} [Group X] (g : Fin 6 → X)
    (hrel : ∀ w ∈ phanA3Rels, wordVal g w = 1) (w : List (Fin 6 × Bool)) :
    assignHom g hrel (PresentedGroup.mk _ (FreeGroup.mk w)) = wordVal g w :=
  rfl

theorem range_assignHom {X : Type} [Group X] (g : Fin 6 → X)
    (hrel : ∀ w ∈ phanA3Rels, wordVal g w = 1) :
    (assignHom g hrel).range = Subgroup.closure (Set.range g) := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
    ← Set.range_comp]
  congr 1
  ext x
  simp only [Set.mem_range, Function.comp_apply]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, (PresentedGroup.toGroup.of _).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, PresentedGroup.toGroup.of _⟩

theorem phanA3_kernel_vanish {X : Type} [Group X]
    (g : Fin 6 → X) (hrel : ∀ w ∈ phanA3Rels, wordVal g w = 1)
    (h3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥(Subgroup.closure (Set.range g)))) :
    wordVal g phanA3U1 = 1 ∧ wordVal g phanA3U2 = 1 := by
  have hrange := range_assignHom g hrel
  set ε := assignHom g hrel with hε
  have key : ∀ e ∈ phanP.ker, ε e = 1 := by
    intro e he
    obtain ⟨hc, k, hk⟩ := phanP_ker e he
    have hmem : ε e ∈ Subgroup.closure (Set.range g) := by
      rw [← hrange]
      exact ⟨e, rfl⟩
    let z : ↥(Subgroup.closure (Set.range g)) := ⟨ε e, hmem⟩
    have hz : z ∈ Subgroup.center ↥(Subgroup.closure (Set.range g)) := by
      rw [Subgroup.mem_center_iff]
      rintro ⟨y, hy⟩
      rw [← hrange] at hy
      obtain ⟨x, rfl⟩ := hy
      apply Subtype.ext
      show ε x * ε e = ε e * ε x
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc x]
    let zc : Subgroup.center ↥(Subgroup.closure (Set.range g)) := ⟨z, hz⟩
    have hpow : zc ^ (3 ^ k) = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      show (ε e) ^ (3 ^ k) = 1
      rw [← map_pow, hk, map_one]
    by_contra hne
    have hzc : zc ≠ 1 := by
      intro h1
      apply hne
      have := congrArg (fun t : Subgroup.center ↥(Subgroup.closure (Set.range g)) => t.val.val) h1
      simpa [zc, z] using this
    have hdvd : orderOf zc ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hpow
    obtain ⟨j, -, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hzc (orderOf_eq_one_iff.1 (by simpa using hj'))
    have h3o : 3 ∣ orderOf zc := by
      rw [hj']
      exact dvd_pow_self 3 hj0
    exact h3 (h3o.trans (orderOf_dvd_natCard zc))
  exact ⟨(assignHom_mk g hrel phanA3U1).symm.trans (key _ phanP_mk_u1),
    (assignHom_mk g hrel phanA3U2).symm.trans (key _ phanP_mk_u2)⟩

end CFSG.ClassicalInvolution.Phan.Q3G
