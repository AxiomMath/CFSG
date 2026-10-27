module

public import CFSG.RankThree.PartOne.S12.PushingUp
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.CGT.PushingUpLit.SOLT

open CFSG.RankThree.PartOne

variable {m : ℕ}

@[expose] def unitVec (a : Fin m) : Fin m → ZMod 2 := Pi.single a 1

theorem permActionTwo_add (σ : Equiv.Perm (Fin m)) (v w : Fin m → ZMod 2) :
    permActionTwo σ (v + w) = permActionTwo σ v + permActionTwo σ w := rfl

theorem permActionTwo_unitVec (σ : Equiv.Perm (Fin m)) (a : Fin m) :
    permActionTwo σ (unitVec a) = unitVec (σ a) := by
  funext i
  simp only [permActionTwo, unitVec, Pi.single_apply, Equiv.Perm.inv_eq_iff_eq]

theorem permActionTwo_one (σ : Equiv.Perm (Fin m)) :
    permActionTwo σ (fun _ => (1 : ZMod 2)) = fun _ => 1 := rfl

theorem permActionTwo_one_add (σ : Equiv.Perm (Fin m)) (a : Fin m) :
    permActionTwo σ ((fun _ => (1 : ZMod 2)) + unitVec a) =
      (fun _ => (1 : ZMod 2)) + unitVec (σ a) := by
  rw [permActionTwo_add, permActionTwo_one, permActionTwo_unitVec]

theorem exists_perm_two (hm : 4 ≤ m) {a b i j : Fin m} (hab : a ≠ b) (hij : i ≠ j) :
    ∃ σ ∈ alternatingGroup (Fin m), σ a = i ∧ σ b = j := by
  have h1 := alternatingGroup.isMultiplyPretransitive (Fin m)
  have hcard : Nat.card (Fin m) = m := by simp
  rw [hcard] at h1
  have h2 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin m)) (Fin m) 2 :=
    MulAction.isMultiplyPretransitive_of_le (n := m - 2) (by omega) (by omega)
  obtain ⟨g, hga, hgb⟩ := (MulAction.is_two_pretransitive_iff.1 h2) hab hij
  exact ⟨(g : Equiv.Perm (Fin m)), g.2, hga, hgb⟩

@[expose] def indVec (s : Finset (Fin m)) : Fin m → ZMod 2 := fun i => if i ∈ s then 1 else 0

theorem indVec_injective : Function.Injective (indVec (m := m)) := by
  intro s t h
  ext i
  have := congrFun h i
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all [indVec]

theorem indVec_pair {x y : Fin m} (hxy : x ≠ y) : indVec {x, y} = unitVec x + unitVec y := by
  funext i
  by_cases hx : i = x
  · subst hx
    simp [indVec, unitVec, hxy]
  · by_cases hy : i = y
    · subst hy
      simp [indVec, unitVec, hx]
    · simp [indVec, unitVec, hx, hy]

theorem card_orbit_two (hm : 4 ≤ m) {a b : Fin m} (hab : a ≠ b) :
    m < Set.ncard {w : Fin m → ZMod 2 |
      ∃ σ ∈ alternatingGroup (Fin m), w = permActionTwo σ (unitVec a + unitVec b)} := by
  classical
  set S := {w : Fin m → ZMod 2 |
    ∃ σ ∈ alternatingGroup (Fin m), w = permActionTwo σ (unitVec a + unitVec b)} with hS
  have hsub : indVec '' ((Finset.powersetCard 2 (Finset.univ : Finset (Fin m)) :
      Finset (Finset (Fin m))) : Set (Finset (Fin m))) ⊆ S := by
    rintro _ ⟨s, hs, rfl⟩
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hs
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hs.2
    obtain ⟨σ, hσ, hσa, hσb⟩ := exists_perm_two hm hab hxy
    refine ⟨σ, hσ, ?_⟩
    rw [permActionTwo_add, permActionTwo_unitVec, permActionTwo_unitVec, hσa, hσb,
      indVec_pair hxy]
  have h1 : Set.ncard (indVec '' ((Finset.powersetCard 2 (Finset.univ : Finset (Fin m)) :
      Finset (Finset (Fin m))) : Set (Finset (Fin m)))) = m.choose 2 := by
    rw [Set.ncard_image_of_injective _ indVec_injective, Set.ncard_coe_finset,
      Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have h2 : m.choose 2 ≤ S.ncard := h1 ▸ Set.ncard_le_ncard hsub (Set.toFinite S)
  have h3 : m < m.choose 2 := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have h4 : (k + 1).choose 2 = k * (k + 1) / 2 := by
      rw [Nat.choose_two_right]
      simp [mul_comm]
    have h5 : Even (k * (k + 1)) := Nat.even_mul_succ_self k
    obtain ⟨q, hq⟩ := h5
    have h6 : 3 * (k + 1) ≤ k * (k + 1) := Nat.mul_le_mul_right _ (by omega)
    rw [h4]
    omega
  omega

theorem sum_unitVec_add (a b : Fin m) :
    ∑ i, (unitVec a + unitVec b) i = 0 := by
  simp only [Pi.add_apply, unitVec, Finset.sum_add_distrib, Finset.sum_pi_single',
    Finset.mem_univ, ite_true]
  decide

theorem sum_one_add_unitVec (n : ℕ) (a : Fin (2 * n + 1)) :
    ∑ i, (((fun _ => (1 : ZMod 2)) + unitVec a) : Fin (2 * n + 1) → ZMod 2) i = 0 := by
  simp only [Pi.add_apply, unitVec, Finset.sum_add_distrib, Finset.sum_pi_single',
    Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have : ((2 * n + 1) • (1 : ZMod 2)) = 1 := by
    rw [nsmul_eq_mul, mul_one]
    push_cast
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h2]
    simp
  rw [this]
  decide

end CFSG.CGT.PushingUpLit.SOLT
