module

public import CFSG.CharacterTheory.FrobeniusKernel.Helpers
public import Mathlib.Algebra.Order.Star.Real

public section

namespace CFSG

namespace FrobeniusKernel.Frobenius

open scoped BigOperators

open FrobeniusKernel.Helpers

noncomputable section

def kernelSet (G X : Type*) [Group G] [MulAction G X] : Set G :=
  {g | g = 1 ∨ ∀ x : X, g • x ≠ x}

@[simp] theorem mem_kernelSet {G X : Type*} [Group G] [MulAction G X]
    (g : G) : g ∈ kernelSet G X ↔ g = 1 ∨ ∀ x : X, g • x ≠ x :=
  Iff.rfl

private theorem not_mem_kernelSet_iff {G X : Type*} [Group G] [MulAction G X]
    (g : G) : g ∉ kernelSet G X ↔ g ≠ 1 ∧ ∃ x : X, g • x = x := by
  simp [kernelSet]

private theorem kernelSet_inv {G X : Type*} [Group G] [MulAction G X]
    (g : G) : g⁻¹ ∈ kernelSet G X ↔ g ∈ kernelSet G X := by
  constructor
  · rintro (h | h)
    · exact Or.inl (inv_eq_one.mp h)
    · right
      intro x hx
      apply h x
      apply (smul_left_cancel g)
      simp [hx]
  · rintro (h | h)
    · simp [h]
    · right
      intro x hx
      apply h x
      apply (smul_left_cancel g⁻¹)
      simp [hx]

private theorem kernelSet_conj {G X : Type*} [Group G] [MulAction G X]
    (a g : G) : a * g * a⁻¹ ∈ kernelSet G X ↔ g ∈ kernelSet G X := by
  constructor
  · rintro (h | h)
    · left
      have h' := congrArg (fun z : G => a⁻¹ * z * a) h
      simpa [mul_assoc] using h'
    · right
      intro x hx
      apply h (a • x)
      simp [mul_smul, hx]
  · rintro (h | h)
    · simp [h]
    · right
      intro x hx
      apply h (a⁻¹ • x)
      apply (smul_left_cancel a)
      simpa [mul_smul] using hx

theorem fixed_unique {G X : Type*} [Group G] [MulAction G X]
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X,
      g • x = x → g • y = y → x = y)
    {g : G} (hg : g ≠ 1) {x y : X}
    (hx : g • x = x) (hy : g • y = y) : x = y :=
  hfrob g hg x y hx hy

private theorem sum_nonKernel_eq_sum_fixed
    {G X R : Type*} [Group G] [Fintype G] [Fintype X]
    [DecidableEq G] [DecidableEq X]
    [MulAction G X] [DecidablePred fun g : G => g ∈ kernelSet G X]
    [AddCommMonoid R]
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X,
      g • x = x → g • y = y → x = y)
    (F : G → R) :
    ∑ g : G, (if g ∉ kernelSet G X then F g else 0) =
      ∑ x : X, ∑ g : G, (if g ≠ 1 ∧ g • x = x then F g else 0) := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  by_cases hnot : g ∉ kernelSet G X
  · rw [if_pos hnot]
    obtain ⟨hg, x, hx⟩ := not_mem_kernelSet_iff g |>.mp hnot
    rw [Finset.sum_eq_single x]
    · simp [hg, hx]
    · intro y _ hyx
      have hy : g • y ≠ y := by
        intro hgy
        exact hyx (hfrob g hg y x hgy hx)
      simp [hy]
    · simp
  · rw [if_neg hnot]
    have hmem : g ∈ kernelSet G X := Classical.not_not.mp hnot
    rcases hmem with rfl | hfree
    · simp
    · symm
      apply Finset.sum_eq_zero
      intro x _
      simp [hfree x]

private theorem sum_fixed_eq_stabilizer
    {G X R : Type*} [Group G] [Fintype G] [Fintype X]
    [DecidableEq G] [DecidableEq X]
    [MulAction G X] [AddCommMonoid R]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (F : G → R) (hF : ∀ a g : G, F (a * g * a⁻¹) = F g)
    (x₀ x : X) [Fintype (MulAction.stabilizer G x₀)] :
    ∑ g : G, (if g ≠ 1 ∧ g • x = x then F g else 0) =
      ∑ h : MulAction.stabilizer G x₀, (if (h : G) ≠ 1 then F h else 0) := by
  classical
  obtain ⟨a, rfl⟩ := htrans x₀ x
  let q : G ≃ G := MulAut.conj a
  let A : G → R := fun g => if g ≠ 1 ∧ g • (a • x₀) = a • x₀ then F g else 0
  have hsum := Equiv.sum_comp q A
  change (∑ g : G, A g) = _
  rw [← hsum]
  simp only [A, q]
  have hpoint (g : G) :
      (a * g * a⁻¹) • (a • x₀) = a • x₀ ↔ g • x₀ = x₀ := by
    constructor
    · intro h
      apply (smul_left_cancel a)
      simpa [mul_smul] using h
    · intro h
      simp [mul_smul, h]
  change (∑ g : G, if a * g * a⁻¹ ≠ 1 ∧
    (a * g * a⁻¹) • (a • x₀) = a • x₀ then
      F (a * g * a⁻¹) else 0) = _
  have hne (g : G) : a * g * a⁻¹ ≠ 1 ↔ g ≠ 1 := by simp
  simp_rw [hpoint, hF, hne]
  have hs :
      (∑ g ∈ Finset.univ.filter (fun g : G => g • x₀ = x₀),
        if g ≠ 1 then F g else 0) =
      ∑ h : MulAction.stabilizer G x₀,
        (if (h : G) ≠ 1 then F h else 0) := Finset.sum_subtype
    (p := fun g : G => g ∈ MulAction.stabilizer G x₀)
    (F := inferInstance)
    (Finset.univ.filter fun g : G => g • x₀ = x₀)
    (by simp [MulAction.mem_stabilizer_iff])
    (fun g : G => if g ≠ 1 then F g else 0)
  rw [← hs]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro g _
  by_cases hg : g = 1 <;> by_cases hx : g • x₀ = x₀ <;> simp [hg, hx]

private theorem sum_nonKernel_eq_card_mul_stabilizer
    {G X R : Type*} [Group G] [Fintype G] [Fintype X]
    [DecidableEq G] [DecidableEq X]
    [MulAction G X] [DecidablePred fun g : G => g ∈ kernelSet G X]
    [AddCommMonoid R]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X,
      g • x = x → g • y = y → x = y)
    (F : G → R) (hF : ∀ a g : G, F (a * g * a⁻¹) = F g)
    (x₀ : X) [Fintype (MulAction.stabilizer G x₀)] :
    ∑ g : G, (if g ∉ kernelSet G X then F g else 0) =
      Fintype.card X •
        ∑ h : MulAction.stabilizer G x₀,
          (if (h : G) ≠ 1 then F h else 0) := by
  classical
  rw [sum_nonKernel_eq_sum_fixed hfrob F]
  simp_rw [sum_fixed_eq_stabilizer htrans F hF x₀]
  rw [Finset.sum_const, Finset.card_univ]

def kernelFinset (G X : Type*) [Group G] [Fintype G] [MulAction G X]
    [DecidablePred fun g : G => g ∈ kernelSet G X] : Finset G :=
  Finset.univ.filter fun g => g ∈ kernelSet G X

@[simp] theorem mem_kernelFinset
    {G X : Type*} [Group G] [Fintype G] [MulAction G X]
    [DecidablePred fun g : G => g ∈ kernelSet G X] (g : G) :
    g ∈ kernelFinset G X ↔ g ∈ kernelSet G X := by
  simp [kernelFinset]

private theorem card_kernelFinset
    {G X : Type*} [Group G] [Fintype G] [Fintype X]
    [DecidableEq G] [DecidableEq X] [MulAction G X]
    [DecidablePred fun g : G => g ∈ kernelSet G X]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X,
      g • x = x → g • y = y → x = y)
    (x₀ : X) [Fintype (MulAction.stabilizer G x₀)] :
    (kernelFinset G X).card = Fintype.card X := by
  classical
  have hcount := sum_nonKernel_eq_card_mul_stabilizer
    htrans hfrob (fun _ : G => (1 : ℕ)) (fun _ _ => rfl) x₀
  have hpartition :
      (kernelFinset G X).card +
        (Finset.univ.filter fun g : G => g ∉ kernelSet G X).card =
          Fintype.card G := by
    let A := kernelFinset G X
    let B := Finset.univ.filter fun g : G => g ∉ kernelSet G X
    have hd : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro g hgA hgB
      have hm : g ∈ kernelSet G X := by simpa [A] using hgA
      have hnm : g ∉ kernelSet G X := by simpa [B] using hgB
      exact hnm hm
    have hu : A ∪ B = Finset.univ := by
      ext g
      simp only [Finset.mem_union, Finset.mem_univ, iff_true]
      by_cases hm : g ∈ kernelSet G X
      · exact Or.inl (by simpa [A] using hm)
      · right
        change g ∈ Finset.univ.filter (fun u : G => u ∉ kernelSet G X)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hm
    change A.card + B.card = Fintype.card G
    rw [← Finset.card_union_of_disjoint hd, hu, Finset.card_univ]
  have hHsum :
      (∑ h : MulAction.stabilizer G x₀,
        (if (h : G) ≠ 1 then (1 : ℕ) else 0)) =
        Fintype.card (MulAction.stabilizer G x₀) - 1 := by
    calc
      (∑ h : MulAction.stabilizer G x₀,
          (if (h : G) ≠ 1 then (1 : ℕ) else 0)) =
          (Finset.univ.filter fun h : MulAction.stabilizer G x₀ => h ≠ 1).card := by
            simpa using (Finset.sum_boole (R := ℕ)
              (fun h : MulAction.stabilizer G x₀ => h ≠ 1) Finset.univ)
      _ = Fintype.card (MulAction.stabilizer G x₀) - 1 := by
        rw [Finset.filter_ne', Finset.card_erase_eq_ite]
        simp
  have hcount' :
      (Finset.univ.filter fun g : G => g ∉ kernelSet G X).card =
        Fintype.card X * (Fintype.card (MulAction.stabilizer G x₀) - 1) := by
    rw [hHsum] at hcount
    simpa [Finset.sum_boole] using hcount
  let : MulAction.IsPretransitive G X :=
    (MulAction.isPretransitive_iff G X).mpr htrans
  have hgroup := Subgroup.card_mul_index (MulAction.stabilizer G x₀)
  rw [MulAction.index_stabilizer_of_transitive G x₀] at hgroup
  simp only [Nat.card_eq_fintype_card] at hgroup
  have hgroup' : Fintype.card X *
      Fintype.card (MulAction.stabilizer G x₀) = Fintype.card G := by
    simpa [mul_comm] using hgroup
  have hHpos : 1 ≤ Fintype.card (MulAction.stabilizer G x₀) :=
    Fintype.card_pos_iff.mpr ⟨1⟩
  have hmul : Fintype.card X *
        (Fintype.card (MulAction.stabilizer G x₀) - 1) + Fintype.card X =
      Fintype.card X * Fintype.card (MulAction.stabilizer G x₀) := by
    calc
      _ = Fintype.card X *
          ((Fintype.card (MulAction.stabilizer G x₀) - 1) + 1) := by
            rw [Nat.mul_add, Nat.mul_one]
      _ = _ := by rw [Nat.sub_add_cancel hHpos]
  omega

private def twoSidedAverage {G : Type*} [Group G] [Fintype G]
    (e : MonoidAlgebra ℂ G) (g h : G) : ℂ :=
  ∑ x : G, e.coeff (g * x * h⁻¹ * x⁻¹)

private theorem twoSidedAverage_conj_left
    {G : Type*} [Group G] [Fintype G]
    {e : MonoidAlgebra ℂ G} (he : e ∈ Set.center (MonoidAlgebra ℂ G))
    (a g h : G) :
    twoSidedAverage e (a * g * a⁻¹) h = twoSidedAverage e g h := by
  classical
  let F : G → ℂ := fun x =>
    e.coeff ((a * g * a⁻¹) * x * h⁻¹ * x⁻¹)
  have hs := Equiv.sum_comp (Equiv.mulLeft a) F
  change (∑ x : G, F x) = _
  rw [← hs]
  apply Finset.sum_congr rfl
  intro x _
  simp only [F]
  change e.coeff ((a * g * a⁻¹) * (a * x) * h⁻¹ * (a * x)⁻¹) = _
  rw [show (a * g * a⁻¹) * (a * x) * h⁻¹ * (a * x)⁻¹ =
      a * (g * x * h⁻¹ * x⁻¹) * a⁻¹ by simp [mul_assoc]]
  exact central_coeff_conj he a _

private theorem twoSidedAverage_conj_right
    {G : Type*} [Group G] [Fintype G]
    (e : MonoidAlgebra ℂ G) (a g h : G) :
    twoSidedAverage e g (a * h * a⁻¹) = twoSidedAverage e g h := by
  classical
  let F : G → ℂ := fun x =>
    e.coeff (g * x * (a * h * a⁻¹)⁻¹ * x⁻¹)
  have hs := Equiv.sum_comp (Equiv.mulRight a⁻¹) F
  change (∑ x : G, F x) = _
  rw [← hs]
  apply Finset.sum_congr rfl
  intro x _
  simp only [F]
  change e.coeff (g * (x * a⁻¹) * (a * h * a⁻¹)⁻¹ * (x * a⁻¹)⁻¹) = _
  congr 1
  simp [mul_assoc]

private theorem sum_twoSided_nonKernel
    {G X : Type*} [Group G] [Fintype G] [Fintype X]
    [DecidableEq G] [DecidableEq X] [MulAction G X]
    [DecidablePred fun g : G => g ∈ kernelSet G X]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X,
      g • x = x → g • y = y → x = y)
    (x₀ : X) [Fintype (MulAction.stabilizer G x₀)]
    (e : MonoidAlgebra ℂ G) (he : e ∈ Set.center (MonoidAlgebra ℂ G)) :
    (∑ g : G, if g ∉ kernelSet G X then
        ∑ h : G, if h ∉ kernelSet G X then twoSidedAverage e g h else 0
      else 0) =
      ((Fintype.card X : ℂ) * Fintype.card X) *
        ∑ g : MulAction.stabilizer G x₀,
          if (g : G) ≠ 1 then
            ∑ h : MulAction.stabilizer G x₀,
              if (h : G) ≠ 1 then twoSidedAverage e g h else 0
          else 0 := by
  classical
  have hleft := sum_nonKernel_eq_card_mul_stabilizer htrans hfrob
    (fun g : G => ∑ h : G, if h ∉ kernelSet G X then
      twoSidedAverage e g h else 0)
    (fun a g => by
      apply Finset.sum_congr rfl
      intro h _
      apply ite_congr rfl
      · intro _
        exact twoSidedAverage_conj_left he a g h
      · intro _
        rfl) x₀
  have hright (g : G) := sum_nonKernel_eq_card_mul_stabilizer htrans hfrob
    (fun h : G => twoSidedAverage e g h)
    (fun a h => twoSidedAverage_conj_right e a g h) x₀
  rw [hleft]
  simp_rw [hright]
  simp only [nsmul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  by_cases hg : (g : G) = 1
  · simp [hg]
  · rw [if_pos hg, if_pos hg, mul_assoc]
    apply congrArg ((Fintype.card X : ℂ) * ·)
    rw [Finset.mul_sum]

private def diagonalHom (G : Type*) [Group G] : G →* G × G where
  toFun g := (g, g)
  map_one' := rfl
  map_mul' _ _ := rfl

private def subgroupDiagonalHom {G : Type*} [Group G] (H : Subgroup G) :
    H →* G × G where
  toFun h := (h, h)
  map_one' := rfl
  map_mul' _ _ := rfl

private def subgroupLeftHom {G : Type*} [Group G] (H : Subgroup G) :
    H →* G × G where
  toFun h := (h, 1)
  map_one' := rfl
  map_mul' _ _ := by simp

private def subgroupProductHom {G : Type*} [Group G] (H : Subgroup G) :
    H × H →* G × G where
  toFun h := (h.1, h.2)
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem four_trace_quantities
    {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H]
    (e : MonoidAlgebra ℂ G) (he : e ∈ Set.center (MonoidAlgebra ℂ G))
    (hei : e * e = e) (hestar : groupAlgebraAdjoint e = e) :
    ∃ nG nH nL nHH : ℕ,
      (Fintype.card G : ℂ)⁻¹ *
          ∑ g : G, twoSidedAverage e g g = nG ∧
      (Fintype.card H : ℂ)⁻¹ *
          ∑ h : H, twoSidedAverage e h h = nH ∧
      (Fintype.card H : ℂ)⁻¹ *
          ∑ h : H, ∑ x : G, e.coeff h = nL ∧
      (Fintype.card (H × H) : ℂ)⁻¹ *
          ∑ p : H × H, twoSidedAverage e p.1 p.2 = nHH := by
  classical
  obtain ⟨nG, hnG⟩ :=
    trace_average_centralIdempotent_eq_nat_of_adjoint
      (diagonalHom G) e he hei hestar
  obtain ⟨nH, hnH⟩ :=
    trace_average_centralIdempotent_eq_nat_of_adjoint
      (subgroupDiagonalHom H) e he hei hestar
  obtain ⟨nL, hnL⟩ :=
    trace_average_centralIdempotent_eq_nat_of_adjoint
      (subgroupLeftHom H) e he hei hestar
  obtain ⟨nHH, hnHH⟩ :=
    trace_average_centralIdempotent_eq_nat_of_adjoint
      (subgroupProductHom H) e he hei hestar
  refine ⟨nG, nH, nL, nHH, ?_, ?_, ?_, ?_⟩
  · simpa [diagonalHom, twoSidedAverage, invOf_eq_inv] using hnG
  · simpa [subgroupDiagonalHom, twoSidedAverage, invOf_eq_inv] using hnH
  · simpa [subgroupLeftHom, invOf_eq_inv] using hnL
  · simpa [subgroupProductHom, twoSidedAverage, invOf_eq_inv] using hnHH

private theorem sum_eq_kernel_add_nonKernel
    {G X R : Type*} [Group G] [Fintype G] [MulAction G X]
    [DecidablePred fun g : G => g ∈ kernelSet G X]
    [AddCommMonoid R] (F : G → R) :
    (∑ g : G, F g) =
      (∑ g : G, if g ∈ kernelSet G X then F g else 0) +
      ∑ g : G, if g ∉ kernelSet G X then F g else 0 := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g _
  by_cases hg : g ∈ kernelSet G X <;> simp [hg]

private theorem sum_eq_value_one_add
    {L R : Type*} [Fintype L] [One L] [DecidableEq L]
    [AddCommMonoid R] (F : L → R) :
    (∑ g : L, F g) = F 1 + ∑ g : L, if g ≠ 1 then F g else 0 := by
  classical
  calc
    (∑ g : L, F g) =
        ∑ g : L, ((if g = 1 then F g else 0) +
          if g ≠ 1 then F g else 0) := by
            apply Finset.sum_congr rfl
            intro g _
            by_cases hg : g = 1 <;> simp [hg]
    _ = (∑ g : L, if g = 1 then F g else 0) +
        ∑ g : L, if g ≠ 1 then F g else 0 := Finset.sum_add_distrib
    _ = F 1 + ∑ g : L, if g ≠ 1 then F g else 0 := by
      rw [Finset.sum_ite_eq' Finset.univ 1]
      simp

private def frobeniusQ
    {G X : Type*} [Group G] [Fintype G] [Fintype X]
    [MulAction G X] [DecidablePred fun g : G => g ∈ kernelSet G X]
    (e : MonoidAlgebra ℂ G) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ *
      (∑ a : G, if a ∈ kernelSet G X then twoSidedAverage e a a else 0)
    - (Fintype.card X : ℂ)⁻¹ *
      (∑ a : G, if a ∈ kernelSet G X then
        ∑ b : G, if b ∈ kernelSet G X then e.coeff (a * b⁻¹) else 0
      else 0)

private theorem first_kernel_term_eq_trace_difference
    {G X : Type*} [Group G] [Fintype G] [Fintype X]
    [DecidableEq G] [DecidableEq X] [MulAction G X]
    [DecidablePred fun g : G => g ∈ kernelSet G X]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X,
      g • x = x → g • y = y → x = y)
    (x₀ : X) [Fintype (MulAction.stabilizer G x₀)]
    (e : MonoidAlgebra ℂ G) (he : e ∈ Set.center (MonoidAlgebra ℂ G)) :
    (Fintype.card G : ℂ)⁻¹ *
        (∑ g : G, if g ∈ kernelSet G X then
          twoSidedAverage e g g else 0) -
      (Fintype.card (MulAction.stabilizer G x₀) : ℂ)⁻¹ *
        Fintype.card G * e.coeff 1 =
    (Fintype.card G : ℂ)⁻¹ *
        ∑ g : G, twoSidedAverage e g g -
      (Fintype.card (MulAction.stabilizer G x₀) : ℂ)⁻¹ *
        ∑ h : MulAction.stabilizer G x₀, twoSidedAverage e h h := by
  classical
  let F : G → ℂ := fun g => twoSidedAverage e g g
  have hF (a g : G) : F (a * g * a⁻¹) = F g := by
    dsimp [F]
    rw [twoSidedAverage_conj_right e a (a * g * a⁻¹) g,
      twoSidedAverage_conj_left he a g g]
  have hcount := sum_nonKernel_eq_card_mul_stabilizer
    htrans hfrob F hF x₀
  have hpartG := sum_eq_kernel_add_nonKernel (X := X) F
  have hpartH := sum_eq_value_one_add
    (fun h : MulAction.stabilizer G x₀ => F h)
  have hpartH' :
      (∑ h : MulAction.stabilizer G x₀, F h) = F 1 +
        ∑ h : MulAction.stabilizer G x₀,
          if (h : G) ≠ 1 then F h else 0 := by
    simpa using hpartH
  have hone : F 1 = (Fintype.card G : ℂ) * e.coeff 1 := by
    simp [F, twoSidedAverage, nsmul_eq_mul]
  let : MulAction.IsPretransitive G X :=
    (MulAction.isPretransitive_iff G X).mpr htrans
  have hgroup := Subgroup.card_mul_index (MulAction.stabilizer G x₀)
  rw [MulAction.index_stabilizer_of_transitive G x₀] at hgroup
  simp only [Nat.card_eq_fintype_card] at hgroup
  have hgroupC : (Fintype.card G : ℂ) =
      Fintype.card X * Fintype.card (MulAction.stabilizer G x₀) := by
    exact_mod_cast (by simpa [mul_comm] using hgroup.symm)
  change _ * (∑ g : G, if g ∈ kernelSet G X then F g else 0) - _ =
    _ * (∑ g : G, F g) - _
  rw [hpartG, hpartH', hone]
  change _ = _ - _ *
    ((Fintype.card G : ℂ) * e.coeff 1 +
      ∑ h : MulAction.stabilizer G x₀,
        if (h : G) ≠ 1 then F h else 0)
  have hcount' :
      (∑ g : G, if g ∉ kernelSet G X then F g else 0) =
        (Fintype.card X : ℂ) *
          ∑ h : MulAction.stabilizer G x₀,
            if (h : G) ≠ 1 then F h else 0 := by
    simpa [nsmul_eq_mul] using hcount
  rw [hcount']
  rw [hgroupC]
  have hX0 : (Fintype.card X : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos_iff.mpr ⟨x₀⟩))
  have hH0 : (Fintype.card (MulAction.stabilizer G x₀) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos_iff.mpr ⟨1⟩))
  field_simp [hX0, hH0]
  ring

private theorem sum_ite_neg
    {ι R : Type*} [Fintype ι] [AddCommGroup R]
    (P : ι → Prop) [DecidablePred P] (F : ι → R) :
    (∑ i : ι, if P i then -F i else 0) =
      -(∑ i : ι, if P i then F i else 0) := by
  classical
  calc
    (∑ i : ι, if P i then -F i else 0) =
        ∑ i : ι, -(if P i then F i else 0) := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : P i <;> simp [hi]
    _ = -(∑ i : ι, if P i then F i else 0) := by
      simpa using (Finset.sum_neg_distrib
        (s := Finset.univ) (fun i : ι => if P i then F i else 0))

private theorem sum_ite_swap
    {ι κ R : Type*} [Fintype ι] [Fintype κ] [AddCommMonoid R]
    (P : ι → Prop) (Q : κ → Prop) [DecidablePred P] [DecidablePred Q]
    (F : ι → κ → R) :
    (∑ i : ι, if P i then ∑ k : κ, if Q k then F i k else 0 else 0) =
      ∑ k : κ, if Q k then ∑ i : ι, if P i then F i k else 0 else 0 := by
  classical
  calc
    (∑ i : ι, if P i then ∑ k : κ, if Q k then F i k else 0 else 0) =
        ∑ i : ι, ∑ k : κ, if P i ∧ Q k then F i k else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : P i
          · rw [if_pos hi]
            apply Finset.sum_congr rfl
            intro k _
            by_cases hk : Q k <;> simp [hi, hk]
          · rw [if_neg hi]
            symm
            apply Finset.sum_eq_zero
            intro k _
            simp [hi]
    _ = ∑ k : κ, ∑ i : ι, if P i ∧ Q k then F i k else 0 := Finset.sum_comm
    _ = ∑ k : κ, if Q k then
          ∑ i : ι, if P i then F i k else 0 else 0 := by
          apply Finset.sum_congr rfl
          intro k _
          by_cases hk : Q k
          · rw [if_pos hk]
            apply Finset.sum_congr rfl
            intro i _
            by_cases hi : P i <;> simp [hi, hk]
          · rw [if_neg hk]
            apply Finset.sum_eq_zero
            intro i _
            simp [hk]

private theorem sum_nonKernel_nonKernel_eq_kernel_kernel
    {G X : Type*} [Group G] [Fintype G] [MulAction G X]
    [DecidablePred fun g : G => g ∈ kernelSet G X]
    (F : G → G → ℂ)
    (hrow : ∀ g : G, ∑ h : G, F g h = 0)
    (hcol : ∀ h : G, ∑ g : G, F g h = 0) :
    (∑ g : G, if g ∉ kernelSet G X then
        ∑ h : G, if h ∉ kernelSet G X then F g h else 0 else 0) =
      ∑ g : G, if g ∈ kernelSet G X then
        ∑ h : G, if h ∈ kernelSet G X then F g h else 0 else 0 := by
  classical
  have hrow' (g : G) :
      (∑ h : G, if h ∉ kernelSet G X then F g h else 0) =
        -∑ h : G, if h ∈ kernelSet G X then F g h else 0 := by
    have hp := sum_eq_kernel_add_nonKernel (X := X) (F g)
    rw [hrow g] at hp
    linear_combination hp.symm
  have hcol' (h : G) :
      (∑ g : G, if g ∉ kernelSet G X then F g h else 0) =
        -∑ g : G, if g ∈ kernelSet G X then F g h else 0 := by
    have hp := sum_eq_kernel_add_nonKernel (X := X) (fun g => F g h)
    rw [hcol h] at hp
    linear_combination hp.symm
  calc
    (∑ g : G, if g ∉ kernelSet G X then
        ∑ h : G, if h ∉ kernelSet G X then F g h else 0 else 0) =
        ∑ g : G, if g ∉ kernelSet G X then
          -(∑ h : G, if h ∈ kernelSet G X then F g h else 0) else 0 := by
            apply Finset.sum_congr rfl
            intro g _
            apply ite_congr rfl
            · intro _
              exact hrow' g
            · intro _
              rfl
    _ = -(∑ g : G, if g ∉ kernelSet G X then
          ∑ h : G, if h ∈ kernelSet G X then F g h else 0 else 0) := by
            rw [sum_ite_neg]
    _ = -(∑ h : G, if h ∈ kernelSet G X then
          ∑ g : G, if g ∉ kernelSet G X then F g h else 0 else 0) := by
            apply congrArg Neg.neg
            exact sum_ite_swap
              (fun g : G => g ∉ kernelSet G X)
              (fun h : G => h ∈ kernelSet G X) F
    _ = -(∑ h : G, if h ∈ kernelSet G X then
          -(∑ g : G, if g ∈ kernelSet G X then F g h else 0) else 0) := by
            apply congrArg Neg.neg
            apply Finset.sum_congr rfl
            intro h _
            apply ite_congr rfl
            · intro _
              exact hcol' h
            · intro _
              rfl
    _ = ∑ g : G, if g ∈ kernelSet G X then
          ∑ h : G, if h ∈ kernelSet G X then F g h else 0 else 0 := by
            rw [sum_ite_neg, neg_neg]
            exact sum_ite_swap
              (fun h : G => h ∈ kernelSet G X)
              (fun g : G => g ∈ kernelSet G X) (fun h g => F g h)

private theorem sum_twoSidedAverage_left_eq_zero
    {G : Type*} [Group G] [Fintype G]
    (e : MonoidAlgebra ℂ G) (hemean : ∑ g : G, e.coeff g = 0)
    (h : G) : ∑ g : G, twoSidedAverage e g h = 0 := by
  classical
  simp only [twoSidedAverage]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro x _
  let q : G ≃ G := Equiv.mulRight (x * h⁻¹ * x⁻¹)
  have hs := Equiv.sum_comp q (fun g : G => e.coeff g)
  simpa [q, mul_assoc] using hs.trans hemean

private theorem sum_twoSidedAverage_right_eq_zero
    {G : Type*} [Group G] [Fintype G]
    (e : MonoidAlgebra ℂ G) (hemean : ∑ g : G, e.coeff g = 0)
    (g : G) : ∑ h : G, twoSidedAverage e g h = 0 := by
  classical
  simp only [twoSidedAverage]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro x _
  let q : G ≃ G := ((Equiv.inv G).trans (Equiv.mulLeft (g * x))).trans
    (Equiv.mulRight x⁻¹)
  have hs := Equiv.sum_comp q (fun h : G => e.coeff h)
  simpa [q, mul_assoc] using hs.trans hemean

private theorem sum_kernel_twoSidedAverage
    {G X : Type*} [Group G] [Fintype G] [MulAction G X]
    [DecidablePred fun g : G => g ∈ kernelSet G X]
    (e : MonoidAlgebra ℂ G) :
    (∑ a : G, if a ∈ kernelSet G X then
        ∑ b : G, if b ∈ kernelSet G X then twoSidedAverage e a b else 0
      else 0) =
      (Fintype.card G : ℂ) *
        ∑ a : G, if a ∈ kernelSet G X then
          ∑ b : G, if b ∈ kernelSet G X then e.coeff (a * b⁻¹) else 0
        else 0 := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ kernelSet G X
  · rw [if_pos ha, if_pos ha]
    simp only [twoSidedAverage]
    have hswap :
        (∑ b : G, if b ∈ kernelSet G X then
          ∑ x : G, e.coeff (a * x * b⁻¹ * x⁻¹) else 0) =
        ∑ x : G, ∑ b : G, if b ∈ kernelSet G X then
          e.coeff (a * x * b⁻¹ * x⁻¹) else 0 := by
      simpa using (sum_ite_swap (fun b : G => b ∈ kernelSet G X)
        (fun _ : G => True) (fun b x => e.coeff (a * x * b⁻¹ * x⁻¹)))
    rw [hswap]
    have hinner (x : G) :
        (∑ b : G, if b ∈ kernelSet G X then
          e.coeff (a * x * b⁻¹ * x⁻¹) else 0) =
        ∑ b : G, if b ∈ kernelSet G X then e.coeff (a * b⁻¹) else 0 := by
      let q : G ≃ G := MulAut.conj x
      let F : G → ℂ := fun b =>
        if b ∈ kernelSet G X then e.coeff (a * b⁻¹) else 0
      have hs := Equiv.sum_comp q F
      calc
        (∑ b : G, if b ∈ kernelSet G X then
            e.coeff (a * x * b⁻¹ * x⁻¹) else 0) =
            ∑ b : G, F (q b) := by
              apply Finset.sum_congr rfl
              intro b _
              simp only [F, q]
              apply ite_congr (propext (kernelSet_conj x b).symm)
              · intro _
                change e.coeff (a * x * b⁻¹ * x⁻¹) =
                  e.coeff (a * (x * b * x⁻¹)⁻¹)
                congr 1
                simp [mul_assoc]
              · intro _
                rfl
        _ = ∑ b : G, F b := hs
        _ = ∑ b : G, if b ∈ kernelSet G X then
            e.coeff (a * b⁻¹) else 0 := rfl
    simp_rw [hinner]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  · simp [ha]

private theorem sum_prod_eq_four_blocks
    {L R : Type*} [Fintype L] [One L] [DecidableEq L]
    [AddCommMonoid R] (F : L → L → R) :
    (∑ p : L × L, F p.1 p.2) =
      F 1 1 + (∑ h : L, if h ≠ 1 then F 1 h else 0) +
        (∑ g : L, if g ≠ 1 then F g 1 else 0) +
          ∑ g : L, if g ≠ 1 then
            ∑ h : L, if h ≠ 1 then F g h else 0 else 0 := by
  classical
  rw [Fintype.sum_prod_type]
  rw [sum_eq_value_one_add]
  rw [sum_eq_value_one_add]
  simp only
  have hinner (g : L) := sum_eq_value_one_add (F g)
  have hrem :
      (∑ g : L, if g ≠ 1 then ∑ h : L, F g h else 0) =
      ∑ g : L, if g ≠ 1 then
        (F g 1 + ∑ h : L, if h ≠ 1 then F g h else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro g _
    apply ite_congr rfl
    · intro _
      exact hinner g
    · intro _
      rfl
  rw [hrem]
  have hsplit :
      (∑ g : L, if g ≠ 1 then
        (F g 1 + ∑ h : L, if h ≠ 1 then F g h else 0) else 0) =
      (∑ g : L, if g ≠ 1 then F g 1 else 0) +
        ∑ g : L, if g ≠ 1 then
          ∑ h : L, if h ≠ 1 then F g h else 0 else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro g _
    by_cases hg : g ≠ 1 <;> simp [hg]
  rw [hsplit]
  abel

private theorem second_trace_combination_eq_cross
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (H : Subgroup G) [Fintype H]
    (e : MonoidAlgebra ℂ G) (he : e ∈ Set.center (MonoidAlgebra ℂ G)) :
    (Fintype.card H : ℂ) *
        ((Fintype.card (H × H) : ℂ)⁻¹ *
          ∑ p : H × H, twoSidedAverage e p.1 p.2) -
      2 * ((Fintype.card H : ℂ)⁻¹ *
        ∑ h : H, ∑ _x : G, e.coeff h) =
    (Fintype.card H : ℂ)⁻¹ *
        (∑ g : H, if (g : G) ≠ 1 then
          ∑ h : H, if (h : G) ≠ 1 then twoSidedAverage e g h else 0
        else 0) -
      (Fintype.card H : ℂ)⁻¹ * Fintype.card G * e.coeff 1 := by
  classical
  let F : H → H → ℂ := fun g h => twoSidedAverage e g h
  let E : H → ℂ := fun h => e.coeff h
  have h11 : F 1 1 = (Fintype.card G : ℂ) * e.coeff 1 := by
    simp [F, twoSidedAverage, nsmul_eq_mul]
  have hrow :
      (∑ h : H, if (h : G) ≠ 1 then F h 1 else 0) =
        (Fintype.card G : ℂ) *
          ∑ h : H, if (h : G) ≠ 1 then E h else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    by_cases hh : (h : G) = 1
    · simp [hh]
    · rw [if_pos hh, if_pos hh]
      simp [F, E, twoSidedAverage, nsmul_eq_mul]
  have hinv :
      (∑ h : H, if (h : G) ≠ 1 then E h⁻¹ else 0) =
        ∑ h : H, if (h : G) ≠ 1 then E h else 0 := by
    let q : H ≃ H := Equiv.inv H
    let A : H → ℂ := fun h => if (h : G) ≠ 1 then E h else 0
    have hs := Equiv.sum_comp q A
    simpa [q, A] using hs
  have hcol :
      (∑ h : H, if (h : G) ≠ 1 then F 1 h else 0) =
        (Fintype.card G : ℂ) *
          ∑ h : H, if (h : G) ≠ 1 then E h else 0 := by
    calc
      (∑ h : H, if (h : G) ≠ 1 then F 1 h else 0) =
          ∑ h : H, if (h : G) ≠ 1 then
            (Fintype.card G : ℂ) * E h⁻¹ else 0 := by
              apply Finset.sum_congr rfl
              intro h _
              apply ite_congr rfl
              · intro _
                dsimp [F, E, twoSidedAverage]
                simp only [one_mul]
                have hc :
                    (∑ x : G, e.coeff (x * (h : G)⁻¹ * x⁻¹)) =
                      ∑ _x : G, e.coeff (h : G)⁻¹ := by
                  apply Finset.sum_congr rfl
                  intro x _
                  exact central_coeff_conj he x (h : G)⁻¹
                rw [hc]
                rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
              · intro _
                rfl
      _ = ∑ h : H, (Fintype.card G : ℂ) *
          (if (h : G) ≠ 1 then E h⁻¹ else 0) := by
            apply Finset.sum_congr rfl
            intro h _
            by_cases hh : (h : G) = 1 <;> simp [hh]
      _ = (Fintype.card G : ℂ) *
          ∑ h : H, if (h : G) ≠ 1 then E h⁻¹ else 0 := by
            rw [Finset.mul_sum]
      _ = _ := by rw [hinv]
  have hEpart := sum_eq_value_one_add E
  have hEpart' : (∑ h : H, E h) = e.coeff 1 +
      ∑ h : H, if (h : G) ≠ 1 then E h else 0 := by
    simpa [E] using hEpart
  have hL :
      (∑ h : H, ∑ _x : G, e.coeff h) =
        (Fintype.card G : ℂ) *
          (e.coeff 1 + ∑ h : H, if (h : G) ≠ 1 then E h else 0) := by
    rw [← hEpart']
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hprod := sum_prod_eq_four_blocks F
  change (∑ p : H × H, F p.1 p.2) = _ at hprod
  have hrow' :
      (∑ h : H, if h ≠ 1 then F h 1 else 0) =
        (Fintype.card G : ℂ) *
          ∑ h : H, if h ≠ 1 then E h else 0 := by simpa using hrow
  have hcol' :
      (∑ h : H, if h ≠ 1 then F 1 h else 0) =
        (Fintype.card G : ℂ) *
          ∑ h : H, if h ≠ 1 then E h else 0 := by simpa using hcol
  rw [h11, hcol', hrow'] at hprod
  let S : ℂ := ∑ h : H, if h ≠ 1 then E h else 0
  let C : ℂ := ∑ g : H, if g ≠ 1 then
    ∑ h : H, if h ≠ 1 then F g h else 0 else 0
  change (∑ p : H × H, F p.1 p.2) =
    (((Fintype.card G : ℂ) * e.coeff 1 +
      (Fintype.card G : ℂ) * S) +
      (Fintype.card G : ℂ) * S) + C at hprod
  have hL' :
      (∑ h : H, ∑ _x : G, e.coeff h) =
        (Fintype.card G : ℂ) * (e.coeff 1 + S) := by
    simpa [S] using hL
  have hcross :
      (∑ g : H, if (g : G) ≠ 1 then
        ∑ h : H, if (h : G) ≠ 1 then twoSidedAverage e g h else 0
      else 0) = C := by
    simp [C, F]
  rw [hcross]
  change _ * (_ * ∑ p : H × H, F p.1 p.2) -
      2 * (_ * ∑ h : H, ∑ _x : G, e.coeff h) = _
  rw [hprod, hL', Fintype.card_prod]
  push_cast
  have hH0 : (Fintype.card H : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos_iff.mpr ⟨1⟩))
  field_simp [hH0]
  ring

private theorem second_kernel_term_eq_trace_combination
    {G X : Type*} [Group G] [Fintype G] [Fintype X]
    [DecidableEq G] [DecidableEq X] [MulAction G X]
    [DecidablePred fun g : G => g ∈ kernelSet G X]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X,
      g • x = x → g • y = y → x = y)
    (x₀ : X) [Fintype (MulAction.stabilizer G x₀)]
    (e : MonoidAlgebra ℂ G) (he : e ∈ Set.center (MonoidAlgebra ℂ G))
    (hemean : ∑ g : G, e.coeff g = 0) :
    (Fintype.card X : ℂ)⁻¹ *
        (∑ a : G, if a ∈ kernelSet G X then
          ∑ b : G, if b ∈ kernelSet G X then e.coeff (a * b⁻¹) else 0
        else 0) -
      (Fintype.card (MulAction.stabilizer G x₀) : ℂ)⁻¹ *
        Fintype.card G * e.coeff 1 =
    (Fintype.card (MulAction.stabilizer G x₀) : ℂ) *
        ((Fintype.card (MulAction.stabilizer G x₀ ×
          MulAction.stabilizer G x₀) : ℂ)⁻¹ *
          ∑ p : MulAction.stabilizer G x₀ × MulAction.stabilizer G x₀,
            twoSidedAverage e p.1 p.2) -
      2 * ((Fintype.card (MulAction.stabilizer G x₀) : ℂ)⁻¹ *
        ∑ h : MulAction.stabilizer G x₀, ∑ _x : G, e.coeff h) := by
  classical
  let H := MulAction.stabilizer G x₀
  let F : G → G → ℂ := fun g h => twoSidedAverage e g h
  let B : ℂ := ∑ a : G, if a ∈ kernelSet G X then
    ∑ b : G, if b ∈ kernelSet G X then e.coeff (a * b⁻¹) else 0 else 0
  let C : ℂ := ∑ g : H, if (g : G) ≠ 1 then
    ∑ h : H, if (h : G) ≠ 1 then twoSidedAverage e g h else 0 else 0
  have hcount := sum_twoSided_nonKernel htrans hfrob x₀ e he
  have hzero := sum_nonKernel_nonKernel_eq_kernel_kernel (X := X) F
    (fun g => sum_twoSidedAverage_right_eq_zero e hemean g)
    (fun h => sum_twoSidedAverage_left_eq_zero e hemean h)
  have hkavg := sum_kernel_twoSidedAverage (X := X) e
  have hrel : ((Fintype.card X : ℂ) * Fintype.card X) * C =
      (Fintype.card G : ℂ) * B := by
    calc
      ((Fintype.card X : ℂ) * Fintype.card X) * C =
          (∑ g : G, if g ∉ kernelSet G X then
            ∑ h : G, if h ∉ kernelSet G X then
              twoSidedAverage e g h else 0 else 0) := by
                simpa [C, H] using hcount.symm
      _ = ∑ g : G, if g ∈ kernelSet G X then
            ∑ h : G, if h ∈ kernelSet G X then
              twoSidedAverage e g h else 0 else 0 := by
                simpa [F] using hzero
      _ = (Fintype.card G : ℂ) * B := by simpa [B] using hkavg
  let : MulAction.IsPretransitive G X :=
    (MulAction.isPretransitive_iff G X).mpr htrans
  have hgroup := Subgroup.card_mul_index H
  rw [MulAction.index_stabilizer_of_transitive G x₀] at hgroup
  simp only [Nat.card_eq_fintype_card] at hgroup
  have hgroupC : (Fintype.card G : ℂ) =
      Fintype.card X * Fintype.card H := by
    exact_mod_cast (by simpa [mul_comm] using hgroup.symm)
  rw [second_trace_combination_eq_cross H e he]
  change (Fintype.card X : ℂ)⁻¹ * B -
      (Fintype.card H : ℂ)⁻¹ * Fintype.card G * e.coeff 1 =
    (Fintype.card H : ℂ)⁻¹ * C -
      (Fintype.card H : ℂ)⁻¹ * Fintype.card G * e.coeff 1
  apply sub_left_inj.mpr
  have hX0 : (Fintype.card X : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos_iff.mpr ⟨x₀⟩))
  have hH0 : (Fintype.card H : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos_iff.mpr ⟨1⟩))
  rw [hgroupC] at hrel
  field_simp [hX0, hH0] at hrel ⊢
  rw [← hrel]

private theorem frobeniusQ_eq_int_of_mean_zero
    {G X : Type*} [Group G] [Fintype G] [Fintype X]
    [DecidableEq G] [DecidableEq X] [MulAction G X]
    [DecidablePred fun g : G => g ∈ kernelSet G X]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X,
      g • x = x → g • y = y → x = y)
    (x₀ : X) [Fintype (MulAction.stabilizer G x₀)]
    (e : MonoidAlgebra ℂ G) (he : e ∈ Set.center (MonoidAlgebra ℂ G))
    (hei : e * e = e) (hestar : groupAlgebraAdjoint e = e)
    (hemean : ∑ g : G, e.coeff g = 0) :
    ∃ z : ℤ, frobeniusQ (X := X) e = z := by
  classical
  let H := MulAction.stabilizer G x₀
  obtain ⟨nG, nH, nL, nHH, hnG, hnH, hnL, hnHH⟩ :=
    four_trace_quantities H e he hei hestar
  have hfirst := first_kernel_term_eq_trace_difference
    htrans hfrob x₀ e he
  have hsecond := second_kernel_term_eq_trace_combination
    htrans hfrob x₀ e he hemean
  let z : ℤ := (nG : ℤ) - nH -
    ((Fintype.card H : ℤ) * nHH - 2 * nL)
  refine ⟨z, ?_⟩
  unfold frobeniusQ
  let A : ℂ := ∑ a : G, if a ∈ kernelSet G X then
    twoSidedAverage e a a else 0
  let B : ℂ := ∑ a : G, if a ∈ kernelSet G X then
    ∑ b : G, if b ∈ kernelSet G X then e.coeff (a * b⁻¹) else 0 else 0
  let corr : ℂ := (Fintype.card H : ℂ)⁻¹ * Fintype.card G * e.coeff 1
  change (Fintype.card G : ℂ)⁻¹ * A -
      (Fintype.card X : ℂ)⁻¹ * B = (z : ℂ)
  calc
    (Fintype.card G : ℂ)⁻¹ * A -
        (Fintype.card X : ℂ)⁻¹ * B =
      ((Fintype.card G : ℂ)⁻¹ * A - corr) -
        ((Fintype.card X : ℂ)⁻¹ * B - corr) := by ring
    _ = ((Fintype.card G : ℂ)⁻¹ *
          ∑ g : G, twoSidedAverage e g g -
        (Fintype.card H : ℂ)⁻¹ *
          ∑ h : H, twoSidedAverage e h h) -
      ((Fintype.card H : ℂ) *
          ((Fintype.card (H × H) : ℂ)⁻¹ *
            ∑ p : H × H, twoSidedAverage e p.1 p.2) -
        2 * ((Fintype.card H : ℂ)⁻¹ *
          ∑ h : H, ∑ _x : G, e.coeff h)) := by
            rw [← hfirst, ← hsecond]
    _ = (nG : ℂ) - nH - ((Fintype.card H : ℂ) * nHH - 2 * nL) := by
      rw [hnG, hnH, hnHH, hnL]
    _ = (z : ℂ) := by
      simp only [z]
      push_cast
      ring

private theorem frobeniusQ_uniformCentralElement
    {G X : Type*} [Group G] [Fintype G] [Fintype X]
    [DecidableEq G] [DecidableEq X] [MulAction G X]
    [DecidablePred fun g : G => g ∈ kernelSet G X]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X,
      g • x = x → g • y = y → x = y)
    (x₀ : X) [Fintype (MulAction.stabilizer G x₀)] :
    frobeniusQ (X := X) (uniformCentralElement G) = 0 := by
  classical
  have hcardK := card_kernelFinset htrans hfrob x₀
  have hS :
      (∑ g : G, if g ∈ kernelSet G X then (1 : ℂ) else 0) =
        Fintype.card X := by
    calc
      (∑ g : G, if g ∈ kernelSet G X then (1 : ℂ) else 0) =
          ((kernelFinset G X).card : ℂ) := by
            simpa [kernelFinset] using (Finset.sum_boole (R := ℂ)
              (fun g : G => g ∈ kernelSet G X) Finset.univ)
      _ = Fintype.card X := by rw [hcardK]
  have hG0 : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos_iff.mpr ⟨1⟩))
  have hX0 : (Fintype.card X : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos_iff.mpr ⟨x₀⟩))
  have havg (a : G) :
      twoSidedAverage (uniformCentralElement G) a a = 1 := by
    simp [twoSidedAverage, uniformCentralElement_coeff, nsmul_eq_mul, hG0]
  have hA :
      (∑ a : G, if a ∈ kernelSet G X then
        twoSidedAverage (uniformCentralElement G) a a else 0) =
        Fintype.card X := by
    simpa [havg] using hS
  have hinner :
      (∑ b : G, if b ∈ kernelSet G X then
        (uniformCentralElement G).coeff b else 0) =
      (Fintype.card G : ℂ)⁻¹ * Fintype.card X := by
    simp only [uniformCentralElement_coeff]
    calc
      (∑ b : G, if b ∈ kernelSet G X then
          (Fintype.card G : ℂ)⁻¹ else 0) =
          ∑ b : G, (Fintype.card G : ℂ)⁻¹ *
            (if b ∈ kernelSet G X then (1 : ℂ) else 0) := by
              apply Finset.sum_congr rfl
              intro b _
              by_cases hb : b ∈ kernelSet G X <;> simp [hb]
      _ = (Fintype.card G : ℂ)⁻¹ *
          ∑ b : G, if b ∈ kernelSet G X then (1 : ℂ) else 0 := by
            rw [Finset.mul_sum]
      _ = _ := by rw [hS]
  have hB :
      (∑ a : G, if a ∈ kernelSet G X then
        ∑ b : G, if b ∈ kernelSet G X then
          (uniformCentralElement G).coeff (a * b⁻¹) else 0 else 0) =
      (Fintype.card X : ℂ) *
        ((Fintype.card G : ℂ)⁻¹ * Fintype.card X) := by
    have hi (a : G) :
        (∑ b : G, if b ∈ kernelSet G X then
          (uniformCentralElement G).coeff (a * b⁻¹) else 0) =
        (Fintype.card G : ℂ)⁻¹ * Fintype.card X := by
      simpa only [uniformCentralElement_coeff] using hinner
    simp_rw [hi]
    calc
      (∑ a : G, if a ∈ kernelSet G X then
          (Fintype.card G : ℂ)⁻¹ * Fintype.card X else 0) =
          ((Fintype.card G : ℂ)⁻¹ * Fintype.card X) *
            ∑ a : G, if a ∈ kernelSet G X then (1 : ℂ) else 0 := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro a _
              by_cases ha : a ∈ kernelSet G X <;> simp [ha]
      _ = _ := by rw [hS]; ring
  unfold frobeniusQ
  rw [hA, hB]
  field_simp [hG0, hX0]
  ring

private theorem frobeniusQ_basis_elem_eq_int
    {G X : Type*} [Group G] [Fintype G] [Fintype X]
    [DecidableEq G] [DecidableEq X] [MulAction G X]
    [DecidablePred fun g : G => g ∈ kernelSet G X]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X,
      g • x = x → g • y = y → x = y)
    (x₀ : X) [Fintype (MulAction.stabilizer G x₀)]
    (b : CentralIdempotentBasis (MonoidAlgebra ℂ G)) (i : Fin b.n) :
    ∃ z : ℤ, frobeniusQ (X := X) (b.elem i) = z := by
  classical
  by_cases hmean : ∑ g : G, (b.elem i).coeff g = 0
  · exact frobeniusQ_eq_int_of_mean_zero htrans hfrob x₀ (b.elem i)
      (b.central i) (by simpa using b.mul_elem i i) (b.adjoint_elem i) hmean
  · have heq := b.elem_eq_uniform_of_sum_coeff_ne_zero i hmean
    refine ⟨0, ?_⟩
    rw [heq, frobeniusQ_uniformCentralElement htrans hfrob x₀]
    norm_num

private def conjugacySum {G : Type*} [Group G] [Fintype G] (a : G) :
    MonoidAlgebra ℂ G :=
  ∑ x : G, MonoidAlgebra.single (x * a * x⁻¹) 1

private theorem conjugacySum_mem_center
    {G : Type*} [Group G] [Fintype G] (a : G) :
    conjugacySum a ∈ Set.center (MonoidAlgebra ℂ G) := by
  classical
  apply mem_center_of_coeff_conj
  intro y g
  let F : G → ℂ := fun x =>
    (MonoidAlgebra.single (x * a * x⁻¹) 1 : MonoidAlgebra ℂ G).coeff g
  have hs := Equiv.sum_comp (Equiv.mulLeft y⁻¹) F
  have hcoeff (z : G) : (conjugacySum a).coeff z =
      ∑ x : G, (MonoidAlgebra.single (x * a * x⁻¹) 1 :
        MonoidAlgebra ℂ G).coeff z := by
    simpa [conjugacySum] using (Finsupp.finset_sum_apply Finset.univ
      (fun x : G => (MonoidAlgebra.single (x * a * x⁻¹) 1 :
        MonoidAlgebra ℂ G)) z)
  rw [hcoeff, hcoeff]
  change (∑ x : G,
      (MonoidAlgebra.single (x * a * x⁻¹) 1 : MonoidAlgebra ℂ G).coeff
        (y * g * y⁻¹)) = ∑ x : G, F x
  rw [← hs]
  apply Finset.sum_congr rfl
  intro x _
  simp only [F, MonoidAlgebra.coeff_single_apply]
  change (if x * a * x⁻¹ = y * g * y⁻¹ then 1 else 0) =
    if (y⁻¹ * x) * a * (y⁻¹ * x)⁻¹ = g then 1 else 0
  have hiff : x * a * x⁻¹ = y * g * y⁻¹ ↔
      (y⁻¹ * x) * a * (y⁻¹ * x)⁻¹ = g := by
    constructor
    · intro h
      have h' := congrArg (fun z : G => y⁻¹ * z * y) h
      simpa [mul_assoc] using h'
    · intro h
      have h' := congrArg (fun z : G => y * z * y⁻¹) h
      simpa [mul_assoc] using h'
  rw [propext hiff]

private theorem basis_elem_twoSidedAverage_identity
    {G : Type*} [Group G] [Fintype G]
    (b : CentralIdempotentBasis (MonoidAlgebra ℂ G)) (i : Fin b.n)
    (a : G) :
    (b.elem i).coeff 1 * twoSidedAverage (b.elem i) a a =
      (Fintype.card G : ℂ) *
        ((b.elem i).coeff a * star ((b.elem i).coeff a)) := by
  classical
  let e := b.elem i
  let c := conjugacySum a
  obtain ⟨d, hd⟩ := b.span_center c (conjugacySum_mem_center a)
  have hec : e * c = d i • e := by
    rw [hd, Finset.mul_sum]
    simp [e, b.mul_elem]
  have hstar : e.coeff a⁻¹ = star (e.coeff a) := by
    have h := congrArg (fun z : MonoidAlgebra ℂ G => z.coeff a⁻¹)
      (b.adjoint_elem i)
    simpa [e] using h.symm
  have hsum_apply (z : G) :
      (∑ x : G, e * MonoidAlgebra.single (x * a * x⁻¹) 1).coeff z =
        ∑ x : G, (e * MonoidAlgebra.single (x * a * x⁻¹) 1).coeff z := by
    simpa using (Finsupp.finset_sum_apply Finset.univ
      (fun x : G => e * MonoidAlgebra.single (x * a * x⁻¹) 1) z)
  have hone : (e * c).coeff 1 =
      (Fintype.card G : ℂ) * star (e.coeff a) := by
    simp only [c, conjugacySum, Finset.mul_sum]
    rw [hsum_apply]
    change (∑ x : G,
      (e * MonoidAlgebra.single (x * a * x⁻¹) 1).coeff 1) = _
    simp only [MonoidAlgebra.coeff_mul_single_apply, one_mul]
    have hc (x : G) :
        e.coeff (x * a * x⁻¹)⁻¹ = star (e.coeff a) := by
      rw [show (x * a * x⁻¹)⁻¹ = x * a⁻¹ * x⁻¹ by simp [mul_assoc]]
      calc
        e.coeff (x * a⁻¹ * x⁻¹) = e.coeff a⁻¹ := by
          simpa [e, mul_assoc] using central_coeff_conj (b.central i) x a⁻¹
        _ = star (e.coeff a) := hstar
    simp_rw [hc]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have ha : (e * c).coeff a = twoSidedAverage e a a := by
    simp only [c, conjugacySum, Finset.mul_sum, twoSidedAverage]
    rw [hsum_apply]
    change (∑ x : G,
      (e * MonoidAlgebra.single (x * a * x⁻¹) 1).coeff a) = _
    simp only [MonoidAlgebra.coeff_mul_single_apply]
    congr 1
    funext x
    congr 2
    simp [mul_assoc]
  have hd_one := congrArg (fun z : MonoidAlgebra ℂ G => z.coeff 1) hec
  have hd_a := congrArg (fun z : MonoidAlgebra ℂ G => z.coeff a) hec
  change (e * c).coeff 1 = d i * e.coeff 1 at hd_one
  change (e * c).coeff a = d i * e.coeff a at hd_a
  rw [hone] at hd_one
  rw [ha] at hd_a
  change e.coeff 1 * twoSidedAverage e a a =
    (Fintype.card G : ℂ) * (e.coeff a * star (e.coeff a))
  calc
    e.coeff 1 * twoSidedAverage e a a =
        e.coeff 1 * (d i * e.coeff a) := by rw [hd_a]
    _ = (d i * e.coeff 1) * e.coeff a := by ring
    _ = ((Fintype.card G : ℂ) * star (e.coeff a)) * e.coeff a := by
      rw [← hd_one]
    _ = _ := by ring

def kernelAlgebra
    {G X : Type*} [Group G] [Fintype G] [MulAction G X]
    [DecidablePred fun g : G => g ∈ kernelSet G X] :
    MonoidAlgebra ℂ G :=
  ∑ g : G, if g ∈ kernelSet G X then MonoidAlgebra.single g 1 else 0

@[simp] theorem kernelAlgebra_coeff
    {G X : Type*} [Group G] [Fintype G] [MulAction G X]
    [DecidablePred fun g : G => g ∈ kernelSet G X] (g : G) :
    (kernelAlgebra (G := G) (X := X)).coeff g =
      if g ∈ kernelSet G X then 1 else 0 := by
  classical
  unfold kernelAlgebra
  let f : G → MonoidAlgebra ℂ G := fun u =>
    if u ∈ kernelSet G X then MonoidAlgebra.single u 1 else 0
  have hs : (∑ u : G, f u).coeff g = ∑ u : G, (f u).coeff g := by
    have h := MonoidAlgebra.coeff_sum (R := ℂ) (M := G) Finset.univ f
    calc
      (∑ u : G, f u).coeff g = (∑ u : G, (f u).coeff) g :=
        congrArg (fun z : G →₀ ℂ => z g) h
      _ = ∑ u : G, (f u).coeff g := by
        simpa using (Finsupp.finset_sum_apply Finset.univ
          (fun u : G => (f u).coeff) g)
  rw [show (∑ u : G, if u ∈ kernelSet G X then
      (MonoidAlgebra.single u 1 : MonoidAlgebra ℂ G) else 0).coeff g =
    ∑ u : G, (if u ∈ kernelSet G X then
      MonoidAlgebra.single u 1 else 0 : MonoidAlgebra ℂ G).coeff g by
        simpa [f] using hs]
  by_cases hg : g ∈ kernelSet G X
  · rw [if_pos hg]
    rw [Finset.sum_eq_single g]
    · simp [hg]
    · intro u _ hug
      by_cases hu : u ∈ kernelSet G X
      · simp [hu, hug]
      · simp [hu]
    · simp
  · rw [if_neg hg]
    apply Finset.sum_eq_zero
    intro u _
    by_cases hu : u ∈ kernelSet G X
    · have hug : u ≠ g := by
        intro h
        exact hg (h ▸ hu)
      simp [hu, hug]
    · simp [hu]

private theorem kernelAlgebra_mem_center
    {G X : Type*} [Group G] [Fintype G] [MulAction G X]
    [DecidablePred fun g : G => g ∈ kernelSet G X] :
    kernelAlgebra (G := G) (X := X) ∈
      Set.center (MonoidAlgebra ℂ G) := by
  classical
  apply mem_center_of_coeff_conj
  intro a g
  simp only [kernelAlgebra_coeff]
  by_cases hg : g ∈ kernelSet G X
  · have hc := (kernelSet_conj a g).mpr hg
    simp [hg, hc]
  · have hc : a * g * a⁻¹ ∉ kernelSet G X := by
      intro h
      exact hg ((kernelSet_conj a g).mp h)
    simp [hg, hc]

theorem groupAlgebraAdjoint_kernelAlgebra
    {G X : Type*} [Group G] [Fintype G] [MulAction G X]
    [DecidablePred fun g : G => g ∈ kernelSet G X] :
    groupAlgebraAdjoint (kernelAlgebra (G := G) (X := X)) =
      kernelAlgebra (G := G) (X := X) := by
  classical
  ext g
  simp only [groupAlgebraAdjoint_coeff, kernelAlgebra_coeff]
  by_cases hg : g ∈ kernelSet G X
  · have hi := (kernelSet_inv g).mpr hg
    simp [hg, hi]
  · have hi : g⁻¹ ∉ kernelSet G X := by
      intro h
      exact hg ((kernelSet_inv g).mp h)
    simp [hg, hi]

private theorem basis_elem_kernel_pair_identity
    {G X : Type*} [Group G] [Fintype G] [MulAction G X]
    [DecidablePred fun g : G => g ∈ kernelSet G X]
    (b : CentralIdempotentBasis (MonoidAlgebra ℂ G)) (i : Fin b.n) :
    (b.elem i).coeff 1 *
        (∑ a : G, if a ∈ kernelSet G X then
          ∑ d : G, if d ∈ kernelSet G X then
            (b.elem i).coeff (a * d⁻¹) else 0 else 0) =
      (∑ a : G, if a ∈ kernelSet G X then (b.elem i).coeff a else 0) *
        star (∑ a : G, if a ∈ kernelSet G X then
          (b.elem i).coeff a else 0) := by
  classical
  let e := b.elem i
  let z := kernelAlgebra (G := G) (X := X)
  let S : ℂ := ∑ a : G, if a ∈ kernelSet G X then e.coeff a else 0
  let B : ℂ := ∑ a : G, if a ∈ kernelSet G X then
    ∑ d : G, if d ∈ kernelSet G X then e.coeff (a * d⁻¹) else 0 else 0
  obtain ⟨c, hc⟩ := b.span_center z kernelAlgebra_mem_center
  have hez : e * z = c i • e := by
    rw [hc, Finset.mul_sum]
    simp [e, b.mul_elem]
  have hp (a : G) : (e * z).coeff a =
      ∑ d : G, if d ∈ kernelSet G X then e.coeff (a * d⁻¹) else 0 := by
    rw [groupAlgebra_coeff_mul_eq_sum]
    simp only [z, kernelAlgebra_coeff]
    let q : G ≃ G := (Equiv.inv G).trans (Equiv.mulLeft a)
    let F : G → ℂ := fun h =>
      e.coeff h * (if h⁻¹ * a ∈ kernelSet G X then 1 else 0)
    have hs := Equiv.sum_comp q F
    change (∑ h : G, F h) = _
    rw [← hs]
    apply Finset.sum_congr rfl
    intro d _
    simp only [F, q]
    change e.coeff (a * d⁻¹) *
      (if (a * d⁻¹)⁻¹ * a ∈ kernelSet G X then 1 else 0) = _
    rw [show (a * d⁻¹)⁻¹ * a = d by simp [mul_assoc]]
    by_cases hd : d ∈ kernelSet G X <;> simp [hd]
  have hS : (e * z).coeff 1 = S := by
    rw [hp]
    simp only [one_mul, S]
    let q : G ≃ G := Equiv.inv G
    let F : G → ℂ := fun d => if d ∈ kernelSet G X then e.coeff d else 0
    have hs := Equiv.sum_comp q F
    rw [← hs]
    apply Finset.sum_congr rfl
    intro d _
    simp only [F, q]
    by_cases hd : d ∈ kernelSet G X
    · have hi := (kernelSet_inv d).mpr hd
      simp [hd, hi]
    · have hi : d⁻¹ ∉ kernelSet G X := by
        intro h
        exact hd ((kernelSet_inv d).mp h)
      simp [hd, hi]
  have hB : B = c i * S := by
    have hpoint (a : G) :
        (∑ d : G, if d ∈ kernelSet G X then e.coeff (a * d⁻¹) else 0) =
          c i * e.coeff a := by
      have h := congrArg (fun u : MonoidAlgebra ℂ G => u.coeff a) hez
      change (e * z).coeff a = c i * e.coeff a at h
      exact (hp a).symm.trans h
    simp only [B]
    simp_rw [hpoint]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a ∈ kernelSet G X <;> simp [ha]
  have hci : S = c i * e.coeff 1 := by
    have h := congrArg (fun u : MonoidAlgebra ℂ G => u.coeff 1) hez
    change (e * z).coeff 1 = c i * e.coeff 1 at h
    exact hS.symm.trans h
  have hstar_coeff (a : G) : star (e.coeff a) = e.coeff a⁻¹ := by
    have h := congrArg (fun u : MonoidAlgebra ℂ G => u.coeff a⁻¹)
      (b.adjoint_elem i)
    simpa [e] using h
  have hSstar : star S = S := by
    let q : G ≃ G := Equiv.inv G
    let F : G → ℂ := fun a => if a ∈ kernelSet G X then e.coeff a else 0
    have hs := Equiv.sum_comp q F
    calc
      star S = ∑ a : G,
          star (if a ∈ kernelSet G X then e.coeff a else 0) := by
            simp [S]
      _ = ∑ a : G, F (q a) := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : a ∈ kernelSet G X
        · have hi := (kernelSet_inv a).mpr ha
          rw [if_pos ha]
          change star (e.coeff a) =
            (if a⁻¹ ∈ kernelSet G X then e.coeff a⁻¹ else 0)
          rw [if_pos hi, hstar_coeff]
        · have hi : a⁻¹ ∉ kernelSet G X := by
            intro hmem
            exact ha ((kernelSet_inv a).mp hmem)
          rw [if_neg ha]
          change star 0 =
            (if a⁻¹ ∈ kernelSet G X then e.coeff a⁻¹ else 0)
          rw [if_neg hi, star_zero]
      _ = ∑ a : G, F a := hs
      _ = S := rfl
  change e.coeff 1 * B = S * star S
  rw [hB, hSstar, hci]
  ring

private theorem coeff_one_mul_frobeniusQ_basis_elem
    {G X : Type*} [Group G] [Fintype G] [Fintype X]
    [MulAction G X]
    [DecidablePred fun g : G => g ∈ kernelSet G X]
    (b : CentralIdempotentBasis (MonoidAlgebra ℂ G)) (i : Fin b.n) :
    (b.elem i).coeff 1 * frobeniusQ (X := X) (b.elem i) =
      (∑ a : G, if a ∈ kernelSet G X then
          (b.elem i).coeff a * star ((b.elem i).coeff a) else 0) -
        (Fintype.card X : ℂ)⁻¹ *
          ((∑ a : G, if a ∈ kernelSet G X then
              (b.elem i).coeff a else 0) *
            star (∑ a : G, if a ∈ kernelSet G X then
              (b.elem i).coeff a else 0)) := by
  classical
  let e := b.elem i
  let A : ℂ := ∑ a : G, if a ∈ kernelSet G X then
    twoSidedAverage e a a else 0
  let C : ℂ := ∑ a : G, if a ∈ kernelSet G X then
    e.coeff a * star (e.coeff a) else 0
  let B : ℂ := ∑ a : G, if a ∈ kernelSet G X then
    ∑ d : G, if d ∈ kernelSet G X then
      e.coeff (a * d⁻¹) else 0 else 0
  let S : ℂ := ∑ a : G, if a ∈ kernelSet G X then e.coeff a else 0
  have hA : e.coeff 1 * A = (Fintype.card G : ℂ) * C := by
    simp only [A, C, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a ∈ kernelSet G X
    · simp only [if_pos ha]
      exact basis_elem_twoSidedAverage_identity b i a
    · simp [ha]
  have hB : e.coeff 1 * B = S * star S := by
    simpa only [e, B, S] using
      basis_elem_kernel_pair_identity (G := G) (X := X) b i
  have hG0 : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos_iff.mpr ⟨1⟩))
  change e.coeff 1 *
      ((Fintype.card G : ℂ)⁻¹ * A -
        (Fintype.card X : ℂ)⁻¹ * B) =
    C - (Fintype.card X : ℂ)⁻¹ * (S * star S)
  calc
    e.coeff 1 *
        ((Fintype.card G : ℂ)⁻¹ * A -
          (Fintype.card X : ℂ)⁻¹ * B) =
      (Fintype.card G : ℂ)⁻¹ * (e.coeff 1 * A) -
        (Fintype.card X : ℂ)⁻¹ * (e.coeff 1 * B) := by ring
    _ = (Fintype.card G : ℂ)⁻¹ *
          ((Fintype.card G : ℂ) * C) -
        (Fintype.card X : ℂ)⁻¹ * (S * star S) := by rw [hA, hB]
    _ = C - (Fintype.card X : ℂ)⁻¹ * (S * star S) := by
      field_simp [hG0]

private theorem sum_normSq_sub_average_cast
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ)
    (hs : s.card ≠ 0) :
    ((∑ a ∈ s, Complex.normSq
        (f a - (s.card : ℂ)⁻¹ * ∑ d ∈ s, f d) : ℝ) : ℂ) =
      (∑ a ∈ s, f a * star (f a)) -
        (s.card : ℂ)⁻¹ *
          ((∑ a ∈ s, f a) * star (∑ a ∈ s, f a)) := by
  let S : ℂ := ∑ a ∈ s, f a
  let n : ℂ := s.card
  let m : ℂ := n⁻¹ * S
  have hn : n ≠ 0 := by
    change (s.card : ℂ) ≠ 0
    exact_mod_cast hs
  have hstarS : (∑ a ∈ s, star (f a)) = star S := by
    simp [S]
  have hstarm : star m = n⁻¹ * star S := by
    simp [m, n]
  calc
    ((∑ a ∈ s, Complex.normSq
        (f a - (s.card : ℂ)⁻¹ * ∑ d ∈ s, f d) : ℝ) : ℂ) =
      ∑ a ∈ s, ((Complex.normSq (f a - m) : ℝ) : ℂ) := by
        simp [m, n, S]
    _ = ∑ a ∈ s, (f a - m) * star (f a - m) := by
      apply Finset.sum_congr rfl
      intro a _
      exact (Complex.mul_conj (f a - m)).symm
    _ = ∑ a ∈ s,
        (f a * star (f a) - f a * star m -
          m * star (f a) + m * star m) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [star_sub]
      ring
    _ = (∑ a ∈ s, f a * star (f a)) -
        S * star m - m * star S + (s.card : ℂ) * (m * star m) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.sum_const, nsmul_eq_mul]
      rw [← Finset.sum_mul, ← Finset.mul_sum, hstarS]
    _ = (∑ a ∈ s, f a * star (f a)) -
        n⁻¹ * (S * star S) := by
      rw [hstarm]
      change (∑ a ∈ s, f a * star (f a)) -
          S * (n⁻¹ * star S) - (n⁻¹ * S) * star S +
            n * ((n⁻¹ * S) * (n⁻¹ * star S)) = _
      field_simp [hn]
      ring

private theorem sum_normSq_sub_average
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ)
    (hs : s.card ≠ 0) :
    (∑ a ∈ s, Complex.normSq
        (f a - (s.card : ℂ)⁻¹ * ∑ d ∈ s, f d) : ℝ) =
      (∑ a ∈ s, Complex.normSq (f a)) -
        (s.card : ℝ)⁻¹ * Complex.normSq (∑ a ∈ s, f a) := by
  apply Complex.ofReal_injective
  rw [sum_normSq_sub_average_cast s f hs]
  have hC : (∑ a ∈ s, f a * star (f a)) =
      ((∑ a ∈ s, Complex.normSq (f a) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro a _
    exact Complex.mul_conj (f a)
  have hS : (∑ a ∈ s, f a) * star (∑ a ∈ s, f a) =
      (Complex.normSq (∑ a ∈ s, f a) : ℂ) :=
    Complex.mul_conj _
  rw [hC, hS]
  push_cast
  ring

private def kernelVariance
    {G X : Type*} [Group G] [Fintype G] [Fintype X]
    [MulAction G X]
    [DecidablePred fun g : G => g ∈ kernelSet G X]
    (e : MonoidAlgebra ℂ G) : ℝ :=
  ∑ a ∈ kernelFinset G X, Complex.normSq
    (e.coeff a - (Fintype.card X : ℂ)⁻¹ *
      ∑ d ∈ kernelFinset G X, e.coeff d)

private theorem coeff_one_mul_frobeniusQ_eq_kernelVariance
    {G X : Type*} [Group G] [Fintype G] [Fintype X]
    [MulAction G X]
    [DecidablePred fun g : G => g ∈ kernelSet G X]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X,
      g • x = x → g • y = y → x = y)
    (x₀ : X) [Fintype (MulAction.stabilizer G x₀)]
    (b : CentralIdempotentBasis (MonoidAlgebra ℂ G)) (i : Fin b.n) :
    (b.elem i).coeff 1 * frobeniusQ (X := X) (b.elem i) =
      (kernelVariance (G := G) (X := X) (b.elem i) : ℂ) := by
  classical
  have hcard := card_kernelFinset htrans hfrob x₀
  have hne : (kernelFinset G X).card ≠ 0 := by
    rw [hcard]
    exact ne_of_gt (Fintype.card_pos_iff.mpr ⟨x₀⟩)
  have hv := sum_normSq_sub_average_cast
    (kernelFinset G X) (fun a : G => (b.elem i).coeff a) hne
  rw [hcard] at hv
  rw [coeff_one_mul_frobeniusQ_basis_elem]
  symm
  simpa only [kernelVariance, kernelFinset, Finset.sum_filter] using hv

private theorem basis_elem_coeff_one_eq_sum_normSq
    {G : Type*} [Group G] [Fintype G]
    (b : CentralIdempotentBasis (MonoidAlgebra ℂ G)) (i : Fin b.n) :
    (b.elem i).coeff 1 =
      ((∑ g : G, Complex.normSq ((b.elem i).coeff g) : ℝ) : ℂ) := by
  classical
  let e := b.elem i
  have hei : e * e = e := by simpa [e] using b.mul_elem i i
  have hcoeff := congrArg (fun z : MonoidAlgebra ℂ G => z.coeff 1) hei
  rw [groupAlgebra_coeff_mul_eq_sum] at hcoeff
  have hstar (g : G) : e.coeff g⁻¹ = star (e.coeff g) := by
    have h := congrArg (fun z : MonoidAlgebra ℂ G => z.coeff g⁻¹)
      (b.adjoint_elem i)
    simpa [e] using h.symm
  simp only [mul_one, hstar] at hcoeff
  calc
    e.coeff 1 = ∑ g : G, e.coeff g * star (e.coeff g) := hcoeff.symm
    _ = ∑ g : G, (Complex.normSq (e.coeff g) : ℂ) := by
      apply Finset.sum_congr rfl
      intro g _
      exact Complex.mul_conj _
    _ = ((∑ g : G, Complex.normSq (e.coeff g) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]

private theorem kernelVariance_nonneg
    {G X : Type*} [Group G] [Fintype G] [Fintype X]
    [MulAction G X]
    [DecidablePred fun g : G => g ∈ kernelSet G X]
    (e : MonoidAlgebra ℂ G) :
    0 ≤ kernelVariance (G := G) (X := X) e := by
  classical
  unfold kernelVariance
  exact Finset.sum_nonneg fun a _ => Complex.normSq_nonneg _

private theorem kernelVariance_le_total_normSq
    {G X : Type*} [Group G] [Fintype G] [Fintype X]
    [MulAction G X]
    [DecidablePred fun g : G => g ∈ kernelSet G X]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X,
      g • x = x → g • y = y → x = y)
    (x₀ : X) [Fintype (MulAction.stabilizer G x₀)]
    (e : MonoidAlgebra ℂ G) :
    kernelVariance (G := G) (X := X) e ≤
      ∑ g : G, Complex.normSq (e.coeff g) := by
  classical
  let K := kernelFinset G X
  let S : ℂ := ∑ a ∈ K, e.coeff a
  have hcard := card_kernelFinset htrans hfrob x₀
  have hne : K.card ≠ 0 := by
    change (kernelFinset G X).card ≠ 0
    rw [hcard]
    exact ne_of_gt (Fintype.card_pos_iff.mpr ⟨x₀⟩)
  have hv := sum_normSq_sub_average K (fun a : G => e.coeff a) hne
  have hmean_nonneg :
      0 ≤ (K.card : ℝ)⁻¹ * Complex.normSq S :=
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Complex.normSq_nonneg _)
  have hVK : kernelVariance (G := G) (X := X) e ≤
      ∑ a ∈ K, Complex.normSq (e.coeff a) := by
    rw [show kernelVariance (G := G) (X := X) e =
        ∑ a ∈ K, Complex.normSq
          (e.coeff a - (K.card : ℂ)⁻¹ * ∑ d ∈ K, e.coeff d) by
      simp only [kernelVariance, K, hcard]]
    rw [hv]
    exact sub_le_self _ hmean_nonneg
  calc
    kernelVariance (G := G) (X := X) e ≤
        ∑ a ∈ K, Complex.normSq (e.coeff a) := hVK
    _ ≤ ∑ g : G, Complex.normSq (e.coeff g) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.subset_univ K
      · intro g _ _
        exact Complex.normSq_nonneg _

private theorem basis_elem_kernel_dichotomy
    {G X : Type*} [Group G] [Fintype G] [Fintype X]
    [MulAction G X]
    [DecidablePred fun g : G => g ∈ kernelSet G X]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X,
      g • x = x → g • y = y → x = y)
    (x₀ : X) [Fintype (MulAction.stabilizer G x₀)]
    (b : CentralIdempotentBasis (MonoidAlgebra ℂ G)) (i : Fin b.n) :
    (∀ a : G, a ∈ kernelSet G X →
        (b.elem i).coeff a = (Fintype.card X : ℂ)⁻¹ *
          ∑ d ∈ kernelFinset G X, (b.elem i).coeff d) ∨
      ((∀ a : G, a ∉ kernelSet G X → (b.elem i).coeff a = 0) ∧
        (∑ d ∈ kernelFinset G X, (b.elem i).coeff d) = 0) := by
  classical
  let e := b.elem i
  let K := kernelFinset G X
  let S : ℂ := ∑ d ∈ K, e.coeff d
  let V : ℝ := kernelVariance (G := G) (X := X) e
  obtain ⟨z, hz⟩ := frobeniusQ_basis_elem_eq_int
    htrans hfrob x₀ b i
  obtain ⟨r, hr, hre⟩ := b.coeff_one_eq_pos_real i
  have hrvC : (r : ℂ) * (z : ℂ) = (V : ℂ) := by
    rw [← hre, ← hz]
    exact coeff_one_mul_frobeniusQ_eq_kernelVariance
      htrans hfrob x₀ b i
  have hrv : r * (z : ℝ) = V := by
    exact_mod_cast hrvC
  have hV0 : 0 ≤ V := kernelVariance_nonneg e
  have hVle : V ≤ ∑ g : G, Complex.normSq (e.coeff g) :=
    kernelVariance_le_total_normSq htrans hfrob x₀ e
  have htotal : (∑ g : G, Complex.normSq (e.coeff g) : ℝ) = r := by
    have h := basis_elem_coeff_one_eq_sum_normSq b i
    rw [hre] at h
    exact_mod_cast h.symm
  have hz0R : (0 : ℝ) ≤ (z : ℝ) := by
    nlinarith
  have hz1R : (z : ℝ) ≤ 1 := by
    rw [htotal] at hVle
    nlinarith
  have hz0 : (0 : ℤ) ≤ z := (Int.cast_le (R := ℝ)).mp (by simpa using hz0R)
  have hz1 : z ≤ (1 : ℤ) := (Int.cast_le (R := ℝ)).mp (by simpa using hz1R)
  have hz_cases : z = 0 ∨ z = 1 := by omega
  rcases hz_cases with hz_zero | hz_one
  · left
    intro a ha
    have hVzero : V = 0 := by
      rw [hz_zero] at hrv
      simpa using hrv.symm
    have hsumzero :
        (∑ d ∈ K, Complex.normSq
          (e.coeff d - (Fintype.card X : ℂ)⁻¹ * S) : ℝ) = 0 := by
      simpa only [V, kernelVariance, K, S, e] using hVzero
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun d (_hd : d ∈ K) => Complex.normSq_nonneg
        (e.coeff d - (Fintype.card X : ℂ)⁻¹ * S))).mp hsumzero
    have haK : a ∈ K := by simpa only [K, mem_kernelFinset] using ha
    have hdiff := Complex.normSq_eq_zero.mp (hall a haK)
    simpa only [e, K, S] using sub_eq_zero.mp hdiff
  · right
    have hVeq : V = r := by
      rw [hz_one] at hrv
      simpa using hrv.symm
    have hcard := card_kernelFinset htrans hfrob x₀
    have hne : K.card ≠ 0 := by
      change (kernelFinset G X).card ≠ 0
      rw [hcard]
      exact ne_of_gt (Fintype.card_pos_iff.mpr ⟨x₀⟩)
    have hv := sum_normSq_sub_average K (fun a : G => e.coeff a) hne
    have hvform : V =
        (∑ a ∈ K, Complex.normSq (e.coeff a)) -
          (Fintype.card X : ℝ)⁻¹ * Complex.normSq S := by
      rw [show K.card = Fintype.card X by simpa only [K] using hcard] at hv
      simpa only [V, kernelVariance, K, S] using hv
    let O : ℝ := ∑ g : G,
      if g ∉ kernelSet G X then Complex.normSq (e.coeff g) else 0
    have hpart : (∑ g : G, Complex.normSq (e.coeff g) : ℝ) =
        (∑ a ∈ K, Complex.normSq (e.coeff a)) + O := by
      have h := sum_eq_kernel_add_nonKernel (X := X)
        (fun g : G => Complex.normSq (e.coeff g))
      simpa only [K, O, kernelFinset, Finset.sum_filter] using h
    have hO0 : 0 ≤ O := by
      apply Finset.sum_nonneg
      intro g _
      by_cases hg : g ∈ kernelSet G X
      · simp [hg]
      · simp [hg, Complex.normSq_nonneg]
    have hmean0 : 0 ≤ (Fintype.card X : ℝ)⁻¹ * Complex.normSq S :=
      mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (Complex.normSq_nonneg _)
    have hbalance : O +
        (Fintype.card X : ℝ)⁻¹ * Complex.normSq S = 0 := by
      rw [← htotal] at hVeq
      nlinarith [hpart]
    have hOzero : O = 0 := by nlinarith
    have hmeanzero :
        (Fintype.card X : ℝ)⁻¹ * Complex.normSq S = 0 := by
      nlinarith
    constructor
    · intro a ha
      have hall := (Finset.sum_eq_zero_iff_of_nonneg
        (s := Finset.univ)
        (f := fun g : G => if g ∉ kernelSet G X then
          Complex.normSq (e.coeff g) else 0)
        (fun g _ => by
          by_cases hg : g ∈ kernelSet G X
          · simp [hg]
          · simp [hg, Complex.normSq_nonneg])).mp hOzero
      have hnorm : Complex.normSq (e.coeff a) = 0 := by
        simpa [ha] using hall a (Finset.mem_univ a)
      simpa only [e] using Complex.normSq_eq_zero.mp hnorm
    · have hX0R : (Fintype.card X : ℝ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (Fintype.card_pos_iff.mpr ⟨x₀⟩))
      have hnorm : Complex.normSq S = 0 :=
        (mul_eq_zero.mp hmeanzero).resolve_left (inv_ne_zero hX0R)
      simpa only [K, S, e] using Complex.normSq_eq_zero.mp hnorm

private theorem coeff_one_mul_eq_zero_of_constant_kernel
    {G X : Type*} [Group G] [Fintype G] [MulAction G X]
    [DecidablePred fun g : G => g ∈ kernelSet G X]
    (z e : MonoidAlgebra ℂ G)
    (hz : ∀ a : G, a ∈ kernelSet G X → z.coeff a = z.coeff 1)
    (hesupp : ∀ a : G, a ∉ kernelSet G X → e.coeff a = 0)
    (hesum : (∑ a ∈ kernelFinset G X, e.coeff a) = 0) :
    (z * e).coeff 1 = 0 := by
  classical
  have hinvsum :
      (∑ a : G, if a ∈ kernelSet G X then e.coeff a⁻¹ else 0) = 0 := by
    let F : G → ℂ := fun a =>
      if a ∈ kernelSet G X then e.coeff a else 0
    have hs := Equiv.sum_comp (Equiv.inv G) F
    calc
      (∑ a : G, if a ∈ kernelSet G X then e.coeff a⁻¹ else 0) =
          ∑ a : G, F a⁻¹ := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : a ∈ kernelSet G X
        · have hi := (kernelSet_inv a).mpr ha
          simp only [F, if_pos ha, if_pos hi]
        · have hi : a⁻¹ ∉ kernelSet G X := by
            intro h
            exact ha ((kernelSet_inv a).mp h)
          simp only [F, if_neg ha, if_neg hi]
      _ = ∑ a : G, F a := hs
      _ = ∑ a ∈ kernelFinset G X, e.coeff a := by
        simp only [F, kernelFinset, Finset.sum_filter]
      _ = 0 := hesum
  rw [groupAlgebra_coeff_mul_eq_sum]
  simp only [mul_one]
  calc
    (∑ a : G, z.coeff a * e.coeff a⁻¹) =
        ∑ a : G, z.coeff 1 *
          (if a ∈ kernelSet G X then e.coeff a⁻¹ else 0) := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a ∈ kernelSet G X
      · rw [if_pos ha, hz a ha]
      · have hi : a⁻¹ ∉ kernelSet G X := by
          intro h
          exact ha ((kernelSet_inv a).mp h)
        rw [if_neg ha, hesupp a⁻¹ hi, mul_zero, mul_zero]
    _ = z.coeff 1 *
        ∑ a : G, if a ∈ kernelSet G X then e.coeff a⁻¹ else 0 := by
      rw [Finset.mul_sum]
    _ = 0 := by rw [hinvsum, mul_zero]

private theorem square_coeff_constant_on_kernel
    {G X : Type*} [Group G] [Fintype G] [Fintype X]
    [MulAction G X]
    [DecidablePred fun g : G => g ∈ kernelSet G X]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X,
      g • x = x → g • y = y → x = y)
    (x₀ : X) [Fintype (MulAction.stabilizer G x₀)]
    (b : CentralIdempotentBasis (MonoidAlgebra ℂ G))
    (z : MonoidAlgebra ℂ G) (hzcenter : z ∈ Set.center (MonoidAlgebra ℂ G))
    (hz : ∀ a : G, a ∈ kernelSet G X → z.coeff a = z.coeff 1) :
    ∀ a d : G, a ∈ kernelSet G X → d ∈ kernelSet G X →
      (z * z).coeff a = (z * z).coeff d := by
  classical
  obtain ⟨c, hc⟩ := b.span_center z hzcenter
  have hze (i : Fin b.n) : z * b.elem i = c i • b.elem i := by
    rw [hc, Finset.sum_mul]
    simp [b.mul_elem]
  have hcbad (i : Fin b.n)
      (hsupp : ∀ a : G, a ∉ kernelSet G X → (b.elem i).coeff a = 0)
      (hsum : (∑ a ∈ kernelFinset G X, (b.elem i).coeff a) = 0) :
      c i = 0 := by
    have hzero := coeff_one_mul_eq_zero_of_constant_kernel
      z (b.elem i) hz hsupp hsum
    have h := congrArg (fun u : MonoidAlgebra ℂ G => u.coeff 1) (hze i)
    change (z * b.elem i).coeff 1 = c i * (b.elem i).coeff 1 at h
    rw [hzero] at h
    obtain ⟨r, hr, hre⟩ := b.coeff_one_eq_pos_real i
    have hcoeff : (b.elem i).coeff 1 ≠ 0 := by
      rw [hre]
      exact_mod_cast (ne_of_gt hr)
    exact (mul_eq_zero.mp h.symm).resolve_right hcoeff
  have hzz : z * z = ∑ i : Fin b.n, (c i * c i) • b.elem i := by
    calc
      z * z = z * (∑ i : Fin b.n, c i • b.elem i) :=
        congrArg (fun u : MonoidAlgebra ℂ G => z * u) hc
      _ = ∑ i : Fin b.n, z * (c i • b.elem i) := by
        rw [Finset.mul_sum]
      _ = ∑ i : Fin b.n, (c i * c i) • b.elem i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [mul_smul_comm, hze, smul_smul]
  have hcoeff (g : G) : (z * z).coeff g =
      ∑ i : Fin b.n, (c i * c i) * (b.elem i).coeff g := by
    rw [hzz]
    simpa using (Finsupp.finset_sum_apply Finset.univ
      (fun i : Fin b.n => (c i * c i) • b.elem i) g)
  intro a d ha hd
  rw [hcoeff, hcoeff]
  apply Finset.sum_congr rfl
  intro i _
  rcases basis_elem_kernel_dichotomy htrans hfrob x₀ b i with hconst | hbad
  · rw [hconst a ha, hconst d hd]
  · have hci := hcbad i hbad.1 hbad.2
    simp [hci]

private theorem kernelAlgebra_square_coeff_card_filter
    {G X : Type*} [Group G] [Fintype G] [MulAction G X]
    [DecidablePred fun g : G => g ∈ kernelSet G X]
    (g : G) :
    (kernelAlgebra (G := G) (X := X) *
      kernelAlgebra (G := G) (X := X)).coeff g =
      (((kernelFinset G X).filter
        (fun h : G => h⁻¹ * g ∈ kernelSet G X)).card : ℂ) := by
  classical
  let P := (kernelFinset G X).filter
    (fun h : G => h⁻¹ * g ∈ kernelSet G X)
  have hcard : P.card = ∑ h : G,
      if h ∈ kernelSet G X ∧ h⁻¹ * g ∈ kernelSet G X then 1 else 0 := by
    simp only [P]
    rw [Finset.card_filter]
    simp only [kernelFinset, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro h _
    by_cases hh : h ∈ kernelSet G X <;>
      by_cases hg : h⁻¹ * g ∈ kernelSet G X <;> simp [hh, hg]
  rw [groupAlgebra_coeff_mul_eq_sum]
  simp only [kernelAlgebra_coeff]
  calc
    (∑ h : G, (if h ∈ kernelSet G X then (1 : ℂ) else 0) *
        (if h⁻¹ * g ∈ kernelSet G X then 1 else 0)) =
      ∑ h : G,
        if h ∈ kernelSet G X ∧ h⁻¹ * g ∈ kernelSet G X then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro h _
        by_cases hh : h ∈ kernelSet G X <;>
          by_cases hg : h⁻¹ * g ∈ kernelSet G X <;> simp [hh, hg]
    _ = (P.card : ℂ) := by exact_mod_cast hcard.symm

private theorem kernelSet_mul
    {G X : Type*} [Group G] [Fintype G] [Fintype X]
    [MulAction G X]
    [DecidablePred fun g : G => g ∈ kernelSet G X]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X,
      g • x = x → g • y = y → x = y)
    (x₀ : X) [Fintype (MulAction.stabilizer G x₀)]
    (cb : CentralIdempotentBasis (MonoidAlgebra ℂ G))
    {a d : G} (ha : a ∈ kernelSet G X) (hd : d ∈ kernelSet G X) :
    a * d ∈ kernelSet G X := by
  classical
  let z := kernelAlgebra (G := G) (X := X)
  have hone : (1 : G) ∈ kernelSet G X := Or.inl rfl
  have hz : ∀ g : G, g ∈ kernelSet G X → z.coeff g = z.coeff 1 := by
    intro g hg
    simp only [z, kernelAlgebra_coeff, if_pos hg, if_pos hone]
  have hsquare := square_coeff_constant_on_kernel
    htrans hfrob x₀ cb z kernelAlgebra_mem_center hz d 1 hd hone
  let K := kernelFinset G X
  let P := K.filter (fun h : G => h⁻¹ * d ∈ kernelSet G X)
  have hfilter_one :
      K.filter (fun h : G => h⁻¹ * 1 ∈ kernelSet G X) = K := by
    apply Finset.filter_eq_self.mpr
    intro h hh
    have hm : h ∈ kernelSet G X := by
      simpa only [K, mem_kernelFinset] using hh
    have hi := (kernelSet_inv h).mpr hm
    simpa only [mul_one] using hi
  have hcardC : (P.card : ℂ) = (K.card : ℂ) := by
    calc
      (P.card : ℂ) = (z * z).coeff d := by
        symm
        simpa only [z, K, P] using
          (kernelAlgebra_square_coeff_card_filter (G := G) (X := X) d)
      _ = (z * z).coeff 1 := hsquare
      _ = ((K.filter
          (fun h : G => h⁻¹ * 1 ∈ kernelSet G X)).card : ℂ) := by
        simpa only [z, K] using
          (kernelAlgebra_square_coeff_card_filter (G := G) (X := X) (1 : G))
      _ = (K.card : ℂ) := by rw [hfilter_one]
  have hcard : P.card = K.card := by exact_mod_cast hcardC
  have hall : ∀ h ∈ K, h⁻¹ * d ∈ kernelSet G X := by
    exact (Finset.card_filter_eq_iff.mp (by simpa only [P] using hcard))
  have hainv : a⁻¹ ∈ K := by
    simp only [K, mem_kernelFinset]
    exact (kernelSet_inv a).mpr ha
  have h := hall a⁻¹ hainv
  simpa only [inv_inv] using h

theorem frobenius_kernel_isNormal
    (G X : Type) [Group G] [Fintype G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : 2 ≤ Fintype.card X)
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (hstab : ∀ x : X, MulAction.stabilizer G x ≠ ⊥)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X,
      g • x = x → g • y = y → x = y) :
    ∃ N : Subgroup G, N.Normal ∧
      (N : Set G) = {1} ∪ {g : G | ∀ x : X, g • x ≠ x} := by
  classical
  have hXpos : 0 < Fintype.card X := by omega
  obtain ⟨x₀⟩ := Fintype.card_pos_iff.mp hXpos
  obtain ⟨cb⟩ := groupAlgebra_centralIdempotentBasis G
  let N : Subgroup G :=
    { carrier := kernelSet G X
      one_mem' := Or.inl rfl
      mul_mem' := fun ha hd => kernelSet_mul htrans hfrob x₀ cb ha hd
      inv_mem' := fun ha => (kernelSet_inv _).mpr ha }
  have hnormal : N.Normal := by
    apply (Subgroup.normal_iff_map_conj_eq).2
    intro a
    ext g
    change g ∈ N.map (MulAut.conj a).toMonoidHom ↔ g ∈ N
    rw [Subgroup.mem_map_equiv]
    change a⁻¹ * g * a ∈ kernelSet G X ↔ g ∈ kernelSet G X
    simpa only [inv_inv] using
      (kernelSet_conj (G := G) (X := X) a⁻¹ g)
  refine ⟨N, hnormal, ?_⟩
  change kernelSet G X = {1} ∪ {g : G | ∀ x : X, g • x ≠ x}
  ext g
  simp only [mem_kernelSet, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_setOf_eq]

end

end FrobeniusKernel.Frobenius

end CFSG
