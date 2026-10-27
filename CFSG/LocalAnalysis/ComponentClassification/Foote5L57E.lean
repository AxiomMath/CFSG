module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.Foote5HaradaE16A
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup Equiv

variable {G : Type} [Group G] [Finite G]

theorem exists_commute_of_coprime {p : ℕ} [Fact p.Prime] {P N : Subgroup G} (hP : IsPGroup p P)
    (hN : ¬ p ∣ Nat.card N) (hPN : ∀ x ∈ P, ∀ n ∈ N, x * n * x⁻¹ ∈ N) {y : G}
    (hy : ∀ x ∈ P, y⁻¹ * (x * y * x⁻¹) ∈ N) :
    ∃ y' : G, y⁻¹ * y' ∈ N ∧ ∀ x ∈ P, x * y' = y' * x := by
  classical
  let _ : MulAction P G := MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp P.subtype)
  have hsmul : ∀ (x : P) (g : G), x • g = (x : G) * g * (x : G)⁻¹ := fun x g => rfl
  let S : SubMulAction P G :=
    { carrier := {g | y⁻¹ * g ∈ N}
      smul_mem' := by
        intro x g hg
        change y⁻¹ * (x • g) ∈ N
        rw [hsmul, show y⁻¹ * ((x : G) * g * (x : G)⁻¹) =
          (y⁻¹ * ((x : G) * y * (x : G)⁻¹)) * ((x : G) * (y⁻¹ * g) * (x : G)⁻¹) by group]
        exact mul_mem (hy x x.2) (hPN x x.2 _ hg) }
  have hcard : Nat.card S = Nat.card N := by
    refine Nat.card_congr
      { toFun := fun g => ⟨y⁻¹ * (g : G), g.2⟩
        invFun := fun n => ⟨y * (n : G), by
          change y⁻¹ * (y * (n : G)) ∈ N
          rw [← mul_assoc, inv_mul_cancel, one_mul]
          exact n.2⟩
        left_inv := fun g => by
          apply Subtype.ext
          change y * (y⁻¹ * (g : G)) = g
          group
        right_inv := fun n => by
          apply Subtype.ext
          change y⁻¹ * (y * (n : G)) = n
          group }
  have hmod := hP.card_modEq_card_fixedPoints S
  have hne : (MulAction.fixedPoints P S).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have h0 : Nat.card (MulAction.fixedPoints P S) = 0 := by
      rw [hemp]
      simp
    rw [h0, hcard] at hmod
    exact hN (Nat.modEq_zero_iff_dvd.mp hmod)
  obtain ⟨⟨y', hy'⟩, hfix⟩ := hne
  refine ⟨y', hy', fun x hx => ?_⟩
  have h1 : (x : G) * y' * x⁻¹ = y' := by
    have h2 := congrArg Subtype.val (hfix ⟨x, hx⟩)
    rw [← hsmul ⟨x, hx⟩ y']
    exact h2
  calc x * y' = x * y' * x⁻¹ * x := by group
    _ = y' * x := by rw [h1]

omit [Finite G] in
theorem exists_odd_pow_two_element [Finite G] (g : G) :
    ∃ m : ℕ, Odd m ∧ ∃ k : ℕ, (g ^ m) ^ 2 ^ k = 1 := by
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  refine ⟨m, hm, k, ?_⟩
  rw [← pow_mul, mul_comm, ← hkm, pow_orderOf_eq_one]

@[expose] def a4u5 : alternatingGroup (Fin 4) :=
  ⟨swap 0 1 * swap 2 3, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def a4v5 : alternatingGroup (Fin 4) :=
  ⟨swap 0 2 * swap 1 3, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def a4c5 : alternatingGroup (Fin 4) :=
  ⟨swap 2 1 * swap 1 0, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def a4y5 : alternatingGroup (Fin 4) :=
  ⟨swap 3 1 * swap 1 0, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def a4y5' : alternatingGroup (Fin 4) :=
  ⟨swap 3 1 * swap 3 0, by rw [Perm.mem_alternatingGroup]; decide⟩

theorem a4_relations : a4u5 * a4u5 = 1 ∧ a4v5 * a4v5 = 1 ∧ a4u5 * a4v5 = a4v5 * a4u5 ∧
    a4u5 ≠ 1 ∧ a4v5 ≠ 1 ∧ a4u5 ≠ a4v5 ∧ a4c5 * a4u5 * a4c5⁻¹ = a4v5 ∧
    a4c5 * a4v5 * a4c5⁻¹ = a4u5 * a4v5 ∧ a4c5 * a4y5 * a4c5⁻¹ * a4y5⁻¹ = a4u5 ∧
    a4c5 * a4y5' * a4c5⁻¹ * a4y5'⁻¹ = a4v5 := by
  decide

omit [Finite G] in
theorem exists_a4_data {X : Subgroup G} (φ : X ≃* alternatingGroup (Fin 4)) :
    ∃ c ∈ X, ∃ y ∈ X, ∃ y' ∈ X, ∃ a₁ a₂ : G,
      a₁ = c * y * c⁻¹ * y⁻¹ ∧ a₂ = c * y' * c⁻¹ * y'⁻¹ ∧ a₁ * a₁ = 1 ∧ a₂ * a₂ = 1 ∧
      a₁ * a₂ = a₂ * a₁ ∧ a₁ ≠ 1 ∧ a₂ ≠ 1 ∧ a₁ ≠ a₂ ∧ c * a₁ * c⁻¹ = a₂ ∧
      c * a₂ * c⁻¹ = a₁ * a₂ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := a4_relations
  have hinj : ∀ a b : alternatingGroup (Fin 4), a ≠ b →
      ((φ.symm a : X) : G) ≠ ((φ.symm b : X) : G) := fun a b hab h =>
    hab (φ.symm.injective (Subtype.ext h))
  refine ⟨_, (φ.symm a4c5).2, _, (φ.symm a4y5).2, _, (φ.symm a4y5').2,
    (φ.symm a4u5 : X), (φ.symm a4v5 : X), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← h9]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  · rw [← h10]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  · rw [← Subgroup.coe_mul, ← map_mul, h1, map_one, Subgroup.coe_one]
  · rw [← Subgroup.coe_mul, ← map_mul, h2, map_one, Subgroup.coe_one]
  · rw [← Subgroup.coe_mul, ← map_mul, h3, map_mul, Subgroup.coe_mul]
  · have := hinj _ _ h4
    rwa [map_one] at this
  · have := hinj _ _ h5
    rwa [map_one] at this
  · exact hinj _ _ h6
  · rw [← h7]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  · have h11 := congrArg (fun a => ((φ.symm a : X) : G)) h8
    simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] using h11

end CFSG.ComponentClassification.Foote5
