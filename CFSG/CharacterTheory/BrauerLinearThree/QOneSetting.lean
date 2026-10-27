module

public import CFSG.CharacterTheory.BrauerLinearThree.CentralizerSylowWreathed
public import CFSG.CharacterTheory.Wreathed.BrauerWreathedOrderGroup
public import CFSG.CharacterTheory.BrauerLinearThree.NineLocal

public section

namespace CFSG.BrauerLinearThree.QOne

open Matrix CFSG.DesarguesianPlanes

open CFSG.TwoRankLowerBound.Helpers in
@[expose] def BrauerWreathedTypeOnePrincipalBlockStatement : Prop :=
  ∀ {G : Type} [Group G] [Fintype G]
    (n : ℕ) (_hn : 2 ≤ n) (S : Sylow 2 G) (S₁ S₂ T : G)
    (_hgen : Subgroup.closure {S₁, S₂, T} = (S : Subgroup G))
    (_hcard : Nat.card (S : Subgroup G) = 2 ^ (2 * n + 1))
    (_hS₁ : S₁ ^ 2 ^ n = 1) (_hS₂ : S₂ ^ 2 ^ n = 1) (_hT : T ^ 2 = 1)
    (_hcomm : S₁ * S₂ = S₂ * S₁) (_hconj : T⁻¹ * S₁ * T = S₂),
    let A := S₁⁻¹ * S₂⁻¹
    let J := A ^ 2 ^ (n - 1)
    let J₁ := S₁ ^ 2 ^ (n - 1)
    let S₀ := Subgroup.closure {S₁, S₂}
    let D := Subgroup.closure {J, J₁}
    let c : Set G → ℕ := fun X => Nat.card (Subgroup.centralizer X)
    let idx := (Subgroup.centralizer (S₀ : Set G)).relIndex (Subgroup.normalizer (S₀ : Set G))
    let caseA : Prop := ∃ g ∈ Subgroup.centralizer {J}, g⁻¹ * T * g = J₁
    idx = 6 → caseA →
    ∀ (F : Type) [Field F] [Fintype F], Fintype.card F % 4 = 1 →
    ∀ (L : Subgroup (GL (Fin 2) F)) [L.Normal],
      (∀ x ∈ L, ∃ a : F, (x : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) a) →
      Odd (Nat.card L) →
      Nonempty (Subgroup.centralizer {J} ≃* GL (Fin 2) F ⧸ L) →
    let q : ℕ := Fintype.card F
    Nat.card G * (c (D : Set G) ^ 2 * (q + 1) ^ 2) = c {J} ^ 3 * (q ^ 2 + q + 1) ∧
    ∀ (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
      [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
      (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index),
      (basis.representation principal).character = 1 →
      ∃ χ : Fin 6 → basis.index,
        (∀ i, χ i ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal) ∧
        χ 0 = principal ∧
        (basis.representation (χ 0)).character 1 = 1 ∧
        (basis.representation (χ 1)).character 1 = (q : ℂ) ^ 3 ∧
        (basis.representation (χ 2)).character 1 = (q : ℂ) * ((q : ℂ) ^ 2 + q + 1) ∧
        (basis.representation (χ 3)).character 1 = (q : ℂ) ^ 2 + q + 1 ∧
        (basis.representation (χ 4)).character 1 = (q : ℂ) ^ 3 - 1 ∧
        (basis.representation (χ 5)).character 1 = ((q : ℂ) + 1) * ((q : ℂ) ^ 2 + q + 1) ∧
        ∀ g : G, Odd (orderOf g) →
          -1 + (basis.representation (χ 1)).character g =
              (basis.representation (χ 2)).character g -
                (basis.representation (χ 3)).character g ∧
            (basis.representation (χ 2)).character g -
                (basis.representation (χ 3)).character g =
              (basis.representation (χ 4)).character g ∧
            (basis.representation (χ 2)).character g + (basis.representation (χ 3)).character g =
              (basis.representation (χ 5)).character g

theorem not_exists_normal_index_two_of_simple {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) : ¬ ∃ H : Subgroup G, H.Normal ∧ H.index = 2 := by
  rintro ⟨H, hHn, hH2⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with rfl | rfl
  · rw [Subgroup.index_bot] at hH2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : IsCyclic G := isCyclic_of_prime_card hH2
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab ((IsCyclic.isMulCommutative (α := G)).is_comm.comm a b)
  · rw [Subgroup.index_top] at hH2
    omega

theorem eq_one_of_mem_center_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {z : G} (hz : z ∈ Subgroup.center G) : z = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · rwa [h, Subgroup.mem_bot] at hz
  · obtain ⟨a, b, hab⟩ := hnonab
    have ha : a ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top a
    exact absurd ((Subgroup.mem_center_iff.mp ha b).symm) hab

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)

include φ hZ hZodd h2 hJ in
theorem exists_wreath_sylow_of_G [Finite G] (hq : Nat.card F % 4 = 1) :
    ∃ (n : ℕ) (S : Sylow 2 G) (S₁ S₂ T : G), 2 ≤ n ∧
      Subgroup.closure {S₁, S₂, T} = (S : Subgroup G) ∧
      Nat.card (S : Subgroup G) = 2 ^ (2 * n + 1) ∧
      S₁ ^ 2 ^ n = 1 ∧ S₂ ^ 2 ^ n = 1 ∧ T ^ 2 = 1 ∧ S₁ * S₂ = S₂ * S₁ ∧
      T⁻¹ * S₁ * T = S₂ ∧ (S : Subgroup G) ≤ Subgroup.centralizer {J} ∧
      (S₁⁻¹ * S₂⁻¹) ^ 2 ^ (n - 1) = J ∧ S₁ ^ 2 ^ (n - 1) = invJ₂ φ := by
  obtain ⟨hk2, α, -, hW, hle, ⟨SC, hSC⟩, hJpow, hJ₂pow, -⟩ :=
    exists_wreathed_sylow φ hZ hZodd h2 hJ hq rfl
  obtain ⟨S, hS⟩ := exists_sylow_eq_of_sylow_centralizer φ hZ hZodd h2 hJ _ SC hSC
  refine ⟨_, S, _, _, _, hk2, hW.closure_eq.trans hS.symm, by rw [hS]; exact hW.card_eq,
    hW.pow_left, hW.pow_right, hW.sq_swap, hW.comm, hW.conj, by rw [hS]; exact hle, hJpow,
    hJ₂pow⟩

omit [Finite F] in
include hZ hZodd h2 hJ in
theorem closure_J_invJ₂_eq_fourV : Subgroup.closure {J, invJ₂ φ} = fourV φ := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact J_mem_fourV φ
    · exact invJ₂_mem_fourV φ hZ hZodd h2 hJ
  · rw [fourV, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · rw [← J_mul_invJ₂ φ hZ hZodd h2 hJ]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

omit [Finite F] in
include hZ hZodd h2 hJ in
theorem centralizer_closure_J_invJ₂ :
    Subgroup.centralizer ((Subgroup.closure {J, invJ₂ φ} : Subgroup G) : Set G) =
      Subgroup.centralizer (fourV φ : Set G) := by
  rw [closure_J_invJ₂_eq_fourV φ hZ hZodd h2 hJ]

omit [Finite F] in
include hZ hZodd h2 hJ in
theorem card_centralizer_closure_J_invJ₂ :
    Nat.card (Subgroup.centralizer ((Subgroup.closure {J, invJ₂ φ} : Subgroup G) : Set G)) *
      Nat.card Z = (Nat.card F - 1) ^ 2 := by
  rw [centralizer_closure_J_invJ₂ φ hZ hZodd h2 hJ, centralizer_fourV_eq]
  exact card_centralizer_inf_invJ₁ φ hZ hZodd h2

omit [Finite F] in
theorem caseOneA_of_simple [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (S₁ S₂ T : G)
    (hgen : Subgroup.closure {S₁, S₂, T} = (S : Subgroup G))
    (hcard : Nat.card (S : Subgroup G) = 2 ^ (2 * n + 1))
    (hS₁ : S₁ ^ 2 ^ n = 1) (hS₂ : S₂ ^ 2 ^ n = 1) (hT : T ^ 2 = 1)
    (hcomm : S₁ * S₂ = S₂ * S₁) (hconj : T⁻¹ * S₁ * T = S₂)
    (hJpow : (S₁⁻¹ * S₂⁻¹) ^ 2 ^ (n - 1) = J) (hJ₂pow : S₁ ^ 2 ^ (n - 1) = invJ₂ φ) :
    (Subgroup.centralizer ((Subgroup.closure {S₁, S₂} : Subgroup G) : Set G)).relIndex
        (Subgroup.normalizer ((Subgroup.closure {S₁, S₂} : Subgroup G) : Set G)) = 6 ∧
      ∃ g ∈ Subgroup.centralizer ({J} : Set G), g⁻¹ * T * g = invJ₂ φ := by
  let : Fintype G := Fintype.ofFinite G
  have hcases := CFSG.Wreathed.BrauerWreathedOrder.brauer_wreathed_order_group_cases n hn S S₁
    S₂ T hgen hcard hS₁ hS₂ hT hcomm hconj
  simp only [hJpow, hJ₂pow] at hcases
  obtain ⟨h1, -, h2', -, -, -, -⟩ := hcases
  have hno := not_exists_normal_index_two_of_simple hnonab
  rcases h1 with h | h
  · exact absurd (h2' (Or.inr h)) hno
  · refine ⟨h, ?_⟩
    by_contra hA
    exact hno (h2' (Or.inl ⟨h, hA⟩))

end CFSG.BrauerLinearThree.QOne
