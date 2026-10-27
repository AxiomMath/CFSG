module

public import CFSG.LieType.HighestRoot.CentChevalleySLThree
public import CFSG.ClassicalInvolution.SL2Facts

public section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup
open scoped MatrixGroups commutatorElement

section Squares

variable {G : Type*} [Group G]

theorem commutatorElement_eq_mul_self_mul (a b : G) :
    ⁅a, b⁆ = a * b * (a * b) * (b⁻¹ * a⁻¹ * b * (b⁻¹ * a⁻¹ * b)) * (b⁻¹ * b⁻¹) := by
  rw [commutatorElement_def]
  group

theorem commutator_le_closure_mul_self (G : Type*) [Group G] :
    commutator G ≤ closure {x : G | ∃ y, y * y = x} := by
  rw [_root_.commutator_def, commutator_le]
  intro a _ b _
  rw [commutatorElement_eq_mul_self_mul]
  exact mul_mem (mul_mem (subset_closure ⟨_, rfl⟩) (subset_closure ⟨_, rfl⟩))
    (subset_closure ⟨_, rfl⟩)

theorem range_le_closure_mul_self {S : Type*} [Group S] (φ : S →* G)
    (hS : closure {x : S | ∃ y, y * y = x} = ⊤) :
    φ.range ≤ closure {x : G | ∃ y ∈ φ.range, y * y = x} := by
  calc φ.range = (closure {x : S | ∃ y, y * y = x}).map φ := by
        rw [hS, MonoidHom.range_eq_map]
    _ = closure (φ '' {x : S | ∃ y, y * y = x}) := MonoidHom.map_closure φ _
    _ ≤ closure {x : G | ∃ y ∈ φ.range, y * y = x} := by
        apply Subgroup.closure_mono
        rintro _ ⟨x, ⟨y, rfl⟩, rfl⟩
        exact ⟨φ y, ⟨y, rfl⟩, (map_mul φ y y).symm⟩

theorem le_of_le_comap_map_of_mul_self {H : Type*} [Group H] (θ : G →* H)
    (hker : θ.ker ≤ center G) (hker2 : ∀ k ∈ θ.ker, k * k = 1) {J P : Subgroup G}
    (hP : P ≤ closure {x | ∃ y ∈ P, y * y = x}) (hle : P ≤ (J.map θ).comap θ) : P ≤ J := by
  refine hP.trans ((closure_le _).mpr ?_)
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨a, ha, hay⟩ := hle hy
  have hk : y * a⁻¹ ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hay, mul_inv_cancel]
  have hcomm : Commute a (y * a⁻¹) := mem_center_iff.mp (hker hk) a
  have e : y * y = a * a := by
    calc y * y = y * a⁻¹ * a * (y * a⁻¹ * a) := by rw [inv_mul_cancel_right]
      _ = y * a⁻¹ * (y * a⁻¹) * (a * a) := hcomm.mul_mul_mul_comm _ _
      _ = a * a := by rw [hker2 _ hk, one_mul]
  rw [SetLike.mem_coe, e]
  exact mul_mem ha ha

theorem le_centralizer_of_mul_self {A : Subgroup G} {b : G}
    (hA : A ≤ closure {x | ∃ y ∈ A, y * y = x})
    (hc : ∀ a ∈ A, ⁅a, b⁆ ∈ center G ∧ ⁅a, b⁆ * ⁅a, b⁆ = 1) : A ≤ centralizer {b} := by
  refine hA.trans ((closure_le _).mpr ?_)
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨hcen, hsq⟩ := hc y hy
  have hcc := mem_center_iff.mp hcen
  have e1 : y * b = ⁅y, b⁆ * b * y := by
    rw [commutatorElement_def]
    group
  rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
  calc y * y * b = y * (y * b) := mul_assoc _ _ _
    _ = y * (⁅y, b⁆ * b * y) := by rw [e1]
    _ = y * ⁅y, b⁆ * b * y := by simp only [mul_assoc]
    _ = ⁅y, b⁆ * y * b * y := by rw [hcc y]
    _ = ⁅y, b⁆ * (y * b) * y := by simp only [mul_assoc]
    _ = ⁅y, b⁆ * (⁅y, b⁆ * b * y) * y := by rw [e1]
    _ = ⁅y, b⁆ * ⁅y, b⁆ * b * (y * y) := by simp only [mul_assoc]
    _ = b * (y * y) := by rw [hsq, one_mul]

theorem le_ker_of_mul_self {M : Type*} [Group M] (φ : G →* M) (hM : ∀ m : M, m * m = 1)
    {A : Subgroup G} (hA : A ≤ closure {x | ∃ y ∈ A, y * y = x}) : A ≤ φ.ker := by
  refine hA.trans ((closure_le _).mpr ?_)
  rintro _ ⟨y, -, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, hM]

theorem le_of_index_eq_two {A H : Subgroup G} (hH : H.index = 2)
    (hA : A ≤ closure {x | ∃ y ∈ A, y * y = x}) : A ≤ H := by
  refine hA.trans ((closure_le _).mpr ?_)
  rintro _ ⟨y, -, rfl⟩
  exact mul_self_mem_of_index_two hH y

end Squares

section SL2

variable {K : Type} [Field K] [Finite K]

theorem closure_mul_self_sl2 (hodd : Odd (Nat.card K)) :
    closure {x : SL(2, K) | ∃ y, y * y = x} = ⊤ := by
  by_cases h3 : Nat.card K = 3
  · rw [eq_top_iff, ← LieType.HighestRoot.closure_orderOf_three_eq_top h3, closure_le]
    intro x hx
    have hx3 : x ^ 3 = 1 := by
      have h : orderOf x = 3 := hx
      rw [← h]
      exact pow_orderOf_eq_one x
    refine subset_closure ⟨x * x, ?_⟩
    calc x * x * (x * x) = x ^ 3 * x := by rw [pow_three]; simp only [mul_assoc]
      _ = x := by rw [hx3, one_mul]
  · have h1 : 1 < Nat.card K := Finite.one_lt_card
    have h4 : 4 ≤ Nat.card K := by
      obtain ⟨k, hk⟩ := hodd
      omega
    have := CFSG.ClassicalInvolution.isPerfect_of_equiv_sl2 h4 (MulEquiv.refl SL(2, K))
    rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top]
    exact commutator_le_closure_mul_self _

theorem range_le_closure_mul_self_sl2 (hodd : Odd (Nat.card K)) {G : Type*} [Group G]
    (ρ : SL(2, K) →* G) : ρ.range ≤ closure {x | ∃ y ∈ ρ.range, y * y = x} :=
  range_le_closure_mul_self ρ (closure_mul_self_sl2 hodd)

theorem map_center_range_sl2_odd {G : Type} [Group G] (hodd : Odd (Nat.card K))
    (ρ : SL(2, K) →* G) (hρ : Function.Injective ρ) :
    (center ↥ρ.range).map ρ.range.subtype = zpowers (ρ (-1)) := by
  have : Finite ↥ρ.range := Finite.of_equiv _ (MonoidHom.ofInjective hρ).toEquiv
  have : Finite ↥((center ↥ρ.range).map ρ.range.subtype) :=
    Finite.of_equiv _ ((center ↥ρ.range).equivMapOfInjective _ ρ.range.subtype_injective).toEquiv
  have hc2 : Nat.card ↥(center ↥ρ.range) = 2 :=
    CFSG.ClassicalInvolution.natCard_center_of_equiv_sl2 hodd (MonoidHom.ofInjective hρ).symm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (ρ (-1)) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, neg_one_sq, map_one]
    · intro h
      exact CFSG.ClassicalInvolution.sl2_neg_one_ne_one hodd (hρ (h.trans (map_one _).symm))
  have hle : zpowers (ρ (-1)) ≤ (center ↥ρ.range).map ρ.range.subtype := by
    rw [zpowers_le, Subgroup.mem_map]
    refine ⟨⟨ρ (-1), MonoidHom.mem_range.mpr ⟨-1, rfl⟩⟩, ?_, rfl⟩
    rw [mem_center_iff]
    rintro ⟨_, A, rfl⟩
    apply Subtype.ext
    show ρ A * ρ (-1) = ρ (-1) * ρ A
    rw [← map_mul, ← map_mul, mul_neg_one, neg_one_mul]
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Nat.card_zpowers, hord, Subgroup.card_map_of_injective ρ.range.subtype_injective, hc2]

theorem pPrimeCore_range_sl2_odd {G : Type} [Group G] (hodd : Odd (Nat.card K))
    (ρ : SL(2, K) →* G) (hρ : Function.Injective ρ) : pPrimeCore 2 ↥ρ.range = ⊥ := by
  have : Finite ↥ρ.range := Finite.of_equiv _ (MonoidHom.ofInjective hρ).toEquiv
  have h1 : 1 < Nat.card K := Finite.one_lt_card
  have h3 : 3 ≤ Nat.card K := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd' : Odd (Nat.card ↥(pPrimeCore 2 ↥ρ.range)) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card))
  exact CFSG.ClassicalInvolution.normal_odd_of_equiv_sl2 hodd h3 (MonoidHom.ofInjective hρ).symm
    _ pPrimeCore_normal hodd'

end SL2

end CFSG.ComponentClassification.HarrisLit.T1
