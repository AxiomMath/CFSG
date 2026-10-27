module

public import CFSG.CharacterTheory.Wreathed.ConditionalFlatTwistedBasesLocal
public import CFSG.CharacterTheory.Wreathed.ConditionalFlatTwistedBasesTwist
public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityCentralProduct
public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityActualColumns

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.FlatTwistedBases

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.WreathCentralSquare
  CFSG.Wreathed.SquareRootSmallCharacterRigidity

variable {G : Type} [Group G] {n : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))

theorem root_eq_actualRoot :
    wreathModelHom S e (Original.s (2 ^ n) * Original.z (2 ^ n)) = actualRoot S e := rfl

theorem root_zpow_involution (hn : 2 ≤ n) {h : ℤ} (hh : Odd h) :
    wreathModelHom S e (Original.x (2 ^ n)) ∈
      Subgroup.zpowers (wreathModelHom S e (Original.s (2 ^ n) * Original.z (2 ^ n)) ^ h) := by
  rw [root_eq_actualRoot]
  have hym : actualRoot S e ^ (2 ^ n) = wreathModelHom S e (Original.x (2 ^ n)) :=
    actualRoot_pow_modulus n (by omega) S e
  have hx2 : wreathModelHom S e (Original.x (2 ^ n)) ^ 2 = 1 := by
    have h1 := pow_orderOf_eq_one (wreathModelHom S e (Original.x (2 ^ n)))
    rwa [CompatibleFamilies.orderOf_x S e hn] at h1
  have hpow : (actualRoot S e ^ h) ^ (2 ^ n) = wreathModelHom S e (Original.x (2 ^ n)) := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hym]
    obtain ⟨k, rfl⟩ := hh
    rw [zpow_add, zpow_one, zpow_mul, zpow_two, ← pow_two, hx2, one_zpow, one_mul]
  rw [← hpow]
  exact Subgroup.npow_mem_zpowers _ _

theorem root_centralizer_structure [Finite G] (hn : 2 ≤ n) :
    orderOf (wreathModelHom S e (Original.s (2 ^ n) * Original.z (2 ^ n))) = 2 * 2 ^ n ∧
    wreathModelHom S e (Original.s (2 ^ n) * Original.z (2 ^ n)) ^ 2 =
      wreathModelHom S e (Original.a (2 ^ n)) ∧
    wreathModelHom S e (Original.s (2 ^ n) * Original.z (2 ^ n)) ^ (2 ^ n) =
      wreathModelHom S e (Original.x (2 ^ n)) ∧
    (∀ c : Subgroup.centralizer
        ({wreathModelHom S e (Original.s (2 ^ n) * Original.z (2 ^ n))} : Set G),
      c ∈ CFSG.oddCore (Subgroup.centralizer
        ({wreathModelHom S e (Original.s (2 ^ n) * Original.z (2 ^ n))} : Set G)) ↔
      Odd (orderOf (c : G))) ∧
    (CFSG.oddCore (Subgroup.centralizer
        ({wreathModelHom S e (Original.s (2 ^ n) * Original.z (2 ^ n))} : Set G))).index =
      2 * 2 ^ n ∧
    (∃ E : CFSG.oddCore (Subgroup.centralizer
          ({wreathModelHom S e (Original.s (2 ^ n) * Original.z (2 ^ n))} : Set G)) ×
        Subgroup.zpowers (wreathModelHom S e (Original.s (2 ^ n) * Original.z (2 ^ n))) ≃*
        Subgroup.centralizer
          ({wreathModelHom S e (Original.s (2 ^ n) * Original.z (2 ^ n))} : Set G),
      ∀ k z, (E (k, z) : G) = ((k : Subgroup.centralizer
        ({wreathModelHom S e (Original.s (2 ^ n) * Original.z (2 ^ n))} : Set G)) : G) * (z : G)) ∧
    ∀ h : ℤ, Odd h →
      Subgroup.centralizer
          ({wreathModelHom S e (Original.s (2 ^ n) * Original.z (2 ^ n)) ^ h} : Set G) =
        Subgroup.centralizer
          ({wreathModelHom S e (Original.s (2 ^ n) * Original.z (2 ^ n))} : Set G) := by
  rw [root_eq_actualRoot]
  obtain ⟨hysq, hym, hyord, -, hmem, hindex, E, hE, -⟩ := original_root_centralizer_product n hn S e
  refine ⟨hyord, hysq, hym, hmem, hindex, ⟨E, hE⟩, fun h hh => ?_⟩
  have hy2 : orderOf (actualRoot S e) = 2 ^ (n + 1) := by
    rw [hyord, pow_succ, Nat.mul_comm]
  have hz : Subgroup.zpowers (actualRoot S e ^ h) = Subgroup.zpowers (actualRoot S e) := by
    apply Subgroup.eq_of_le_of_card_ge
      (Subgroup.zpowers_le.mpr (Subgroup.zpow_mem_zpowers (actualRoot S e) h))
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_odd_power hy2 hh, hy2]
  rw [← centralizer_zpowers_eq_singleton, hz, centralizer_zpowers_eq_singleton]

theorem root_centralizer_quotient [Finite G] (hn : 2 ≤ n) {h : ℤ} (hh : Odd h) :
    ∃ (N : Subgroup (Subgroup.centralizer (Subgroup.zpowers
        (wreathModelHom S e (Original.s (2 ^ n) * Original.z (2 ^ n)) ^ h) : Set G)))
      (_ : N.Normal), Odd (Nat.card N) ∧
      IsPGroup 2 (Subgroup.centralizer (Subgroup.zpowers
        (wreathModelHom S e (Original.s (2 ^ n) * Original.z (2 ^ n)) ^ h) : Set G) ⧸ N) ∧
      IsMulCommutative (Subgroup.centralizer (Subgroup.zpowers
        (wreathModelHom S e (Original.s (2 ^ n) * Original.z (2 ^ n)) ^ h) : Set G) ⧸ N) ∧
      Nat.card (Subgroup.centralizer (Subgroup.zpowers
        (wreathModelHom S e (Original.s (2 ^ n) * Original.z (2 ^ n)) ^ h) : Set G) ⧸ N) =
        2 * 2 ^ n := by
  have hyord := actualRoot_orderOf n hn S e
  have hy2 : orderOf (actualRoot S e) = 2 ^ (n + 1) := by
    rw [hyord, pow_succ, Nat.mul_comm]
  have hyh : orderOf (actualRoot S e ^ h) = 2 * 2 ^ n := by
    rw [orderOf_odd_power hy2 hh, pow_succ, Nat.mul_comm]
  rw [root_eq_actualRoot, centralizer_zpowers_eq_singleton]
  obtain ⟨hodd, -, -, -, -, hquot, hcyc, -⟩ :=
    maximal_root_centralizer_direct_product n hn S e (actualRoot S e ^ h) hyh
  have hcard := (maximal_root_centralizer_index n hn S e (actualRoot S e ^ h) hyh).2.1
  have : IsCyclic (Subgroup.centralizer ({actualRoot S e ^ h} : Set G) ⧸
      CFSG.oddCore (Subgroup.centralizer ({actualRoot S e ^ h} : Set G))) := hcyc
  refine ⟨CFSG.oddCore _, inferInstance, hodd, hquot, ?_, hcard⟩
  exact (MonoidHom.id _).isMulCommutative_of_isCyclic_of_ker_le_center fun z hz => by
    rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hz
    rw [hz]
    exact Subgroup.one_mem _

theorem root_singleton_basis [Fintype G] (hn : 2 ≤ n) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (lam : involutionCentralizer n S e →* ℂˣ) {h : ℤ} (hh : Odd h)
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.centralizer (Subgroup.zpowers
      (wreathModelHom S e (Original.s (2 ^ n) * Original.z (2 ^ n)) ^ h) : Set G)))
    (ℓ : localBasis.index)
    (hℓ : ∀ c, (localBasis.representation ℓ).character c = lam (Subgroup.inclusion
      (centralizer_zpowers_le_involutionCentralizer S e (root_zpow_involution S e hn hh)) c)) :
    SingletonTwistedBasisData localBasis ideal ℓ (fun c => (lam (Subgroup.inclusion
      (centralizer_zpowers_le_involutionCentralizer S e (root_zpow_involution S e hn hh)) c) :
        ℂ)) (2 * 2 ^ n) := by
  obtain ⟨N, hnormal, hodd, hquot, hcomm, hcard⟩ := root_centralizer_quotient S e hn hh
  have := singletonTwistedBasisData_of_comm localBasis ideal (lam.comp (Subgroup.inclusion
    (centralizer_zpowers_le_involutionCentralizer S e (root_zpow_involution S e hn hh)))) ℓ hℓ N
    hodd hquot
  rw [hcard] at this
  exact this

end CFSG.Wreathed.FlatTwistedBases
