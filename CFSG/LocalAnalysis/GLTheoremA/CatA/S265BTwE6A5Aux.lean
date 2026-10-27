module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreKac
public import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsCoreDefs
import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeEndComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.TE6

open scoped Pointwise

theorem center_eq_bot_and_mem_of_isComponentOf_sup {G : Type*} [Group G] {X D J : Subgroup G}
    (hXc : IsCyclic X) (hXodd : Odd (Nat.card X)) (hXD : X ≤ Subgroup.centralizer (D : Set G))
    (hDq : CFSG.IsQuasisimple D) (hDz : Subgroup.center D = ⊥)
    (hJ : CFSG.Open.IsComponentOf J (X ⊔ D)) :
    Subgroup.center J = ⊥ ∧ ∀ v ∈ X ⊔ D, v * v = 1 → v ∈ J := by
  have hJD : J = D := CFSG.StandardType.TwE6D3.eq_of_isComponentOf_sup hXc hXD
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hDq)
    (CFSG.Assembly.isComponentOf_iff_open.2 hJ)
  rw [hJD]
  refine ⟨hDz, fun v hv hv1 => ?_⟩
  have hLE : X ≤ Subgroup.normalizer (D : Set G) :=
    hXD.trans (Subgroup.centralizer_le_normalizer _)
  have hv' : v ∈ (X : Set G) * (D : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right X D hLE]
    exact hv
  obtain ⟨x, hx, d, hd, rfl⟩ := hv'
  have hcomm : d * x = x * d := Subgroup.mem_centralizer_iff.1 (hXD hx) d hd
  have h2 : x ^ 2 * d ^ 2 = 1 := by
    rw [pow_two, pow_two]
    calc x * x * (d * d) = x * (x * d) * d := by simp only [mul_assoc]
      _ = x * (d * x) * d := by rw [hcomm]
      _ = (x * d) * (x * d) := by simp only [mul_assoc]
      _ = 1 := hv1
  have hx2D : x ^ 2 ∈ D := by
    rw [eq_inv_of_mul_eq_one_left h2]
    exact D.inv_mem (D.pow_mem hd 2)
  have hx2c : (⟨x ^ 2, hx2D⟩ : D) ∈ Subgroup.center D := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (Subgroup.pow_mem _ (hXD hx) 2) g.1 g.2)
  rw [hDz, Subgroup.mem_bot] at hx2c
  have hx2 : x ^ 2 = 1 := congrArg Subtype.val hx2c
  have hord : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
  have hordX : orderOf x ∣ Nat.card X := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : X)
    rwa [Subgroup.orderOf_mk] at this
  have hx1 : x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hord with h1 | h1
    · exact orderOf_eq_one_iff.1 h1
    · exact absurd (h1 ▸ hordX) hXodd.not_two_dvd_nat
  simpa [hx1] using hd

section Coroot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs

private theorem coroot_check : ∀ m0 m1 m2 m3 m4 m5 : Fin 3,
    cntB m0.val m1.val m2.val m3.val m4.val m5.val = 30 →
    ∃ γ ∈ R6, ∀ i : Fin Tag.E6.rank,
      (((![m0.val, m1.val, m2.val, m3.val, m4.val, m5.val] : Fin 6 → ℕ) i : ℕ) : ℤ) % 3 =
        (∑ l, Tag.E6.cartan i l * γ l) % 3 := by
  decide +kernel


theorem exists_corootTuple_of_ncard_thirty {L : Type} [Field L] [IsAlgClosed L]
    (h3 : ((3 : ℕ) : L) ≠ 0) {a : Fin Tag.E6.rank → Lˣ} (hap : ∀ i, a i ^ 3 = 1)
    (h30 : (kernelRoots (rootCharHom a)).ncard = 30) :
    ∃ (γ : Fin TwistTag.E6.tag.rank → ℤ) (ζ : Lˣ), IsRoot TwistTag.E6.tag γ ∧ ζ ^ 3 = 1 ∧
      ζ ≠ 1 ∧ a = CFSG.StandardType.TwE6RootAs.corootTuple γ ζ := by
  classical
  haveI : NeZero ((3 : ℕ) : L) := ⟨h3⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 3
  have hu : IsUnit ζ₀ := hζ₀.isUnit (by norm_num)
  have hζ : IsPrimitiveRoot ((hu.unit : Lˣ) : L) 3 := by simpa using hζ₀
  have hζu : IsPrimitiveRoot hu.unit 3 := IsPrimitiveRoot.coe_units_iff.1 hζ
  choose y hy hya using fun i => hζ.eq_pow_of_pow_eq_one
    (show ((a i : Lˣ) : L) ^ 3 = 1 by rw [← Units.val_pow_eq_pow_val, hap i, Units.val_one])
  have hya' : ∀ i, hu.unit ^ y i = a i := fun i =>
    Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hya i)
  have hchar : ∀ β, rootChar a β = hu.unit ^ dotμ ((1 : WeylGroup Tag.E6) • β)
      (y 0 : ℤ) (y 1 : ℤ) (y 2 : ℤ) (y 3 : ℤ) (y 4 : ℤ) (y 5 : ℤ) := by
    intro β
    rw [one_smul]
    have h1 : rootChar a β = ∏ i, hu.unit ^ ((y i : ℤ) * β i) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← hya' i, ← zpow_natCast, ← zpow_mul]
    rw [h1, Finset.prod_zpow_eq_zpow_sum, sum_rank_E6]
    simp only [dotμ]
    congr 1
    ring
  have hcnt : cntB (y 0 : ℤ) (y 1 : ℤ) (y 2 : ℤ) (y 3 : ℤ) (y 4 : ℤ) (y 5 : ℤ) = 30 := by
    rw [← ncard_kernelRoots_eq_cntB hζ 1 hchar]
    exact h30
  obtain ⟨γ, hγR, hγ⟩ := coroot_check ⟨y 0, hy 0⟩ ⟨y 1, hy 1⟩ ⟨y 2, hy 2⟩ ⟨y 3, hy 3⟩
    ⟨y 4, hy 4⟩ ⟨y 5, hy 5⟩ hcnt
  have hvec : ∀ i : Fin Tag.E6.rank, (![y 0, y 1, y 2, y 3, y 4, y 5] : Fin 6 → ℕ) i = y i := by
    intro i
    fin_cases i <;> rfl
  have h3z : hu.unit ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact hζu.pow_eq_one
  have hzpow : ∀ m n : ℤ, m % 3 = n % 3 → hu.unit ^ m = hu.unit ^ n := by
    intro m n hmn
    obtain ⟨k, hk⟩ : (3 : ℤ) ∣ m - n := Int.dvd_of_emod_eq_zero (by omega)
    rw [show m = n + 3 * k by omega, zpow_add, zpow_mul, h3z, one_zpow, mul_one]
  refine ⟨γ, hu.unit, isRoot_of_mem_R6 hγR, hζu.pow_eq_one, hζu.ne_one (by norm_num), ?_⟩
  funext i
  have hi := hγ i
  rw [hvec i] at hi
  show a i = hu.unit ^ (∑ l, TwistTag.E6.tag.cartan i l * γ l)
  rw [← hya' i, ← zpow_natCast]
  exact hzpow _ _ hi

end Coroot

end CFSG.LocalAnalysis.GLTheoremA.S265.TE6

end
