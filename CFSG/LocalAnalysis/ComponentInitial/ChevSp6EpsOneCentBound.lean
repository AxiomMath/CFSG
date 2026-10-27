module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerStatements
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64LagrangianCompletion
import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCyclicKernel
import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64NextBlock
import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerPtSylow

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

theorem card_le_of_isPGroup_two_of_dvd {X : Type*} [Group X] [Finite X] {P : Subgroup X}
    (hP : IsPGroup 2 P) (hdvd : Nat.card P ∣ 2 ^ 10 * 2835) : Nat.card P ≤ 2 ^ 10 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hP
  rw [hk] at hdvd ⊢
  have hcop : Nat.Coprime (2 ^ k) 2835 := Nat.Coprime.pow_left k (by norm_num)
  exact Nat.le_of_dvd (by positivity) (hcop.dvd_of_dvd_mul_right hdvd)

theorem epsOne_cent_two_bound_of_model {G : Type} [Group G] [Finite G]
    (hG : CFSG.oddCore G = ⊥) {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L) (hLn : ¬ L.Normal)
    (hZ : center L = ⊥) (hmodel : CFSG.Blueprint.LieModel L .PSp 3 2 1)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G)))) {z : G}
    (hzT : z ∈ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype)
    (hz : orderOf z = 2) (hH : CFSG.oddCore (centralizer ({z} : Set G)) = ⊥)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
    (φ : L ≃* bilinIsometryGroup b) {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V}
    (he : IsSymplecticBasis b e) :
    ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer ({z} : Set G) → Nat.card P ≤ 2 ^ 10 := by
  intro P hP hPC
  obtain ⟨hTC, hsup, hinf, -⟩ :=
    standard_binary_symplectic_six_initial hG hL hLn hZ hmodel T hT hzT hz hH
  rw [standard_binary_symplectic_six_sylow_eq hG hL hLn hZ hmodel T hT hzT hz hH] at hTC hsup hinf
  have hzC : z ∈ centralizer (L : Set G) := hTC (mem_zpowers z)
  have hle : zpowers z ≤ normalizer (L : Set G) := by
    rw [zpowers_le]
    exact centralizer_le_normalizer _ hzC
  have hcard := natCard_sup_mul_inf hle
  rw [inf_comm, hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hz, EpsOne.card_L_of φ he,
    sup_comm, hsup] at hcard
  refine card_le_of_isPGroup_two_of_dvd hP ?_
  rw [show 2 ^ 10 * 2835 = 2 * 1451520 by norm_num, ← hcard]
  exact Subgroup.card_dvd_of_le hPC

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
