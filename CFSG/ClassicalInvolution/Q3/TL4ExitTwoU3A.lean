module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GH74.Generic.Context
public import CFSG.RankThree.Classical.SteinbergBJUnitaryThreeInvolutions
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Generic.SL2Anticommute
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.U3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical

variable {G : Type} [Group G]

theorem exists_four_of_quat {N : Subgroup G} [N.Normal]
    (hOut : ∀ P : Subgroup (G ⧸ N), IsPGroup 2 P → IsCyclic P) {P : Subgroup G}
    (e : ↥P ≃* QuaternionGroup 2) : ∃ s ∈ P, s ∈ N ∧ orderOf s = 4 := by
  by_contra hA
  have hsq : ∀ q : QuaternionGroup 2, q * q = 1 → ∀ r, q * r = r * q := by decide
  have h4 : ∀ q : QuaternionGroup 2, q * q ≠ 1 → q * q * (q * q) = 1 := by decide
  have hcent : ∀ x : P, (x : G) ∈ N → x ∈ Subgroup.center P := by
    intro x hxN
    rw [Subgroup.mem_center_iff]
    intro y
    by_cases hx : e x * e x = 1
    · apply e.injective
      rw [map_mul, map_mul]
      exact (hsq _ hx (e y)).symm
    · exfalso
      have hx2 : x * x ≠ 1 := fun h0 => hx (by rw [← map_mul, h0, map_one])
      have hx4 : x * x * (x * x) = 1 := e.injective (by
        rw [map_mul, map_mul, map_one]
        exact h4 _ hx)
      have ho : orderOf x = 4 := by
        refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
        · rw [pow_one, sq]
          exact hx2
        · rw [show (2 : ℕ) ^ (1 + 1) = 2 + 2 from rfl, pow_add, sq]
          exact hx4
      exact hA ⟨x, x.2, hxN, by rw [Subgroup.orderOf_coe]; exact ho⟩
  have hP2 : IsPGroup 2 ↥P := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  have : IsCyclic (P.map (QuotientGroup.mk' N)) := hOut _ (hP2.map _)
  let φ : ↥P →* ↥(P.map (QuotientGroup.mk' N)) :=
    ((QuotientGroup.mk' N).comp P.subtype).codRestrict _ fun x => ⟨x, x.2, rfl⟩
  have hφ : φ.ker ≤ Subgroup.center P := fun x hx => hcent x
    ((QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val (MonoidHom.mem_ker.mp hx)))
  have hcomm := (φ.isMulCommutative_of_isCyclic_of_ker_le_center hφ).is_comm.comm
    (e.symm (QuaternionGroup.a 1)) (e.symm (QuaternionGroup.xa 0))
  have h1 := congrArg e hcomm
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1
  exact absurd h1 (by decide)

theorem exists_conj_of_psu {N : Subgroup G} {p f : ℕ} (hp2 : p ≠ 2)
    (hL : CFSG.Blueprint.LieModel ↥N .PSU 3 p f) {x y : G} (hx : x ∈ N) (hy : y ∈ N)
    (hx2 : orderOf x = 2) (hy2 : orderOf y = 2) : ∃ n ∈ N, n * x * n⁻¹ = y := by
  obtain ⟨hp, hf, K, _, _, hK, ⟨e₀⟩⟩ := CFSG.GH74.Generic.lieModel_psu_data hL
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  set E : ↥N ≃* unitaryPSU h 3 := e₀.trans (unitaryPSUEquiv h (by norm_num)).symm with hE
  have hx' : orderOf (E ⟨x, hx⟩) = 2 := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hx2]
  have hy' : orderOf (E ⟨y, hy⟩) = 2 := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hy2]
  obtain ⟨c, hc⟩ := isConj_iff.mp ((isConj_unitaryProj_unitaryInvT h hp2 hx').trans
    (isConj_unitaryProj_unitaryInvT h hp2 hy').symm)
  refine ⟨(E.symm c : N), (E.symm c).2, ?_⟩
  have h1 : E.symm c * ⟨x, hx⟩ * (E.symm c)⁻¹ = ⟨y, hy⟩ := E.injective (by
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hc])
  exact congrArg Subtype.val h1

theorem isComponent_of_normal {C J₀ : Subgroup G} (hJC : J₀ ≤ C)
    (hJn : ∀ c ∈ C, ∀ j ∈ J₀, c * j * c⁻¹ ∈ J₀) (hJq : IsQuasisimple ↥J₀) :
    IsComponent (J₀.subgroupOf C) := by
  refine ⟨LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJC).symm hJq,
    Subgroup.Normal.isSubnormal ⟨fun j hj c => ?_⟩⟩
  rw [Subgroup.mem_subgroupOf] at hj ⊢
  exact hJn c c.2 j hj

end CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.U3
