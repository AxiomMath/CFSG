module

public import CFSG.ClassicalInvolution.Q3.Q3TMFSBasic
public import CFSG.ClassicalInvolution.Q3.Q3TMFSSmall
public import CFSG.ClassicalInvolution.Q3.Q3YQuat
public import CFSG.ClassicalInvolution.Q3.TA3SOLCoreQ8
public import CFSG.ClassicalInvolution.Q3.Q3SBasic
public import CFSG.LieType.HighestRoot.CentChevalleySLThree

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3.Q3T.MFS
open CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal (IsQ8Pair q8Hom q8Hom_injective)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped commutatorElement MatrixGroups

variable {Y : Type} [Group Y] [Finite Y] {z : Y} {L T : Subgroup Y}

theorem mem_of_pow_two [T.Normal] (hTL : T ⊔ L = ⊤) (h3 : memberIndex L T = 3) {x : Y} {k : ℕ}
    (hx : x ^ 2 ^ k = 1) : x ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx)
  have hP : IsPGroup 2 (Subgroup.zpowers x) := IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  exact isPGroup_two_le_of_odd_index (odd_index_of_memberIndex_eq_three hTL h3).1 hP
    (Subgroup.mem_zpowers x)

theorem mem_of_member [T.Normal] (hL : IsClassicalMember3 L z) (hTL : T ⊔ L = ⊤)
    (h3 : memberIndex L T = 3) : z ∈ T :=
  mem_of_pow_two hTL h3 (k := 1) (by rw [pow_one, ← hL.orderOf_eq_two]; exact pow_orderOf_eq_one z)

theorem three_dvd_card_outer [T.Normal] (hTL : T ⊔ L = ⊤) (h3 : memberIndex L T = 3)
    (hC : Subgroup.centralizer (T : Set Y) = ⊥) : 3 ∣ Nat.card (Outer T) :=
  (odd_index_of_memberIndex_eq_three hTL h3).2.trans (index_dvd_card_outer T hC)

theorem exists_q8 [T.Normal] (hL : IsClassicalMember3 L z) (hTL : T ⊔ L = ⊤)
    (h3 : memberIndex L T = 3) :
    ∃ φ : QuaternionGroup 2 →* Y, Function.Injective φ ∧ ∀ x, φ x ∈ L ∧ φ x ∈ T := by
  obtain ⟨x, hx, y, hy, hxx, hyy, hxy⟩ := hL.exists_quaternion_pair_sq
  have hz2 : z * z = 1 := by
    rw [← pow_two, ← hL.orderOf_eq_two]
    exact pow_orderOf_eq_one z
  have hzy : z * y = y * z := by rw [← hyy, mul_assoc]
  have hpair : IsQ8Pair y x := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_two y, hyy, pow_two, hz2]
    · rw [pow_two, pow_two, hxx, hyy]
    · have h1 : x * y * x⁻¹ = z * y := by
        calc x * y * x⁻¹ = x * y * x⁻¹ * y⁻¹ * y := by group
          _ = z * y := by rw [hxy]
      rw [h1]
      exact eq_inv_of_mul_eq_one_left (by rw [mul_assoc, hyy, hz2])
    · rw [pow_two, hyy]
      exact hL.ne_one
  refine ⟨q8Hom hpair, q8Hom_injective hpair, fun q => ⟨q8Hom_mem hpair hy hx q, ?_⟩⟩
  refine mem_of_pow_two hTL h3 (k := 3) ?_
  rw [← map_pow, show q ^ 2 ^ 3 = 1 by revert q; decide, map_one]

theorem exists_three_element [T.Normal] (hL : IsClassicalMember3 L z)
    (h3 : memberIndex L T = 3) : ∃ y ∈ L, y ∉ T ∧ ∃ k : ℕ, y ^ 3 ^ k = 1 := by
  by_contra hno
  simp only [not_exists, not_and] at hno
  obtain ⟨ψ, hψs, hψk⟩ := hL.exists_hom
  set M : Subgroup L := T.subgroupOf L ⊔ classicalInvolutionOddCore L with hMdef
  have hle : Subgroup.closure {x : SL(2, ZMod 3) | orderOf x = 3} ≤ M.map ψ := by
    rw [Subgroup.closure_le]
    intro w hw
    obtain ⟨u, rfl⟩ := hψs w
    obtain ⟨e, r, hr3, hr⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos u).ne' 3
      (by norm_num)
    have hur : ((u : Y) ^ r) ^ 3 ^ e = 1 := by
      rw [← pow_mul, mul_comm, ← hr, ← Subgroup.coe_pow, pow_orderOf_eq_one, Subgroup.coe_one]
    have huT : u ^ r ∈ M := Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr (by
      rw [Subgroup.coe_pow]
      by_contra hT
      exact hno _ (pow_mem u.2 r) hT e hur))
    have hcop : Nat.Coprime r (orderOf (ψ u)) := by
      rw [show orderOf (ψ u) = 3 from hw]
      exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hr3).symm
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm, ← map_pow, ← map_pow]
    exact Subgroup.mem_map_of_mem ψ (pow_mem huT m)
  have hM : M = ⊤ := by
    have hclos := LieType.HighestRoot.closure_orderOf_three_eq_top (K := ZMod 3)
      (by rw [Nat.card_zmod])
    rw [hclos, top_le_iff] at hle
    refine eq_top_iff.mpr fun l _ => ?_
    obtain ⟨m, hm, hml⟩ := (Subgroup.mem_map.mp (hle ▸ Subgroup.mem_top (ψ l)) :
      ∃ m ∈ M, ψ m = ψ l)
    have hk : m⁻¹ * l ∈ classicalInvolutionOddCore L :=
      (hψk _).mp (by rw [map_mul, map_inv, hml, inv_mul_cancel])
    have := mul_mem hm (Subgroup.mem_sup_right hk : m⁻¹ * l ∈ M)
    rwa [mul_inv_cancel_left] at this
  have h1 : memberIndex L T = 1 := by
    rw [memberIndex, ← hMdef, hM, Subgroup.index_top]
  omega

omit [Finite Y] in
theorem isSubnormal_trans {A B C : Subgroup Y} (h₁ : IsSubnormal A B) (h₂ : IsSubnormal B C) :
    IsSubnormal A C :=
  h₁.trans h₂

theorem commute_of_isComponentOf [T.Normal] (hL : IsClassicalMember3 L z) {K : Subgroup Y}
    (hK : IsComponentOf K (T ⊓ Subgroup.centralizer ({z} : Set Y))) :
    ∀ l ∈ L, ∀ k ∈ K, l * k = k * l := by
  set C := Subgroup.centralizer ({z} : Set Y) with hCdef
  have hCT : T ⊓ C ≤ C := inf_le_right
  have hnT : ((T ⊓ C).subgroupOf C).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (inferInstance : T.Normal).conj_mem _ (Subgroup.mem_inf.mp hn).1 g
    · exact mul_mem (mul_mem g.2 (Subgroup.mem_inf.mp hn).2) (inv_mem g.2)
  have hKC : IsSubnormal K C :=
    isSubnormal_trans hK.2.1 (IsSubnormal.step hCT hnT (IsSubnormal.refl C))
  have hKle : K ≤ C := hK.1.trans hCT
  have hLle : L ≤ C := hL.le_centralizer
  have hKc : IsComponentOf (K.subgroupOf C) ⊤ :=
    ⟨le_top, (ComponentClassification.LBalance.subnormal_subgroupOf_iff hKle).mpr hKC,
      ComponentClassification.Components.quasisimple_of_equiv
        (Subgroup.subgroupOfEquivOfLe hKle) hK.2.2⟩
  have hLs : IsSubnormal (L.subgroupOf C) ⊤ :=
    (ComponentClassification.LBalance.subnormal_subgroupOf_iff hLle).mpr hL.subnormal
  have : Group.IsSolvable (L.subgroupOf C) := by
    have := hL.isSolvable
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hLle).toMonoidHom) (MulEquiv.injective _)
  have hc := ComponentClassification.LocalComponents.commutes_with_solvable_subnormal
    (K.subgroupOf C) (L.subgroupOf C) hKc hLs
  intro l hl k hk
  have hmem : ⁅(⟨k, hKle hk⟩ : C), (⟨l, hLle hl⟩ : C)⁆ ∈ ⁅K.subgroupOf C, L.subgroupOf C⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mpr hk)
      (Subgroup.mem_subgroupOf.mpr hl)
  rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact (congrArg Subtype.val hmem).symm

end CFSG.ClassicalInvolution.Q3.TA3.Frame
