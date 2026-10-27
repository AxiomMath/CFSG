module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.CharacterTheory.Burnside
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Index
import CFSG.FeitThompson.OddOrderTheorem
import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem isSolvable_inf_normalizer_of_isSylowOf_two {R YB : Subgroup G}
    (hYB : CFSG.ABGLocalTools.IsSylowOf 2 YB R) :
    Group.IsSolvable ↥(R ⊓ normalizer (YB : Set G)) := by
  have hYBN : YB ≤ R ⊓ normalizer (YB : Set G) := le_inf hYB.le Subgroup.le_normalizer
  have hNN : R ⊓ normalizer (YB : Set G) ≤ normalizer (YB : Set G) := inf_le_right
  haveI hnorm : (YB.subgroupOf (R ⊓ normalizer (YB : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYBN).mpr hNN
  have hP2 : IsPGroup 2 (YB.subgroupOf (R ⊓ normalizer (YB : Set G))) :=
    hYB.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hYBN).symm
  haveI : Group.IsNilpotent ↥(YB.subgroupOf (R ⊓ normalizer (YB : Set G))) :=
    hP2.isNilpotent
  haveI : Group.IsSolvable ↥(YB.subgroupOf (R ⊓ normalizer (YB : Set G))) := inferInstance
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 YB (R ⊓ normalizer (YB : Set G)) :=
    hYB.of_le hYBN inf_le_left
  have hnd : ¬ 2 ∣ (YB.subgroupOf (R ⊓ normalizer (YB : Set G))).index :=
    (CFSG.ABGLocalTools.isSylowOf_iff.mp hSyl).2.2
  have hodd : Odd (Nat.card (↥(R ⊓ normalizer (YB : Set G)) ⧸
      YB.subgroupOf (R ⊓ normalizer (YB : Set G)))) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hnd)
  haveI : Group.IsSolvable (↥(R ⊓ normalizer (YB : Set G)) ⧸
      YB.subgroupOf (R ⊓ normalizer (YB : Set G))) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  exact Group.isSolvable_of_subgroup_quotient (YB.subgroupOf (R ⊓ normalizer (YB : Set G)))

private theorem eq_pow_mul_pow_of_prime_dvd_two_p {n p q : ℕ} (hn : n ≠ 0) (hpq : p ≠ q)
    (h : ∀ r : ℕ, r.Prime → r ∣ n → r = p ∨ r = q) :
    n = p ^ n.factorization p * q ^ n.factorization q := by
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod_of_support_subset _ (s := {p, q}) ?_ _ (fun _ _ => pow_zero _),
    Finset.prod_pair hpq]
  intro r hr
  rw [Nat.support_factorization] at hr
  have := h r (Nat.prime_of_mem_primeFactors hr) (Nat.dvd_of_mem_primeFactors hr)
  simpa using this

private theorem isSolvable_of_le_normalizer_of_relIndex {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {R L : Subgroup G} (hLn : L ≤ normalizer (R : Set G))
    (hR : Group.IsSolvable ↥(R ⊓ L))
    (hprime : ∀ q : ℕ, q.Prime → q ∣ R.relIndex L → q = 2 ∨ q = p) :
    Group.IsSolvable ↥L := by
  haveI hRLn : (R.subgroupOf L).Normal :=
    ⟨fun n hn g => Subgroup.le_set_normalizer_iff.mp hLn (g : G) g.2 (n : G)
      (Subgroup.mem_subgroupOf.mp hn)⟩
  have hRLsolv : Group.IsSolvable ↥(R.subgroupOf L) := by
    let φ : ↥(R.subgroupOf L) →* ↥(R ⊓ L) :=
      { toFun := fun x => ⟨(x.1 : G), Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp x.2, x.1.2⟩⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hφ : Function.Injective φ := by
      intro x y hxy
      have h1 : ((φ x : ↥(R ⊓ L)) : G) = ((φ y : ↥(R ⊓ L)) : G) := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h1)
    exact Group.isSolvable_of_isSolvable_injective hφ
  have hn0 : R.relIndex L ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hfac : R.relIndex L =
      2 ^ (R.relIndex L).factorization 2 * p ^ (R.relIndex L).factorization p :=
    eq_pow_mul_pow_of_prime_dvd_two_p hn0 (Ne.symm hp2) hprime
  haveI : Fintype (↥L ⧸ R.subgroupOf L) := Fintype.ofFinite _
  have hcardQ : Nat.card (↥L ⧸ R.subgroupOf L) = R.relIndex L := rfl
  have hcard : Fintype.card (↥L ⧸ R.subgroupOf L) =
      2 ^ (R.relIndex L).factorization 2 * p ^ (R.relIndex L).factorization p := by
    rw [Fintype.card_eq_nat_card, hcardQ]
    exact hfac
  haveI hQ : Group.IsSolvable (↥L ⧸ R.subgroupOf L) :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two hp
      (Ne.symm hp2) hcard
  exact Group.isSolvable_of_subgroup_quotient (R.subgroupOf L)

theorem solvable_normalizer_inf_of_sylow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {H R YB : Subgroup G} (hRH : R ≤ H) (hRn : H ≤ normalizer (R : Set G))
    (hidx : ∀ q : ℕ, q.Prime → q ∣ R.relIndex H → q = 2 ∨ q = p)
    (hYB : CFSG.ABGLocalTools.IsSylowOf 2 YB R) :
    Group.IsSolvable ↥(H ⊓ normalizer (YB : Set G)) := by
  have hNR : Group.IsSolvable ↥(R ⊓ normalizer (YB : Set G)) :=
    isSolvable_inf_normalizer_of_isSylowOf_two hYB
  have hLn : H ⊓ normalizer (YB : Set G) ≤ normalizer (R : Set G) := inf_le_left.trans hRn
  have hRL : R ⊓ (H ⊓ normalizer (YB : Set G)) = R ⊓ normalizer (YB : Set G) := by
    rw [← inf_assoc, inf_eq_left.mpr hRH]
  have hR : Group.IsSolvable ↥(R ⊓ (H ⊓ normalizer (YB : Set G))) := by
    rw [hRL]
    exact hNR
  have hdvd : R.relIndex (H ⊓ normalizer (YB : Set G)) ∣ R.relIndex H := by
    have h1 : R.relIndex ((H ⊓ normalizer (YB : Set G)) ⊔ R) *
        ((H ⊓ normalizer (YB : Set G)) ⊔ R).relIndex H = R.relIndex H :=
      Subgroup.relIndex_mul_relIndex (H := R) (K := (H ⊓ normalizer (YB : Set G)) ⊔ R) (L := H)
        le_sup_right (sup_le inf_le_left hRH)
    rw [relIndex_sup_of_le_normalizer hLn] at h1
    exact Dvd.intro _ h1
  exact isSolvable_of_le_normalizer_of_relIndex hp hp2 hLn hR
    (fun q hq hqL => hidx q hq (hqL.trans hdvd))

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
