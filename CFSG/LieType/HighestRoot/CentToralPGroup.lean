module

public import CFSG.LieType.HighestRoot.CentTrialitySL2
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.WeylCharStab

public section

namespace CFSG.LieType.HighestRoot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

variable {τ : Tag} {K : Type} [Field K]

theorem mem_toralRootGroup_of_pow_eq_one
    {p n : ℕ} (hp : p.Prime) {a : Fin τ.rank → Kˣ} (ha : ∀ i, a i ^ p = 1)
    {x : ModGL τ K} (hx : x ∈ toralCentralizer τ K a) (hn : Nat.Coprime n p)
    (hxn : x ^ n = 1) : x ∈ toralRootGroup τ K a := by
  obtain ⟨-, hnormal, -, -, φ, hφ, -⟩ :=
    Chevalley_toral_centralizer_root_generated_quotient τ K a
  haveI : ((toralRootGroup τ K a).subgroupOf (toralCentralizer τ K a)).Normal := hnormal
  have hG : IsPGroup p (toralCentralizer τ K a ⧸
      (toralRootGroup τ K a).subgroupOf (toralCentralizer τ K a)) :=
    IsPGroup.of_surjective (isPGroup_quotient hp ha) φ hφ
  let q : toralCentralizer τ K a ⧸
      (toralRootGroup τ K a).subgroupOf (toralCentralizer τ K a) :=
    QuotientGroup.mk ⟨x, hx⟩
  have hq : q ^ n = 1 := by
    change (QuotientGroup.mk ⟨x, hx⟩ :
      toralCentralizer τ K a ⧸
        (toralRootGroup τ K a).subgroupOf (toralCentralizer τ K a)) ^ n = 1
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have hcoe : (⟨x, hx⟩ : toralCentralizer τ K a) ^ n = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow]
      exact hxn
    rw [hcoe]
    exact one_mem _
  have hq1 : q = 1 := by
    have h1 : orderOf q = 1 := by
      refine (hG.orderOf_coprime hn.symm q).eq_one_of_dvd ?_
      exact orderOf_dvd_of_pow_eq_one hq
    exact orderOf_eq_one_iff.1 h1
  change (QuotientGroup.mk ⟨x, hx⟩ :
    toralCentralizer τ K a ⧸
      (toralRootGroup τ K a).subgroupOf (toralCentralizer τ K a)) = 1 at hq1
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq1
  exact hq1

theorem mem_rootSpan_of_mem_toralCentralizer_of_charPow [Finite K]
    {p : ℕ} (hp : p.Prime) (hpK : p ≠ ringChar K) {a : Fin τ.rank → Kˣ}
    (ha : ∀ i, a i ^ p = 1) {x : ModGL τ K} (hx : x ∈ toralCentralizer τ K a)
    (hxr : ∃ n : ℕ, x ^ (ringChar K ^ n) = 1) :
    x ∈ rootSpan τ K (rootCharKernel a) := by
  obtain ⟨n, hn⟩ := hxr
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hchar, hcard⟩ := FiniteField.card K (ringChar K)
  have hm : (m : ℕ) ≠ 0 := m.ne_zero
  have hcop : Nat.Coprime (ringChar K ^ n) p := by
    refine Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hchar).2 ?_)
    exact fun hd => hpK ((Nat.prime_dvd_prime_iff_eq hchar hp).1 hd).symm
  have hxM : x ∈ toralRootGroup τ K a :=
    mem_toralRootGroup_of_pow_eq_one hp ha hx hcop hn
  refine mem_rootSpan_of_mem_toralRootGroup_of_pow ?_ hxM hn
  have hcard' : Nat.card K = ringChar K ^ (m : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcard]
  rw [hcard']
  exact Nat.Coprime.pow_left n (coprime_pow_sub_one hchar hm)

end CFSG.LieType.HighestRoot

end
