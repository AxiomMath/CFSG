module

public import CFSG.Adapters.WholeGroupLayer
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Core
public import TauCeti.GroupTheory.OrderOfElement.PPart

public section

namespace CFSG.GroupTheory

open Subgroup

section Generic

variable {Q : Type} [Group Q] [Finite Q]

theorem mem_centralizer_of_mem_sup_centralizer_of_coprime (J : Subgroup Q) {y : Q}
    (hy : y ∈ J ⊔ Subgroup.centralizer (J : Set Q)) {n : ℕ} (hyn : y ^ n = 1)
    (hcop : n.Coprime (Nat.card J)) : y ∈ Subgroup.centralizer (J : Set Q) := by
  have hLC : J ≤ Subgroup.normalizer (Subgroup.centralizer (J : Set Q) : Set Q) :=
    Subgroup.le_normalizer.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _))
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLC] at hy
  obtain ⟨k, hk, c, hc, rfl⟩ := hy
  have hcomm : Commute k c := Subgroup.mem_centralizer_iff.mp hc k hk
  have h1 : k ^ n * c ^ n = 1 := by
    rw [← hcomm.mul_pow, hyn]
  have hkn_mem : k ^ n ∈ Subgroup.centralizer (J : Set Q) := by
    rw [eq_inv_of_mul_eq_one_left h1]
    exact Subgroup.inv_mem _ (pow_mem hc n)
  have hnk : n.Coprime (orderOf k) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard J hk) hcop
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hnk
  have hkC : k ∈ Subgroup.centralizer (J : Set Q) := by
    have h := pow_mem hkn_mem m
    rwa [hm] at h
  exact Subgroup.mul_mem _ hkC hc

theorem isPGroup_of_forall_fix_disp {U : Type*} [Group U] [Finite U] {q : ℕ}
    [Fact q.Prime] {C W : Subgroup U} (hW : IsPGroup q W)
    (hfix : IsPGroup q (fixingSubgroup (MulAut U) (C : Set U))) {A : Subgroup (MulAut U)}
    (hAW : ∀ α ∈ A, ∀ w ∈ W, α w = w) (hAC : ∀ α ∈ A, ∀ c ∈ C, c⁻¹ * α c ∈ W) :
    IsPGroup q A := by
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hW
  rintro ⟨α, hα⟩
  have hpow : ∀ c ∈ C, ∀ n : ℕ, (α ^ n) c = c * (c⁻¹ * α c) ^ n := by
    intro c hc n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hAW α hα _ (hAC α hα c hc),
        pow_succ', ← mul_assoc, mul_inv_cancel_left]
  have hfixα : α ^ q ^ a ∈ fixingSubgroup (MulAut U) (C : Set U) := by
    rw [mem_fixingSubgroup_iff]
    intro c hc
    rw [MulAut.smul_def, hpow c hc]
    have hw : (⟨c⁻¹ * α c, hAC α hα c hc⟩ : W) ^ Nat.card W = 1 := pow_card_eq_one'
    rw [ha] at hw
    have hw' : (c⁻¹ * α c) ^ q ^ a = 1 := congrArg Subtype.val hw
    rw [hw', mul_one]
  obtain ⟨b, hb⟩ := hfix ⟨_, hfixα⟩
  refine ⟨a + b, Subtype.ext ?_⟩
  have hb' : (α ^ q ^ a) ^ q ^ b = 1 := congrArg Subtype.val hb
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [pow_add, pow_mul, hb']

theorem map_commutator_eq_bot_of_isCyclic {H A : Type*} [Group H] [Group A] [IsCyclic A]
    (φ : H →* MulAut A) : (commutator H).map φ = ⊥ := by
  have hc : ∀ a b : MulAut A, a * b = b * a := fun a b =>
    (IsCyclic.mulAutMulEquiv (G := A)).injective (by rw [map_mul, map_mul, mul_comm])
  rw [commutator_def, Subgroup.map_commutator, eq_bot_iff, Subgroup.commutator_le]
  intro a _ b _
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact hc a b

theorem mem_centralizer_of_mem_fittingSubgroup_of_coprime {p : ℕ} {H : Subgroup Q}
    (hH : ∀ q : ℕ, q.Prime → q ≠ p → H ≤ Subgroup.centralizer (CFSG.pCore q Q : Set Q))
    {x : Q} (hx : x ∈ CFSG.fittingSubgroup Q) (hxp : (orderOf x).Coprime p) :
    x ∈ Subgroup.centralizer (H : Set Q) := by
  suffices h : ∀ n : ℕ, ∀ x : Q, orderOf x = n → x ∈ CFSG.fittingSubgroup Q →
      (orderOf x).Coprime p → x ∈ Subgroup.centralizer (H : Set Q) from h _ x rfl hx hxp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hn hx hxp
    have hn0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
    by_cases h1 : n = 1
    · rw [h1, orderOf_eq_one_iff] at hn
      rw [hn]
      exact Subgroup.one_mem _
    obtain ⟨q, hq, hqn⟩ := Nat.exists_prime_and_dvd h1
    have hqp : q ≠ p := by
      rintro rfl
      exact (Nat.Prime.coprime_iff_not_dvd hq).mp (hn ▸ hxp).symm hqn
    haveI : Fact q.Prime := ⟨hq⟩
    have hzx : Subgroup.zpowers x ≤ CFSG.fittingSubgroup Q := Subgroup.zpowers_le.mpr hx
    have hpart_mem := hzx (TauCeti.pPart_mem_zpowers q x)
    have hfree_mem := hzx (TauCeti.pFreePart_mem_zpowers q x)
    have hpart_q : ∃ k : ℕ, TauCeti.pPart q x ^ q ^ k = 1 :=
      ⟨(orderOf x).factorization q, by rw [← TauCeti.orderOf_pPart hq hn0, pow_orderOf_eq_one]⟩
    have hpart_C : TauCeti.pPart q x ∈ Subgroup.centralizer (H : Set Q) :=
      Subgroup.le_centralizer_iff.mp (hH q hq hqp)
        (CFSG.RankThree.PartTwo.Sec4.Census.mem_pCore_of_mem_fittingSubgroup hpart_mem hpart_q)
    have hord : orderOf (TauCeti.pFreePart q x) = n / q ^ n.factorization q := by
      rw [TauCeti.orderOf_pFreePart hq hn0, hn]
    have hn0' : 0 < n := hn ▸ orderOf_pos x
    have hlt : orderOf (TauCeti.pFreePart q x) < n := by
      rw [hord]
      exact Nat.div_lt_self hn0'
        (Nat.one_lt_pow (Nat.pos_iff_ne_zero.mp
          (Nat.Prime.factorization_pos_of_dvd hq hn0'.ne' hqn)) hq.one_lt)
    have hfree_cop : (orderOf (TauCeti.pFreePart q x)).Coprime p := by
      rw [hord]
      exact Nat.Coprime.coprime_dvd_left (Nat.ordCompl_dvd n q) (hn ▸ hxp)
    have hfree_C := ih _ hlt _ rfl hfree_mem hfree_cop
    rw [← TauCeti.pPart_mul_pFreePart q x]
    exact Subgroup.mul_mem _ hpart_C hfree_C

theorem isNilpotent_of_le_centralizer_layer_pCores {p : ℕ} (hp : p.Prime)
    {Y : Subgroup Q}
    (h1 : Y ≤ Subgroup.centralizer (CFSG.layer Q : Set Q))
    (h2 : ∀ q : ℕ, q.Prime → q ≠ p → Y ≤ Subgroup.centralizer (CFSG.pCore q Q : Set Q))
    (h3 : ∀ x ∈ Y, ∃ n : ℕ, x ^ p ^ n ∈ Subgroup.centralizer (CFSG.pCore p Q : Set Q)) :
    Group.IsNilpotent Y := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcent : ∀ y ∈ Y, (orderOf y).Coprime p → y ∈ Subgroup.centralizer (Y : Set Q) := by
    intro y hy hyp
    have hyOp : y ∈ Subgroup.centralizer (CFSG.pCore p Q : Set Q) := by
      obtain ⟨n, hn⟩ := h3 y hy
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (Nat.Coprime.pow_left n hyp.symm)
      have h := pow_mem hn m
      rwa [hm] at h
    have hzF : Subgroup.zpowers y ≤ Subgroup.centralizer (CFSG.fittingSubgroup Q : Set Q) := by
      refine CFSG.subgroup_le_centralizer_fitting_of_le_centralizer_pCores fun q => ?_
      rw [Subgroup.zpowers_le]
      have hq : ((q : ℕ)).Prime := Nat.prime_of_mem_primeFactors q.1.2
      by_cases hqp : ((q : ℕ)) = p
      · rw [hqp]
        exact hyOp
      · exact h2 _ hq hqp hy
    have hzE : Subgroup.zpowers y ≤ Subgroup.centralizer (CFSG.layer Q : Set Q) :=
      Subgroup.zpowers_le.mpr (h1 hy)
    have hyFstar : y ∈ Subgroup.centralizer (CFSG.generalizedFitting Q : Set Q) := by
      rw [← Subgroup.zpowers_le, Subgroup.le_centralizer_iff, CFSG.generalizedFitting.eq_sup]
      exact sup_le (Subgroup.le_centralizer_iff.mp hzF) (Subgroup.le_centralizer_iff.mp hzE)
    exact mem_centralizer_of_mem_fittingSubgroup_of_coprime h2
      (CFSG.Adapters.centralizer_generalizedFitting_le_fittingSubgroup Q hyFstar) hyp
  let π : ↥Y →* ↥Y ⧸ Subgroup.center ↥Y := QuotientGroup.mk' (Subgroup.center ↥Y)
  have hpq : IsPGroup p (↥Y ⧸ Subgroup.center ↥Y) := by
    intro z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥Y) z
    have hg0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
    have hfree : TauCeti.pFreePart p g ∈ Subgroup.center ↥Y := by
      have hcop : (orderOf ((TauCeti.pFreePart p g : ↥Y) : Q)).Coprime p := by
        rw [Subgroup.orderOf_coe]
        exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr
          (TauCeti.not_dvd_orderOf_pFreePart hp hg0)).symm
      have hC := hcent _ (TauCeti.pFreePart p g).2 hcop
      rw [Subgroup.mem_center_iff]
      intro h
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hC h h.2)
    refine ⟨(orderOf g).factorization p, ?_⟩
    have hk : TauCeti.pPart p g ^ p ^ (orderOf g).factorization p = 1 := by
      rw [← TauCeti.orderOf_pPart hp hg0, pow_orderOf_eq_one]
    have hπfree : π (TauCeti.pFreePart p g) = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hfree
    have hg : π g = π (TauCeti.pPart p g) := by
      conv_lhs => rw [← TauCeti.pPart_mul_pFreePart p g]
      rw [map_mul, hπfree, mul_one]
    show π g ^ p ^ (orderOf g).factorization p = 1
    rw [hg, ← map_pow, hk, map_one]
  haveI : Group.IsNilpotent (↥Y ⧸ Subgroup.center ↥Y) := hpq.isNilpotent
  exact Subgroup.isNilpotent_of_ker_le_center π (by rw [QuotientGroup.ker_mk'])

end Generic

end CFSG.GroupTheory