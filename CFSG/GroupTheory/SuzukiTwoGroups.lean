module

public import CFSG.GroupTheory.SuzukiTwoGroupsKernel
public import CFSG.GroupTheory.SuzukiTwoGroupsAbelianCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.theorem_1a

public section

namespace CFSG.GroupTheory

open Subgroup

namespace SuzukiTwoGroup

universe u

variable {S : Type u} [Group S] [Finite S] (hS : IsPGroup 2 S) {A : Subgroup (MulAut S)}
  (htrans : ∀ x y : S, orderOf x = 2 → orderOf y = 2 → ∃ a ∈ A, a x = y)
include hS htrans

omit [Finite S] hS in
theorem apply_eq_self_of_apply_eq_self [IsCyclic A] {x₀ : S} (hx₀ : orderOf x₀ = 2) {b : A}
    (hb : (b : MulAut S) x₀ = x₀) {z : S} (hz : orderOf z = 2) : (b : MulAut S) z = z := by
  have hAc : IsMulCommutative A := IsCyclic.isMulCommutative
  obtain ⟨a, ha, rfl⟩ := htrans x₀ z hx₀ hz
  have hab : (b : MulAut S) * a = a * b :=
    congrArg Subtype.val (mul_comm' b (⟨a, ha⟩ : A))
  rw [← MulAut.mul_apply, hab, MulAut.mul_apply, hb]

theorem coprime_card_stabilizer [IsCyclic A] {x₀ : S} (hx₀ : orderOf x₀ = 2) :
    Nat.Coprime (Nat.card (MulAction.stabilizer A x₀)) (Nat.card {x : S // orderOf x = 2}) := by
  by_contra h
  obtain ⟨p, hp, hpA, hpI⟩ := Nat.Prime.not_coprime_iff_dvd.1 h
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := MulAction.stabilizer A x₀) p hpA
  have hgo : orderOf ((g : A) : MulAut S) = p := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hg
  have hgx : ((g : A) : MulAut S) x₀ = x₀ := MulAction.mem_stabilizer_iff.1 g.2
  refine false_of_apply_eq_self_of_pow_eq_one hS htrans hx₀ (g : A).2
    (fun z hz => apply_eq_self_of_apply_eq_self htrans hx₀ hgx hz) hp
    (by rw [← hgo]; exact pow_orderOf_eq_one _) (fun h1 => ?_) hpI
  rw [h1, orderOf_one] at hgo
  exact hp.one_lt.ne hgo

theorem exists_regular_subgroup [IsCyclic A] {x₀ : S} (hx₀ : orderOf x₀ = 2) :
    ∃ B : Subgroup A, IsCyclic B ∧ ∀ x y : S, orderOf x = 2 → orderOf y = 2 →
      ∃! b : B, ((b : A) : MulAut S) x = y := by
  classical
  set A₀ := MulAction.stabilizer A x₀ with hA₀def
  set I := Nat.card {x : S // orderOf x = 2} with hIdef
  have hcop := coprime_card_stabilizer hS htrans hx₀
  have hcm : Nat.card A₀ * I = Nat.card A := by
    rw [hIdef, ← index_stabilizer_eq_card_involutions htrans hx₀]
    exact A₀.card_mul_index
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := A)
  have hγo : orderOf γ = Nat.card A := orderOf_eq_card_of_forall_mem_zpowers hγ
  have hA₀0 : Nat.card A₀ ≠ 0 := Nat.card_pos.ne'
  have hδo : orderOf (γ ^ Nat.card A₀) = I := by
    rw [orderOf_pow_of_dvd hA₀0 (by rw [hγo, ← hcm]; exact dvd_mul_right _ _), hγo, ← hcm,
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hA₀0)]
  refine ⟨zpowers (γ ^ Nat.card A₀), inferInstance, fun x y hx hy => ?_⟩
  have hfree : ∀ b : zpowers (γ ^ Nat.card A₀), ((b : A) : MulAut S) x = x → b = 1 := by
    intro b hb
    have hbA₀ : (b : A) ∈ A₀ := MulAction.mem_stabilizer_iff.2
      (apply_eq_self_of_apply_eq_self htrans hx hb hx₀)
    have h1 : orderOf (b : A) ∣ Nat.card A₀ := Subgroup.orderOf_dvd_natCard A₀ hbA₀
    have h2 : orderOf (b : A) ∣ I := by
      have h := Subgroup.orderOf_dvd_natCard _ b.2
      rwa [Nat.card_zpowers, hδo] at h
    have h3 : orderOf (b : A) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    exact Subtype.ext (orderOf_eq_one_iff.1 h3)
  let f : zpowers (γ ^ Nat.card A₀) → {z : S // orderOf z = 2} := fun b =>
    ⟨((b : A) : MulAut S) x, by rw [MulEquiv.orderOf_eq]; exact hx⟩
  have hfinj : Function.Injective f := by
    intro b b' hbb'
    have h : ((b : A) : MulAut S) x = ((b' : A) : MulAut S) x := congrArg Subtype.val hbb'
    have h' : (((b'⁻¹ * b : zpowers (γ ^ Nat.card A₀)) : A) : MulAut S) x = x := by
      change ((b' : A) : MulAut S)⁻¹ (((b : A) : MulAut S) x) = x
      rw [h, MulAut.inv_apply, MulEquiv.symm_apply_apply]
    exact (inv_mul_eq_one.1 (hfree _ h')).symm
  have hfbij : Function.Bijective f := hfinj.bijective_of_nat_card_le (by
    rw [Nat.card_zpowers, hδo])
  obtain ⟨b, hb⟩ := hfbij.2 ⟨y, hy⟩
  refine ⟨b, congrArg Subtype.val hb, fun b' hb' => hfinj ?_⟩
  rw [hb]
  exact Subtype.ext hb'

end SuzukiTwoGroup

open SuzukiTwoGroup

universe u

theorem isSuzukiTwoGroup_appendixIII {S : Type u} [Group S] (hS : IsSuzukiTwoGroup S) :
    BenderSuzuki.PFAppendixIII.IsSuzukiTwoGroup S := by
  obtain ⟨hfin, hS2, hnab, ⟨x₀, y₀, hx₀, hy₀, hxy⟩, A, hAcyc, htrans⟩ := hS
  have hinvol : ∀ x : S, orderOf x = 2 → BenderSuzuki.PFAppendixIII.IsInvolution x :=
    fun x hx => ⟨(orderOf_eq_two_iff_sq_eq_one.1 hx).2, (orderOf_eq_two_iff_sq_eq_one.1 hx).1⟩
  have hinvol' : ∀ x : S, BenderSuzuki.PFAppendixIII.IsInvolution x → orderOf x = 2 :=
    fun x hx => orderOf_eq_two_iff_sq_eq_one.2 ⟨hx.2, hx.1⟩
  refine ⟨?_, hnab, ⟨x₀, y₀, hinvol x₀ hx₀, hinvol y₀ hy₀, hxy⟩, ?_⟩
  · obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hS2
    exact ⟨n, by rw [Subgroup.card_top]; exact hn⟩
  · obtain ⟨B, hBcyc, hreg⟩ := exists_regular_subgroup hS2 htrans hx₀
    refine ⟨B, inferInstance, inferInstance, hBcyc, ⟨fun {b₁ b₂} h => ?_⟩, ?_, ?_⟩
    · exact Subtype.ext (Subtype.ext (MulEquiv.ext h))
    · intro x hx b
      exact hinvol _ (by
        change orderOf (((b : A) : MulAut S) x) = 2
        rw [MulEquiv.orderOf_eq]
        exact hinvol' x hx)
    · intro x hx y hy
      obtain ⟨b, hb, hbu⟩ := hreg x y (hinvol' x hx) (hinvol' y hy)
      exact ⟨b, hb.symm, fun b' hb' => hbu b' hb'.symm⟩

theorem IsSuzukiTwoGroup.higman {S : Type u} [Group S] (hS : IsSuzukiTwoGroup S) :
    omega₁ S (p := 2) = center S ∧ center S = frattini S ∧
      frattini S = _root_.commutator S ∧ IsElementaryAbelian 2 (center S) ∧
      ∃ n : ℕ, 2 ≤ n ∧ Nat.card (center S) = 2 ^ n ∧ Monoid.exponent S = 4 ∧
        Group.nilpotencyClass S = 2 ∧
        (Nat.card S = (2 ^ n) ^ 2 ∨ Nat.card S = (2 ^ n) ^ 3) := by
  have hP := isSuzukiTwoGroup_appendixIII hS
  obtain ⟨hfin, hS2, hnab, ⟨x₀, y₀, hx₀, hy₀, hxy⟩, A, hAcyc, htrans⟩ := hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 S) := ⟨hS2⟩
  obtain ⟨-, hZ2⟩ := BenderSuzuki.External.Higman.theorem1_involutions_center hP
  have h2 := BenderSuzuki.External.Higman.theorem1_center_quotient_orders_and_exponent hP
  dsimp only at h2
  obtain ⟨hQcomm, hQ2, -, hcard, h4⟩ := h2
  have hZsq : ∀ z ∈ center S, z ^ 2 = 1 := fun z hz => congrArg Subtype.val (hZ2 ⟨z, hz⟩)
  have hΩ : omega₁ S (p := 2) = center S := by
    ext x
    rw [mem_omega₁_iff hS2 htrans]
    constructor
    · intro hx
      by_cases hx1 : x = 1
      · rw [hx1]
        exact one_mem _
      · exact mem_center_of_orderOf_eq_two hS2 htrans (orderOf_eq_two_iff_sq_eq_one.2 ⟨hx, hx1⟩)
    · exact hZsq x
  have hcomm_le : _root_.commutator S ≤ center S :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).1 hQcomm
  have hcomm_ne : _root_.commutator S ≠ ⊥ := fun h => hnab ((_root_.commutator_eq_bot_iff S).1 h)
  have hcomm_st : IsStable A (_root_.commutator S) := fun a _ t ht =>
    (Subgroup.characteristic_iff_le_comap.mp inferInstance a) ht
  have hS' : _root_.commutator S = center S := by
    refine le_antisymm hcomm_le ?_
    rw [← hΩ]
    exact omega₁_le_of_isStable hS2 htrans hcomm_ne hcomm_st
  have hsqZ : ∀ x : S, x ^ 2 ∈ center S := fun x => by
    have h := hQ2 (x : S ⧸ center S)
    rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h
  have hΦ : frattini S = center S := by
    apply le_antisymm
    · rw [frattini_eq_closure_commutator_union_powers (p := 2), closure_le]
      rintro x (hx | ⟨y, rfl⟩)
      · exact hcomm_le hx
      · exact hsqZ y
    · rw [← hS']
      exact commutator_le_frattini_of_isPGroup (p := 2)
  have hZel : IsElementaryAbelian 2 (center S) :=
    { toIsMulCommutative := IsMulCommutative.of_comm fun a b =>
        Subtype.ext (Subgroup.mem_center_iff.1 b.2 a)
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun z => hZ2 z }
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (hS2.to_subgroup (center S))
  have hn2 : 2 ≤ n := by
    classical
    have hx₀Z := mem_center_of_orderOf_eq_two hS2 htrans hx₀
    have hy₀Z := mem_center_of_orderOf_eq_two hS2 htrans hy₀
    let _ : Fintype (center S) := Fintype.ofFinite _
    have h3 : 3 ≤ Nat.card (center S) := by
      rw [Nat.card_eq_fintype_card]
      have hne1 : (1 : center S) ≠ ⟨x₀, hx₀Z⟩ := fun h =>
        (orderOf_eq_two_iff_sq_eq_one.1 hx₀).2 (congrArg Subtype.val h).symm
      have hne2 : (1 : center S) ≠ ⟨y₀, hy₀Z⟩ := fun h =>
        (orderOf_eq_two_iff_sq_eq_one.1 hy₀).2 (congrArg Subtype.val h).symm
      have hne3 : (⟨x₀, hx₀Z⟩ : center S) ≠ ⟨y₀, hy₀Z⟩ := fun h =>
        hxy (congrArg Subtype.val h)
      have hcard3 : ({1, ⟨x₀, hx₀Z⟩, ⟨y₀, hy₀Z⟩} : Finset (center S)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hne1, hne2]), Finset.card_pair hne3]
      exact hcard3 ▸ Finset.card_le_univ _
    by_contra h
    push Not at h
    interval_cases n <;> rw [hn] at h3 <;> norm_num at h3
  have hexp : Monoid.exponent S = 4 := by
    have hdvd : Monoid.exponent S ∣ 2 ^ 2 := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 h4
    have hnot2 : ¬ Monoid.exponent S ∣ 2 := fun h => hnab (IsMulCommutative.of_comm fun a b =>
      Commute.of_orderOf_dvd_two (fun g => (Monoid.order_dvd_exponent g).trans h) a b)
    obtain ⟨i, hi, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    interval_cases i
    · exact absurd (he ▸ one_dvd 2) hnot2
    · exact absurd (he ▸ dvd_refl 2) hnot2
    · rw [he]
      norm_num
  have hnil : Group.IsNilpotent S := hS2.isNilpotent
  have hclass : Group.nilpotencyClass S = 2 := by
    apply le_antisymm
    · rw [← Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le, eq_top_iff]
      intro x _
      rw [Subgroup.mem_upperCentralSeries_succ_iff, Subgroup.upperCentralSeries_one]
      intro y
      exact hcomm_le (commutator_mem_commutator (mem_top x) (mem_top y))
    · by_contra h
      push Not at h
      have h1 : Group.nilpotencyClass S ≤ 1 := by omega
      rw [← Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le,
        Subgroup.upperCentralSeries_one] at h1
      exact hnab ((_root_.commutator_eq_bot_iff S).1
        ((_root_.commutator_eq_bot_iff_center_eq_top S).2 h1))
  refine ⟨hΩ, hΦ.symm, hΦ.trans hS'.symm, hZel, n, hn2, hn, hexp, hclass, ?_⟩
  rw [← hn]
  exact hcard

universe v w

theorem higman_suzuki_two_groups :
    (∀ (S : Type u) [Group S], IsSuzukiTwoGroup S →
      omega₁ S (p := 2) = center S ∧ center S = frattini S ∧
        frattini S = _root_.commutator S ∧ IsElementaryAbelian 2 (center S) ∧
        ∃ n : ℕ, 2 ≤ n ∧ Nat.card (center S) = 2 ^ n ∧ Monoid.exponent S = 4 ∧
          Group.nilpotencyClass S = 2 ∧
          (Nat.card S = (2 ^ n) ^ 2 ∨ Nat.card S = (2 ^ n) ^ 3)) ∧
    (∀ (U : Type v) (Y : Type w) [Group U] [Group Y] [Finite U] [Finite Y] [IsCyclic Y] (n : ℕ),
      1 ≤ n → Nat.card U = (2 ^ n) ^ 2 → Nat.card Y = 2 ^ n - 1 →
      ∀ ρ : Y →* MulAut U, (∀ y : Y, y ≠ 1 → ∀ u : U, ρ y u = u → u = 1) →
      ∀ (V : Subgroup U) [V.Normal], (∀ y : Y, ∀ v ∈ V, ρ y v ∈ V) →
      ∀ [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 (U ⧸ V)] (θ : U ⧸ V ≃* V),
      (∀ (y : Y) (u : U),
        ((θ ((ρ y u : U) : U ⧸ V) : V) : U) = ρ y ((θ (u : U ⧸ V) : V) : U)) →
      IsMulCommutative U) :=
  ⟨fun _ _ hS => hS.higman, fun _ _ _ _ _ _ _ _ hn hU hY ρ hfix V _ hVY _ _ θ hθ =>
    isMulCommutative_of_fixedPointFree_cyclic hn hU hY ρ hfix V hVY θ hθ⟩

end CFSG.GroupTheory
