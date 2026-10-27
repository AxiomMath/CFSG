module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.GroupAction.CardCommute
public import Mathlib.GroupTheory.Index
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.Basic

public section

namespace CFSG.GroupTheory.SuzukiTwoGroup

open Subgroup

variable {S : Type*} [Group S]

theorem eq_one_of_pow_eq_one_of_odd (hS : IsPGroup 2 S) {m : ℕ} (hm : Odd m) {x : S}
    (hx : x ^ m = 1) : x = 1 := by
  obtain ⟨j, hj⟩ := hS x
  have hcop : Nat.Coprime (2 ^ j) m := Nat.Coprime.pow_left j (Nat.coprime_two_left.2 hm)
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hj)
    (orderOf_dvd_of_pow_eq_one hx))

theorem pow_apply_eq_mul_pow (β : MulAut S) (r : S) (hc : β (r⁻¹ * β r) = r⁻¹ * β r) :
    ∀ k : ℕ, (β ^ k) r = r * (r⁻¹ * β r) ^ k
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ', MulAut.mul_apply, pow_apply_eq_mul_pow β r hc k, map_mul, map_pow, hc,
      pow_succ', ← mul_assoc, mul_inv_cancel_left]

theorem apply_eq_self_of_apply_commElem_eq (hS : IsPGroup 2 S) (β : MulAut S) {m : ℕ}
    (hm : Odd m) (hβm : β ^ m = 1) {r : S} (hc : β (r⁻¹ * β r) = r⁻¹ * β r) : β r = r := by
  have h := pow_apply_eq_mul_pow β r hc m
  rw [hβm, MulAut.one_apply] at h
  have hcm : (r⁻¹ * β r) ^ m = 1 := by
    have h' : r * 1 = r * (r⁻¹ * β r) ^ m := by rw [mul_one]; exact h
    exact (mul_left_cancel h').symm
  have h1 := eq_one_of_pow_eq_one_of_odd hS hm hcm
  rw [inv_mul_eq_one] at h1
  exact h1.symm

theorem eq_one_of_mem_closure_inv_mul_of_fixed {Q : Type*} [Group Q] [IsMulCommutative Q]
    (T : Q →* Q) {m : ℕ} (hm : Odd m) (hTm : ∀ q, T^[m] q = q)
    (h2 : ∀ q : Q, ∃ j : ℕ, q ^ 2 ^ j = 1) {w : Q}
    (hw : w ∈ Subgroup.closure (Set.range fun q => q⁻¹ * T q)) (hTw : T w = w) : w = 1 := by
  let _ : CommGroup Q := { (inferInstance : Group Q) with mul_comm := mul_comm' }
  let ν : Q →* Q :=
    { toFun := fun q => ∏ i ∈ Finset.range m, T^[i] q
      map_one' := by simp [iterate_map_one]
      map_mul' := fun x y => by
        simp only [iterate_map_mul]
        exact Finset.prod_mul_distrib }
  have hgen : ∀ q, ν (q⁻¹ * T q) = 1 := by
    intro q
    change ∏ i ∈ Finset.range m, T^[i] (q⁻¹ * T q) = 1
    have hi : ∀ i, T^[i] (q⁻¹ * T q) = T^[i + 1] q / T^[i] q := by
      intro i
      rw [iterate_map_mul, iterate_map_inv, Function.iterate_succ_apply, div_eq_mul_inv,
        mul_comm]
    simp_rw [hi]
    calc ∏ i ∈ Finset.range m, T^[i + 1] q / T^[i] q = T^[m] q / T^[0] q :=
          Finset.prod_range_div (fun i => T^[i] q) m
      _ = 1 := by rw [hTm, Function.iterate_zero_apply, div_self']
  have hker : Subgroup.closure (Set.range fun q => q⁻¹ * T q) ≤ ν.ker := by
    rw [Subgroup.closure_le]
    rintro _ ⟨q, rfl⟩
    exact hgen q
  have hνw : ν w = w ^ m := by
    change ∏ i ∈ Finset.range m, T^[i] w = w ^ m
    have hfix : ∀ i, T^[i] w = w := fun i => Function.iterate_fixed hTw i
    simp [hfix]
  have hwm : w ^ m = 1 := by
    rw [← hνw]
    exact hker hw
  obtain ⟨j, hj⟩ := h2 w
  have hcop : Nat.Coprime (2 ^ j) m := Nat.Coprime.pow_left j (Nat.coprime_two_left.2 hm)
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hj)
    (orderOf_dvd_of_pow_eq_one hwm))

@[expose] def restrictHom (β : MulAut S) {T : Subgroup S} (hβT : ∀ t ∈ T, β t ∈ T) : T →* T where
  toFun t := ⟨β t, hβT t t.2⟩
  map_one' := Subtype.ext (map_one β)
  map_mul' x y := Subtype.ext (map_mul β (x : S) (y : S))

theorem coe_iterate_restrictHom (β : MulAut S) {T : Subgroup S} (hβT : ∀ t ∈ T, β t ∈ T)
    (k : ℕ) (t : T) : (((restrictHom β hβT)^[k] t : T) : S) = (β ^ k) t := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ', MulAut.mul_apply, ← ih]
    rfl

theorem eq_one_of_mem_closure_commElem_of_isMulCommutative (hS : IsPGroup 2 S) (β : MulAut S)
    {m : ℕ} (hm : Odd m) (hβm : β ^ m = 1) {T : Subgroup S} [IsMulCommutative T]
    (hβT : ∀ t ∈ T, β t ∈ T) {w : S}
    (hw : w ∈ Subgroup.closure {x | ∃ t ∈ T, x = t⁻¹ * β t}) (hβw : β w = w) : w = 1 := by
  set f := restrictHom β hβT with hf
  have hset : {x | ∃ t ∈ T, x = t⁻¹ * β t} =
      T.subtype '' Set.range (fun q : T => q⁻¹ * f q) := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨_, ⟨⟨t, ht⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
      exact ⟨(q : S), q.2, rfl⟩
  rw [hset, ← MonoidHom.map_closure] at hw
  obtain ⟨w', hw', rfl⟩ := hw
  have hfix : f w' = w' := Subtype.ext hβw
  have key := eq_one_of_mem_closure_inv_mul_of_fixed f hm
    (fun q => Subtype.ext (by rw [coe_iterate_restrictHom, hβm, MulAut.one_apply]))
    (fun q => by
      obtain ⟨j, hj⟩ := hS (q : S)
      exact ⟨j, Subtype.ext (by simpa using hj)⟩) hw' hfix
  rw [key]
  rfl

theorem mem_closure_sq_of_apply_eq_self (β : MulAut S) {m : ℕ}
    (hm : Odd m) (hβm : β ^ m = 1) {R : Subgroup S} (hβR : ∀ r ∈ R, β r ∈ R)
    (hgen : Subgroup.closure {x | ∃ r ∈ R, x = r⁻¹ * β r} = R) {x : S} (hxR : x ∈ R)
    (hx : β x = x) : x ∈ Subgroup.closure {y | ∃ r ∈ R, y = r ^ 2} := by
  set f := restrictHom β hβR with hf
  set Ψ := BenderSuzuki.External.Higman.squaresSubgroup R with hΨdef
  have hΨ : Ψ ≤ Ψ.comap f := by
    rw [hΨdef, BenderSuzuki.External.Higman.squaresSubgroup, Subgroup.closure_le]
    rintro _ ⟨y, rfl⟩
    exact Subgroup.subset_closure ⟨f y, by rw [map_pow]⟩
  have hQ2 : ∀ q : R ⧸ Ψ, q ^ 2 = 1 := by
    intro q
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.subset_closure ⟨r, rfl⟩
  have hQcomm : IsMulCommutative (R ⧸ Ψ) := IsMulCommutative.of_comm fun a b =>
    Commute.of_orderOf_dvd_two (fun g => orderOf_dvd_of_pow_eq_one (hQ2 g)) a b
  let TQ : R ⧸ Ψ →* R ⧸ Ψ := QuotientGroup.map Ψ Ψ f hΨ
  have hTQ : ∀ (k : ℕ) (r : R), TQ^[k] (r : R ⧸ Ψ) = ((f^[k] r : R) : R ⧸ Ψ) := by
    intro k
    induction k with
    | zero => intro r; rfl
    | succ k ih =>
      intro r
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      rfl
  have hgenR : Subgroup.closure (Set.range fun r : R => r⁻¹ * f r) = ⊤ := by
    apply Subgroup.map_injective R.subtype_injective
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hset : R.subtype '' Set.range (fun r : R => r⁻¹ * f r) =
        {x | ∃ r ∈ R, x = r⁻¹ * β r} := by
      ext y
      constructor
      · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
        exact ⟨r, r.2, rfl⟩
      · rintro ⟨r, hr, rfl⟩
        exact ⟨_, ⟨⟨r, hr⟩, rfl⟩, rfl⟩
    rw [hset]
    exact hgen
  have hgenQ : Subgroup.closure (Set.range fun q : R ⧸ Ψ => q⁻¹ * TQ q) = ⊤ := by
    have h := congrArg (Subgroup.map (QuotientGroup.mk' Ψ)) hgenR
    rw [MonoidHom.map_closure,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Ψ)] at h
    rw [← h]
    congr 1
    ext q
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨_, ⟨r, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
      exact ⟨(r : R ⧸ Ψ), rfl⟩
  have hfixQ : TQ ((⟨x, hxR⟩ : R) : R ⧸ Ψ) = ((⟨x, hxR⟩ : R) : R ⧸ Ψ) := by
    change ((f ⟨x, hxR⟩ : R) : R ⧸ Ψ) = _
    congr 1
    exact Subtype.ext hx
  have key := eq_one_of_mem_closure_inv_mul_of_fixed TQ hm
    (fun q => by
      obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective q
      rw [hTQ]
      congr 1
      exact Subtype.ext (by rw [coe_iterate_restrictHom, hβm, MulAut.one_apply]))
    (fun q => ⟨1, by simpa using hQ2 q⟩) (hgenQ ▸ Subgroup.mem_top _) hfixQ
  rw [QuotientGroup.eq_one_iff] at key
  have hmem : x ∈ Ψ.map R.subtype := ⟨_, key, rfl⟩
  rw [hΨdef, BenderSuzuki.External.Higman.squaresSubgroup, MonoidHom.map_closure] at hmem
  refine Subgroup.closure_mono ?_ hmem
  rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
  exact ⟨y, y.2, by simp⟩

theorem dvd_natCard_of_dvd_index_stabilizer {G X : Type*} [Group G] [Finite G] [MulAction G X]
    [Finite X] {d : ℕ} (hd : ∀ x : X, d ∣ (MulAction.stabilizer G x).index) :
    d ∣ Nat.card X := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype X := Fintype.ofFinite X
  let _ : Fintype (Quotient (MulAction.orbitRel G X)) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, MulAction.card_eq_sum_card_group_div_card_stabilizer G X]
  refine Finset.dvd_sum fun ω _ => ?_
  have h := (MulAction.stabilizer G ω.out).card_mul_index
  rw [Nat.card_eq_fintype_card (α := G), Nat.card_eq_fintype_card] at h
  rw [← h, Nat.mul_div_cancel_left _ Fintype.card_pos]
  exact hd ω.out

end CFSG.GroupTheory.SuzukiTwoGroup
