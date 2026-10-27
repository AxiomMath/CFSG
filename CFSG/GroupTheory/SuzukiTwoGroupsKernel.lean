module

public import CFSG.GroupTheory.SuzukiTwoGroupsBasic
public import CFSG.GroupTheory.SuzukiTwoGroupsCoprime
public import CFSG.GroupTheory.SuzukiTwoGroupsQuadratic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core

public section

namespace CFSG.GroupTheory.SuzukiTwoGroup

open Subgroup
open scoped commutatorElement

variable {S : Type*} [Group S]

section Stable

variable {A : Subgroup (MulAut S)}

theorem isStable_closure {X : Set S} (hX : ∀ a ∈ A, ∀ x ∈ X, a x ∈ X) :
    IsStable A (closure X) := by
  intro a ha t ht
  have hle : closure X ≤ (closure X).comap a.toMonoidHom :=
    (closure_le _).2 fun x hx => subset_closure (hX a ha x hx)
  exact hle ht

theorem isStable_closure_commElem (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {β : MulAut S}
    (hβA : β ∈ A) {R : Subgroup S} (hR : IsStable A R) :
    IsStable A (closure {x | ∃ r ∈ R, x = r⁻¹ * β r}) := by
  refine isStable_closure fun a ha x hx => ?_
  obtain ⟨r, hr, rfl⟩ := hx
  refine ⟨a r, hR a ha r hr, ?_⟩
  rw [map_mul, map_inv, ← MulAut.mul_apply, hAcomm a ha β hβA, MulAut.mul_apply]

theorem isStable_closure_sq {R : Subgroup S} (hR : IsStable A R) :
    IsStable A (closure {y | ∃ r ∈ R, y = r ^ 2}) := by
  refine isStable_closure fun a ha y hy => ?_
  obtain ⟨r, hr, rfl⟩ := hy
  exact ⟨a r, hR a ha r hr, map_pow a r 2⟩

end Stable

theorem mem_zpowers_of_orderOf_eq {G : Type*} [Group G] [Finite G] [IsCyclic G] {g h : G}
    (hgh : orderOf g = orderOf h) : g ∈ zpowers h := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  set p := orderOf h with hp
  have hp0 : 0 < p := orderOf_pos h
  have hsub : (zpowers h : Set G).toFinset ⊆ Finset.univ.filter (fun a => a ^ p = 1) := by
    intro a ha
    rw [Set.mem_toFinset] at ha
    obtain ⟨k, rfl⟩ := ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hp, pow_orderOf_eq_one,
      one_zpow]
  have hcard : (Finset.univ.filter (fun a : G => a ^ p = 1)).card ≤
      (zpowers h : Set G).toFinset.card := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    change _ ≤ Nat.card (zpowers h)
    rw [Nat.card_zpowers]
    exact IsCyclic.card_pow_eq_one_le hp0
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hg : g ∈ Finset.univ.filter (fun a : G => a ^ p = 1) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hgh, pow_orderOf_eq_one]
  rw [← heq, Set.mem_toFinset] at hg
  exact hg

theorem closure_sq_ne_self [Finite S] (hS : IsPGroup 2 S) {R : Subgroup S} (hR : R ≠ ⊥) :
    closure {y | ∃ r ∈ R, y = r ^ 2} ≠ R := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 R) := ⟨hS.to_subgroup R⟩
  have : Nontrivial R := (nontrivial_iff_ne_bot R).2 hR
  have htop : closure {y : R | ∃ r : R, y = r ^ 2} = ⊤ := by
    apply map_injective R.subtype_injective
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, range_subtype]
    conv_rhs => rw [← h]
    congr 1
    ext y
    constructor
    · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
      exact ⟨r, r.2, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨_, ⟨⟨r, hr⟩, rfl⟩, rfl⟩
  have hle : (⊤ : Subgroup R) ≤ frattini R := by
    rw [← htop, closure_le]
    rintro _ ⟨r, rfl⟩
    exact CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) r
  obtain ⟨M, hM, -⟩ := (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup R)).resolve_left
    bot_ne_top
  exact hM.1 (top_le_iff.1 (hle.trans (frattini_le_coatom hM)))

theorem pow_dvd_two_pow_sub_one_of_dvd {n k p c : ℕ} (hp : p.Prime) (hk1 : 1 ≤ k)
    (hk : k ≤ 2 * n) (hpn : p ∣ 2 ^ n - 1) (hnk : 2 ^ n - 1 ∣ 2 ^ k - 1)
    (hck : p ^ c ∣ 2 ^ k - 1) : p ^ c ∣ 2 ^ n - 1 := by
  have hn1 : 1 ≤ n := by omega
  have hgcd := Nat.pow_sub_one_gcd_pow_sub_one 2 n k
  rw [Nat.gcd_eq_left hnk] at hgcd
  have hnk' : n.gcd k = n := by
    have h2 : 2 ^ n = 2 ^ n.gcd k := by
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have h1' : 1 ≤ 2 ^ n.gcd k := Nat.one_le_two_pow
      omega
    exact (Nat.pow_right_injective (le_refl 2) h2).symm
  have hdvd : n ∣ k := hnk' ▸ Nat.gcd_dvd_right n k
  obtain ⟨t, rfl⟩ := hdvd
  have ht : t = 1 ∨ t = 2 := by
    have ht1 : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with rfl | h
      · omega
      · exact h
    have ht2 : t ≤ 2 := by
      by_contra h
      push Not at h
      have : n * 3 ≤ n * t := Nat.mul_le_mul_left n h
      omega
    omega
  rcases ht with rfl | rfl
  · simpa using hck
  · have hsplit : 2 ^ (n * 2) - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
      rw [pow_mul]
      obtain ⟨y, hy⟩ : ∃ y, 2 ^ n = y + 1 :=
        ⟨2 ^ n - 1, by have := Nat.one_le_two_pow (n := n); omega⟩
      rw [hy, Nat.add_sub_cancel, show (y + 1) ^ 2 = y * (y + 1 + 1) + 1 by ring,
        Nat.add_sub_cancel]
    rw [hsplit] at hck
    have hcop : Nat.Coprime (p ^ c) (2 ^ n + 1) := by
      refine Nat.Coprime.pow_left c ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hp1 => ?_)
      have h2 : p ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub hp1 hpn
      have h3 : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by
        have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        omega
      rw [h3] at h2
      have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2
      rw [hp2] at hpn
      have hodd : Odd (2 ^ n - 1) := by
        have h1 : 2 ≤ 2 ^ n := by
          calc 2 = 2 ^ 1 := (pow_one 2).symm
            _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
        rw [Nat.odd_iff]
        have : 2 ^ n % 2 = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega))
        omega
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hpn)
    exact hcop.dvd_of_dvd_mul_right hck

theorem odd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n - 1) := by
  obtain ⟨t, ht⟩ : ∃ t, 2 ^ n = 2 * t ∧ 1 ≤ t :=
    ⟨2 ^ (n - 1), by rw [← pow_succ', Nat.sub_add_cancel hn], Nat.one_le_two_pow⟩
  exact ⟨t - 1, by omega⟩

section Kernel

variable [Finite S] (hS : IsPGroup 2 S) {A : Subgroup (MulAut S)}
  (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
  (htrans : ∀ x y : S, orderOf x = 2 → orderOf y = 2 → ∃ a ∈ A, a x = y)

include hS hAcomm htrans in
theorem exists_subgroup_sq_le_omega₁ {x₀ : S} (hx₀ : orderOf x₀ = 2) {β : MulAut S}
    (hβA : β ∈ A) (hβI : ∀ x : S, orderOf x = 2 → β x = x) {m : ℕ} (hm : Odd m)
    (hβm : β ^ m = 1) (hβ1 : β ≠ 1) :
    ∃ R : Subgroup S, IsStable A R ∧ omega₁ S (p := 2) ≤ R ∧
      (∀ x ∈ R, x ^ 2 ∈ omega₁ S (p := 2)) ∧ (∀ x ∈ R, β x = x → x ∈ omega₁ S (p := 2)) ∧
      ∃ r ∈ R, r ∉ omega₁ S (p := 2) := by
  classical
  set E := omega₁ S (p := 2) with hEdef
  have hEmem : ∀ x, x ∈ E ↔ x ^ 2 = 1 := fun x => mem_omega₁_iff hS htrans
  have hex : ∃ R : Subgroup S, IsStable A R ∧ ∃ r ∈ R, β r ≠ r := by
    refine ⟨⊤, fun _ _ _ _ => mem_top _, ?_⟩
    by_contra h
    push Not at h
    exact hβ1 (MulEquiv.ext fun r => h r (mem_top r))
  obtain ⟨R, ⟨hRst, r₀, hr₀, hβr₀⟩, hRmin⟩ := WellFounded.has_min
    (measure fun R : Subgroup S => Nat.card R).wf {R | IsStable A R ∧ ∃ r ∈ R, β r ≠ r} hex
  have hmin : ∀ R' : Subgroup S, R' < R → IsStable A R' → ∀ r ∈ R', β r = r := by
    intro R' hlt hst r hr
    by_contra hne
    exact hRmin R' ⟨hst, r, hr, hne⟩ (Subgroup.card_lt_of_lt hlt)
  have hβR : ∀ r ∈ R, β r ∈ R := hRst β hβA
  have hRne : R ≠ ⊥ := by
    rintro rfl
    rw [mem_bot] at hr₀
    rw [hr₀, map_one] at hβr₀
    exact hβr₀ rfl
  have hER : E ≤ R := omega₁_le_of_isStable hS htrans hRne hRst
  set K := closure {x | ∃ r ∈ R, x = r⁻¹ * β r} with hKdef
  have hKR : K ≤ R := (closure_le _).2 (by
    rintro _ ⟨r, hr, rfl⟩
    exact R.mul_mem (R.inv_mem hr) (hβR r hr))
  have hKst : IsStable A K := isStable_closure_commElem hAcomm hβA hRst
  have hβK : ∃ k ∈ K, β k ≠ k := by
    by_contra h
    push Not at h
    exact hβr₀ (apply_eq_self_of_apply_commElem_eq hS β hm hβm
      (h _ (subset_closure ⟨r₀, hr₀, rfl⟩)))
  have hKeq : K = R := by
    by_contra hne
    obtain ⟨k, hk, hβk⟩ := hβK
    exact hβk (hmin K (lt_of_le_of_ne hKR hne) hKst k hk)
  have hRnab : ¬ IsMulCommutative R := by
    intro hRc
    have hKne : K ≠ ⊥ := by
      obtain ⟨k, hk, hβk⟩ := hβK
      rintro h
      rw [h, mem_bot] at hk
      rw [hk, map_one] at hβk
      exact hβk rfl
    have hx₀K : x₀ ∈ K := omega₁_le_of_isStable hS htrans hKne hKst
      ((hEmem x₀).2 (orderOf_eq_two_iff_sq_eq_one.1 hx₀).1)
    exact (orderOf_eq_two_iff_sq_eq_one.1 hx₀).2
      (eq_one_of_mem_closure_commElem_of_isMulCommutative hS β hm hβm hβR hx₀K (hβI x₀ hx₀))
  set Φ := closure {y | ∃ r ∈ R, y = r ^ 2} with hΦdef
  have hΦR : Φ ≤ R := (closure_le _).2 (by
    rintro _ ⟨r, hr, rfl⟩
    exact R.pow_mem hr 2)
  have hβΦ : ∀ f ∈ Φ, β f = f :=
    hmin Φ (lt_of_le_of_ne hΦR (closure_sq_ne_self hS hRne)) (isStable_closure_sq hRst)
  have hsqΦ : ∀ x ∈ R, x ^ 2 ∈ Φ := fun x hx => subset_closure ⟨x, hx, rfl⟩
  have hΦconj : ∀ r ∈ R, ∀ f ∈ Φ, r * f * r⁻¹ ∈ Φ := by
    intro r hr f hf
    have hle : Φ ≤ Φ.comap (MulAut.conj r).toMonoidHom := (closure_le _).2 (by
      rintro _ ⟨s, hs, rfl⟩
      refine subset_closure ⟨r * s * r⁻¹, R.mul_mem (R.mul_mem hr hs) (R.inv_mem hr), ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, pow_two]
      group)
    exact hle hf
  have hΦZ : ∀ f ∈ Φ, ∀ y ∈ R, y * f = f * y := by
    have hle : R ≤ centralizer (Φ : Set S) := by
      rw [← hKeq]
      refine (closure_le _).2 ?_
      rintro _ ⟨r, hr, rfl⟩
      rw [SetLike.mem_coe, mem_centralizer_iff]
      intro f hf
      have h1 : β (r * f * r⁻¹) = r * f * r⁻¹ := hβΦ _ (hΦconj r hr f hf)
      rw [map_mul, map_mul, map_inv, hβΦ f hf] at h1
      calc f * (r⁻¹ * β r) = r⁻¹ * (r * f * r⁻¹) * β r := by group
        _ = r⁻¹ * (β r * f * (β r)⁻¹) * β r := by rw [h1]
        _ = r⁻¹ * β r * f := by group
    intro f hf y hy
    exact (mem_centralizer_iff.1 (hle hy) f hf).symm
  have hCΦ : ∀ x ∈ R, β x = x → x ∈ Φ := fun x hx hβx =>
    mem_closure_sq_of_apply_eq_self β hm hβm hβR hKeq hx hβx
  have hcommΦ : ∀ x ∈ R, ∀ y ∈ R, ⁅x, y⁆ ∈ Φ := by
    intro x hx y hy
    have h : ⁅x, y⁆ = x ^ 2 * (x⁻¹ * y) ^ 2 * y⁻¹ ^ 2 := by
      rw [commutatorElement_def]
      simp only [pow_two]
      group
    rw [h]
    exact Φ.mul_mem (Φ.mul_mem (hsqΦ x hx) (hsqΦ _ (R.mul_mem (R.inv_mem hx) hy)))
      (hsqΦ _ (R.inv_mem hy))
  have hcommE : ∀ x ∈ R, ∀ y ∈ R, ⁅x, y⁆ ∈ E := by
    intro x hx y hy
    rw [hEmem]
    have hc : Commute x ⁅x, y⁆ := hΦZ _ (hcommΦ x hx y hy) x hx
    have h1 : ⁅x * x, y⁆ = ⁅x, y⁆ * ⁅x, y⁆ := commutatorElement_mul_left_of_commute hc
    have h2 : ⁅x * x, y⁆ = 1 := by
      rw [← pow_two]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hΦZ _ (hsqΦ x hx) y hy).symm
    rw [pow_two, ← h1, h2]
  have hsqE : ∀ x ∈ R, x ^ 2 ∈ E := by
    intro x hx
    rw [← hKeq] at hx
    refine closure_induction (p := fun x _ => x ^ 2 ∈ E) (fun c hc => ?_)
      (by rw [one_pow]; exact one_mem _) (fun a b ha hb iha ihb => ?_)
      (fun a _ iha => by rw [inv_pow]; exact E.inv_mem iha) hx
    · obtain ⟨r, hr, rfl⟩ := hc
      have hcR : r⁻¹ * β r ∈ R := R.mul_mem (R.inv_mem hr) (hβR r hr)
      have hβsq : (β r) ^ 2 = r ^ 2 := by rw [← map_pow, hβΦ _ (hsqΦ r hr)]
      have hdef : r * (r⁻¹ * β r) = β r := by group
      have hcomm : Commute r ⁅r⁻¹ * β r, r⁆ := hΦZ _ (hcommΦ _ hcR r hr) r hr
      have h1 := mul_sq_of_commute hcomm
      rw [hdef, hβsq] at h1
      have hd : Commute ⁅r⁻¹ * β r, r⁆ (r ^ 2) :=
        (hΦZ _ (hcommΦ _ hcR r hr) (r ^ 2) (R.pow_mem hr 2)).symm
      have h2 : r ^ 2 * (⁅r⁻¹ * β r, r⁆ * (r⁻¹ * β r) ^ 2) = r ^ 2 * 1 := by
        rw [mul_one, ← mul_assoc, ← hd.eq, ← h1]
      rw [eq_inv_of_mul_eq_one_right (mul_left_cancel h2)]
      exact E.inv_mem (hcommE _ hcR r hr)
    · have haR : a ∈ R := hKR ha
      have hbR : b ∈ R := hKR hb
      have hcomm : Commute a ⁅b, a⁆ := hΦZ _ (hcommΦ b hbR a haR) a haR
      rw [mul_sq_of_commute hcomm]
      exact E.mul_mem (E.mul_mem (hcommE b hbR a haR) iha) ihb
  have hΦE : Φ ≤ E := (closure_le _).2 (by
    rintro _ ⟨r, hr, rfl⟩
    exact hsqE r hr)
  refine ⟨R, hRst, hER, hsqE, fun x hx hβx => hΦE (hCΦ x hx hβx), ?_⟩
  by_contra h
  push Not at h
  apply hRnab
  refine IsMulCommutative.of_comm fun a b => Subtype.ext ?_
  exact Subgroup.mem_center_iff.1 (omega₁_le_center hS htrans (h b b.2)) a

omit [Finite S] in
include htrans in
theorem index_stabilizer_eq_card_involutions {y : S} (hy : orderOf y = 2) :
    (MulAction.stabilizer A y).index = Nat.card {z : S // orderOf z = 2} := by
  rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq]
  have horb : MulAction.orbit A y = {z : S | orderOf z = 2} := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      change orderOf ((a : MulAut S) y) = 2
      rw [MulEquiv.orderOf_eq]
      exact hy
    · intro hz
      obtain ⟨a, ha, rfl⟩ := htrans y z hy hz
      exact ⟨⟨a, ha⟩, rfl⟩
  rw [horb]
  rfl

include hS htrans in
theorem card_involutions_add_one :
    Nat.card {x : S // orderOf x = 2} + 1 = Nat.card (omega₁ S (p := 2)) := by
  classical
  have hset : ((omega₁ S (p := 2) : Subgroup S) : Set S) = insert 1 {x : S | orderOf x = 2} := by
    ext x
    rw [SetLike.mem_coe, Set.mem_insert_iff, mem_omega₁_iff hS htrans]
    change x ^ 2 = 1 ↔ x = 1 ∨ orderOf x = 2
    rw [orderOf_eq_two_iff_sq_eq_one]
    constructor
    · intro h
      by_cases hx : x = 1
      · exact Or.inl hx
      · exact Or.inr ⟨h, hx⟩
    · rintro (rfl | ⟨h, -⟩)
      · exact one_pow 2
      · exact h
  have h1 : Nat.card (omega₁ S (p := 2)) =
      ((omega₁ S (p := 2) : Subgroup S) : Set S).ncard := Nat.card_coe_set_eq _
  rw [h1, hset, Set.ncard_insert_of_notMem (by simp) (Set.toFinite _)]
  exact congrArg (· + 1) (Nat.card_coe_set_eq {x : S | orderOf x = 2})

include hS htrans in
theorem false_of_apply_eq_self_of_pow_eq_one [IsCyclic A] {x₀ : S} (hx₀ : orderOf x₀ = 2)
    {β : MulAut S} (hβA : β ∈ A) (hβI : ∀ x : S, orderOf x = 2 → β x = x) {p : ℕ}
    (hp : p.Prime) (hβp : β ^ p = 1) (hβ1 : β ≠ 1)
    (hpI : p ∣ Nat.card {x : S // orderOf x = 2}) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  set E := omega₁ S (p := 2) with hEdef
  have hEmem : ∀ x, x ∈ E ↔ x ^ 2 = 1 := fun x => mem_omega₁_iff hS htrans
  have hAc : IsMulCommutative A := IsCyclic.isMulCommutative
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) ⟨b, hb⟩)
  have hIE := card_involutions_add_one hS htrans
  rw [← hEdef] at hIE
  obtain ⟨n, hn⟩ : ∃ n, Nat.card E = 2 ^ n := (IsPGroup.iff_card).1 (hS.to_subgroup E)
  have hx₀E : x₀ ∈ E := (hEmem x₀).2 (orderOf_eq_two_iff_sq_eq_one.1 hx₀).1
  have hn1 : 1 ≤ n := by
    by_contra h
    push Not at h
    have hn0 : n = 0 := by omega
    rw [hn0, pow_zero] at hn
    have : (⟨x₀, hx₀E⟩ : E) = 1 := Subsingleton.elim (h := Nat.card_eq_one_iff_unique.1 hn |>.1) _ _
    exact (orderOf_eq_two_iff_sq_eq_one.1 hx₀).2 (congrArg Subtype.val this)
  have hI : Nat.card {x : S // orderOf x = 2} = 2 ^ n - 1 := by omega
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [hI] at hpI
    exact (Nat.not_even_iff_odd.2 (odd_two_pow_sub_one hn1)) (even_iff_two_dvd.2 hpI)
  have hm : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨R, hRst, hER, hsqE, hCE, r₁, hr₁R, hr₁E⟩ :=
    exists_subgroup_sq_le_omega₁ hS hAcomm htrans hx₀ hβA hβI hm hβp hβ1
  have hEc : E ≤ center S := omega₁_le_center hS htrans
  have hEn : E.Normal := ⟨fun x hx g => by
    rw [(Subgroup.mem_center_iff.1 (hEc hx) g), mul_inv_cancel_right]
    exact hx⟩
  set E' := E.subgroupOf R with hE'def
  have hE'card : Nat.card E' = Nat.card E := Nat.card_congr (subgroupOfEquivOfLe hER).toEquiv
  have hbound := card_quotient_le_sq_of_sq_eq_one_imp_mem (G := R) E'
    (fun x hx => Subgroup.mem_center_iff.2 fun g => Subtype.ext
      (Subgroup.mem_center_iff.1 (hEc (Subgroup.mem_subgroupOf.1 hx)) g))
    (fun e he => Subtype.ext ((hEmem _).1 (Subgroup.mem_subgroupOf.1 he)))
    (fun x => Subgroup.mem_subgroupOf.2 (hsqE x x.2))
    (fun x hx => Subgroup.mem_subgroupOf.2 ((hEmem x).2 (congrArg Subtype.val hx)))
  obtain ⟨k, hk⟩ : ∃ k, Nat.card (R ⧸ E') = 2 ^ k :=
    (IsPGroup.iff_card).1 ((hS.to_subgroup R).to_quotient E')
  have hRcard : Nat.card R = 2 ^ k * 2 ^ n := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup E', hk, hE'card, hn]
  have hk2n : k ≤ 2 * n := by
    rw [hk, hE'card, hn, ← pow_mul, mul_comm] at hbound
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hbound
  have hk1 : 1 ≤ k := by
    by_contra h
    push Not at h
    have hk0 : k = 0 := by omega
    rw [hk0, pow_zero, one_mul, ← hn] at hRcard
    have := Subgroup.eq_of_le_of_card_ge hER hRcard.le
    exact hr₁E (this ▸ hr₁R)
  let X : SubMulAction A S :=
    { carrier := {x | x ∈ R ∧ x ∉ E}
      smul_mem' := fun a x hx => by
        refine ⟨hRst a a.2 x hx.1, fun h => hx.2 ((hEmem x).2 ?_)⟩
        have h' := (hEmem _).1 h
        change ((a : MulAut S) x) ^ 2 = 1 at h'
        rwa [← map_pow, map_eq_one_iff _ (a : MulAut S).injective] at h' }
  have hXcard : Nat.card X = 2 ^ n * (2 ^ k - 1) := by
    have h1 : Nat.card X = ((R : Set S) \ (E : Set S)).ncard := Nat.card_coe_set_eq _
    rw [h1, Set.ncard_sdiff hER (Set.toFinite _), ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    change Nat.card R - Nat.card E = _
    rw [hRcard, hn, Nat.mul_sub, mul_one, mul_comm]
  have hinv : ∀ x ∈ R, x ∉ E → orderOf (x ^ 2) = 2 := fun x hx hxE =>
    orderOf_eq_two_iff_sq_eq_one.2 ⟨(hEmem _).1 (hsqE x hx), fun h => hxE ((hEmem x).2 h)⟩
  have hdiv1 : 2 ^ n - 1 ∣ Nat.card X := by
    rw [← hI]
    refine dvd_natCard_of_dvd_index_stabilizer (G := A) fun ⟨x, hxR, hxE⟩ => ?_
    rw [SubMulAction.stabilizer_of_subMul]
    have hle : MulAction.stabilizer A x ≤ MulAction.stabilizer A (x ^ 2) := fun a ha => by
      rw [MulAction.mem_stabilizer_iff] at ha ⊢
      rw [smul_pow', ha]
    rw [← Subgroup.relIndex_mul_index hle,
      index_stabilizer_eq_card_involutions htrans (hinv x hxR hxE)]
    exact dvd_mul_left _ _
  set c := (Nat.card A).factorization p with hc
  have hβo : orderOf (⟨β, hβA⟩ : A) = p := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hβp hβ1
  have hdiv2 : p ^ c ∣ Nat.card X := by
    refine dvd_natCard_of_dvd_index_stabilizer (G := A) fun ⟨x, hxR, hxE⟩ => ?_
    rw [SubMulAction.stabilizer_of_subMul]
    have hnot : ¬ p ∣ Nat.card (MulAction.stabilizer A x) := by
      intro hpd
      obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' (G := MulAction.stabilizer A x) p hpd
      have hho : orderOf (h : A) = p := by rw [Subgroup.orderOf_coe]; exact hh
      have hmem : (⟨β, hβA⟩ : A) ∈ zpowers (h : A) := mem_zpowers_of_orderOf_eq (hβo.trans hho.symm)
      have hβs : (⟨β, hβA⟩ : A) ∈ MulAction.stabilizer A x := (zpowers_le.2 h.2) hmem
      exact hxE (hCE x hxR (MulAction.mem_stabilizer_iff.1 hβs))
    have hcm := (MulAction.stabilizer A x).card_mul_index
    have hpc : p ^ c ∣ Nat.card A := Nat.ordProj_dvd _ _
    rw [← hcm] at hpc
    exact (Nat.Coprime.pow_left c ((Nat.Prime.coprime_iff_not_dvd hp).2 hnot)).dvd_of_dvd_mul_left
      hpc
  have hnot : ¬ p ^ c ∣ 2 ^ n - 1 := by
    intro h
    rw [← hI] at h
    have hβs : (⟨β, hβA⟩ : A) ∈ MulAction.stabilizer A x₀ :=
      MulAction.mem_stabilizer_iff.2 (hβI x₀ hx₀)
    have hpstab : p ∣ Nat.card (MulAction.stabilizer A x₀) := by
      have := Subgroup.orderOf_dvd_natCard (MulAction.stabilizer A x₀) hβs
      rwa [hβo] at this
    have hcm := (MulAction.stabilizer A x₀).card_mul_index
    rw [index_stabilizer_eq_card_involutions htrans hx₀] at hcm
    have hdvd : p ^ (c + 1) ∣ Nat.card A := by
      rw [← hcm, pow_succ']
      exact Nat.mul_dvd_mul hpstab h
    exact Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' hp hdvd
  rw [hXcard] at hdiv1 hdiv2
  have hcop1 : Nat.Coprime (2 ^ n - 1) (2 ^ n) := by
    have h1 : 2 ^ n = (2 ^ n - 1) + 1 := by have := Nat.one_le_two_pow (n := n); omega
    conv_rhs => rw [h1]
    exact (Nat.coprime_self_add_right).2 (Nat.coprime_one_right _)
  have hcop2 : Nat.Coprime (p ^ c) (2 ^ n) :=
    Nat.Coprime.pow c n ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  exact hnot (pow_dvd_two_pow_sub_one_of_dvd hp hk1 hk2n (hI ▸ hpI)
    (hcop1.dvd_of_dvd_mul_left hdiv1) (hcop2.dvd_of_dvd_mul_left hdiv2))

end Kernel

end CFSG.GroupTheory.SuzukiTwoGroup
