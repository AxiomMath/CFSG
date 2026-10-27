module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG

open Subgroup

variable {X : Type*} [Group X]

theorem list_prod_zpow_eq_zpow_sum {G : Type*} [Group G] (y : G) (m : ℤ) (k : ℕ) :
    ((List.range k).map fun i => y ^ (m ^ i)).prod =
      y ^ ((List.range k).map fun i => m ^ i).sum := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih, List.map_append,
      List.sum_append, zpow_add]
    simp

theorem pow_mulAut_conj (y : X) (τ : MulAut X) (k : ℕ) :
    τ ^ k * MulAut.conj y = MulAut.conj ((τ ^ k) y) * τ ^ k := by
  have hmul : ∀ z : X, τ * MulAut.conj z = MulAut.conj (τ z) * τ := by
    intro z
    ext w
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    calc
      (τ * τ ^ k) * MulAut.conj y = τ * (τ ^ k * MulAut.conj y) := by group
      _ = τ * (MulAut.conj ((τ ^ k) y) * τ ^ k) := by rw [ih]
      _ = (τ * MulAut.conj ((τ ^ k) y)) * τ ^ k := by group
      _ = (MulAut.conj (τ ((τ ^ k) y)) * τ) * τ ^ k := by rw [hmul]
      _ = MulAut.conj ((τ * τ ^ k) y) * (τ * τ ^ k) := by
            rw [← mul_assoc, MulAut.mul_apply]

theorem conj_mul_pow_eq_conj_prod_mul_pow (y : X) (τ : MulAut X) (k : ℕ) :
    (MulAut.conj y * τ) ^ k =
      MulAut.conj ((List.range k).map fun i => (τ ^ i) y).prod * τ ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, List.range_succ, List.map_append, List.prod_append,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, pow_succ]
    calc
      (MulAut.conj ((List.range k).map fun i => (τ ^ i) y).prod * τ ^ k) *
          (MulAut.conj y * τ)
          = MulAut.conj ((List.range k).map fun i => (τ ^ i) y).prod *
              ((τ ^ k * MulAut.conj y) * τ) := by group
      _ = MulAut.conj ((List.range k).map fun i => (τ ^ i) y).prod *
              ((MulAut.conj ((τ ^ k) y) * τ ^ k) * τ) := by rw [pow_mulAut_conj]
      _ = (MulAut.conj ((List.range k).map fun i => (τ ^ i) y).prod *
              MulAut.conj ((τ ^ k) y)) * (τ ^ k * τ) := by group
      _ = MulAut.conj (((List.range k).map fun i => (τ ^ i) y).prod * (τ ^ k) y) *
              (τ ^ k * τ) := by rw [← map_mul]
      _ = MulAut.conj (((List.range k).map fun i => (τ ^ i) y).prod * (τ ^ k) y) *
              τ ^ (k + 1) := by rw [pow_succ]

theorem pow_apply_eq_zpow_of_apply_eq_zpow {P : Subgroup X} {τ : MulAut X} {m : ℤ}
    (hm : ∀ x ∈ P, τ x = x ^ m) :
    ∀ (i : ℕ) (x : X), x ∈ P → (τ ^ i) x = x ^ (m ^ i : ℤ) := by
  intro i
  induction i with
  | zero => intro x hx; simp
  | succ i ih =>
    intro x hx
    rw [pow_succ', MulAut.mul_apply, ih x hx, hm _ (Subgroup.zpow_mem (K := P) hx _),
      ← zpow_mul, pow_succ]

theorem prod_range_apply_eq_zpow_sum {P : Subgroup X} {τ : MulAut X} {m : ℤ} {y : X}
    (hm : ∀ x ∈ P, τ x = x ^ m) (hy : y ∈ P) (k : ℕ) :
    ((List.range k).map fun i => (τ ^ i) y).prod =
      y ^ ((List.range k).map fun i => m ^ i).sum := by
  rw [show ((List.range k).map fun i => (τ ^ i) y) =
      ((List.range k).map fun i => y ^ (m ^ i : ℤ)) from
    List.map_congr_left (fun i _ => pow_apply_eq_zpow_of_apply_eq_zpow hm i y hy)]
  exact list_prod_zpow_eq_zpow_sum y m k

theorem exists_int_eq_one_add_mul_of_mem_pgroup {p : ℕ} [Fact p.Prime]
    {P : Subgroup X} (hP : IsPGroup p P) {τ : MulAut X}
    (hτ : τ ^ p = 1) {m : ℤ} (hm : ∀ x ∈ P, τ x = x ^ m)
    {g : X} (hg : g ∈ P) (hg1 : g ≠ 1) :
    ∃ t : ℤ, m = 1 + p * t := by
  classical
  have hτpow := pow_apply_eq_zpow_of_apply_eq_zpow hm
  obtain ⟨e, he⟩ := hP.exists_orderOf_eq_pow ⟨g, hg⟩
  have horder : orderOf g = p ^ e := by simpa using he
  have he1 : 1 ≤ e := by
    by_contra h
    have he0 : e = 0 := by omega
    have hg1' : g = 1 := by
      rw [← orderOf_eq_one_iff, horder, he0, pow_zero]
    exact hg1 hg1'
  have hgdvd : (orderOf g : ℤ) ∣ m ^ p - 1 := by
    have hco : g ^ (m ^ p) = g := by
      rw [← hτpow p g hg, hτ, MulAut.one_apply]
    rwa [orderOf_dvd_sub_iff_zpow_eq_zpow, zpow_one]
  have hpdvd : (p : ℤ) ∣ (orderOf g : ℤ) := by
    rw [horder]
    simpa using pow_dvd_pow (p : ℤ) he1
  have hmp : (p : ℤ) ∣ m ^ p - 1 := hpdvd.trans hgdvd
  have hm1mod : (m : ZMod p) = 1 := by
    have hcast : ((m ^ p - 1 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hmp
    push_cast at hcast
    rw [ZMod.pow_card] at hcast
    exact sub_eq_zero.mp hcast
  have hm_sub : (p : ℤ) ∣ m - 1 := by
    have hcast : ((m - 1 : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [hm1mod, sub_self]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcast
  obtain ⟨t, ht⟩ := hm_sub
  exact ⟨t, by linarith⟩

theorem pow_eq_one_of_orderOf_eq_prime_pow_of_sq_dvd_sub {p : ℕ} [Fact p.Prime]
    {y : X} {S : ℤ} (horder : ∃ e : ℕ, orderOf y = p ^ e)
    (hord : (orderOf y : ℤ) ∣ S) (hsq : (p : ℤ) ^ 2 ∣ S - p) : y ^ p = 1 := by
  obtain ⟨e, he⟩ := horder
  have he2 : e ≤ 1 := by
    by_contra hgt
    have he2' : 2 ≤ e := by omega
    have hdiv : (p : ℤ) ^ 2 ∣ (orderOf y : ℤ) := by
      rw [he]
      exact pow_dvd_pow (p : ℤ) he2'
    have hS : (p : ℤ) ^ 2 ∣ S := hdiv.trans hord
    have hp2dvd : (p : ℤ) ^ 2 ∣ (p : ℤ) := by
      simpa using dvd_sub hS hsq
    have hp2dvdNat : p ^ 2 ∣ p := by exact_mod_cast hp2dvd
    have hle := Nat.le_of_dvd (Fact.out : p.Prime).pos hp2dvdNat
    have h2 := (Fact.out : p.Prime).two_le
    nlinarith
  have he01 : e = 0 ∨ e = 1 := by omega
  rcases he01 with rfl | rfl
  · have hy1 : y = 1 := by
      rw [← orderOf_eq_one_iff]
      simpa using he
    rw [hy1, one_pow]
  · exact orderOf_dvd_iff_pow_eq_one.mp (by rw [he]; simp)

theorem pow_eq_one_of_prod_range_eq_one [Finite X] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {P : Subgroup X} (hP : IsPGroup p P) (hPc : IsCyclic P) {τ : MulAut X}
    (hτP : ∀ s ∈ P, τ s ∈ P) (hτ : τ ^ p = 1) {y : X} (hy : y ∈ P)
    (hN : ((List.range p).map fun i => (τ ^ i) y).prod = 1) : y ^ p = 1 := by
  classical
  let τP : P →* P :=
    { toFun := fun x => ⟨τ x, hτP x x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro x z; ext; simp }
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic τP
  have hτapply : ∀ z ∈ P, τ z = z ^ m := by
    intro z hz
    simpa [τP] using congrArg Subtype.val (hm ⟨z, hz⟩)
  have hS : y ^ ((List.range p).map fun i => m ^ i).sum = 1 := by
    rw [← prod_range_apply_eq_zpow_sum hτapply hy, hN]
  have hord : (orderOf y : ℤ) ∣ ((List.range p).map fun i => m ^ i).sum :=
    orderOf_dvd_iff_zpow_eq_one.mpr hS
  obtain ⟨e, he⟩ := hP.exists_orderOf_eq_pow ⟨y, hy⟩
  have horder : orderOf y = p ^ e := by simpa using he
  obtain ⟨g, hg⟩ := hPc.exists_generator
  by_cases hg1 : g = 1
  · have hy1 : y = 1 := by
      have hmem := hg ⟨y, hy⟩
      rw [hg1, Subgroup.zpowers_one_eq_bot] at hmem
      simpa using hmem
    rw [hy1, one_pow]
  · have hg1X : (g : X) ≠ 1 := by
      intro h
      exact hg1 (Subtype.ext h)
    obtain ⟨t, ht⟩ :=
      exists_int_eq_one_add_mul_of_mem_pgroup hP hτ hτapply g.2 hg1X
    have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
    have hsq := odd_sq_dvd_geom_sum₂_sub (R := ℤ) (a := 1) (b := t) hodd
    simp only [one_pow, mul_one] at hsq
    have hsq' : (p : ℤ) ^ 2 ∣ ((List.range p).map fun i => m ^ i).sum - p := by
      rw [← ht] at hsq
      simpa [Finset.sum, ← Multiset.coe_range] using hsq
    exact pow_eq_one_of_orderOf_eq_prime_pow_of_sq_dvd_sub ⟨e, horder⟩ hord hsq'

theorem pow_eq_one_of_conj_mul_pow_eq [Finite X] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {P : Subgroup X} (hP : IsPGroup p P) (hPc : IsCyclic P) {φ : MulAut X}
    (hφP : ∀ s ∈ P, φ s ∈ P)
    (hZ : Function.Injective (MulAut.conj : X →* MulAut X))
    (hφinn : ∀ k : ℕ, φ ^ k ∈ (MulAut.conj : X →* MulAut X).range → φ ^ k = 1)
    {y : X} (hy : y ∈ P) {j : ℕ} (hj : (MulAut.conj y * φ ^ j) ^ p = 1) : y ^ p = 1 := by
  classical
  have hmem : ∀ i : ℕ, ∀ s ∈ P, (φ ^ i) s ∈ P := by
    intro i
    induction i with
    | zero => intro s hs; simpa using hs
    | succ i ih =>
      intro s hs
      rw [pow_succ, MulAut.mul_apply]
      exact ih _ (hφP _ hs)
  set N := ((List.range p).map fun i => ((φ ^ j) ^ i) y).prod with hNdef
  have h1 : MulAut.conj N * (φ ^ j) ^ p = 1 := by
    rw [conj_mul_pow_eq_conj_prod_mul_pow] at hj
    exact hj
  have hinner : φ ^ (j * p) ∈ (MulAut.conj : X →* MulAut X).range := by
    rw [pow_mul]
    refine ⟨N⁻¹, ?_⟩
    rw [map_inv]
    exact (eq_inv_of_mul_eq_one_right h1).symm
  have hφjp : (φ ^ j) ^ p = 1 := by
    have h := hφinn (j * p) hinner
    rwa [pow_mul] at h
  have hN1 : N = 1 := by
    apply hZ
    rw [hφjp, mul_one] at h1
    rw [h1, map_one]
  exact pow_eq_one_of_prod_range_eq_one hp2 hP hPc (hmem j) hφjp hy hN1

theorem eq_of_conj_mul_pow_eq_of_forall_inner_eq_one {φ : MulAut X} {y y' : X} {j j' : ℕ}
    (hZ : Function.Injective (MulAut.conj : X →* MulAut X))
    (hφinn : ∀ k : ℕ, φ ^ k ∈ (MulAut.conj : X →* MulAut X).range → φ ^ k = 1)
    (h : MulAut.conj y * φ ^ j = MulAut.conj y' * φ ^ j') : y = y' := by
  have key : ∀ (y y' : X) (j j' : ℕ), j' ≤ j →
      MulAut.conj y * φ ^ j = MulAut.conj y' * φ ^ j' → y = y' := by
    intro y y' j j' hjle heq
    have hcancel : MulAut.conj y * φ ^ (j - j') = MulAut.conj y' := by
      apply mul_right_cancel (b := φ ^ j')
      rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hjle]
      exact heq
    have hin : φ ^ (j - j') ∈ (MulAut.conj : X →* MulAut X).range := by
      refine ⟨y⁻¹ * y', ?_⟩
      rw [map_mul, map_inv]
      rw [← hcancel, ← mul_assoc, inv_mul_cancel, one_mul]
    have htriv := hφinn (j - j') hin
    have hconj : MulAut.conj y = MulAut.conj y' := by
      rw [← hcancel, htriv, mul_one]
    exact hZ hconj
  rcases le_total j' j with hj | hj
  · exact key y y' j j' hj h
  · exact (key y' y j' j hj h.symm).symm

theorem card_quotient_inf_zpowers_le [Finite X] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hZ : Function.Injective (MulAut.conj : X →* MulAut X)) {P₀ : Subgroup X}
    (hP₀ : IsPGroup p P₀) (hP₀c : IsCyclic P₀) {φ : MulAut X} (hφP : ∀ s ∈ P₀, φ s ∈ P₀)
    (hφinn : ∀ k : ℕ, φ ^ k ∈ (MulAut.conj : X →* MulAut X).range → φ ^ k = 1)
    {R : Subgroup (MulAut X)} (hR : Open.IsElemAbelian p R)
    (hRφ : ∀ α ∈ R, ∃ y ∈ P₀, ∃ j : ℕ, α = MulAut.conj y * φ ^ j) :
    Nat.card (R ⧸ (R ⊓ zpowers φ).subgroupOf R) ≤ p := by
  classical
  have hrep : ∀ α : R, ∃ y : P₀, ∃ j : ℕ, (α : MulAut X) = MulAut.conj (y : X) * φ ^ j := by
    intro α
    obtain ⟨y, hy, j, hj⟩ := hRφ α α.2
    exact ⟨⟨y, hy⟩, j, hj⟩
  let yof : R → P₀ := fun α => Classical.choose (hrep α)
  let jof : R → ℕ := fun α => Classical.choose (Classical.choose_spec (hrep α))
  have hjof : ∀ α : R, (α : MulAut X) = MulAut.conj (yof α : X) * φ ^ (jof α) :=
    fun α => Classical.choose_spec (Classical.choose_spec (hrep α))
  have hpow : ∀ α : R, (yof α : X) ^ p = 1 := by
    intro α
    refine pow_eq_one_of_conj_mul_pow_eq (P := P₀) (j := jof α) hp2 hP₀ hP₀c hφP hZ hφinn
      (yof α).2 ?_
    rw [← hjof α]
    exact hR.2 (α : MulAut X) α.2
  let T := {y : P₀ // y ^ p = 1}
  let F : R → T := fun α => ⟨yof α, by
    apply Subtype.ext
    simpa using hpow α⟩
  have hF_eq : ∀ (α : R) (y : P₀) (j : ℕ),
      (α : MulAut X) = MulAut.conj (y : X) * φ ^ j → y = yof α := by
    intro α y j hyj
    exact Subtype.ext (eq_of_conj_mul_pow_eq_of_forall_inner_eq_one (y := (y : X))
      (y' := (yof α : X)) (j := j) (j' := jof α) hZ hφinn (by rw [← hyj, hjof α]))
  let H : Subgroup (MulAut X) := R ⊓ zpowers φ
  let HR : Subgroup R := H.subgroupOf R
  let Fbar : R ⧸ HR → T :=
    Quotient.lift F (fun a b hab => by
      have hab' : a⁻¹ * b ∈ HR := (QuotientGroup.leftRel_apply).mp hab
      have hhabX : ((a : R) : MulAut X)⁻¹ * ((b : R) : MulAut X) ∈ H := by
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using (Subgroup.mem_subgroupOf.mp hab')
      have hhabφ : ((a : R) : MulAut X)⁻¹ * ((b : R) : MulAut X) ∈ zpowers φ :=
        (Subgroup.mem_inf.mp hhabX).2
      have hpowmem : ((a : R) : MulAut X)⁻¹ * ((b : R) : MulAut X) ∈ Submonoid.powers φ :=
        (mem_powers_iff_mem_zpowers).mpr hhabφ
      obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff
        (((a : R) : MulAut X)⁻¹ * ((b : R) : MulAut X)) φ).mp hpowmem
      have hb : (b : MulAut X) = MulAut.conj (yof a : X) * φ ^ (jof a + k) := by
        calc
          (b : MulAut X) = (a : MulAut X) * ((a : MulAut X)⁻¹ * (b : MulAut X)) := by group
          _ = (MulAut.conj (yof a : X) * φ ^ jof a) * φ ^ k := by rw [hk, hjof a]
          _ = MulAut.conj (yof a : X) * φ ^ (jof a + k) := by group
      exact Subtype.ext (hF_eq b (yof a) (jof a + k) hb))
  have hFbar_inj : Function.Injective Fbar := by
    intro q1 q2
    refine Quotient.inductionOn₂ q1 q2 ?_
    intro a b hq
    change F a = F b at hq
    have hy : yof a = yof b := congrArg Subtype.val hq
    apply QuotientGroup.eq.mpr
    rw [Subgroup.mem_subgroupOf]
    have hyX : (yof b : X) = (yof a : X) := by rw [hy]
    have hmφ : ((a⁻¹ * b : R) : MulAut X) ∈ zpowers φ := by
      have hcalc : ((a⁻¹ * b : R) : MulAut X) = (φ ^ jof a)⁻¹ * φ ^ jof b := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hjof a, hjof b, hyX, mul_inv_rev]
        group
      rw [hcalc]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers φ _))
        (Subgroup.npow_mem_zpowers φ _)
    exact Subgroup.mem_inf.mpr ⟨(a⁻¹ * b).2, hmφ⟩
  have hTcard : Nat.card T ≤ p := by
    have : Fintype P₀ := Fintype.ofFinite P₀
    have h := IsCyclic.card_pow_eq_one_le (α := P₀) (n := p) (Fact.out : p.Prime).pos
    simpa [T, Nat.card_eq_fintype_card, Fintype.card_subtype] using h
  exact (Nat.card_le_card_of_injective Fbar hFbar_inj).trans hTcard

theorem card_le_mul_card_inf_zpowers [Finite X] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hZ : Function.Injective (MulAut.conj : X →* MulAut X)) {P₀ : Subgroup X}
    (hP₀ : IsPGroup p P₀) (hP₀c : IsCyclic P₀) {φ : MulAut X} (hφP : ∀ s ∈ P₀, φ s ∈ P₀)
    (hφinn : ∀ k : ℕ, φ ^ k ∈ (MulAut.conj : X →* MulAut X).range → φ ^ k = 1)
    {R : Subgroup (MulAut X)} (hR : Open.IsElemAbelian p R)
    (hRφ : ∀ α ∈ R, ∃ y ∈ P₀, ∃ j : ℕ, α = MulAut.conj y * φ ^ j) :
    Nat.card R ≤ p * Nat.card (R ⊓ zpowers φ : Subgroup (MulAut X)) := by
  have hquot := card_quotient_inf_zpowers_le hp2 hZ hP₀ hP₀c hφP hφinn hR hRφ
  have hHR : Nat.card ((R ⊓ zpowers φ).subgroupOf R) =
      Nat.card (R ⊓ zpowers φ : Subgroup (MulAut X)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : R ⊓ zpowers φ ≤ R)).toEquiv
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup, hHR]
  exact Nat.mul_le_mul_right _ hquot

theorem exists_sylow_forall_apply_mem [Finite X] {p : ℕ} [Fact p.Prime]
    {R : Subgroup (MulAut X)} (hR : IsPGroup p R) :
    ∃ Q : Sylow p X, ∀ α ∈ R, ∀ s ∈ (Q : Subgroup X), α s ∈ Q := by
  obtain ⟨Q, hQ⟩ := hR.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p X)
    (not_dvd_card_sylow p X)
  refine ⟨Q, fun α hα s hs => ?_⟩
  have h : α • Q = Q := (Subgroup.smul_def (⟨α, hα⟩ : R) Q).symm.trans (hQ ⟨α, hα⟩)
  have hmem : α • s ∈ ((α • Q : Sylow p X) : Subgroup X) := by
    rw [Sylow.pointwise_smul_def]
    exact Subgroup.smul_mem_pointwise_smul s α _ hs
  rw [h] at hmem
  exact hmem

end CFSG

end
