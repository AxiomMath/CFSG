module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open scoped Pointwise

section SmallAut

variable {X : Type*} [Group X]

private theorem smallAut_isPGroup_zpowers {p : ℕ} {α : MulAut X} (hα : α ^ p = 1) :
    IsPGroup p (Subgroup.zpowers α) := by
  intro h
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h.2
  rw [Subgroup.coe_pow, ← hk, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, hα, one_zpow, Subgroup.coe_one]

private theorem smallAut_card_modEq_card_fixed [Finite X] {p : ℕ} [Fact p.Prime]
    {A : Subgroup (MulAut X)} (hA : IsPGroup p A) {S : Set X} (hS : ∀ a ∈ A, ∀ x ∈ S, a x ∈ S) :
    S.ncard ≡ {x | x ∈ S ∧ x ∈ FixedPoints.subgroup A X}.ncard [MOD p] := by
  let T : SubMulAction A X :=
    { carrier := S
      smul_mem' := fun a _ hx => hS a a.2 _ hx }
  have h := hA.card_modEq_card_fixedPoints T
  have hfix : Nat.card (MulAction.fixedPoints A T) =
      {x | x ∈ S ∧ x ∈ FixedPoints.subgroup A X}.ncard := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr
      { toFun := fun y => ⟨y.1.1, y.1.2, fun a => congrArg Subtype.val (y.2 a)⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, fun a => Subtype.ext (x.2.2 a)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [hfix] at h
  exact h

private theorem smallAut_exists_sylow_invariant [Finite X] {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    {A : Subgroup (MulAut X)} (hA : IsPGroup p A) (hpX : ¬ p ∣ Nat.card X) :
    ∃ R : Sylow r X, ∀ a ∈ A, ∀ x ∈ (R : Subgroup X), a x ∈ (R : Subgroup X) := by
  have hnd : ¬ p ∣ Nat.card (Sylow r X) := by
    intro h
    obtain ⟨P⟩ : Nonempty (Sylow r X) := inferInstance
    exact hpX (h.trans ((Sylow.card_dvd_index P).trans (Subgroup.index_dvd_card _)))
  obtain ⟨R, hR⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow r X) hnd
  refine ⟨R, fun a ha x hx => ?_⟩
  have h1 : ((⟨a, ha⟩ : A) • R : Sylow r X) = R := hR ⟨a, ha⟩
  have h2 : (⟨a, ha⟩ : A) • x ∈ (((⟨a, ha⟩ : A) • R : Sylow r X) : Subgroup X) :=
    Subgroup.smul_mem_pointwise_smul x (⟨a, ha⟩ : A) (R : Subgroup X) hx
  rw [h1] at h2
  exact h2

private theorem smallAut_exists_mem_sylow_orderOf_eq [Finite X] {r k : ℕ} [Fact r.Prime]
    (R : Sylow r X) {x : X} (hx : orderOf x = r ^ k) :
    ∃ y ∈ (R : Subgroup X), orderOf y = r ^ k := by
  have hP : IsPGroup r (Subgroup.zpowers x) := IsPGroup.of_card (by rw [Nat.card_zpowers, hx])
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X Q R
  refine ⟨MulAut.conj g x, ?_, by rw [MulEquiv.orderOf_eq]; exact hx⟩
  have h1 := Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (Q : Subgroup X)
    (hQ (Subgroup.mem_zpowers x))
  rw [← Sylow.coe_subgroup_smul, hg] at h1
  exact h1

private theorem smallAut_arith {p r k c : ℕ} (hp : p = 5 ∨ p = 7) (hr : r = 2 ∨ r = 3)
    (hk : k ≤ 3) (hc : c ∣ r ^ k) (hmod : r ^ k ≡ c [MOD p]) :
    c = r ^ k ∨ (p = 7 ∧ r = 2 ∧ k = 3 ∧ c = 1) := by
  have key : ∀ p ∈ ({5, 7} : Finset ℕ), ∀ r ∈ ({2, 3} : Finset ℕ), ∀ k ∈ Finset.range 4,
      ∀ c ∈ Nat.divisors (r ^ k), r ^ k % p = c % p →
        c = r ^ k ∨ (p = 7 ∧ r = 2 ∧ k = 3 ∧ c = 1) := by decide
  refine key p ?_ r ?_ k ?_ c ?_ hmod
  · rcases hp with rfl | rfl <;> simp
  · rcases hr with rfl | rfl <;> simp
  · simpa [Nat.lt_succ_iff] using hk
  · exact Nat.mem_divisors.mpr ⟨hc, (pow_pos (by rcases hr with rfl | rfl <;> norm_num) k).ne'⟩

private theorem smallAut_le_three {r k : ℕ} (hr : r = 2 ∨ r = 3) (h : r ^ k ∣ 216) : k ≤ 3 := by
  by_contra hk
  have h4 : r ^ 4 ∣ 216 := (pow_dvd_pow r (by omega)).trans h
  rcases hr with rfl | rfl <;> revert h4 <;> decide

private theorem smallAut_le_fixed_or [Finite X] {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hp : p = 5 ∨ p = 7) (hr : r = 2 ∨ r = 3) (hX : Nat.card X ∣ 216)
    {A : Subgroup (MulAut X)} (hA : IsPGroup p A) {R : Subgroup X} (hRp : IsPGroup r R)
    (hR : ∀ a ∈ A, ∀ x ∈ R, a x ∈ R) :
    R ≤ FixedPoints.subgroup A X ∨
      (p = 7 ∧ r = 2 ∧ Nat.card R = 8 ∧ R ⊓ FixedPoints.subgroup A X = ⊥) := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hRp
  have hk3 : k ≤ 3 :=
    smallAut_le_three hr (hk ▸ (Subgroup.card_subgroup_dvd_card R).trans hX)
  have hmod : Nat.card R ≡ Nat.card ↥(R ⊓ FixedPoints.subgroup A X) [MOD p] :=
    smallAut_card_modEq_card_fixed hA (S := (R : Set X)) hR
  have hdvd : Nat.card ↥(R ⊓ FixedPoints.subgroup A X) ∣ Nat.card R :=
    Subgroup.card_dvd_of_le inf_le_left
  rw [hk] at hmod hdvd
  rcases smallAut_arith hp hr hk3 hdvd hmod with h | ⟨h7, h2, h3, h1⟩
  · left
    exact inf_eq_left.mp
      (Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq (hk.trans h.symm)))
  · right
    exact ⟨h7, h2, by rw [hk, h2, h3]; norm_num, Subgroup.eq_bot_of_card_le _ h1.le⟩

private theorem smallAut_false_of_bad_case [Finite X] {A : Subgroup (MulAut X)}
    (hA : IsPGroup 7 A) {R : Subgroup X} (hR : ∀ a ∈ A, ∀ x ∈ R, a x ∈ R)
    (hcard : Nat.card R = 8) (hbot : R ⊓ FixedPoints.subgroup A X = ⊥)
    (h4 : ∃ y ∈ R, orderOf y = 4) : False := by
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  obtain ⟨y, hyR, hy4⟩ := h4
  set S : Set X := {x | x ∈ R ∧ orderOf x = 4}
  have hSinv : ∀ a ∈ A, ∀ x ∈ S, a x ∈ S := fun a ha x hx =>
    ⟨hR a ha x hx.1, by rw [MulEquiv.orderOf_eq]; exact hx.2⟩
  have hmod := smallAut_card_modEq_card_fixed hA hSinv
  have hempty : {x | x ∈ S ∧ x ∈ FixedPoints.subgroup A X} = ∅ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hxS hxF
    have hx1 : x ∈ R ⊓ FixedPoints.subgroup A X := ⟨hxS.1, hxF⟩
    rw [hbot, Subgroup.mem_bot] at hx1
    have := hxS.2
    rw [hx1, orderOf_one] at this
    omega
  rw [hempty, Set.ncard_empty] at hmod
  have h7 : 7 ∣ S.ncard := (Nat.modEq_zero_iff_dvd).1 hmod
  have hpos : 0 < S.ncard := (Set.ncard_pos).2 ⟨y, hyR, hy4⟩
  have h7le : 7 ≤ S.ncard := Nat.le_of_dvd hpos h7
  obtain ⟨z, hz⟩ : ∃ z : R, orderOf z = 2 :=
    exists_prime_orderOf_dvd_card' 2 (by rw [hcard]; norm_num)
  have hz2 : orderOf (z : X) = 2 := by rw [Subgroup.orderOf_coe]; exact hz
  have h1z : (1 : X) ≠ z := by
    intro h
    have := hz2
    rw [← h, orderOf_one] at this
    omega
  have hsub : ({(1 : X), (z : X)} : Set X) ∪ S ⊆ (R : Set X) := by
    rintro x (hx | hx)
    · rcases hx with rfl | rfl
      · exact R.one_mem
      · exact z.2
    · exact hx.1
  have hdisj : Disjoint ({(1 : X), (z : X)} : Set X) S := by
    rw [Set.disjoint_left]
    rintro x (rfl | rfl) hxS
    · have := hxS.2
      rw [orderOf_one] at this
      omega
    · have := hxS.2
      rw [hz2] at this
      omega
  have hcount := Set.ncard_le_ncard hsub
  rw [Set.ncard_union_eq hdisj, Set.ncard_pair h1z] at hcount
  have hR8 : (R : Set X).ncard = 8 := by rw [← Nat.card_coe_set_eq]; exact hcard
  omega

private theorem smallAut_exists_sylow_le_fixed [Finite X] {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hp : p = 5 ∨ p = 7) (hr : r = 2 ∨ r = 3) (hX : Nat.card X ∣ 216)
    {A : Subgroup (MulAut X)} (hA : IsPGroup p A)
    (h7 : p = 7 → 8 ∣ Nat.card X → ∃ x : X, orderOf x = 4) :
    ∃ R : Sylow r X, (R : Subgroup X) ≤ FixedPoints.subgroup A X := by
  have hpX : ¬ p ∣ Nat.card X := fun h => by
    have h216 := h.trans hX
    rcases hp with rfl | rfl <;> revert h216 <;> decide
  obtain ⟨R, hR⟩ := smallAut_exists_sylow_invariant (r := r) hA hpX
  refine ⟨R, ?_⟩
  rcases smallAut_le_fixed_or hp hr hX hA R.isPGroup' hR with h | ⟨h7', h2, hcard, hbot⟩
  · exact h
  · exfalso
    subst h7' h2
    have h8 : 8 ∣ Nat.card X := hcard ▸ Subgroup.card_subgroup_dvd_card (R : Subgroup X)
    obtain ⟨x, hx⟩ := h7 rfl h8
    obtain ⟨y, hyR, hy⟩ :=
      smallAut_exists_mem_sylow_orderOf_eq (k := 2) R (by rw [hx]; norm_num)
    exact smallAut_false_of_bad_case hA hR hcard hbot ⟨y, hyR, by rw [hy]; norm_num⟩

private theorem smallAut_sup_eq_top [Finite X] (hX : Nat.card X ∣ 216) (R₂ : Sylow 2 X)
    (R₃ : Sylow 3 X) : (R₂ : Subgroup X) ⊔ R₃ = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set M : Subgroup X := (R₂ : Subgroup X) ⊔ R₃
  have h2 : ¬ 2 ∣ M.index := fun h =>
    R₂.not_dvd_index (h.trans (Subgroup.index_dvd_of_le le_sup_left))
  have h3 : ¬ 3 ∣ M.index := fun h =>
    R₃.not_dvd_index (h.trans (Subgroup.index_dvd_of_le le_sup_right))
  have hcop2 : Nat.Coprime M.index 2 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2).symm
  have hcop3 : Nat.Coprime M.index 3 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).symm
  have hcop : Nat.Coprime M.index 216 := by
    rw [show (216 : ℕ) = 2 ^ 3 * 3 ^ 3 by norm_num]
    exact (hcop2.pow_right 3).mul_right (hcop3.pow_right 3)
  exact Subgroup.index_eq_one.mp
    (Nat.Coprime.eq_one_of_dvd hcop ((Subgroup.index_dvd_card M).trans hX))

end SmallAut

theorem eq_one_of_card_dvd_216 {X : Type*} [Group X] [Finite X] (hX : Nat.card X ∣ 216)
    {p : ℕ} (hp : p = 5 ∨ p = 7) {α : MulAut X} (hα : α ^ p = 1)
    (h7 : p = 7 → 8 ∣ Nat.card X → ∃ x : X, orderOf x = 4) : α = 1 := by
  have : Fact p.Prime := ⟨by rcases hp with rfl | rfl; exacts [Nat.prime_five, Nat.prime_seven]⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : IsPGroup p (Subgroup.zpowers α) := smallAut_isPGroup_zpowers hα
  obtain ⟨R₂, h₂⟩ := smallAut_exists_sylow_le_fixed (r := 2) hp (Or.inl rfl) hX hA h7
  obtain ⟨R₃, h₃⟩ := smallAut_exists_sylow_le_fixed (r := 3) hp (Or.inr rfl) hX hA h7
  have hsup := smallAut_sup_eq_top hX R₂ R₃
  have htop : FixedPoints.subgroup (Subgroup.zpowers α) X = ⊤ :=
    top_le_iff.mp (hsup ▸ sup_le h₂ h₃)
  ext x
  have hx : x ∈ FixedPoints.subgroup (Subgroup.zpowers α) X := htop ▸ Subgroup.mem_top x
  exact hx ⟨α, Subgroup.mem_zpowers α⟩

theorem mem_centralizer_of_card_dvd_216 {G : Type*} [Group G] {X : Subgroup G} [Finite X]
    (hX : Nat.card X ∣ 216) {p : ℕ} (hp : p = 5 ∨ p = 7) {w : G}
    (hwN : w ∈ Subgroup.normalizer (X : Set G)) (hwp : w ^ p = 1)
    (h7 : p = 7 → 8 ∣ Nat.card X → ∃ x ∈ X, orderOf x = 4) :
    w ∈ Subgroup.centralizer (X : Set G) := by
  set n : Subgroup.normalizer (X : Set G) := ⟨w, hwN⟩
  have hnp : n ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hwp)
  have hα : X.normalizerMonoidHom n ^ p = 1 := by rw [← map_pow, hnp, map_one]
  have h1 : X.normalizerMonoidHom n = 1 := by
    refine eq_one_of_card_dvd_216 hX hp hα fun h8 hd => ?_
    obtain ⟨x, hx, hox⟩ := h7 h8 hd
    exact ⟨⟨x, hx⟩, by rw [Subgroup.orderOf_mk]; exact hox⟩
  have h2 : n ∈ X.normalizerMonoidHom.ker := h1
  rw [Subgroup.normalizerMonoidHom_ker] at h2
  exact h2

end CFSG.LocalAnalysis.GLTheoremA.T263.DX
