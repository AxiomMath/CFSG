module

public import CFSG.CharacterTheory.Semidihedral.StructureTransport
public import CFSG.Permutation.FiveTransitive.CyclicTwoAutomorphismKernel
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition

public section

namespace CFSG.Semidihedral.Principal

open CFSG.Open CFSG.FiveTransitive.CyclicTwoAutomorphismKernel
  CFSG.DisconnectedInvolutionGraph.Helpers

theorem isPGroup_mulAut_of_invariant_cyclic {T : Type*} [Group T] [Finite T]
    (hT : IsPGroup 2 T) (u : T) (hpres : ∀ φ : MulAut T, φ u ∈ Subgroup.zpowers u)
    (hcoset : ∀ x y : T, x ∉ Subgroup.zpowers u → y ∉ Subgroup.zpowers u →
      y * x⁻¹ ∈ Subgroup.zpowers u) :
    IsPGroup 2 (MulAut T) := by
  intro φ
  have hmaps : ∀ w ∈ Subgroup.zpowers u, φ w ∈ Subgroup.zpowers u := by
    intro w hw
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [map_zpow]
    exact Subgroup.zpow_mem _ (hpres φ) m
  let f : Subgroup.zpowers u →* Subgroup.zpowers u :=
    (φ.toMonoidHom.domRestrict (Subgroup.zpowers u)).codRestrict (Subgroup.zpowers u)
      (fun w => hmaps w w.2)
  have hf : Function.Injective f := fun a b hab =>
    Subtype.ext (φ.injective (congrArg Subtype.val hab))
  let φZ : MulAut (Subgroup.zpowers u) :=
    MulEquiv.ofBijective f ⟨hf, Finite.injective_iff_surjective.mp hf⟩
  have hφZ : ∀ j : ℕ, ∀ w : Subgroup.zpowers u, (((φZ ^ j) w : Subgroup.zpowers u) : T) =
      (φ ^ j) (w : T) := by
    intro j
    induction j with
    | zero => intro w; rfl
    | succ j ih =>
      intro w
      rw [pow_succ φZ j, MulAut.mul_apply, ih, pow_succ φ j, MulAut.mul_apply]
      rfl
  obtain ⟨c, hc⟩ := automorphism_two_group (hT.to_subgroup (Subgroup.zpowers u)) φZ
  have hψZ : ∀ w ∈ Subgroup.zpowers u, (φ ^ 2 ^ c) w = w := by
    intro w hw
    have h := hφZ (2 ^ c) ⟨w, hw⟩
    rw [hc] at h
    exact h.symm
  obtain ⟨d, hd⟩ := IsPGroup.iff_orderOf.mp hT u
  suffices hfix : (φ ^ 2 ^ c) ^ 2 ^ d = 1 by
    exact ⟨c + d, by rw [pow_add, pow_mul, hfix]⟩
  set ψ := φ ^ 2 ^ c with hψ
  have hψpowZ : ∀ j : ℕ, ∀ w ∈ Subgroup.zpowers u, (ψ ^ j) w = w := by
    intro j
    induction j with
    | zero => intro w _; rfl
    | succ j ih => intro w hw; rw [pow_succ' ψ j, MulAut.mul_apply, ih w hw, hψZ w hw]
  by_cases hall : ∀ y : T, y ∈ Subgroup.zpowers u
  · exact MulEquiv.ext fun y => hψpowZ _ y (hall y)
  push Not at hall
  obtain ⟨x, hx⟩ := hall
  have hψx : ψ x ∉ Subgroup.zpowers u := fun h => hx (by
    have h1 := ψ.injective (hψZ _ h)
    rwa [h1] at h)
  have hbZ : ψ x * x⁻¹ ∈ Subgroup.zpowers u := hcoset x (ψ x) hx hψx
  have hψpow : ∀ j : ℕ, (ψ ^ j) x = (ψ x * x⁻¹) ^ j * x := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ' ψ j, MulAut.mul_apply, ih, map_mul, map_pow, hψZ _ hbZ, pow_succ,
        mul_assoc _ (ψ x * x⁻¹) x, inv_mul_cancel_right]
  have hbN : (ψ x * x⁻¹) ^ 2 ^ d = 1 := by
    rw [← hd]
    exact orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_of_mem_zpowers hbZ)
  refine MulEquiv.ext fun y => ?_
  by_cases hy : y ∈ Subgroup.zpowers u
  · exact hψpowZ _ y hy
  · have hyx : y * x⁻¹ ∈ Subgroup.zpowers u := hcoset x y hx hy
    have hy' : y = (y * x⁻¹) * x := by group
    rw [hy', map_mul, hψpowZ _ _ hyx, hψpow, hbN, one_mul]
    rfl

theorem isKleinFour_of_card_four_of_not_isCyclic {T : Type*} [Group T]
    (hcard : Nat.card T = 4) (hcyc : ¬ IsCyclic T) : IsKleinFour T := by
  have : Finite T := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial T := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  refine ⟨hcard, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun g hg => ?_⟩
  have hdvd : orderOf g ∣ 2 ^ 2 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hcard]
    exact orderOf_dvd_natCard g
  obtain ⟨k, hk, hgk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  interval_cases k
  · exact absurd (orderOf_eq_one_iff.mp (by simpa using hgk)) hg
  · simpa using hgk
  · exact absurd (isCyclic_of_orderOf_eq_card g (by rw [hgk, hcard]; norm_num)) hcyc

theorem isPGroup_mulAut_subgroup_of_cyclic_index_two {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup 2 G) (A : Subgroup G) [IsCyclic A]
    (hout : ∀ g : G, g ∉ A → g ^ 4 = 1)
    (hcoset : ∀ x y : G, x ∉ A → y ∉ A → y * x⁻¹ ∈ A)
    (hsq : ∀ b ∈ A, b ^ 4 = 1 → ∀ x : G, x ∉ A → (b * x) ^ 2 = x ^ 2)
    (T : Subgroup G) (hV : ¬ IsKleinFour T) (hQ : ¬ Nonempty (T ≃* QuaternionGroup 2)) :
    IsPGroup 2 (MulAut T) := by
  have hT : IsPGroup 2 T := hG.to_subgroup T
  by_cases hcyc : IsCyclic T
  · exact automorphism_two_group hT
  obtain ⟨x, hxA⟩ : ∃ x : T, (x : G) ∉ A := by
    by_contra h
    push Not at h
    exact hcyc (isCyclic_of_injective (Subgroup.inclusion fun y hy => h ⟨y, hy⟩)
      (Subgroup.inclusion_injective _))
  have hCcyc : IsCyclic (A.subgroupOf T) :=
    isCyclic_of_injective ((T.subtype.comp (A.subgroupOf T).subtype).codRestrict A
      fun w => w.2) (fun a b hab => by
        have h := congrArg Subtype.val hab
        exact Subtype.ext (Subtype.ext h))
  obtain ⟨g, hg⟩ := hCcyc.exists_generator
  have hmem : ∀ w : T, w ∈ Subgroup.zpowers (g : T) ↔ (w : G) ∈ A := by
    intro w
    constructor
    · intro hw
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact Subgroup.mem_subgroupOf.mp (Subgroup.zpow_mem _ g.2 k)
    · intro hw
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨w, Subgroup.mem_subgroupOf.mpr hw⟩)
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [← Subgroup.coe_zpow, hk]⟩
  set u : T := (g : T) with hu
  have hcosetT : ∀ y w : T, y ∉ Subgroup.zpowers u → w ∉ Subgroup.zpowers u →
      w * y⁻¹ ∈ Subgroup.zpowers u := by
    intro y w hy hw
    rw [hmem] at hy hw ⊢
    exact hcoset y w hy hw
  have hx : x ∉ Subgroup.zpowers u := fun h => hxA ((hmem x).mp h)
  have hindex : (Subgroup.zpowers u).index = 2 := by
    rw [Subgroup.index_eq_two_iff_exists_notMem_and]
    refine ⟨x, hx, fun b => ?_⟩
    by_cases hb : b ∈ Subgroup.zpowers u
    · exact Or.inr hb
    · left
      have hxinv : x⁻¹ ∉ Subgroup.zpowers u := fun h => hx (inv_mem_iff.mp h)
      simpa using hcosetT x⁻¹ b hxinv hb
  have hcardT : Nat.card T = 2 * orderOf u := by
    rw [← Subgroup.card_mul_index (Subgroup.zpowers u), Nat.card_zpowers, hindex, mul_comm]
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hT u
  have hpres : ∀ φ : MulAut T, φ u ∈ Subgroup.zpowers u := by
    intro φ
    have hφord : orderOf (φ u) = 2 ^ k := by rw [MulEquiv.orderOf_eq, hk]
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k) with rfl | rfl | rfl | hk3
    · exact absurd (isCyclic_of_prime_card (p := 2) (by rw [hcardT, hk]; norm_num)) hcyc
    · exact absurd (isKleinFour_of_card_four_of_not_isCyclic (by rw [hcardT, hk]; norm_num)
        hcyc) hV
    ·
      have hu4 : u ^ 4 = 1 := by rw [show 4 = 2 ^ 2 by norm_num, ← hk, pow_orderOf_eq_one]
      have hsame : ∀ y : T, y ∉ Subgroup.zpowers u → y ^ 2 = x ^ 2 := by
        intro y hy
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hcosetT x y hx hy)
        have hb : ((u ^ j : T) : G) ∈ A := (hmem _).mp (Subgroup.zpow_mem_zpowers u j)
        have hb4 : ((u ^ j : T) : G) ^ 4 = 1 := by
          rw [← Subgroup.coe_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
            hu4, one_zpow, Subgroup.coe_one]
        have h := hsq _ hb hb4 x hxA
        have hy' : y = u ^ j * x := by rw [hj]; group
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_pow, hy', Subgroup.coe_mul]
        exact h
      by_cases hx2 : x ^ 2 = 1
      · by_contra hφu
        have h := hsame _ hφu
        rw [hx2] at h
        have hdvd := orderOf_dvd_of_pow_eq_one h
        rw [hφord] at hdvd
        exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by norm_num)
      ·
        exfalso
        have hinv : ∀ t : T, orderOf t = 2 → t = u ^ 2 := by
          intro t ht
          have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
          have ht1 : t ≠ 1 := by
            intro h1
            rw [h1, orderOf_one] at ht
            exact absurd ht (by norm_num)
          have htu : t ∈ Subgroup.zpowers u := by
            by_contra htu
            exact hx2 ((hsame t htu).symm.trans ht2)
          obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp htu
          have hk4 : (orderOf u : ℤ) = 4 := by rw [hk]; norm_num
          have hj2 : (4 : ℤ) ∣ j * 2 := by
            rw [← hk4, orderOf_dvd_iff_zpow_eq_one, zpow_mul, zpow_ofNat]
            exact ht2
          have hj1 : ¬ (4 : ℤ) ∣ j := by
            rw [← hk4, orderOf_dvd_iff_zpow_eq_one]
            exact ht1
          rw [← zpow_ofNat, zpow_eq_zpow_iff_modEq, hk4, Int.ModEq]
          omega
        have hrank : NoCommutingDistinctInvolutions T := fun a b _ =>
          Subtype.ext ((hinv a a.2).trans (hinv b b.2).symm)
        rcases rank_one_two_cyclic_or_quaternion hT hrank with hc | ⟨m, hm, ⟨ι⟩⟩
        · exact hcyc hc
        · have hcardQ : Nat.card (QuaternionGroup (2 ^ m)) = 4 * 2 ^ m := by
            rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
          rw [Nat.card_congr ι.toEquiv, hcardT, hk] at hcardQ
          have hm1 : m = 1 := by
            have h2 : 2 ^ m = 2 ^ 1 := by omega
            exact Nat.pow_right_injective le_rfl h2
          subst hm1
          exact hQ ⟨ι.symm⟩
    ·
      by_contra hφu
      have h4 := hout _ (fun h => hφu ((hmem _).mpr h))
      have h4' : (φ u) ^ 4 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact h4)
      have hdvd := orderOf_dvd_of_pow_eq_one h4'
      rw [hφord] at hdvd
      have hle := Nat.le_of_dvd (by norm_num) hdvd
      have h8 : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk3
      omega
  exact isPGroup_mulAut_of_invariant_cyclic hT u hpres hcosetT

theorem eq_rotation_pow_mul_reflection_of_not_mem {n : ℕ} (hn : 3 ≤ n)
    (g : SemidihedralGroup n) (hg : g ∉ Subgroup.zpowers (r n)) :
    ∃ i : ℕ, g = r n ^ i * s n := by
  obtain ⟨c, hc, -⟩ := unique_normal_form n hn g
  have h2 := c.2.isLt
  rcases (by omega : c.2.val = 0 ∨ c.2.val = 1) with h0 | h1
  · rw [h0, pow_zero, mul_one] at hc
    exact absurd (hc ▸ Subgroup.npow_mem_zpowers (r n) c.1.val) hg
  · rw [h1, pow_one] at hc
    exact ⟨c.1.val, hc⟩

theorem rotation_pow_mul_reflection_pow_four {n : ℕ} (hn : 3 ≤ n) (i : ℕ) :
    (r n ^ i * s n) ^ 4 = 1 := by
  have h := reflection_zpow_square n hn (i : ℤ)
  rw [zpow_natCast, zpow_natCast] at h
  rw [show 4 = 2 * 2 from rfl, pow_mul, h, ← pow_mul, mul_comm, pow_mul, z_sq n hn, one_pow]

theorem rotation_mul_reflection_sq {n : ℕ} (hn : 4 ≤ n) (k : ℤ) (i : ℕ)
    (hk : (r n ^ k) ^ 4 = 1) :
    (r n ^ k * (r n ^ i * s n)) ^ 2 = (r n ^ i * s n) ^ 2 := by
  rw [← mul_assoc, ← zpow_natCast (r n) i, ← zpow_add, reflection_zpow_square n (by omega),
    reflection_zpow_square n (by omega), zpow_add]
  have hhalf : half n = 4 * 2 ^ (n - 4) := by
    rw [half, show n - 2 = 2 + (n - 4) by omega, pow_add]
    norm_num
  have hz : z n ^ k = 1 := by
    rw [z, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hhalf, pow_mul, hk,
      one_pow]
  rw [hz, one_mul]

theorem subgroup_automorphisms_outside_four_and_quaternion_eight {S : Type*} [Group S] {n : ℕ}
    (hn : 4 ≤ n) (hS : Nonempty (SemidihedralGroup n ≃* S)) :
    (∀ T : Subgroup S, ¬ IsKleinFour T → ¬ Nonempty (T ≃* QuaternionGroup 2) →
      IsPGroup 2 (MulAut T)) ∧ IsPGroup 2 (MulAut S) := by
  obtain ⟨e⟩ := hS
  have := presentation_finite n (by omega)
  have : Finite S := Finite.of_equiv _ e.toEquiv
  have hG : IsPGroup 2 S := (isTwoGroup n (by omega)).of_equiv e
  have hmem : ∀ g : SemidihedralGroup n,
      e g ∈ Subgroup.zpowers (e (r n)) ↔ g ∈ Subgroup.zpowers (r n) := fun g => by
    rw [← map_rotationSubgroup n e, mem_map_equiv_iff]
    rfl
  have houtside : ∀ g : S, g ∉ Subgroup.zpowers (e (r n)) →
      ∃ i : ℕ, g = e (r n ^ i * s n) := by
    intro g hg
    obtain ⟨i, hi⟩ := eq_rotation_pow_mul_reflection_of_not_mem (by omega) (e.symm g)
      (by rwa [← hmem, e.apply_symm_apply])
    exact ⟨i, by rw [← hi, e.apply_symm_apply]⟩
  have hout : ∀ g : S, g ∉ Subgroup.zpowers (e (r n)) → g ^ 4 = 1 := by
    intro g hg
    obtain ⟨i, rfl⟩ := houtside g hg
    rw [← map_pow, rotation_pow_mul_reflection_pow_four (by omega), map_one]
  have hcoset : ∀ x y : S, x ∉ Subgroup.zpowers (e (r n)) → y ∉ Subgroup.zpowers (e (r n)) →
      y * x⁻¹ ∈ Subgroup.zpowers (e (r n)) := by
    intro x y hx hy
    obtain ⟨i, rfl⟩ := houtside x hx
    obtain ⟨j, rfl⟩ := houtside y hy
    rw [← map_inv, ← map_mul, hmem]
    have h : r n ^ j * s n * (r n ^ i * s n)⁻¹ = r n ^ j * (r n ^ i)⁻¹ := by group
    rw [h]
    exact Subgroup.mul_mem _ (Subgroup.npow_mem_zpowers _ _)
      (Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers _ _))
  have hsq : ∀ b ∈ Subgroup.zpowers (e (r n)), b ^ 4 = 1 →
      ∀ x : S, x ∉ Subgroup.zpowers (e (r n)) → (b * x) ^ 2 = x ^ 2 := by
    intro b hb hb4 x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    obtain ⟨i, rfl⟩ := houtside x hx
    rw [← map_zpow, ← map_pow] at hb4
    rw [← map_zpow, ← map_mul, ← map_pow, ← map_pow,
      rotation_mul_reflection_sq hn k i (e.injective (hb4.trans (map_one e).symm))]
  refine ⟨fun T hV hQ => isPGroup_mulAut_subgroup_of_cyclic_index_two hG _ hout hcoset hsq T
    hV hQ, isPGroup_mulAut_of_invariant_cyclic hG (e (r n)) (fun φ => ?_) hcoset⟩
  by_contra hφ
  have hdvd := orderOf_dvd_of_pow_eq_one (hout _ hφ)
  rw [MulEquiv.orderOf_eq, equiv_orderOf, orderOf_r n (by omega), modulus] at hdvd
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  have h8 : 2 ^ 3 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end CFSG.Semidihedral.Principal
