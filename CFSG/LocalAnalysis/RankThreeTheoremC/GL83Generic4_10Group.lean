module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup

variable {J K : Type} [Group J] [Finite J] [Group K]

omit [Finite J] in
private theorem u3grp_card_fibre (ψ : J →* K) {k : K} (hk : k ∈ ψ.range) :
    Nat.card (ψ ⁻¹' {k}) = Nat.card ψ.ker := by
  obtain ⟨j₀, hj₀⟩ := hk
  have h1 : ∀ y : ψ ⁻¹' {k}, j₀⁻¹ * (y : J) ∈ ψ.ker := fun y => by
    have hy : ψ y = k := y.2
    rw [MonoidHom.mem_ker, map_mul, map_inv, hj₀, hy, inv_mul_cancel]
  have h2 : ∀ x : ψ.ker, j₀ * (x : J) ∈ ψ ⁻¹' {k} := fun x => by
    have hx : ψ x = 1 := x.2
    simp [Set.mem_preimage, map_mul, hj₀, hx]
  exact Nat.card_congr
    { toFun := fun y => ⟨j₀⁻¹ * y, h1 y⟩
      invFun := fun x => ⟨j₀ * x, h2 x⟩
      left_inv := fun y => Subtype.ext (mul_inv_cancel_left j₀ y)
      right_inv := fun x => Subtype.ext (inv_mul_cancel_left j₀ x) }

omit [Finite J] in
private theorem u3grp_exists_fixed_fibre {p : ℕ} [Fact p.Prime] (ψ : J →* K)
    (hψ : Function.Surjective ψ) (hcop : ¬ p ∣ Nat.card ψ.ker) {A : Subgroup J}
    (hA : IsPGroup p A) {k : K} (hk : ∀ a ∈ A, ψ a * k = k * ψ a) :
    ∃ j : J, ψ j = k ∧ ∀ a ∈ A, a * j = j * a := by
  let _ : MulAction A (ψ ⁻¹' {k}) :=
    { smul := fun a y => ⟨(a : J) * (y : J) * (a : J)⁻¹, by
        have hy : ψ y = k := y.2
        have ha := hk a a.2
        simp only [Set.mem_preimage, Set.mem_singleton_iff, map_mul, map_inv, hy]
        rw [ha, mul_assoc, mul_inv_cancel, mul_one]⟩
      one_smul := fun y => Subtype.ext (by
        change ((1 : A) : J) * (y : J) * ((1 : A) : J)⁻¹ = y
        simp)
      mul_smul := fun a b y => Subtype.ext (by
        change ((a * b : A) : J) * (y : J) * ((a * b : A) : J)⁻¹ =
          (a : J) * ((b : J) * (y : J) * (b : J)⁻¹) * (a : J)⁻¹
        simp [mul_assoc]) }
  have hcard : ¬ p ∣ Nat.card (ψ ⁻¹' {k}) := by
    rwa [u3grp_card_fibre ψ (MonoidHom.mem_range.mpr (hψ k))]
  obtain ⟨⟨j, hj⟩, hfix⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (ψ ⁻¹' {k}) hcard
  refine ⟨j, hj, fun a ha => ?_⟩
  have h := congrArg Subtype.val (hfix ⟨a, ha⟩)
  have h' : a * j * a⁻¹ = j := h
  rw [mul_inv_eq_iff_eq_mul] at h'
  exact h'

set_option linter.unusedVariables false in
theorem exists_involution_lift {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (ψ : J →* K)
    (hψ : Function.Surjective ψ) (hodd : Odd (Nat.card ψ.ker)) (hcop : ¬ p ∣ Nat.card ψ.ker)
    {Z₀ : Subgroup J} (hZ₀ : IsPGroup p Z₀) {zb : K} (h1 : zb ≠ 1) (h2 : zb ^ 2 = 1)
    (hc : ∀ c ∈ Z₀, zb * ψ c = ψ c * zb) :
    ∃ z : J, z ≠ 1 ∧ z ^ 2 = 1 ∧ ψ z = zb ∧ ∀ c ∈ Z₀, z * c = c * z := by
  obtain ⟨w, hwψ, hwc⟩ := u3grp_exists_fixed_fibre ψ hψ hcop hZ₀ fun c hc' => (hc c hc').symm
  obtain ⟨a, d, hd, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos w).ne'
  have hzψ : ψ (w ^ d) = zb := by
    obtain ⟨e, he⟩ := hd
    rw [map_pow, hwψ, he, pow_succ, pow_mul, h2, one_pow, one_mul]
  refine ⟨w ^ d, fun h => h1 (by rw [← hzψ, h, map_one]), ?_, hzψ, fun c hc' => ?_⟩
  · have hker : (w ^ d) ^ 2 ∈ ψ.ker := by rw [MonoidHom.mem_ker, map_pow, hzψ, h2]
    have hpow : ((w ^ d) ^ 2) ^ 2 ^ a = 1 := by
      rw [← pow_mul, ← pow_mul, show d * (2 * 2 ^ a) = orderOf w * 2 by rw [hn]; ring, pow_mul,
        pow_orderOf_eq_one, one_pow]
    have hcop2 : Nat.Coprime (2 ^ a) (Nat.card ψ.ker) :=
      Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hodd)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop2 (orderOf_dvd_of_pow_eq_one hpow)
      (Subgroup.orderOf_dvd_natCard _ hker))
  · exact Commute.pow_left (hwc c hc').symm d

set_option linter.unusedSectionVars false in
theorem centralizer_le_map_centralizer (ψ : J →* K) (hψ : Function.Surjective ψ)
    (hodd : Odd (Nat.card ψ.ker)) {z : J} (hz : z ^ 2 = 1) :
    Subgroup.centralizer ({ψ z} : Set K) ≤ (Subgroup.centralizer ({z} : Set J)).map ψ := by
  intro k hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : ¬ 2 ∣ Nat.card ψ.ker := Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hodd)
  have hA : IsPGroup 2 (zpowers z) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hz)
  have hkc : Commute k (ψ z) := mem_centralizer_singleton_iff.mp hk
  obtain ⟨j, hjk, hjc⟩ := u3grp_exists_fixed_fibre ψ hψ hcop hA (k := k) fun a ha => by
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ha
    rw [map_zpow]
    exact (hkc.zpow_right n).symm.eq
  exact ⟨j, mem_centralizer_singleton_iff.mpr (hjc z (mem_zpowers z)).symm, hjk⟩

set_option linter.unusedVariables false in
theorem normalizer_map_le_map_normalizer {p : ℕ} [Fact p.Prime] (ψ : J →* K)
    (hψ : Function.Surjective ψ) (hcop : ¬ p ∣ Nat.card ψ.ker) (Q : Sylow p J) :
    Subgroup.normalizer (((Q : Subgroup J).map ψ : Subgroup K) : Set K) ≤
      (Subgroup.normalizer ((Q : Subgroup J) : Set J)).map ψ := by
  intro k hk
  obtain ⟨j, rfl⟩ := hψ k
  set W : Subgroup J := ((Q : Subgroup J).map ψ).comap ψ with hW
  have hQW : (Q : Subgroup J) ≤ W := le_comap_map ψ _
  have hjQW : ((j • Q : Sylow p J) : Subgroup J) ≤ W := by
    intro y hy
    rw [Sylow.coe_subgroup_smul, mem_smul_pointwise_iff_exists] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    have hψs : ψ (MulAut.conj j • s) = ψ j * ψ s * (ψ j)⁻¹ := by
      rw [MulAut.smul_def, MulAut.conj_apply, map_mul, map_mul, map_inv]
    rw [hW, mem_comap, hψs]
    exact (mem_normalizer_iff.mp hk (ψ s)).mp (mem_map_of_mem ψ hs)
  obtain ⟨w, hw⟩ := MulAction.exists_smul_eq W (Q.subtype hQW) ((j • Q).subtype hjQW)
  rw [Sylow.smul_subtype hQW w] at hw
  have hwQ : (w : J) • Q = j • Q := Sylow.subtype_injective hw
  have hn : (w : J)⁻¹ * j ∈ normalizer ((Q : Subgroup J) : Set J) :=
    Sylow.smul_eq_iff_mem_normalizer.mp (by rw [mul_smul, ← hwQ, inv_smul_smul])
  have hmul : ψ j = ψ (w : J) * ψ ((w : J)⁻¹ * j) := by rw [← map_mul, mul_inv_cancel_left]
  rw [hmul]
  exact Subgroup.mul_mem _ (map_mono le_normalizer w.2) (mem_map_of_mem ψ hn)

theorem eq_top_of_involution_generation {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (ψ : J →* K)
    (hψ : Function.Surjective ψ) (hodd : Odd (Nat.card ψ.ker)) (hcop : ¬ p ∣ Nat.card ψ.ker)
    (Q : Sylow p J) {Z₀ : Subgroup J} (hZ₀ : IsPGroup p Z₀) {zb : K} (h1 : zb ≠ 1)
    (h2 : zb ^ 2 = 1) (hc : ∀ c ∈ Z₀, zb * ψ c = ψ c * zb)
    (hgen : Subgroup.closure ((Subgroup.centralizer ({zb} : Set K) : Set K) ∪
      (Subgroup.normalizer (((Q : Subgroup J).map ψ : Subgroup K) : Set K) : Set K)) = ⊤)
    {M₁ : Subgroup J} (hker : ψ.ker ≤ M₁)
    (hN : Subgroup.normalizer ((Q : Subgroup J) : Set J) ≤ M₁)
    (hC : ∀ z : J, z ≠ 1 → z ^ 2 = 1 → (∀ c ∈ Z₀, z * c = c * z) →
      Subgroup.centralizer ({z} : Set J) ≤ M₁) :
    M₁ = ⊤ := by
  obtain ⟨z, hz1, hz2, hzψ, hzc⟩ := exists_involution_lift hp2 ψ hψ hodd hcop hZ₀ h1 h2 hc
  have hCK : Subgroup.centralizer ({zb} : Set K) ≤ M₁.map ψ := by
    rw [← hzψ]
    exact (centralizer_le_map_centralizer ψ hψ hodd hz2).trans (map_mono (hC z hz1 hz2 hzc))
  have hNK : Subgroup.normalizer (((Q : Subgroup J).map ψ : Subgroup K) : Set K) ≤ M₁.map ψ :=
    (normalizer_map_le_map_normalizer ψ hψ hcop Q).trans (map_mono hN)
  have htop : M₁.map ψ = ⊤ :=
    top_le_iff.mp (hgen ▸ (closure_le _).mpr (Set.union_subset hCK hNK))
  refine top_le_iff.mp fun j _ => ?_
  obtain ⟨m, hm, hmj⟩ : ψ j ∈ M₁.map ψ := htop ▸ mem_top (ψ j)
  have hjm : j * m⁻¹ ∈ ψ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hmj, mul_inv_cancel]
  simpa using M₁.mul_mem (hker hjm) hm

end CFSG.LocalAnalysis.RankThreeTheoremC
