module

public import CFSG.GroupTheory.SevenInvolutionWreathLawGraph

public section

namespace CFSG.GroupTheory.SevenInvolutionWreathLaw

variable {K : Type*} [Group K]

theorem involutionProductLaw_of_conj
    (hconj : ∀ u v : K, orderOf u = 2 → orderOf v = 2 → IsConj u v) {x : K} (hx : orderOf x = 2)
    (hlawx : ∀ u v : K, orderOf u = 2 → orderOf v = 2 → u ∈ Subgroup.centralizer {x} →
      v ∈ Subgroup.centralizer {x} → u ≠ v → u ≠ x → v ≠ x →
      (u * v = v * u → u * v = x) ∧ (u * v ≠ v * u → (u * v) ^ 2 = x)) :
    InvolutionProductLaw K := by
  intro z u v hz hu hv huz hvz huv hu' hv'
  obtain ⟨g, hg⟩ := isConj_iff.mp (hconj x z hx hz)
  let ψ : K ≃* K := MulAut.conj g⁻¹
  have hψ : ∀ y, ψ y = g⁻¹ * y * g := fun y => by simp [ψ]
  have hψz : ψ z = x := by rw [hψ, ← hg]; group
  have hcent : ∀ y, y ∈ Subgroup.centralizer {z} → ψ y ∈ Subgroup.centralizer {x} := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    rw [← hψz, ← map_mul, ← map_mul, hy]
  obtain ⟨h1, h2⟩ := hlawx (ψ u) (ψ v) (by rw [MulEquiv.orderOf_eq]; exact hu)
    (by rw [MulEquiv.orderOf_eq]; exact hv) (hcent u huz) (hcent v hvz)
    (fun h => huv (ψ.injective h)) (fun h => hu' (ψ.injective (h.trans hψz.symm)))
    (fun h => hv' (ψ.injective (h.trans hψz.symm)))
  refine ⟨fun hc => ψ.injective ?_, fun hc => ψ.injective ?_⟩
  · rw [map_mul, hψz]
    exact h1 (by rw [← map_mul, ← map_mul, hc])
  · rw [map_pow, map_mul, hψz]
    exact h2 fun h => hc (ψ.injective (by rw [map_mul, map_mul]; exact h))

theorem ncard_involutions_centralizer_of_conj
    (hconj : ∀ u v : K, orderOf u = 2 → orderOf v = 2 → IsConj u v) {x : K} (hx : orderOf x = 2)
    (h7 : {g : K | g ∈ Subgroup.centralizer {x} ∧ orderOf g = 2}.ncard = 7) {z : K}
    (hz : orderOf z = 2) : {g : K | g ∈ Subgroup.centralizer {z} ∧ orderOf g = 2}.ncard = 7 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (hconj x z hx hz)
  let φ : K ≃* K := MulAut.conj g
  have hφx : φ x = z := hg
  have himage : φ '' {y : K | y ∈ Subgroup.centralizer {x} ∧ orderOf y = 2} =
      {y : K | y ∈ Subgroup.centralizer {z} ∧ orderOf y = 2} := by
    ext y
    constructor
    · rintro ⟨y', ⟨hy'c, hy'o⟩, rfl⟩
      refine ⟨?_, by rw [MulEquiv.orderOf_eq]; exact hy'o⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hy'c ⊢
      rw [← hφx, ← map_mul, ← map_mul, hy'c]
    · rintro ⟨hyc, hyo⟩
      refine ⟨φ.symm y, ⟨?_, by rw [MulEquiv.orderOf_eq]; exact hyo⟩, φ.apply_symm_apply y⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hyc ⊢
      have hxz : x = φ.symm z := by rw [← hφx, MulEquiv.symm_apply_apply]
      rw [hxz, ← map_mul, ← map_mul, hyc]
  rw [← himage, Set.ncard_image_of_injective _ φ.injective, h7]

theorem local_product_law [Finite K] {s t w : K} (hst : s * t = t * s) (hs : orderOf s = 4)
    (ht : orderOf t = 4) (hinter : Subgroup.zpowers s ⊓ Subgroup.zpowers t = ⊥)
    (hw : orderOf w = 2) (hwout : w ∉ Subgroup.closure {s, t}) (hsw : w⁻¹ * s * w = t)
    (htw : w⁻¹ * t * w = s)
    (h7 : {g : K | g ∈ Subgroup.centralizer {(s * t) ^ 2} ∧ orderOf g = 2}.ncard = 7) :
    orderOf ((s * t) ^ 2) = 2 ∧
      ∀ u v : K, orderOf u = 2 → orderOf v = 2 → u ∈ Subgroup.centralizer {(s * t) ^ 2} →
        v ∈ Subgroup.centralizer {(s * t) ^ 2} → u ≠ v → u ≠ (s * t) ^ 2 → v ≠ (s * t) ^ 2 →
        (u * v = v * u → u * v = (s * t) ^ 2) ∧ (u * v ≠ v * u → (u * v) ^ 2 = (s * t) ^ 2) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set x := (s * t) ^ 2 with hxdef
  set A := Subgroup.closure ({s, t} : Set K) with hA
  have hsA : s ∈ A := Subgroup.subset_closure (Set.mem_insert _ _)
  have htA : t ∈ A := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hc : Commute s t := hst
  have hs4 : s ^ 4 = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
  have ht4 : t ^ 4 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hs2 : s ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hs]; norm_num)
  have ht2 : t ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [ht]; norm_num)
  have hinter' : ∀ g, g ∈ Subgroup.zpowers s → g ∈ Subgroup.zpowers t → g = 1 := by
    intro g hgs hgt
    have hg : g ∈ Subgroup.zpowers s ⊓ Subgroup.zpowers t := ⟨hgs, hgt⟩
    rw [hinter] at hg
    exact Subgroup.mem_bot.mp hg
  have ht2inv : (t ^ 2)⁻¹ = t ^ 2 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_add]; exact ht4)
  have hx : x = s ^ 2 * t ^ 2 := hc.mul_pow 2
  have hpq : s ^ 2 ≠ t ^ 2 := fun h => hs2 (hinter' _ (Subgroup.npow_mem_zpowers s 2)
    (h ▸ Subgroup.npow_mem_zpowers t 2))
  have hx1 : x ≠ 1 := by
    intro h
    rw [hx] at h
    have h' : s ^ 2 = (t ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [ht2inv] at h'
    exact hpq h'
  have hpx : s ^ 2 ≠ x := by
    intro h
    rw [hx] at h
    exact ht2 (mul_left_cancel (a := s ^ 2) (by rw [mul_one]; exact h)).symm
  have hqx : t ^ 2 ≠ x := by
    intro h
    rw [hx] at h
    exact hs2 (mul_right_cancel (b := t ^ 2) (by rw [one_mul]; exact h)).symm
  have hx2 : x ^ 2 = 1 := by
    rw [hx, (hc.pow_pow 2 2).mul_pow, ← pow_mul, ← pow_mul]
    norm_num [hs4, ht4]
  have hxord : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  have hpord : orderOf (s ^ 2) = 2 :=
    orderOf_eq_prime (by rw [← pow_mul]; norm_num [hs4]) hs2
  have hqord : orderOf (t ^ 2) = 2 :=
    orderOf_eq_prime (by rw [← pow_mul]; norm_num [ht4]) ht2
  have hpqc : s ^ 2 * t ^ 2 = t ^ 2 * s ^ 2 := (hc.pow_pow 2 2).eq
  have hpxc : s ^ 2 * x = x * s ^ 2 := by
    rw [hx]
    exact ((Commute.refl (s ^ 2)).mul_right (hc.pow_pow 2 2)).eq
  have hqxc : t ^ 2 * x = x * t ^ 2 := by
    rw [hx]
    exact (((hc.pow_pow 2 2).symm).mul_right (Commute.refl (t ^ 2))).eq
  set r := s * t⁻¹ with hr
  have hrA : r ∈ A := A.mul_mem hsA (A.inv_mem htA)
  have hr2 : r ^ 2 = x := by
    rw [hr, hc.inv_right.mul_pow, inv_pow, ht2inv, hx]
  have hr4 : r ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hr2, hx2]
  have hrord : orderOf r = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := r)
      (by rw [pow_one, hr2]; exact hx1) (by norm_num [hr4])
    rw [h]
    norm_num
  have hcrt : Commute r t := hc.mul_left (Commute.refl t).inv_left
  have hcrs : Commute r s := (Commute.refl s).mul_left hc.symm.inv_left
  have hrq : ∀ j : ℤ, r ^ j * t ^ 2 = t ^ 2 * r ^ j := fun j => ((hcrt.zpow_left j).pow_right 2).eq
  have hrp : ∀ j : ℤ, r ^ j * s ^ 2 = s ^ 2 * r ^ j := fun j => ((hcrs.zpow_left j).pow_right 2).eq
  have hrx : ∀ j : ℤ, r ^ j * x = x * r ^ j := fun j => by
    rw [← hr2]
    exact (((Commute.refl r).zpow_left j).pow_right 2).eq
  have hww : w * w = 1 := mul_self_of_orderOf_eq_two hw
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  let φ : K ≃* K := MulAut.conj w
  have hφ : ∀ g, φ g = w * g * w := fun g => by simp [φ, MulAut.conj_apply, hwinv]
  have hφs : φ s = t := by rw [hφ, ← hsw, hwinv]
  have hφt : φ t = s := by rw [hφ, ← htw, hwinv]
  have hφr : φ r = r⁻¹ := by rw [hr, map_mul, map_inv, hφs, hφt, mul_inv_rev, inv_inv]
  have hφrz : ∀ j : ℤ, φ (r ^ j) = r ^ (-j) := fun j => by
    rw [map_zpow, hφr, inv_zpow, zpow_neg]
  have hφp : φ (s ^ 2) = t ^ 2 := by rw [map_pow, hφs]
  have hφq : φ (t ^ 2) = s ^ 2 := by rw [map_pow, hφt]
  have hφx : φ x = x := by rw [hx, map_mul, hφp, hφq, hpqc]
  have hw_mul : ∀ g h : K, g * w * (h * w) = g * φ h := fun g h => by rw [hφ]; group
  have hwx : w * x = x * w := by
    have h := hφx
    rw [hφ] at h
    calc w * x = w * x * (w * w) := by rw [hww, mul_one]
      _ = (w * x * w) * w := by group
      _ = x * w := by rw [h]
  set d : ℤ → K := fun j => r ^ j * w with hd
  have hdd : ∀ j k : ℤ, d j * d k = r ^ (j - k) := fun j k => by
    simp only [hd]
    rw [hw_mul, hφrz, ← zpow_add, sub_eq_add_neg]
  have hdsq : ∀ j, d j * d j = 1 := fun j => by rw [hdd, sub_self, zpow_zero]
  have hdA : ∀ j, d j ∉ A := fun j hj => hwout (by
    have hwj : w = (r ^ j)⁻¹ * d j := by simp only [hd]; group
    rw [hwj]
    exact A.mul_mem (A.inv_mem (A.zpow_mem hrA j)) hj)
  have hd1 : ∀ j, d j ≠ 1 := fun j h => hdA j (h ▸ A.one_mem)
  have hdord : ∀ j, orderOf (d j) = 2 := fun j =>
    orderOf_eq_prime (by rw [sq]; exact hdsq j) (hd1 j)
  have hdx : ∀ j, d j * x = x * d j := fun j => by
    calc d j * x = r ^ j * (w * x) := by simp only [hd]; group
      _ = r ^ j * (x * w) := by rw [hwx]
      _ = (r ^ j * x) * w := by group
      _ = (x * r ^ j) * w := by rw [hrx]
      _ = x * d j := by simp only [hd]; group
  have hdp : ∀ j, d j * s ^ 2 * d j = t ^ 2 := fun j => by
    calc d j * s ^ 2 * d j = r ^ j * w * (s ^ 2 * r ^ j * w) := by simp only [hd]; group
      _ = r ^ j * φ (s ^ 2 * r ^ j) := by rw [hw_mul]
      _ = r ^ j * (t ^ 2 * r ^ (-j)) := by rw [map_mul, hφp, hφrz]
      _ = (r ^ j * t ^ 2) * r ^ (-j) := by group
      _ = t ^ 2 := by rw [hrq, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  have hdq : ∀ j, d j * t ^ 2 * d j = s ^ 2 := fun j => by
    calc d j * t ^ 2 * d j = r ^ j * w * (t ^ 2 * r ^ j * w) := by simp only [hd]; group
      _ = r ^ j * φ (t ^ 2 * r ^ j) := by rw [hw_mul]
      _ = r ^ j * (s ^ 2 * r ^ (-j)) := by rw [map_mul, hφq, hφrz]
      _ = (r ^ j * s ^ 2) * r ^ (-j) := by group
      _ = s ^ 2 := by rw [hrp, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  have hzpow : ∀ j k : ℤ, r ^ j = r ^ k ↔ j % 4 = k % 4 := fun j k => by
    rw [zpow_eq_zpow_iff_modEq, hrord]
    rfl
  have hdeq : ∀ j k : ℤ, d j = d k ↔ j % 4 = k % 4 := fun j k => by
    simp only [hd]
    rw [mul_left_inj, hzpow]
  set T := {g : K | g ∈ Subgroup.centralizer {x} ∧ orderOf g = 2} with hT
  have hmemT : ∀ g, g ∈ T ↔ g * x = x * g ∧ orderOf g = 2 := fun g => by
    simp only [hT, Set.mem_ofPred_eq, Subgroup.mem_centralizer_singleton_iff]
  set E : Finset K := ({x, s ^ 2, t ^ 2} : Finset K) ∪
    (Finset.range 4).image (fun j : ℕ => d j) with hE
  have hEsub : (E : Set K) ⊆ T := by
    intro g hg
    rw [Finset.mem_coe, hE, Finset.mem_union, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_image] at hg
    rw [hmemT]
    rcases hg with (rfl | rfl | rfl) | ⟨j, -, rfl⟩
    · exact ⟨rfl, hxord⟩
    · exact ⟨hpxc, hpord⟩
    · exact ⟨hqxc, hqord⟩
    · exact ⟨hdx j, hdord j⟩
  have hcore : ({x, s ^ 2, t ^ 2} : Finset K).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hpq
    · simpa using ⟨hpx.symm, hqx.symm⟩
  have hinj : Set.InjOn (fun j : ℕ => d j) ↑(Finset.range 4) := by
    intro j hj k hk h
    simp only [Finset.coe_range, Set.mem_Iio] at hj hk
    have h' := (hdeq j k).mp h
    omega
  have hdisj : Disjoint ({x, s ^ 2, t ^ 2} : Finset K)
      ((Finset.range 4).image fun j : ℕ => d j) := by
    rw [Finset.disjoint_left]
    intro g hg hg'
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hg'
    apply hdA j
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with h | h | h <;> rw [h]
    · rw [hx]
      exact A.mul_mem (A.pow_mem hsA 2) (A.pow_mem htA 2)
    · exact A.pow_mem hsA 2
    · exact A.pow_mem htA 2
  have hEcard : E.card = 7 := by
    rw [hE, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj,
      Finset.card_range, hcore]
  have hTE : (E : Set K) = T :=
    Set.eq_of_subset_of_ncard_le hEsub (by rw [h7, Set.ncard_coe_finset, hEcard]) (Set.toFinite T)
  have hdec : ∀ g, g ∈ T → g ≠ x → g = s ^ 2 ∨ g = t ^ 2 ∨ ∃ j : ℤ, g = d j := by
    intro g hg hgx
    rw [← hTE, Finset.mem_coe, hE, Finset.mem_union, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_image] at hg
    rcases hg with (h | h | h) | ⟨j, -, h⟩
    · exact absurd h hgx
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨j, h.symm⟩)
  have hpd : ∀ j, s ^ 2 * d j ≠ d j * s ^ 2 ∧ (s ^ 2 * d j) ^ 2 = x ∧
      (d j * s ^ 2) ^ 2 = x := fun j => by
    refine ⟨fun h => hpq ?_, ?_, ?_⟩
    · calc s ^ 2 = (d j * d j) * s ^ 2 := by rw [hdsq, one_mul]
        _ = d j * (d j * s ^ 2) := by group
        _ = d j * (s ^ 2 * d j) := by rw [h]
        _ = d j * s ^ 2 * d j := by group
        _ = t ^ 2 := hdp j
    · calc (s ^ 2 * d j) ^ 2 = s ^ 2 * (d j * s ^ 2 * d j) := by rw [sq]; group
        _ = x := by rw [hdp, hx]
    · calc (d j * s ^ 2) ^ 2 = (d j * s ^ 2 * d j) * s ^ 2 := by rw [sq]; group
        _ = x := by rw [hdp, ← hpqc, hx]
  have hqd : ∀ j, t ^ 2 * d j ≠ d j * t ^ 2 ∧ (t ^ 2 * d j) ^ 2 = x ∧
      (d j * t ^ 2) ^ 2 = x := fun j => by
    refine ⟨fun h => hpq ?_, ?_, ?_⟩
    · calc s ^ 2 = d j * t ^ 2 * d j := (hdq j).symm
        _ = d j * (t ^ 2 * d j) := by group
        _ = d j * (d j * t ^ 2) := by rw [h]
        _ = (d j * d j) * t ^ 2 := by group
        _ = t ^ 2 := by rw [hdsq, one_mul]
    · calc (t ^ 2 * d j) ^ 2 = t ^ 2 * (d j * t ^ 2 * d j) := by rw [sq]; group
        _ = x := by rw [hdq, ← hpqc, hx]
    · calc (d j * t ^ 2) ^ 2 = (d j * t ^ 2 * d j) * t ^ 2 := by rw [sq]; group
        _ = x := by rw [hdq, hx]
  have hr2z : r ^ (2 : ℤ) = x := by rw [zpow_ofNat, hr2]
  have hdd' : ∀ j k : ℤ, d j ≠ d k → (d j * d k = d k * d j → d j * d k = x) ∧
      (d j * d k ≠ d k * d j → (d j * d k) ^ 2 = x) := fun j k hjk => by
    have hjk' : ¬ j % 4 = k % 4 := fun h => hjk ((hdeq j k).mpr h)
    rw [hdd, hdd]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h' := (hzpow _ _).mp h
      rw [← hr2z, hzpow]
      omega
    · have h' : ¬ (j - k) % 4 = (k - j) % 4 := fun h' => h ((hzpow _ _).mpr h')
      rw [← zpow_natCast, ← zpow_mul, ← hr2z, hzpow]
      push_cast
      omega
  refine ⟨hxord, fun u v hu hv hux hvx huv hu' hv' => ?_⟩
  have huT : u ∈ T := (hmemT u).mpr ⟨Subgroup.mem_centralizer_singleton_iff.mp hux, hu⟩
  have hvT : v ∈ T := (hmemT v).mpr ⟨Subgroup.mem_centralizer_singleton_iff.mp hvx, hv⟩
  rcases hdec u huT hu' with rfl | rfl | ⟨j, rfl⟩ <;>
    rcases hdec v hvT hv' with rfl | rfl | ⟨k, rfl⟩
  · exact absurd rfl huv
  · exact ⟨fun _ => hx.symm, fun h => absurd hpqc h⟩
  · exact ⟨fun h => absurd h (hpd k).1, fun _ => (hpd k).2.1⟩
  · exact ⟨fun _ => by rw [← hpqc, hx], fun h => absurd hpqc.symm h⟩
  · exact absurd rfl huv
  · exact ⟨fun h => absurd h (hqd k).1, fun _ => (hqd k).2.1⟩
  · exact ⟨fun h => absurd h.symm (hpd j).1, fun _ => (hpd j).2.2⟩
  · exact ⟨fun h => absurd h.symm (hqd j).1, fun _ => (hqd j).2.2⟩
  · exact hdd' j k huv

end CFSG.GroupTheory.SevenInvolutionWreathLaw
