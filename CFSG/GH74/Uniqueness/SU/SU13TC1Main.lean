module

public import CFSG.GH74.Uniqueness.SU.SU13TB1Main
public import CFSG.GH74.Uniqueness.SU.SU13TB2Ord
public import CFSG.GH74.Uniqueness.SU.SU13Data9

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

variable {G : Type} [Group G] [Finite G]

theorem not_mem_oc_of_involution {X : Subgroup G} {w : G} (hw : orderOf w = 2) : w ∉ oc X := by
  intro h
  have h3 := orderOf_dvd_natCard (⟨w, h⟩ : oc X)
  rw [Subgroup.orderOf_mk, hw] at h3
  exact (Nat.not_even_iff_odd.mpr (odd_card_oc X)) (even_iff_two_dvd.mpr h3)

theorem lemma232_core [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) {z : G} (hz : orderOf z = 2)
    (e : Elts G z) (f : FPart z e) (p3 : P3Part z e) :
    (∀ g : G, g * e.s₁ = e.s₁ * g → ∃ c k : G, c * e.s₁ = e.s₁ * c ∧ c * z = z * c ∧
      k ∈ oc (centralizer ({e.s₁} : Set G)) ∧ g = c * k) ∧
    ¬ GConj e.s₁ e.s₂ ∧ ¬ GConj e.s₁ e.s₃ ∧ ¬ GConj e.s₂ e.s₃ ∧
    (∃ k : G, k * e.s₂ = e.s₂ * k ∧ k * z * k⁻¹ = e.t) ∧
    (∃ k : G, k * e.s₂ = e.s₂ * k ∧ k * z * k⁻¹ = e.t * z) := by
  have hq : IsSylowIn (centralizer ({e.s₁} : Set G)) f.T₁ :=
    isSylowIn_of_unique_involution f.T₁_syl f.T₁_z hz f.T₁_uniq
  have hz1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hz; exact absurd hz (by norm_num)
  have hz2 : z * z = 1 := by rw [← pow_two]; exact sq_eq_one_of_orderOf_eq_two hz
  have hcard1 : 2 < Nat.card f.T₁ := by
    obtain ⟨k, hk, ⟨φ⟩⟩ := f.T₁_quat
    have : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
    rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  have hu3 : ∀ y ∈ zpowers z, orderOf y = 2 → y = z := by
    rintro y ⟨n, rfl⟩ hy
    beta_reduce at hy ⊢
    have h1 : z ^ n = z ^ (n % (orderOf z : ℤ)) := (zpow_mod_orderOf z n).symm
    rw [hz] at h1
    have h2 : n % ((2 : ℕ) : ℤ) = 0 ∨ n % ((2 : ℕ) : ℤ) = 1 := by omega
    rcases h2 with h2 | h2
    · rw [h1, h2, zpow_zero, orderOf_one] at hy
      exact absurd hy (by norm_num)
    · rw [h1, h2, zpow_one]
  have h3 : IsSylowIn (centralizer ({e.s₃} : Set G)) (zpowers z) :=
    isSylowIn_of_unique_involution p3.syl (mem_zpowers z) hz hu3
  have hcard3 : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, hz]
  have hbs := eq_oc_mul_centralizer_of_quaternion hz hq f.T₁_z f.T₁_quat
  have hd := not_gconj_of_sylow (s₁ := e.s₁) (s₂ := e.s₂) (s₃ := e.s₃) (z := z) (t := e.t) hq f.T₁_uniq
    hcard1 h3 hu3 hcard3 e.s₂_comm.symm e.t_s₂ hz e.t_ord e.t_ne.symm e.t_comm.symm
  have hne12 : ¬ GConj e.s₂ e.s₁ := fun h => hd.1 h.symm
  have hne23 : ¬ GConj e.s₂ e.s₃ := hd.2.2
  have hk₁ : ∃ k : G, k * e.s₂ = e.s₂ * k ∧ k * z * k⁻¹ = e.t :=
    exists_centralizer_conj hz inferInstance hnab e.class3 e.class2 hne12 hne23 e.s₂_ord e.t_comm e.t_ord
      e.t_ne e.t_s₂
  have htz2 : orderOf (e.t * z) = 2 :=
    orderOf_mul_eq_two_of_commute e.t_ord hz e.t_comm e.t_ne
  have ht1 : e.t ≠ 1 := by
    intro h; have := e.t_ord; rw [h, orderOf_one] at this; exact absurd this (by norm_num)
  have hw : e.t * z * z = z * (e.t * z) := by
    calc e.t * z * z = e.t * (z * z) := by group
      _ = e.t := by rw [hz2, mul_one]
      _ = z * (e.t * z) := by rw [← mul_assoc, ← e.t_comm, mul_assoc, hz2, mul_one]
  have hws : e.t * z * e.s₂ = e.s₂ * (e.t * z) := by
    calc e.t * z * e.s₂ = e.t * (z * e.s₂) := by group
      _ = e.t * (e.s₂ * z) := by rw [← e.s₂_comm]
      _ = (e.t * e.s₂) * z := by group
      _ = (e.s₂ * e.t) * z := by rw [e.t_s₂]
      _ = e.s₂ * (e.t * z) := by group
  have hk₂ : ∃ k : G, k * e.s₂ = e.s₂ * k ∧ k * z * k⁻¹ = e.t * z :=
    exists_centralizer_conj hz inferInstance hnab e.class3 e.class2 hne12 hne23 e.s₂_ord hw htz2
      (fun h => ht1 (by simpa using h)) hws
  refine ⟨?_, hd.1, hd.2.1, hd.2.2, hk₁, hk₂⟩
  intro g hg
  obtain ⟨c, hc, k, hk, hgck⟩ := hbs g (mem_centralizer_singleton_iff.mpr hg)
  obtain ⟨hcX, hcz⟩ := mem_inf.mp hc
  exact ⟨c, k, mem_centralizer_singleton_iff.mp hcX, mem_centralizer_singleton_iff.mp hcz, hk, hgck⟩

theorem involutions_cent_t {M T : Subgroup G} {z t : G} (hz : orderOf z = 2) (ht : orderOf t = 2)
    (htz : t ≠ z) (hcomm : t * z = z * t) (hTM : T ≤ M) (hzc : ∀ m ∈ M, m * z = z * m)
    (hT4 : Nat.card T = 4) (hTmem : ∀ x ∈ T, x = t * z ∨ x = t ∨ x = z ∨ x = 1)
    (hcard : Nat.card (Mbar M) = 4)
    {w : G} (hwM : w ∈ M) (hw2 : orderOf w = 2) (hwt : w * t = t * w) :
    w = z ∨ w = t ∨ w = t * z := by
  have htz2 : orderOf (t * z) = 2 := orderOf_mul_eq_two_of_commute ht hz hcomm htz
  have hz2 : z * z = 1 := by rw [← pow_two]; exact sq_eq_one_of_orderOf_eq_two hz
  have ht2 : t * t = 1 := by rw [← pow_two]; exact sq_eq_one_of_orderOf_eq_two ht
  have htz2' : (t * z) * (t * z) = 1 := by rw [← pow_two]; exact sq_eq_one_of_orderOf_eq_two htz2
  have hw2' : w * w = 1 := by rw [← pow_two]; exact sq_eq_one_of_orderOf_eq_two hw2
  have hwz : w * z = z * w := hzc w hwM
  have hker : ∀ τ : ↥T, proj M (Subgroup.inclusion hTM τ) = 1 → τ = 1 := by
    intro τ hτ
    have h1 : (Subgroup.inclusion hTM τ) ∈ pPrimeCore 2 ↥M := by rw [← ker_proj M]; exact hτ
    have h2 : (τ : G) ∈ oc M := mem_oc.mpr ⟨hTM τ.2, h1⟩
    rcases hTmem _ τ.2 with h | h | h | h
    · exact absurd h2 (h ▸ not_mem_oc_of_involution htz2)
    · exact absurd h2 (h ▸ not_mem_oc_of_involution ht)
    · exact absurd h2 (h ▸ not_mem_oc_of_involution hz)
    · exact Subtype.ext h
  let ψ : ↥T →* Mbar M := (proj M).comp (Subgroup.inclusion hTM)
  have hψinj : Function.Injective ψ := (injective_iff_map_eq_one ψ).mpr hker
  have hψbij : Function.Bijective ψ := hψinj.bijective_of_nat_card_le (by rw [hcard, hT4])
  obtain ⟨τ, hτ⟩ := hψbij.2 (proj M ⟨w, hwM⟩)
  have hτM : (τ : G) ∈ M := hTM τ.2
  have hq : (τ : G)⁻¹ * w ∈ oc M := by
    have hmem : (⟨(τ : G)⁻¹ * w, M.mul_mem (M.inv_mem hτM) hwM⟩ : ↥M) ∈ (proj M).ker := by
      rw [MonoidHom.mem_ker]
      have : (⟨(τ : G)⁻¹ * w, M.mul_mem (M.inv_mem hτM) hwM⟩ : ↥M) =
          (Subgroup.inclusion hTM τ)⁻¹ * ⟨w, hwM⟩ := rfl
      rw [this, map_mul, map_inv]
      exact inv_mul_eq_one.mpr hτ
    rw [ker_proj M] at hmem
    exact mem_oc.mpr ⟨_, hmem⟩
  have hτ2 : (τ : G) * τ = 1 := by
    rcases hTmem _ τ.2 with h | h | h | h <;> rw [h]
    · exact htz2'
    · exact ht2
    · exact hz2
    · exact one_mul 1
  have hτw : (τ : G) * w = w * τ := by
    rcases hTmem _ τ.2 with h | h | h | h <;> rw [h]
    · calc t * z * w = t * (z * w) := by group
        _ = t * (w * z) := by rw [hwz]
        _ = (t * w) * z := by group
        _ = (w * t) * z := by rw [hwt]
        _ = w * (t * z) := by group
    · exact hwt.symm
    · exact hwz.symm
    · simp
  have he : (τ : G)⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ2
  have hsq : ((τ : G)⁻¹ * w) * ((τ : G)⁻¹ * w) = 1 := by
    rw [he]
    calc (τ : G) * w * ((τ : G) * w) = (τ : G) * ((w * τ) * w) := by group
      _ = (τ : G) * ((τ * w) * w) := by rw [hτw]
      _ = (τ * τ) * (w * w) := by group
      _ = 1 := by rw [hτ2, hw2', mul_one]
  have h1 := eq_one_of_mem_oc_of_sq hq hsq
  rw [he] at h1
  have hwτ : w = τ := by
    calc w = τ * (τ * w) := by rw [← mul_assoc, hτ2, one_mul]
      _ = τ * 1 := by rw [h1]
      _ = τ := mul_one _
  rcases hTmem _ τ.2 with h | h | h | h
  · right; right; rw [hwτ]; exact h
  · right; left; rw [hwτ]; exact h
  · left; rw [hwτ]; exact h
  · exfalso
    rw [hwτ, h, orderOf_one] at hw2
    exact absurd hw2 (by norm_num)

theorem lemma232_nine [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) {z : G} (hz : orderOf z = 2)
    (e : Elts G z) (f : FPart z e) (p3 : P3Part z e) {E : Subgroup G} (hm : MPart9 z e E) :
    Lem232 z e := by
  obtain ⟨ha, hd12, hd13, hd23, hk₁, hk₂⟩ := lemma232_core hnab hz e f p3
  set C : Subgroup G := centralizer ({e.s₂} : Set G) with hC
  set M : Subgroup G := C ⊓ centralizer ({z} : Set G) with hM
  have hMC : M ≤ C := inf_le_left
  have hzC : z ∈ C := mem_centralizer_singleton_iff.mpr e.s₂_comm.symm
  have htC : e.t ∈ C := mem_centralizer_singleton_iff.mpr e.t_s₂
  have hzM : z ∈ M := mem_inf.mpr ⟨hzC, mem_centralizer_singleton_iff.mpr rfl⟩
  have htM : e.t ∈ M := mem_inf.mpr ⟨htC, mem_centralizer_singleton_iff.mpr e.t_comm⟩
  have hzc : ∀ m ∈ M, m * z = z * m := fun m hm' => mem_centralizer_singleton_iff.mp (mem_inf.mp hm').2
  have hz1 : z ≠ 1 := by
    intro h; rw [h, orderOf_one] at hz; exact absurd hz (by norm_num)
  have ht1 : e.t ≠ 1 := by
    intro h; have := e.t_ord; rw [h, orderOf_one] at this; exact absurd this (by norm_num)
  have ht_sq : e.t * e.t = 1 := by rw [← pow_two]; exact sq_eq_one_of_orderOf_eq_two e.t_ord
  have hz_sq : z * z = 1 := by rw [← pow_two]; exact sq_eq_one_of_orderOf_eq_two hz
  have hcomm : Commute e.t z := e.t_comm
  let T : Subgroup G := CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions e.t z ht_sq hz_sq hcomm
  have hTk : IsKleinFour T :=
    CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions e.t z ht_sq hz_sq ht1 hz1
      e.t_ne hcomm
  have hTmem : ∀ x ∈ T, x = e.t * z ∨ x = e.t ∨ x = z ∨ x = 1 := by
    intro x hx
    have : x ∈ ({e.t * z, e.t, z, 1} : Set G) := hx
    simpa using this
  have htT : e.t ∈ T := by
    show e.t ∈ ({e.t * z, e.t, z, 1} : Set G)
    simp
  have hzT : z ∈ T := by
    show z ∈ ({e.t * z, e.t, z, 1} : Set G)
    simp
  have hTM : T ≤ M := by
    intro x hx
    rcases hTmem x hx with rfl | rfl | rfl | rfl
    · exact M.mul_mem htM hzM
    · exact htM
    · exact hzM
    · exact M.one_mem
  have hTC : T ≤ C := hTM.trans hMC
  have hT4 : Nat.card T = 4 := hTk.card_four
  have hTp : IsPGroup 2 T := IsPGroup.of_card (n := 2) (by rw [hT4]; norm_num)
  have hTz : ∀ r ∈ T, r * z = z * r := fun r hr => hzc r (hTM hr)
  obtain ⟨κ⟩ := hm.kl
  have hcard4 : Nat.card (Mbar M) = 4 := by
    rw [Nat.card_congr κ.toEquiv]; simp
  obtain ⟨R', hR'C, hTR'⟩ := exists_isSylowIn_ge hTC hTp
  have hR'ne : R' ≠ ⊥ := by
    intro h
    have : z ∈ R' := hTR' hzT
    rw [h, mem_bot] at this
    exact hz1 this
  obtain ⟨w, hwR', hww, hw1, hwc⟩ := exists_central_involution hR'C.isPGroup hR'ne
  have hw2 : orderOf w = 2 := by
    refine orderOf_eq_prime ?_ hw1
    rw [pow_two]; exact hww
  have hwz : w * z = z * w := (hwc z (hTR' hzT)).symm
  have hwt : w * e.t = e.t * w := (hwc e.t (hTR' htT)).symm
  have hwC : w ∈ C := hR'C.1 hwR'
  have hwM : w ∈ M := mem_inf.mpr ⟨hwC, mem_centralizer_singleton_iff.mpr hwz⟩
  have hwcases := involutions_cent_t hz e.t_ord e.t_ne hcomm.eq hTM hzc hT4 hTmem hcard4 hwM hw2 hwt
  obtain ⟨k, hkC, hkw⟩ : ∃ k ∈ C, k * z * k⁻¹ = w := by
    rcases hwcases with h | h | h
    · exact ⟨1, C.one_mem, by rw [h]; group⟩
    · obtain ⟨k, hk, hkz⟩ := hk₁
      exact ⟨k, mem_centralizer_singleton_iff.mpr hk, by rw [hkz, h]⟩
    · obtain ⟨k, hk, hkz⟩ := hk₂
      exact ⟨k, mem_centralizer_singleton_iff.mpr hk, by rw [hkz, h]⟩
  have hR'M : R' ≤ C ⊓ centralizer ({k * z * k⁻¹} : Set G) := by
    intro r hr
    refine mem_inf.mpr ⟨hR'C.1 hr, ?_⟩
    rw [hkw, mem_centralizer_singleton_iff]
    exact hwc r hr
  have hcardM : Nat.card (C ⊓ centralizer ({k * z * k⁻¹} : Set G) : Subgroup G) = 108 := by
    rw [card_inf_centralizer_conj (le_normalizer hkC) z]
    exact hm.card
  have hdvd : Nat.card R' ∣ 108 := hcardM ▸ Subgroup.card_dvd_of_le hR'M
  obtain ⟨a, hRa⟩ := (IsPGroup.iff_card (p := 2)).mp hR'C.isPGroup
  have hale : a ≤ 2 := by
    by_contra hlt
    have h8 : 2 ^ 3 ∣ Nat.card R' := hRa ▸ pow_dvd_pow 2 (by omega)
    have := h8.trans hdvd
    norm_num at this
  have hR'le : Nat.card R' ≤ Nat.card T := by
    rw [hRa, hT4]
    calc 2 ^ a ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hale
      _ = 4 := by norm_num
  have hTR : R' = T := (Subgroup.eq_of_le_of_card_ge hTR' hR'le).symm
  have hTsyl : IsSylowIn C T := hTR ▸ hR'C
  have cl : ∀ u : G, u * e.s₂ = e.s₂ * u → orderOf u = 2 →
      ∃ c : G, c * e.s₂ = e.s₂ * c ∧ c * u * c⁻¹ = z := by
    intro u hu hu2
    have huC : u ∈ C := mem_centralizer_singleton_iff.mpr hu
    have hK : zpowers u ≤ C := (zpowers_le).mpr huC
    have hKp : IsPGroup 2 (zpowers u) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu2]; norm_num)
    obtain ⟨c₀, hc₀C, hc₀⟩ := hTsyl.exists_conj_le hK hKp
    have hu'T : c₀⁻¹ * u * c₀ ∈ T :=
      hc₀ (mem_conjSub.mpr (by simp [mul_assoc]))
    have hu'2 : orderOf (c₀⁻¹ * u * c₀) = 2 := by
      have := orderOf_conj_eq (a := u) c₀⁻¹
      rw [inv_inv] at this
      rw [this]; exact hu2
    rcases hTmem _ hu'T with h | h | h | h
    · obtain ⟨k, hkC, hk⟩ := hk₂
      have hkC' : k ∈ C := mem_centralizer_singleton_iff.mpr hkC
      refine ⟨k⁻¹ * c₀⁻¹, mem_centralizer_singleton_iff.mp (C.mul_mem (C.inv_mem hkC') (C.inv_mem hc₀C)), ?_⟩
      calc k⁻¹ * c₀⁻¹ * u * (k⁻¹ * c₀⁻¹)⁻¹ = k⁻¹ * (c₀⁻¹ * u * c₀) * k := by group
        _ = k⁻¹ * (e.t * z) * k := by rw [h]
        _ = z := by rw [← hk]; group
    · obtain ⟨k, hkC, hk⟩ := hk₁
      have hkC' : k ∈ C := mem_centralizer_singleton_iff.mpr hkC
      refine ⟨k⁻¹ * c₀⁻¹, mem_centralizer_singleton_iff.mp (C.mul_mem (C.inv_mem hkC') (C.inv_mem hc₀C)), ?_⟩
      calc k⁻¹ * c₀⁻¹ * u * (k⁻¹ * c₀⁻¹)⁻¹ = k⁻¹ * (c₀⁻¹ * u * c₀) * k := by group
        _ = k⁻¹ * e.t * k := by rw [h]
        _ = z := by rw [← hk]; group
    · refine ⟨c₀⁻¹, mem_centralizer_singleton_iff.mp (C.inv_mem hc₀C), ?_⟩
      simpa using h
    · rw [h, orderOf_one] at hu'2
      exact absurd hu'2 (by norm_num)
  have hone : ∀ u v : G, u * e.s₂ = e.s₂ * u → v * e.s₂ = e.s₂ * v → orderOf u = 2 → orderOf v = 2 →
      ∃ c : G, c * e.s₂ = e.s₂ * c ∧ c * u * c⁻¹ = v := by
    intro u v hu hv hu2 hv2
    obtain ⟨cu, hcu, hzu⟩ := cl u hu hu2
    obtain ⟨cv, hcv, hzv⟩ := cl v hv hv2
    refine ⟨cv⁻¹ * cu, ?_, ?_⟩
    · have hcvinv : cv⁻¹ * e.s₂ = e.s₂ * cv⁻¹ := (Commute.inv_left (show Commute cv e.s₂ from hcv)).eq
      calc cv⁻¹ * cu * e.s₂ = cv⁻¹ * (cu * e.s₂) := by group
        _ = cv⁻¹ * (e.s₂ * cu) := by rw [hcu]
        _ = (cv⁻¹ * e.s₂) * cu := by group
        _ = (e.s₂ * cv⁻¹) * cu := by rw [hcvinv]
        _ = e.s₂ * (cv⁻¹ * cu) := by group
    · calc cv⁻¹ * cu * u * (cv⁻¹ * cu)⁻¹ = cv⁻¹ * (cu * u * cu⁻¹) * cv := by group
        _ = cv⁻¹ * z * cv := by rw [hzu]
        _ = v := by rw [← hzv]; group
  exact ⟨ha, hd12, hd13, hd23, hk₁, hk₂, ⟨T, hTsyl, hzT, hTz⟩, hone⟩

end CFSG.GH74.Uniqueness.SU.SU13
