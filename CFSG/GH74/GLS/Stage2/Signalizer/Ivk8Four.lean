module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Cbar
public import CFSG.GH74.GLS.SP.Local.SPLAltCoverC
public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.GlueLib

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.Uniqueness.SU.SU13.TA Equiv Equiv.Perm

section Cover

variable {K : Type} [Group K] {n : ℕ} {π : K →* alternatingGroup (Fin n)}

theorem perm_no_prime_cent {m : ℕ} (hn8 : 8 ≤ m) (hn11 : m ≤ 11) {w y : Perm (Fin m)}
    (hw : w.cycleType = {2, 2, 2, 2}) (hy : y ∈ centralizer ({w} : Set (Perm (Fin m))))
    {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hyord : orderOf y = r) : False := by
  have hdvd : r ∣ Nat.card ↥(centralizer ({w} : Set (Perm (Fin m)))) := by
    rw [← hyord]
    exact Subgroup.orderOf_dvd_natCard _ hy
  rw [CFSG.GH74.GLS.SP.Local.altCover_card_centralizer_cycleType w hw] at hdvd
  have h2304 : r ∣ 2 ^ 8 * 3 ^ 2 := by
    have := hdvd.trans (CFSG.GH74.GLS.SP.Local.altCover_factorial_mul_dvd hn8 hn11)
    norm_num at this ⊢
    exact this
  rcases (Nat.Prime.dvd_mul hr).1 h2304 with h | h
  · have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h)
    omega
  · have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 (hr.dvd_of_dvd_pow h)
    omega

theorem cover_cent_pow (hπ : TwoCover π) (hn8 : 8 ≤ n) (hn11 : n ≤ 11) {a b : K}
    (ha : orderOf a = 2) (haK : a ∉ π.ker) (hab : a * b = b * a) {r : ℕ} (hr : r.Prime)
    (h5 : 5 ≤ r) {k : ℕ} (hb : b ^ (r ^ k) = 1) : b = 1 := by
  by_contra hb1
  have hr2 : Nat.Coprime 2 (r ^ k) :=
    ((Nat.coprime_primes Nat.prime_two hr).2 (by omega)).pow_right k
  have hbk : b ∉ π.ker := by
    intro hk
    have h2 : orderOf b ∣ Nat.gcd 2 (r ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (hπ.sq_eq_one_of_mem_ker' hk))
        (orderOf_dvd_of_pow_eq_one hb)
    rw [hr2] at h2
    exact hb1 (orderOf_eq_one_iff.1 (Nat.dvd_one.1 h2))
  have hπb : (π b) ^ (r ^ k) = 1 := by rw [← map_pow, hb, map_one]
  have hπb1 : π b ≠ 1 := fun h => hbk h
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hr).1 (orderOf_dvd_of_pow_eq_one hπb)
  have hj1 : 1 ≤ j := by
    by_contra h0
    have : j = 0 := by omega
    rw [this, pow_zero] at hj
    exact hπb1 (orderOf_eq_one_iff.1 hj)
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hyord : orderOf ((π b) ^ (r ^ i)) = r := by
    rw [orderOf_pow' _ (pow_ne_zero _ hr.ne_zero), hj, pow_succ,
      Nat.gcd_eq_right (Dvd.intro _ rfl), mul_comm, Nat.mul_div_cancel _ (pow_pos hr.pos i)]
  let w : Perm (Fin n) := ((π a : alternatingGroup (Fin n)) : Perm (Fin n))
  let y : Perm (Fin n) := (((π b) ^ (r ^ i) : alternatingGroup (Fin n)) : Perm (Fin n))
  have hw : w.cycleType = {2, 2, 2, 2} := hπ.cycleType_of_orderOf_eq_two hn8 hn11 ha haK
  have hy : y ∈ centralizer ({w} : Set (Perm (Fin n))) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h : Commute (π a) ((π b) ^ (r ^ i)) := by
      refine Commute.pow_right ?_ _
      show π a * π b = π b * π a
      rw [← map_mul, ← map_mul, hab]
    have h' := congrArg (fun k : alternatingGroup (Fin n) => (k : Perm (Fin n))) h.eq
    simpa [w, y] using h'.symm
  exact perm_no_prime_cent hn8 hn11 hw hy hr h5
    (by rw [show orderOf y = orderOf ((π b) ^ (r ^ i)) from Subgroup.orderOf_coe _, hyord])

end Cover

section Main

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem oddCore_orderOf_odd {y : G} (hy : y ∈ OddCore z) : Odd (orderOf y) :=
  (oddCore_odd_card z).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hy)

theorem not_mem_oddCore_of_orderOf_eq_two {y : G} (hy : orderOf y = 2) : y ∉ OddCore z := by
  intro h
  have := oddCore_orderOf_odd h
  rw [hy] at this
  exact absurd this (by decide)

theorem four_cent_pow (hctx : Stage2Ctx G z Kind.ly S) {U : Subgroup G}
    (hU : IVK.IsFourSubgroup U) {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) {x : G}
    (hx : x ∈ centralizer (U : Set G)) {k : ℕ} (hxr : x ^ (r ^ k) = 1) :
    x ∈ pPrimeCoreOf 2 (centralizer (U : Set G)) := by
  obtain ⟨hUe, hU4⟩ := hU
  have := hUe
  have hsq : ∀ a ∈ U, a ^ 2 = 1 := fun a ha => elemPow_eq_one_of_isElementaryAbelian a ha
  have hcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥U)).comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hUne : U ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hU4
    omega
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hUne
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hu2 : orderOf u = 2 := orderOf_eq_prime (hsq u hu) hu1'
  obtain ⟨v, hv, hvu⟩ : ∃ v ∈ U, v ∉ zpowers u := by
    by_contra h
    push Not at h
    have hle : U ≤ zpowers u := fun v hv => h v hv
    have := Subgroup.card_le_of_le hle
    rw [hU4, Nat.card_zpowers, hu2] at this
    omega
  have hv1 : v ≠ 1 := fun h => hvu (h ▸ one_mem _)
  have hvu' : v ≠ u := fun h => hvu (h ▸ mem_zpowers u)
  obtain ⟨n', -, hsp⟩ := ly_sporadic hctx
  obtain ⟨c, hc⟩ := isConj_iff.mp (hsp.one_class u z hu2 hctx.central.1)
  have hz2 : z ^ 2 = 1 := by rw [← hctx.central.1]; exact pow_orderOf_eq_one z
  have hxu : x ∈ centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (hx u hu).symm
  have hvu2 : v ∈ centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (hcomm u hu v hv).symm
  have hx'C : c * x * c⁻¹ ∈ Cen z := by
    have := conj_mem_centralizer (c := c) hxu
    rwa [hc] at this
  have hv'C : c * v * c⁻¹ ∈ Cen z := by
    have := conj_mem_centralizer (c := c) hvu2
    rwa [hc] at this
  have hxv : c * x * c⁻¹ * (c * v * c⁻¹) = c * v * c⁻¹ * (c * x * c⁻¹) := by
    have h : v * x = x * v := hx v hv
    calc c * x * c⁻¹ * (c * v * c⁻¹) = c * (x * v) * c⁻¹ := by group
      _ = c * (v * x) * c⁻¹ := by rw [h]
      _ = c * v * c⁻¹ * (c * x * c⁻¹) := by group
  have hv'2 : (c * v * c⁻¹) ^ 2 = 1 := by rw [conj_pow, hsq v hv]; group
  have hv'ord : orderOf (c * v * c⁻¹) = 2 := by
    refine orderOf_eq_prime hv'2 ?_
    intro h
    exact hv1 (by simpa using h)
  have hv'z : c * v * c⁻¹ ≠ z := by
    intro h
    rw [← hc] at h
    exact hvu' (by simpa using h)
  have hx'r : (c * x * c⁻¹) ^ (r ^ k) = 1 := by
    rw [conj_pow, hxr]; group
  obtain ⟨m, hm, π, hπ, hker⟩ := cbar_twoCover hctx
  let a : CentralizerBar z := toBar z ⟨c * v * c⁻¹, hv'C⟩
  let b : CentralizerBar z := toBar z ⟨c * x * c⁻¹, hx'C⟩
  have hmem : ∀ y : ↥(Cen z), toBar z y = 1 → (y : G) ∈ OddCore z := fun y hy =>
    ⟨y, (QuotientGroup.eq_one_iff _).1 hy, rfl⟩
  have ha2 : a ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨c * v * c⁻¹, hv'C⟩ : ↥(Cen z)) ^ 2 = 1 := Subtype.ext (by simpa using hv'2)
    rw [this, map_one]
  have ha1 : a ≠ 1 := fun h =>
    not_mem_oddCore_of_orderOf_eq_two hv'ord (hmem _ h)
  have ha_ord : orderOf a = 2 := orderOf_eq_prime ha2 ha1
  have hzC : z ∈ Cen z := Subgroup.mem_centralizer_singleton_iff.2 rfl
  let zb : CentralizerBar z := toBar z ⟨z, hzC⟩
  have hzb_center : zb ∈ center (CentralizerBar z) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective _ g
    show toBar z g' * toBar z ⟨z, hzC⟩ = toBar z ⟨z, hzC⟩ * toBar z g'
    rw [← map_mul, ← map_mul]
    exact congrArg (toBar z) (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 g'.2))
  have hzb1 : zb ≠ 1 := fun h =>
    not_mem_oddCore_of_orderOf_eq_two (hctx.central.1) (hmem _ h)
  have hzbk : zb ∈ π.ker := by rw [hker]; exact hzb_center
  have haK : a ∉ π.ker := by
    intro hak
    obtain ⟨e0, he01, he0u⟩ := (Nat.card_eq_two_iff' (1 : π.ker)).mp hπ.card_ker
    have h1 : (⟨a, hak⟩ : π.ker) = e0 := he0u _ (fun h => ha1 (congrArg Subtype.val h))
    have h2 : (⟨zb, hzbk⟩ : π.ker) = e0 := he0u _ (fun h => hzb1 (congrArg Subtype.val h))
    have h3 : a = zb := congrArg Subtype.val (h1.trans h2.symm)
    have h4 : (⟨c * v * c⁻¹, hv'C⟩ : ↥(Cen z))⁻¹ * ⟨z, hzC⟩ ∈ pPrimeCore 2 ↥(Cen z) :=
      QuotientGroup.eq.1 h3
    have h5 : (c * v * c⁻¹)⁻¹ * z ∈ OddCore z := ⟨_, h4, rfl⟩
    have hcm : Commute (c * v * c⁻¹) z := Subgroup.mem_centralizer_singleton_iff.1 hv'C
    have h6 : ((c * v * c⁻¹)⁻¹ * z) ^ 2 = 1 := by
      rw [hcm.inv_left.mul_pow, inv_pow, hv'2, hz2]
      simp
    have h7 : orderOf ((c * v * c⁻¹)⁻¹ * z) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h6) with h | h
      · exact h
      · have := oddCore_orderOf_odd h5
        rw [h] at this
        exact absurd this (by decide)
    have h8 : (c * v * c⁻¹)⁻¹ * z = 1 := orderOf_eq_one_iff.1 h7
    exact hv'z (inv_mul_eq_one.1 h8)
  have hab : a * b = b * a := by
    show toBar z _ * toBar z _ = toBar z _ * toBar z _
    rw [← map_mul, ← map_mul]
    exact congrArg (toBar z) (Subtype.ext hxv.symm)
  have hbr : b ^ (r ^ k) = 1 := by
    rw [← map_pow]
    have : (⟨c * x * c⁻¹, hx'C⟩ : ↥(Cen z)) ^ (r ^ k) = 1 := Subtype.ext (by simpa using hx'r)
    rw [this, map_one]
  have hm8 : 8 ≤ m ∧ m ≤ 11 := by omega
  have hb1 : b = 1 := cover_cent_pow hπ hm8.1 hm8.2 ha_ord haK hab hr h5 hbr
  have hx'O : c * x * c⁻¹ ∈ OddCore z := hmem _ hb1
  have hHle : centralizer (U : Set G) ≤ centralizer ({u} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 hu)
  have hN := CFSG.GH74.GLS.Stage1.Thm3.Sec4.le_pPrimeCoreOf' (X := centralizer (U : Set G))
    (N := oddPart c z (centralizer (U : Set G))) inf_le_left (oddPart_norm hc hHle)
    (oddPart_odd c z _)
  exact hN ⟨hx, hx'O⟩

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
