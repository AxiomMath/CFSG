module

public import CFSG.LargeExtraspecial.AS35CHyp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup QuadraticMap

variable {G : Type} [Group G] [Finite G]

theorem conj_eq_inv_of_fixedPointFree {N : Subgroup G} {y : G}
    (hyN : ∀ k ∈ N, y * k * y⁻¹ ∈ N) (hy2 : y * y = 1)
    (hfix : ∀ k ∈ N, k * y = y * k → k = 1) {k : G} (hk : k ∈ N) : y * k * y⁻¹ = k⁻¹ := by
  let φ : N →* N :=
    { toFun := fun a => ⟨y * a * y⁻¹, hyN a a.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  have hφ : MonoidHom.FixedPointFree φ := by
    intro a ha
    have h : y * (a : G) * y⁻¹ = a := congrArg Subtype.val ha
    apply Subtype.ext
    apply hfix a a.2
    calc (a : G) * y = y * a * y⁻¹ * y := by rw [h]
      _ = y * a := by group
  have hinv : Function.Involutive φ := by
    intro a
    apply Subtype.ext
    change y * (y * (a : G) * y⁻¹) * y⁻¹ = a
    have hy : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
    rw [hy]
    calc y * (y * (a : G) * y) * y = (y * y) * a * (y * y) := by group
      _ = a := by rw [hy2]; group
  have h := congrFun (MonoidHom.FixedPointFree.coe_eq_inv_of_involutive hφ hinv) ⟨k, hk⟩
  exact congrArg Subtype.val h

namespace Setting

variable (S : Setting G)

theorem eq_one_of_mem_M_of_odd {e : G} (he : e ∈ S.QG) {N : Subgroup G}
    (hNC : N ≤ centralizer ({e} : Set G))
    (hNn : ∀ c ∈ centralizer ({e} : Set G), ∀ k ∈ N, c * k * c⁻¹ ∈ N)
    (hodd : Odd (Nat.card N)) {a : G} (haN : a ∈ N) (haM : a ∈ S.M) : a = 1 := by
  have hae : a * e = e * a := mem_centralizer_singleton_iff.mp (hNC haN)
  have h1 : ∀ b ∈ S.QG, b * e = e * b → a * b = b * a := by
    intro b hb hbe
    have hbC : b ∈ centralizer ({e} : Set G) := mem_centralizer_singleton_iff.mpr hbe
    have hN' : a * b * a⁻¹ * b⁻¹ ∈ N := by
      have := mul_mem haN (hNn b hbC a⁻¹ (inv_mem haN))
      simpa [mul_assoc] using this
    have hQ' : a * b * a⁻¹ * b⁻¹ ∈ S.QG := mul_mem (S.conj_mem_QG haM hb) (inv_mem hb)
    have h := eq_one_of_mem_of_odd hodd S.isPGroup_QG hN' hQ'
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h, one_mul]
  have h2 : ∀ q ∈ S.QG, a * q = q * a := by
    intro q hq
    set n := a * q * a⁻¹ * q⁻¹ with hn_def
    have hnQ : n ∈ S.QG := mul_mem (S.conj_mem_QG haM hq) (inv_mem hq)
    have hne : n * e = e * n := by
      rw [← S.polar_cl_eq_zero_iff hnQ he]
      have hρq : ((S.ρ ⟨a, haM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl q) = S.cl (a * q * a⁻¹) :=
        S.ρ_cl ⟨a, haM⟩ hq
      have hae' : a * e * a⁻¹ = e := by rw [hae]; group
      have hρe : ((S.ρ ⟨a, haM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl e) = S.cl e := by
        have h := S.ρ_cl ⟨a, haM⟩ he
        rwa [show ((⟨a, haM⟩ : S.M) : G) = a from rfl, hae'] at h
      have key : polar S.q (S.cl (a * q * a⁻¹)) (S.cl e) = polar S.q (S.cl q) (S.cl e) := by
        rw [← hρq]
        conv_lhs => rw [← hρe]
        exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (S.ρ ⟨a, haM⟩).2 _ _
      rw [S.cl_mul (S.conj_mem_QG haM hq) (inv_mem hq), S.cl_inv hq, polar_add_left, key]
      exact CharTwo.add_self_eq_zero _
    have han : a * n = n * a := h1 n hnQ hne
    have hpow : ∀ k : ℕ, a ^ k * q * (a ^ k)⁻¹ = n ^ k * q := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        calc a ^ (k + 1) * q * (a ^ (k + 1))⁻¹ = a * (a ^ k * q * (a ^ k)⁻¹) * a⁻¹ := by group
          _ = a * (n ^ k * q) * a⁻¹ := by rw [ih]
          _ = n ^ k * (a * q * a⁻¹) := by
            rw [← mul_assoc a, (Commute.pow_right han k).eq]
            group
          _ = n ^ k * (n * q) := by rw [hn_def]; group
          _ = n ^ (k + 1) * q := by group
    have hk := hpow (orderOf a)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hk
    have hnk : n ^ orderOf a = 1 := mul_right_cancel (hk.symm.trans (one_mul q).symm)
    have hoa : Odd (orderOf a) := by
      have h := orderOf_dvd_natCard (⟨a, haN⟩ : N)
      rw [Subgroup.orderOf_mk] at h
      exact Odd.of_dvd_nat hodd h
    have h4 : n ^ 4 = 1 := S.pow_four_eq_one hnQ
    have hcop : Nat.Coprime (orderOf a) (2 ^ 2) := (Nat.coprime_two_right.mpr hoa).pow_right 2
    have hdvd : orderOf n ∣ 1 := hcop ▸
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hnk) (orderOf_dvd_of_pow_eq_one h4)
    have hn1 : n = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
    calc a * q = n * (q * a) := by rw [hn_def]; group
      _ = q * a := by rw [hn1, one_mul]
  exact eq_one_of_mem_of_odd hodd S.isPGroup_QG haN (S.mem_QG_of_commute haM h2)

theorem mem_M_of_commute_of_zInOTwo {e : G} (he : e ∈ S.QG) {N : Subgroup G}
    (hNn : ∀ c ∈ centralizer ({e} : Set G), ∀ k ∈ N, c * k * c⁻¹ ∈ N)
    (hodd : Odd (Nat.card N)) {y : G} (hy : S.ZInOTwo y) {k : G} (hk : k ∈ N)
    (hky : k * y = y * k) : k ∈ S.M := by
  have hzC : S.z ∈ centralizer ({e} : Set G) :=
    mem_centralizer_singleton_iff.mpr (S.z_comm_QG he).symm
  have hkC : k ∈ centralizer ({y} : Set G) := mem_centralizer_singleton_iff.mpr hky
  have h1 : k * S.z * k⁻¹ * S.z⁻¹ ∈ N := by
    have := mul_mem hk (hNn S.z hzC k⁻¹ (inv_mem hk))
    simpa [mul_assoc] using this
  have h2 : k * S.z * k⁻¹ * S.z⁻¹ ∈ oTwoCent y :=
    mul_mem (conj_mem_oTwoCent hkC hy) (inv_mem hy)
  have h := eq_one_of_mem_of_odd hodd (isPGroup_oTwoCent y) h1 h2
  rw [S.mem_M_iff]
  calc k * S.z = k * S.z * k⁻¹ * S.z⁻¹ * (S.z * k) := by group
    _ = S.z * k := by rw [h, one_mul]

theorem eq_bot_of_odd {e : G} (he : e ∈ S.QG) {N : Subgroup G}
    (hNC : N ≤ centralizer ({e} : Set G))
    (hNn : ∀ c ∈ centralizer ({e} : Set G), ∀ k ∈ N, c * k * c⁻¹ ∈ N)
    (hodd : Odd (Nat.card N)) {t : G} (hte : t * e = e * t) (ht2 : t * t = 1)
    (ht : S.ZInOTwo t) (htz : S.ZInOTwo (t * S.z)) : N = ⊥ := by
  have hzC : S.z ∈ centralizer ({e} : Set G) :=
    mem_centralizer_singleton_iff.mpr (S.z_comm_QG he).symm
  have htC : t ∈ centralizer ({e} : Set G) := mem_centralizer_singleton_iff.mpr hte
  have hfz : ∀ k ∈ N, k * S.z = S.z * k → k = 1 := fun k hk hkz =>
    S.eq_one_of_mem_M_of_odd he hNC hNn hodd hk (S.mem_M_iff.mpr hkz)
  have hft : ∀ k ∈ N, k * t = t * k → k = 1 := fun k hk hkt =>
    S.eq_one_of_mem_M_of_odd he hNC hNn hodd hk
      (S.mem_M_of_commute_of_zInOTwo he hNn hodd ht hk hkt)
  have hftz : ∀ k ∈ N, k * (t * S.z) = t * S.z * k → k = 1 := fun k hk hkt =>
    S.eq_one_of_mem_M_of_odd he hNC hNn hodd hk
      (S.mem_M_of_commute_of_zInOTwo he hNn hodd htz hk hkt)
  rw [eq_bot_iff]
  intro k hk
  rw [mem_bot]
  apply hftz k hk
  have hinvz := conj_eq_inv_of_fixedPointFree (hNn S.z hzC) S.z_mul_z hfz hk
  have hinvt := conj_eq_inv_of_fixedPointFree (hNn t htC) ht2 hft hk
  have h1 : t * S.z * k * (t * S.z)⁻¹ = k := by
    calc t * S.z * k * (t * S.z)⁻¹ = t * (S.z * k * S.z⁻¹) * t⁻¹ := by group
      _ = t * k⁻¹ * t⁻¹ := by rw [hinvz]
      _ = (t * k * t⁻¹)⁻¹ := by group
      _ = k := by rw [hinvt, inv_inv]
  calc k * (t * S.z) = t * S.z * k * (t * S.z)⁻¹ * (t * S.z) := by rw [h1]
    _ = t * S.z * k := by group

theorem exists_commute_of_four_le {A : Subgroup G} (hAQ : A ≤ S.QG) (hA : 4 ≤ Nat.card A)
    {e : G} (he : e ∈ S.QG) : ∃ t ∈ A, t ≠ 1 ∧ t * e = e * t := by
  by_contra! H
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra! h
    have hbot : A = ⊥ := (eq_bot_iff_forall A).mpr h
    rw [hbot, card_bot] at hA
    omega
  obtain ⟨b, hbA, hb⟩ : ∃ b ∈ A, b ∉ ({1, a, a⁻¹} : Set G) := by
    by_contra! h
    have hsub : (A : Set G) ⊆ {1, a, a⁻¹} := h
    have h3 : ({1, a, a⁻¹} : Set G).ncard ≤ 3 := by
      have h1 := Set.ncard_insert_le (1 : G) {a, a⁻¹}
      have h2 := Set.ncard_insert_le a {a⁻¹}
      rw [Set.ncard_singleton] at h2
      omega
    have hle := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans h3
    have hcard : Nat.card A = (A : Set G).ncard := Nat.card_coe_set_eq (A : Set G)
    omega
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hb
  obtain ⟨hb1, -, hbainv⟩ := hb
  have hab1 : a * b ≠ 1 := fun h => hbainv (eq_inv_of_mul_eq_one_right h)
  apply H (a * b) (mul_mem haA hbA) hab1
  rw [← S.polar_cl_eq_zero_iff (mul_mem (hAQ haA) (hAQ hbA)) he, S.cl_mul (hAQ haA) (hAQ hbA),
    polar_add_left, (S.polar_cl_eq_one_iff (hAQ haA) he).mpr (H a haA ha1),
    (S.polar_cl_eq_one_iff (hAQ hbA) he).mpr (H b hbA hb1)]
  decide

end Setting

end CFSG.LargeExtraspecial
