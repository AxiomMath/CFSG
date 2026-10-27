module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.ComponentInitial.SteinbergBM

open Subgroup

variable {F Y : Type} [Group F] [Group Y] {θ : F →* Y}

theorem eq_one_of_mem_ker_of_pow (hR : Nat.Coprime 2 (Nat.card θ.ker)) {x : F}
    (hx : θ x = 1) {m : ℕ} (hxm : x ^ 2 ^ m = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hxm
  have h2 : orderOf x ∣ Nat.card θ.ker := by
    have h := orderOf_dvd_natCard (⟨x, hx⟩ : θ.ker)
    have e : orderOf (⟨x, hx⟩ : θ.ker) = orderOf x := Subgroup.orderOf_mk x hx
    rwa [e] at h
  have h3 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes (hR.pow_left m) h1 h2
  exact orderOf_eq_one_iff.1 h3

theorem conj_sq_eq_one {G : Type*} [Group G] {f : G} (hf : f ^ 2 = 1) (q : G) :
    (q * f * q⁻¹) ^ 2 = 1 := by
  rw [pow_two, show q * f * q⁻¹ * (q * f * q⁻¹) = q * (f * f) * q⁻¹ by group, ← pow_two, hf,
    mul_one, mul_inv_cancel]

variable {Q : Subgroup F}

theorem eq_of_sq_eq_one_of_map_eq (hR : Nat.Coprime 2 (Nat.card θ.ker))
    (hZ : ∀ c ∈ Q, θ c = 1 → ∀ q ∈ Q, q * c = c * q) {q q' : F} (hq : q ∈ Q) (hq' : q' ∈ Q)
    (hq2 : q ^ 2 = 1) (hq'2 : q' ^ 2 = 1) (h : θ q = θ q') : q = q' := by
  set c := q⁻¹ * q' with hc
  have hcQ : c ∈ Q := mul_mem (inv_mem hq) hq'
  have hcθ : θ c = 1 := by rw [hc, map_mul, map_inv, h, inv_mul_cancel]
  have hcq : q * c = c * q := hZ c hcQ hcθ q hq
  have e : q' = q * c := by rw [hc, mul_inv_cancel_left]
  have hc2 : c ^ 2 ^ 1 = 1 := by
    have h' : q' ^ 2 = q ^ 2 * c ^ 2 := by
      rw [e, pow_two, pow_two, pow_two]
      calc q * c * (q * c) = q * (c * q) * c := by group
        _ = q * (q * c) * c := by rw [← hcq]
        _ = q * q * (c * c) := by group
    rw [h', hq2, one_mul] at hq'2
    rw [pow_one]
    exact hq'2
  have h1 := eq_one_of_mem_ker_of_pow hR hcθ hc2
  rw [hc, inv_mul_eq_one] at h1
  exact h1

theorem mem_of_pow_two_pow_eq_one [Q.Normal] (hR : Nat.Coprime 2 (Nat.card θ.ker))
    {D : Subgroup Y} (hDQ : D.comap θ = θ.ker ⊔ Q) {x : F} (hx : θ x ∈ D) {m : ℕ}
    (hxm : x ^ 2 ^ m = 1) : x ∈ Q := by
  have hx' : x ∈ θ.ker ⊔ Q := by
    rw [← hDQ]
    exact hx
  rw [← SetLike.mem_coe, Subgroup.mul_normal] at hx'
  obtain ⟨r, hr, q, hq, rfl⟩ := hx'
  have h1 : (QuotientGroup.mk r : F ⧸ Q) ^ 2 ^ m = 1 := by
    have h := congrArg (QuotientGroup.mk' Q) hxm
    have hq1 : QuotientGroup.mk' Q q = 1 := (QuotientGroup.eq_one_iff q).2 hq
    rw [map_pow, map_one, map_mul, hq1, mul_one] at h
    exact h
  have h2 : (QuotientGroup.mk r : F ⧸ Q) ^ Nat.card θ.ker = 1 := by
    have h : r ^ Nat.card θ.ker = 1 := by
      have := pow_card_eq_one' (G := θ.ker) (x := ⟨r, hr⟩)
      exact congrArg Subtype.val this
    rw [← QuotientGroup.mk_pow, h, QuotientGroup.mk_one]
  have h3 : orderOf (QuotientGroup.mk r : F ⧸ Q) = 1 :=
    Nat.eq_one_of_dvd_coprimes (hR.pow_left m) (orderOf_dvd_of_pow_eq_one h1)
      (orderOf_dvd_of_pow_eq_one h2)
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact mul_mem h3 hq

theorem exists_conj_eq_of_conj_map [Q.Normal] (hR : Nat.Coprime 2 (Nat.card θ.ker))
    (hZ : ∀ c ∈ Q, θ c = 1 → ∀ q ∈ Q, q * c = c * q) {D : Subgroup Y} (hQD : Q.map θ = D)
    (hDQ : D.comap θ = θ.ker ⊔ Q) {f t : F} (hf2 : f ^ 2 = 1) (htQ : t ∈ Q) (ht2 : t ^ 2 = 1)
    (hfD : θ f ∈ D) {d : Y} (hd : d ∈ D) (hdt : d * θ f * d⁻¹ = θ t) :
    ∃ q ∈ Q, q * f * q⁻¹ = t := by
  have hfQ : f ∈ Q := mem_of_pow_two_pow_eq_one hR hDQ hfD (m := 1) (by rw [pow_one]; exact hf2)
  rw [← hQD] at hd
  obtain ⟨q, hq, rfl⟩ := hd
  refine ⟨q, hq, eq_of_sq_eq_one_of_map_eq hR hZ (‹Q.Normal›.conj_mem f hfQ q) htQ
    (conj_sq_eq_one hf2 q) ht2 ?_⟩
  rw [map_mul, map_mul, map_inv]
  exact hdt

theorem exists_conj_eq_of_inverts (hR : Nat.Coprime 2 (Nat.card θ.ker))
    (hθ : Function.Surjective θ) {a : F} (ha : ∀ r ∈ θ.ker, a⁻¹ * r * a = r⁻¹) {f : F} {y : Y}
    (hy : y * θ f * y⁻¹ = θ a) : ∃ w : F, w * f * w⁻¹ = a := by
  obtain ⟨w₀, rfl⟩ := hθ y
  set r := a⁻¹ * (w₀ * f * w₀⁻¹) with hr
  have hrR : r ∈ θ.ker := by
    rw [MonoidHom.mem_ker, hr, map_mul, map_inv, map_mul, map_mul, map_inv, hy, inv_mul_cancel]
  obtain ⟨j, hj⟩ : Odd (Nat.card θ.ker) := Nat.coprime_two_left.1 hR
  have hrm : r ^ Nat.card θ.ker = 1 := by
    have := pow_card_eq_one' (G := θ.ker) (x := ⟨r, hrR⟩)
    exact congrArg Subtype.val this
  set s := r⁻¹ ^ (j + 1) with hs
  have hsR : s ∈ θ.ker := pow_mem (inv_mem hrR) _
  have hs2 : s * s = r⁻¹ := by
    rw [hs, ← pow_add, show j + 1 + (j + 1) = Nat.card θ.ker + 1 by omega, pow_succ, inv_pow,
      hrm, inv_one, one_mul]
  have hsa : s * a * s⁻¹ = a * r := by
    have h1 : a⁻¹ * s * a = s⁻¹ := ha s hsR
    calc s * a * s⁻¹ = a * (a⁻¹ * s * a) * s⁻¹ := by group
      _ = a * (s * s)⁻¹ := by rw [h1]; group
      _ = a * r := by rw [hs2, inv_inv]
  refine ⟨s⁻¹ * w₀, ?_⟩
  calc s⁻¹ * w₀ * f * (s⁻¹ * w₀)⁻¹ = s⁻¹ * (w₀ * f * w₀⁻¹) * s := by group
    _ = s⁻¹ * (a * r) * s := by rw [hr, mul_inv_cancel_left]
    _ = s⁻¹ * (s * a * s⁻¹) * s := by rw [hsa]
    _ = a := by group

theorem two_mul_card_dvd_card_centralizer [Q.Normal] (hR : Nat.Coprime 2 (Nat.card θ.ker))
    (hZ : ∀ c ∈ Q, θ c = 1 → ∀ q ∈ Q, q * c = c * q) {D : Subgroup Y} [D.Normal]
    (hQD : Q.map θ = D) {t : F} (htQ : t ∈ Q) (ht2 : t ^ 2 = 1) {U : Subgroup Y} (hUD : U ≤ D)
    (hUt : ∀ u ∈ U, u * θ t = θ t * u) {a : F} (ha2 : a ^ 2 = 1) (hat : a * t = t * a)
    (haD : θ a ∉ D) : 2 * Nat.card U ∣ Nat.card (centralizer ({t} : Set F)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer ({t} : Set F) with hH
  set H₀ := (D.comap θ).subgroupOf H with hH₀
  set Q₀ := Q ⊓ U.comap θ with hQ₀
  have hQ₀H : ∀ q ∈ Q₀, q ∈ H ∧ q ∈ D.comap θ := by
    intro q hq
    obtain ⟨hqQ, hqU⟩ := mem_inf.1 hq
    refine ⟨?_, hUD hqU⟩
    rw [hH, mem_centralizer_singleton_iff]
    have h1 : q * t * q⁻¹ = t := eq_of_sq_eq_one_of_map_eq hR hZ (‹Q.Normal›.conj_mem t htQ q)
      htQ (conj_sq_eq_one ht2 q) ht2 (by rw [map_mul, map_mul, map_inv, hUt _ hqU,
        mul_inv_cancel_right])
    calc q * t = q * t * q⁻¹ * q := by group
      _ = t * q := by rw [h1]
  have hUQ₀ : Nat.card U ∣ Nat.card Q₀ := by
    let ρ : Q₀ →* U := (θ.comp Q₀.subtype).codRestrict U fun q => (mem_inf.1 q.2).2
    have hρ : Function.Surjective ρ := by
      intro u
      have hu : (u : Y) ∈ Q.map θ := by
        rw [hQD]
        exact hUD u.2
      obtain ⟨q, hq, hqu⟩ := hu
      refine ⟨⟨q, mem_inf.2 ⟨hq, ?_⟩⟩, Subtype.ext hqu⟩
      rw [mem_comap, hqu]
      exact u.2
    exact Subgroup.card_dvd_of_surjective hρ
  have hQ₀H₀ : Nat.card Q₀ ∣ Nat.card H₀ := by
    refine Subgroup.card_dvd_of_injective
      ⟨⟨fun q => ⟨⟨q, (hQ₀H q q.2).1⟩, (hQ₀H q q.2).2⟩, rfl⟩, fun _ _ => rfl⟩ ?_
    intro q q' h
    have h' := congrArg (fun x : H₀ => ((x : H) : F)) h
    exact Subtype.ext h'
  have haH : a ∈ H := by
    rw [hH, mem_centralizer_singleton_iff]
    exact hat
  have hidx : 2 ∣ Nat.card (H ⧸ H₀) := by
    have hord : orderOf (QuotientGroup.mk ⟨a, haH⟩ : H ⧸ H₀) = 2 := by
      apply orderOf_eq_prime
      · rw [← QuotientGroup.mk_pow, show (⟨a, haH⟩ : H) ^ 2 = 1 from Subtype.ext ha2,
          QuotientGroup.mk_one]
      · rw [Ne, QuotientGroup.eq_one_iff, mem_subgroupOf]
        exact haD
    rw [← hord]
    exact orderOf_dvd_natCard _
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup H₀]
  exact Nat.mul_dvd_mul hidx (hUQ₀.trans hQ₀H₀)

end CFSG.LocalAnalysis.ComponentInitial.SteinbergBM
