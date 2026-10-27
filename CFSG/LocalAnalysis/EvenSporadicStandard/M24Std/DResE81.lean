module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.ResidueDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.StandardQuotient

public section

namespace CFSG.EvenSporadicStandard.M24Std.DRes

open Subgroup CFSG.Open

open Subgroup CFSG.Open

section CommProd

variable {G : Type} [Group G]

def commProd (H K : Subgroup G) (hc : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a) : Subgroup G where
  carrier := {x | ∃ h ∈ H, ∃ k ∈ K, h * k = x}
  one_mem' := ⟨1, one_mem _, 1, one_mem _, mul_one 1⟩
  mul_mem' := by
    rintro _ _ ⟨h1, hh1, k1, hk1, rfl⟩ ⟨h2, hh2, k2, hk2, rfl⟩
    refine ⟨h1 * h2, mul_mem hh1 hh2, k1 * k2, mul_mem hk1 hk2, ?_⟩
    calc h1 * h2 * (k1 * k2) = h1 * (h2 * k1) * k2 := by group
      _ = h1 * (k1 * h2) * k2 := by rw [hc h2 hh2 k1 hk1 |>.symm]
      _ = h1 * k1 * (h2 * k2) := by group
  inv_mem' := by
    rintro _ ⟨h, hh, k, hk, rfl⟩
    refine ⟨h⁻¹, inv_mem hh, k⁻¹, inv_mem hk, ?_⟩
    have := hc h hh k hk
    calc h⁻¹ * k⁻¹ = (k * h)⁻¹ := by group
      _ = (h * k)⁻¹ := by rw [this]

theorem mem_commProd {H K : Subgroup G} {hc : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a} {x : G} :
    x ∈ commProd H K hc ↔ ∃ h ∈ H, ∃ k ∈ K, h * k = x := Iff.rfl

theorem commProd_eq_sup {H K : Subgroup G} (hc : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a) :
    commProd H K hc = H ⊔ K := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨h, hh, k, hk, rfl⟩
    exact mul_mem (mem_sup_left hh) (mem_sup_right hk)
  · refine sup_le ?_ ?_
    · intro h hh
      exact ⟨h, hh, 1, one_mem _, mul_one h⟩
    · intro k hk
      exact ⟨1, one_mem _, k, hk, one_mul k⟩

theorem card_commProd {H K : Subgroup G} (hc : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a)
    (hd : ∀ x ∈ H, x ∈ K → x = 1) :
    Nat.card (commProd H K hc) = Nat.card H * Nat.card K := by
  let f : H × K → commProd H K hc := fun p => ⟨p.1 * p.2, p.1, p.1.2, p.2, p.2.2, rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ hab
      have h1 : (a : G) * b = a' * b' := congrArg Subtype.val hab
      have h2 : (a : G)⁻¹ * a' = b * (b' : G)⁻¹ := by
        calc (a : G)⁻¹ * a' = (a : G)⁻¹ * (a' * b') * (b' : G)⁻¹ := by group
          _ = (a : G)⁻¹ * (a * b) * (b' : G)⁻¹ := by rw [← h1]
          _ = b * (b' : G)⁻¹ := by group
      have h3 : (a : G)⁻¹ * a' = 1 :=
        hd _ (mul_mem (inv_mem a.2) a'.2) (h2 ▸ mul_mem b.2 (inv_mem b'.2))
      have h4 : (a : G) = a' := inv_mul_eq_one.1 h3
      have h5 : (b : G) = b' := by
        rw [← h4] at h1
        exact mul_left_cancel h1
      exact Prod.ext (Subtype.ext h4) (Subtype.ext h5)
    · rintro ⟨_, a, ha, b, hb, rfl⟩
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_prod] at this
  exact this.symm

end CommProd

section E81

variable {G : Type} [Group G]

abbrev conjSub (z : G) (H : Subgroup G) : Subgroup G := H.map (MulAut.conj z).toMonoidHom

theorem mem_conjSub {z : G} {H : Subgroup G} {x : G} :
    x ∈ conjSub z H ↔ ∃ h ∈ H, z * h * z⁻¹ = x := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩

structure E81Data (D X Q1 T1 E : Subgroup G) (z : G) : Prop where
  hz : z * z = 1
  hcomm : ∀ a ∈ E, ∀ b ∈ E, a * (z * b * z⁻¹) = (z * b * z⁻¹) * a
  hint : ∀ a ∈ E, z * a * z⁻¹ ∈ E → a = 1
  hXE : X ≤ E
  hD : D = X ⊔ conjSub z X
  hXQ : X ≤ Q1
  hQE : Q1 ≤ E
  hTE : T1 ≤ E
  hQ2 : IsPGroup 2 Q1
  hXn : ∀ q ∈ Q1, ∀ x ∈ X, q * x * q⁻¹ ∈ X
  hTn : ∀ τ ∈ T1, ∀ q ∈ Q1, τ * q * τ⁻¹ ∈ Q1
  hTX : ∀ τ ∈ T1, ∀ x ∈ X, τ * x * τ⁻¹ ∈ X
  hT9 : Nat.card T1 = 9
  hTc : ∀ a ∈ T1, ∀ b ∈ T1, a * b = b * a
  hT3 : ∀ a ∈ T1, a ^ 3 = 1
  hfaith : ∀ τ ∈ T1, τ ≠ 1 → ∃ q ∈ Q1, τ * q * τ⁻¹ * q⁻¹ ∉ X

namespace E81Data

variable {D X Q1 T1 E : Subgroup G} {z : G} (h : E81Data D X Q1 T1 E z)
include h

theorem zinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right h.hz

theorem conj_conj (a : G) : z * (z * a * z⁻¹) * z⁻¹ = a := by
  calc z * (z * a * z⁻¹) * z⁻¹ = (z * z) * a * (z * z)⁻¹ := by group
    _ = a := by rw [h.hz]; group

theorem comm_conj {a b : G} (ha : a ∈ E) (hb : b ∈ conjSub z E) : a * b = b * a := by
  obtain ⟨b', hb', rfl⟩ := mem_conjSub.1 hb
  exact h.hcomm a ha b' hb'

theorem comm_sub {S : Subgroup G} (hS : S ≤ E) : ∀ a ∈ S, ∀ b ∈ conjSub z S, a * b = b * a :=
  fun _ ha _ hb => h.comm_conj (hS ha) (map_mono hS hb)

theorem inf_conj {a : G} (ha : a ∈ E) (hb : a ∈ conjSub z E) : a = 1 := by
  obtain ⟨b, hb', hba⟩ := mem_conjSub.1 hb
  have : z * a * z⁻¹ = b := by
    rw [← hba]
    exact h.conj_conj b
  exact h.hint a ha (this ▸ hb')

theorem mem_D {d : G} : d ∈ D ↔ ∃ x ∈ X, ∃ y ∈ conjSub z X, x * y = d := by
  rw [h.hD, ← commProd_eq_sup (h.comm_sub h.hXE)]
  exact Iff.rfl

theorem D_inf_E {d : G} (hd : d ∈ D) (hdE : d ∈ E) : d ∈ X := by
  obtain ⟨x, hx, y, hy, rfl⟩ := h.mem_D.1 hd
  have hyE : y ∈ E := by
    have : y = x⁻¹ * (x * y) := by group
    rw [this]
    exact mul_mem (inv_mem (h.hXE hx)) hdE
  have hy1 : y = 1 := h.inf_conj hyE (map_mono h.hXE hy)
  rw [hy1, mul_one]
  exact hx

theorem z_conj_D {d : G} (hd : d ∈ D) : z * d * z⁻¹ ∈ D := by
  obtain ⟨x, hx, y, hy, rfl⟩ := h.mem_D.1 hd
  obtain ⟨y0, hy0, rfl⟩ := mem_conjSub.1 hy
  rw [h.mem_D]
  refine ⟨y0, hy0, z * x * z⁻¹, mem_conjSub.2 ⟨x, hx, rfl⟩, ?_⟩
  have hc := h.hcomm y0 (h.hXE hy0) x (h.hXE hx)
  calc y0 * (z * x * z⁻¹) = (z * x * z⁻¹) * y0 := hc
    _ = z * (x * (z⁻¹ * y0 * z)) * z⁻¹ := by group
    _ = z * (x * (z * y0 * z⁻¹)) * z⁻¹ := by rw [h.zinv]
    _ = z * (x * (z * y0 * z⁻¹)) * z⁻¹ := rfl

theorem z_mem_normalizer : z ∈ normalizer (D : Set G) := by
  rw [mem_normalizer_iff]
  intro d
  constructor
  · exact fun hd => h.z_conj_D hd
  · intro hd
    have := h.z_conj_D hd
    rwa [h.conj_conj] at this

theorem mem_normalizer_of_normalizes {S : Subgroup G} (hSE : S ≤ E)
    (hS : ∀ q ∈ S, ∀ x ∈ X, q * x * q⁻¹ ∈ X) : S ≤ normalizer (D : Set G) := by
  have key : ∀ q ∈ S, ∀ d ∈ D, q * d * q⁻¹ ∈ D := by
    intro q hq d hd
    obtain ⟨x, hx, y, hy, rfl⟩ := h.mem_D.1 hd
    rw [h.mem_D]
    refine ⟨q * x * q⁻¹, hS q hq x hx, y, hy, ?_⟩
    have hc := h.comm_conj (hSE hq) (map_mono h.hXE hy)
    calc q * x * q⁻¹ * y = q * x * (q⁻¹ * y) := by group
      _ = q * x * (y * q⁻¹) := by
        have := h.comm_conj (hSE (inv_mem hq)) (map_mono h.hXE hy)
        rw [this]
      _ = q * (x * y) * q⁻¹ := by group
  intro q hq
  rw [mem_normalizer_iff]
  intro d
  exact ⟨fun hd => key q hq d hd, fun hd => by
    have := key q⁻¹ (inv_mem hq) _ hd
    rwa [inv_inv, show q⁻¹ * (q * d * q⁻¹) * q = d by group] at this⟩

theorem T1_le_N : T1 ≤ normalizer (D : Set G) := h.mem_normalizer_of_normalizes h.hTE h.hTX

theorem Q1_le_N : Q1 ≤ normalizer (D : Set G) := h.mem_normalizer_of_normalizes h.hQE h.hXn

theorem conj_le_N {S : Subgroup G} (hS : S ≤ normalizer (D : Set G)) :
    conjSub z S ≤ normalizer (D : Set G) := by
  rintro _ ⟨s, hs, rfl⟩
  exact mul_mem (mul_mem h.z_mem_normalizer (hS hs)) (inv_mem h.z_mem_normalizer)

omit h in
theorem eq_one_of_pow_two_of_odd {Y : Type*} [Group Y] {y : Y} (h2 : ∃ k : ℕ, y ^ (2 ^ k) = 1)
    (hodd : Odd (orderOf y)) : y = 1 := by
  obtain ⟨k, hk⟩ := h2
  have hdvd : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hj] at hodd
  have hj0 : j = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, hne⟩)
  rw [hj0, pow_zero] at hj
  exact orderOf_eq_one_iff.1 hj

theorem key1 [Finite G] {τ1 τ2 : G} (hτ1 : τ1 ∈ T1) (hτ2 : τ2 ∈ conjSub z T1)
    (hN : τ1 * τ2 ∈ normalizer (D : Set G))
    (hO : (QuotientGroup.mk (⟨τ1 * τ2, hN⟩ : normalizer (D : Set G)) : egQD D) ∈
      fusionOddCore (egQD D)) : τ1 = 1 := by
  by_contra hne
  obtain ⟨q, hq, hqX⟩ := h.hfaith τ1 hτ1 hne
  apply hqX
  have hqN : q ∈ normalizer (D : Set G) := h.Q1_le_N hq
  have hcQ : τ1 * q * τ1⁻¹ * q⁻¹ ∈ Q1 := mul_mem (h.hTn τ1 hτ1 q hq) (inv_mem hq)
  have hτ2q : q * τ2 = τ2 * q := h.comm_conj (h.hQE hq) (map_mono h.hTE hτ2)
  have hc_eq : τ1 * τ2 * q * (τ1 * τ2)⁻¹ * q⁻¹ = τ1 * q * τ1⁻¹ * q⁻¹ := by
    have h1 : τ2 * q * τ2⁻¹ = q := by rw [← hτ2q]; group
    calc τ1 * τ2 * q * (τ1 * τ2)⁻¹ * q⁻¹ = τ1 * (τ2 * q * τ2⁻¹) * τ1⁻¹ * q⁻¹ := by group
      _ = τ1 * q * τ1⁻¹ * q⁻¹ := by rw [h1]
  let nτ : normalizer (D : Set G) := ⟨τ1 * τ2, hN⟩
  let nq : normalizer (D : Set G) := ⟨q, hqN⟩
  let φ1 : normalizer (D : Set G) →* egQD D := QuotientGroup.mk' _
  have hcval : ((nτ * nq * nτ⁻¹ * nq⁻¹ : normalizer (D : Set G)) : G) =
      τ1 * q * τ1⁻¹ * q⁻¹ := hc_eq
  have hφO : φ1 (nτ * nq * nτ⁻¹ * nq⁻¹) ∈ fusionOddCore (egQD D) := by
    have e1 : φ1 (nτ * nq * nτ⁻¹ * nq⁻¹) =
        φ1 nτ * (φ1 nq * (φ1 nτ)⁻¹ * (φ1 nq)⁻¹) := by
      simp only [map_mul, map_inv]
      group
    rw [e1]
    exact mul_mem hO ((inferInstance : (fusionOddCore (egQD D)).Normal).conj_mem _ (inv_mem hO)
      (φ1 nq))
  have hpow : ∃ k : ℕ, (φ1 (nτ * nq * nτ⁻¹ * nq⁻¹)) ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := h.hQ2 ⟨_, hcQ⟩
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : (nτ * nq * nτ⁻¹ * nq⁻¹) ^ (2 ^ k) = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hcval]
      exact congrArg Subtype.val hk
    rw [this, map_one]
  have hodd : Odd (orderOf (φ1 (nτ * nq * nτ⁻¹ * nq⁻¹))) :=
    Odd.of_dvd_nat (odd_natCard_fusionOddCore (egQD D)) (Subgroup.orderOf_dvd_natCard _ hφO)
  have h1 := eq_one_of_pow_two_of_odd hpow hodd
  have hcD : ((nτ * nq * nτ⁻¹ * nq⁻¹ : normalizer (D : Set G)) : G) ∈ D :=
    mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h1)
  rw [hcval] at hcD
  exact h.D_inf_E hcD (h.hQE hcQ)

theorem key2 [Finite G] {τ1 τ2 : G} (hτ1 : τ1 ∈ T1) (hτ2 : τ2 ∈ conjSub z T1)
    (hN : τ1 * τ2 ∈ normalizer (D : Set G))
    (hO : (QuotientGroup.mk (⟨τ1 * τ2, hN⟩ : normalizer (D : Set G)) : egQD D) ∈
      fusionOddCore (egQD D)) : τ2 = 1 := by
  obtain ⟨σ, hσ, rfl⟩ := mem_conjSub.1 hτ2
  have hzN := h.z_mem_normalizer
  set τ1' : G := z * τ1 * z⁻¹ with hτ1'
  have hτ1'mem : τ1' ∈ conjSub z T1 := mem_conjSub.2 ⟨τ1, hτ1, rfl⟩
  have hcomm : σ * τ1' = τ1' * σ := h.comm_conj (h.hTE hσ) (map_mono h.hTE hτ1'mem)
  have hprod : z * (τ1 * (z * σ * z⁻¹)) * z⁻¹ = σ * τ1' := by
    calc z * (τ1 * (z * σ * z⁻¹)) * z⁻¹ = (z * τ1 * z⁻¹) * (z * (z * σ * z⁻¹) * z⁻¹) := by group
      _ = τ1' * σ := by rw [h.conj_conj σ]
      _ = σ * τ1' := hcomm.symm
  have hN' : σ * τ1' ∈ normalizer (D : Set G) := by
    rw [← hprod]
    exact mul_mem (mul_mem hzN hN) (inv_mem hzN)
  have hO' : (QuotientGroup.mk (⟨σ * τ1', hN'⟩ : normalizer (D : Set G)) : egQD D) ∈
      fusionOddCore (egQD D) := by
    have e : (⟨σ * τ1', hN'⟩ : normalizer (D : Set G)) =
        ⟨z, hzN⟩ * ⟨τ1 * (z * σ * z⁻¹), hN⟩ * ⟨z, hzN⟩⁻¹ := by
      apply Subtype.ext
      exact hprod.symm
    rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    have := (inferInstance : (fusionOddCore (egQD D)).Normal).conj_mem _ hO
      (QuotientGroup.mk ⟨z, hzN⟩)
    simpa using this
  have h1 := h.key1 hσ hτ1'mem hN' hO'
  rw [h1]
  group

theorem hasElemAbThree81 [Finite G] :
    HasElemAbThree81 (egQD D ⧸ fusionOddCore (egQD D)) := by
  classical
  set N := normalizer (D : Set G) with hNdef
  set T2 := conjSub z T1 with hT2def
  have hcommT : ∀ a ∈ T1, ∀ b ∈ T2, a * b = b * a := h.comm_sub h.hTE
  set T12 := commProd T1 T2 hcommT with hT12
  have hT12N : T12 ≤ N := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact mul_mem (h.T1_le_N ha) (h.conj_le_N h.T1_le_N hb)
  let Φ : ↥(T12.subgroupOf N) →* egQD D ⧸ fusionOddCore (egQD D) :=
    (QuotientGroup.mk' (fusionOddCore (egQD D))).comp
      ((QuotientGroup.mk' (D.subgroupOf N)).comp (T12.subgroupOf N).subtype)
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨n, hn⟩ hΦ
    obtain ⟨τ1, hτ1, τ2, hτ2, hτ⟩ := mem_subgroupOf.1 hn
    have hO : (QuotientGroup.mk n : egQD D) ∈ fusionOddCore (egQD D) :=
      (QuotientGroup.eq_one_iff _).1 hΦ
    have hN : τ1 * τ2 ∈ N := hτ ▸ n.2
    have hn' : n = ⟨τ1 * τ2, hN⟩ := Subtype.ext hτ.symm
    rw [hn'] at hO
    have h1 := h.key1 hτ1 hτ2 hN hO
    have h2 := h.key2 hτ1 hτ2 hN hO
    apply Subtype.ext
    apply Subtype.ext
    show (n : G) = 1
    rw [← hτ, h1, h2, mul_one]
  have hcardT12 : Nat.card T12 = 81 := by
    have hT2card : Nat.card T2 = 9 := by
      rw [hT2def, Subgroup.card_map_of_injective (MulAut.conj z).injective, h.hT9]
    rw [hT12, card_commProd hcommT (fun x hx1 hx2 => h.inf_conj (h.hTE hx1)
      (map_mono h.hTE hx2)), h.hT9, hT2card]
  have hT2comm : ∀ a ∈ T2, ∀ b ∈ T2, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show z * a * z⁻¹ * (z * b * z⁻¹) = z * b * z⁻¹ * (z * a * z⁻¹)
    calc z * a * z⁻¹ * (z * b * z⁻¹) = z * (a * b) * z⁻¹ := by group
      _ = z * (b * a) * z⁻¹ := by rw [h.hTc a ha b hb]
      _ = z * b * z⁻¹ * (z * a * z⁻¹) := by group
  have hT12comm : ∀ x ∈ T12, ∀ y ∈ T12, x * y = y * x := by
    rintro _ ⟨a, ha, b, hb, rfl⟩ _ ⟨a', ha', b', hb', rfl⟩
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [(hcommT a' ha' b hb).symm]
      _ = (a * a') * (b * b') := by group
      _ = (a' * a) * (b' * b) := by rw [h.hTc a ha a' ha', hT2comm b hb b' hb']
      _ = a' * (a * b') * b := by group
      _ = a' * (b' * a) * b := by rw [hcommT a ha b' hb']
      _ = a' * b' * (a * b) := by group
  have hT12exp : ∀ x ∈ T12, x ^ 3 = 1 := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    have hab : Commute a b := hcommT a ha b hb
    rw [hab.mul_pow, h.hT3 a ha, one_mul]
    obtain ⟨b0, hb0, rfl⟩ := mem_conjSub.1 hb
    have hc3 := map_pow (MulAut.conj z) b0 3
    rw [h.hT3 b0 hb0, map_one] at hc3
    simpa [MulAut.conj_apply] using hc3.symm
  refine ⟨Φ.range, ?_, ?_, ?_⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT12N).toEquiv, hcardT12]
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    exact hT12comm _ (mem_subgroupOf.1 x.2) _ (mem_subgroupOf.1 y.2)
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ 3 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      show ((x : N) : G) ^ 3 = 1
      exact hT12exp _ (mem_subgroupOf.1 x.2)
    rw [this, map_one]

end E81Data

end E81

end CFSG.EvenSporadicStandard.M24Std.DRes
