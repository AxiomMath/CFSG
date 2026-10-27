module

public import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.EvenSporadicStandard.HSStd.HL34

open Equiv Equiv.Perm Subgroup
open scoped Pointwise

theorem card_centralizer_prime_order_le {σ : Perm (Fin 5)} (hσ : (orderOf σ).Prime) :
    Nat.card (centralizer ({σ} : Set (Perm (Fin 5)))) ≤ 12 := by
  obtain ⟨n, hn⟩ := cycleType_prime_order hσ
  have hsum : σ.cycleType.sum ≤ Fintype.card (Fin 5) := sum_cycleType_le σ
  have hc := nat_card_centralizer σ
  generalize hp : orderOf σ = p at hn hσ
  rw [hn, Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at hsum
  rw [hn, Fintype.card_fin] at hc
  have hp2 := hσ.two_le
  have hp5 : p ≤ 5 := by
    have := Nat.le_mul_of_pos_left p (by omega : 0 < n + 1)
    omega
  interval_cases p
  · have hn1 : n = 0 ∨ n = 1 := by omega
    rcases hn1 with rfl | rfl
    · simp [Nat.factorial] at hc
      omega
    · simp at hc
      omega
  · have hn1 : n = 0 := by omega
    subst hn1
    simp at hc
    omega
  · exact absurd hσ (by decide)
  · have hn1 : n = 0 := by omega
    subst hn1
    simp at hc
    omega

theorem card_centralizer_le_of_ne_one {σ : Perm (Fin 5)} (h : σ ≠ 1) :
    Nat.card (centralizer ({σ} : Set (Perm (Fin 5)))) ≤ 12 := by
  have h1 : orderOf σ ≠ 1 := fun h' => h (orderOf_eq_one_iff.1 h')
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h1
  have hord := orderOf_pow_orderOf_div (orderOf_pos σ).ne' hpd
  refine le_trans (Subgroup.card_le_of_le ?_)
    (card_centralizer_prime_order_le (σ := σ ^ (orderOf σ / p)) (by rw [hord]; exact hp))
  intro x hx
  rw [mem_centralizer_iff] at hx ⊢
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact (Commute.pow_left (hx σ rfl : σ * x = x * σ) _).eq

variable {D : Type*} [Group D]

theorem conj_eq_inv_of_fixed_point_free (N : Subgroup D) [Finite N] {t : D} (ht : t * t = 1)
    (hN : ∀ n ∈ N, t * n * t⁻¹ ∈ N) (hfix : ∀ n ∈ N, t * n * t⁻¹ = n → n = 1) :
    ∀ n ∈ N, t * n * t⁻¹ = n⁻¹ := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  let f : N → N := fun x => ⟨(x : D)⁻¹ * (t * x * t⁻¹), N.mul_mem (N.inv_mem x.2) (hN _ x.2)⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    have h : (x : D)⁻¹ * (t * x * t⁻¹) = (y : D)⁻¹ * (t * y * t⁻¹) := congrArg Subtype.val hxy
    have hz : t * ((y : D) * (x : D)⁻¹) * t⁻¹ = (y : D) * (x : D)⁻¹ := by
      have h1 : t * y * t⁻¹ = (y : D) * (x : D)⁻¹ * (t * x * t⁻¹) := by
        calc t * y * t⁻¹ = (y : D) * ((y : D)⁻¹ * (t * y * t⁻¹)) := by group
          _ = (y : D) * ((x : D)⁻¹ * (t * x * t⁻¹)) := by rw [h]
          _ = _ := by group
      calc t * ((y : D) * (x : D)⁻¹) * t⁻¹ = (t * y * t⁻¹) * (t * x * t⁻¹)⁻¹ := by group
        _ = _ := by rw [h1]; group
    exact Subtype.ext (mul_inv_eq_one.1 (hfix _ (N.mul_mem y.2 (N.inv_mem x.2)) hz)).symm
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.1 hinj
  intro n hn
  obtain ⟨x, hx⟩ := hsurj ⟨n, hn⟩
  have hx' : (x : D)⁻¹ * (t * x * t⁻¹) = n := congrArg Subtype.val hx
  rw [← hx']
  simp only [hti, mul_inv_rev, inv_inv, mul_assoc, ht, mul_one]

theorem eq_bot_of_fixed_point_free
    (hZ : ∀ N : Subgroup D, N.Normal → Odd (Nat.card N) → N = ⊥)
    (N : Subgroup D) [N.Normal] [Finite N] {t : D} (ht : t * t = 1)
    (hfix : ∀ n ∈ N, t * n * t⁻¹ = n → n = 1) : N = ⊥ := by
  have hinv := conj_eq_inv_of_fixed_point_free N ht
    (fun n hn => Normal.conj_mem inferInstance n hn t) hfix
  refine hZ N inferInstance ?_
  by_contra hev
  have h2 : 2 ∣ Nat.card N := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hev)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hxx : x * x = 1 := by rw [← sq, ← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx; omega
  have hxi : (x : D)⁻¹ = x := inv_eq_of_mul_eq_one_right (congrArg Subtype.val hxx)
  apply hx1
  exact Subtype.ext (hfix x x.2 (by rw [hinv x x.2, hxi]))

section Product

variable {t : D} {K : Subgroup D}

theorem commute_of_mem_zpowers {z y : D} (hz : z ∈ zpowers t) (hy : y ∈ centralizer ({t} : Set D)) :
    z * y = y * z := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hz
  have h : t * y = y * t := mem_centralizer_iff.1 hy t rfl
  exact (Commute.zpow_left (h : Commute t y) n).eq

theorem zpowers_le_centralizer : zpowers t ≤ centralizer ({t} : Set D) :=
  (zpowers_le).2 (mem_centralizer_iff.2 fun g hg => by rw [Set.mem_singleton_iff.1 hg])

theorem eq_one_or_eq_of_mem_zpowers (ht : orderOf t = 2) {z : D} (hz : z ∈ zpowers t) :
    z = 1 ∨ z = t := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hz
  rw [← zpow_mod_orderOf, ht]
  have h : n % ((2 : ℕ) : ℤ) = 0 ∨ n % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases h with h | h <;> rw [h]
  · exact Or.inl (zpow_zero t)
  · exact Or.inr (zpow_one t)

theorem exists_mul_of_mem_sup (hK : K ≤ centralizer ({t} : Set D)) {x : D}
    (hx : x ∈ zpowers t ⊔ K) : ∃ z ∈ zpowers t, ∃ k ∈ K, x = z * k := by
  have hcomm : ∀ w ∈ zpowers t, ∀ y ∈ K, w * y * w⁻¹ = y := fun w hw y hy => by
    rw [commute_of_mem_zpowers hw (hK hy), mul_inv_cancel_right]
  have hle : zpowers t ≤ normalizer K := by
    intro z hz
    rw [mem_normalizer_iff]
    intro k
    constructor
    · intro hk'
      rw [hcomm z hz k hk']
      exact hk'
    · intro hk'
      have h := hcomm z⁻¹ (inv_mem hz) _ hk'
      have e : z⁻¹ * (z * k * z⁻¹) * z⁻¹⁻¹ = k := by group
      rw [e] at h
      rw [h]
      exact hk'
  have hx' : x ∈ ((zpowers t : Subgroup D) : Set D) * (K : Set D) := by
    rw [← coe_mul_of_left_le_normalizer_right (zpowers t) K hle]
    exact hx
  obtain ⟨z, hz, k, hk, rfl⟩ := Set.mem_mul.1 hx'
  exact ⟨z, hz, k, hk, rfl⟩

theorem card_zpowers_sup [Finite D] (hK : K ≤ centralizer ({t} : Set D))
    (hd : Disjoint (zpowers t) K) : Nat.card ↥(zpowers t ⊔ K) = orderOf t * Nat.card K := by
  have hcomm : ∀ (a : ↥(zpowers t)) (b : ↥K), Commute ((zpowers t).subtype a) (K.subtype b) :=
    fun a b => commute_of_mem_zpowers a.2 (hK b.2)
  have hinj := (MonoidHom.noncommCoprod_injective (zpowers t).subtype K.subtype hcomm).2
    ⟨Subtype.val_injective, Subtype.val_injective, by simpa [Subgroup.range_subtype] using hd⟩
  have hrange := MonoidHom.noncommCoprod_range (zpowers t).subtype K.subtype hcomm
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hrange
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_prod,
    Nat.card_zpowers]

theorem card_perm_five : Nat.card (Perm (Fin 5)) = 120 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem card_centralizer_eq [Finite D] (ht : orderOf t = 2)
    (hC : centralizer ({t} : Set D) = zpowers t ⊔ K) (hd : Disjoint (zpowers t) K)
    (eK : ↥K ≃* Perm (Fin 5)) : Nat.card ↥(centralizer ({t} : Set D)) = 240 := by
  rw [hC, card_zpowers_sup (le_sup_right.trans hC.ge) hd, ht, Nat.card_congr eK.toEquiv,
    card_perm_five]

theorem card_inf_centralizer_le [Finite D] (eK : ↥K ≃* Perm (Fin 5)) {k : D} (hk : k ∈ K)
    (hk1 : k ≠ 1) : Nat.card ↥(K ⊓ centralizer ({k} : Set D)) ≤ 12 := by
  have hσ : eK ⟨k, hk⟩ ≠ 1 := fun h =>
    hk1 (congrArg Subtype.val (eK.injective (h.trans (map_one eK).symm)))
  have hmem : ∀ x : ↥(K ⊓ centralizer ({k} : Set D)),
      eK ⟨x.1, x.2.1⟩ ∈ centralizer ({eK ⟨k, hk⟩} : Set (Perm (Fin 5))) := by
    intro x
    rw [mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    rw [← map_mul, ← map_mul]
    exact congrArg eK (Subtype.ext (mem_centralizer_iff.1 x.2.2 k rfl))
  refine le_trans (Nat.card_le_card_of_injective
    (fun x => (⟨eK ⟨x.1, x.2.1⟩, hmem x⟩ : ↥(centralizer ({eK ⟨k, hk⟩} :
      Set (Perm (Fin 5)))))) ?_) (card_centralizer_le_of_ne_one hσ)
  intro x y hxy
  have h1 := eK.injective (congrArg Subtype.val hxy)
  have h2 : ((⟨(x : D), x.2.1⟩ : ↥K) : D) = ((⟨(y : D), y.2.1⟩ : ↥K) : D) :=
    congrArg Subtype.val h1
  exact Subtype.ext h2

end Product

theorem centralizer_eq_bot_of_normal [Finite D]
    (hZ : ∀ N : Subgroup D, N.Normal → Odd (Nat.card N) → N = ⊥)
    {t : D} (ht : orderOf t = 2) {K : Subgroup D}
    (hC : centralizer ({t} : Set D) = zpowers t ⊔ K) (hd : Disjoint (zpowers t) K)
    (eK : ↥K ≃* Perm (Fin 5)) (H : Subgroup D) [H.Normal]
    (hH : ¬ H ≤ centralizer ({t} : Set D))
    (hX : 24 < Nat.card ↥(H ⊓ centralizer ({t} : Set D))) :
    centralizer (H : Set D) = ⊥ := by
  have ht2 : t * t = 1 := by rw [← sq, ← ht]; exact pow_orderOf_eq_one t
  have hKC : K ≤ centralizer ({t} : Set D) := le_sup_right.trans hC.ge
  have step : ∀ m ∈ centralizer (H : Set D), t * m = m * t → m = 1 := by
    intro m hmN hmt
    have hmC : m ∈ centralizer ({t} : Set D) :=
      mem_centralizer_iff.2 fun g hg => by rw [Set.mem_singleton_iff.1 hg]; exact hmt
    obtain ⟨z, hz, k, hk, rfl⟩ := exists_mul_of_mem_sup hKC (hC ▸ hmC)
    by_cases hk1 : k = 1
    · rw [hk1, mul_one] at hmN ⊢
      rcases eq_one_or_eq_of_mem_zpowers ht hz with h | h
      · exact h
      · exfalso
        apply hH
        intro x hx
        refine mem_centralizer_iff.2 fun g hg => ?_
        rw [Set.mem_singleton_iff.1 hg, ← h]
        exact (mem_centralizer_iff.1 hmN x hx).symm
    · exfalso
      have hle : H ⊓ centralizer ({t} : Set D) ≤ zpowers t ⊔ (K ⊓ centralizer ({k} : Set D)) := by
        rintro x ⟨hxH, hxC⟩
        obtain ⟨z', hz', k', hk', rfl⟩ := exists_mul_of_mem_sup hKC (hC ▸ hxC)
        have hxm : z' * k' * (z * k) = z * k * (z' * k') := mem_centralizer_iff.1 hmN _ hxH
        have hkz' : z' * k = k * z' := commute_of_mem_zpowers hz' (hKC hk)
        have hk'z : z * k' = k' * z := commute_of_mem_zpowers hz (hKC hk')
        have hzz : z' * z = z * z' := commute_of_mem_zpowers hz' (zpowers_le_centralizer hz)
        have e1 : z' * k' * (z * k) = z' * z * (k' * k) := by
          calc z' * k' * (z * k) = z' * (k' * z) * k := by simp only [mul_assoc]
            _ = z' * (z * k') * k := by rw [← hk'z]
            _ = z' * z * (k' * k) := by simp only [mul_assoc]
        have e2 : z * k * (z' * k') = z * z' * (k * k') := by
          calc z * k * (z' * k') = z * (k * z') * k' := by simp only [mul_assoc]
            _ = z * (z' * k) * k' := by rw [← hkz']
            _ = z * z' * (k * k') := by simp only [mul_assoc]
        rw [e1, e2, ← hzz] at hxm
        have hcomm : k' * k = k * k' := mul_left_cancel hxm
        exact mul_mem (mem_sup_left hz') (mem_sup_right ⟨hk', mem_centralizer_iff.2 fun g hg => by
          rw [Set.mem_singleton_iff.1 hg]; exact hcomm.symm⟩)
      have h1 := Subgroup.card_le_of_le hle
      rw [card_zpowers_sup (K := K ⊓ centralizer ({k} : Set D)) (fun y hy => hKC hy.1)
        (hd.mono_right inf_le_left), ht] at h1
      have h2 := card_inf_centralizer_le eK hk hk1
      omega
  refine eq_bot_of_fixed_point_free hZ (centralizer (H : Set D)) ht2 fun n hn hfix => ?_
  exact step n hn (mul_inv_eq_iff_eq_mul.1 hfix)

end CFSG.EvenSporadicStandard.HSStd.HL34
