module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSevenCore

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.ABGLocalTools

theorem exists_fixed_of_involutive {α : Type*} [Finite α] (hα : Odd (Nat.card α)) {f : α → α}
    (hf : Function.Involutive f) : ∃ a, f a = a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ : Perm α := hf.toPerm f with hσ
  have hσ2 : σ ^ 2 = 1 := by
    ext a
    simp [hσ, sq, hf a]
  have hP : IsPGroup 2 (zpowers σ) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (orderOf_dvd_of_pow_eq_one (by rw [pow_one]; exact hσ2) : orderOf σ ∣ 2 ^ 1)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨a, ha⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card α
    (fun h => (Nat.not_even_iff_odd.mpr hα) (even_iff_two_dvd.mpr h))
  exact ⟨a, ha ⟨σ, mem_zpowers σ⟩⟩

variable {H : Type*} [Group H] {N : Subgroup H} [N.Normal]

theorem exists_lift_commute [Finite H] (hN : Odd (Nat.card N)) {s : H} (hs : s * s = 1) (q : H ⧸ N)
    (hq : (s : H ⧸ N) * q = q * s) : ∃ y : H, (y : H ⧸ N) = q ∧ s * y = y * s := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hs' : ∀ X : H, s * (s * X) = X := fun X => by rw [← mul_assoc, hs, one_mul]
  have hq' : (y * s)⁻¹ * (s * y) ∈ N := by
    rw [← QuotientGroup.eq]
    exact hq.symm
  set c := y⁻¹ * s * y * s with hc
  have hcN : c ∈ N := by
    have := (inferInstance : N.Normal).conj_mem _ hq' s
    have e : s * ((y * s)⁻¹ * (s * y)) * s⁻¹ = c := by rw [hc, hsi]; group
    rwa [e] at this
  let f : N → N := fun n => ⟨c * (s * n * s), N.mul_mem hcN (by
    simpa [hsi] using (inferInstance : N.Normal).conj_mem _ n.2 s)⟩
  have hf : Function.Involutive f := fun n => Subtype.ext (by
    show c * (s * (c * (s * n * s)) * s) = n
    simp only [hc, mul_assoc, hs, mul_one, hs', mul_inv_cancel_left, inv_mul_cancel_left])
  obtain ⟨n, hn⟩ := exists_fixed_of_involutive hN hf
  have hn' : c * (s * n * s) = n := congrArg Subtype.val hn
  refine ⟨y * n, ?_, ?_⟩
  · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (n : H)).mpr n.2, mul_one]
  · calc s * (y * n) = y * (c * (s * n * s)) * s := by
          rw [hc]; simp only [mul_assoc, hs, mul_one, hs', mul_inv_cancel_left]
      _ = y * n * s := by rw [hn']

theorem odd_orderOf_of_odd_mk (hN : Odd (Nat.card N)) {y : H}
    (hy : Odd (orderOf (y : H ⧸ N))) : Odd (orderOf y) := by
  set m := orderOf (y : H ⧸ N)
  have hm : y ^ m ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact pow_orderOf_eq_one _
  have h1 : y ^ (m * Nat.card N) = 1 := by
    rw [pow_mul]
    exact orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard N hm)
  exact Odd.of_dvd_nat (hy.mul hN) (orderOf_dvd_of_pow_eq_one h1)

variable {G : Type*} [Group G]

@[expose] noncomputable def quotAut {K : Subgroup G} (g : normalizer (K : Set G)) :
    MulAut (K ⧸ pPrimeCore 2 K) :=
  QuotientGroup.congr _ _ (K.normalizerMonoidHom g)
    ((characteristic_iff_map_eq.mp inferInstance) _)

theorem quotAut_mk {K : Subgroup G} (g : normalizer (K : Set G)) (k : K) :
    quotAut g (k : K ⧸ pPrimeCore 2 K) =
      ((⟨(g : G) * k * (g : G)⁻¹, (g.2 k).mp k.2⟩ : K) : K ⧸ pPrimeCore 2 K) := rfl

theorem mem_normalizer_of_conj_le [Finite G] {K : Subgroup G} {g : G}
    (h : ∀ k ∈ K, g * k * g⁻¹ ∈ K) : g ∈ normalizer (K : Set G) := by
  have hle : K.map (MulAut.conj g).toMonoidHom ≤ K := by
    rintro _ ⟨k, hk, rfl⟩
    exact h k hk
  have heq : K.map (MulAut.conj g).toMonoidHom = K :=
    eq_of_le_of_card_ge hle (card_map_of_injective (MulAut.conj g).injective).ge
  rw [mem_normalizer_iff]
  intro k
  constructor
  · exact h k
  · intro hk
    rw [← heq] at hk
    obtain ⟨k', hk', hkk⟩ := hk
    have : k' = k := by
      have := congrArg (fun z => g⁻¹ * z * g) hkk
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      have e : ∀ z, g⁻¹ * (g * z * g⁻¹) * g = z := fun z => by group
      rwa [e, e] at this
    rwa [← this]

@[expose] def a0456 : alternatingGroup (Fin 7) :=
  ⟨swap 0 4 * swap 5 6, mem_alternatingGroup.mpr (by decide)⟩

theorem zpow_cases_three {M : Type*} [Group M] {g : M} (h : g ^ 3 = 1) (i : ℤ) :
    g ^ i = 1 ∨ g ^ i = g ∨ g ^ i = g ^ 2 := by
  rw [zpow_eq_zpow_emod' i h]
  have : i % (3 : ℕ) = 0 ∨ i % (3 : ℕ) = 1 ∨ i % (3 : ℕ) = 2 := by omega
  rcases this with h0 | h0 | h0 <;> rw [h0] <;> simp

theorem a123_pow_three : a123 ^ 3 = 1 := Subtype.ext (by decide)

theorem ne_a123_zpow (i : ℤ) : a456 ≠ a123 ^ i ∧ a450 ≠ a123 ^ i ∧ a450 * a456 ≠ a123 ^ i := by
  rcases zpow_cases_three a123_pow_three i with h | h | h <;> rw [h] <;>
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩ <;>
    · have := congrArg Subtype.val e
      revert this
      decide

theorem not_commute_a012 (j : ℤ) :
    a450 * a123 ^ j * a012 ≠ a012 * (a450 * a123 ^ j) ∧
      a0456 * a123 ^ j * a012 ≠ a012 * (a0456 * a123 ^ j) := by
  rcases zpow_cases_three a123_pow_three j with h | h | h <;> rw [h] <;>
    refine ⟨fun e => ?_, fun e => ?_⟩ <;>
    · have := congrArg Subtype.val e
      revert this
      decide

namespace Seven

variable {G : Type} [Group G] {A B : Subgroup G}
  {ψA : A ≃* alternatingGroup (Fin 7)} {ψB : B ≃* alternatingGroup (Fin 7)}

@[expose] noncomputable def c1 (ψA : A ≃* alternatingGroup (Fin 7)) : G := (ψA.symm a450 : G)

@[expose] noncomputable def cr (ψB : B ≃* alternatingGroup (Fin 7)) : G := (ψB.symm a450 : G)

@[expose] noncomputable def xa (ψA : A ≃* alternatingGroup (Fin 7)) : G := (ψA.symm a4523 : G)

@[expose] noncomputable def y0 (ψB : B ≃* alternatingGroup (Fin 7)) : G := (ψB.symm a4523 : G)

@[expose] noncomputable def sB (ψB : B ≃* alternatingGroup (Fin 7)) : G := (ψB.symm a0456 : G)

theorem w_zpow (i : ℤ) : w ψA ^ i = (ψA.symm (a123 ^ i) : G) := by
  rw [map_zpow, Subgroup.coe_zpow]
  rfl

theorem v_zpow (j : ℤ) : v ψB ^ j = (ψB.symm (a123 ^ j) : G) := by
  rw [map_zpow, Subgroup.coe_zpow]
  rfl

theorem w_mem_centralizer_B (hco : AltCoords 7 A B ψA ψB) : w ψA ∈ centralizer (B : Set G) :=
  hco.2.2.1 ⟨ψA.symm a123, ⟨a123, a123_mem_rootAlt, rfl⟩, rfl⟩

theorem eq_one_of_mem_of_mem_centralizer {K : Subgroup G} (ψ : K ≃* alternatingGroup (Fin 7))
    {a : G} (ha : a ∈ K) (hc : a ∈ centralizer (K : Set G)) : a = 1 := by
  have hz : ψ ⟨a, ha⟩ ∈ center (alternatingGroup (Fin 7)) := mem_center_iff.mpr fun g => by
    obtain ⟨b, rfl⟩ := ψ.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ((mem_centralizer_iff.mp hc) b b.2)
  rw [alternatingGroup.center_eq_bot (by simp)] at hz
  have h1 : (⟨a, ha⟩ : K) = 1 := ψ.injective (by rw [mem_bot.mp hz, map_one])
  exact congrArg Subtype.val h1

theorem exists_eq_zpow_of_mem_A (hco : AltCoords 7 A B ψA ψB) {a : G} (ha : a ∈ A)
    (hO : InOmega ψA ψB a) : ∃ i : ℤ, ψA ⟨a, ha⟩ = a123 ^ i := by
  obtain ⟨k, hk, i, j, hkij⟩ := hO
  have hkA := (mem_inf.mp hk).1
  have hwk : w ψA ^ i * k = k * w ψA ^ i :=
    (mem_centralizer_iff.mp hkA) _ (zpow_mem (w_mem ψA) i)
  have hz : (w ψA) ^ (-i) * a = k * v ψB ^ j := by
    rw [hkij]
    calc w ψA ^ (-i) * (k * w ψA ^ i * v ψB ^ j)
        = w ψA ^ (-i) * (w ψA ^ i * k) * v ψB ^ j := by rw [hwk]; group
      _ = k * v ψB ^ j := by group
  have hz1 := eq_one_of_mem_of_mem_centralizer ψA (mul_mem (zpow_mem (w_mem ψA) _) ha)
    (hz ▸ mul_mem hkA (zpow_mem (v_mem_centralizer_A hco) j))
  have haw : a = w ψA ^ i := by
    calc a = w ψA ^ i * ((w ψA) ^ (-i) * a) := by group
      _ = w ψA ^ i := by rw [hz1, mul_one]
  refine ⟨i, ?_⟩
  have : (⟨a, ha⟩ : A) = ψA.symm (a123 ^ i) :=
    Subtype.ext (by show a = ((ψA.symm (a123 ^ i) : A) : G); rw [haw, w_zpow])
  rw [this, MulEquiv.apply_symm_apply]

theorem exists_commute_of_inOmega (hco : AltCoords 7 A B ψA ψB) {a b : G} (ha : a ∈ A)
    (hb : b ∈ B) (hO : InOmega ψA ψB (a⁻¹ * b)) :
    ∃ j : ℤ, ∀ r ∈ rootAlt 7, ψB ⟨b, hb⟩ * a123 ^ j * r = r * (ψB ⟨b, hb⟩ * a123 ^ j) := by
  obtain ⟨k, hk, i, j, hkij⟩ := hO
  have hkA := (mem_inf.mp hk).1
  have hkB := (mem_inf.mp hk).2
  have hak : a * k = k * a := (mem_centralizer_iff.mp hkA) a ha
  have e1 : b * v ψB ^ (-j) = k * (a * w ψA ^ i) := by
    have hb' : b = a * (k * w ψA ^ i * v ψB ^ j) := by rw [← hkij]; group
    calc b * v ψB ^ (-j) = a * (k * w ψA ^ i * v ψB ^ j) * v ψB ^ (-j) := by rw [← hb']
      _ = a * k * w ψA ^ i := by group
      _ = k * a * w ψA ^ i := by rw [hak]
      _ = k * (a * w ψA ^ i) := by group
  have hb'B : b * v ψB ^ (-j) ∈ B := mul_mem hb (zpow_mem (v_mem ψB) _)
  have hψ : ψB ⟨b, hb⟩ * a123 ^ (-j) = ψB ⟨b * v ψB ^ (-j), hb'B⟩ := by
    have : (⟨b * v ψB ^ (-j), hb'B⟩ : B) = ⟨b, hb⟩ * ψB.symm (a123 ^ (-j)) :=
      Subtype.ext (by
        show b * v ψB ^ (-j) = b * ((ψB.symm (a123 ^ (-j)) : B) : G)
        rw [v_zpow])
    rw [this, map_mul, MulEquiv.apply_symm_apply]
  refine ⟨-j, fun r hr => ?_⟩
  have hy : (ψB.symm r : G) ∈ centralizer (A : Set G) :=
    hco.2.2.2.1 ⟨ψB.symm r, ⟨r, hr, rfl⟩, rfl⟩
  have h1 : (a * w ψA ^ i) * ψB.symm r = ψB.symm r * (a * w ψA ^ i) :=
    (mem_centralizer_iff.mp hy) _ (mul_mem ha (zpow_mem (w_mem ψA) i))
  have h2 : (ψB.symm r : G) * k = k * ψB.symm r := (mem_centralizer_iff.mp hkB) _ (ψB.symm r).2
  have hc : (⟨b * v ψB ^ (-j), hb'B⟩ : B) * ψB.symm r = ψB.symm r * ⟨b * v ψB ^ (-j), hb'B⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [e1]
    calc k * (a * w ψA ^ i) * ψB.symm r = k * ((a * w ψA ^ i) * ψB.symm r) := by group
      _ = k * (ψB.symm r * (a * w ψA ^ i)) := by rw [h1]
      _ = (ψB.symm r * k) * (a * w ψA ^ i) := by rw [h2]; group
      _ = ψB.symm r * (k * (a * w ψA ^ i)) := by group
  rw [hψ]
  have := congrArg ψB hc
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this

theorem not_inOmega_A (hco : AltCoords 7 A B ψA ψB) :
    ¬ InOmega ψA ψB (u ψA) ∧ ¬ InOmega ψA ψB (c1 ψA) ∧ ¬ InOmega ψA ψB (c1 ψA * u ψA) := by
  have key : ∀ σ : alternatingGroup (Fin 7), InOmega ψA ψB (ψA.symm σ : G) →
      ∃ i : ℤ, σ = a123 ^ i := fun σ h => by
    obtain ⟨i, hi⟩ := exists_eq_zpow_of_mem_A hco (ψA.symm σ).2 h
    rw [Subtype.coe_eta, MulEquiv.apply_symm_apply] at hi
    exact ⟨i, hi⟩
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨i, hi⟩ := key a456 h
    exact (ne_a123_zpow i).1 hi
  · obtain ⟨i, hi⟩ := key a450 h
    exact (ne_a123_zpow i).2.1 hi
  · have e : c1 ψA * u ψA = (ψA.symm (a450 * a456) : G) := by rw [map_mul]; rfl
    rw [e] at h
    obtain ⟨i, hi⟩ := key _ h
    exact (ne_a123_zpow i).2.2 hi

theorem not_inOmega_B (hco : AltCoords 7 A B ψA ψB) {a : G} (ha : a ∈ A) :
    ¬ InOmega ψA ψB (a⁻¹ * cr ψB) ∧ ¬ InOmega ψA ψB (a⁻¹ * sB ψB) := by
  have key : ∀ σ : alternatingGroup (Fin 7), InOmega ψA ψB (a⁻¹ * (ψB.symm σ : G)) →
      ∃ j : ℤ, σ * a123 ^ j * a012 = a012 * (σ * a123 ^ j) := fun σ h => by
    obtain ⟨j, hj⟩ := exists_commute_of_inOmega hco ha (ψB.symm σ).2 h
    have := hj a012 a012_mem_rootAlt
    rw [Subtype.coe_eta, MulEquiv.apply_symm_apply] at this
    exact ⟨j, this⟩
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨j, hj⟩ := key a450 h
    exact (not_commute_a012 j).1 hj
  · obtain ⟨j, hj⟩ := key a0456 h
    exact (not_commute_a012 j).2 hj

theorem mem_H7_of_A (hco : AltCoords 7 A B ψA ψB) {σ : alternatingGroup (Fin 7)}
    (hσ : σ * a123 = a123 * σ) : (ψA.symm σ : G) ∈ H7 ψA ψB := by
  refine ⟨mem_centralizer_singleton_iff.mpr ?_, mem_centralizer_singleton_iff.mpr ?_⟩
  · show (ψA.symm σ : G) * (ψA.symm a123 : G) = (ψA.symm a123 : G) * (ψA.symm σ : G)
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hσ]
  · exact (mem_centralizer_iff.mp (v_mem_centralizer_A hco)) _ (ψA.symm σ).2

theorem mem_H7_of_B (hco : AltCoords 7 A B ψA ψB) {σ : alternatingGroup (Fin 7)}
    (hσ : σ * a123 = a123 * σ) : (ψB.symm σ : G) ∈ H7 ψA ψB := by
  refine ⟨mem_centralizer_singleton_iff.mpr ?_, mem_centralizer_singleton_iff.mpr ?_⟩
  · exact (mem_centralizer_iff.mp (w_mem_centralizer_B hco)) _ (ψB.symm σ).2
  · show (ψB.symm σ : G) * (ψB.symm a123 : G) = (ψB.symm a123 : G) * (ψB.symm σ : G)
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hσ]

theorem u_mem_H7 (hco : AltCoords 7 A B ψA ψB) : u ψA ∈ H7 ψA ψB :=
  mem_H7_of_A hco (Subtype.ext (by decide))

theorem c1_mem_H7 (hco : AltCoords 7 A B ψA ψB) : c1 ψA ∈ H7 ψA ψB :=
  mem_H7_of_A hco (Subtype.ext (by decide))

theorem cr_mem_H7 (hco : AltCoords 7 A B ψA ψB) : cr ψB ∈ H7 ψA ψB :=
  mem_H7_of_B hco (Subtype.ext (by decide))

theorem sB_mem_H7 (hco : AltCoords 7 A B ψA ψB) : sB ψB ∈ H7 ψA ψB :=
  mem_H7_of_B hco (Subtype.ext (by decide))

theorem inOmega_of_mem_core [Finite G] (hco : AltCoords 7 A B ψA ψB)
    (hN : normalizer (A : Set G) ⊔ normalizer (B : Set G) ≤
      normalizer ((centralizer (A : Set G) ⊓ centralizer (B : Set G) : Subgroup G) : Set G))
    (ht1B : ∀ t ∈ centralizer (B : Set G), t * t = 1 → t ≠ 1 →
      centralizer ({t} : Set G) ≤ normalizer (B : Set G))
    {g : G} (hg : g ∈ H7 ψA ψB) (hO : (⟨g, hg⟩ : H7 ψA ψB) ∈ pPrimeCore 2 (H7 ψA ψB)) :
    InOmega ψA ψB g :=
  core_le hco hN ht1B ⟨⟨g, hg⟩, hO, rfl⟩

end Seven

end CFSG.ComponentClassification.RankTwoAlt
