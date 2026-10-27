module

import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoreConjugacy
import CFSG.RankThree.PartOne.K1214.Basic
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

section Field

theorem exists_generator_units (K : Type) [Field K] [Finite K] :
    ∃ t : K, orderOf t = Nat.card K - 1 ∧ ∀ y : K, y ≠ 0 → ∃ j : ℕ, y = t ^ j := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  refine ⟨g, ?_, ?_⟩
  · rw [orderOf_units, orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units]
  · intro y hy
    have := mem_powers_iff_mem_zpowers.mpr (hg (Units.mk0 y hy))
    obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).mp this
    exact ⟨j, by simpa using (congrArg Units.val hj).symm⟩

theorem intCast_pow_prime (K : Type) [Field K] (p : ℕ) [hp : Fact p.Prime] [CharP K p] (n : ℤ) :
    (n : K) ^ p = n := by
  have : ExpChar K p := ExpChar.prime hp.out
  have h := map_intCast (frobenius K p) n
  rwa [frobenius_def] at h

theorem exists_pow_sq_eq_intCast {K : Type} [Field K] {p : ℕ} [hp : Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) {t : K} (ht : orderOf t = p ^ 2 - 1)
    (hgen : ∀ y : K, y ≠ 0 → ∃ j : ℕ, y = t ^ j) {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) :
    ∃ m : ℕ, (n : K) = (t ^ 2) ^ m := by
  have hn0 : (n : K) ≠ 0 := fun h => hn ((CharP.intCast_eq_zero_iff K p n).mp h)
  obtain ⟨j, hj⟩ := hgen _ hn0
  have ht0 : t ≠ 0 := by
    rintro rfl
    have hp1 : 1 < p := hp.out.one_lt
    rw [orderOf_zero] at ht
    have : 4 ≤ p ^ 2 := by nlinarith
    omega
  have h1 : (n : K) ^ p = n := intCast_pow_prime K p n
  have h2 : t ^ (j * (p - 1)) = 1 := by
    have h3 : t ^ (j * p) = t ^ j := by rw [pow_mul, ← hj, h1, hj]
    have hp1 : 1 ≤ p := hp.out.one_lt.le
    have : t ^ j * t ^ (j * (p - 1)) = t ^ j * 1 := by
      rw [← pow_add, mul_one]
      calc t ^ (j + j * (p - 1)) = t ^ (j * p) := by congr 1; zify [hp1]; ring
        _ = t ^ j := h3
    exact mul_left_cancel₀ (pow_ne_zero _ ht0) this
  have h4 := orderOf_dvd_of_pow_eq_one h2
  rw [ht] at h4
  have hp3 : 3 ≤ p := by
    have := hp.out.two_le
    omega
  have h5 : (p - 1) * (p + 1) = p ^ 2 - 1 := by
    zify [Nat.one_le_pow 2 p (by omega), (by omega : 1 ≤ p)]
    ring
  rw [← h5, mul_comm j] at h4
  have h6 : (p + 1) ∣ j := Nat.dvd_of_mul_dvd_mul_left (by omega) h4
  have hodd : Even (p + 1) := (hp.out.odd_of_ne_two hp2).add_one
  obtain ⟨c, hc⟩ := hodd
  obtain ⟨j', hj'⟩ := h6
  refine ⟨c * j', ?_⟩
  rw [hj, hj', hc, pow_mul, pow_mul]
  congr 1
  ring_nf

theorem lt_orderOf_sq {K : Type} [Field K] {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {t : K}
    (ht : orderOf t = p ^ 2 - 1) : p < orderOf (t ^ 2) := by
  have hp3 : 3 ≤ p := by
    have := hp.out.two_le
    omega
  have hodd : 2 ∣ p ^ 2 - 1 := by
    have h2 : Odd (p ^ 2) := (hp.out.odd_of_ne_two hp2).pow
    obtain ⟨c, hc⟩ := h2
    exact ⟨c, by omega⟩
  rw [orderOf_pow_of_dvd (by norm_num) (ht ▸ hodd), ht]
  have : 2 * p < p ^ 2 - 1 := by
    have : 3 * p ≤ p ^ 2 := by nlinarith
    omega
  omega

theorem exists_pow_sq_mul_not_mem {K : Type} [Field K] {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {t : K} (ht : orderOf t = p ^ 2 - 1) {a : K} (ha : a ≠ 0) {D : AddSubgroup K}
    (hD : Nat.card D = p) : ∃ k : ℕ, (t ^ 2) ^ k * a ∉ D := by
  by_contra! hall
  have : Finite D := Nat.finite_of_card_ne_zero (by rw [hD]; exact hp.out.ne_zero)
  have hinj : Function.Injective (fun k : Fin (orderOf (t ^ 2)) =>
      (⟨(t ^ 2) ^ (k : ℕ) * a, hall k⟩ : D)) := by
    intro i j hij
    have h1 : (t ^ 2) ^ (i : ℕ) * a = (t ^ 2) ^ (j : ℕ) * a := congrArg Subtype.val hij
    have h2 := mul_right_cancel₀ ha h1
    exact Fin.ext (pow_injOn_Iio_orderOf i.2 j.2 h2)
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_fin, hD] at this
  exact absurd (lt_orderOf_sq hp2 ht) (not_lt.mpr this)

theorem exists_pow_sq_mul_mem_coset {K : Type} [Field K] {p : ℕ} [hp : Fact p.Prime] [CharP K p]
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ 2) {t : K} (ht : orderOf t = p ^ 2 - 1)
    (hgen : ∀ y : K, y ≠ 0 → ∃ j : ℕ, y = t ^ j) {a : K} (ha : a ≠ 0) {D : AddSubgroup K}
    (hD : Nat.card D = p) {a₀ : K} (ha₀ : a₀ ∉ D) :
    ∃ k : ℕ, ∃ d ∈ D, (t ^ 2) ^ k * a = a₀ + d := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hp.out.ne_zero)
  obtain ⟨k₁, hk₁⟩ := exists_pow_sq_mul_not_mem hp2 ht ha hD
  set z : K := (t ^ 2) ^ k₁ * a with hz
  set H : AddSubgroup K := D ⊔ AddSubgroup.zmultiples z with hH
  have hDH : D < H := lt_of_le_of_ne le_sup_left fun h => hk₁ (by
    have : z ∈ H := AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples z)
    rwa [← h] at this)
  have hcard : Nat.card H = p ^ 2 := by
    have h2 : Nat.card H ∣ p ^ 2 := hK ▸ AddSubgroup.card_addSubgroup_dvd_card H
    have h3 : Nat.card D < Nat.card H := AddSubgroup.card_lt_of_lt hDH
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow hp.out).mp h2
    rw [hD] at h3
    have hp1 := hp.out.one_lt
    interval_cases j
    · rw [pow_zero] at hj'
      omega
    · rw [pow_one] at hj'
      omega
    · exact hj'
  have htop : H = ⊤ := (AddSubgroup.card_eq_iff_eq_top H).mp (by rw [hcard, hK])
  have ha₀H : a₀ ∈ H := htop ▸ AddSubgroup.mem_top a₀
  obtain ⟨d, hd, w, hw, hdw⟩ := AddSubgroup.mem_sup.mp ha₀H
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hw
  have hn : ¬ (p : ℤ) ∣ n := by
    rintro ⟨c, rfl⟩
    apply ha₀
    have : (p * c) • z = 0 := by
      rw [mul_comm, mul_smul]
      simp
    rw [← hdw, this, add_zero]
    exact hd
  obtain ⟨m, hm⟩ := exists_pow_sq_eq_intCast hp2 ht hgen hn
  refine ⟨m + k₁, -d, D.neg_mem hd, ?_⟩
  rw [pow_add, mul_assoc, ← hz, ← hdw, zsmul_eq_mul, hm]
  ring

theorem zmultiples_ne_zmultiples_pow_sq_mul {K : Type} [Field K] {p : ℕ} [hp : Fact p.Prime]
    [CharP K p] (hp5 : 5 ≤ p) {t : K} (ht : orderOf t = p ^ 2 - 1) {a : K} (ha : a ≠ 0) {i : ℕ}
    (hi1 : 1 ≤ i) (hi2 : i ≤ 2) :
    AddSubgroup.zmultiples a ≠ AddSubgroup.zmultiples ((t ^ 2) ^ i * a) := by
  intro h
  have hmem : (t ^ 2) ^ i * a ∈ AddSubgroup.zmultiples a := by
    rw [h]
    exact AddSubgroup.mem_zmultiples _
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
  rw [zsmul_eq_mul] at hn
  have hn' : (n : K) = (t ^ 2) ^ i := mul_right_cancel₀ ha (by rw [hn])
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [orderOf_zero] at ht
    have : 25 ≤ p ^ 2 := by nlinarith
    omega
  have h1 : ((t ^ 2) ^ i) ^ p = (t ^ 2) ^ i := by rw [← hn']; exact intCast_pow_prime K p n
  have hp1 : 1 ≤ p := by omega
  have h2 : t ^ (2 * i * (p - 1)) = 1 := by
    have h3 : t ^ (2 * i * p) = t ^ (2 * i) := by
      have e1 : t ^ (2 * i * p) = ((t ^ 2) ^ i) ^ p := by
        rw [← pow_mul, ← pow_mul, mul_assoc]
      have e2 : t ^ (2 * i) = (t ^ 2) ^ i := by rw [← pow_mul]
      rw [e1, e2]
      exact h1
    have : t ^ (2 * i) * t ^ (2 * i * (p - 1)) = t ^ (2 * i) * 1 := by
      rw [← pow_add, mul_one]
      calc t ^ (2 * i + 2 * i * (p - 1)) = t ^ (2 * i * p) := by congr 1; zify [hp1]; ring
        _ = t ^ (2 * i) := h3
    exact mul_left_cancel₀ (pow_ne_zero _ ht0) this
  have h4 := orderOf_dvd_of_pow_eq_one h2
  rw [ht] at h4
  have h5 : (p - 1) * (p + 1) = p ^ 2 - 1 := by
    zify [Nat.one_le_pow 2 p (by omega), hp1]
    ring
  rw [← h5, mul_comm (2 * i)] at h4
  have h6 : (p + 1) ∣ 2 * i := Nat.dvd_of_mul_dvd_mul_left (by omega) h4
  have := Nat.le_of_dvd (by omega) h6
  omega

end Field

section Torus

variable {G : Type} [Group G]

structure IsFieldTorus (p : ℕ) (U : Subgroup G) (h : G) : Prop where
  card_eq : Nat.card U = p ^ 2
  mem_normalizer : h ∈ normalizer (U : Set G)
  coset : ∀ π ∈ U, π ≠ 1 → ∀ D : Subgroup G, D ≤ U → Nat.card D = p →
    ∀ π₀ ∈ U, π₀ ∉ D → ∃ k : ℕ, ∃ d ∈ D, h ^ k * π * (h ^ k)⁻¹ = π₀ * d
  zpowers_ne_one : ∀ π ∈ U, π ≠ 1 → zpowers π ≠ zpowers (h * π * h⁻¹)
  zpowers_ne_two : ∀ π ∈ U, π ≠ 1 → zpowers π ≠ zpowers (h ^ 2 * π * (h ^ 2)⁻¹)

theorem IsFieldTorus.of_hom {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [CharP K p]
    (hp5 : 5 ≤ p) (hK : Nat.card K = p ^ 2) {t : K} (ht : orderOf t = p ^ 2 - 1)
    (hgen : ∀ y : K, y ≠ 0 → ∃ j : ℕ, y = t ^ j) {ψ : Multiplicative K →* G}
    (hψ : Function.Injective ψ) {h : G}
    (hh : ∀ a : K, h * ψ (Multiplicative.ofAdd a) * h⁻¹ =
      ψ (Multiplicative.ofAdd (t ^ 2 * a))) : IsFieldTorus p ψ.range h := by
  have hp2 : p ≠ 2 := by omega
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [orderOf_zero] at ht
    have : 25 ≤ p ^ 2 := by nlinarith
    omega
  have iter : ∀ (k : ℕ) (a : K), h ^ k * ψ (Multiplicative.ofAdd a) * (h ^ k)⁻¹ =
      ψ (Multiplicative.ofAdd ((t ^ 2) ^ k * a)) := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih =>
      intro a
      calc h ^ (k + 1) * ψ (Multiplicative.ofAdd a) * (h ^ (k + 1))⁻¹
          = h * (h ^ k * ψ (Multiplicative.ofAdd a) * (h ^ k)⁻¹) * h⁻¹ := by
            rw [pow_succ']
            group
        _ = ψ (Multiplicative.ofAdd ((t ^ 2) ^ (k + 1) * a)) := by
            rw [ih, hh, pow_succ' (t ^ 2) k, mul_assoc]
  have hz : ∀ a b : K, ψ (Multiplicative.ofAdd b) ∈ zpowers (ψ (Multiplicative.ofAdd a)) →
      b ∈ AddSubgroup.zmultiples a := by
    intro a b hb
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hb
    rw [← map_zpow, ← ofAdd_zsmul] at hn
    exact ⟨n, congrArg Multiplicative.toAdd (hψ hn)⟩
  have hne : ∀ (i : ℕ), 1 ≤ i → i ≤ 2 → ∀ a : K, a ≠ 0 →
      zpowers (ψ (Multiplicative.ofAdd a)) ≠
        zpowers (h ^ i * ψ (Multiplicative.ofAdd a) * (h ^ i)⁻¹) := by
    intro i hi1 hi2 a ha heq
    rw [iter] at heq
    have h1 : (t ^ 2) ^ i * a ∈ AddSubgroup.zmultiples a :=
      hz a _ (heq ▸ mem_zpowers _)
    have h2 : a ∈ AddSubgroup.zmultiples ((t ^ 2) ^ i * a) :=
      hz _ a (heq ▸ mem_zpowers _)
    exact zmultiples_ne_zmultiples_pow_sq_mul hp5 ht ha hi1 hi2
      (le_antisymm (AddSubgroup.zmultiples_le.mpr h2) (AddSubgroup.zmultiples_le.mpr h1))
  have hnonzero : ∀ π ∈ ψ.range, π ≠ 1 → ∃ a : K, a ≠ 0 ∧ π = ψ (Multiplicative.ofAdd a) := by
    rintro _ ⟨x, rfl⟩ hx1
    refine ⟨x.toAdd, fun h0 => hx1 ?_, rfl⟩
    have : x = 1 := Multiplicative.ext h0
    rw [this, map_one]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv.symm, Nat.card_congr Multiplicative.toAdd,
      hK]
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Multiplicative.ofAdd (t ^ 2 * x.toAdd), by rw [← hh]; rfl⟩
    · rintro ⟨x, hx⟩
      refine ⟨Multiplicative.ofAdd ((t ^ 2)⁻¹ * x.toAdd), ?_⟩
      have h1 : h * ψ (Multiplicative.ofAdd ((t ^ 2)⁻¹ * x.toAdd)) * h⁻¹ = h * y * h⁻¹ := by
        rw [hh, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 ht0), one_mul]
        exact hx
      exact mul_left_cancel (mul_right_cancel h1)
  · intro π hπ hπ1 D hDU hDc π₀ hπ₀ hπ₀D
    obtain ⟨a, ha, rfl⟩ := hnonzero π hπ hπ1
    obtain ⟨x₀, rfl⟩ := hπ₀
    let Dadd : AddSubgroup K :=
      { carrier := {a | ψ (Multiplicative.ofAdd a) ∈ D}
        zero_mem' := by simp
        add_mem' := fun {a b} ha hb => by
          simpa [ofAdd_add, map_mul] using D.mul_mem ha hb
        neg_mem' := fun {a} ha => by simpa [ofAdd_neg, map_inv] using D.inv_mem ha }
    have hDadd : Nat.card Dadd = p := by
      rw [← hDc]
      refine Nat.card_eq_of_bijective (fun a => ⟨ψ (Multiplicative.ofAdd a.1), a.2⟩) ⟨?_, ?_⟩
      · intro a b hab
        exact Subtype.ext (congrArg Multiplicative.toAdd (hψ (congrArg Subtype.val hab)))
      · rintro ⟨d, hd⟩
        obtain ⟨x, rfl⟩ := hDU hd
        exact ⟨⟨x.toAdd, hd⟩, rfl⟩
    have ha₀ : x₀.toAdd ∉ Dadd := hπ₀D
    obtain ⟨k, d, hd, hk⟩ := exists_pow_sq_mul_mem_coset hp2 hK ht hgen ha hDadd ha₀
    refine ⟨k, ψ (Multiplicative.ofAdd d), hd, ?_⟩
    rw [iter, hk, ofAdd_add, map_mul]
    rfl
  · intro π hπ hπ1
    obtain ⟨a, ha, rfl⟩ := hnonzero π hπ hπ1
    have := hne 1 le_rfl (by norm_num) a ha
    simpa using this
  · intro π hπ hπ1
    obtain ⟨a, ha, rfl⟩ := hnonzero π hπ hπ1
    exact hne 2 (by norm_num) le_rfl a ha

end Torus

section Claim

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_of_commute {X Y : Subgroup G} (h : ∀ y ∈ Y, ∀ x ∈ X, y * x = x * y) :
    Y ≤ normalizer (X : Set G) := fun y hy =>
  centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun x hx => (h y hy x hx).symm)

omit [Finite G] in
theorem exists_mul_of_mem_sup_of_commute {X Y : Subgroup G}
    (h : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) {g : G} (hg : g ∈ X ⊔ Y) :
    ∃ x ∈ X, ∃ y ∈ Y, g = x * y := by
  let S : Subgroup G :=
    { carrier := {g | ∃ x ∈ X, ∃ y ∈ Y, g = x * y}
      one_mem' := ⟨1, X.one_mem, 1, Y.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨x, hx, y, hy, rfl⟩ ⟨x', hx', y', hy', rfl⟩
        refine ⟨x * x', X.mul_mem hx hx', y * y', Y.mul_mem hy hy', ?_⟩
        calc x * y * (x' * y') = x * (y * x') * y' := by group
          _ = x * (x' * y) * y' := by rw [← h x' hx' y hy]
          _ = x * x' * (y * y') := by group
      inv_mem' := by
        rintro _ ⟨x, hx, y, hy, rfl⟩
        refine ⟨x⁻¹, X.inv_mem hx, y⁻¹, Y.inv_mem hy, ?_⟩
        have hc : Commute x⁻¹ y⁻¹ := (show Commute x y from h x hx y hy).inv_inv
        exact (mul_inv_rev x y).trans hc.eq.symm }
  have : X ⊔ Y ≤ S := sup_le (fun x hx => ⟨x, hx, 1, Y.one_mem, by simp⟩)
    (fun y hy => ⟨1, X.one_mem, y, hy, by simp⟩)
  exact this hg

omit [Finite G] in
theorem isElemAbelian_sup_of_commute {p : ℕ} {A B : Subgroup G} (hA : IsElemAbelian p A)
    (hB : IsElemAbelian p B) (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsElemAbelian p (A ⊔ B) := CFSG.Open.IsElemAbelian.sup_of_commute hA hB h

@[expose] def IsFixedPointFree (T A : Subgroup G) : Prop :=
  T ⊓ centralizer (A : Set G) = ⊥

omit [Finite G] in
theorem IsFixedPointFree.mono {T A B : Subgroup G} (h : IsFixedPointFree T A) (hAB : A ≤ B) :
    IsFixedPointFree T B := by
  unfold IsFixedPointFree at h ⊢
  exact le_bot_iff.mp (h ▸ inf_le_inf_left T (Subgroup.centralizer_le hAB))

omit [Finite G] in
theorem IsFixedPointFree.map_conj_iff {T A : Subgroup G} {g : G}
    (hg : g ∈ normalizer (T : Set G)) :
    IsFixedPointFree T (A.map (MulAut.conj g).toMonoidHom) ↔ IsFixedPointFree T A := by
  have hT : T.map (MulAut.conj g).toMonoidHom = T := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have hC := CFSG.RankThreeCoreUniqueness.Helpers.centralizer_map_automorphism A (MulAut.conj g)
  have key : T ⊓ centralizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
      (T ⊓ centralizer (A : Set G)).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective, hT, hC]
  unfold IsFixedPointFree
  rw [key, Subgroup.map_eq_bot_iff_of_injective _
    (show Function.Injective (MulAut.conj g).toMonoidHom from (MulAut.conj g).injective)]

theorem eq_zpowers_of_card_eq_prime {p : ℕ} [hp : Fact p.Prime] {ℓ : Subgroup G}
    (hℓ : Nat.card ℓ = p) {b : G} (hb : b ∈ ℓ) (hb1 : b ≠ 1) : ℓ = zpowers b := by
  have h1 : orderOf b ∣ p := by
    have := orderOf_dvd_natCard (⟨b, hb⟩ : ℓ)
    rwa [Subgroup.orderOf_mk, hℓ] at this
  have hord : orderOf b = p := by
    rcases (Nat.dvd_prime hp.out).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hb1
    · exact h
  exact (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hb)
    (by rw [Nat.card_zpowers, hord, hℓ])).symm

theorem eq_or_le_of_isFixedPointFree {p : ℕ} [hp : Fact p.Prime] {E U X T : Subgroup G} {h : G}
    (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3) (hUE : U ≤ E) (hXE : X ≤ E)
    (hXc : Nat.card X = p) (hUX : Disjoint U X) (hT : IsFieldTorus p U h)
    (hhX : ∀ ξ ∈ X, h * ξ = ξ * h) (hhT : h ∈ normalizer (T : Set G))
    (hXfpf : IsFixedPointFree T X)
    (hact : ∀ B₀ : Subgroup G, B₀ ≤ E → Nat.card B₀ = p ^ 2 →
      ∃ B : Subgroup G, B ≤ E ∧ Nat.card B = p ^ 2 ∧ B ≠ B₀ ∧ ¬ IsFixedPointFree T B)
    {ℓ : Subgroup G} (hℓE : ℓ ≤ E) (hℓc : Nat.card ℓ = p) (hℓ : IsFixedPointFree T ℓ) :
    ℓ = X ∨ ℓ ≤ U := by
  by_contra hcon
  obtain ⟨hℓX, hℓU⟩ := not_or.mp hcon
  have hp1 : 1 < p := hp.out.one_lt
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hUc := hT.card_eq
  have hsupUX : U ⊔ X = E := by
    have hc1 := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer U X
      (le_normalizer_of_commute fun x hx u hu => hcomm x (hXE hx) u (hUE hu)) hUX
    refine Subgroup.eq_of_le_of_card_ge (sup_le hUE hXE) ?_
    rw [hEc, hc1, hUc, hXc, pow_succ]
  have hℓne : ℓ ≠ ⊥ := fun h0 => by
    rw [h0, Subgroup.card_bot] at hℓc
    omega
  obtain ⟨⟨b, hbℓ⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hℓne
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hℓb : ℓ = zpowers b := eq_zpowers_of_card_eq_prime hℓc hbℓ hb1'
  obtain ⟨π, hπU, ξ, hξX, hbπξ⟩ := exists_mul_of_mem_sup_of_commute
    (fun u hu x hx => hcomm u (hUE hu) x (hXE hx)) (hsupUX ▸ hℓE hbℓ)
  have hξ1 : ξ ≠ 1 := by
    rintro rfl
    apply hℓU
    rw [hℓb, zpowers_le, hbπξ, mul_one]
    exact hπU
  have hXξ : X = zpowers ξ := eq_zpowers_of_card_eq_prime hXc hξX hξ1
  have hπ1 : π ≠ 1 := by
    rintro rfl
    apply hℓX
    rw [hℓb, hbπξ, one_mul, hXξ]
  obtain ⟨B, hBE, hBc, hBU, hBact⟩ := hact U hUE hUc
  have hξB : ξ ∉ B := by
    intro hξB
    exact hBact (hXfpf.mono (by rw [hXξ, zpowers_le]; exact hξB))
  have hBUcomm : ∀ u ∈ U, ∀ β ∈ B, u * β = β * u := fun u hu β hβ =>
    hcomm u (hUE hu) β (hBE hβ)
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer (A := U)
    (B := B) (le_normalizer_of_commute fun β hβ u hu => (hBUcomm u hu β hβ).symm)
  rw [hUc, hBc] at hprod
  have hDc : Nat.card (U ⊓ B : Subgroup G) = p := by
    have h1 : Nat.card (U ⊓ B : Subgroup G) ∣ p ^ 2 :=
      hUc ▸ Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow hp.out).mp h1
    have hNle : Nat.card (U ⊔ B : Subgroup G) ≤ p ^ 3 :=
      Nat.le_of_dvd (by positivity) (hEc ▸ Subgroup.card_dvd_of_le (sup_le hUE hBE))
    interval_cases j
    · rw [pow_zero] at hj'
      rw [hj', mul_one] at hprod
      have : p ^ 3 < p ^ 2 * p ^ 2 := by
        rw [← pow_add]
        exact Nat.pow_lt_pow_right hp1 (by norm_num)
      omega
    · rwa [pow_one] at hj'
    · exfalso
      apply hBU
      have h2 : U ⊓ B = U := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hj', hUc])
      exact (Subgroup.eq_of_le_of_card_ge (inf_eq_left.mp h2) (by rw [hBc, hUc])).symm
  have hsupUB : U ⊔ B = E := by
    have hN : Nat.card (U ⊔ B : Subgroup G) = p ^ 3 := by
      rw [hDc] at hprod
      have : Nat.card (U ⊔ B : Subgroup G) * p = p ^ 3 * p := by
        rw [hprod]
        ring
      exact Nat.eq_of_mul_eq_mul_right (by omega) this
    exact Subgroup.eq_of_le_of_card_ge (sup_le hUE hBE) (by rw [hN, hEc])
  obtain ⟨u, huU, β, hβB, hξuβ⟩ := exists_mul_of_mem_sup_of_commute hBUcomm
    (hsupUB ▸ hXE hξX)
  have hπ₁ξ : u⁻¹ * ξ = β := by rw [hξuβ]; group
  have hπ₁D : u⁻¹ ∉ (U ⊓ B : Subgroup G) := by
    intro hmem
    apply hξB
    rw [hξuβ]
    exact B.mul_mem (by simpa using B.inv_mem hmem.2) hβB
  obtain ⟨k, d, hdD, hkd⟩ := hT.coset π hπU hπ1 (U ⊓ B) inf_le_left hDc u⁻¹ (U.inv_mem huU) hπ₁D
  have hgξ : h ^ k * ξ * (h ^ k)⁻¹ = ξ := by
    have hc : Commute (h ^ k) ξ := (show Commute h ξ from hhX ξ hξX).pow_left k
    rw [hc.eq]
    group
  have hgb : h ^ k * b * (h ^ k)⁻¹ ∈ B := by
    have h1 : h ^ k * b * (h ^ k)⁻¹ = (h ^ k * π * (h ^ k)⁻¹) * (h ^ k * ξ * (h ^ k)⁻¹) := by
      rw [hbπξ]
      group
    rw [h1, hkd, hgξ]
    have hdU : d ∈ U := hdD.1
    have hdcomm : u⁻¹ * d = d * u⁻¹ :=
      hcomm _ (hUE (U.inv_mem huU)) _ (hUE hdU)
    have h2 : u⁻¹ * d * ξ = d * (u⁻¹ * ξ) := by rw [hdcomm]; group
    rw [h2, hπ₁ξ]
    exact B.mul_mem hdD.2 hβB
  set B'' : Subgroup G := B.map (MulAut.conj (h ^ k)⁻¹).toMonoidHom with hB''
  have hbB'' : b ∈ B'' := ⟨h ^ k * b * (h ^ k)⁻¹, hgb, by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group⟩
  have hℓB'' : ℓ ≤ B'' := by rw [hℓb, zpowers_le]; exact hbB''
  have hg : (h ^ k)⁻¹ ∈ normalizer (T : Set G) :=
    (Subgroup.normalizer (T : Set G)).inv_mem ((Subgroup.normalizer (T : Set G)).pow_mem hhT k)
  exact ((IsFixedPointFree.map_conj_iff hg).not.mpr hBact) (hℓ.mono hℓB'')

theorem sup_eq_of_card_eq_prime {p : ℕ} [hp : Fact p.Prime] {A B U : Subgroup G}
    (hA : Nat.card A = p) (hB : Nat.card B = p) (hAB : A ≠ B) (hAU : A ≤ U) (hBU : B ≤ U)
    (hU : Nat.card U = p ^ 2) : A ⊔ B = U := by
  have hp1 : 1 < p := hp.out.one_lt
  have h1 : p ∣ Nat.card (A ⊔ B : Subgroup G) := hA ▸ Subgroup.card_dvd_of_le le_sup_left
  have h2 : Nat.card (A ⊔ B : Subgroup G) ∣ p ^ 2 :=
    hU ▸ Subgroup.card_dvd_of_le (sup_le hAU hBU)
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow hp.out).mp h2
  interval_cases j
  · rw [pow_zero] at hj'
    rw [hj'] at h1
    exact absurd (Nat.le_of_dvd one_pos h1) (by omega)
  · exfalso
    rw [pow_one] at hj'
    have hAeq : A = A ⊔ B := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hj', hA])
    have hBA : B ≤ A := hAeq ▸ le_sup_right
    exact hAB (Subgroup.eq_of_le_of_card_ge hBA (by rw [hA, hB])).symm
  · exact Subgroup.eq_of_le_of_card_ge (sup_le hAU hBU) (by rw [hj', hU])

structure IsFPFPoint (p : ℕ) (E T : Subgroup G) (x : G) : Prop where
  mem : x ∈ E
  orderOf_eq : orderOf x = p
  fpf : IsFixedPointFree T (zpowers x)
  exists_torus : ∃ (U : Subgroup G) (h : G), U ≤ E ∧ Disjoint U (zpowers x) ∧
    IsFieldTorus p U h ∧ h * x = x * h ∧ h ∈ normalizer (T : Set G)

theorem zpowers_eq_of_isFPFPoint {p : ℕ} [hp : Fact p.Prime] {E T : Subgroup G} {x y : G}
    (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3)
    (hact : ∀ B₀ : Subgroup G, B₀ ≤ E → Nat.card B₀ = p ^ 2 →
      ∃ B : Subgroup G, B ≤ E ∧ Nat.card B = p ^ 2 ∧ B ≠ B₀ ∧ ¬ IsFixedPointFree T B)
    (hx : IsFPFPoint p E T x) (hy : IsFPFPoint p E T y) : zpowers y = zpowers x := by
  by_contra hxy
  obtain ⟨Ux, ax, hUxE, hUxX, hTx, hax, haxT⟩ := hx.exists_torus
  obtain ⟨Uy, ay, hUyE, hUyY, hTy, hay, hayT⟩ := hy.exists_torus
  have hp1 : 1 < p := hp.out.one_lt
  have hXc : Nat.card (zpowers x) = p := by rw [Nat.card_zpowers, hx.orderOf_eq]
  have hYc : Nat.card (zpowers y) = p := by rw [Nat.card_zpowers, hy.orderOf_eq]
  have hXE : zpowers x ≤ E := zpowers_le.mpr hx.mem
  have hYE : zpowers y ≤ E := zpowers_le.mpr hy.mem
  have cx := fun {ℓ : Subgroup G} (h1 : ℓ ≤ E) (h2 : Nat.card ℓ = p) (h3 : IsFixedPointFree T ℓ) =>
    eq_or_le_of_isFixedPointFree hE hEc hUxE hXE hXc hUxX hTx
      (fun ξ hξ => by
        obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hξ
        exact (Commute.zpow_right (show Commute ax x from hax) n).eq) haxT hx.fpf hact h1 h2 h3
  have cy := fun {ℓ : Subgroup G} (h1 : ℓ ≤ E) (h2 : Nat.card ℓ = p) (h3 : IsFixedPointFree T ℓ) =>
    eq_or_le_of_isFixedPointFree hE hEc hUyE hYE hYc hUyY hTy
      (fun ξ hξ => by
        obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hξ
        exact (Commute.zpow_right (show Commute ay y from hay) n).eq) hayT hy.fpf hact h1 h2 h3
  have hxUy : zpowers x ≤ Uy :=
    (cy hXE hXc hx.fpf).resolve_left fun h => hxy h.symm
  have hxUy' : x ∈ Uy := hxUy (mem_zpowers x)
  have hx1 : x ≠ 1 := by
    intro h
    have := hx.orderOf_eq
    rw [h, orderOf_one] at this
    omega
  have hxUx : x ∉ Ux := fun h =>
    hx1 (Subgroup.disjoint_def.mp hUxX h (mem_zpowers x))
  set x₁ : G := ay * x * ay⁻¹ with hx₁
  set x₂ : G := ay * x₁ * ay⁻¹ with hx₂
  have hayN := hTy.mem_normalizer
  have hx₁Uy : x₁ ∈ Uy := (Subgroup.mem_normalizer_iff.mp hayN x).mp hxUy'
  have hx₂Uy : x₂ ∈ Uy := (Subgroup.mem_normalizer_iff.mp hayN x₁).mp hx₁Uy
  have hconj : ∀ a : G, orderOf (ay * a * ay⁻¹) = orderOf a := fun a => by
    have := orderOf_injective (MulAut.conj ay).toMonoidHom (MulAut.conj ay).injective a
    simpa using this
  have hx₁1 : x₁ ≠ 1 := fun h => by
    have := hconj x
    rw [← hx₁, h, orderOf_one, hx.orderOf_eq] at this
    omega
  have hzp : ∀ a : G, zpowers (ay * a * ay⁻¹) = (zpowers a).map (MulAut.conj ay).toMonoidHom :=
    fun a => (MonoidHom.map_zpowers (MulAut.conj ay).toMonoidHom a).symm
  have hfpf₁ : IsFixedPointFree T (zpowers x₁) := by
    rw [hx₁, hzp]
    exact (IsFixedPointFree.map_conj_iff hayT).mpr hx.fpf
  have hfpf₂ : IsFixedPointFree T (zpowers x₂) := by
    rw [hx₂, hzp]
    exact (IsFixedPointFree.map_conj_iff hayT).mpr hfpf₁
  have hc₁ : Nat.card (zpowers x₁) = p := by rw [Nat.card_zpowers, hconj x, hx.orderOf_eq]
  have hc₂ : Nat.card (zpowers x₂) = p := by rw [Nat.card_zpowers, hconj x₁, hconj x,
    hx.orderOf_eq]
  have hne₁ : zpowers x ≠ zpowers x₁ := hTy.zpowers_ne_one x hxUy' hx1
  have hne₂ : zpowers x ≠ zpowers x₂ := by
    have := hTy.zpowers_ne_two x hxUy' hx1
    have e2 : ay ^ 2 * x * (ay ^ 2)⁻¹ = x₂ := by
      rw [hx₂, hx₁, pow_two, mul_inv_rev]
      simp only [mul_assoc]
    rwa [e2] at this
  have hne₁₂ : zpowers x₁ ≠ zpowers x₂ := hTy.zpowers_ne_one x₁ hx₁Uy hx₁1
  have hl₁ : zpowers x₁ ≤ Ux :=
    (cx ((zpowers_le.mpr hx₁Uy).trans hUyE) hc₁ hfpf₁).resolve_left fun h => hne₁ h.symm
  have hl₂ : zpowers x₂ ≤ Ux :=
    (cx ((zpowers_le.mpr hx₂Uy).trans hUyE) hc₂ hfpf₂).resolve_left fun h => hne₂ h.symm
  have hUx : zpowers x₁ ⊔ zpowers x₂ = Ux :=
    sup_eq_of_card_eq_prime hc₁ hc₂ hne₁₂ hl₁ hl₂ hTx.card_eq
  have hUy : zpowers x₁ ⊔ zpowers x₂ = Uy :=
    sup_eq_of_card_eq_prime hc₁ hc₂ hne₁₂ (zpowers_le.mpr hx₁Uy) (zpowers_le.mpr hx₂Uy)
      hTy.card_eq
  exact hxUx (hUx ▸ hUy ▸ hxUy')

end Claim

end CFSG.LocalAnalysis.RankThreeTheoremC
