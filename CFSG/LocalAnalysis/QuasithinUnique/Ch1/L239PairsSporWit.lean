module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporGoodE
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

section Sylow

variable {Y : Type*} [Group Y] [Finite Y]

theorem exists_conj_of_prime_order {r m : ℕ} [Fact r.Prime] (hY : Nat.card Y = r * m)
    (hm : ¬ r ∣ m) {b b₀ : Y} (hb : orderOf b = r) (hb₀ : orderOf b₀ = r) :
    ∃ g : Y, g * b₀ * g⁻¹ ∈ Subgroup.zpowers b := by
  have hsyl : ∀ c : Y, orderOf c = r →
      IsPGroup r (Subgroup.zpowers c) ∧ ¬ r ∣ (Subgroup.zpowers c).index := by
    intro c hc
    have hcard : Nat.card (Subgroup.zpowers c) = r := by rw [Nat.card_zpowers, hc]
    refine ⟨IsPGroup.of_card (n := 1) (by rw [hcard, pow_one]), ?_⟩
    have h := Subgroup.card_mul_index (Subgroup.zpowers c)
    rw [hcard, hY] at h
    have hr : 0 < r := (Fact.out : r.Prime).pos
    have : (Subgroup.zpowers c).index = m := Nat.eq_of_mul_eq_mul_left hr h
    rw [this]
    exact hm
  obtain ⟨hP, hPi⟩ := hsyl b hb
  obtain ⟨hP₀, hP₀i⟩ := hsyl b₀ hb₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y (hP₀.toSylow hP₀i) (hP.toSylow hPi)
  refine ⟨g, ?_⟩
  have h : ((g • hP₀.toSylow hP₀i : Sylow r Y) : Set Y) = ((hP.toSylow hPi : Sylow r Y) : Set Y) :=
    congrArg (fun P : Sylow r Y => ((P : Subgroup Y) : Set Y)) hg
  rw [Sylow.coe_smul] at h
  have hmem : (MulAut.conj g) b₀ ∈ ((hP.toSylow hPi : Sylow r Y) : Set Y) := by
    rw [← h]
    exact Set.smul_mem_smul_set (Subgroup.mem_zpowers b₀)
  exact hmem

theorem exists_noncomm_of_prime_order {r m : ℕ} [Fact r.Prime] (hY : Nat.card Y = r * m)
    (hm : ¬ r ∣ m) (Q : Subgroup Y) [Q.Normal] {b₀ : Y} (hb₀ : orderOf b₀ = r)
    (h₀ : ∃ q ∈ Q, q * b₀ ≠ b₀ * q) {b : Y} (hb : orderOf b = r) : ∃ q ∈ Q, q * b ≠ b * q := by
  by_contra hcon'
  have hcon : ∀ q ∈ Q, q * b = b * q := fun q hq => by
    by_contra h
    exact hcon' ⟨q, hq, h⟩
  obtain ⟨g, hg⟩ := exists_conj_of_prime_order hY hm hb hb₀
  obtain ⟨q₀, hq₀, hne⟩ := h₀
  have hq : g * q₀ * g⁻¹ ∈ Q := Subgroup.Normal.conj_mem inferInstance q₀ hq₀ g
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hg
  have hc : (g * q₀ * g⁻¹) * (g * b₀ * g⁻¹) = (g * b₀ * g⁻¹) * (g * q₀ * g⁻¹) := by
    rw [← hk]
    exact ((show Commute (g * q₀ * g⁻¹) b from hcon _ hq).zpow_right k).eq
  apply hne
  have h2 : g * (q₀ * b₀) * g⁻¹ = g * (b₀ * q₀) * g⁻¹ := by
    calc g * (q₀ * b₀) * g⁻¹ = (g * q₀ * g⁻¹) * (g * b₀ * g⁻¹) := by group
      _ = (g * b₀ * g⁻¹) * (g * q₀ * g⁻¹) := hc
      _ = g * (b₀ * q₀) * g⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h2)

theorem hE_transfer {m : ℕ} (hY : Nat.card Y = 3 * m) (hm : ¬ 3 ∣ m) (Q : Subgroup Y) [Q.Normal]
    {b₀ : Y} (hb₀ : orderOf b₀ = 3)
    (h₀ : ∃ x ∈ ⁅Q, Subgroup.zpowers b₀⁆, ∃ y ∈ ⁅Q, Subgroup.zpowers b₀⁆, x * y ≠ y * x ∨ x * x ≠ 1)
    {b : Y} (hb : orderOf b = 3) :
    ∃ x ∈ ⁅Q, Subgroup.zpowers b⁆, ∃ y ∈ ⁅Q, Subgroup.zpowers b⁆, x * y ≠ y * x ∨ x * x ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_conj_of_prime_order hY hm hb hb₀
  obtain ⟨x, hx, y, hy, hxy⟩ := h₀
  set f : Y →* Y := (MulAut.conj g).toMonoidHom with hf
  have hmap : ⁅Q, Subgroup.zpowers b₀⁆.map f ≤ ⁅Q, Subgroup.zpowers b⁆ := by
    rw [Subgroup.map_commutator]
    refine Subgroup.commutator_mono ?_ ?_
    · rintro _ ⟨q, hq, rfl⟩
      exact Subgroup.Normal.conj_mem inferInstance q hq g
    · rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
      exact hg
  have hinj : Function.Injective f := (MulAut.conj g).injective
  refine ⟨f x, hmap ⟨x, hx, rfl⟩, f y, hmap ⟨y, hy, rfl⟩, ?_⟩
  rcases hxy with h | h
  · left
    intro h'
    apply h
    apply hinj
    rw [map_mul, map_mul, h']
  · right
    intro h'
    apply h
    apply hinj
    rw [map_mul, h', map_one]

end Sylow

section Witnesses

theorem prime_dvd_two_pow_mul {a p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hr2 : r ≠ 2)
    (h : r ∣ 2 ^ a * 3 * p) : r = 3 ∨ r = p := by
  rcases (Nat.Prime.dvd_mul hr).1 h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hr).1 h1 with h2 | h2
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h2)) hr2
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h2)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr hp).1 h1)

theorem goodLocal_of_noncentral {X : Type*} [Group X] (Y : Subgroup X) [Finite ↥Y]
    (hE : ∀ b : ↥Y, orderOf b = 3 → ∃ x ∈ ⁅CFSG.pCore 2 ↥Y, Subgroup.zpowers b⁆,
      ∃ y ∈ ⁅CFSG.pCore 2 ↥Y, Subgroup.zpowers b⁆, x * y ≠ y * x ∨ x * x ≠ 1)
    (hnc : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → ∀ c : ↥Y, orderOf c = r →
      ∃ q ∈ CFSG.pCore 2 ↥Y, q * c ≠ c * q) : GoodLocal Y := by
  set Q : Subgroup ↥Y := CFSG.pCore 2 ↥Y with hQ
  have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup
  have hcent : ∀ y : ↥Y, (∀ q ∈ Q, y * q = q * y) → y ∈ Q := by
    intro y hy
    set C : Subgroup ↥Y := Subgroup.centralizer (Q : Set ↥Y) with hC
    have hCn : C.Normal := Subgroup.normal_centralizer
    have hyC : y ∈ C := by
      rw [hC, Subgroup.mem_centralizer_iff]
      intro q hq
      exact (hy q hq).symm
    have hC2 : IsPGroup 2 C := by
      rw [IsPGroup.iff_orderOf]
      intro g
      have hgpos : orderOf g ≠ 0 := (orderOf_pos g).ne'
      refine ⟨(orderOf g).primeFactorsList.length,
        Nat.eq_prime_pow_of_unique_prime_dvd hgpos fun {d} hd hdvd => ?_⟩
      by_contra hd2
      have hcord : orderOf ((g : ↥Y) ^ (orderOf (g : ↥Y) / d)) = d := by
        apply orderOf_pow_orderOf_div (by rwa [Subgroup.orderOf_coe])
        rwa [Subgroup.orderOf_coe]
      have hcC : (g : ↥Y) ^ (orderOf (g : ↥Y) / d) ∈ C := C.pow_mem g.2 _
      have hcQ : ∀ q ∈ Q, q * ((g : ↥Y) ^ (orderOf (g : ↥Y) / d)) =
          ((g : ↥Y) ^ (orderOf (g : ↥Y) / d)) * q := fun q hq => by
        have := Subgroup.mem_centralizer_iff.1 hcC q hq
        exact this
      by_cases hd3 : d = 3
      · subst hd3
        obtain ⟨x, hx, y, hy, hxy⟩ := hE _ hcord
        have hbot : ⁅Q, Subgroup.zpowers ((g : ↥Y) ^ (orderOf (g : ↥Y) / 3))⁆ ≤ ⊥ := by
          rw [Subgroup.commutator_le]
          intro q hq z hz
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
          rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
          exact ((show Commute q ((g : ↥Y) ^ (orderOf (g : ↥Y) / 3)) from hcQ q hq).zpow_right
            k).eq
        have hx1 : x = 1 := Subgroup.mem_bot.1 (hbot hx)
        have hy1 : y = 1 := Subgroup.mem_bot.1 (hbot hy)
        rcases hxy with h | h
        · exact h (by rw [hx1, hy1])
        · exact h (by rw [hx1, mul_one])
      · obtain ⟨q, hq, hne'⟩ := hnc d hd hd2 hd3 _ hcord
        exact hne' (hcQ q hq)
    exact le_pCore_of_normal hC2 hyC
  exact GoodLocal.of_data_E Q hQ2 hcent hE

theorem pCoreOf_eq_map {X : Type*} [Group X] (Y : Subgroup X) :
    pCoreOf 2 Y = (CFSG.pCore 2 ↥Y).map Y.subtype := CFSG.openPCoreOf_eq_map_pCore 2 Y

theorem exists_lift_commutator {X : Type*} [Group X] (Y : Subgroup X) (b : ↥Y) {x : X}
    (hx : x ∈ ⁅pCoreOf 2 Y, Subgroup.zpowers (b : X)⁆) :
    ∃ x' ∈ ⁅CFSG.pCore 2 ↥Y, Subgroup.zpowers b⁆, (x' : X) = x := by
  have h : (⁅CFSG.pCore 2 ↥Y, Subgroup.zpowers b⁆).map Y.subtype =
      ⁅pCoreOf 2 Y, Subgroup.zpowers (b : X)⁆ := by
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers, pCoreOf_eq_map]
    rfl
  rw [← h] at hx
  obtain ⟨x', hx', rfl⟩ := hx
  exact ⟨x', hx', rfl⟩

theorem exists_witness3_lift {X : Type*} [Group X] (Y : Subgroup X)
    (w3 : ∃ b ∈ Y, orderOf b = 3 ∧ ∃ x ∈ ⁅pCoreOf 2 Y, Subgroup.zpowers b⁆,
      ∃ y ∈ ⁅pCoreOf 2 Y, Subgroup.zpowers b⁆, x * y ≠ y * x ∨ x * x ≠ 1) :
    ∃ b : ↥Y, orderOf b = 3 ∧ ∃ x ∈ ⁅CFSG.pCore 2 ↥Y, Subgroup.zpowers b⁆,
      ∃ y ∈ ⁅CFSG.pCore 2 ↥Y, Subgroup.zpowers b⁆, x * y ≠ y * x ∨ x * x ≠ 1 := by
  obtain ⟨b₀, hb₀Y, hb₀, x, hx, y, hy, hxy⟩ := w3
  refine ⟨⟨b₀, hb₀Y⟩, ?_, ?_⟩
  · rw [← Subgroup.orderOf_coe]
    exact hb₀
  obtain ⟨x', hx', rfl⟩ := exists_lift_commutator Y ⟨b₀, hb₀Y⟩ hx
  obtain ⟨y', hy', rfl⟩ := exists_lift_commutator Y ⟨b₀, hb₀Y⟩ hy
  refine ⟨x', hx', y', hy', ?_⟩
  rcases hxy with h | h
  · left
    intro h'
    exact h (congrArg Subtype.val h')
  · right
    intro h'
    exact h (congrArg Subtype.val h')

theorem goodLocal_of_witnesses {X : Type*} [Group X] (Y : Subgroup X) [Finite ↥Y] {a p : ℕ}
    (hp : p.Prime) (h5 : 5 ≤ p) (hcard : Nat.card ↥Y = 2 ^ a * 3 * p)
    (w3 : ∃ b ∈ Y, orderOf b = 3 ∧ ∃ x ∈ ⁅pCoreOf 2 Y, Subgroup.zpowers b⁆,
      ∃ y ∈ ⁅pCoreOf 2 Y, Subgroup.zpowers b⁆, x * y ≠ y * x ∨ x * x ≠ 1)
    (wp : ∃ b ∈ Y, orderOf b = p ∧ ∃ q ∈ pCoreOf 2 Y, q * b ≠ b * q) : GoodLocal Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact p.Prime := ⟨hp⟩
  have hm3 : Nat.card ↥Y = 3 * (2 ^ a * p) := by rw [hcard]; ring
  have hmp : Nat.card ↥Y = p * (2 ^ a * 3) := by rw [hcard]; ring
  have h3m : ¬ 3 ∣ 2 ^ a * p := by
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h1 | h1
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
        (Nat.prime_three.dvd_of_dvd_pow h1)
      omega
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h1
      omega
  have hpm : ¬ p ∣ 2 ^ a * 3 := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1)
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h1
      omega
  set Q : Subgroup ↥Y := CFSG.pCore 2 ↥Y with hQ
  obtain ⟨b₀, hb₀', hw3⟩ := exists_witness3_lift Y w3
  have hE : ∀ b : ↥Y, orderOf b = 3 → ∃ x ∈ ⁅Q, Subgroup.zpowers b⁆,
      ∃ y ∈ ⁅Q, Subgroup.zpowers b⁆, x * y ≠ y * x ∨ x * x ≠ 1 := fun b hb =>
    hE_transfer hm3 h3m Q hb₀' hw3 hb
  obtain ⟨c₀, hc₀Y, hc₀, q₀, hq₀, hne⟩ := wp
  have hwp : ∃ q ∈ Q, q * (⟨c₀, hc₀Y⟩ : ↥Y) ≠ (⟨c₀, hc₀Y⟩ : ↥Y) * q := by
    rw [pCoreOf_eq_map] at hq₀
    obtain ⟨q', hq', rfl⟩ := hq₀
    refine ⟨q', hq', fun h' => hne ?_⟩
    exact congrArg Subtype.val h'
  have hc₀' : orderOf (⟨c₀, hc₀Y⟩ : ↥Y) = p := by
    rw [← Subgroup.orderOf_coe]
    exact hc₀
  refine goodLocal_of_noncentral Y hE fun r hr hr2 hr3 c hc => ?_
  have hrY : r ∣ 2 ^ a * 3 * p := by
    rw [← hcard, ← hc]
    exact orderOf_dvd_natCard _
  rcases prime_dvd_two_pow_mul hp hr hr2 hrY with h | h
  · exact absurd h hr3
  · subst h
    have : Fact r.Prime := ⟨hr⟩
    exact exists_noncomm_of_prime_order hmp hpm Q hc₀' hwp hc

end Witnesses

end CFSG.QuasithinUnique.Vol2Native.L239
