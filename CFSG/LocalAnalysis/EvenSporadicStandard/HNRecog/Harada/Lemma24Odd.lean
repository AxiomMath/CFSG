module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24Defs
public import CFSG.GroupTheory.OddInversion

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup

open scoped commutatorElement

theorem normal_odd_le_zpowers {Y : Type} [Group Y] [Finite Y] {a t : Y}
    (ha : a ∈ Subgroup.center Y) (ha3 : orderOf a = 3) (ht : t ^ 2 = 1) {τ : Y → Prop}
    (hτ : ∀ s : Y, τ s → s ^ 2 = 1 → s ≠ 1 → ∃ y : Y, y * t * y⁻¹ = s)
    (hodd : ∀ N : Subgroup Y, N ≤ centralizer ({t} : Set Y) →
      (∀ c ∈ centralizer ({t} : Set Y), ∀ n ∈ N, c * n * c⁻¹ ∈ N) → Odd (Nat.card N) →
      N ≤ zpowers a)
    (hW : ∃ s ∈ tInvolutions t τ, s ∈ ⁅Wsub t τ, Wsub t τ⁆) :
    ∀ N : Subgroup Y, N.Normal → Odd (Nat.card N) → N ≤ zpowers a := by
  obtain ⟨s, hs, hsc⟩ := hW
  have ht1 : t ≠ 1 := by
    intro ht1eq
    obtain ⟨y, hy⟩ := hτ s hs.2.2.2 hs.2.1 hs.2.2.1
    have h1 : (1 : Y) = s := by simpa [ht1eq] using hy
    exact hs.2.2.1 h1.symm
  have ht2 : orderOf t = 2 := orderOf_eq_prime (p := 2) ht ht1
  have hcent : ∀ (y : Y) (k : ℤ), a ^ k * y = y * a ^ k := by
    intro y k
    have hcomm : Commute y a := Subgroup.mem_center_iff.mp ha y
    exact (hcomm.zpow_right k).eq.symm
  have hconj_a : ∀ (y : Y) (k : ℤ), y * a ^ k * y⁻¹ = a ^ k := by
    intro y k
    rw [← hcent y k]; group
  intro N hNnorm hNodd
  have hC_le : (N ⊓ centralizer ({t} : Set Y)) ≤ zpowers a := by
    refine hodd (N ⊓ centralizer ({t} : Set Y)) inf_le_right ?_ ?_
    · intro c hc n hn
      exact ⟨hNnorm.conj_mem n hn.1 c,
        (centralizer ({t} : Set Y)).mul_mem
          ((centralizer ({t} : Set Y)).mul_mem hc hn.2)
          ((centralizer ({t} : Set Y)).inv_mem hc)⟩
    · exact Odd.of_dvd_nat hNodd (Subgroup.card_dvd_of_le inf_le_left)
  have htN : t ∈ Subgroup.normalizer (N : Set Y) := by
    haveI : N.Normal := hNnorm
    rw [Subgroup.normalizer_eq_top]
    trivial
  have hINVt : ∀ x ∈ N, ∃ k : ℤ, t * x * t⁻¹ = x⁻¹ * a ^ k := by
    intro x hx
    have hbij := CFSG.OddInversion.fixed_mul_inverted_bijOn (A := N) hNodd ht2 htN
    obtain ⟨⟨c, j⟩, hmem, hcj⟩ := hbij.surjOn hx
    have hc : c ∈ N ⊓ centralizer ({t} : Set Y) := hmem.1
    have hj : j ∈ CFSG.OddInversion.invertedSet N t := hmem.2
    have hcA : c ∈ zpowers a := hC_le hc
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hcA
    have hct : t * c * t⁻¹ = c := by
      have hcomm : c * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp hc.2
      rw [← hcomm]; group
    have hjt : t * j * t⁻¹ = j⁻¹ := (CFSG.OddInversion.mem_invertedSet.mp hj).2
    refine ⟨2 * m, ?_⟩
    rw [← hcj]
    calc t * (c * j) * t⁻¹
        = (t * c * t⁻¹) * (t * j * t⁻¹) := by group
      _ = c * j⁻¹ := by rw [hct, hjt]
      _ = (c * j)⁻¹ * a ^ (2 * m) := by
            rw [mul_inv_rev, ← hm, ← zpow_neg, mul_assoc, ← zpow_add,
              show -m + 2 * m = m by ring, ← hcent j⁻¹ m]
  let Kp : Y → Prop := fun g => ∀ x ∈ N, ∃ k : ℤ, g * x * g⁻¹ = x * a ^ k
  let Km : Y → Prop := fun g => ∀ x ∈ N, ∃ k : ℤ, g * x * g⁻¹ = x⁻¹ * a ^ k
  have hKp_one : Kp 1 := by
    intro x _
    exact ⟨0, by simp⟩
  have hKp_mul : ∀ {g h : Y}, Kp g → Kp h → Kp (g * h) := by
    intro g h hg hh x hx
    obtain ⟨k1, hk1⟩ := hh x hx
    obtain ⟨k2, hk2⟩ := hg (h * x * h⁻¹) (hNnorm.conj_mem x hx h)
    refine ⟨k1 + k2, ?_⟩
    rw [show (g * h) * x * (g * h)⁻¹ = g * (h * x * h⁻¹) * g⁻¹ by group,
      hk2, hk1, mul_assoc, zpow_add]
  have hKpKm : ∀ {g h : Y}, Kp g → Km h → Km (g * h) := by
    intro g h hg hh x hx
    obtain ⟨k1, hk1⟩ := hh x hx
    obtain ⟨k2, hk2⟩ := hg (h * x * h⁻¹) (hNnorm.conj_mem x hx h)
    refine ⟨k1 + k2, ?_⟩
    rw [show (g * h) * x * (g * h)⁻¹ = g * (h * x * h⁻¹) * g⁻¹ by group,
      hk2, hk1, mul_assoc, zpow_add]
  have hKmKp : ∀ {g h : Y}, Km g → Kp h → Km (g * h) := by
    intro g h hg hh x hx
    obtain ⟨k1, hk1⟩ := hh x hx
    obtain ⟨k2, hk2⟩ := hg (h * x * h⁻¹) (hNnorm.conj_mem x hx h)
    refine ⟨k2 - k1, ?_⟩
    rw [show (g * h) * x * (g * h)⁻¹ = g * (h * x * h⁻¹) * g⁻¹ by group,
      hk2, hk1]
    calc (x * a ^ k1)⁻¹ * a ^ k2
        = a ^ (-k1) * x⁻¹ * a ^ k2 := by rw [mul_inv_rev, ← zpow_neg]
      _ = x⁻¹ * a ^ (-k1) * a ^ k2 := by rw [hcent x⁻¹ (-k1)]
      _ = x⁻¹ * a ^ (k2 - k1) := by
            rw [mul_assoc, ← zpow_add, show -k1 + k2 = k2 - k1 by ring]
  have hKmKm : ∀ {g h : Y}, Km g → Km h → Kp (g * h) := by
    intro g h hg hh x hx
    obtain ⟨k1, hk1⟩ := hh x hx
    obtain ⟨k2, hk2⟩ := hg (h * x * h⁻¹) (hNnorm.conj_mem x hx h)
    refine ⟨k2 - k1, ?_⟩
    rw [show (g * h) * x * (g * h)⁻¹ = g * (h * x * h⁻¹) * g⁻¹ by group,
      hk2, hk1]
    calc (x⁻¹ * a ^ k1)⁻¹ * a ^ k2
        = a ^ (-k1) * x * a ^ k2 := by rw [mul_inv_rev, ← zpow_neg, inv_inv]
      _ = x * a ^ (-k1) * a ^ k2 := by rw [hcent x (-k1)]
      _ = x * a ^ (k2 - k1) := by
            rw [mul_assoc, ← zpow_add, show -k1 + k2 = k2 - k1 by ring]
  have hKp_inv : ∀ {g : Y}, Kp g → Kp (g⁻¹) := by
    intro g hg x hx
    rw [inv_inv]
    set y : Y := g⁻¹ * x * g with hy_def
    have hyN : y ∈ N := by
      rw [hy_def]
      simpa using hNnorm.conj_mem x hx g⁻¹
    obtain ⟨k, hk⟩ := hg y hyN
    have hgy : g * y * g⁻¹ = x := by rw [hy_def]; group
    rw [hgy] at hk
    refine ⟨-k, ?_⟩
    have hy : y = x * a ^ (-k) := by
      rw [hk, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
    exact hy
  have hKm_inv : ∀ {g : Y}, Km g → Km (g⁻¹) := by
    intro g hg x hx
    rw [inv_inv]
    set y : Y := g⁻¹ * x * g with hy_def
    have hyN : y ∈ N := by
      rw [hy_def]
      simpa using hNnorm.conj_mem x hx g⁻¹
    obtain ⟨k, hk⟩ := hg y hyN
    have hgy : g * y * g⁻¹ = x := by rw [hy_def]; group
    rw [hgy] at hk
    refine ⟨k, ?_⟩
    have hyinv : y⁻¹ = x * a ^ (-k) := by
      rw [hk, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
    have hy : y = x⁻¹ * a ^ k := by
      rw [← inv_inv y, hyinv, mul_inv_rev, ← zpow_neg, neg_neg, hcent x⁻¹ k]
    exact hy
  let Kplus : Subgroup Y :=
    { carrier := {g : Y | Kp g}
      mul_mem' := fun hg hh => hKp_mul hg hh
      one_mem' := hKp_one
      inv_mem' := fun hg => hKp_inv hg }
  let K : Subgroup Y :=
    { carrier := {g : Y | Kp g ∨ Km g}
      mul_mem' := by
        intro g h hg hh
        rcases hg with hg | hg <;> rcases hh with hh | hh
        · exact Or.inl (hKp_mul hg hh)
        · exact Or.inr (hKpKm hg hh)
        · exact Or.inr (hKmKp hg hh)
        · exact Or.inl (hKmKm hg hh)
      one_mem' := Or.inl hKp_one
      inv_mem' := by
        intro g hg
        rcases hg with hg | hg
        · exact Or.inl (hKp_inv hg)
        · exact Or.inr (hKm_inv hg) }
  have hKm_tau : ∀ s : Y, τ s → s ^ 2 = 1 → s ≠ 1 → Km s := by
    intro s hτs hs2 hs1 x hx
    obtain ⟨y, hy⟩ := hτ s hτs hs2 hs1
    have hmem : y⁻¹ * x * y ∈ N := by simpa using hNnorm.conj_mem x hx y⁻¹
    obtain ⟨k, hk⟩ := hINVt (y⁻¹ * x * y) hmem
    refine ⟨k, ?_⟩
    rw [← hy]
    calc (y * t * y⁻¹) * x * (y * t * y⁻¹)⁻¹
        = y * (t * (y⁻¹ * x * y) * t⁻¹) * y⁻¹ := by group
      _ = y * ((y⁻¹ * x * y)⁻¹ * a ^ k) * y⁻¹ := by rw [hk]
      _ = x⁻¹ * a ^ k := by
            rw [show y * ((y⁻¹ * x * y)⁻¹ * a ^ k) * y⁻¹
                  = (y * (y⁻¹ * x * y)⁻¹ * y⁻¹) * (y * a ^ k * y⁻¹) by group,
                show y * (y⁻¹ * x * y)⁻¹ * y⁻¹ = x⁻¹ by group,
                hconj_a y k]
  have hWK : Wsub t τ ≤ K := by
    rw [Wsub, Subgroup.closure_le]
    intro u hu
    exact Or.inr (hKm_tau u hu.2.2.2 hu.2.1 hu.2.2.1)
  have hcomm_Kp : ∀ g h : Y, (Kp g ∨ Km g) → (Kp h ∨ Km h) → Kp ⁅g, h⁆ := by
    intro g h hg hh
    rw [commutatorElement_def,
      show g * h * g⁻¹ * h⁻¹ = (g * h) * (h * g)⁻¹ by group]
    rcases hg with hg | hg <;> rcases hh with hh | hh
    · exact hKp_mul (hKp_mul hg hh) (hKp_inv (hKp_mul hh hg))
    · exact hKmKm (hKpKm hg hh) (hKm_inv (hKmKp hh hg))
    · exact hKmKm (hKmKp hg hh) (hKm_inv (hKpKm hh hg))
    · exact hKp_mul (hKmKm hg hh) (hKp_inv (hKmKm hh hg))
  have hcomm_le : ⁅Wsub t τ, Wsub t τ⁆ ≤ Kplus :=
    Subgroup.commutator_le.mpr (fun g hg h hh => hcomm_Kp g h (hWK hg) (hWK hh))
  have hsKp : Kp s := hcomm_le hsc
  have hsKm : Km s := hKm_tau s hs.2.2.2 hs.2.1 hs.2.2.1
  intro x hx
  obtain ⟨k1, hk1⟩ := hsKp x hx
  obtain ⟨k2, hk2⟩ := hsKm x hx
  have hx2 : x ^ 2 = a ^ (k2 - k1) := by
    have h1 : x * a ^ k1 = x⁻¹ * a ^ k2 := by rw [← hk1, hk2]
    have h2 : x ^ 2 * a ^ k1 = a ^ k2 := by
      have := congrArg (fun y => x * y) h1
      rw [show x * (x * a ^ k1) = x ^ 2 * a ^ k1 by rw [pow_two, mul_assoc],
          show x * (x⁻¹ * a ^ k2) = a ^ k2 by rw [← mul_assoc, mul_inv_cancel, one_mul]]
        at this
      exact this
    have h3 : x ^ 2 = a ^ k2 * a ^ (-k1) := by
      calc x ^ 2 = x ^ 2 * a ^ k1 * a ^ (-k1) := by
            rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
        _ = a ^ k2 * a ^ (-k1) := by rw [h2]
    rw [h3, ← zpow_add, show k2 + -k1 = k2 - k1 by ring]
  have hx2mem : x ^ 2 ∈ zpowers a := Subgroup.mem_zpowers_iff.mpr ⟨k2 - k1, hx2.symm⟩
  have hfin : (x ^ 2) ^ ((Nat.card N + 1) / 2) ∈ zpowers a :=
    (Subgroup.zpowers a).pow_mem hx2mem _
  have hxpow : x = (x ^ 2) ^ ((Nat.card N + 1) / 2) := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact (CFSG.OddInversion.pow_two_mul_eq_self (D := N) hNodd hx).symm
  rw [← hxpow] at hfin
  exact hfin

end CFSG.EvenSporadicStandard.HNRecog.Harada
