module

public import CFSG.Open.LocalVocabulary
import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup

public section

open scoped commutatorElement

namespace CFSG.GroupTheory

private theorem zpow_eq_self_or_inv_of_dvd {G : Type*} [Group G] {g : G} {p e : ℕ} {k : ℤ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hord : orderOf g = p ^ e)
    (hdvd : ((p : ℤ) ^ e) ∣ (k - 1) * (k + 1)) :
    g ^ k = g ∨ g ^ k = g⁻¹ := by
  have hpZ : Prime (p : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hp)
  have hp_not_two : ¬ (p : ℤ) ∣ 2 := by
    intro h
    have h2 : p ∣ 2 := Int.natCast_dvd_natCast.mp h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  by_cases hplus : (p : ℤ) ∣ k + 1
  · have hnot : ¬ (p : ℤ) ∣ k - 1 := by
      intro hminus
      have h2 : (p : ℤ) ∣ 2 := by
        have := Int.dvd_sub hplus hminus
        simpa using this
      exact hp_not_two h2
    have hdiv : ((p : ℤ) ^ e) ∣ k + 1 := hpZ.pow_dvd_of_dvd_mul_left e hnot hdvd
    right
    have hmod : k ≡ (-1 : ℤ) [ZMOD orderOf g] := by
      rw [hord]
      exact Int.modEq_iff_dvd.mpr (by
        rw [show (-1 : ℤ) - k = -(k + 1) by ring]
        exact dvd_neg.mpr hdiv)
    simpa [zpow_neg_one] using
      (zpow_eq_zpow_iff_modEq (x := g) (m := k) (n := -1)).mpr hmod
  · have hnot : ¬ (p : ℤ) ∣ k + 1 := hplus
    have hdiv : ((p : ℤ) ^ e) ∣ k - 1 := hpZ.pow_dvd_of_dvd_mul_right e hnot hdvd
    left
    have hmod : k ≡ (1 : ℤ) [ZMOD orderOf g] := by
      rw [hord]
      exact Int.modEq_iff_dvd.mpr (by
        rw [show (1 : ℤ) - k = -(k - 1) by ring]
        exact dvd_neg.mpr hdiv)
    simpa using
      (zpow_eq_zpow_iff_modEq (x := g) (m := k) (n := 1)).mpr hmod

private theorem zpow_eq_or_inv_of_conj_eq {G : Type*} [Group G] {g y : G} {p e : ℕ} {k : ℤ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hord : orderOf g = p ^ e)
    (hk' : g ^ k = y * g * y⁻¹) (hy2 : y ^ 2 = 1) :
    g ^ k = g ∨ g ^ k = g⁻¹ := by
  have hy1 : y * y = 1 := by rw [← sq, hy2]
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy1
  have hconj₁ : y * (y * g * y⁻¹) * y⁻¹ = g := by
    rw [hyinv, show y * (y * g * y) * y = (y * y) * g * (y * y) by group,
      hy1, one_mul, mul_one]
  have hconj₂ : y * g ^ k * y⁻¹ = g ^ (k * k) := by
    calc y * g ^ k * y⁻¹ = (y * g * y⁻¹) ^ k := by rw [conj_zpow]
      _ = (g ^ k) ^ k := by rw [← hk']
      _ = g ^ (k * k) := by rw [← zpow_mul]
  have hyy : g = g ^ (k * k) := by
    calc g = y * (y * g * y⁻¹) * y⁻¹ := hconj₁.symm
      _ = y * g ^ k * y⁻¹ := by rw [← hk']
      _ = g ^ (k * k) := hconj₂
  have hdvd' : (orderOf g : ℤ) ∣ (k - 1) * (k + 1) := by
    rw [orderOf_dvd_iff_zpow_eq_one]
    rw [show (k - 1) * (k + 1) = k * k - 1 by ring, zpow_sub, zpow_one, ← hyy, mul_inv_cancel]
  have hdvd : ((p : ℤ) ^ e) ∣ (k - 1) * (k + 1) := by
    rwa [hord, Nat.cast_pow] at hdvd'
  exact zpow_eq_self_or_inv_of_dvd hp hp2 hord hdvd

theorem conj_eq_or_eq_inv_of_isCyclic_of_isPGroup {G : Type*} [Group G] [Finite G]
    {P : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hP : IsPGroup p P) (hcyc : IsCyclic ↥P) {y : G}
    (hyN : y ∈ Subgroup.normalizer (P : Set G)) (hy2 : y ^ 2 = 1) :
    (∀ x ∈ P, y * x * y⁻¹ = x) ∨ (∀ x ∈ P, y * x * y⁻¹ = x⁻¹) := by
  classical
  by_cases hbot : P = ⊥
  · left
    intro x hx
    rw [hbot] at hx
    rw [Subgroup.mem_bot.mp hx]
    simp
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp hP
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥P)
  have hord : orderOf (g : G) = Nat.card P := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg]
  have hyP : y * (g : G) * y⁻¹ ∈ P :=
    (Subgroup.mem_normalizer_iff.mp hyN (g : G)).mp g.2
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y * (g : G) * y⁻¹, hyP⟩)
  have hk' : (g : G) ^ k = y * (g : G) * y⁻¹ := by simpa using congrArg Subtype.val hk
  have he' : orderOf (g : G) = p ^ e := by rw [hord, he]
  have key : ∀ m : ℤ, y * (g : G) ^ m * y⁻¹ = (g : G) ^ (k * m) := by
    intro m
    calc y * (g : G) ^ m * y⁻¹ = (y * (g : G) * y⁻¹) ^ m := by rw [conj_zpow]
      _ = ((g : G) ^ k) ^ m := by rw [← hk']
      _ = (g : G) ^ (k * m) := by rw [← zpow_mul]
  rcases zpow_eq_or_inv_of_conj_eq hp hp2 he' hk' hy2 with hgk | hgk
  · left
    intro x hx
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    have hm' : (g : G) ^ m = x := by simpa using congrArg Subtype.val hm
    calc y * x * y⁻¹ = y * (g : G) ^ m * y⁻¹ := by rw [← hm']
      _ = (g : G) ^ (k * m) := key m
      _ = ((g : G) ^ k) ^ m := by rw [zpow_mul]
      _ = (g : G) ^ m := by rw [hgk]
      _ = x := hm'
  · right
    intro x hx
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    have hm' : (g : G) ^ m = x := by simpa using congrArg Subtype.val hm
    calc y * x * y⁻¹ = y * (g : G) ^ m * y⁻¹ := by rw [← hm']
      _ = (g : G) ^ (k * m) := key m
      _ = ((g : G)⁻¹) ^ m := by rw [zpow_mul, hgk]
      _ = ((g : G) ^ m)⁻¹ := by rw [inv_zpow]
      _ = x⁻¹ := by rw [hm']

theorem not_le_centralizer_of_forall_conj_eq_inv {G : Type*} [Group G] {P : Subgroup G} {a : G}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hP : IsPGroup p P) (hne : P ≠ ⊥)
    (hinv : ∀ x ∈ P, a * x * a⁻¹ = x⁻¹) : ¬ P ≤ Subgroup.centralizer ({a} : Set G) := by
  intro hle
  refine hne (eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr ?_)
  have hxx : x * x = 1 := by
    have h1 := hinv x hx
    rw [← Subgroup.mem_centralizer_singleton_iff.mp (hle hx), mul_inv_cancel_right] at h1
    exact mul_eq_one_iff_eq_inv.mpr h1
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have h1 : orderOf x ∣ p ^ k :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hxx)
  have hcop : Nat.Coprime (p ^ k) 2 :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem commutator_eq_of_isCyclic_of_isPGroup_of_inverts {G : Type*} [Group G] [Finite G]
    {P A : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hP : IsPGroup p P) (hcyc : IsCyclic ↥P)
    (hAN : A ≤ Subgroup.normalizer (P : Set G))
    (ha : ∃ a ∈ A, ∀ x ∈ P, a * x * a⁻¹ = x⁻¹) : ⁅P, A⁆ = P := by
  classical
  obtain ⟨a, haA, hinv⟩ := ha
  have hle : ⁅P, A⁆ ≤ P := by
    rw [Subgroup.commutator_le]
    intro x hx a ha
    rw [commutatorElement_def]
    have hmem : a * x⁻¹ * a⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (hAN ha) x⁻¹).mp (P.inv_mem hx)
    rw [show x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) by group]
    exact P.mul_mem hx hmem
  refine le_antisymm hle ?_
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥P)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp hP
  have hodd : Odd (orderOf (g : G)) := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, he]
    exact (hp.odd_of_ne_two hp2).pow
  have hgm : (g : G) ∈ Subgroup.zpowers ((g : G) ^ 2) := by
    rw [mem_zpowers_pow_iff]
    exact Nat.coprime_two_left.mpr hodd
  have hPle : P ≤ Subgroup.zpowers ((g : G) ^ 2) := by
    have hzple : Subgroup.zpowers (g : G) ≤ Subgroup.zpowers ((g : G) ^ 2) :=
      Subgroup.zpowers_le.mpr hgm
    intro x hx
    apply hzple
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, by simpa using congrArg Subtype.val hm⟩
  have hmem : (g : G) ^ 2 ∈ ⁅P, A⁆ := by
    have hcommut : ⁅(g : G), a⁆ = (g : G) ^ 2 := by
      rw [commutatorElement_def]
      calc (g : G) * a * (g : G)⁻¹ * a⁻¹ = (g : G) * (a * (g : G)⁻¹ * a⁻¹) := by group
        _ = (g : G) * (a * (g : G) * a⁻¹)⁻¹ := by
          rw [show a * (g : G)⁻¹ * a⁻¹ = (a * (g : G) * a⁻¹)⁻¹ by group]
        _ = (g : G) * ((g : G)⁻¹)⁻¹ := by rw [hinv (g : G) g.2]
        _ = (g : G) * (g : G) := by rw [inv_inv]
        _ = (g : G) ^ 2 := by rw [pow_two]
    rw [← hcommut]
    exact Subgroup.commutator_mem_commutator g.2 haA
  exact hPle.trans (Subgroup.zpowers_le.mpr hmem)

theorem sup_inf_centralizer_eq_of_isCyclic_of_isPGroup {G : Type*} [Group G] [Finite G]
    {P A : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hP : IsPGroup p P) (hcyc : IsCyclic ↥P)
    (hAN : A ≤ Subgroup.normalizer (P : Set G))
    (hA : CFSG.Open.IsElemAbelian 2 A) {a : G} (haA : a ∈ A)
    (hinv : ∀ y ∈ P, a * y * a⁻¹ = y⁻¹) :
    A = (A ⊓ Subgroup.centralizer (P : Set G)) ⊔ Subgroup.zpowers a := by
  classical
  set B : Subgroup G := A ⊓ Subgroup.centralizer (P : Set G) with hBdef
  refine le_antisymm ?_ (sup_le inf_le_left (Subgroup.zpowers_le.mpr haA))
  intro x hx
  by_cases hxB : x ∈ B
  · exact Subgroup.mem_sup_left hxB
  · have hdichx := conj_eq_or_eq_inv_of_isCyclic_of_isPGroup
      hp hp2 hP hcyc (hAN hx) (hA.2 x hx)
    have hxinv : ∀ y ∈ P, x * y * x⁻¹ = y⁻¹ := by
      rcases hdichx with hc | hi'
      · exfalso
        apply hxB
        refine ⟨hx, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
        calc y * x = (x * y * x⁻¹) * x := by rw [hc y hy]
          _ = x * y := by group
      · exact hi'
    have hxaB : x * a ∈ B := by
      refine ⟨A.mul_mem hx haA, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      have hconj : (x * a) * y * (x * a)⁻¹ = y := by
        calc (x * a) * y * (x * a)⁻¹ = x * (a * y * a⁻¹) * x⁻¹ := by group
          _ = x * y⁻¹ * x⁻¹ := by rw [hinv y hy]
          _ = (x * y * x⁻¹)⁻¹ := by group
          _ = (y⁻¹)⁻¹ := by rw [hxinv y hy]
          _ = y := by rw [inv_inv]
      calc y * (x * a) = ((x * a) * y * (x * a)⁻¹) * (x * a) := by rw [hconj]
        _ = (x * a) * y := by group
    have hxeq : x = (x * a) * a⁻¹ := by group
    rw [hxeq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hxaB)
      (Subgroup.mem_sup_right ((Subgroup.zpowers a).inv_mem (Subgroup.mem_zpowers a)))

theorem relIndex_inf_centralizer_eq_two_of_isCyclic_of_isPGroup {G : Type*} [Group G] [Finite G]
    {P A : Subgroup G} (hA : CFSG.Open.IsElemAbelian 2 A) {a : G} (haA : a ∈ A)
    (haP : ¬ P ≤ Subgroup.centralizer ({a} : Set G))
    (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1)
    (hAsup : A = (A ⊓ Subgroup.centralizer (P : Set G)) ⊔ Subgroup.zpowers a) :
    (A ⊓ Subgroup.centralizer (P : Set G)).relIndex A = 2 := by
  classical
  set B : Subgroup G := A ⊓ Subgroup.centralizer (P : Set G) with hBdef
  have hnotB : a ∉ B := by
    intro haB
    exact haP fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp haB.2) x hx)
  have hAKcomm : ∀ b ∈ B, b * a = a * b := by
    have : IsMulCommutative ↥A := hA.1
    intro b hb
    have hcomm' := (IsMulCommutative.is_comm (M := ↥A)).comm ⟨b, hb.1⟩ ⟨a, haA⟩
    simpa using congrArg Subtype.val hcomm'
  have horder_a : orderOf a = 2 := orderOf_eq_prime ha2 ha1
  have hBK : B ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
    have hcent : B ≤ Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
      rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
      exact hAKcomm
    exact hcent.trans (Subgroup.centralizer_le_normalizer _)
  have hrelZ : (B ⊓ Subgroup.zpowers a).relIndex (Subgroup.zpowers a) = 2 := by
    have hdvd : (B ⊓ Subgroup.zpowers a).relIndex (Subgroup.zpowers a) ∣
        Nat.card (Subgroup.zpowers a) :=
      Subgroup.relIndex_dvd_card (H := B ⊓ Subgroup.zpowers a) (K := Subgroup.zpowers a)
    rw [Nat.card_zpowers, horder_a] at hdvd
    have hne : (B ⊓ Subgroup.zpowers a).relIndex (Subgroup.zpowers a) ≠ 1 := by
      intro h1
      have hle : Subgroup.zpowers a ≤ B ⊓ Subgroup.zpowers a := Subgroup.relIndex_eq_one.mp h1
      exact hnotB (hle (Subgroup.mem_zpowers a)).1
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two _ hdvd with h1 | h2
    · exact absurd h1 hne
    · exact h2
  calc
    B.relIndex A = B.relIndex (B ⊔ Subgroup.zpowers a) := by rw [hAsup]
    _ = (B ⊓ Subgroup.zpowers a).relIndex (Subgroup.zpowers a) :=
      (relIndex_sup_eq_relIndex_inf_of_le_normalizer
        (H := B) (K := Subgroup.zpowers a) hBK).1
    _ = 2 := hrelZ

end CFSG.GroupTheory
