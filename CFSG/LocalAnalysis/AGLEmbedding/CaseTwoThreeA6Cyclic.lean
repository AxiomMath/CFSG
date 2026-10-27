module

import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoHexGroup
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPOmega
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

variable {X : Type*} [Group X]

theorem exists_cube_eq_of_isCyclic [Finite X] {D : Subgroup X} (hDc : IsCyclic D)
    (hD3 : IsPGroup 3 D) (hD9 : 9 ≤ Nat.card D) {z : X} (hzD : z ∈ D) (hz3 : z ^ 3 = 1) :
    ∃ y ∈ D, y ^ 3 = z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := hDc.exists_generator
  have hgo : orderOf g = Nat.card D := orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hD3
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have : k ≤ 1 := by omega
    have h1 : 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    rw [← hk] at h1
    omega
  have h9 : (9 : ℤ) ∣ (orderOf g : ℤ) := by
    rw [hgo, hk]
    have : (9 : ℕ) ∣ 3 ^ k := by
      rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
      exact Nat.pow_dvd_pow 3 hk2
    exact_mod_cast this
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨z, hzD⟩)
  have hm3 : g ^ (m * 3) = 1 := by
    rw [zpow_mul, hm]
    exact Subtype.ext (by simpa using hz3)
  have hdvd : (orderOf g : ℤ) ∣ m * 3 := orderOf_dvd_iff_zpow_eq_one.mpr hm3
  have h3m : (3 : ℤ) ∣ m := by
    have h93 : (9 : ℤ) ∣ m * 3 := h9.trans hdvd
    obtain ⟨c, hc⟩ := h93
    exact ⟨c, by omega⟩
  obtain ⟨m', rfl⟩ := h3m
  refine ⟨((g ^ m' : D) : X), (g ^ m').2, ?_⟩
  have : (g ^ m') ^ 3 = (⟨z, hzD⟩ : D) := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
    exact_mod_cast hm
  exact congrArg Subtype.val this

theorem mem_sup_of_cube_eq_one [Finite X] {A D : Subgroup X} (hAc : IsCyclic A)
    (hcomm : ∀ a ∈ A, ∀ d ∈ D, Commute a d) {z w : X} (hD : D = Subgroup.zpowers z)
    (hz3 : z ^ 3 = 1) (hwA : w ∈ A) (hwo : orderOf w = 3) {x : X} (hx : x ∈ A ⊔ D)
    (hx3 : x ^ 3 = 1) : x ∈ Subgroup.zpowers w ⊔ Subgroup.zpowers z := by
  have hAC : A ≤ Subgroup.centralizer (D : Set X) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun d hd => (hcomm a ha d hd).eq.symm
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A D
    (hAC.trans (Subgroup.centralizer_le_normalizer _))] at hx
  obtain ⟨a, ha, d, hd, rfl⟩ := hx
  have hd3 : d ^ 3 = 1 := by
    rw [hD] at hd
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
  have ha3 : a ^ 3 = 1 := by
    rw [(hcomm a ha d hd).mul_pow, hd3, mul_one] at hx3
    exact hx3
  have : IsCyclic A := hAc
  have haw : a ∈ Subgroup.zpowers w := mem_zpowers_of_pow_eq_one Nat.prime_three hwA hwo ha ha3
  rw [hD] at hd
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left haw) (Subgroup.mem_sup_right hd)

theorem rstruct_of_cyclic [Finite X] {P A D : Subgroup X}
    (hP : IsPGroup 3 P) (hAP : A ≤ P) (hDP : D ≤ P) (hAD : A ⊓ D = ⊥)
    (hcomm : ∀ a ∈ A, ∀ d ∈ D, Commute a d)
    (hAc : IsCyclic A) (hDc : IsCyclic D) (hA9 : 9 ≤ Nat.card A)
    {z w : X} (hzD : z ∈ D) (hzo : orderOf z = 3) (hwA : w ∈ A) (hwo : orderOf w = 3)
    (hzc : ∀ g ∈ P, Commute z g)
    (hcard : Nat.card P ≤ 27 * Nat.card D)
    (hrk : ∃ E ≤ P, IsElemAbelian 3 E ∧ 27 ≤ Nat.card E)
    (hΩ : ∀ g ∈ P, (∀ h ∈ P, Commute g h) → g ^ 3 = 1 → g ∈ A ⊔ D) :
    (∃ y ∈ P, y ^ 3 = z) ∨ (Nat.card P = 3 ^ 4 ∧ ∃ a ∈ P, a ^ 3 ∈ Subgroup.zpowers w ∧
      a ^ 3 ≠ 1 ∧ ∀ r ∈ P, r ^ 3 = 1 → r ∉ Subgroup.zpowers w ⊔ Subgroup.zpowers z →
        a * r ≠ r * a) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz3 : z ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
  have hD3 : IsPGroup 3 D := hP.to_le hDP
  by_cases hD9 : 9 ≤ Nat.card D
  · left
    obtain ⟨y, hyD, hy⟩ := exists_cube_eq_of_isCyclic hDc hD3 hD9 hzD hz3
    exact ⟨y, hDP hyD, hy⟩
  right
  have hzle : Subgroup.zpowers z ≤ D := Subgroup.zpowers_le.mpr hzD
  obtain ⟨kD, hkD⟩ := IsPGroup.iff_card.mp hD3
  have hDcard : Nat.card D = 3 := by
    have h1 : 3 ≤ Nat.card D := by
      have := Subgroup.card_le_of_le hzle
      rwa [Nat.card_zpowers, hzo] at this
    have hk1 : kD = 1 := by
      rw [hkD] at h1 hD9
      rcases Nat.lt_or_ge kD 2 with h | h
      · interval_cases kD
        · norm_num at h1
        · rfl
      · have : 3 ^ 2 ≤ 3 ^ kD := Nat.pow_le_pow_right (by norm_num) h
        omega
    rw [hkD, hk1, pow_one]
  have hDz : D = Subgroup.zpowers z := (Subgroup.eq_of_le_of_card_ge hzle (by
    rw [Nat.card_zpowers, hzo, hDcard])).symm
  have hDC : D ≤ Subgroup.centralizer (A : Set X) := fun d hd =>
    Subgroup.mem_centralizer_iff.mpr fun a ha => (hcomm a ha d hd).eq
  have hADcard : Nat.card (A ⊔ D : Subgroup X) = Nat.card A * 3 := by
    rw [card_sup_of_le_centralizer hDC hAD, hDcard]
  have hΩAD := fun {x : X} (hx : x ∈ A ⊔ D) (hx3 : x ^ 3 = 1) =>
    mem_sup_of_cube_eq_one hAc hcomm hDz hz3 hwA hwo hx hx3
  have hwz9 : Nat.card (Subgroup.zpowers w ⊔ Subgroup.zpowers z : Subgroup X) = 9 := by
    have hc : Subgroup.zpowers z ≤ Subgroup.centralizer (Subgroup.zpowers w : Set X) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact (Commute.zpow_left (hcomm w hwA z hzD) n).eq
    have hb : Subgroup.zpowers w ⊓ Subgroup.zpowers z = ⊥ :=
      eq_bot_iff.mpr (hAD ▸ inf_le_inf (Subgroup.zpowers_le.mpr hwA) hzle)
    rw [card_sup_of_le_centralizer hc hb, Nat.card_zpowers, Nat.card_zpowers, hwo, hzo]
  have hADP : A ⊔ D ≤ P := sup_le hAP hDP
  have hne : A ⊔ D ≠ P := by
    intro heq
    obtain ⟨E, hEP, hEe, hE27⟩ := hrk
    have hEle : E ≤ Subgroup.zpowers w ⊔ Subgroup.zpowers z := fun e he =>
      hΩAD (heq ▸ hEP he) (hEe.2 e he)
    have := Subgroup.card_le_of_le hEle
    omega
  obtain ⟨kA, hkA⟩ := IsPGroup.iff_card.mp (hP.to_le hAP)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  have hdvd : Nat.card (A ⊔ D : Subgroup X) ∣ Nat.card P := Subgroup.card_dvd_of_le hADP
  rw [hADcard, hkA, hn, ← pow_succ] at hdvd
  have hle1 : kA + 1 ≤ n := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  have hne1 : kA + 1 ≠ n := by
    intro h
    apply hne
    refine (Subgroup.eq_of_le_of_card_ge hADP ?_)
    rw [hADcard, hkA, hn, ← h, pow_succ]
  have hn4 : n ≤ 4 := by
    have h1 : 3 ^ n ≤ 3 ^ 4 := by
      rw [← hn]
      calc Nat.card P ≤ 27 * Nat.card D := hcard
        _ = 3 ^ 4 := by rw [hDcard]; norm_num
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have hkA2 : 2 ≤ kA := by
    have h1 : 3 ^ 2 ≤ 3 ^ kA := by rw [← hkA]; exact hA9
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have hn' : n = 4 := by omega
  have hkA' : kA = 2 := by omega
  refine ⟨by rw [hn, hn'], ?_⟩
  obtain ⟨a₀, ha₀⟩ := hAc.exists_generator
  set a : X := (a₀ : X) with ha
  have hao : orderOf a = 9 := by
    rw [ha, Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers ha₀, hkA, hkA']
    norm_num
  have haA : a ∈ A := a₀.2
  have : IsCyclic A := hAc
  refine ⟨a, hAP haA, ?_, ?_, ?_⟩
  · refine mem_zpowers_of_pow_eq_one Nat.prime_three hwA hwo (A.pow_mem haA 3) ?_
    rw [← pow_mul, show 3 * 3 = orderOf a by rw [hao]]
    exact pow_orderOf_eq_one a
  · intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hao] at this
    norm_num at this
  · intro r hrP hr3 hrn har
    have hrAD : r ∉ A ⊔ D := fun h => hrn (hΩAD h hr3)
    set C := P ⊓ Subgroup.centralizer ({r} : Set X) with hC
    have hAC : A ≤ C := by
      intro x hx
      refine Subgroup.mem_inf.mpr ⟨hAP hx, ?_⟩
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (ha₀ ⟨x, hx⟩)
      have hx' : x = a ^ m := by
        rw [ha, ← Subgroup.coe_zpow, hm]
      rw [Subgroup.mem_centralizer_singleton_iff, hx']
      exact (Commute.zpow_left (show Commute a r from har) m).eq
    have hDC' : D ≤ C := by
      intro x hx
      refine Subgroup.mem_inf.mpr ⟨hDP hx, ?_⟩
      rw [hDz] at hx
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Commute.zpow_left (hzc r hrP) m).eq
    have hrC : r ∈ C := Subgroup.mem_inf.mpr ⟨hrP, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    have hADC : A ⊔ D ≤ C := sup_le hAC hDC'
    have hCP : C ≤ P := inf_le_left
    have hC27 : 27 < Nat.card C := by
      by_contra hle
      push Not at hle
      have heq := Subgroup.eq_of_le_of_card_ge hADC (by rw [hADcard, hkA, hkA']; exact hle)
      exact hrAD (heq ▸ hrC)
    obtain ⟨kC, hkC⟩ := IsPGroup.iff_card.mp (hP.to_le hCP)
    have hCdvd : Nat.card C ∣ Nat.card P := Subgroup.card_dvd_of_le hCP
    rw [hkC, hn, hn'] at hCdvd
    have hkC4 : kC ≤ 4 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hCdvd
    have hkC3 : 3 < kC := by
      have : 3 ^ 3 < 3 ^ kC := by rw [← hkC]; norm_num; exact hC27
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
    have hCeq : C = P := Subgroup.eq_of_le_of_card_ge hCP (by
      rw [hkC, hn, hn', show kC = 4 by omega])
    have hrZ : ∀ h ∈ P, Commute r h := by
      intro h hh
      have hhC : h ∈ C := hCeq ▸ hh
      exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hhC).2).symm
    exact hrAD (hΩ r hrP hrZ hr3)

end CFSG.AGLEmbedding
