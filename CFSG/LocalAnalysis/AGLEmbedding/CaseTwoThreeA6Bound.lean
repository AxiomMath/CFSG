module

import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoHexGroup
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFGroup
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPOdd
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReducedBAux
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoThreeA6Dec
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoThreeA6Transv
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem pow_three_mem_centralizer_of_dec {A S : Subgroup X} (hS : IsPGroup 3 S)
    (hdec : ∀ y ∈ S, ∃ l ∈ S ⊓ A, l⁻¹ * y ∈ Subgroup.centralizer (A : Set X))
    (hb : ∀ l ∈ A, (∃ k : ℕ, l ^ 3 ^ k = 1) → l ^ 3 = 1) {y : X} (hy : y ∈ S) :
    y ^ 3 ∈ Subgroup.centralizer (A : Set X) := by
  obtain ⟨l, hl, hlc⟩ := hdec y hy
  obtain ⟨k, hk⟩ := hS ⟨l, hl.1⟩
  have hl3 : l ^ 3 = 1 := hb l hl.2 ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hcomm : Commute l (l⁻¹ * y) := Subgroup.mem_centralizer_iff.mp hlc l hl.2
  have h : y ^ 3 = (l⁻¹ * y) ^ 3 := by
    calc y ^ 3 = (l * (l⁻¹ * y)) ^ 3 := by rw [mul_inv_cancel_left]
      _ = (l⁻¹ * y) ^ 3 := by rw [hcomm.mul_pow, hl3, one_mul]
  rw [h]
  exact Subgroup.pow_mem _ hlc 3

theorem center_eq_zpowers_of_sylow {A : Subgroup X} (hZ : Nat.card (Subgroup.center ↥A) = 3)
    (S : Sylow 3 X) (hSN : (S : Subgroup X) ≤ Subgroup.normalizer (A : Set X)) {w : X}
    (hwo : orderOf w = 3)
    (hΩ : ∀ g ∈ (S : Subgroup X), (∀ h ∈ (S : Subgroup X), Commute g h) → g ^ 3 = 1 →
      g ∈ Subgroup.zpowers w) :
    (∀ x ∈ A, x ∈ Subgroup.centralizer (A : Set X) → x ∈ Subgroup.zpowers w) ∧ w ∈ A ∧
      w ∈ Subgroup.centralizer (A : Set X) ∧ w ∈ (S : Subgroup X) ∧
      ∀ g ∈ (S : Subgroup X), Commute w g := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set Cn := Subgroup.centralizer (A : Set X) with hCn
  obtain ⟨ζ, hζA, hζC, hζ1, hζ3⟩ := exists_center_of_card hZ
  have hζo : orderOf ζ = 3 := orderOf_eq_prime hζ3 hζ1
  have hZζ : ∀ x ∈ A, x ∈ Cn → x ∈ Subgroup.zpowers ζ := by
    intro x hxA hxC
    have hxZ : (⟨x, hxA⟩ : A) ∈ Subgroup.center A := Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y y.2)
    have hζZ : (⟨ζ, hζA⟩ : A) ∈ Subgroup.center A := Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hζC y y.2)
    have heq : Subgroup.zpowers (⟨ζ, hζA⟩ : A) = Subgroup.center A :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hζZ)
        (by rw [hZ, Nat.card_zpowers, Subgroup.orderOf_mk, hζo])
    have hx' : (⟨x, hxA⟩ : A) ∈ Subgroup.zpowers (⟨ζ, hζA⟩ : A) := heq ▸ hxZ
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx'
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hSζ : ∀ g ∈ (S : Subgroup X), Commute g ζ := by
    intro g hg
    have hgN := hSN hg
    have hgζ : g * ζ * g⁻¹ ∈ Subgroup.zpowers ζ :=
      hZζ _ ((Subgroup.mem_normalizer_iff.mp hgN ζ).mp hζA)
        ((Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer hgN) ζ).mp hζC)
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨g, hg⟩
    exact commute_of_mem_normalizer_zpowers_of_pow_prime_pow hp hζo
      (mem_normalizer_zpowers_of_mem_zpowers hgζ) (by simpa using congrArg Subtype.val hk)
  have hζS : ζ ∈ (S : Subgroup X) := by
    have hζN : Subgroup.zpowers ζ ≤ Subgroup.normalizer ((S : Subgroup X) : Set X) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.centralizer_le_normalizer _
        (Subgroup.mem_centralizer_iff.mpr fun g hg => (hSζ g hg).eq)
    have hV := IsPGroup.to_sup_of_normal_left' S.isPGroup'
      (isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hζ3)) hζN
    have hmax := S.is_maximal' hV le_sup_left
    exact hmax ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers ζ)
  have hζw : ζ ∈ Subgroup.zpowers w := hΩ ζ hζS (fun g hg => (hSζ g hg).symm) hζ3
  have hζeq : Subgroup.zpowers ζ = Subgroup.zpowers w := Subgroup.eq_of_le_of_card_ge
    (Subgroup.zpowers_le.mpr hζw) (by rw [Nat.card_zpowers, Nat.card_zpowers, hζo, hwo])
  have hwZ : w ∈ Subgroup.zpowers ζ := hζeq ▸ Subgroup.mem_zpowers w
  refine ⟨fun x hxA hxC => hζeq ▸ hZζ x hxA hxC, Subgroup.zpowers_le.mpr hζA hwZ,
    Subgroup.zpowers_le.mpr hζC hwZ, Subgroup.zpowers_le.mpr hζS hwZ, fun g hg => ?_⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hwZ
  rw [← hn]
  exact ((hSζ g hg).symm).zpow_left n

theorem card_inf_centralizer_le_of_dec {A S R : Subgroup X} (hS : IsPGroup 3 S)
    (hSN : S ≤ Subgroup.normalizer (A : Set X))
    (hdec : ∀ y ∈ S, ∃ l ∈ S ⊓ A, l⁻¹ * y ∈ Subgroup.centralizer (A : Set X))
    (hb : ∀ l ∈ A, (∃ k : ℕ, l ^ 3 ^ k = 1) → l ^ 3 = 1) {w : X}
    (hZw : ∀ x ∈ A, x ∈ Subgroup.centralizer (A : Set X) → x ∈ Subgroup.zpowers w)
    (hwA : w ∈ A) (hwC : w ∈ Subgroup.centralizer (A : Set X)) (hwS : w ∈ S)
    (hwZ : ∀ g ∈ S, Commute w g) (hwo : orderOf w = 3) {z : X} (hzS : z ∈ S)
    (hz3 : z ^ 3 = 1) (hzA : z ∉ A) (hzC : z ∉ Subgroup.centralizer (A : Set X))
    (hRS : R ≤ S) (hR81 : Nat.card R = 3 ^ 4) (hRz : ∀ x ∈ R, x * z = z * x)
    (hCR : ∀ x ∈ S, x * z = z * x → x ∈ R) {a : X} (haR : a ∈ R)
    (ha3 : a ^ 3 ∈ Subgroup.zpowers w) (ha31 : a ^ 3 ≠ 1)
    (har : ∀ r ∈ R, r ^ 3 = 1 → r ∉ Subgroup.zpowers w ⊔ Subgroup.zpowers z → a * r ≠ r * a) :
    Nat.card (S ⊓ Subgroup.centralizer (A : Set X) : Subgroup X) ≤ 3 ^ 3 ∧
      ∃ d ∈ S ⊓ Subgroup.centralizer (A : Set X),
        ∃ c ∈ S ⊓ Subgroup.centralizer (A : Set X), d * c ≠ c * d := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set Cn := Subgroup.centralizer (A : Set X) with hCn
  have hpe : ∀ x ∈ S, ∃ k : ℕ, x ^ 3 ^ k = 1 := fun x hx => by
    obtain ⟨k, hk⟩ := hS ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hSin : ∀ x ∈ S, x ∈ A ⊔ Cn := fun x hx => by
    obtain ⟨l, hl, hlc⟩ := hdec x hx
    rw [show x = l * (l⁻¹ * x) by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl.2) (Subgroup.mem_sup_right hlc)
  have hw3 : w ^ 3 = 1 := by rw [← hwo]; exact pow_orderOf_eq_one w
  have hw1 : w ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hwo; norm_num at hwo
  have hWA : Subgroup.zpowers w ≤ A := Subgroup.zpowers_le.mpr hwA
  obtain ⟨t, ht, htc⟩ := hdec z hzS
  set cb := t⁻¹ * z with hcb
  have ht3 : t ^ 3 = 1 := hb t ht.2 (hpe t ht.1)
  have htcb : Commute t cb := Subgroup.mem_centralizer_iff.mp htc t ht.2
  have hzbt : z = t * cb := by rw [hcb]; group
  have hcb3 : cb ^ 3 = 1 := by
    have h1 : z ^ 3 = t ^ 3 * cb ^ 3 := by rw [hzbt, htcb.mul_pow]
    rwa [hz3, ht3, one_mul, eq_comm] at h1
  have hcbS : cb ∈ S := Subgroup.mul_mem _ (Subgroup.inv_mem _ ht.1) hzS
  have htC : t ∉ Cn := fun h1 => hzC (hzbt ▸ Subgroup.mul_mem _ h1 htc)
  have hcbA : cb ∉ A := fun h1 => hzA (hzbt ▸ Subgroup.mul_mem _ ht.2 h1)
  have htz : Commute t z := by rw [hzbt]; exact (Commute.refl t).mul_right htcb
  have hcbz : Commute cb z := by rw [hzbt]; exact htcb.symm.mul_right (Commute.refl cb)
  have htR : t ∈ R := hCR t ht.1 htz.eq
  have htn : t ∉ Subgroup.zpowers w ⊔ Subgroup.zpowers z := by
    intro hmem
    obtain ⟨u, hu, v, hv, huv⟩ := (mem_zpowers_sup_zpowers_iff (hwZ z hzS)).mp hmem
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    have hzjA : z ^ j ∈ A := by
      have : z ^ j = (w ^ i)⁻¹ * t := by rw [← huv]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.zpow_mem _ hwA i)) ht.2
    by_cases hzj : z ^ j = 1
    · apply htC
      rw [← huv, hzj, mul_one]
      exact Subgroup.zpow_mem _ hwC i
    · apply hzA
      have hzo : orderOf z = 3 := orderOf_eq_prime hz3 (fun h1 => hzC (h1 ▸ Subgroup.one_mem _))
      have hzjo : orderOf (z ^ j) = 3 := orderOf_eq_prime (by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]) hzj
      have heq : Subgroup.zpowers (z ^ j) = Subgroup.zpowers z := Subgroup.eq_of_le_of_card_ge
        (Subgroup.zpowers_le.mpr (Subgroup.zpow_mem_zpowers z j))
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hzo, hzjo])
      exact (Subgroup.zpowers_le.mpr hzjA) (heq ▸ Subgroup.mem_zpowers z)
  obtain ⟨ta, hta, htac⟩ := hdec a (hRS haR)
  set da := ta⁻¹ * a with hda
  have hta3 : ta ^ 3 = 1 := hb ta hta.2 (hpe ta hta.1)
  have htada : Commute ta da := Subgroup.mem_centralizer_iff.mp htac ta hta.2
  have habd : a = ta * da := by rw [hda]; group
  have hdaS : da ∈ S := Subgroup.mul_mem _ (Subgroup.inv_mem _ hta.1) (hRS haR)
  have hda3 : da ^ 3 = a ^ 3 := by rw [habd, htada.mul_pow, hta3, one_mul]
  have hdat : Commute da t := (Subgroup.mem_centralizer_iff.mp htac t ht.2).symm
  have hcbta : Commute cb ta := (Subgroup.mem_centralizer_iff.mp htc ta hta.2).symm
  have htat : ta * t ≠ t * ta := by
    intro h1
    apply har t htR ht3 htn
    rw [habd, mul_assoc, hdat.eq, ← mul_assoc, h1, mul_assoc]
  set e := da * cb * da⁻¹ * cb⁻¹ with he
  have hkey : ta * t * (da * cb) = t * ta * (cb * da) := by
    have e1 : a * z = ta * t * (da * cb) := by
      rw [habd, hzbt, mul_assoc ta, ← mul_assoc da, hdat.eq]
      group
    have e2 : z * a = t * ta * (cb * da) := by
      rw [habd, hzbt, mul_assoc t, ← mul_assoc cb, hcbta.eq]
      group
    rw [← e1, ← e2, hRz a haR]
  have heX : e⁻¹ = (t * ta)⁻¹ * (ta * t) := by
    calc e⁻¹ = cb * da * (da * cb)⁻¹ := by rw [he]; group
      _ = (t * ta)⁻¹ * (t * ta * (cb * da)) * (da * cb)⁻¹ := by group
      _ = (t * ta)⁻¹ * (ta * t * (da * cb)) * (da * cb)⁻¹ := by rw [hkey]
      _ = (t * ta)⁻¹ * (ta * t) := by group
  have heW : e ∈ Subgroup.zpowers w := by
    have hA : e⁻¹ ∈ A := by
      rw [heX]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ ht.2 hta.2))
        (Subgroup.mul_mem _ hta.2 ht.2)
    have hC : e⁻¹ ∈ Cn := by
      refine Subgroup.inv_mem _ ?_
      rw [he]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ htac htc)
        (Subgroup.inv_mem _ htac)) (Subgroup.inv_mem _ htc)
    simpa using Subgroup.inv_mem _ (hZw _ hA hC)
  have he1 : e ≠ 1 := by
    intro h1
    apply htat
    have h2 : (t * ta)⁻¹ * (ta * t) = 1 := by rw [← heX, h1, inv_one]
    exact (inv_mul_eq_one.mp h2).symm
  set I := A ⊓ (R ⊔ Cn) with hI
  set F := R ⊓ Cn with hF
  have hcount := card_mul_card_eq_of_sup (hRS.trans hSN) (fun x hx => hSin x (hRS hx))
  have hCIle : Cn ⊓ I ≤ Subgroup.zpowers w := fun x hx => hZw x hx.2.1 hx.1
  have hCI : Nat.card (Cn ⊓ I : Subgroup X) ∣ 3 := by
    have := Subgroup.card_dvd_of_le hCIle
    rwa [Nat.card_zpowers, hwo] at this
  have htI : t ∈ I := ⟨ht.2, by
    rw [show t = z * cb⁻¹ by rw [hcb]; group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hCR z hzS rfl))
      (Subgroup.mem_sup_right (Subgroup.inv_mem _ htc))⟩
  have htaI : ta ∈ I := ⟨hta.2, by
    rw [show ta = a * da⁻¹ by rw [hda]; group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left haR)
      (Subgroup.mem_sup_right (Subgroup.inv_mem _ htac))⟩
  have hI27 : 3 ^ 3 ≤ Nat.card I := by
    obtain ⟨hE9c, hE9e⟩ := card_sup_zpowers_rep ht.2 htC ht3 hwC hw1 hw3
    have hE9I : Subgroup.zpowers t ⊔ Subgroup.zpowers w ≤ I :=
      sup_le (Subgroup.zpowers_le.mpr htI)
        (Subgroup.zpowers_le.mpr ⟨hwA, Subgroup.mem_sup_right hwC⟩)
    have htaE : ta ∉ Subgroup.zpowers t ⊔ Subgroup.zpowers w := by
      intro hmem
      apply htat
      have htE : t ∈ Subgroup.zpowers t ⊔ Subgroup.zpowers w :=
        Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
      exact congrArg Subtype.val (hE9e.1.is_comm.comm ⟨ta, hmem⟩ ⟨t, htE⟩)
    have hgt : 3 ^ 2 < Nat.card I := by
      by_contra hle
      push Not at hle
      have heq := Subgroup.eq_of_le_of_card_ge hE9I (by rw [hE9c]; exact hle)
      exact htaE (heq ▸ htaI)
    have hdvd : Nat.card I ∣ 3 ^ 5 := by
      have h1 : Nat.card I ∣ Nat.card R * Nat.card (Cn ⊓ I : Subgroup X) :=
        ⟨Nat.card F, hcount⟩
      rw [hR81] at h1
      exact h1.trans (by
        rw [show 3 ^ 5 = 3 ^ 4 * 3 by norm_num]
        exact Nat.mul_dvd_mul_left _ hCI)
    obtain ⟨m, hm, hmI⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    rw [hmI] at hgt ⊢
    have : 2 < m := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hgt
    exact Nat.pow_le_pow_right (by norm_num) this
  have hF9 : Nat.card F ≤ 3 ^ 2 := by
    have hCI3 : Nat.card (Cn ⊓ I : Subgroup X) ≤ 3 := Nat.le_of_dvd (by norm_num) hCI
    have h1 : 3 ^ 3 * Nat.card F ≤ 3 ^ 4 * 3 := by
      calc 3 ^ 3 * Nat.card F ≤ Nat.card I * Nat.card F := Nat.mul_le_mul_right _ hI27
        _ = Nat.card R * Nat.card (Cn ⊓ I : Subgroup X) := hcount.symm
        _ ≤ 3 ^ 4 * 3 := by rw [hR81]; exact Nat.mul_le_mul_left _ hCI3
    omega
  have hF0 : Subgroup.zpowers cb ⊔ Subgroup.zpowers w ≤ F :=
    sup_le (Subgroup.zpowers_le.mpr ⟨hCR cb hcbS hcbz.eq, htc⟩)
      (Subgroup.zpowers_le.mpr ⟨hCR w hwS (hwZ z hzS).eq, hwC⟩)
  have hcbw : cb ∉ Subgroup.zpowers w := fun h1 => hcbA (hWA h1)
  have hF0c : Nat.card (Subgroup.zpowers cb ⊔ Subgroup.zpowers w : Subgroup X) = 3 ^ 2 := by
    have hcbo : orderOf cb = 3 := orderOf_eq_prime hcb3 (fun h1 => hcbA (h1 ▸ A.one_mem))
    have hc : Subgroup.zpowers w ≤ Subgroup.centralizer (Subgroup.zpowers cb : Set X) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact ((hwZ cb hcbS).symm.zpow_left n).eq
    have hbot : Subgroup.zpowers cb ⊓ Subgroup.zpowers w = ⊥ :=
      zpowers_inf_eq_bot_of_not_mem' Nat.prime_three hcbo hcbw
    rw [card_sup_of_le_centralizer hc hbot, Nat.card_zpowers, Nat.card_zpowers, hcbo, hwo]
    norm_num
  have hFeq : F = Subgroup.zpowers cb ⊔ Subgroup.zpowers w :=
    (Subgroup.eq_of_le_of_card_ge hF0 (by rw [hF0c]; exact hF9)).symm
  have hCD : ∀ y ∈ S ⊓ Cn, y * cb = cb * y →
      y ∈ Subgroup.zpowers cb ⊔ Subgroup.zpowers w := by
    intro y hy hyc
    have hyt : y * t = t * y := (Subgroup.mem_centralizer_iff.mp hy.2 t ht.2).symm
    have hyz : y * z = z * y := by
      rw [hzbt, ← mul_assoc, hyt, mul_assoc, hyc, ← mul_assoc]
    rw [← hFeq]
    exact ⟨hCR y hy.1 hyz, hy.2⟩
  have hdaC : da ∈ Cn := htac
  have hD27 : Nat.card (S ⊓ Cn : Subgroup X) ≤ 3 ^ 3 :=
    card_le_of_transvection (hS.to_le inf_le_left) ⟨hcbS, htc⟩ ⟨hwS, hwC⟩ ⟨hdaS, hdaC⟩
      (fun g hg => hwZ g hg.1) hcb3 hwo hcbw hCD (hda3 ▸ ha3) (hda3 ▸ ha31) heW he1
  exact ⟨hD27, da, ⟨hdaS, hdaC⟩, cb, ⟨hcbS, htc⟩,
    fun h1 => he1 (by rw [he, h1]; group)⟩

end CFSG.AGLEmbedding
