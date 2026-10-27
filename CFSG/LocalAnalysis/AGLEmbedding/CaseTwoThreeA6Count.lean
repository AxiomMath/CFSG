module

import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoHexGroup
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFGroup
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoThreeA6Dec
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

variable {X : Type} [Group X] [Finite X]

theorem false_of_elemAbelian_of_dec {A S E : Subgroup X} (hS : IsPGroup 3 S)
    (hSN : S ≤ Subgroup.normalizer (A : Set X))
    (hdec : ∀ y ∈ S, ∃ l ∈ S ⊓ A, l⁻¹ * y ∈ Subgroup.centralizer (A : Set X))
    (hb : ∀ l ∈ A, (∃ k : ℕ, l ^ 3 ^ k = 1) → l ^ 3 = 1)
    (hc : ∀ T : Subgroup X, T ≤ A → IsPGroup 3 T →
      Nat.card T ≤ 3 ^ 3 ∧ (IsMulCommutative T → Nat.card T ≤ 3 ^ 2)) {w : X}
    (hZw : ∀ x ∈ A, x ∈ Subgroup.centralizer (A : Set X) → x ∈ Subgroup.zpowers w)
    (hwA : w ∈ A) (hwC : w ∈ Subgroup.centralizer (A : Set X)) (hwo : orderOf w = 3)
    (hD27 : Nat.card (S ⊓ Subgroup.centralizer (A : Set X) : Subgroup X) ≤ 3 ^ 3)
    (hDnab : ∃ d ∈ S ⊓ Subgroup.centralizer (A : Set X),
      ∃ c ∈ S ⊓ Subgroup.centralizer (A : Set X), d * c ≠ c * d)
    (hES : E ≤ S) (hEe : IsElemAbelian 3 E) (hE81 : 3 ^ 4 ≤ Nat.card E) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Cn := Subgroup.centralizer (A : Set X) with hCn
  set D := S ⊓ Cn with hD
  have hpe : ∀ x ∈ S, ∃ k : ℕ, x ^ 3 ^ k = 1 := fun x hx => by
    obtain ⟨k, hk⟩ := hS ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hSin : ∀ x ∈ S, x ∈ A ⊔ Cn := fun x hx => by
    obtain ⟨l, hl, hlc⟩ := hdec x hx
    rw [show x = l * (l⁻¹ * x) by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl.2) (Subgroup.mem_sup_right hlc)
  have hw3 : w ^ 3 = 1 := by rw [← hwo]; exact pow_orderOf_eq_one w
  obtain ⟨da, hdaD, cb, hcbD, hdacb⟩ := hDnab
  have hNoE : ∀ V ≤ D, IsElemAbelian 3 V → Nat.card V < 3 ^ 3 := by
    intro V hV hVe
    by_contra hge
    push Not at hge
    have heq : V = D := Subgroup.eq_of_le_of_card_ge hV (hD27.trans hge)
    apply hdacb
    have h1 : da ∈ V := heq ▸ hdaD
    have h2 : cb ∈ V := heq ▸ hcbD
    exact congrArg Subtype.val (hVe.1.is_comm.comm ⟨da, h1⟩ ⟨cb, h2⟩)
  set IE := A ⊓ (E ⊔ Cn) with hIE
  set FE := E ⊓ Cn with hFE
  have hcountE := card_mul_card_eq_of_sup (hES.trans hSN) (fun x hx => hSin x (hES hx))
  have hFED : FE ≤ D := inf_le_inf_right _ hES
  have hFEe : IsElemAbelian 3 FE := d1_isElemAbelian_of_le hEe inf_le_left
  have hCIE : 3 ≤ Nat.card (Cn ⊓ IE : Subgroup X) := by
    have h1 : Subgroup.zpowers w ≤ Cn ⊓ IE := by
      rw [Subgroup.zpowers_le]
      exact ⟨hwC, hwA, Subgroup.mem_sup_right hwC⟩
    have := Subgroup.card_le_of_le h1
    rwa [Nat.card_zpowers, hwo] at this
  have hENC : E ≤ Subgroup.normalizer (Cn : Set X) := fun x hx =>
    mem_normalizer_centralizer (hSN (hES hx))
  have hdecE : ∀ x ∈ E ⊔ Cn, ∃ e ∈ E, ∃ k ∈ Cn, x = e * k := by
    intro x hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hENC] at hx
    obtain ⟨e, he, k, hk, rfl⟩ := hx
    exact ⟨e, he, k, hk, rfl⟩
  have hZ3 : ∀ x ∈ A, x ∈ Cn → x ^ 3 = 1 := by
    intro x hxA hxC
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hZw x hxA hxC)
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw3, one_zpow]
  have hIE3 : IsPGroup 3 IE := by
    intro x
    obtain ⟨e, he, c, hc', hec⟩ := hdecE x x.2.2
    have hxc : Commute (x : X) c⁻¹ :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.inv_mem _ hc') x x.2.1)
    have hxe : (x : X) = e * c := hec
    have h1 : (x : X) ^ 3 * (c⁻¹) ^ 3 = 1 := by
      rw [← hxc.mul_pow, hxe, mul_inv_cancel_right]
      exact hEe.2 e he
    have h2 : (x : X) ^ 3 = ((c⁻¹) ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : (x : X) ^ 3 ∈ Cn :=
      h2 ▸ Subgroup.inv_mem _ (Cn.pow_mem (Subgroup.inv_mem _ hc') 3)
    have h4 := hZ3 _ (A.pow_mem x.2.1 3) h3
    refine ⟨2, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [show 3 ^ 2 = 3 * 3 by norm_num, pow_mul, h4]
  have hIE27 : Nat.card IE ≤ 3 ^ 3 := (hc IE inf_le_left hIE3).1
  by_cases hIEab : IsMulCommutative IE
  ·
    have hIE9 : Nat.card IE ≤ 3 ^ 2 := (hc IE inf_le_left hIE3).2 hIEab
    have hFE27 : 3 ^ 3 ≤ Nat.card FE := by
      have h1 : 3 ^ 4 * 3 ≤ 3 ^ 2 * Nat.card FE := by
        calc 3 ^ 4 * 3 ≤ Nat.card E * Nat.card (Cn ⊓ IE : Subgroup _) :=
              Nat.mul_le_mul hE81 hCIE
          _ = Nat.card IE * Nat.card FE := hcountE
          _ ≤ 3 ^ 2 * Nat.card FE := Nat.mul_le_mul_right _ hIE9
      omega
    exact absurd (hNoE FE hFED hFEe) (not_lt.mpr hFE27)
  ·
    obtain ⟨l₁, hl₁, l₂, hl₂, hll⟩ : ∃ l₁ ∈ IE, ∃ l₂ ∈ IE, l₁ * l₂ ≠ l₂ * l₁ := by
      by_contra hcomm
      push Not at hcomm
      exact hIEab ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
    have hFE9 : 3 ^ 2 ≤ Nat.card FE := by
      have h1 : 3 ^ 4 * 3 ≤ 3 ^ 3 * Nat.card FE := by
        calc 3 ^ 4 * 3 ≤ Nat.card E * Nat.card (Cn ⊓ IE : Subgroup _) :=
              Nat.mul_le_mul hE81 hCIE
          _ = Nat.card IE * Nat.card FE := hcountE
          _ ≤ 3 ^ 3 * Nat.card FE := Nat.mul_le_mul_right _ hIE27
      omega
    have hlift : ∀ l ∈ IE, ∃ e ∈ E, ∃ l' ∈ S ⊓ A, l'⁻¹ * e ∈ Cn ∧ l'⁻¹ * l ∈ A ⊓ Cn := by
      intro l hl
      obtain ⟨e, he, k, hk, hek⟩ := hdecE l hl.2
      obtain ⟨l', hl', hl'c⟩ := hdec e (hES he)
      refine ⟨e, he, l', hl', hl'c, Subgroup.mul_mem _ (Subgroup.inv_mem _ hl'.2) hl.1, ?_⟩
      rw [hek, ← mul_assoc]
      exact Subgroup.mul_mem _ hl'c hk
    obtain ⟨e₁, he₁, l₁', hl₁', hc₁, hz₁⟩ := hlift l₁ hl₁
    obtain ⟨e₂, he₂, l₂', hl₂', hc₂, hz₂⟩ := hlift l₂ hl₂
    obtain ⟨c₁, hc₁def⟩ : ∃ c, c = l₁'⁻¹ * e₁ := ⟨_, rfl⟩
    obtain ⟨c₂, hc₂def⟩ : ∃ c, c = l₂'⁻¹ * e₂ := ⟨_, rfl⟩
    rw [← hc₁def] at hc₁
    rw [← hc₂def] at hc₂
    have hcl : ∀ {c l : X}, c ∈ Cn → l ∈ A → l * c = c * l := fun hc hl =>
      Subgroup.mem_centralizer_iff.mp hc _ hl
    have hll' : l₁' * l₂' ≠ l₂' * l₁' := by
      intro h1
      apply hll
      obtain ⟨u₁, hu₁A, hu₁C, hl₁e⟩ : ∃ u ∈ A, u ∈ Cn ∧ l₁ = l₁' * u :=
        ⟨l₁'⁻¹ * l₁, hz₁.1, hz₁.2, by group⟩
      obtain ⟨u₂, hu₂A, hu₂C, hl₂e⟩ : ∃ u ∈ A, u ∈ Cn ∧ l₂ = l₂' * u :=
        ⟨l₂'⁻¹ * l₂, hz₂.1, hz₂.2, by group⟩
      have hu₁c : ∀ x ∈ A, x * u₁ = u₁ * x := fun x hx =>
        Subgroup.mem_centralizer_iff.mp hu₁C x hx
      have hu₂c : ∀ x ∈ A, x * u₂ = u₂ * x := fun x hx =>
        Subgroup.mem_centralizer_iff.mp hu₂C x hx
      rw [hl₁e, hl₂e]
      calc l₁' * u₁ * (l₂' * u₂) = l₁' * (u₁ * l₂') * u₂ := by group
        _ = l₁' * (l₂' * u₁) * u₂ := by rw [← hu₁c _ hl₂'.2]
        _ = l₁' * l₂' * (u₁ * u₂) := by group
        _ = l₂' * l₁' * (u₂ * u₁) := by rw [h1, ← hu₁c _ hu₂A]
        _ = l₂' * (l₁' * u₂) * u₁ := by group
        _ = l₂' * (u₂ * l₁') * u₁ := by rw [hu₂c _ hl₁'.2]
        _ = l₂' * u₂ * (l₁' * u₁) := by group
    have hc₁D : c₁ ∈ D :=
      ⟨hc₁def ▸ Subgroup.mul_mem _ (Subgroup.inv_mem _ hl₁'.1) (hES he₁), hc₁⟩
    have hc₂D : c₂ ∈ D :=
      ⟨hc₂def ▸ Subgroup.mul_mem _ (Subgroup.inv_mem _ hl₂'.1) (hES he₂), hc₂⟩
    have he₁e : e₁ = l₁' * c₁ := by rw [hc₁def]; group
    have he₂e : e₂ = l₂' * c₂ := by rw [hc₂def]; group
    have hcc : c₁ * c₂ ≠ c₂ * c₁ := by
      intro hc12
      apply hll'
      have hee : e₁ * e₂ = e₂ * e₁ := congrArg Subtype.val (hEe.1.is_comm.comm ⟨e₁, he₁⟩ ⟨e₂, he₂⟩)
      rw [he₁e, he₂e] at hee
      have e1 : l₁' * c₁ * (l₂' * c₂) = l₁' * l₂' * (c₁ * c₂) := by
        rw [mul_assoc, ← mul_assoc c₁, ← hcl hc₁ hl₂'.2]; group
      have e2 : l₂' * c₂ * (l₁' * c₁) = l₂' * l₁' * (c₂ * c₁) := by
        rw [mul_assoc, ← mul_assoc c₂, ← hcl hc₂ hl₁'.2]; group
      rw [e1, e2, hc12] at hee
      exact mul_right_cancel hee
    have hl₁'3 : l₁' ^ 3 = 1 := hb l₁' hl₁'.2 (hpe l₁' hl₁'.1)
    have hc₁3 : c₁ ^ 3 = 1 := by
      have h1 : e₁ ^ 3 = 1 := hEe.2 e₁ he₁
      rw [he₁e, (Commute.symm (hcl hc₁ hl₁'.2).symm).mul_pow, hl₁'3, one_mul] at h1
      exact h1
    have hcF : ∀ {e l c : X}, e ∈ E → l ∈ A → c = l⁻¹ * e →
        ∀ f ∈ FE, f * c = c * f := by
      intro e l c he hl hce f hf
      have hfe : f * e = e * f := congrArg Subtype.val (hEe.1.is_comm.comm ⟨f, hf.1⟩ ⟨e, he⟩)
      have hfl : Commute l f := hcl hf.2 hl
      rw [hce]
      calc f * (l⁻¹ * e) = (f * l⁻¹) * e := by rw [mul_assoc]
        _ = (l⁻¹ * f) * e := by rw [(Commute.inv_left hfl).eq]
        _ = l⁻¹ * (f * e) := by rw [mul_assoc]
        _ = l⁻¹ * (e * f) := by rw [hfe]
        _ = l⁻¹ * e * f := by rw [mul_assoc]
    have hFc₂ : FE ≤ Subgroup.centralizer ({c₂} : Set X) := fun f hf =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hcF he₂ hl₂'.2 hc₂def f hf)
    have hFc₁ : FE ≤ Subgroup.centralizer ({c₁} : Set X) := fun f hf =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hcF he₁ hl₁'.2 hc₁def f hf)
    have hc₁n : c₁ ∉ FE := fun h1 => hcc (Subgroup.mem_centralizer_singleton_iff.mp (hFc₂ h1))
    obtain ⟨hVc, hVe⟩ := card_sup_zpowers_elem le_rfl hc₁3 hc₁n hFc₁ hFEe
    have hVD : FE ⊔ Subgroup.zpowers c₁ ≤ D := sup_le hFED (Subgroup.zpowers_le.mpr hc₁D)
    have := hNoE _ hVD hVe
    rw [hVc] at this
    omega

end CFSG.AGLEmbedding
