module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction628.ElemModule
public import CFSG.GroupTheory.ABGLocalTools.FrobeniusFixedPoints
public import CFSG.Holt.StarCase.Lemma26Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction629.TwoGroups
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628

section
open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem noKlein_comm_mem {p f : ℕ} {S X N : Subgroup K} {z : K} (h : Setup628 p f S X N z)
    {w : K} (hwS : w ∈ S) (hw1 : w ≠ 1) (hzw : z * w = w * z) {n : K} (hnX : n ∈ X)
    (hn : w * n = n * w) : n ∈ N := by
  have hcz : Commute z w := hzw
  have hfix : ∀ k : ℤ, z * w ^ k * z⁻¹ = w ^ k := fun k => by
    rw [(hcz.zpow_right k).eq, mul_inv_cancel_right]
  have hfix' : ∀ k : ℤ, z⁻¹ * w ^ k * z = w ^ k := fun k => by
    rw [(hcz.inv_left.zpow_right k).eq, inv_mul_cancel_right]
  have hS₀le : zpowers w ≤ S := Subgroup.zpowers_le.mpr hwS
  have hS₀ne : zpowers w ≠ ⊥ := fun h0 => hw1 (Subgroup.zpowers_eq_bot.mp h0)
  have hzN : z ∈ normalizer ((zpowers w : Subgroup K) : Set K) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      rw [hfix k]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers w) k
    · intro hg
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
      have hgeq : g = w ^ k :=
        calc g = z⁻¹ * (z * g * z⁻¹) * z := by group
          _ = z⁻¹ * w ^ k * z := by rw [hk]
          _ = w ^ k := hfix' k
      rw [hgeq]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers w) k
  have hzS₀ : zpowers z ≤ normalizer ((zpowers w : Subgroup K) : Set K) :=
    Subgroup.zpowers_le.mpr hzN
  have hnC : n ∈ centralizer ((zpowers w : Subgroup K) : Set K) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact ((show Commute w n from hn).zpow_left k).eq
  exact h.hC _ hS₀le hS₀ne hzS₀ (Subgroup.mem_inf.mpr ⟨hnX, hnC⟩)

theorem noKlein_quat_not_comm (m : ℕ) (hm : 2 ≤ m) :
    ¬ ∀ u v : QuaternionGroup m, u * v = v * u := by
  intro hcomm
  have h1 := hcomm (QuaternionGroup.a 1) (QuaternionGroup.xa 0)
  rw [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a] at h1
  have h2 : (0 - 1 : ZMod (2 * m)) = 0 + 1 := QuaternionGroup.xa.inj h1
  have h3 : ((2 : ℕ) : ZMod (2 * m)) = 0 := by
    push_cast
    linear_combination -h2
  have h4 : 2 * m ∣ 2 := (CharP.cast_eq_zero_iff (ZMod (2 * m)) (2 * m) 2).mp h3
  have h5 := Nat.le_of_dvd (by norm_num) h4
  omega

theorem no_klein_in_centralizer {p f : ℕ} {S X N : Subgroup K} {z : K}
    (h : Setup628 p f S X N z) {e₁ e₂ : K} (he₁ : e₁ ∈ S) (he₂ : e₂ ∈ S)
    (hz₁ : z * e₁ = e₁ * z) (hz₂ : z * e₂ = e₂ * z) (h₁ : e₁ ^ 2 = 1) (h₂ : e₂ ^ 2 = 1)
    (h₁ne : e₁ ≠ 1) (h₂ne : e₂ ≠ 1) (hne : e₁ ≠ e₂) (hc : e₁ * e₂ = e₂ * e₁) : False := by
  haveI : Fact f.Prime := ⟨h.hf⟩
  have hsq₁ : e₁ * e₁ = 1 := (sq e₁).symm.trans h₁
  have hsq₂ : e₂ * e₂ = 1 := (sq e₂).symm.trans h₂
  have hw1 : e₁ * e₂ ≠ 1 := fun h12 =>
    hne ((eq_inv_of_mul_eq_one_right h12).trans (inv_eq_of_mul_eq_one_right hsq₁)).symm
  have hw1z : z * (e₁ * e₂) = e₁ * e₂ * z :=
    calc z * (e₁ * e₂) = (z * e₁) * e₂ := (mul_assoc z e₁ e₂).symm
      _ = (e₁ * z) * e₂ := by rw [hz₁]
      _ = e₁ * (z * e₂) := mul_assoc e₁ z e₂
      _ = e₁ * (e₂ * z) := by rw [hz₂]
      _ = e₁ * e₂ * z := (mul_assoc e₁ e₂ z).symm
  have hodd : Odd (Nat.card X) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp h.hX
    rw [hk]
    exact Odd.pow (Nat.Prime.odd_of_ne_two h.hf h.hf2)
  have hle : X ≤ N := by
    refine CFSG.Holt.StarLemma26.le_of_forall_commute_mem (a := e₁) (b := e₂) (N := X) (K := N)
      hodd hsq₁ hsq₂ hc (h.hSX (Subgroup.mem_sup_left he₁)) (h.hSX (Subgroup.mem_sup_left he₂)) ?_
    intro w hw n hn hcomm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with hw | hw | hw
    · rw [hw] at hcomm
      exact noKlein_comm_mem h he₁ h₁ne hz₁ hn hcomm
    · rw [hw] at hcomm
      exact noKlein_comm_mem h he₂ h₂ne hz₂ hn hcomm
    · rw [hw] at hcomm
      exact noKlein_comm_mem h (S.mul_mem he₁ he₂) hw1 hw1z hn hcomm
  exact h.hXN hle

theorem isCyclic_of_abelian_centralizer {p f : ℕ} {S X N : Subgroup K} {z : K}
    (h : Setup628 p f S X N z) {A : Subgroup K} (hAS : A ≤ S)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hzA : ∀ a ∈ A, z * a = a * z) : IsCyclic A := by
  by_contra hnc
  have hA2 : IsPGroup 2 A := IsPGroup.to_le h.hS hAS
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial A := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    exact hnc isCyclic_of_subsingleton
  have hcard : 2 ∣ Nat.card A := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hA2
    have h1 : 1 < Nat.card A := Finite.one_lt_card
    rw [hn] at h1 ⊢
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp at h1
    exact dvd_pow_self 2 hn0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hcard
  have hxne : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx
    norm_num at hx
  have hx2 : x ^ 2 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have he₀A : (x : K) ∈ A := x.2
  have he₀sq : (x : K) ^ 2 = 1 := by
    have h2 := congrArg Subtype.val hx2
    simpa using h2
  have he₀ne : (x : K) ≠ 1 := fun h0 => hxne (Subtype.ext h0)
  by_cases hu : ∀ e ∈ A, e ^ 2 = 1 → e = 1 ∨ e = (x : K)
  ·
    obtain ⟨n, hn3, -, ⟨e⟩⟩ := quaternion_of_unique_involution hA2 he₀A he₀sq he₀ne hu hnc
    have hm : 2 ≤ 2 ^ (n - 2) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine noKlein_quat_not_comm (2 ^ (n - 2)) hm (fun u v => ?_)
    have h1 : e.symm u * e.symm v = e.symm v * e.symm u :=
      Subtype.ext (hAc _ (e.symm u).2 _ (e.symm v).2)
    have h2 := congrArg e h1
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h2
  ·
    have hex' : ∃ e ∈ A, e ^ 2 = 1 ∧ e ≠ 1 ∧ e ≠ (x : K) := by
      by_contra hcon
      apply hu
      intro e heA he2
      by_contra hne
      exact hcon ⟨e, heA, he2, fun h1 => hne (Or.inl h1), fun h2 => hne (Or.inr h2)⟩
    obtain ⟨e, heA, he2, he1, hex⟩ := hex'
    exact no_klein_in_centralizer h (hAS he₀A) (hAS heA) (hzA _ he₀A) (hzA _ heA)
      he₀sq he2 he₀ne he1 (Ne.symm hex) (hAc _ he₀A _ heA)
end

section
open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Open
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

theorem exists_fpf_subgroup {A : Subgroup K} {z : K} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hz : z ^ p = 1) (hA2 : IsPGroup 2 A) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hzA : z ∈ normalizer (A : Set K)) (hnc : ∃ a ∈ A, z * a ≠ a * z) :
    ∃ B : Subgroup K, B ≤ A ∧ B ≠ ⊥ ∧ z ∈ normalizer (B : Set K) ∧
      ∀ b ∈ B, z * b = b * z → b = 1 := by
  have hzpA : zpowers z ≤ normalizer (A : Set K) := zpowers_le.mpr hzA
  have hle : ⁅zpowers z, A⁆ ≤ A := by
    rw [commutator_le]
    intro g hg a ha
    have h1 : g * a * g⁻¹ ∈ A := (mem_normalizer_iff.mp (hzpA hg) a).mp ha
    have h2 : g * a * g⁻¹ * a⁻¹ ∈ A := A.mul_mem h1 (A.inv_mem ha)
    simpa [commutatorElement_def] using h2
  refine ⟨⁅zpowers z, A⁆, hle, ?_, ?_, ?_⟩
  ·
    intro hbot
    obtain ⟨a, ha, hnca⟩ := hnc
    apply hnca
    have h1 : ⁅z, a⁆ ∈ ⁅zpowers z, A⁆ := commutator_mem_commutator (mem_zpowers z) ha
    rw [hbot, mem_bot, commutatorElement_def] at h1
    calc z * a = (z * a * z⁻¹ * a⁻¹) * (a * z) := by group
      _ = a * z := by rw [h1, one_mul]
  ·
    exact normalizer_commutator_ge_left _ _ (mem_zpowers z)
  ·
    intro b hb hbfix
    have hbA : b ∈ A := hle hb
    have h1 : b ^ p ∈ ⁅A, A⁆ := pow_mem_commutator_of_fixed (P := A) hz hzA hb hbfix
    have hAA : ⁅A, A⁆ = ⊥ := by
      rw [eq_bot_iff, commutator_le]
      intro g hg a ha
      rw [mem_bot, commutatorElement_def]
      have := hAc g hg a ha
      calc g * a * g⁻¹ * a⁻¹ = (a * g) * g⁻¹ * a⁻¹ := by rw [this]
        _ = 1 := by group
    rw [hAA, mem_bot] at h1
    obtain ⟨k, hk⟩ := hA2 ⟨b, hbA⟩
    have hk' : b ^ (2 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hcop : Nat.Coprime p (2 ^ k) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    exact (pow_eq_one_iff_of_coprime hcop).mp ⟨h1, hk'⟩

theorem clifford_commute_of_mem_zpowers {z : K} {p : ℕ} (hp : p.Prime) (hz : z ^ p = 1)
    (hz1 : z ≠ 1) {b k : K} (hb : b ∈ zpowers z) (hb1 : b ≠ 1) (hbk : b * k = k * b) :
    z * k = k * z := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (zpowers z) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hz hz1
  have hb1' : (⟨b, hb⟩ : zpowers z) ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  have hmem := mem_zpowers_of_prime_card hcard hb1' (g' := ⟨z, mem_zpowers z⟩)
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hmem
  have hzj : b ^ j = z := by
    have := congrArg Subtype.val hj
    simpa using this
  have hc : Commute b k := hbk
  rw [← hzj]
  exact (hc.zpow_left j).eq

theorem clifford_not_dvd_card {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) {S B : Subgroup K}
    (hS : IsPGroup 2 S) (hBS : B ≤ S) : ¬ f ∣ Nat.card B := by
  obtain ⟨n, hn⟩ := (hS.to_le hBS).exists_card_eq
  intro hdvd
  rw [hn] at hdvd
  exact hf2 ((Nat.prime_dvd_prime_iff_eq hf Nat.prime_two).mp (hf.dvd_of_dvd_pow hdvd))

theorem z_centralizes_abelian {p f : ℕ} {S X N : Subgroup K} {z : K} (h : Setup628 p f S X N z)
    {A : Subgroup K} (hAS : A ≤ S) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hzA : z ∈ normalizer (A : Set K)) : ∀ a ∈ A, z * a = a * z := by
  by_contra hnc
  push Not at hnc
  obtain ⟨B, hBA, hBne, hzB, hBfix⟩ :=
    exists_fpf_subgroup h.hp h.hp2 h.hzp (h.hS.to_le hAS) hAc hzA hnc
  haveI : Fact f.Prime := ⟨h.hf⟩
  obtain ⟨W, _, _, _, ρ, hW, hS₀, hz⟩ := exists_module h
  have hBS : B ≤ S := hBA.trans hAS
  have hBG : B ≤ S ⊔ zpowers z := hBS.trans le_sup_left
  have hzB' : zpowers z ≤ normalizer (B : Set K) := zpowers_le.mpr hzB
  have hKcomm : IsMulCommutative (B.subgroupOf (S ⊔ zpowers z)) := by
    refine IsMulCommutative.of_comm fun a b => ?_
    apply Subtype.ext
    apply Subtype.ext
    exact hAc _ (hBA a.2) _ (hBA b.2)
  have hBK : (zpowers z).subgroupOf (S ⊔ zpowers z) ≤
      normalizer ((B.subgroupOf (S ⊔ zpowers z) : Subgroup ↥(S ⊔ zpowers z)) :
        Set ↥(S ⊔ zpowers z)) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    have hgz : (g : K) ∈ zpowers z := mem_subgroupOf.mp hg
    have := mem_normalizer_iff.mp (hzB' hgz) (x : K)
    simpa [mem_subgroupOf] using this
  have hfpf : ∀ b ∈ (zpowers z).subgroupOf (S ⊔ zpowers z), b ≠ 1 →
      ∀ k ∈ B.subgroupOf (S ⊔ zpowers z), b * k = k * b → k = 1 := by
    intro b hb hb1 k hk hbk
    apply Subtype.ext
    apply hBfix _ (mem_subgroupOf.mp hk)
    exact clifford_commute_of_mem_zpowers h.hp h.hzp h.hz1 (mem_subgroupOf.mp hb)
      (fun h' => hb1 (Subtype.ext h')) (congrArg Subtype.val hbk)
  have hchar : ¬ ringChar (ZMod f) ∣ Nat.card (B.subgroupOf (S ⊔ zpowers z)) := by
    rw [ZMod.ringChar_zmod_n, Nat.card_congr (subgroupOfEquivOfLe hBG).toEquiv]
    exact clifford_not_dvd_card h.hf h.hf2 h.hS hBS
  have hfix : Representation.invariants (ρ.comp (B.subgroupOf (S ⊔ zpowers z)).subtype) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_bot]
    apply hS₀ B hBS hBne hzB' w
    intro g hg
    exact hw ⟨g, mem_subgroupOf.mpr hg⟩
  have hmain := CFSG.ABGLocalTools.finrank_invariants_mul_card_of_fixedPointFree ρ hKcomm hBK hfpf
    hchar hfix
  have hinv : Representation.invariants
      (ρ.comp ((zpowers z).subgroupOf (S ⊔ zpowers z)).subtype) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_bot]
    apply hz w
    exact hw ⟨⟨z, mem_sup_right (mem_zpowers z)⟩, mem_subgroupOf.mpr (mem_zpowers z)⟩
  rw [hinv, finrank_bot, zero_mul] at hmain
  have hpos : 0 < Module.finrank (ZMod f) W := Module.finrank_pos
  omega
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628
