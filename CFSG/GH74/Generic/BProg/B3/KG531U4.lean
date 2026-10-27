module

public import CFSG.GH74.Generic.BProg.B3.KG531Crit
public import CFSG.GH74.Generic.BProg.B3.KG531U4Arith
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClU4Single
public import CFSG.GH74.Orders.LieType

public section

namespace CFSG.GH74.Generic.BProg.B3

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped MatrixGroups commutatorElement

namespace KG531U4

theorem commutator_top_eq_top {S : Type} [Group S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = ⊤ := by
  have := hS
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have hm : ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
    exact hm
  · exact h

theorem card_B₁ {S : Type} [Group S] {t : S} {B₁ B₂ : Subgroup S} {p f : ℕ}
    (h : KG531Cfg t B₁ B₂ p f) : Nat.card ↥B₁ = p ^ f * (p ^ (2 * f) - 1) / 2 := by
  have hz : Nat.card ↥(center ↥B₁) = 1 := by
    rw [h.center₁]
    exact Subgroup.card_bot
  have hc : Nat.card ↥B₁ = Nat.card (↥B₁ ⧸ center ↥B₁) * Nat.card ↥(center ↥B₁) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [hz, mul_one, KG531Crit.card_psl_two h.prime h.odd h.model₁] at hc
  exact hc

theorem card_B₂ {S : Type} [Group S] {t : S} {B₁ B₂ : Subgroup S} {p f : ℕ}
    (h : KG531Cfg t B₁ B₂ p f) : Nat.card ↥B₂ = 2 * Nat.card ↥B₁ := by
  rw [card_B₁ h, KG531Crit.card_sl_two h.model₂]
  have hq := CFSG.GH74.Generic.S1.kl5_odd_pow (f := f) h.prime h.odd
  have hpow : p ^ (2 * f) = (p ^ f) ^ 2 := by rw [← pow_mul, mul_comm]
  have hodd : (p ^ (2 * f)) % 2 = 1 := by
    rw [hpow, pow_two, Nat.mul_mod, hq]
  have hev : 2 ∣ p ^ f * (p ^ (2 * f) - 1) := Dvd.dvd.mul_left (by omega) _
  exact (Nat.mul_div_cancel' hev).symm

theorem card_B₁_eq {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hL : LieModel S .PSU 4 p f) {t : S} {B₁ B₂ : Subgroup S} {p' f' : ℕ}
    (h : KG531Cfg t B₁ B₂ p' f') :
    Nat.card ↥B₁ = (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) / 2 := by
  have := hS
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := CFSG.GH74.statedClassicalModel_of_lieModel (by norm_num) hL
  have hcomp : CFSG.Assembly.IsComponentOf B₁ ((⊤ : Subgroup S) ⊓ centralizer ({t} : Set S)) := by
    rw [top_inf_eq]
    exact (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf h.comp₁.1).2
      h.comp₁.2
  have hsmall : CFSG.ComponentClassification.RestrictedStd.SmallSource B₁ := by
    refine Or.inl ⟨p', f', h.prime, h.odd, ?_, h.five, Or.inl ⟨by decide, h.model₁⟩, ?_⟩
    · rcases Nat.eq_zero_or_pos f' with h0 | h0
      · have h5 := h.five
        rw [h0, pow_zero] at h5
        omega
      · exact h0
    · rw [h.center₁, Subgroup.card_bot]
      exact odd_one
  have hWs : IsSimpleGroup ↥(⊤ : Subgroup S) := Subgroup.topEquiv.isSimpleGroup
  have hWnab : ∃ x y : ↥(⊤ : Subgroup S), x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨⟨a, Subgroup.mem_top a⟩, ⟨b, Subgroup.mem_top b⟩, fun hh => hab (congrArg Subtype.val hh)⟩
  have hCW : centralizer ((⊤ : Subgroup S) : Set S) = ⊥ := by
    rw [Subgroup.coe_top, Subgroup.centralizer_univ]
    exact CFSG.ComponentClassification.OutcomeLocal.center_eq_bot_of_isSimpleGroup hnab
  have ht1 : t ∈ ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ := by
    rw [commutator_top_eq_top hS hnab]
    exact Subgroup.mem_top t
  obtain ⟨E, _, _, hE, ⟨eB⟩⟩ := CFSG.GH74.GLS.IVK.su4_single_rowS (A := S) (W := ⊤) hWs hWnab hCW
    h.t_ord ht1 hcomp hsmall hp hp2 hf hK (Subgroup.topEquiv.trans e)
  have hodd : Odd p := hp.odd_of_ne_two hp2
  rw [Nat.card_congr eB.toEquiv,
    ← Nat.card_congr (LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
      2 E).toEquiv,
    CFSG.GorensteinWalter.psl2_card_formula E
      ⟨p, 2 * f, hp, hodd, by omega, by rw [hE, ← pow_mul, mul_comm]⟩, hE]

end KG531U4

theorem kg531_u4 (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (_hmod : p ^ f % 8 ≠ 7) :
    KG531Empty (fun X _ => LieModel X .PSU 4 p f) := by
  intro S _ _ hS hnab hL t B₁ B₂ p' f' h
  have hB₁ := KG531U4.card_B₁_eq hS hnab hp hp2 hf hL h
  have hdvd : Nat.card ↥B₁ * Nat.card ↥B₂ ∣ Nat.card S :=
    (KG531Crit.card_mul_dvd_of_commute_disjoint h.comp₁.1 h.comp₂.1 h.comm h.disj).trans
      (Subgroup.card_subgroup_dvd_card _)
  rw [KG531U4.card_B₂ h, CFSG.GH74.card_of_lieModel_PSU (by norm_num) hp2 hL] at hdvd
  have hq := CFSG.GH74.Generic.S1.kl5_odd_pow (f := f) hp hp2
  have h3 : 3 ≤ p ^ f := by
    have hodd : Odd p := hp.odd_of_ne_two hp2
    have h2 := hp.two_le
    have : 3 ≤ p := by
      obtain ⟨k, hk⟩ := hodd
      omega
    exact this.trans (Nat.le_self_pow (by omega) p)
  exact KG531U4Arith.not_dvd_card_u4 (p ^ f) hq h3 hB₁ hdvd

end CFSG.GH74.Generic.BProg.B3
