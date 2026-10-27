module

public import CFSG.LargeExtraspecial.AS35QIxFrob
public import CFSG.LargeExtraspecial.AS35QIxOrd

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QIx

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace IxLift

variable (T : IxLift S)

theorem F_mem_Mbar (hS : S.SixHyp) {m₁ : S.O} (hm₁ : m₁ ∈ S.Mbar)
    (hm₁ζ : m₁ * T.ζ ≠ T.ζ * m₁) : T.F ∈ S.Mbar := by
  have h1 := T.conj_inv_of_not_comm hm₁ hm₁ζ
  have h2 := T.comm_of_inv_of_inv h1 T.F_inv_zeta
  have h3 := T.mem_Mbar_of_comm hS h2
  have e : T.F = m₁⁻¹ * (m₁ * T.F) := by group
  rw [e]
  exact S.Mbar.mul_mem (S.Mbar.inv_mem hm₁) h3

theorem card_Mbar_of_not_comm (hS : S.SixHyp) {m₁ : S.O} (hm₁ : m₁ ∈ S.Mbar)
    (hm₁ζ : m₁ * T.ζ ≠ T.ζ * m₁) : Nat.card S.Mbar = 1296 := by
  have := AS35QTh.finite_O S
  have hF := T.F_mem_Mbar hS hm₁ hm₁ζ
  set H : Subgroup S.Mbar := T.Mbar0.subgroupOf S.Mbar with hH
  have hmemH : ∀ b : S.Mbar, b ∈ H ↔ (b : S.O) * T.ζ = T.ζ * b := by
    intro b
    rw [hH, mem_subgroupOf, T.mem_Mbar0]
    exact ⟨fun h => h.2, fun h => ⟨b.2, h⟩⟩
  have hidx : H.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨T.F, hF⟩, fun b => ?_⟩
    rw [hmemH, hmemH]
    simp only [Subgroup.coe_mul]
    rcases T.conj_zeta b.2 with h | h
    · have hb := T.comm_of_conj_eq h
      refine Or.inr ⟨hb, ?_⟩
      intro hbF
      apply T.F_not_comm
      calc T.F * T.ζ = (b : S.O)⁻¹ * ((b * T.F) * T.ζ) := by group
        _ = (b : S.O)⁻¹ * (T.ζ * (b * T.F)) := by rw [hbF]
        _ = (b : S.O)⁻¹ * (T.ζ * b) * T.F := by group
        _ = (b : S.O)⁻¹ * (b * T.ζ) * T.F := by rw [hb]
        _ = T.ζ * T.F := by group
    · refine Or.inl ⟨T.comm_of_inv_of_inv h T.F_inv_zeta, ?_⟩
      intro hb
      apply T.zeta_ne_inv
      rw [← h, hb, mul_assoc, mul_inv_cancel, mul_one]
  have h1 := H.index_mul_card
  rw [hidx] at h1
  have h2 : Nat.card H = Nat.card T.Mbar0 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h2, T.card_Mbar0 hS] at h1
  omega

theorem card_le_sixteen (hS : S.SixHyp) {m₁ : S.O} (hm₁ : m₁ ∈ S.Mbar)
    (hm₁ζ : m₁ * T.ζ ≠ T.ζ * m₁) {P : Subgroup S.O} (hPM : P ≤ S.Mbar) (hP : IsPGroup 2 P) :
    Nat.card P ≤ 16 := by
  have := AS35QTh.finite_O S
  have hdvd : Nat.card P ∣ 1296 := by
    rw [← T.card_Mbar_of_not_comm hS hm₁ hm₁ζ]
    exact Subgroup.card_dvd_of_le hPM
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  rw [hk] at hdvd ⊢
  by_contra hlt
  push Not at hlt
  have h5 : 5 ≤ k := by
    by_contra h
    push Not at h
    interval_cases k <;> norm_num at hlt
  have : 2 ^ 5 ∣ 1296 := (pow_dvd_pow 2 h5).trans hdvd
  norm_num at this

theorem exists_conj_mem_of_max {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    {P : Subgroup H} (hmax : ∀ Q : Subgroup H, IsPGroup p Q → P ≤ Q → Nat.card Q ≤ Nat.card P)
    (hP : IsPGroup p P) {x : H} (hx : IsPGroup p (zpowers x)) : ∃ m : H, m * x * m⁻¹ ∈ P := by
  obtain ⟨S₁, hS₁⟩ := hx.exists_le_sylow
  obtain ⟨S₂, hS₂⟩ := hP.exists_le_sylow
  have heq : P = S₂ := Subgroup.eq_of_le_of_card_ge hS₂ (hmax _ S₂.2 hS₂)
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq H S₁ S₂
  refine ⟨m, ?_⟩
  rw [heq, ← hm, Sylow.coe_subgroup_smul]
  exact Subgroup.smul_mem_pointwise_smul _ _ _ (hS₁ (mem_zpowers x))

theorem F_isPGroup (hF : T.F ∈ S.Mbar) : IsPGroup 2 (zpowers (⟨T.F, hF⟩ : S.Mbar)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine IsPGroup.of_card (n := 1) ?_
  rw [Nat.card_zpowers, pow_one]
  refine orderOf_eq_prime ?_ ?_
  · exact Subtype.ext (by rw [pow_two]; exact T.F_mul_self)
  · intro h
    apply T.F_not_comm
    have : T.F = 1 := congrArg Subtype.val h
    rw [this, one_mul, mul_one]

theorem exists_outer_involution (hS : S.SixHyp) {m₁ : S.O} (hm₁ : m₁ ∈ S.Mbar)
    (hm₁ζ : m₁ * T.ζ ≠ T.ζ * m₁) {P : Subgroup S.O} (hPM : P ≤ S.Mbar) (hP : IsPGroup 2 P)
    (hcard : 16 ≤ Nat.card P) : ∃ σ ∈ P, σ * σ = 1 ∧ σ * T.ζ ≠ T.ζ * σ := by
  have := AS35QTh.finite_O S
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := T.F_mem_Mbar hS hm₁ hm₁ζ
  have hP' : IsPGroup 2 (P.subgroupOf S.Mbar) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPM).symm
  have hP'card : Nat.card (P.subgroupOf S.Mbar) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv
  have hmax : ∀ Q : Subgroup S.Mbar, IsPGroup 2 Q → P.subgroupOf S.Mbar ≤ Q →
      Nat.card Q ≤ Nat.card (P.subgroupOf S.Mbar) := by
    intro Q hQ _
    have h := T.card_le_sixteen hS hm₁ hm₁ζ (P := Q.map S.Mbar.subtype)
      (Subgroup.map_subtype_le _) (hQ.map _)
    rw [Subgroup.card_map_of_injective S.Mbar.subtype_injective] at h
    omega
  obtain ⟨m, hm⟩ := exists_conj_mem_of_max hmax hP' (T.F_isPGroup hF)
  refine ⟨(m : S.O) * T.F * (m : S.O)⁻¹, mem_subgroupOf.mp hm, ?_, ?_⟩
  · rw [show (m : S.O) * T.F * (m : S.O)⁻¹ * ((m : S.O) * T.F * (m : S.O)⁻¹) =
      (m : S.O) * (T.F * T.F) * (m : S.O)⁻¹ by group, T.F_mul_self]
    group
  · intro hc
    have hc' : T.F * ((m : S.O)⁻¹ * T.ζ * m) = ((m : S.O)⁻¹ * T.ζ * m) * T.F := by
      calc T.F * ((m : S.O)⁻¹ * T.ζ * m) =
          (m : S.O)⁻¹ * (((m : S.O) * T.F * (m : S.O)⁻¹) * T.ζ) * m := by group
        _ = (m : S.O)⁻¹ * (T.ζ * ((m : S.O) * T.F * (m : S.O)⁻¹)) * m := by rw [hc]
        _ = ((m : S.O)⁻¹ * T.ζ * m) * T.F := by group
    apply T.F_not_comm
    rcases T.conj_zeta (S.Mbar.inv_mem m.2) with h | h
    · rw [inv_inv] at h
      rw [h] at hc'
      exact hc'
    · rw [inv_inv] at h
      rw [h] at hc'
      exact (Commute.inv_right_iff.mp hc').eq

end IxLift

end CFSG.LargeExtraspecial.AS35QIx
