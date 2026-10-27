module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB6Prop

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

namespace Hyp52

variable (h : Hyp52 X)

theorem sec8_Q_sylow (hJn : (h.J.subgroupOf (centralizer ({h.a} : Set X))).Normal) :
    h.Q ≤ centralizer ({h.a} : Set X) ⊓ normalizer (h.B : Set X) ∧
      ∃ R : Sylow 2 ↥(centralizer ({h.a} : Set X) ⊓ normalizer (h.B : Set X)),
        (R : Subgroup _) = h.Q.subgroupOf (centralizer ({h.a} : Set X) ⊓ normalizer (h.B : Set X))
    := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := centralizer ({h.a} : Set X) ⊓ normalizer (h.B : Set X) with hY
  have hSC : h.S ≤ centralizer ({h.a} : Set X) := h.S_le.trans inf_le_left
  have hCN : centralizer ({h.a} : Set X) ≤ normalizer (h.J : Set X) :=
    Six.centralizer_le_normalizer_of_normal h.J_le hJn
  have hS2 : IsPGroup 2 h.S := by
    obtain ⟨R, hR⟩ := h.S_sylow
    have h1 : IsPGroup 2 (h.S.subgroupOf (centralizer ({h.a} : Set X) ⊓
        normalizer (h.J : Set X))) := hR ▸ R.isPGroup'
    have h2 := h1.map (centralizer ({h.a} : Set X) ⊓ normalizer (h.J : Set X)).subtype
    rwa [map_subgroupOf_eq_of_le h.S_le] at h2
  have hQY : h.Q ≤ Y := le_inf (inf_le_left.trans hSC) inf_le_right
  refine ⟨hQY, ?_⟩
  have hQ2 : IsPGroup 2 (h.Q.subgroupOf Y) := (hS2.to_le inf_le_left).comap_subtype
  obtain ⟨R, hR⟩ := hQ2.exists_le_sylow
  set R₀ := (R : Subgroup Y).map Y.subtype with hR₀
  have hR₀Y : R₀ ≤ Y := map_subtype_le _
  have hQR₀ : h.Q ≤ R₀ := fun g hg => ⟨⟨g, hQY hg⟩, hR (mem_subgroupOf.mpr hg), rfl⟩
  have hR₀2 : IsPGroup 2 R₀ := R.isPGroup'.map _
  have hR₀CN : R₀ ≤ centralizer ({h.a} : Set X) ⊓ normalizer (h.J : Set X) :=
    le_inf (hR₀Y.trans inf_le_left) ((hR₀Y.trans inf_le_left).trans hCN)
  obtain ⟨c, hc, hcS⟩ := exists_conjugate_le_of_sylow h.S_sylow hR₀CN hR₀2
  have hca : c ∈ centralizer ({h.a} : Set X) := (mem_inf.mp hc).1
  have hcJ : c ∈ normalizer (h.J : Set X) := (mem_inf.mp hc).2
  have hcard : Nat.card R₀ ≤ Nat.card h.Q := by
    by_contra hlt
    push Not at hlt
    have hBQ : h.B ≤ h.Q := le_inf (h.B_le.trans inf_le_left) le_normalizer
    set E' := conjugate h.B c with hE'
    have hE'S : E' ≤ h.S := (map_mono (hBQ.trans hQR₀)).trans hcS
    have hE'C : E' ≤ coreActionKernel h.J := by
      rw [hE', ← Six.conjugate_coreActionKernel hcJ]
      exact map_mono (h.B_le.trans inf_le_right)
    have hE'card : Nat.card E' = Nat.card h.B := GSLit.card_conjugate h.B c
    have hle : conjugate R₀ c ≤ h.S ⊓ normalizer (E' : Set X) := by
      refine le_inf hcS ?_
      have hN : conjugate (normalizer (h.B : Set X)) c = normalizer (conjugate h.B c : Set X) :=
        map_equiv_normalizer_eq h.B (MulAut.conj c⁻¹)
      rw [hE', ← hN]
      exact map_mono (hR₀Y.trans inf_le_right)
    have hlt' : Nat.card ↥(h.S ⊓ normalizer (h.B : Set X)) <
        Nat.card ↥(h.S ⊓ normalizer (E' : Set X)) :=
      calc Nat.card ↥(h.S ⊓ normalizer (h.B : Set X)) < Nat.card R₀ := hlt
        _ = Nat.card (conjugate R₀ c) := (GSLit.card_conjugate R₀ c).symm
        _ ≤ _ := card_le_of_le hle
    obtain ⟨L, hL⟩ := h.isoCorr_of_lt E' (le_inf hE'S hE'C) (Or.inr ⟨hE'card, hlt'⟩)
    have hL' := Six.isoCorrSub_conjugate (inv_mem hca) (inv_mem hcJ) hL
    rw [hE', conjugate_conjugate, mul_inv_cancel, conjugate_one] at hL'
    exact h.not_isoCorrSub_B _ hL'
  have heq : h.Q = R₀ := eq_of_le_of_card_ge hQR₀ hcard
  refine ⟨R, ?_⟩
  rw [heq, hR₀]
  exact (comap_map_eq_self_of_injective Y.subtype_injective _).symm

theorem sec8_card_T (hT : h.T = h.B ⊔ zpowers h.a)
    (hC : h.P ⊓ centralizer (h.S : Set X) = zpowers h.a) : Nat.card h.T = 2 * Nat.card h.B := by
  classical
  have haB := Six.a_not_mem_B hC
  have haa := Six.a_mul_a_self h
  have hBT : h.B ≤ h.T := by
    rw [hT]
    exact le_sup_left
  have haT : h.a ∈ h.T := by
    rw [hT]
    exact mem_sup_right (mem_zpowers _)
  have hcomm : ∀ β ∈ h.B, β * h.a = h.a * β := fun β hβ =>
    Six.comm_a hC ((h.B_le.trans inf_le_left) hβ)
  have hcases : ∀ t ∈ h.T, ∃ β ∈ h.B, t = β ∨ t = β * h.a := by
    intro t ht
    let M : Subgroup X :=
      { carrier := {y | ∃ β ∈ h.B, y = β ∨ y = β * h.a}
        mul_mem' := by
          rintro y z ⟨β, hβ, hy⟩ ⟨γ, hγ, hz⟩
          refine ⟨β * γ, mul_mem hβ hγ, ?_⟩
          rcases hy with hy | hy <;> rcases hz with hz | hz <;> rw [hy, hz]
          · exact Or.inl rfl
          · exact Or.inr (by group)
          · refine Or.inr ?_
            rw [mul_assoc, ← hcomm γ hγ, ← mul_assoc]
          · refine Or.inl ?_
            rw [show β * h.a * (γ * h.a) = β * (h.a * γ) * h.a by group, ← hcomm γ hγ,
              show β * (γ * h.a) * h.a = β * γ * (h.a * h.a) by group, haa, mul_one]
        one_mem' := ⟨1, one_mem _, Or.inl rfl⟩
        inv_mem' := by
          rintro y ⟨β, hβ, hy⟩
          refine ⟨β⁻¹, inv_mem hβ, ?_⟩
          rcases hy with hy | hy <;> rw [hy]
          · exact Or.inl rfl
          · refine Or.inr ?_
            have ha' : h.a⁻¹ = h.a := inv_eq_of_mul_eq_one_right haa
            rw [mul_inv_rev, ha', eq_comm, inv_mul_eq_iff_eq_mul, ← mul_assoc, hcomm β hβ,
              mul_assoc, mul_inv_cancel, mul_one] }
    have hle : h.B ⊔ zpowers h.a ≤ M := by
      refine sup_le (fun β hβ => ⟨β, hβ, Or.inl rfl⟩) ?_
      rw [zpowers_le]
      exact ⟨1, one_mem _, Or.inr (one_mul _).symm⟩
    rw [hT] at ht
    exact hle ht
  have hidx : (h.B.subgroupOf h.T).index = 2 := by
    refine index_eq_two_iff.mpr ⟨⟨h.a, haT⟩, fun t => ?_⟩
    rw [mem_subgroupOf, mem_subgroupOf]
    obtain ⟨β, hβ, ht⟩ := hcases t t.2
    simp only [Subgroup.coe_mul]
    have hβa : β * h.a ∉ h.B := fun h1 => haB (by
      have := mul_mem (inv_mem hβ) h1
      rwa [inv_mul_cancel_left] at this)
    rcases ht with ht | ht
    · rw [ht]
      simp [hβ, hβa]
    · rw [ht, mul_assoc, haa, mul_one]
      simp [hβ, hβa]
  have h1 := card_mul_index (h.B.subgroupOf h.T)
  rw [hidx, Six.card_subgroupOf_eq, inf_eq_left.mpr hBT] at h1
  omega

theorem sec8_P4_setup (hT : h.T = h.B ⊔ zpowers h.a)
    (hC : h.P ⊓ centralizer (h.S : Set X) = zpowers h.a) (hP4 : Nat.card h.P = 4)
    (hxx : h.x * h.x = 1) :
    ∃ b : X, orderOf b = 2 ∧ h.B = zpowers b ∧ h.P = h.T ∧
      (∀ w ∈ h.P, w = 1 ∨ w = h.a ∨ w = b ∨ w = h.a * b) ∧ b * h.a = h.a * b ∧
      h.x * b * h.x⁻¹ = h.a * b ∧ h.x⁻¹ * b * h.x = h.a * b ∧
      normalizer (h.B : Set X) = centralizer ({b} : Set X) ∧
      h.Q = h.S ⊓ centralizer ({b} : Set X) ∧
      ((centralizer ({b} : Set X)).subgroupOf h.S).index = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haB := Six.a_not_mem_B hC
  have haa := Six.a_mul_a_self h
  have ha' : h.a⁻¹ = h.a := inv_eq_of_mul_eq_one_right haa
  have ha1 : h.a ≠ 1 := by
    intro h1
    have := h.orderOf_a
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  have hTP : h.T ≤ h.P := inf_le_right
  have hcardT := h.sec8_card_T hT hC
  have hB2 : IsPGroup 2 h.B := by
    obtain ⟨R, hR⟩ := h.S_sylow
    have h1 : IsPGroup 2 (h.S.subgroupOf (centralizer ({h.a} : Set X) ⊓
        normalizer (h.J : Set X))) := hR ▸ R.isPGroup'
    have h2 := h1.map (centralizer ({h.a} : Set X) ⊓ normalizer (h.J : Set X)).subtype
    rw [map_subgroupOf_eq_of_le h.S_le] at h2
    exact h2.to_le (h.B_le.trans inf_le_left)
  have hTle : Nat.card h.T ≤ 4 := hP4 ▸ card_le_of_le hTP
  have hBcard : Nat.card h.B = 2 := by
    have hB1 : Nat.card h.B ≠ 1 := fun h1 => h.B_ne_bot ((card_eq_one).mp h1)
    obtain ⟨k, hk⟩ := hB2.exists_card_eq
    rcases k with _ | _ | k
    · exact absurd (by rw [hk, pow_zero]) hB1
    · rw [hk, pow_one]
    · exfalso
      rw [hk] at hcardT
      have : 2 * 2 ^ (k + 2) ≤ 4 := hcardT ▸ hTle
      have h8 : 8 ≤ 2 * 2 ^ (k + 2) := by
        rw [pow_succ, pow_succ]
        have := Nat.one_le_two_pow (n := k)
        omega
      omega
  have hPT : h.P = h.T := (eq_of_le_of_card_ge hTP (by rw [hP4, hcardT, hBcard])).symm
  obtain ⟨⟨b', hbB'⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h.B_ne_bot
  have hb1' : b' ≠ 1 := fun h1 => hb1 (Subtype.ext h1)
  have hzB : zpowers b' = h.B := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr hbB')
    rw [hBcard, Nat.card_zpowers]
    have hdvd : orderOf b' ∣ 2 := hBcard ▸ Subgroup.orderOf_dvd_natCard _ hbB'
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hb1'
    · exact h1.ge
  have hbo : orderOf b' = 2 := by
    rw [← Nat.card_zpowers, hzB, hBcard]
  have hbb : b' * b' = 1 := by rw [← pow_two, ← hbo, pow_orderOf_eq_one]
  have hb'inv : b'⁻¹ = b' := inv_eq_of_mul_eq_one_right hbb
  have hbS : b' ∈ h.S := (h.B_le.trans inf_le_left) hbB'
  have hab : b' * h.a = h.a * b' := Six.comm_a hC hbS
  have hba : b' ≠ h.a := fun h1 => haB (h1 ▸ hbB')
  have hBmem : ∀ β ∈ h.B, β = 1 ∨ β = b' := by
    intro β hβ
    rw [← hzB] at hβ
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hβ
    have h2 : b' ^ (2 : ℤ) = 1 := by rw [zpow_two, hbb]
    obtain ⟨r, hr | hr⟩ := Int.even_or_odd' k
    · left
      rw [hr, zpow_mul, h2, one_zpow]
    · right
      rw [hr, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
  have hPmem : ∀ w ∈ h.P, w = 1 ∨ w = h.a ∨ w = b' ∨ w = h.a * b' := by
    intro w hw
    rw [hPT, hT] at hw
    have hle : h.B ⊔ zpowers h.a ≤ closure ({h.a, b'} : Set X) :=
      sup_le (by rw [← hzB, zpowers_le]; exact subset_closure (by simp))
        (by rw [zpowers_le]; exact subset_closure (by simp))
    rcases Six.mem_closure_pair_cases haa hbb hab (hle hw) with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr h1))
  have hxS : h.x ∈ h.S := h.x_mem
  have hxa : h.x * h.a = h.a * h.x := Six.comm_a hC hxS
  have hbP : b' ∈ h.P := h.B_le hbB'
  have hxb : h.x * b' * h.x⁻¹ = h.a * b' := by
    have hmem : h.x * b' * h.x⁻¹ ∈ h.P := by
      exact Six.conj_mem_P h hxS hbP
    rcases hPmem _ hmem with h1 | h1 | h1 | h1
    · exfalso
      apply hb1'
      calc b' = h.x⁻¹ * (h.x * b' * h.x⁻¹) * h.x := by group
        _ = 1 := by rw [h1]; group
    · exfalso
      apply hba
      calc b' = h.x⁻¹ * (h.x * b' * h.x⁻¹) * h.x := by group
        _ = h.x⁻¹ * (h.a * h.x) := by rw [h1, mul_assoc]
        _ = h.a := by rw [← hxa, inv_mul_cancel_left]
    · exfalso
      have hmem2 : b' ∈ h.B ⊓ conjugate h.B h.x :=
        mem_inf.mpr ⟨hbB', mem_conjugate_iff.mpr (by rw [h1]; exact hbB')⟩
      rw [h.inf_conjugate_x, mem_bot] at hmem2
      exact hb1' hmem2
    · exact h1
  have hxinv : h.x⁻¹ = h.x := inv_eq_of_mul_eq_one_right hxx
  have hxb' : h.x⁻¹ * b' * h.x = h.a * b' := by
    rw [hxinv]
    calc h.x * b' * h.x = h.x * b' * h.x⁻¹ := by rw [hxinv]
      _ = h.a * b' := hxb
  have hNC : normalizer (h.B : Set X) = centralizer ({b'} : Set X) := by
    ext g
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro hg
      have h1 : g * b' * g⁻¹ ∈ h.B := (mem_normalizer_iff.mp hg b').mp hbB'
      rcases hBmem _ h1 with h2 | h2
      · exfalso
        apply hb1'
        calc b' = g⁻¹ * (g * b' * g⁻¹) * g := by group
          _ = 1 := by rw [h2]; group
      · calc g * b' = g * b' * g⁻¹ * g := by group
          _ = b' * g := by rw [h2]
    · intro hg
      rw [mem_normalizer_iff]
      intro β
      have hgb : g * b' * g⁻¹ = b' := by rw [hg, mul_inv_cancel_right]
      constructor
      · intro hβ
        rcases hBmem _ hβ with rfl | rfl
        · simp
        · rw [hgb]
          exact hbB'
      · intro hβ
        rcases hBmem _ hβ with h1 | h1
        · have : β = 1 := by
            calc β = g⁻¹ * (g * β * g⁻¹) * g := by group
              _ = 1 := by rw [h1]; group
          rw [this]
          exact one_mem _
        · have : β = b' := by
            calc β = g⁻¹ * (g * β * g⁻¹) * g := by group
              _ = g⁻¹ * (g * b' * g⁻¹) * g := by rw [h1, hgb]
              _ = b' := by group
          rw [this]
          exact hbB'
  have hQC : h.Q = h.S ⊓ centralizer ({b'} : Set X) := by
    show h.S ⊓ normalizer (h.B : Set X) = _
    rw [hNC]
  have hindex : ((centralizer ({b'} : Set X)).subgroupOf h.S).index = 2 := by
    have hsb : ∀ s ∈ h.S, s * b' * s⁻¹ = b' ∨ s * b' * s⁻¹ = h.a * b' := by
      intro s hs
      have hmem : s * b' * s⁻¹ ∈ h.P := Six.conj_mem_P h hs hbP
      rcases hPmem _ hmem with h1 | h1 | h1 | h1
      · exfalso
        apply hb1'
        calc b' = s⁻¹ * (s * b' * s⁻¹) * s := by group
          _ = 1 := by rw [h1]; group
      · exfalso
        apply hba
        have hsa : s * h.a = h.a * s := Six.comm_a hC hs
        calc b' = s⁻¹ * (s * b' * s⁻¹) * s := by group
          _ = s⁻¹ * (h.a * s) := by rw [h1, mul_assoc]
          _ = h.a := by rw [← hsa, inv_mul_cancel_left]
      · exact Or.inl h1
      · exact Or.inr h1
    have hmemC : ∀ t : h.S, t ∈ (centralizer ({b'} : Set X)).subgroupOf h.S ↔
        (t : X) * b' * (t : X)⁻¹ = b' := by
      intro t
      rw [mem_subgroupOf, mem_centralizer_singleton_iff]
      constructor
      · intro h1
        rw [h1, mul_inv_cancel_right]
      · intro h1
        calc (t : X) * b' = (t : X) * b' * (t : X)⁻¹ * (t : X) := by group
          _ = b' * (t : X) := by rw [h1]
    refine index_eq_two_iff.mpr ⟨⟨h.x, hxS⟩, fun t => ?_⟩
    rw [hmemC, hmemC]
    simp only [Subgroup.coe_mul]
    have hxb2 : (t : X) * h.x * b' * ((t : X) * h.x)⁻¹ =
        (t : X) * h.a * (t : X)⁻¹ * ((t : X) * b' * (t : X)⁻¹) := by
      calc (t : X) * h.x * b' * ((t : X) * h.x)⁻¹ = (t : X) * (h.x * b' * h.x⁻¹) * (t : X)⁻¹ := by
            group
        _ = (t : X) * (h.a * b') * (t : X)⁻¹ := by rw [hxb]
        _ = _ := by group
    have hta : (t : X) * h.a * (t : X)⁻¹ = h.a := by
      rw [Six.comm_a hC t.2, mul_inv_cancel_right]
    rw [hxb2, hta]
    have hab1 : h.a * b' ≠ b' := fun h2 => ha1 (by
      calc h.a = h.a * b' * b'⁻¹ := by group
        _ = 1 := by rw [h2, mul_inv_cancel])
    rcases hsb t t.2 with h1 | h1
    · rw [h1]
      simp [hab1]
    · rw [h1, ← mul_assoc, haa, one_mul]
      simp [hab1]
  exact ⟨b', hbo, hzB.symm, hPT, hPmem, hab, hxb, hxb', hNC, hQC, hindex⟩

end Hyp52

end CFSG.ComponentClassification.GSThmB
