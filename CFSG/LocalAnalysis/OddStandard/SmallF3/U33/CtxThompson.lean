module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Wreath
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.CtxCommute

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type*} [Group G] {x₁ x₂ lam : G}

private theorem baseGrp_le_wreathGrp : baseGrp x₁ x₂ ≤ wreathGrp x₁ x₂ lam := by
  rw [baseGrp, wreathGrp]
  exact Subgroup.closure_mono (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl <;> simp)

private theorem commute_sup_wreathGrp {P : Subgroup G} (hPc : IsMulCommutative ↥P)
    (hcomm : ∀ a ∈ P, ∀ b ∈ wreathGrp x₁ x₂ lam, a * b = b * a) :
    ∀ p ∈ P, ∀ y ∈ P ⊔ wreathGrp x₁ x₂ lam, p * y = y * p := by
  haveI : IsMulCommutative ↥P := hPc
  intro p hp y hy
  obtain ⟨a, ha, s, hs, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp hy
  calc p * (a * s) = (p * a) * s := by rw [mul_assoc]
    _ = (a * p) * s := by rw [setLike_mul_comm (s := P) hp ha]
    _ = a * (p * s) := by rw [mul_assoc]
    _ = a * (s * p) := by rw [hcomm p hp s hs]
    _ = (a * s) * p := by rw [mul_assoc]

private theorem abelian_le_sup_wreathGrp_decomp [Finite G] {P C : Subgroup G}
    (h : WreathRel x₁ x₂ lam)
    (hcomm : ∀ a ∈ P, ∀ b ∈ wreathGrp x₁ x₂ lam, a * b = b * a)
    (hinf : P ⊓ wreathGrp x₁ x₂ lam = ⊥)
    (hPC : P ≤ C) (hCPT : C ≤ P ⊔ wreathGrp x₁ x₂ lam) (hC : IsMulCommutative ↥C) :
    C = P ⊔ (wreathGrp x₁ x₂ lam ⊓ C) ∧
      Nat.card ↥C = Nat.card ↥P * Nat.card ↥(wreathGrp x₁ x₂ lam ⊓ C) ∧
      Nat.card ↥(wreathGrp x₁ x₂ lam ⊓ C) ≤ 16 ∧
      (Nat.card ↥(wreathGrp x₁ x₂ lam ⊓ C) = 16 → C = P ⊔ baseGrp x₁ x₂) := by
  haveI : IsMulCommutative ↥C := hC
  have hD_le_T : wreathGrp x₁ x₂ lam ⊓ C ≤ wreathGrp x₁ x₂ lam := inf_le_left
  have hD_le_C : wreathGrp x₁ x₂ lam ⊓ C ≤ C := inf_le_right
  have hDcomm : IsMulCommutative ↥(wreathGrp x₁ x₂ lam ⊓ C) :=
    IsMulCommutative.of_setLike_mul_comm fun a ha b hb =>
      setLike_mul_comm (s := C) (hD_le_C ha) (hD_le_C hb)
  have hPD : ∀ a ∈ P, ∀ b ∈ wreathGrp x₁ x₂ lam ⊓ C, a * b = b * a :=
    fun a ha b hb => hcomm a ha b hb.1
  have hCeq : C = P ⊔ (wreathGrp x₁ x₂ lam ⊓ C) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨a, ha, s, hs, rfl⟩ := (mem_sup_iff_of_commute hcomm).mp (hCPT hx)
      have hsC : s ∈ C := by
        have h1 : a⁻¹ * (a * s) ∈ C :=
          Subgroup.mul_mem C (Subgroup.inv_mem C (hPC ha)) hx
        rwa [← mul_assoc, inv_mul_cancel, one_mul] at h1
      exact (mem_sup_iff_of_commute hPD).mpr ⟨a, ha, s, ⟨hs, hsC⟩, rfl⟩
    · exact sup_le hPC inf_le_right
  have hPinfD : P ⊓ (wreathGrp x₁ x₂ lam ⊓ C) = ⊥ := by
    apply le_antisymm ?_ bot_le
    calc P ⊓ (wreathGrp x₁ x₂ lam ⊓ C) ≤ P ⊓ wreathGrp x₁ x₂ lam :=
          inf_le_inf le_rfl inf_le_left
      _ = ⊥ := hinf
  have hcardC : Nat.card ↥C = Nat.card ↥P * Nat.card ↥(wreathGrp x₁ x₂ lam ⊓ C) := by
    conv_lhs => rw [hCeq]
    exact card_sup_of_commute hPD hPinfD
  have hD16 : Nat.card ↥(wreathGrp x₁ x₂ lam ⊓ C) ≤ 16 :=
    h.card_le_sixteen hD_le_T hDcomm
  refine ⟨hCeq, hcardC, hD16, ?_⟩
  intro hcard
  have hDA : wreathGrp x₁ x₂ lam ⊓ C = baseGrp x₁ x₂ :=
    h.eq_baseGrp_of_card_sixteen hD_le_T hDcomm hcard
  rw [hCeq, hDA]

private theorem card_le_card_sup_baseGrp [Finite G] {P : Subgroup G} (h : WreathRel x₁ x₂ lam)
    (hPc : IsMulCommutative ↥P)
    (hcomm : ∀ a ∈ P, ∀ b ∈ wreathGrp x₁ x₂ lam, a * b = b * a)
    (hinf : P ⊓ wreathGrp x₁ x₂ lam = ⊥)
    (hcardW : Nat.card ↥(P ⊔ baseGrp x₁ x₂) = Nat.card ↥P * 16)
    {B : Subgroup G} (hB : B ≤ P ⊔ wreathGrp x₁ x₂ lam) (hBc : IsMulCommutative ↥B) :
    Nat.card ↥B ≤ Nat.card ↥(P ⊔ baseGrp x₁ x₂) := by
  haveI : IsMulCommutative ↥P := hPc
  haveI : IsMulCommutative ↥B := hBc
  have hP_PT := commute_sup_wreathGrp (P := P) hPc hcomm
  have hPB : ∀ b ∈ B, ∀ p ∈ P, b * p = p * b := by
    intro b hb p hp
    exact (hP_PT p hp b (hB hb)).symm
  have hB'c : IsMulCommutative ↥(B ⊔ P) :=
    isMulCommutative_sup_of_commute hPB hBc hPc
  have hB'le : B ⊔ P ≤ P ⊔ wreathGrp x₁ x₂ lam := sup_le hB le_sup_left
  obtain ⟨-, hcardB', hD16, -⟩ :=
    abelian_le_sup_wreathGrp_decomp (P := P) (C := B ⊔ P) h hcomm hinf le_sup_right hB'le hB'c
  calc Nat.card ↥B ≤ Nat.card ↥(B ⊔ P) := Subgroup.card_le_of_le le_sup_left
    _ = Nat.card ↥P * Nat.card ↥(wreathGrp x₁ x₂ lam ⊓ (B ⊔ P)) := hcardB'
    _ ≤ Nat.card ↥P * 16 := Nat.mul_le_mul_left _ hD16
    _ = Nat.card ↥(P ⊔ baseGrp x₁ x₂) := hcardW.symm

theorem ambientMaxCardThompson_sup_wreathGrp [Finite G] {P : Subgroup G} (h : WreathRel x₁ x₂ lam)
    (hPc : IsMulCommutative P) (hcomm : ∀ a ∈ P, ∀ b ∈ wreathGrp x₁ x₂ lam, a * b = b * a)
    (hinf : P ⊓ wreathGrp x₁ x₂ lam = ⊥) :
    CFSG.ambientMaxCardThompson (P ⊔ wreathGrp x₁ x₂ lam) = P ⊔ baseGrp x₁ x₂ := by
  haveI : IsMulCommutative ↥P := hPc
  have hAT : baseGrp x₁ x₂ ≤ wreathGrp x₁ x₂ lam := baseGrp_le_wreathGrp
  have hPA : ∀ a ∈ P, ∀ b ∈ baseGrp x₁ x₂, a * b = b * a :=
    fun a ha b hb => hcomm a ha b (hAT hb)
  have hWcomm : IsMulCommutative ↥(P ⊔ baseGrp x₁ x₂) :=
    isMulCommutative_sup_of_commute hPA hPc (h.baseGrp_eq).1
  have hWle : P ⊔ baseGrp x₁ x₂ ≤ P ⊔ wreathGrp x₁ x₂ lam := sup_le_sup_left hAT P
  have hPinfA : P ⊓ baseGrp x₁ x₂ = ⊥ := by
    apply le_antisymm ?_ bot_le
    calc P ⊓ baseGrp x₁ x₂ ≤ P ⊓ wreathGrp x₁ x₂ lam := inf_le_inf le_rfl hAT
      _ = ⊥ := hinf
  have hcardW : Nat.card ↥(P ⊔ baseGrp x₁ x₂) = Nat.card ↥P * 16 := by
    rw [card_sup_of_commute hPA hPinfA, (h.baseGrp_eq).2.2]
  have hWmem : (P ⊔ baseGrp x₁ x₂) ∈
      CFSG.ambientMaxCardAbelianFamily (P ⊔ wreathGrp x₁ x₂ lam) := by
    refine ⟨hWle, hWcomm, ?_⟩
    intro B hB hBc
    exact card_le_card_sup_baseGrp h hPc hcomm hinf hcardW hB hBc
  have hfamily_le : ∀ B ∈ CFSG.ambientMaxCardAbelianFamily (P ⊔ wreathGrp x₁ x₂ lam),
      B ≤ P ⊔ baseGrp x₁ x₂ := by
    intro B hB
    obtain ⟨hBle, hBcomm, hBmax⟩ := hB
    have hcardWB : Nat.card ↥(P ⊔ baseGrp x₁ x₂) ≤ Nat.card ↥B := hBmax _ hWle hWcomm
    have hcardBW : Nat.card ↥B ≤ Nat.card ↥(P ⊔ baseGrp x₁ x₂) :=
      card_le_card_sup_baseGrp h hPc hcomm hinf hcardW hBle hBcomm
    have hcard_eq : Nat.card ↥B = Nat.card ↥(P ⊔ baseGrp x₁ x₂) := le_antisymm hcardBW hcardWB
    have hPB : ∀ b ∈ B, ∀ p ∈ P, b * p = p * b := by
      intro b hb p hp
      exact (commute_sup_wreathGrp (P := P) hPc hcomm p hp b (hBle hb)).symm
    have hB'c : IsMulCommutative ↥(B ⊔ P) :=
      isMulCommutative_sup_of_commute hPB hBcomm hPc
    have hB'le : B ⊔ P ≤ P ⊔ wreathGrp x₁ x₂ lam := sup_le hBle le_sup_left
    have hcardB'W : Nat.card ↥(B ⊔ P) ≤ Nat.card ↥(P ⊔ baseGrp x₁ x₂) :=
      card_le_card_sup_baseGrp h hPc hcomm hinf hcardW hB'le hB'c
    have hBB' : B = B ⊔ P :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (hcardB'W.trans (le_of_eq hcard_eq.symm))
    have hPB_le : P ≤ B := hBB'.symm ▸ le_sup_right
    obtain ⟨-, hcardB, -, heq⟩ :=
      abelian_le_sup_wreathGrp_decomp (P := P) (C := B) h hcomm hinf hPB_le hBle hBcomm
    have hmul : Nat.card ↥P * Nat.card ↥(wreathGrp x₁ x₂ lam ⊓ B) = Nat.card ↥P * 16 := by
      rw [← hcardB, hcard_eq, hcardW]
    have hD16eq : Nat.card ↥(wreathGrp x₁ x₂ lam ⊓ B) = 16 :=
      Nat.mul_left_cancel (Nat.card_pos (α := P)) hmul
    exact le_of_eq (heq hD16eq)
  unfold CFSG.ambientMaxCardThompson
  exact le_antisymm (sSup_le fun B hB => hfamily_le B hB)
    (CFSG.le_ambientMaxCardThompson hWmem)

end CFSG.OddStandard.SmallF3.HarrisU33
