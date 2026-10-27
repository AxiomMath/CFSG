module

public import CFSG.LocalAnalysis.EvenBN.U5.LinParts
public import CFSG.LocalAnalysis.EvenBN.U5.LinEndgame

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ABGLocalTools (IsSylowOf)
open scoped MatrixGroups

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem sec43_three (hl : d.LinCtx) (k : d.Know12) (c : d.CaseBData) (h42 : c.Sec42)
    (h44 : ∀ X : Subgroup G, X ≤ c.S → CFSG.IsElementaryAbelian 2 X → (2 ^ f) ^ 10 < Nat.card X →
      X ≤ c.Bc ∨ X ≤ c.Bt)
    (R : Subgroup G) (hout : c.Sec43Out R) :
    ∀ Y : Subgroup G, Y ≤ R → CFSG.IsElementaryAbelian 2 Y → (2 ^ f) ^ 12 ≤ Nat.card Y →
      Y = c.Bc ∨ Y = c.Bt := by
  have hd := hl.hyp
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hd.two_le
  obtain ⟨hSeq, hEchar, -⟩ := k.s9_1 c.S c.S_syl c.P_le_S
  have hES : d.E ≤ c.S := hSeq ▸ le_sup_left
  have hDS : d.D ≤ c.S := hSeq ▸ le_sup_right
  have hSN : c.S ≤ normalizer (d.E : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hES).1 (by haveI := hEchar; infer_instance)
  have hEt : d.E.map (MulAut.conj d.t).toMonoidHom = d.E :=
    LinCase.swap_map_eq_of_mem_normalizer (hd.t_mem_normalizer_E_caseB hl.gms)
  have hDt : d.D.map (MulAut.conj d.t).toMonoidHom = d.D :=
    LinCase.swap_map_eq_of_mem_normalizer hd.t_mem_normalizer_D
  haveI hBel : CFSG.IsElementaryAbelian 2 c.Bc := h42.elem
  haveI hBtel : CFSG.IsElementaryAbelian 2 c.Bt := CFSG.IsElementaryAbelian.map _
  have hBD : c.Bc ≤ d.D := inf_le_right
  have hBtD : c.Bt ≤ d.D := by
    have := Subgroup.map_mono (f := (MulAut.conj d.t).toMonoidHom) hBD
    rwa [hDt] at this
  have hBtcard : Nat.card c.Bt = (2 ^ f) ^ 12 :=
    (Subgroup.card_map_of_injective (MulAut.conj d.t).injective).trans h42.card
  have hBtE : Nat.card (c.Bt ⊓ d.E : Subgroup G) = (2 ^ f) ^ 8 := by
    have e : c.Bt ⊓ d.E = (c.Bc ⊓ d.E).map (MulAut.conj d.t).toMonoidHom := by
      rw [Subgroup.map_inf _ _ _ (MulAut.conj d.t).injective, hEt]
      rfl
    rw [e, Subgroup.card_map_of_injective (MulAut.conj d.t).injective]
    exact h42.card_inf_E
  have key : ∀ B₁ : Subgroup G, B₁ ≤ d.D → CFSG.IsElementaryAbelian 2 B₁ →
      Nat.card B₁ = (2 ^ f) ^ 12 → Nat.card (B₁ ⊓ d.E : Subgroup G) = (2 ^ f) ^ 8 →
      ∀ Y : Subgroup G, Y ≤ R → CFSG.IsElementaryAbelian 2 Y → (2 ^ f) ^ 12 ≤ Nat.card Y →
        Y ⊓ c.S ≤ B₁ → Y = B₁ := by
    intro B₁ hB₁D hB₁el hB₁card hB₁E Y hYR hYel hYcard hYS
    have hY4 := hout.card_le Y hYR hYel
    have hYScard : (2 ^ f) ^ 10 < Nat.card (Y ⊓ c.S : Subgroup G) := by
      have h4 : 4 * (2 ^ f) ^ 10 < (2 ^ f) ^ 12 := by
        have h2 : 4 < (2 ^ f) ^ 2 := lt_of_lt_of_le (by norm_num)
          (Nat.pow_le_pow_left hq 2)
        have h10 : 0 < (2 ^ f) ^ 10 := by positivity
        calc 4 * (2 ^ f) ^ 10 < (2 ^ f) ^ 2 * (2 ^ f) ^ 10 := Nat.mul_lt_mul_of_pos_right h2 h10
          _ = (2 ^ f) ^ 12 := by ring
      omega
    have hYleS : Y ≤ c.S := by
      intro y hy
      by_contra hyS
      set Z : Subgroup G := B₁ ⊓ centralizer ({y} : Set G) with hZ
      have hZB : Z ≤ B₁ := inf_le_left
      have hZS : Z ≤ c.S := hZB.trans (hB₁D.trans hDS)
      haveI : CFSG.IsElementaryAbelian 2 B₁ := hB₁el
      have hZel : CFSG.IsElementaryAbelian 2 Z := CFSG.IsElementaryAbelian.of_le hB₁el hZB
      have hcomm : ∀ z ∈ Z, y * z = z * y := fun z hz =>
        (mem_centralizer_singleton_iff.1 hz.2).symm
      have h1 := hout.card_fix y (hYR hy) hyS Z hZS hZel hcomm
      have h2 := Common.card_sup_mul_card_inf_eq (A := d.E) (B := Z) (hZS.trans hSN)
      rw [sup_comm] at h2
      have hEpos : 0 < Nat.card d.E := Nat.card_pos
      have h3 : Nat.card Z ≤ (2 ^ f) ^ 2 * Nat.card (d.E ⊓ Z : Subgroup G) := by
        refine Nat.le_of_mul_le_mul_left ?_ hEpos
        calc Nat.card d.E * Nat.card Z = Nat.card (Z ⊔ d.E : Subgroup G) *
              Nat.card (d.E ⊓ Z : Subgroup G) := h2.symm
          _ ≤ ((2 ^ f) ^ 2 * Nat.card d.E) * Nat.card (d.E ⊓ Z : Subgroup G) :=
              Nat.mul_le_mul_right _ h1
          _ = Nat.card d.E * ((2 ^ f) ^ 2 * Nat.card (d.E ⊓ Z : Subgroup G)) := by ring
      have h4 : Nat.card (d.E ⊓ Z : Subgroup G) ≤ (2 ^ f) ^ 8 := by
        rw [← hB₁E, inf_comm (a := B₁)]
        exact Subgroup.card_le_of_le (inf_le_inf_left _ hZB)
      have h5 : Nat.card (Y ⊓ c.S : Subgroup G) ≤ Nat.card Z := by
        refine Subgroup.card_le_of_le fun z hz => ?_
        exact ⟨hYS hz, mem_centralizer_singleton_iff.2
          (congrArg Subtype.val (mul_comm' (⟨z, hz.1⟩ : Y) ⟨y, hy⟩))⟩
      have h6 : (2 ^ f) ^ 2 * (2 ^ f) ^ 8 = (2 ^ f) ^ 10 := by ring
      have := Nat.mul_le_mul_left ((2 ^ f) ^ 2) h4
      omega
    have hYB : Y ≤ B₁ := by simpa [inf_eq_left.2 hYleS] using hYS
    exact Subgroup.eq_of_le_of_card_ge hYB (by rw [hB₁card]; exact hYcard)
  intro Y hYR hYel hYcard
  have hYSel : CFSG.IsElementaryAbelian 2 (Y ⊓ c.S : Subgroup G) :=
    CFSG.IsElementaryAbelian.of_le hYel inf_le_left
  have hq10 : (2 ^ f) ^ 10 < Nat.card (Y ⊓ c.S : Subgroup G) := by
    have hY4 := hout.card_le Y hYR hYel
    have h2 : 4 < (2 ^ f) ^ 2 := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_left hq 2)
    have h10 : 0 < (2 ^ f) ^ 10 := by positivity
    have h4 : 4 * (2 ^ f) ^ 10 < (2 ^ f) ^ 12 := by
      calc 4 * (2 ^ f) ^ 10 < (2 ^ f) ^ 2 * (2 ^ f) ^ 10 := Nat.mul_lt_mul_of_pos_right h2 h10
        _ = (2 ^ f) ^ 12 := by ring
    omega
  rcases h44 (Y ⊓ c.S) inf_le_right hYSel hq10 with h | h
  · exact Or.inl (key c.Bc hBD hBel h42.card h42.card_inf_E Y hYR hYel hYcard h)
  · exact Or.inr (key c.Bt hBtD hBtel hBtcard hBtE Y hYR hYel hYcard h)

end Data


end CFSG.LocalAnalysis.EvenBN.U5
