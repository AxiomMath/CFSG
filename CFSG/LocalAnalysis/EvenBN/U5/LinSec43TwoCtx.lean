module

public import CFSG.LocalAnalysis.EvenBN.U5.LinSec43TwoGenC
public import CFSG.LocalAnalysis.EvenBN.U5.LinSec42E

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ABGLocalTools (IsSylowOf)
open scoped MatrixGroups

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

namespace CaseBData

variable (hl : d.LinCtx) (k : d.Know12) (c : d.CaseBData)
include hl k c

theorem lin43_pair_full (h41 : c.Sec41) :
    ∃ P' Q' : Subgroup G, IsSylowOf 2 P' c.X ∧ c.X ⊓ c.S ≠ P' ∧ IsSylowOf 2 Q' c.Y ∧
      c.Y ⊓ c.S ≠ Q' ∧
      (∃ θ : (Fin 2 → c.k) → G, Timmesfeld.ARS.IsNaturalModule c.φY θ ∧
        Set.range θ = ↑(d.F ⊓ centralizer ((c.X ⊓ c.S : Subgroup G) : Set G))) ∧
      (∃ θ : (Fin 2 → c.k) → G, Timmesfeld.ARS.IsNaturalModule c.φY θ ∧
        Set.range θ = ↑(d.F ⊓ centralizer (P' : Set G))) ∧
      (∃ θ : (Fin 2 → c.k) → G, Timmesfeld.ARS.IsNaturalModule c.φX θ ∧
        Set.range θ = ↑(d.F ⊓ centralizer ((c.Y ⊓ c.S : Subgroup G) : Set G))) ∧
      (∃ θ : (Fin 2 → c.k) → G, Timmesfeld.ARS.IsNaturalModule c.φX θ ∧
        Set.range θ = ↑(d.F ⊓ centralizer (Q' : Set G))) ∧
      (d.F ⊓ centralizer ((c.X ⊓ c.S : Subgroup G) : Set G)) ⊔
          (d.F ⊓ centralizer (P' : Set G)) = d.F ∧
      (d.F ⊓ centralizer ((c.X ⊓ c.S : Subgroup G) : Set G)) ⊓
          (d.F ⊓ centralizer (P' : Set G)) = ⊥ ∧
      (d.F ⊓ centralizer ((c.Y ⊓ c.S : Subgroup G) : Set G)) ⊔
          (d.F ⊓ centralizer (Q' : Set G)) = d.F ∧
      (d.F ⊓ centralizer ((c.Y ⊓ c.S : Subgroup G) : Set G)) ⊓
          (d.F ⊓ centralizer (Q' : Set G)) = ⊥ := by
  have hp : d.CaseHyp := hl.toCaseHyp
  have hd := hl.hyp
  have hf2 := hd.two_le
  have hk' : Fintype.card c.k = (2 ^ f) ^ 2 := c.card_k
  have hkm : Nat.card c.k = 2 ^ (2 * f) := by
    rw [Nat.card_eq_fintype_card, hk', ← pow_mul, mul_comm]
  obtain ⟨P', hP', hPP'⟩ := exists_isSylowOf_ne hkm (by omega : 1 ≤ 2 * f) c.φX
    (c.X ⊓ c.S)
  obtain ⟨Q', hQ', hQQ'⟩ := exists_isSylowOf_ne hkm (by omega : 1 ≤ 2 * f) c.φY
    (c.Y ⊓ c.S)
  have hcomm : ∀ x ∈ c.X, ∀ y ∈ c.Y, x * y = y * x :=
    fun x hx y hy => (mem_centralizer_iff.1 (c.X_le_centralizer_Y hx) y hy).symm
  have hXF : c.X ≤ normalizer (d.F : Set G) :=
    (c.X_le_M₁).trans (s313a_M₁_le_normalizer_F hp k c.S_syl c.P_le_S)
  have hYF : c.Y ≤ normalizer (d.F : Set G) :=
    (c.Y_le_M₁).trans (s313a_M₁_le_normalizer_F hp k c.S_syl c.P_le_S)
  have hcardF : Nat.card d.F = 2 ^ (4 * (2 * f)) := by
    rw [hd.card_F hl.gms, ← pow_mul]
    congr 1
    ring
  have hle' : Nat.card (d.F ⊓ centralizer ((c.X ⊓ c.S : Subgroup G) : Set G) : Subgroup G) ≤
      2 ^ (2 * (2 * f)) := by
    rw [← h41.centerIn_eq]
    refine (h41.card.trans ?_).le
    rw [← pow_mul]
    congr 1
    ring
  have key := sl2_pair_module_small hkm (by omega : 2 ≤ 2 * f) (by omega : 2 * f ≠ 3)
    (hd.isElementaryAbelian_F hl.gms) hcardF c.φX c.φY hXF hYF hcomm
    (s313a_F_inf_centralizer_X_inf_centralizer_Y hp k c.S_syl c.P_le_S c.ψ)
    (s313a_isSylowOf_X_inf_S hp k c.S_syl c.P_le_S c.ψ) hP' hPP'
    (s313a_isSylowOf_Y_inf_S hp k c.S_syl c.P_le_S c.ψ) hQ' hQQ'
    (s313a_card_F_Y_eq hp k c.S_syl c.P_le_S c.ψ hk').symm hle'
  obtain ⟨-, hUU', hUU, hWW', hWW, hWX, hWX', hUY, hUY'⟩ := key
  exact ⟨P', Q', hP', hPP', hQ', hQQ', hUY, hUY', hWX, hWX', hUU', hUU, hWW', hWW⟩

theorem lin43_comm_X_Y {a b : G} (ha : a ∈ c.X) (hb : b ∈ c.Y) : a * b = b * a :=
  (mem_centralizer_iff.1 (c.X_le_centralizer_Y ha) b hb).symm

theorem lin43_exists_mul_S :
    ∀ s ∈ c.S, ∃ d' ∈ d.D, ∃ p ∈ c.X ⊓ c.S, ∃ q' ∈ c.Y ⊓ c.S, s = d' * p * q' := by
  intro s hs
  have hS : c.S = d.D ⊔ (c.S ⊓ d.M₁) := s313a_S_eq_D_sup hl.toCaseHyp k c.S_syl c.P_le_S
  have hM : c.S ⊓ d.M₁ = (c.X ⊓ c.S) ⊔ (c.Y ⊓ c.S) :=
    s313a_S_inf_M₁_eq hl.toCaseHyp k c.S_syl c.P_le_S c.ψ
  have hnorm : c.S ⊓ d.M₁ ≤ normalizer (d.D : Set G) :=
    inf_le_right.trans ((lin_M₁_le_L₁ hl k c).trans (lin_L₁_le_normalizer_D hl k c))
  rw [hS] at hs
  obtain ⟨d', hd', m, hm, rfl⟩ := Common.exists_mul_of_le_normalizer hnorm s hs
  rw [hM] at hm
  have hcomm : ∀ x ∈ c.X ⊓ c.S, ∀ y ∈ c.Y ⊓ c.S, x * y = y * x :=
    fun x hx y hy => lin43_comm_X_Y hl k c hx.1 hy.1
  have hm' : m ∈ (((c.X ⊓ c.S) ⊔ (c.Y ⊓ c.S) : Subgroup G) : Set G) := hm
  rw [(CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).2] at hm'
  obtain ⟨p, hp, q', hq', rfl⟩ := hm'
  exact ⟨d', hd', p, hp, q', hq', by group⟩

theorem lin43_exists_mul_DQ :
    ∀ s ∈ d.D ⊔ (c.Y ⊓ c.S), ∃ d' ∈ d.D, ∃ q' ∈ c.Y ⊓ c.S, s = d' * q' := by
  intro s hs
  have hnorm : c.Y ⊓ c.S ≤ normalizer (d.D : Set G) :=
    inf_le_left.trans ((lin_Y_le_L₁ hl k c).trans (lin_L₁_le_normalizer_D hl k c))
  exact Common.exists_mul_of_le_normalizer hnorm s hs

theorem lin43_card_S : Nat.card c.S = (2 ^ f) ^ 4 * Nat.card d.D := by
  rw [(k.s10_o c.S c.S_syl c.P_le_S).card_S, k.s9e.card_D, ← pow_add]

theorem lin43_card_Q : Nat.card (c.Y ⊓ c.S : Subgroup G) = (2 ^ f) ^ 2 := by
  have hf2 := hl.hyp.two_le
  have hkm : Nat.card c.k = 2 ^ (2 * f) := c.card_k_eq
  have := Prelim.card_of_isSylowOf hkm (by omega : 1 ≤ 2 * f) c.φY
    (s313a_isSylowOf_Y_inf_S hl.toCaseHyp k c.S_syl c.P_le_S c.ψ)
  exact this.trans (by rw [← pow_mul, mul_comm])

theorem lin43_card_DQ : Nat.card (d.D ⊔ (c.Y ⊓ c.S) : Subgroup G) ≤ (2 ^ f) ^ 2 * Nat.card d.D := by
  have hnorm : c.Y ⊓ c.S ≤ normalizer (d.D : Set G) :=
    inf_le_left.trans ((lin_Y_le_L₁ hl k c).trans (lin_L₁_le_normalizer_D hl k c))
  have h1 := Common.card_sup_mul_card_inf_eq hnorm
  rw [lin43_card_Q hl k c] at h1
  have hpos : 0 < Nat.card (d.D ⊓ (c.Y ⊓ c.S) : Subgroup G) := Nat.card_pos
  calc Nat.card (d.D ⊔ (c.Y ⊓ c.S) : Subgroup G)
      = Nat.card (d.D ⊔ (c.Y ⊓ c.S) : Subgroup G) * 1 := (mul_one _).symm
    _ ≤ Nat.card (d.D ⊔ (c.Y ⊓ c.S) : Subgroup G) *
        Nat.card (d.D ⊓ (c.Y ⊓ c.S) : Subgroup G) := Nat.mul_le_mul_left _ hpos
    _ = Nat.card d.D * (2 ^ f) ^ 2 := h1
    _ = (2 ^ f) ^ 2 * Nat.card d.D := mul_comm _ _

theorem lin43_card_k : Nat.card c.k = (2 ^ f) ^ 2 := by
  rw [c.card_k_eq, ← pow_mul, mul_comm]

theorem lin43_S_le_normalizer_D : c.S ≤ normalizer (d.D : Set G) :=
  (lin_S_le_L₁ hl k c).trans (lin_L₁_le_normalizer_D hl k c)

theorem lin43_card_le_S {A₀ : Subgroup G} (hA₀ : A₀ ≤ c.S) :
    Nat.card A₀ ≤ (2 ^ f) ^ 4 * Nat.card (A₀ ⊓ d.D : Subgroup G) :=
  LinT43.card_le_mul_card_inf hA₀ (lin_D_le_S hl k c) (hA₀.trans (lin43_S_le_normalizer_D hl k c))
    (lin43_card_S hl k c).le

theorem lin43_card_le_DQ {A₀ : Subgroup G} (hA₀ : A₀ ≤ d.D ⊔ (c.Y ⊓ c.S)) :
    Nat.card A₀ ≤ (2 ^ f) ^ 2 * Nat.card (A₀ ⊓ d.D : Subgroup G) :=
  LinT43.card_le_mul_card_inf hA₀ le_sup_left
    (hA₀.trans (sup_le (fun _ hx => le_normalizer hx)
      (inf_le_left.trans ((lin_Y_le_L₁ hl k c).trans (lin_L₁_le_normalizer_D hl k c)))))
    (lin43_card_DQ hl k c)

end CaseBData

end Data

end CFSG.LocalAnalysis.EvenBN.U5
