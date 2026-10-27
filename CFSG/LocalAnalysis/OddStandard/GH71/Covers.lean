module

public import CFSG.LocalAnalysis.OddStandard.GH71.Basic
public import CFSG.GH74.GLS.Stage2.Signalizer.Defs

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Signalizer

variable {G : Type} [Group G]

theorem odd_card_sup_of_le_normalizer' [Finite G] {H N : Subgroup G}
    (hHN : H ≤ normalizer (N : Set G)) (hH : Odd (Nat.card H)) (hN : Odd (Nat.card N)) :
    Odd (Nat.card (H ⊔ N : Subgroup G)) := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hHN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hHN
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (H ⊔ N)),
    ← Nat.card_congr e.toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe (le_sup_right : N ≤ H ⊔ N)).toEquiv]
  exact (Odd.of_dvd_nat hH (Subgroup.card_quotient_dvd_card _)).mul hN

theorem covers_iff {A B C : Subgroup G} (hC : A ⊓ B ≤ normalizer (C : Set G)) :
    Covers A B C ↔ ∀ b ∈ B, ∃ a ∈ A ⊓ B, ∃ c ∈ C, b = a * c := by
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (A ⊓ B) C hC
  constructor
  · intro h b hb
    have hb' : b ∈ ((A ⊓ B ⊔ C : Subgroup G) : Set G) := h hb
    rw [hset] at hb'
    obtain ⟨a, ha, c, hc, rfl⟩ := hb'
    exact ⟨a, ha, c, hc, rfl⟩
  · intro h b hb
    obtain ⟨a, ha, c, hc, rfl⟩ := h b hb
    exact mul_mem (mem_sup_left ha) (mem_sup_right hc)

theorem covers_mono {A A' B C : Subgroup G} (hA : A ≤ A') (h : Covers A B C) : Covers A' B C :=
  h.trans (sup_le_sup_right (inf_le_inf_right B hA) C)

theorem covers_frattini [Finite G] {p : ℕ} (hp : p.Prime) {H N P : Subgroup G} (hNH : N ≤ H)
    (hHN : H ≤ normalizer (N : Set G)) (hN : Odd (Nat.card N))
    (hP : Open.fusionIsSylowIn p P N) : Covers (normalizer (P : Set G)) H N := by
  intro h hh
  obtain ⟨c, hcN, hc⟩ := exists_conj_sylow_of_odd hp hN hP (fusionIsSylowIn_map_conj hP (hHN hh))
  have ha : c⁻¹ * h ∈ normalizer (P : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h1 : h * x * h⁻¹ ∈ P.map (MulAut.conj h).toMonoidHom := ⟨x, hx, rfl⟩
      rw [hc] at h1
      obtain ⟨y, hy, hyx⟩ := h1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      have : c⁻¹ * h * x * (c⁻¹ * h)⁻¹ = y := by
        rw [show c⁻¹ * h * x * (c⁻¹ * h)⁻¹ = c⁻¹ * (h * x * h⁻¹) * c by group, ← hyx]
        group
      rw [this]; exact hy
    · intro hx
      have h1 : c * (c⁻¹ * h * x * (c⁻¹ * h)⁻¹) * c⁻¹ ∈ P.map (MulAut.conj c).toMonoidHom :=
        ⟨_, hx, rfl⟩
      rw [← hc] at h1
      obtain ⟨y, hy, hyx⟩ := h1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
      have : x = y := by
        have e : h * y * h⁻¹ = h * x * h⁻¹ := by rw [hyx]; group
        exact (mul_left_cancel (mul_right_cancel e)).symm
      rw [this]; exact hy
  have hcH : c⁻¹ * h ∈ H := H.mul_mem (H.inv_mem (hNH hcN)) hh
  have hn : (c⁻¹ * h)⁻¹ * c * (c⁻¹ * h) ∈ N := by
    have := (mem_normalizer_iff.mp (hHN (H.inv_mem hcH)) c).mp hcN
    simpa [mul_assoc] using this
  have e : h = (c⁻¹ * h) * ((c⁻¹ * h)⁻¹ * c * (c⁻¹ * h)) := by group
  rw [e]
  exact mul_mem (mem_sup_left ⟨ha, hcH⟩) (mem_sup_right hn)

theorem le_pPrimeCoreOf_of_covers [Finite G] {X H W : Subgroup G}
    (hcov : Covers H X (pPrimeCoreOf 2 X)) (hWX : W ≤ X) (hW : Odd (Nat.card W))
    (hn : H ⊓ X ≤ normalizer (W : Set G)) : W ≤ pPrimeCoreOf 2 X := by
  set O := pPrimeCoreOf 2 X with hO
  have hOX : O ≤ X := pPrimeCoreOf_le' X
  have hXO : X ≤ normalizer (O : Set G) := le_normalizer_pPrimeCoreOf' X
  have hWO : W ≤ normalizer (O : Set G) := hWX.trans hXO
  have hnorm : X ≤ normalizer ((W ⊔ O : Subgroup G) : Set G) := by
    have h1 : H ⊓ X ≤ normalizer ((W ⊔ O : Subgroup G) : Set G) := fun x hx =>
      inf_normalizer_le_normalizer_sup W O ⟨hn hx, hXO hx.2⟩
    have h2 : O ≤ normalizer ((W ⊔ O : Subgroup G) : Set G) := by
      have hset := Subgroup.coe_mul_of_left_le_normalizer_right W O hWO
      intro o ho
      rw [mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        have hy' : y ∈ ((W ⊔ O : Subgroup G) : Set G) := hy
        rw [hset] at hy'
        obtain ⟨w, hw, o', ho', rfl⟩ := hy'
        have hw1 : w⁻¹ * o * w ∈ O := by
          have := (mem_normalizer_iff.mp (hWO (inv_mem hw)) o).mp ho
          simpa [mul_assoc] using this
        have e : o * (w * o') * o⁻¹ = w * ((w⁻¹ * o * w) * o' * o⁻¹) := by group
        rw [e]
        exact mul_mem (mem_sup_left hw) (mem_sup_right
          (O.mul_mem (O.mul_mem hw1 ho') (O.inv_mem ho)))
      · intro hy
        have hy' : o * y * o⁻¹ ∈ ((W ⊔ O : Subgroup G) : Set G) := hy
        rw [hset] at hy'
        obtain ⟨w, hw, o', ho', hwo⟩ := hy'
        have hw1 : w⁻¹ * o⁻¹ * w ∈ O := by
          have := (mem_normalizer_iff.mp (hWO (inv_mem hw)) o⁻¹).mp (O.inv_mem ho)
          simpa [mul_assoc] using this
        have e : y = w * ((w⁻¹ * o⁻¹ * w) * o' * o) := by
          have : y = o⁻¹ * (o * y * o⁻¹) * o := by group
          rw [this, ← hwo]; group
        rw [e]
        exact mul_mem (mem_sup_left hw) (mem_sup_right (O.mul_mem (O.mul_mem hw1 ho') ho))
    intro x hx
    obtain ⟨a, ha, c, hc, rfl⟩ := (covers_iff (fun y hy => hXO hy.2)).mp hcov x hx
    exact mul_mem (h1 ⟨ha.1, ha.2⟩) (h2 hc)
  have hodd := odd_card_sup_of_le_normalizer' hWO hW (odd_card_pPrimeCoreOf' X)
  exact le_sup_left.trans (le_pPrimeCoreOf_of_odd (sup_le hWX hOX) hodd hnorm)

theorem covers_map_conj {A B C : Subgroup G} (g : G) (h : Covers A B C) :
    Covers (A.map (MulAut.conj g).toMonoidHom) (B.map (MulAut.conj g).toMonoidHom)
      (C.map (MulAut.conj g).toMonoidHom) := by
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  unfold Covers at h ⊢
  rw [← map_inf_eq _ _ _ hinj, ← Subgroup.map_sup]
  exact map_mono h

end CFSG.OddStandard.GH71
