module

public import CFSG.CGT.Timmesfeld75.PaperSteps
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.CGT.T75P

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped MatrixGroups Matrix

variable {G : Type} [Group G]

structure A8Cfg (T H : Subgroup G) : Prop where
  le : T ≤ H
  wc : IsWC T
  nat : NaturalSL T H 3 1
  comp : ∃ K : Subgroup G, K ≤ H ∧ T ⊓ K = ⊥ ∧ T ⊔ K = H
  odd : Odd H.index

namespace A8Cfg

variable {T H : Subgroup G} (c : A8Cfg T H)

include c

theorem le_normalizer : H ≤ Subgroup.normalizer (T : Set G) := by
  obtain ⟨hN, -⟩ := c.nat
  have key : ∀ h ∈ H, ∀ x ∈ T, h * x * h⁻¹ ∈ T := by
    intro h hh x hx
    have := hN.conj_mem ⟨x, c.le hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨h, hh⟩
    exact Subgroup.mem_subgroupOf.mp this
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key h hh x hx, fun hx => ?_⟩
  have := key h⁻¹ (H.inv_mem hh) _ hx
  simpa [mul_assoc] using this

theorem card_T : Nat.card T = 8 := by
  obtain ⟨-, e, φ, -⟩ := c.nat
  have hF : Nat.card (GaloisField 2 1) = 2 := by
    have := GaloisField.card 2 1 one_ne_zero
    simpa using this
  rw [Nat.card_congr φ.toEquiv,
    Nat.card_congr (Multiplicative.ofAdd (α := Fin 3 → GaloisField 2 1)).symm, Nat.card_pi]
  simp [hF]

theorem card_H : Nat.card H = 1344 := by
  obtain ⟨hN, e, φ, -⟩ := c.nat
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (T.subgroupOf H)
  have h2 : Nat.card (T.subgroupOf H) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe c.le).toEquiv]
    exact c.card_T
  have h3 : Nat.card (↥H ⧸ T.subgroupOf H) = 168 := by
    let : Fintype (GaloisField 2 1) := Fintype.ofFinite _
    have hF : Fintype.card (GaloisField 2 1) = 2 := by
      have := GaloisField.card 2 1 one_ne_zero
      rw [Nat.card_eq_fintype_card] at this
      simpa using this
    rw [Nat.card_congr e.toEquiv, Matrix.card_SL_field 3]
    simp [hF, Fin.prod_univ_three]
  rw [h1, h2, h3]

end A8Cfg

end CFSG.CGT.T75P
