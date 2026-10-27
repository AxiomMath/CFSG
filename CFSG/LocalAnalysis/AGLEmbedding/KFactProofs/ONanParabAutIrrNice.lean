module

public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrDefs

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open CFSG.RankThree.PartOne.OutStructure
open scoped commutatorElement

theorem OutPTwoGen.of_outPNice {X : Type*} [Group X] [Finite X] {p : ℕ}
    (h : OutPNice p X) : OutPTwoGen X p := by
  obtain ⟨D, E, hID, hD2, hpE, hcomm, hcomp⟩ := h
  have hDE : D ≤ E := fun δ hδ => hpE δ ⟨0, by simpa using hδ⟩
  have hDn : D.Normal := by
    refine ⟨fun δ hδ γ => ?_⟩
    have h1 : ⁅γ, δ⁆ ∈ D := hcomm γ δ (hDE hδ)
    have h2 : γ * δ * γ⁻¹ = ⁅γ, δ⁆ * δ := by
      simp [commutatorElement_def, mul_assoc]
    rw [h2]
    exact D.mul_mem h1 hδ
  intro P hP
  have hPE : P ≤ E := fun x hx => by
    obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
    exact hpE x ⟨k, by
      have : x ^ p ^ k = 1 := congrArg Subtype.val hk
      rw [this]
      exact D.one_mem⟩
  have hpel : ∀ x ∈ P, ∃ k : ℕ, x ^ p ^ k = 1 := fun x hx => by
    obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hpelD : ∀ x ∈ P, ∃ k : ℕ, x ^ p ^ k ∈ D := fun x hx => by
    obtain ⟨k, hk⟩ := hpel x hx
    exact ⟨k, by rw [hk]; exact D.one_mem⟩
  set q : MulAut X →* MulAut X ⧸ D := QuotientGroup.mk' D with hq
  obtain ⟨a, ha⟩ := Finite.exists_max (fun x : ↥P => orderOf (q x))
  refine ⟨a.1, a.2, a.1, a.2, fun x hx => ?_⟩
  have hxa : q x ∈ Subgroup.zpowers (q a.1) := by
    rcases hcomp x (hPE hx) a.1 (hPE a.2) (hpelD x hx) (hpelD a.1 a.2) with ⟨m, hm⟩ | ⟨m, hm⟩
    · refine ⟨-m, ?_⟩
      have : q (x * a.1 ^ m) = 1 := (QuotientGroup.eq_one_iff _).2 hm
      rw [map_mul, map_zpow] at this
      show q a.1 ^ (-m) = q x
      rw [zpow_neg]
      exact (eq_inv_of_mul_eq_one_left this).symm
    · have hmem : q a.1 ∈ Subgroup.zpowers (q x) := by
        refine ⟨-m, ?_⟩
        have : q (a.1 * x ^ m) = 1 := (QuotientGroup.eq_one_iff _).2 hm
        rw [map_mul, map_zpow] at this
        show q x ^ (-m) = q a.1
        rw [zpow_neg]
        exact (eq_inv_of_mul_eq_one_left this).symm
      have hle : Subgroup.zpowers (q a.1) ≤ Subgroup.zpowers (q x) :=
        (Subgroup.zpowers_le).2 hmem
      have hord : orderOf (q x) ≤ orderOf (q a.1) := ha ⟨x, hx⟩
      have hcard : Nat.card (Subgroup.zpowers (q x)) ≤ Nat.card (Subgroup.zpowers (q a.1)) := by
        rw [Nat.card_zpowers, Nat.card_zpowers]
        exact hord
      have heq := Subgroup.eq_of_le_of_card_ge hle hcard
      rw [heq]
      exact Subgroup.mem_zpowers _
  obtain ⟨n, hn0⟩ := hxa
  have hn : q a.1 ^ n = q x := hn0
  have hδD : (a.1 ^ n)⁻¹ * x ∈ D := by
    have : q ((a.1 ^ n)⁻¹ * x) = 1 := by
      rw [map_mul, map_inv, map_zpow, hn, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).1 this
  have hδP : (a.1 ^ n)⁻¹ * x ∈ P := P.mul_mem (P.inv_mem (P.zpow_mem a.2 n)) hx
  obtain ⟨k, hk⟩ := hpel _ hδP
  have hδI : (a.1 ^ n)⁻¹ * x ∈ inn X := hD2 _ hδD k (by rw [hk]; exact (inn X).one_mem)
  have hx' : x = a.1 ^ n * ((a.1 ^ n)⁻¹ * x) := by group
  rw [hx']
  exact Subgroup.mul_mem_sup (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) n) hδI

end CFSG.AGLEmbedding.ParabAutIrr
