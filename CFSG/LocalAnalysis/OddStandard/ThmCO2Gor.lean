module

public import CFSG.LocalAnalysis.OddStandard.ThmCO2GorEasy
public import CFSG.LocalAnalysis.OddStandard.ThmCO2GorNormal
public import CFSG.LocalAnalysis.OddStandard.ThmCO2GorWalter
public import CFSG.Milestones.CL_LIT_Walter_abelian_Sylow_two_simple

public section

namespace CFSG.OddStandard.ThmC.O2.Gor

open CFSG Subgroup
open scoped MatrixGroups

theorem gor42Hard_of_steps
    (hW : CFSG.Walter.WalterOrderForm) : Gor42Hard := by
  intro Q _ _ hO hP R hcard _ habel hD
  exfalso
  have hfpf : ∀ g ∈ normalizer ((R : Subgroup Q) : Set Q),
      (∀ r ∈ (R : Subgroup Q), g * r * g⁻¹ = r) ∨
        (∀ r ∈ (R : Subgroup Q), g * r * g⁻¹ = r → r = 1) :=
    fun g hg => (hD g hg).imp id (fun h => h.1)
  have hR1 : (R : Subgroup Q) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    norm_num at hcard
  set M : Subgroup Q := normalClosure ((R : Subgroup Q) : Set Q) with hMdef
  obtain ⟨hsimple, hnab⟩ := normalClosure_simple hO hP R hR1 habel hfpf
  have hRM : (R : Subgroup Q) ≤ M := Subgroup.le_normalClosure
  let RM : Sylow 2 M := R.subtype hRM
  have hmem : ∀ x : M, x ∈ (RM : Subgroup M) ↔ (x : Q) ∈ (R : Subgroup Q) := fun x => by
    simp [RM, Sylow.coe_subtype, Subgroup.mem_subgroupOf]
  have hab : IsMulCommutative (RM : Subgroup M) := ⟨⟨fun a b => Subtype.ext (Subtype.ext
    (habel _ ((hmem _).1 a.2) _ ((hmem _).1 b.2)))⟩⟩
  have hc : Nat.card (RM : Subgroup M) = 16 := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRM).toEquiv
  obtain ⟨e⟩ := nonempty_psl2_sixteen hW hnab RM hab hc
  obtain ⟨g, hg, u, hu, hne⟩ := exists_bad_of_mulEquiv e RM
  have hgR : ∀ h ∈ normalizer ((RM : Subgroup M) : Set M), ∀ x ∈ (R : Subgroup Q),
      (h : Q) * x * (h : Q)⁻¹ ∈ (R : Subgroup Q) := by
    intro h hh x hx
    have := (Subgroup.mem_normalizer_iff.1 hh ⟨x, hRM hx⟩).1 ((hmem _).2 hx)
    exact (hmem _).1 this
  have hgN : (g : Q) ∈ normalizer ((R : Subgroup Q) : Set Q) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hgR g hg x
    · intro hx
      have := hgR g⁻¹ (Subgroup.inv_mem _ hg) _ hx
      simpa [mul_assoc] using this
  have key : ∀ r ∈ (R : Subgroup Q), (g : Q) ^ 3 * r * ((g : Q) ^ 3)⁻¹ = r := by
    rcases hD _ hgN with h | ⟨_, h3⟩
    · intro r hr
      have hc1 : Commute (g : Q) r := by
        have := h r hr
        calc (g : Q) * r = ((g : Q) * r * (g : Q)⁻¹) * g := by group
          _ = r * g := by rw [this]
      have hc3 : Commute ((g : Q) ^ 3) r := hc1.pow_left 3
      rw [hc3.eq, mul_inv_cancel_right]
    · exact h3
  apply hne
  apply Subtype.ext
  simpa using key u ((hmem u).1 hu)

theorem gor42_of_walter (hW : CFSG.Walter.WalterOrderForm) : Gor42 :=
  gor42_of_hard (gor42Hard_of_steps hW)

theorem gor42 :
    Gor42 :=
  gor42_of_walter fun G _ _ _ hn P hP =>
    CFSG.Milestones.cl_lit_walter_abelian_sylow_two_simple G hn P hP

end CFSG.OddStandard.ThmC.O2.Gor
