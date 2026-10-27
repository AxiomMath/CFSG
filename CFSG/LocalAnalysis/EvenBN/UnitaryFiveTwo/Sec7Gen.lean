module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec7Diag

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {d : Data G} {A : Subgroup G}

namespace Data.Hyp

theorem comm_inv_gen (h : d.Hyp) (hc : ⁅A, A.map (MulAut.conj d.t).toMonoidHom⁆ = ⊥) :
    ⁅A, A.map (MulAut.conj d.t⁻¹).toMonoidHom⁆ = ⊥ := by
  rw [h.t_inv]
  exact hc

theorem delta_apply (h : d.Hyp) (hc : ⁅A, A.map (MulAut.conj d.t).toMonoidHom⁆ = ⊥) (a : A) :
    Common.diagonalHom A d.t (h.comm_inv_gen hc) a = (a : G) * (d.t * a * d.t⁻¹) := by
  rw [Common.diagonalHom_apply, h.t_inv]

theorem range_delta_le (h : d.Hyp) (hperf : ⁅A, A⁆ = A)
    (hc : ⁅A, A.map (MulAut.conj d.t).toMonoidHom⁆ = ⊥) :
    (Common.diagonalHom A d.t (h.comm_inv_gen hc)).range ≤ d.L := by
  set δ := Common.diagonalHom A d.t (h.comm_inv_gen hc) with hδ
  have hAperf : Group.IsPerfect ↥A := (Common.isPerfect_subgroup_iff_commutator_eq A).mpr hperf
  have htop : ⁅(⊤ : Subgroup ↥A), (⊤ : Subgroup ↥A)⁆ = ⊤ := by
    rw [← _root_.commutator_def]
    exact hAperf.commutator_eq_top
  have hperfR : ⁅δ.range, δ.range⁆ = δ.range :=
    calc ⁅δ.range, δ.range⁆ = ⁅(⊤ : Subgroup ↥A).map δ, (⊤ : Subgroup ↥A).map δ⁆ := by
          rw [← MonoidHom.range_eq_map]
      _ = (⁅(⊤ : Subgroup ↥A), (⊤ : Subgroup ↥A)⁆).map δ :=
          (Subgroup.map_commutator _ _ _).symm
      _ = δ.range := by rw [htop, ← MonoidHom.range_eq_map]
  exact h.perfect_le hperfR (Common.range_diagonalHom_le (h.comm_inv_gen hc) h.t_mul_t)

theorem range_delta_eq (h : d.Hyp) (hU : d.UnitaryProductData A) :
    (Common.diagonalHom A d.t (h.comm_inv_gen hU.comm)).range = d.L := by
  refine le_antisymm (h.range_delta_le hU.perfect hU.comm) ?_
  set δ := Common.diagonalHom A d.t (h.comm_inv_gen hU.comm) with hδ
  have hAA : ∀ a ∈ A, ∀ c ∈ A.map (MulAut.conj d.t).toMonoidHom, a * c = c * a := by
    intro a ha c hc
    obtain ⟨y, hy, rfl⟩ := hc
    exact Swap.comm_of_commutator_eq_bot hU.comm ha hy
  have hzδ : ∀ z ∈ A ⊓ A.map (MulAut.conj d.t).toMonoidHom, ∀ b : A,
      z * δ b = δ b * z := by
    intro z hz b
    rw [h.delta_apply hU.comm]
    have h1 : z * (b : G) = (b : G) * z := (hAA b b.2 z hz.2).symm
    have h2 : z * (d.t * b * d.t⁻¹) = d.t * b * d.t⁻¹ * z :=
      hAA z hz.1 (d.t * b * d.t⁻¹) ⟨b, b.2, rfl⟩
    calc z * (↑b * (d.t * ↑b * d.t⁻¹)) = (z * b) * (d.t * b * d.t⁻¹) := by group
      _ = b * z * (d.t * b * d.t⁻¹) := by rw [h1]
      _ = b * (z * (d.t * b * d.t⁻¹)) := by group
      _ = b * (d.t * b * d.t⁻¹ * z) := by rw [h2]
      _ = b * (d.t * b * d.t⁻¹) * z := by group
  have hdec : ∀ l ∈ d.L, ∃ b : A, ∃ z ∈ A ⊓ A.map (MulAut.conj d.t).toMonoidHom,
      d.t * z = z * d.t ∧ l = δ b * z := by
    intro l hl
    obtain ⟨b, z, hz, htz, hlz⟩ := Swap.exists_eq_swapHom_mul hU.comm h.t_mul_t (hU.L_le hl)
      (h.mul_t_of_mem_L hl).symm
    refine ⟨b, z, hz, htz, ?_⟩
    rw [hlz, h.delta_apply hU.comm, Swap.swapHom_apply]
  have hcomm_in : ∀ l ∈ d.L, ∀ l' ∈ d.L, ⁅l, l'⁆ ∈ δ.range := by
    intro l hl l' hl'
    obtain ⟨b, z, hz, htz, rfl⟩ := hdec l hl
    obtain ⟨b', z', hz', htz', rfl⟩ := hdec l' hl'
    have hzz' : z * z' = z' * z := hAA z hz.1 z' hz'.2
    rw [commutatorElement_mul_mul_eq (hzδ z hz b') hzz' (hzδ z' hz' b)]
    exact ⟨⁅b, b'⁆, by rw [map_commutatorElement]⟩
  intro y hy
  have : y ∈ ⁅d.L, d.L⁆ := by rw [h.commutator_L]; exact hy
  exact (Subgroup.commutator_le.2 hcomm_in) this

theorem center_eq_ker_delta (h : d.Hyp) (hU : d.UnitaryProductData A) :
    center ↥A = (Common.diagonalHom A d.t (h.comm_inv_gen hU.comm)).ker := by
  refine le_antisymm (fun z hz => ?_) (Common.ker_diagonalHom_le_center (h.comm_inv_gen hU.comm))
  rw [MonoidHom.mem_ker]
  have hrange := h.range_delta_eq hU
  have hzL : Common.diagonalHom A d.t (h.comm_inv_gen hU.comm) z ∈ d.L :=
    hrange ▸ ⟨z, rfl⟩
  have hcen : (⟨_, hzL⟩ : d.L) ∈ center d.L := by
    rw [mem_center_iff]
    rintro ⟨g, hg⟩
    have hgR : g ∈ (Common.diagonalHom A d.t (h.comm_inv_gen hU.comm)).range := by
      rw [hrange]
      exact hg
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hgR
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul, mem_center_iff.mp hz a]
  rw [h.center_eq_bot, Subgroup.mem_bot] at hcen
  exact congrArg Subtype.val hcen

theorem quotient_equiv (h : d.Hyp) (hU : d.UnitaryProductData A) :
    Nonempty (↥A ⧸ center ↥A ≃* ↥d.L) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (h.center_eq_ker_delta hU)).trans
    ((QuotientGroup.quotientKerEquivRange
      (Common.diagonalHom A d.t (h.comm_inv_gen hU.comm))).trans
      (MulEquiv.subgroupCongr (h.range_delta_eq hU)))⟩

theorem isQuasisimple (h : d.Hyp) (hU : d.UnitaryProductData A) :
    CFSG.Open.IsQuasisimple ↥A := by
  haveI := h.isSimpleGroup_L
  obtain ⟨e⟩ := h.quotient_equiv hU
  have hperf : Group.IsPerfect ↥A :=
    (Common.isPerfect_subgroup_iff_commutator_eq A).mpr hU.perfect
  unfold CFSG.Open.IsQuasisimple
  exact ⟨hperf.commutator_eq_top, e.isSimpleGroup⟩

section OddCenter


theorem odd_center (h : d.Hyp) (hU : d.UnitaryProductData A) :
    Odd (Nat.card (center ↥A)) := by
  rw [h.center_eq_ker_delta hU]
  refine Common.odd_card_ker_diagonalHom_of_centralizer_le (h.comm_inv_gen hU.comm) h.t_mul_t ?_ ?_
  · rw [h.range_delta_eq hU]
    exact h.centralizer_inf_H_eq.le
  · rw [h.range_delta_eq hU]
    have hnc := h.not_comm_L
    push_neg at hnc
    exact hnc

end OddCenter

theorem delta_mem_L (h : d.Hyp) (hU : d.UnitaryProductData A) {x : G} (hx : x ∈ A) :
    x * (d.t * x * d.t⁻¹) ∈ d.L := by
  have := h.range_delta_eq hU
  have hmem : Common.diagonalHom A d.t (h.comm_inv_gen hU.comm) ⟨x, hx⟩ ∈ d.L := this ▸ ⟨_, rfl⟩
  rwa [h.delta_apply hU.comm] at hmem

theorem delta_surj (h : d.Hyp) (hU : d.UnitaryProductData A) :
    ∀ y ∈ d.L, ∃ x ∈ A, x * (d.t * x * d.t⁻¹) = y := by
  intro y hy
  rw [← h.range_delta_eq hU] at hy
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hy
  refine ⟨(a : G), a.2, ?_⟩
  rw [← ha, h.delta_apply hU.comm]

end Data.Hyp

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
