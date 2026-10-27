module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem11K
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec2Lem4

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem exists_mem_TL_ch611_F4 (h331 : Stmt3_3_1_F4) (h432 : Stmt4_3_2_F4) (h512 : Stmt5_1_2_F4)
    (h614 : Stmt6_1_4_F4) (h615 : Stmt6_1_5_F4) {t : G} (htT : t ∈ T)
    (htZ : t ∈ Subgroup.centralizer (ch6ZS T L V : Set G)) :
    ∃ t' ∈ T ⊓ L, t'⁻¹ * t ∈ Subgroup.centralizer (V : Set G) := by
  set R := ch6Q T V with hRdef
  set A := T ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) with hAdef
  have hRA : R ≤ A := fun x hx => ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun z hz =>
    Subgroup.mem_centralizer_iff.mp hx.2 z hz.1⟩
  have hTLA : T ⊓ L ≤ A := fun x hx => ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun z hz =>
    (Subgroup.mem_centralizer_iff.mp hz.2 x hx).symm⟩
  have hAT : A ≤ T := inf_le_left
  have h8 : R.relIndex T = 8 := h.relIndex_Q_T_F4 h331 h615
  have h4 : R.relIndex (T ⊓ L) = 4 := by
    have e : R.subgroupOf (T ⊓ L) = (Subgroup.centralizer (V : Set G)).subgroupOf (T ⊓ L) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, hRdef, Subgroup.mem_inf]
      exact ⟨fun hx => hx.2, fun hx => ⟨x.2.1, hx⟩⟩
    rw [Subgroup.relIndex, e]
    exact h.relIndex_TL_ch611

  have hA1 : A.relIndex T ≠ 1 := by
    intro h1
    have hTA : T ≤ A := Subgroup.relIndex_eq_one.mp h1
    have hle : ch6ZS T L V ≤ quasithinOmegaOneCenter T := fun x hx =>
      Subgroup.subset_closure ⟨⟨h.toHyp611.le_T hx.1, Subgroup.mem_centralizer_iff.mpr
        fun y hy => (Subgroup.mem_centralizer_iff.mp (hTA hy).2 x hx).symm⟩,
        h.toHyp611.isElemAbelian.2 x hx.1⟩
    have := Subgroup.card_le_of_le hle
    rw [h.card_omega_F4 h331 h432 h512 h614 h615, h.toHyp611Nat.card_ZS] at this
    norm_num at this
  have hA0 : A.relIndex T ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hmul := Subgroup.relIndex_mul_relIndex R A T hRA hAT
  rw [h8] at hmul
  have hRA4 : R.relIndex A ≤ 4 := by
    by_contra hcon
    have : 2 ≤ A.relIndex T := by omega
    nlinarith

  set B := (T ⊓ L) ⊔ R with hBdef
  have hRB : R ≤ B := le_sup_right
  have hBA : B ≤ A := sup_le hTLA hRA
  have hRB4 : 4 ≤ R.relIndex B := h4 ▸ Subgroup.relIndex_le_of_le_right le_sup_left
    Subgroup.index_ne_zero_of_finite
  have hmul2 := Subgroup.relIndex_mul_relIndex R B A hRB hBA
  have hBA1 : B.relIndex A = 1 := by
    have hpos : B.relIndex A ≠ 0 := Subgroup.index_ne_zero_of_finite
    by_contra hne
    have : 2 ≤ B.relIndex A := by omega
    nlinarith
  have htB : t ∈ B := Subgroup.relIndex_eq_one.mp hBA1 ⟨htT, htZ⟩
  have hTLR : T ⊓ L ≤ Subgroup.normalizer (R : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxV := h.toHyp611.T_le_normalizer hx.1
    constructor
    · rintro ⟨hyT, hyV⟩
      refine ⟨T.mul_mem (T.mul_mem hx.1 hyT) (T.inv_mem hx.1), ?_⟩
      exact Subgroup.mem_centralizer_iff.mpr fun v hv => by
        have h1 : x⁻¹ * v * x ∈ V := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxV) v).mp hv
          simpa using this
        have h2 := Subgroup.mem_centralizer_iff.mp hyV _ h1
        calc v * (x * y * x⁻¹) = x * ((x⁻¹ * v * x) * y) * x⁻¹ := by group
          _ = x * (y * (x⁻¹ * v * x)) * x⁻¹ := by rw [h2]
          _ = x * y * x⁻¹ * v := by group
    · rintro ⟨hyT, hyV⟩
      have hyT' : y ∈ T := by
        have := T.mul_mem (T.mul_mem (T.inv_mem hx.1) hyT) hx.1
        simpa [mul_assoc] using this
      refine ⟨hyT', Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
      have h1 : x * v * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hxV v).mp hv
      have h2 := Subgroup.mem_centralizer_iff.mp hyV _ h1
      calc v * y = x⁻¹ * ((x * v * x⁻¹) * (x * y * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * y * x⁻¹) * (x * v * x⁻¹)) * x := by rw [h2]
        _ = y * v := by group
  have hBmul : (B : Set G) = (T ⊓ L : Subgroup G) * (R : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTLR
  have htB' : t ∈ ((T ⊓ L : Subgroup G) : Set G) * (R : Set G) := hBmul ▸ htB
  obtain ⟨a, ha, r, hr, hart⟩ := htB'
  refine ⟨a, ha, ?_⟩
  rw [← hart, inv_mul_cancel_left]
  exact hr.2

end Hyp6Sec2

end CFSG.Quasithin.H13
