module

public import CFSG.Quasithin.Vol2.Ch6Sec1Basic
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp611

theorem isUniqueM_F4 (h432 : Stmt4_3_2_F4) (h : Hyp611 G T M L V n) : IsUniqueM (L ⊔ T) M := by
  have hM := (h432 G T M L h.simple h.nonabelian h.qtke h.sylow h.maxTwoLocal h.T_le h.maximal
    h.faithful h.L_le h.normal ⟨n, h.two_le, h.lie⟩).1
  exact ⟨⟨h.maxTwoLocal, sup_le h.L_le h.T_le⟩,
    fun M' hM' => hM M' hM'.1 (le_sup_left.trans hM'.2)⟩

end Hyp611

theorem stmt6_1_3_one_F4 (h432 : Stmt4_3_2_F4) (h : Hyp611 G T M L V n) (hTI : IsTISetIn V M) :
    E6.HypE61 T M V :=
  h.hypE61 hTI (h.isUniqueM_F4 h432) h.centralizer_eq

theorem Hyp611Nat.hypE61_F4 (h432 : Stmt4_3_2_F4) (h : Hyp611Nat G T M L V n) : E6.HypE61 T M V :=
  stmt6_1_3_one_F4 h432 h.toHyp611 h.isTISetIn

theorem stmt6_1_8_F4 (h432 : Stmt4_3_2_F4) (h615 : Stmt6_1_5_F4) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V : Subgroup G) (n : ℕ), Hyp611Nat G T M L V n →
      (∀ U H : Subgroup G, U ≠ ⊥ → U ≤ V → H ≤ Subgroup.normalizer (U : Set G) →
        H ⊓ M = H ⊓ Subgroup.normalizer (V : Set G)) ∧
      ∀ H : Subgroup G, IsHStar T M H → H ⊓ M = H ⊓ Subgroup.normalizer (V : Set G) := by
  intro G _ _ T M L V n h
  have hE := h.hypE61_F4 h432
  have hNV := hE.normalizer_le
  refine ⟨fun U H hU hUV hHU => h.inf_eq_inf_normalizer hNV hU hUV hHU, fun H hH => ?_⟩
  have hU := inf_omegaOneCenter_ne_bot h.sylow.1 h.toHyp611.isElemAbelian h.toHyp611.le_T
    h.toHyp611.T_le_normalizer h.toHyp611.ne_bot
  refine h.inf_eq_inf_normalizer hNV hU inf_le_left ?_
  have hHZ := h615 G T M L V n h.toHyp611 H hH
  have hfix : ∀ y ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G),
      ∀ w ∈ quasithinOmegaOneCenter T, y * w * y⁻¹ = w := by
    intro y hy w hw
    have hc := Subgroup.mem_centralizer_iff.mp hy w hw
    calc y * w * y⁻¹ = w * y * y⁻¹ := by rw [hc]
      _ = w := by group
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    rw [hfix x (hHZ hx) u hu.2]
    exact hu
  · intro hu
    have key : x⁻¹ * (x * u * x⁻¹) * x⁻¹⁻¹ = x * u * x⁻¹ :=
      hfix x⁻¹ (Subgroup.inv_mem _ (hHZ hx)) _ hu.2
    have e : x⁻¹ * (x * u * x⁻¹) * x⁻¹⁻¹ = u := by group
    rw [e] at key
    rw [key]
    exact hu

end CFSG.Quasithin.H13
