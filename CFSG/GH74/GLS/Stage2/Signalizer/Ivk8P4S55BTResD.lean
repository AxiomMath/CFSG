module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTResDG

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Signalizer
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S T Tstar : Subgroup G} {p : ℕ}
  {H P : Subgroup G} {g : G} {X Y : Subgroup G} {t : G} {q : ℕ} {I Q₁ : Subgroup G}

theorem diag_solvable (h : Cfg55E G z k S T Tstar p H P g X Y)
    (hd : Data5A2 z k S T Tstar p H P t q I Q₁) {w : G} (hw : w = z ∨ w = t)
    {W : Subgroup (HBar H)} (hWw : W ≤ centralizer (barIn H (zpowers w) : Set (HBar H)))
    (hWI : W ≤ centralizer (barIn H I : Set (HBar H))) : Group.IsSolvable ↥W := by
  by_contra hns
  obtain ⟨D, hDW, hDp, hDne⟩ := ResD.exists_perfect_le_of_not_isSolvable hns
  have hu := hd.u.udata
  have hwH : w ∈ H := by
    rcases hw with hw | hw <;> rw [hw]
    · exact z_mem_H h hd.u
    · exact t_mem_H h hd.u
  have hw2 : orderOf w = 2 := by
    rcases hw with hw | hw <;> rw [hw]
    · exact h.ctx.central.1
    · exact orderOf_eq_prime (by rw [sq]; exact hu.t_sq) hu.t_ne
  obtain ⟨D₁, hD₁H, hD₁w, hD₁p, hD₁D⟩ :=
    ResD.exists_perfect_lift_barIn hwH hw2 hDp (hDW.trans hWw)
  have hDI := ResD.comm_mem_pPrimeCoreOf hD₁H hd.i.good.le_H (by rw [hD₁D]; exact hDW.trans hWI)
  obtain ⟨w', c, hww, hcw, hcS⟩ := ResD.exists_conj_to_z h hd hw
  obtain ⟨hwU, -, -, -, -, -, -⟩ := ResD.pair_facts hd hww
  have hA := ResD.diagAt_of_conj h hd hww hcw hcS
  have hbot := hA.eq_bot (D := D₁.map (MulAut.conj c).toMonoidHom) ?_ ?_ ?_
  · apply hDne
    rw [← hD₁D, (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj c).injective).mp hbot]
    unfold barIn
    rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
  · rintro _ ⟨d, hd', rfl⟩
    rw [← hcw]
    exact ResD.conj_mem_centralizer (hD₁w hd') c
  · rw [← Subgroup.map_commutator, hD₁p]
  · rintro _ ⟨d, hd', rfl⟩ _ ⟨i, hi, rfl⟩
    have hiw : i ∈ centralizer ({w} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hd.i.good.comm i hi w hwU).symm
    refine ⟨⁅d, i⁆, ⟨hDI d hd' i hi, ?_⟩, map_commutatorElement _ _ _⟩
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hD₁w hd') hiw)
      (Subgroup.inv_mem _ (hD₁w hd'))) (Subgroup.inv_mem _ hiw)

theorem diag_swap (h : Cfg55E G z k S T Tstar p H P g X Y)
    (hd : Data5A2 z k S T Tstar p H P t q I Q₁) {w : G} (hw : w = z ∨ w = t) {y : G}
    (hyH : y ∈ H) (hy2 : orderOf y = 2) (hyz : IsConj z y) (hyw : y * w = w * y)
    (hne : y ≠ w)
    (hyI : barIn H (zpowers y) ≤ centralizer (barIn H I : Set (HBar H))) :
    ¬ IsConj z (y * w) := by
  intro hc
  have hyI' := ResD.comm_mem_pPrimeCoreOf (Subgroup.zpowers_le.mpr hyH) hd.i.good.le_H hyI y
    (Subgroup.mem_zpowers y)
  obtain ⟨w', c, hww, hcw, hcS⟩ := ResD.exists_conj_to_z h hd hw
  obtain ⟨hwU, -, -, -, -, -, -⟩ := ResD.pair_facts hd hww
  have hA := ResD.diagAt_of_conj h hd hww hcw hcS
  have hyC : c * y * c⁻¹ ∈ Cen z := by
    rw [← hcw]
    exact ResD.conj_mem_centralizer (Subgroup.mem_centralizer_singleton_iff.mpr hyw) c
  have hy2' : orderOf (c * y * c⁻¹) = 2 := by
    rw [← hy2]
    exact (SemiconjBy.orderOf_eq c (x := y) (y := c * y * c⁻¹)
      (by unfold SemiconjBy; group)).symm
  have hyz' : c * y * c⁻¹ ≠ z := by
    rw [← hcw]
    intro he
    exact hne (mul_left_cancel (mul_right_cancel he))
  refine hA.not_conj hyC hy2' (hyz.trans (isConj_iff.mpr ⟨c, rfl⟩)) hyz' ?_ ?_
  · rintro _ ⟨i, hi, rfl⟩
    have hiw : i ∈ centralizer ({w} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hd.i.good.comm i hi w hwU).symm
    have hyw' : y ∈ centralizer ({w} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr hyw
    refine ⟨⁅y, i⁆, ⟨hyI' i hi, ?_⟩, map_commutatorElement _ _ _⟩
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hyw' hiw)
      (Subgroup.inv_mem _ hyw')) (Subgroup.inv_mem _ hiw)
  · have e : c * y * c⁻¹ * z = c * (y * w) * c⁻¹ := by rw [← hcw]; group
    rw [e]
    exact hc.trans (isConj_iff.mpr ⟨c, rfl⟩)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
