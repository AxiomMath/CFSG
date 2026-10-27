module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23LcBase
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23ExU16
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23LcTwin

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Balance


section Y62

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem lc_y_exists (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hno : SecNoExit R e) (hα : alphaOf (Subgroup.closure ({u, t} : Set Y)) = ⊥)
    {L : Subgroup Y} (hLu : L ≤ Subgroup.centralizer ({u} : Set Y))
    (hKL : conjSub g (tightCore R) ≤ L) (hK'L : conjSub g K' ≤ L) :
    ∃ y ∈ L, y * y = 1 ∧ (¬ ∀ l ∈ L, y * l = l * y) ∧ ∀ l ∈ L, t * l * t⁻¹ = y * l * y⁻¹ := by
  classical
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have hq8 := lc_members_q8 hP hc hno hα
  have hKq := hq8 _ (CoreAssembly.mem_conjClass_self _)
  have hK'q := hq8 _ hc.std.hK'.1
  have hcomm := lc_twins_commute hP hc hno hα
  have hZ := Lc.center_sup_twins hKq hK'q hz.unique hz'.unique hz.sq hcomm
  have hge : g * t * g⁻¹ = u * e := hd.hgt
  have hes : e ∉ tightCore R ⊔ K' := e_not_mem_sup hc
  have ht0 : t ∈ tightCore R ⊔ K' := Subgroup.mem_sup_left hz.mem
  have hu0 : u ∈ tightCore R ⊔ K' := hd.hu
  have hE₁L : conjSub g (tightCore R ⊔ K') ≤ L := by
    rw [conjSub_sup]; exact sup_le hKL hK'L
  have hs1 : u * e ∈ conjSub g (tightCore R ⊔ K') := hge ▸ conj_mem_conjSub ht0
  have hv1 : g * u * g⁻¹ ∈ conjSub g (tightCore R ⊔ K') := conj_mem_conjSub hu0
  have hA : u * e * (u * e) = 1 := ue_sq hc
  have hcuL : ∀ x ∈ L, x * u = u * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hLu hx)
  have hcen : ∀ x ∈ conjSub g (tightCore R ⊔ K'),
      (∀ y ∈ conjSub g (tightCore R ⊔ K'), x * y = y * x) → x = 1 ∨ x = u * e := by
    intro x hx hxc
    have hx0 : g⁻¹ * x * g ∈ tightCore R ⊔ K' := mem_conjSub_iff.mp hx
    have h1 := hZ _ hx0 (fun y hy => by
      have hy1 : g * y * g⁻¹ ∈ conjSub g (tightCore R ⊔ K') := conj_mem_conjSub hy
      have h2 := hxc _ hy1
      calc g⁻¹ * x * g * y = g⁻¹ * (x * (g * y * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * y * g⁻¹) * x) * g := by rw [h2]
        _ = y * (g⁻¹ * x * g) := by group)
    rcases h1 with h | h
    · left
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    · right
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = u * e := by rw [h]; exact hge
  have hunot : u ∉ conjSub g (tightCore R ⊔ K') := by
    intro h
    rcases hcen u h (fun y hy => (hcuL y (hE₁L hy)).symm) with h1 | h1
    · exact hd.hu1 h1
    · apply hd.he1
      have : u * 1 = u * e := by rw [mul_one]; exact h1
      exact (mul_left_cancel this).symm
  have hB := gug_mem_B hc
  have hab : u * e * u = u * (u * e) := comm_gen hc _ (by simp) _ (by simp)
  have hac : u * e * t = t * (u * e) := comm_gen hc _ (by simp) _ (by simp)
  have hbc : u * t = t * u := comm_ut hc
  have hcase := enum8 (u * e) u t hab hac hbc hA hd.hu2 hz.sq _ hB
  have hmain : t ∈ conjSub g (tightCore R ⊔ K') ∨ u * t ∈ conjSub g (tightCore R ⊔ K') := by
    rcases hcase with h | h | h | h | h | h | h | h
    · exact absurd (by
        calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
          _ = 1 := by rw [h]; group) hd.hu1
    · exact absurd (by
        have : g * u * g⁻¹ = g * t * g⁻¹ := by rw [h, hge]
        have h2 : u = t := by
          calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
            _ = g⁻¹ * (g * t * g⁻¹) * g := by rw [this]
            _ = t := by group
        exact h2) hd.huz
    · exact absurd (h ▸ hv1) hunot
    · exact Or.inl (h ▸ hv1)
    · refine absurd ?_ hunot
      have h2 : u = (u * e) * (g * u * g⁻¹) := by
        rw [h]
        calc u = (u * e * (u * e)) * u := by rw [hA, one_mul]
          _ = u * e * (u * e * u) := by group
      rw [h2]
      exact Subgroup.mul_mem _ hs1 hv1
    · refine Or.inl ?_
      have h2 : t = (u * e) * (g * u * g⁻¹) := by
        rw [h]
        calc t = (u * e * (u * e)) * t := by rw [hA, one_mul]
          _ = u * e * (u * e * t) := by group
      rw [h2]
      exact Subgroup.mul_mem _ hs1 hv1
    · exact Or.inr (h ▸ hv1)
    · refine Or.inr ?_
      have h2 : u * t = (u * e) * (g * u * g⁻¹) := by
        rw [h]
        calc u * t = (u * e * (u * e)) * u * t := by rw [hA, one_mul]
          _ = u * e * (u * e * u * t) := by group
      rw [h2]
      exact Subgroup.mul_mem _ hs1 hv1
  have hnc : ∀ y ∈ conjSub g (tightCore R ⊔ K'), y ≠ 1 → y ≠ u * e →
      ¬ ∀ l ∈ L, y * l = l * y := by
    intro y hy hy1 hy2 hall
    rcases hcen y hy (fun y' hy' => hall y' (hE₁L hy')) with h | h
    · exact hy1 h
    · exact hy2 h
  have htC : t ∈ Subgroup.centralizer ({u} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (comm_ut hc).symm
  rcases hmain with h | h
  ·
    refine ⟨t, hE₁L h, hz.sq, hnc t h hz.ne_one ?_, fun l _ => rfl⟩
    intro hts
    apply hes
    have : e = u * t := by
      calc e = u * (u * e) := by rw [← mul_assoc, hd.hu2, one_mul]
        _ = u * t := by rw [← hts]
    rw [this]
    exact Subgroup.mul_mem _ hu0 ht0
  ·
    have hut2 : u * t * (u * t) = 1 := by
      calc u * t * (u * t) = u * (t * u) * t := by group
        _ = u * (u * t) * t := by rw [← hbc]
        _ = (u * u) * (t * t) := by group
        _ = 1 := by rw [hd.hu2, hz.sq]; group
    refine ⟨u * t, hE₁L h, hut2, hnc _ h ?_ ?_, ?_⟩
    · intro h1
      apply hd.huz
      have h2 : u = t⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [h2]
      exact inv_eq_of_mul_eq_one_right hz.sq
    · intro hts
      apply hes
      have : e = t := by
        have h3 : u * t = u * e := hts
        have := mul_left_cancel h3
        exact this.symm
      rw [this]
      exact ht0
    · intro l hl
      have hm : t * l * t⁻¹ ∈ Subgroup.centralizer ({u} : Set Y) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ htC (hLu hl)) (Subgroup.inv_mem _ htC)
      have hm' := Subgroup.mem_centralizer_singleton_iff.mp hm
      calc t * l * t⁻¹ = u * (t * l * t⁻¹) * u⁻¹ := by rw [← hm']; group
        _ = u * t * l * (u * t)⁻¹ := by group

end Y62

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
