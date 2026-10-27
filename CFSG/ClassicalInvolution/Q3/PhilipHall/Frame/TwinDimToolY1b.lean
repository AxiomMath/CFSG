module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolY1a
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolE1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap


section Y1b

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem e_not_mem_sup (hc : P23Cfg n Y R S t K' W u e g) : e ∉ tightCore R ⊔ K' := by
  intro he
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hK'Ω : K' ∈ Om R := hc.std.hK'.1
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hzK' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  obtain ⟨R₁, R₁', b₁, b', hR, hR', hRD, hR'D, hc', -, -, -, -, -, -⟩ := e_decomp hc
  have hRN := hRD.2
  have hR'N := hR'D.2
  have hQ : IsSylow2In (R₁ ⊔ R₁') (tightCore R ⊔ K') :=
    Q3T8.Asc77.T7A.isSylow2In_sup_of_twin hΩ hK hK'Ω hc.std.hne hz hzK' hR hR' hc'
  have he2 : e * e = 1 := hd.he2
  have hle : R₁ ⊔ R₁' ≤ Subgroup.centralizer ({e} : Set Y) := by
    refine sup_le (fun r hr => ?_) (fun r hr => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (T7K.comm_e hd (hRN hr))
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (T7K.comm_e hd (hR'N hr))
  have hcz : Subgroup.centralizer (Subgroup.zpowers e : Set Y) = Subgroup.centralizer {e} := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have heN : R₁ ⊔ R₁' ≤ Subgroup.normalizer (Subgroup.zpowers e : Set Y) := by
    refine hle.trans ?_
    rw [← hcz]
    exact Subgroup.centralizer_le_normalizer _
  have hpe : IsPGroup 2 (Subgroup.zpowers e) := isPGroup_zpowers_of_mul_self_eq_one he2 hd.he1
  have hpg : IsPGroup 2 ↥((R₁ ⊔ R₁') ⊔ Subgroup.zpowers e) :=
    hQ.2.1.to_sup_of_normal_right' hpe heN
  have heQ : e ∈ R₁ ⊔ R₁' := by
    have := hQ.2.2 _ (sup_le hQ.1 (Subgroup.zpowers_le.mpr he)) hpg le_sup_left
    rw [← this]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
  obtain ⟨a, ha, b, hb, hab0⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hc' heQ
  have hab : e = a * b := hab0.symm
  have hbr : ∀ r ∈ R₁, b * r = r * b := fun r hr => (hc' r hr b hb).symm
  have hac : ∀ r ∈ R₁, a * r = r * a := by
    intro r hr
    have h1 : r * e = e * r := T7K.comm_e hd (hRN hr)
    rw [hab] at h1
    have h2 : r * a * b = a * r * b := by
      calc r * a * b = r * (a * b) := by group
        _ = (a * b) * r := h1
        _ = a * (b * r) := by group
        _ = a * (r * b) := by rw [hbr r hr]
        _ = a * r * b := by group
    exact (mul_right_cancel h2).symm
  have hbc : ∀ r ∈ R₁', b * r = r * b := by
    intro r hr
    have h1 : r * e = e * r := T7K.comm_e hd (hR'N hr)
    rw [hab] at h1
    have har : a * r = r * a := hc' a ha r hr
    have h2 : a * (r * b) = a * (b * r) := by
      calc a * (r * b) = (a * r) * b := by group
        _ = (r * a) * b := by rw [har]
        _ = r * (a * b) := by group
        _ = (a * b) * r := h1
        _ = a * (b * r) := by group
    exact (mul_left_cancel h2).symm
  have hapg : IsPGroup 2 (Subgroup.zpowers a) := hR.2.1.to_le (Subgroup.zpowers_le.mpr ha)
  have hbpg : IsPGroup 2 (Subgroup.zpowers b) := hR'.2.1.to_le (Subgroup.zpowers_le.mpr hb)
  have haK : a ∈ tightCore R := hR.1 ha
  have hbK' : b ∈ K' := hR'.1 hb
  have hatq : a ∈ trivialOnQuot (tightCore R) :=
    TwinADescent3.mem_tq_of_sylCent hΩ h2 hK
      ⟨R₁, hR, fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (hac r hr).symm⟩
  have hbtq : b ∈ trivialOnQuot K' :=
    TwinADescent3.mem_tq_of_sylCent hΩ h2 hK'Ω
      ⟨R₁', hR', fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (hbc r hr).symm⟩
  have ha1z : a = 1 ∨ a = t := hΩ.center_two hK hz a haK hapg
    (fun y hy => (mem_trivialOnQuot_iff.mp hatq).2 y hy)
  have hb1z : b = 1 ∨ b = t := hΩ.center_two hK'Ω hzK' b hbK' hbpg
    (fun y hy => (mem_trivialOnQuot_iff.mp hbtq).2 y hy)
  have hez : e = t := by
    have hz2 : t * t = 1 := hz.sq
    rcases ha1z with h1 | h1 <;> rcases hb1z with h2 | h2
    · exact absurd (by rw [hab, h1, h2]; simp) hd.he1
    · rw [hab, h1, h2]; simp
    · rw [hab, h1, h2]; simp
    · exact absurd (by rw [hab, h1, h2]; exact hz2) hd.he1
  have hgz : g * t * g⁻¹ = t := by
    have := T7K.comm_e hd (T7K.g_mem_normalizer hd)
    rw [hez] at this
    calc g * t * g⁻¹ = (t * g) * g⁻¹ := by rw [this]
      _ = t := by group
  have h3 := hd.hgt
  rw [hgz, hez] at h3
  have : u = 1 := by
    have h4 : u * t = 1 * t := by rw [one_mul]; exact h3.symm
    exact mul_right_cancel h4
  exact hd.hu1 this

theorem B_natCard (hc : P23Cfg n Y R S t K' W u e g) :
    Nat.card ↥(Subgroup.closure ({u * e, u, t} : Set Y)) = 8 := by
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hD := T7A.isElemAbelian2_closure_pair hd.hu2 hz.sq hd.hu1 hz.ne_one hd.huz (comm_ut hc)
  have he2 : orderOf e = 2 := orderOf_eq_prime (by rw [pow_two]; exact hd.he2) hd.he1
  have hsub : ∀ x ∈ ({u * e, u, t} : Set Y), x ∈ Subgroup.closure ({u, t} : Set Y) ⊔
      Subgroup.zpowers e := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.subset_closure (by simp)))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers e))
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  have hcl : Subgroup.closure ({u * e, u, t} : Set Y) =
      Subgroup.closure ({u, t} : Set Y) ⊔ Subgroup.zpowers e := by
    apply le_antisymm
    · exact (Subgroup.closure_le _).mpr hsub
    · refine sup_le ?_ (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.closure_le]
        intro x hx
        rcases hx with rfl | rfl
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
      · have : e = u⁻¹ * (u * e) := by group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
          (Subgroup.subset_closure (by simp))
  have hcomm : Commutes (Subgroup.closure ({u, t} : Set Y)) (Subgroup.zpowers e) := by
    have hle : Subgroup.closure ({u, t} : Set Y) ≤ Subgroup.centralizer ({e} : Set Y) := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (T7K.comm_e_of_mem_W hd hd.huW)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (T7K.comm_e_of_mem_W hd hd.hzW)
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have : Commute x e := Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
    exact (this.zpow_right i).eq
  have hinf : Subgroup.closure ({u, t} : Set Y) ⊓ Subgroup.zpowers e = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases T7A.eq_one_or_eq_of_mem_zpowers he2 hx.2 with h1 | h1
    · rw [h1]
      exact Subgroup.one_mem _
    · exfalso
      refine e_not_mem_sup hc ?_
      have hle : Subgroup.closure ({u, t} : Set Y) ≤ tightCore R ⊔ K' := by
        rw [Subgroup.closure_le]
        intro y hy
        rcases hy with rfl | rfl
        · exact hd.hu
        · exact Subgroup.mem_sup_left hz.mem
      rw [← h1]
      exact hle hx.1
  have hN := T7A.card_sup_mul_card_inf (T7A.le_normalizer_of_commutes hcomm)
  rw [hinf, Subgroup.card_bot, Nat.card_zpowers, he2, hD.1, mul_one] at hN
  rw [hcl, sup_comm, hN]
  norm_num

end Y1b

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
