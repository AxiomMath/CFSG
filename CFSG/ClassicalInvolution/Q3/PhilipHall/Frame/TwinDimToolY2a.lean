module

public import CFSG.ClassicalInvolution.Q3.Q3T7S23A03
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


section Y2

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem not_mem_tq_u (hc : P23Cfg n Y R S t K' W u e g) :
    tightCore R ∉ tqMembers3 (Om R) u ∧ K' ∉ tqMembers3 (Om R) u := by
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hK'Ω : K' ∈ Om R := hc.std.hK'.1
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hzK' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  obtain ⟨R₁, R₁', b₁, b', hR, hR', -, -, -, hb₁R, hb'R', ob₁, ob', hub, -⟩ := e_decomp hc
  have hb₁K : b₁ ∈ tightCore R := hR.1 hb₁R
  have hb'K' : b' ∈ K' := hR'.1 hb'R'
  have hbt : b' ∈ trivialOnQuot (tightCore R) :=
    Q3T8.Asc77.T7L.twin_le_trivialOnQuot hΩ hK'Ω hK hc.std.hne hzK' hz hb'K'
  have hat : b₁ ∈ trivialOnQuot K' :=
    Q3T8.Asc77.T7L.twin_le_trivialOnQuot hΩ hK hK'Ω hc.std.hne.symm hz hzK' hb₁K
  have hsq : ∀ {x : Y}, (x = 1 ∨ x = t) → x * x = t → False := by
    intro x hx hxx
    rcases hx with rfl | rfl
    · exact hz.ne_one (by rw [← hxx]; simp)
    · exact hz.ne_one (by rw [hz.sq] at hxx; exact hxx.symm)
  constructor
  · rintro ⟨-, hu⟩
    have hb₁tq : b₁ ∈ trivialOnQuot (tightCore R) := by
      have : b₁ = u * b'⁻¹ := by rw [hub]; group
      rw [this]
      exact Subgroup.mul_mem _ hu (Subgroup.inv_mem _ hbt)
    exact hsq (hΩ.center_two hK hz b₁ hb₁K (hR.2.1.to_le (Subgroup.zpowers_le.mpr hb₁R))
      (fun y hy => (mem_trivialOnQuot_iff.mp hb₁tq).2 y hy)) ob₁
  · rintro ⟨-, hu⟩
    have hb'tq : b' ∈ trivialOnQuot K' := by
      have : b' = b₁⁻¹ * u := by rw [hub]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hat) hu
    exact hsq (hΩ.center_two hK'Ω hzK' b' hb'K' (hR'.2.1.to_le (Subgroup.zpowers_le.mpr hb'R'))
      (fun y hy => (mem_trivialOnQuot_iff.mp hb'tq).2 y hy)) ob'

theorem conj_cent_u (hc : P23Cfg n Y R S t K' W u e g) {T : Subgroup Y}
    (hTe : T ≤ Subgroup.centralizer ({e} : Set Y)) (hTt : ∀ x ∈ T, x * t = t * x) :
    conjSub g T ≤ Subgroup.centralizer ({u} : Set Y) := by
  have hd := hc.data
  have hNe := normalizer_le_centralizer_e hd
  have hgN : g ∈ Subgroup.normalizer (W : Set Y) := T7K.g_mem_normalizer hd
  have hgC : g ∈ Subgroup.centralizer ({e} : Set Y) := hNe hgN
  have hu : u = (g * t * g⁻¹) * e := by
    rw [hd.hgt, mul_assoc, hd.he2, mul_one]
  rintro _ ⟨x, hx, rfl⟩
  have e1 : (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := rfl
  rw [e1, Subgroup.mem_centralizer_singleton_iff]
  have hxe : x * e = e * x := Subgroup.mem_centralizer_singleton_iff.mp (hTe hx)
  have hge : g * e = e * g := Subgroup.mem_centralizer_singleton_iff.mp hgC
  have hye : (g * x * g⁻¹) * e = e * (g * x * g⁻¹) := by
    have hge' : g⁻¹ * e = e * g⁻¹ := by
      calc g⁻¹ * e = g⁻¹ * (e * g) * g⁻¹ := by group
        _ = g⁻¹ * (g * e) * g⁻¹ := by rw [hge]
        _ = e * g⁻¹ := by group
    calc (g * x * g⁻¹) * e = g * x * (g⁻¹ * e) := by group
      _ = g * x * (e * g⁻¹) := by rw [hge']
      _ = g * (x * e) * g⁻¹ := by group
      _ = g * (e * x) * g⁻¹ := by rw [hxe]
      _ = (g * e) * x * g⁻¹ := by group
      _ = (e * g) * x * g⁻¹ := by rw [hge]
      _ = e * (g * x * g⁻¹) := by group
  have hxt := hTt x hx
  have hyt : (g * x * g⁻¹) * (g * t * g⁻¹) = (g * t * g⁻¹) * (g * x * g⁻¹) := by
    calc (g * x * g⁻¹) * (g * t * g⁻¹) = g * (x * t) * g⁻¹ := by group
      _ = g * (t * x) * g⁻¹ := by rw [hxt]
      _ = (g * t * g⁻¹) * (g * x * g⁻¹) := by group
  show (g * x * g⁻¹) * u = u * (g * x * g⁻¹)
  rw [hu]
  calc (g * x * g⁻¹) * ((g * t * g⁻¹) * e)
      = ((g * x * g⁻¹) * (g * t * g⁻¹)) * e := by group
    _ = ((g * t * g⁻¹) * (g * x * g⁻¹)) * e := by rw [hyt]
    _ = (g * t * g⁻¹) * ((g * x * g⁻¹) * e) := by group
    _ = (g * t * g⁻¹) * (e * (g * x * g⁻¹)) := by rw [hye]
    _ = ((g * t * g⁻¹) * e) * (g * x * g⁻¹) := by group

end Y2

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
