module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolY1b
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf7A03

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap


section Y1c

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem exists_three_gens (hc : P23Cfg n Y R S t K' W u e g) :
    ∃ x₁ x₂ x₃ : Y, x₁ ∈ W ∧ x₂ ∈ W ∧ x₃ ∈ W ∧ W ≤ Subgroup.closure ({x₁, x₂, x₃} : Set Y) := by
  have hs := hs_of_cfg hc
  have hst := hs.stand
  have : Fact (Q3CL.ClassicalClause (Om R)) := ⟨hst.cls⟩
  have hctx : Q3CL.Thompson.Ctx (Om R) W :=
    CFSG.ClassicalInvolution.Q8P.Asc77.T7D.ctx_of_stand hst hc.std.hW
  obtain ⟨e', F, he, -, -, -, hab, hcomm, hac, -⟩ :=
    exists_frame4 hs hc.std.hW hc.std.htW hc.std.hS4
  obtain ⟨x₁, x₂, x₃, h₁, h₂, h₃, r₁, r₂, r₃, t₁, t₂, t₃, s₁, s₂, s₃⟩ :=
    CFSG.ClassicalInvolution.Q8P.Asc77.T7E.Frame4.exists_gens hctx F
  have hgen : W ≤ Subgroup.closure ({x₁, x₂, x₃} : Set Y) :=
    CFSG.ClassicalInvolution.Q8P.Asc77.T7E.Frame4.W_le_closure hctx F he hab hcomm hac h₁ h₂ h₃ r₂
      r₃ t₃
  exact ⟨x₁, x₂, x₃, (h₁ ▸ Subgroup.mem_zpowers x₁ : x₁ ∈ F.ρ.R ⊓ W).2,
    (h₂ ▸ Subgroup.mem_zpowers x₂ : x₂ ∈ F.ρ'.R ⊓ W).2,
    (h₃ ▸ Subgroup.mem_zpowers x₃ : x₃ ∈ F.ρ₃.R ⊓ W).2, hgen⟩

theorem mem_B_of_involution (hc : P23Cfg n Y R S t K' W u e g) {w : Y} (hw : w ∈ W)
    (hw2 : w * w = 1) : w ∈ Subgroup.closure ({u * e, u, t} : Set Y) := by
  obtain ⟨x₁, x₂, x₃, h₁, h₂, h₃, hgen⟩ := exists_three_gens hc
  have hB := B_isElemAbelian hc
  exact T7K.mem_of_involution_of_card_eq_eight
    (Q3CL.Thompson.commutes_of_mem_WSet (CoreData.of_S hc.std.perp.core).hyp hc.std.hW) h₁ h₂ h₃
    hgen (T7K.B_le_W hc.data) (fun s hs' => by simpa only [pow_two] using hB.2 s hs')
    (B_natCard hc) hw hw2

theorem z_cases (hc : P23Cfg n Y R S t K' W u e g) :
    ∃ v' : Y, (v' = g * u * g⁻¹ ∨ v' = g * u * g⁻¹ * (u * e)) ∧ (t = v' ∨ t = u * v') := by
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz2 : t * t = 1 := hz.sq
  have hgN : g ∈ Subgroup.normalizer (W : Set Y) := T7K.g_mem_normalizer hd
  have hge : g * e * g⁻¹ = e := by
    rw [T7K.comm_e hd hgN]
    group
  have hgze : g * (t * e) * g⁻¹ = u := by
    calc g * (t * e) * g⁻¹ = (g * t * g⁻¹) * (g * e * g⁻¹) := by group
      _ = (u * e) * e := by rw [hd.hgt, hge]
      _ = u * (e * e) := by group
      _ = u := by rw [hd.he2, mul_one]
  have hcut : u * t = t * u := comm_ut hc
  have hcue : u * e = e * u := T7K.comm_e_of_mem_W hd hd.huW
  have hcte : t * e = e * t := T7K.comm_e_of_mem_W hd hd.hzW
  have hinj : ∀ x y : Y, g * x * g⁻¹ = g * y * g⁻¹ → x = y := fun x y h =>
    mul_left_cancel (mul_right_cancel h)
  have hxW : g * u * g⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hgN u).mp hd.huW
  have hx2 : (g * u * g⁻¹) * (g * u * g⁻¹) = 1 := by
    calc (g * u * g⁻¹) * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [hd.hu2]; group
  have hxB := mem_B_of_involution hc hxW hx2
  have hsup : ∀ x : Y, x ∈ tightCore R ⊔ K' → e = x → False := fun x hx hex =>
    e_not_mem_sup hc (hex ▸ hx)
  have hKe : u = t * e → False := fun h => by
    refine e_not_mem_sup hc ?_
    have : e = t * u := by rw [h, ← mul_assoc, hz2, one_mul]
    rw [this]
    exact (tightCore R ⊔ K').mul_mem (Subgroup.mem_sup_left hz.mem) hd.hu
  rcases T7K.mem_cases_of_commuting_involutions hd.hu2 hz2 hd.he2 hcut hcue hcte hxB with
    h | h | h | h | h | h | h | h
  · exact absurd (hinj u 1 (by rw [h]; group)) hd.hu1
  · exact ⟨t, Or.inl h.symm, Or.inl rfl⟩
  · exact absurd (hKe (hinj u (t * e) (by rw [h, hgze]))) id
  · refine ⟨g * u * g⁻¹, Or.inl rfl, Or.inr ?_⟩
    rw [h, ← mul_assoc, hd.hu2, one_mul]
  · exact absurd (hinj u e (by rw [h, hge])) (fun h' => hsup u hd.hu h'.symm)
  · refine ⟨g * u * g⁻¹ * (u * e), Or.inr rfl, Or.inr ?_⟩
    rw [h]
    calc t = u * (u * t) := by rw [← mul_assoc, hd.hu2, one_mul]
      _ = u * (t * u) := by rw [hcut]
      _ = u * (t * u * (e * e)) := by rw [hd.he2, mul_one]
      _ = u * (t * e * (u * e)) := by
          calc u * (t * u * (e * e)) = u * (t * (u * e) * e) := by group
            _ = u * (t * (e * u) * e) := by rw [hcue]
            _ = u * (t * e * (u * e)) := by group
  · exact absurd (hinj u t (by rw [h, hd.hgt])) hd.huz
  · refine ⟨g * u * g⁻¹ * (u * e), Or.inr rfl, Or.inl ?_⟩
    rw [h]
    calc t = u * (t * u) := by calc t = u * (u * t) := by rw [← mul_assoc, hd.hu2, one_mul]
                                  _ = u * (t * u) := by rw [hcut]
      _ = u * (t * u * (e * e)) := by rw [hd.he2, mul_one]
      _ = u * t * e * (u * e) := by
          calc u * (t * u * (e * e)) = u * t * (u * e) * e := by group
            _ = u * t * (e * u) * e := by rw [hcue]
            _ = u * t * e * (u * e) := by group
      _ = u * t * e * (u * e) := rfl

end Y1c

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
