module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLMain
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLEZ
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7EGenD
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LL3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL


section WFix

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem wFix_of_cfg (hc : P23Cfg n Y R S t K' W u e g) :
    ∀ w ∈ W, (∀ y ∈ MGrp (Om R) W, y * w = w * y) → w = 1 ∨ w = e := by
  have hstd := hc.std
  have hC := CoreData.of_S hstd.perp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hperp : KPerp (Om R) (tightCore R) = {tightCore R, K'} :=
    hstd.perp.perp.trans (twinSet_eq_pair hstd.two hstd.hK' hstd.hne)
  have hs : CFSG.ClassicalInvolution.Q8P.Asc77.Hyp23Setting (Om R) (tightCore R) K' t :=
    ⟨CFSG.ClassicalInvolution.Q8P.ascStand_of_twinCore hC, hstd.perp.disc, hz, hstd.hK',
      hstd.hne, hperp⟩
  have hst := hs.stand
  have : Fact (Q3CL.ClassicalClause (Om R)) := ⟨hst.cls⟩
  have c : Q3CL.Thompson.Ctx (Om R) W :=
    CFSG.ClassicalInvolution.Q8P.Asc77.T7D.ctx_of_stand hst hstd.hW
  obtain ⟨e₀, F, he₀, -, -, -, hab, hcomm, hac, -⟩ :=
    exists_frame4 hs hstd.hW hstd.htW hstd.hS4
  obtain ⟨x₁, x₂, x₃, h₁, h₂, h₃, r₁, r₂, r₃, t₁, t₂, t₃, s₁, s₂, s₃⟩ :=
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T7E.Frame4.exists_gens c F
  obtain ⟨m, -, o₁, o₂, o₃, z₁, z₂, -⟩ :=
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T7E.Frame4.orders c F h₁ h₂ h₃
  have hgen : W ≤ Subgroup.closure ({x₁, x₂, x₃} : Set Y) :=
    CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T7E.Frame4.W_le_closure c F he₀ hab hcomm hac
      h₁ h₂ h₃ r₂ r₃ t₃
  have m₁ : x₁ ∈ W := (h₁ ▸ Subgroup.mem_zpowers x₁ : x₁ ∈ F.ρ.R ⊓ W).2
  have m₂ : x₂ ∈ W := (h₂ ▸ Subgroup.mem_zpowers x₂ : x₂ ∈ F.ρ'.R ⊓ W).2
  have m₃ : x₃ ∈ W := (h₃ ▸ Subgroup.mem_zpowers x₃ : x₃ ∈ F.ρ₃.R ⊓ W).2
  have key : ∀ a ∈ W, (∀ y ∈ MGrp (Om R) W, y * a = a * y) →
      a = 1 ∨ a = (x₁ * x₂⁻¹ * x₃ ^ 2) ^ m := by
    intro a ha hM
    refine A3Mod.fixed_eq_one_or (show Commute x₁ x₂ from c.comm_W _ m₁ _ m₂)
      (show Commute x₁ x₃ from c.comm_W _ m₁ _ m₃) (show Commute x₂ x₃ from c.comm_W _ m₂ _ m₃)
      o₁ o₂ o₃ (z₁.trans z₂.symm) r₁ r₂ r₃ t₁ t₂ t₃ s₁ s₂ s₃ (hgen ha) ?_ ?_ ?_
    · rw [hM _ (Asc77.Thompson.le_MGrp_of_mem_D F.ρ.hR F.ρ.hr)]; group
    · rw [hM _ (Asc77.Thompson.le_MGrp_of_mem_D F.ρ'.hR F.ρ'.hr)]; group
    · rw [hM _ (Asc77.Thompson.le_MGrp_of_mem_D F.ρ₃.hR F.ρ₃.hr)]; group
  have hd := hc.data
  have heW : e ∈ W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set Y)) := by
    rw [← hd.he]
    exact Subgroup.subset_closure (Set.mem_singleton e)
  have heM : ∀ y ∈ MGrp (Om R) W, y * e = e * y := fun y hy =>
    CFSG.ClassicalInvolution.Asc77.T7E.Frame4.commutes_of_mem_centerIn heW.2
      (Asc77.Thompson.MGrp_le_normalizer _ W hy)
  have he₄ : e = (x₁ * x₂⁻¹ * x₃ ^ 2) ^ m := (key e heW.1 heM).resolve_left hd.he1
  intro w hw hwM
  rcases key w hw hwM with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans he₄.symm)

theorem lemLEZ_proved (n : ℕ) : LemLEZ n := by
  intro _ _ Y _ _ R S t K' W u e g hc _ hE _
  have hd := hc.data
  have hΩ : HypOmegaGen (Om R) := (CoreData.of_S hc.std.perp.core).hyp
  obtain ⟨φ⟩ := hd.hS4
  have hNe := normalizer_le_centralizer_e hd
  have hME : MGrp (Om R) W ≤ rLayer (Om R) e :=
    iSup₂_le fun R' hR' => F7C.le_rLayer hR'.1 (hR'.2.trans hNe)
  have hEM : rLayer (Om R) e ≤ oddCoreOf (rLayer (Om R) e) ⊔ MGrp (Om R) W :=
    F7G.rLayer_le_sup_MGrp hΩ hE
  exact omegaOneCenter_of_fix (Asc77.Thompson.isPGroup_of_mem_WSet hd.hW) φ hME hE hEM
    (p23_e_mem_rLayer hc) (wFix_of_cfg hc)

end WFix

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
