module

public import CFSG.ClassicalInvolution.AschTight.S19MFactM2
public import CFSG.ClassicalInvolution.AschTight.S19FCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911


theorem factM1_three (E : Type) [Group E] [Finite E] [IsSimpleGroup E] (Ω : Set (Subgroup E))
    (e' : ℕ) (M : Ih8Model 3 1 Ω .G2 0 e') (φ : MulAut E) (hφ : φ * φ = 1)
    {L : Subgroup E} (hL : L ∈ Ω)
    (hφL : L.map φ.toMonoidHom = L)
    (hab : ∀ P : Subgroup E, IsPGroup 2 P → P ≤ L → (∀ x ∈ P, φ x = x) →
      ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) :
    ∃ x : E, φ = MulAut.conj x := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have he' : 1 ≤ e' := M.admissible.2.1
  have htag : (StatedLieTag.G2 = .G2 ∨ StatedLieTag.G2 = .trialityD4) := Or.inl rfl
  obtain ⟨R, hRcls, rfl⟩ := (M.mem_iff L).mp hL
  have hRfund := M.cls_sub hRcls
  have hinj : Function.Injective M.ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact M.ker_le_center.trans
      (RouteD.G2D4.center_modelUniv_g2d4_eq_bot hp2 htag 0 he').le
  refine S19F.exists_conj_of_transport M.ψ ⟨hinj, M.surj⟩ φ hφ hφL hab fun α hα hαR habα => ?_
  exact S19F.factM1_g2 hp2 he' α hα hRfund hαR habα

theorem factM2_three (E : Type) [Group E] [Finite E] [IsSimpleGroup E] (Ω : Set (Subgroup E))
    (e' : ℕ) (M : Ih8Model 3 1 Ω .G2 0 e') (hne : Ω.Nonempty) (x : E) (hx : x * x = 1)
    (hx1 : x ≠ 1) : ∃ L ∈ Ω, IsUniqueInvolution L x := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have ht : IsT6Tag StatedLieTag.G2 0 := Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have hadm := M.admissible
  have : Finite (modelUniv StatedLieTag.G2 0 3 e' Fact.out).K :=
    ModelFacts.finite_modelUniv hp2 Fact.out (ih8_isFundTag_mf M.isFundTag) hadm
  have hker : Odd (Nat.card M.ψ.ker) :=
    S19M.odd_natCard_ker M.ker_le_center (S19M.factM3 3 e' Fact.out hp2 StatedLieTag.G2 0 ht hadm)
  obtain ⟨y, hy, hy1, rfl⟩ := S19M.exists_involution_lift M.surj hker hx hx1
  obtain ⟨R₀, hR₀⟩ := M.cls_nonempty hne
  obtain ⟨c₀, hc₀⟩ := S19M.exists_isUniqueInvolution_of_mem_fund hp2 ht hadm (M.cls_sub hR₀)
  obtain ⟨g, hg⟩ := S19M.involutionsConj_modelUniv hp2 ht hadm c₀ y hc₀.sq hy hc₀.ne_one hy1
  have hc : IsUniqueInvolution (conjSub g R₀) y := by
    have h := hc₀.conj g
    rwa [hg] at h
  exact ⟨_, M.map_mem (M.cls_conj R₀ hR₀ g), S19M.isUniqueInvolution_map hker hc⟩

end CFSG.ClassicalInvolution.Asc77.T3CII
