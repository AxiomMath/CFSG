module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Assembly


theorem rk2_twA_rigid {G : Type} [Group G] [Finite G] {K : Subgroup G} {lab₁ lab₂ : GLALabel}
    (h₁ : LabelOf K lab₁) (h₂ : LabelOf K lab₂) (ht₁ : lab₁.tag = .twA) (ht₂ : lab₂.tag = .twA)
    (hr : 4 ≤ lab₂.rank) : lab₁ = lab₂ := by
  obtain ⟨-, -, hM₁⟩ := labelOf_model h₁
  obtain ⟨-, -, hM₂⟩ := labelOf_model h₂
  obtain ⟨t₁, r₁, n₁⟩ := lab₁
  obtain ⟨t₂, r₂, n₂⟩ := lab₂
  simp only at ht₁ ht₂ hr
  subst ht₁ ht₂
  have hM₁' : CFSG.Blueprint.LieModel (↥K ⧸ Subgroup.center ↥K) .PSU (r₁ + 1) 2 n₁ := hM₁
  have hM₂' : CFSG.Blueprint.LieModel (↥K ⧸ Subgroup.center ↥K) .PSU (r₂ + 1) 2 n₂ := hM₂
  obtain ⟨-, h2, h3⟩ := CFSG.SeitzReduction.UnitaryPilot.sumEvenTypeDetAt (m := r₂ + 1) (by omega)
    (↥K ⧸ Subgroup.center ↥K) n₂ .PSU (r₁ + 1) n₁ hM₂' hM₁'.admissible hM₁'
  have hr12 : r₁ = r₂ := by omega
  subst hr12 h3
  rfl

end CFSG.LocalAnalysis.GLTheoremA
