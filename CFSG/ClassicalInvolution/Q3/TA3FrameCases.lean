module

public import CFSG.ClassicalInvolution.Q3.TA3FrameOut
public import CFSG.ClassicalInvolution.Q3.TA3FrameNoQ8
public import CFSG.ClassicalInvolution.Q3.TA3FrameExc
public import CFSG.ClassicalInvolution.Q3.TA3FrameSp4
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L5U5

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Frame

open CFSG CFSG.Open CFSG.Blueprint CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3.Q3T.MFS

@[expose] def FamilyLayer (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], TwoSubgroupsFourGenerated X → P X →
    ∀ t : X, orderOf t = 2 → LayerExcludesQ8 X t

@[expose] def SpecialFrame (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (z : Y) (L T : Subgroup Y), Setting z L T →
    memberIndex L T = 3 → TwoSubgroupsFourGenerated ↥T → P ↥T → False

structure FrameParts : Prop where
  l3 : FamilyLayer fun X _ => ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 5 ≤ p ^ f ∧
    Assembly.LowTwoRank.StatedClassicalModel X .PSL 3 p f
  u3 : FamilyLayer fun X _ => ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 5 ≤ p ^ f ∧
    Assembly.LowTwoRank.StatedClassicalModel X .PSU 3 p f
  l4 : FamilyLayer fun X _ => ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 5 ≤ p ^ f ∧ p ^ f % 8 ≠ 1 ∧
    LieModel X .PSL 4 p f
  u4 : FamilyLayer fun X _ => ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 5 ≤ p ^ f ∧ p ^ f % 8 ≠ 7 ∧
    LieModel X .PSU 4 p f
  l5 : FamilyLayer fun X _ => ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 5 ≤ p ^ f ∧ p ^ f % 4 = 3 ∧
    LieModel X .PSL 5 p f
  u5 : FamilyLayer fun X _ => ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 5 ≤ p ^ f ∧ p ^ f % 4 = 1 ∧
    LieModel X .PSU 5 p f
  l34 : SpecialFrame fun X _ => LieModel X .PSL 3 2 2
  d43 : SpecialFrame fun X _ => LieModel X .trialityD4 0 3 1

theorem eq_three_or_five_le {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    (p = 3 ∧ f = 1) ∨ 5 ≤ p ^ f := by
  by_cases h3 : p ^ f = 3
  · exact Or.inl (Nat.prime_three.pow_eq_iff.mp h3)
  · exact Or.inr (Q5L5U5.five_le hp hp2 hf h3).2

variable {Y : Type} [Group Y] [Finite Y] {z : Y} {L T : Subgroup Y}

theorem false_of_layer [T.Normal] (hL : IsClassicalMember3 L z) (hTL : T ⊔ L = ⊤)
    (h3 : memberIndex L T = 3) (h : ∀ t : T, orderOf t = 2 → LayerExcludesQ8 T t) : False :=
  false_of_layerExcludesQ8 hL hTL h3 (h _ (by rw [Subgroup.orderOf_mk]; exact hL.orderOf_eq_two))

theorem false_of_smallFamily (hP : FrameParts) (hS : Setting z L T) (h3 : memberIndex L T = 3)
    (hF : TwoSubgroupsFourGenerated ↥T) (hfam : SmallFamily ↥T) : False := by
  have := hS.normal
  have hL := hS.member
  have hTL := hS.sup
  have hC := hS.cent
  rcases hfam with ⟨p, f, hp, hp2, hf, h⟩ | ⟨p, f, hp, hp2, hf, h⟩ | ⟨p, f, hp, hp2, hf, h⟩ |
    ⟨f, h⟩ | ⟨p, f, hp, hp2, hf, hm, h⟩ | ⟨p, f, hp, hp2, hf, hm, h⟩ |
    ⟨p, f, hp, hp2, hf, hm, h⟩ | ⟨p, f, hp, hp2, hf, hm, h⟩ | h | ⟨p, f, hp, hp2, hf, h⟩ |
    ⟨p, f, hp, hp2, hf, h⟩ | ⟨p, f, hp, hp2, hf, h⟩ | h
  · rcases eq_three_or_five_le hp hp2 hf with ⟨rfl, rfl⟩ | h5
    · exact false_of_not_three_dvd hTL h3 hC (not_three_dvd_g2_three h)
    · exact false_of_layer hL hTL h3 (layerExcludesQ8_g2 hF hp hp2 h5 h)
  · rcases eq_three_or_five_le hp hp2 hf with ⟨rfl, rfl⟩ | h5
    · exact hP.d43 Y z L T hS h3 hF h
    · exact false_of_layer hL hTL h3 (layerExcludesQ8_d4 hF hp hp2 h5 h)
  · rcases eq_three_or_five_le hp hp2 hf with ⟨rfl, rfl⟩ | h5
    · exact false_of_not_three_dvd hTL h3 hC
        (not_three_dvd_psp_three (statedClassicalModel_of_lieModel_psp h))
    · exact false_of_layer hL hTL h3 (layerExcludesQ8_psp4 hF hp hp2 h5 h)
  · exact false_of_noQ8 hL hTL h3 (noQ8_ree h)
  · rcases eq_three_or_five_le hp hp2 hf with ⟨rfl, rfl⟩ | h5
    · exact false_of_not_three_dvd hTL h3 hC
        (not_three_dvd_psl_three (by norm_num) (Q5L5U5.statedClassicalModel_of_lieModel_psl h))
    · exact false_of_layer hL hTL h3 (hP.l4 _ hF ⟨p, f, hp, hp2, h5, hm, h⟩)
  · rcases eq_three_or_five_le hp hp2 hf with ⟨rfl, rfl⟩ | h5
    · exact false_of_not_three_dvd hTL h3 hC
        (not_three_dvd_psu_three (Q5L5U5.statedClassicalModel_of_lieModel_psu h))
    · exact false_of_layer hL hTL h3 (hP.u4 _ hF ⟨p, f, hp, hp2, h5, hm, h⟩)
  · rcases eq_three_or_five_le hp hp2 hf with ⟨rfl, rfl⟩ | h5
    · exact false_of_not_three_dvd hTL h3 hC
        (not_three_dvd_psl_three (by norm_num) (Q5L5U5.statedClassicalModel_of_lieModel_psl h))
    · exact false_of_layer hL hTL h3 (hP.l5 _ hF ⟨p, f, hp, hp2, h5, hm, h⟩)
  · have h5 : 5 ≤ p ^ f := (Q5L5U5.five_le hp hp2 hf (by omega)).2
    exact false_of_layer hL hTL h3 (hP.u5 _ hF ⟨p, f, hp, hp2, h5, hm, h⟩)
  · exact false_of_not_three_dvd hTL h3 hC (not_three_dvd_M12 h)
  · exact false_of_noQ8 hL hTL h3 (noQ8_psl2_odd hp hp2 h)
  · rcases eq_three_or_five_le hp hp2 hf with ⟨rfl, rfl⟩ | h5
    · exact false_of_not_three_dvd hTL h3 hC (not_three_dvd_psl_three le_rfl h)
    · exact false_of_layer hL hTL h3 (hP.l3 _ hF ⟨p, f, hp, hp2, h5, h⟩)
  · rcases eq_three_or_five_le hp hp2 hf with ⟨rfl, rfl⟩ | h5
    · exact false_of_not_three_dvd hTL h3 hC (not_three_dvd_psu_three h)
    · exact false_of_layer hL hTL h3 (hP.u3 _ hF ⟨p, f, hp, hp2, h5, h⟩)
  · exact false_of_not_three_dvd hTL h3 hC (not_three_dvd_M11 h)

end CFSG.ClassicalInvolution.Q3.TA3.Frame
