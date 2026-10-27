module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSp4Def
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSp4X
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSp4Fld

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSp4
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldEquiv)

theorem fieldAlpha_proj {F : Type} [Field F] (A : gsp 2 F) (σ : F ≃+* F) (g : StatedSp 2 F) :
    (conjAut 2 F A * fieldAut 2 F σ) (proj 2 F g) = proj 2 F ((conjSp 2 F A * fieldSp 2 F σ) g) := by
  rw [MulAut.mul_apply, MulAut.mul_apply, fieldAut_proj, conjAut_proj]

theorem coreField_defining {F : Type} [Field F] [Finite F] (A : gsp 2 F) (σ : F ≃+* F) (hσ1 : σ ≠ 1)
    (hσ2 : σ ^ 2 = 1) (d : Fˣ)
    (hd : (A : GL (Fin 2 ⊕ Fin 2) F) * glFieldEquiv (Fin 2 ⊕ Fin 2) σ (A : GL (Fin 2 ⊕ Fin 2) F) =
      Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) d)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpc : ringChar F = p)
    {X : Subgroup (StatedProj (StatedSp 2 F))} (h : PConfig (conjAut 2 F A * fieldAut 2 F σ) p X) :
    False := by
  classical
  have : CharP F p := hpc ▸ ringChar.charP F
  have hodd : ringChar F ≠ 2 := by rw [hpc]; exact hp2
  obtain ⟨hXp, hX1, -, hN⟩ := h
  obtain ⟨W, hW0, hWiso, hNW⟩ := exists_isotropic_parabolic hXp hX1
  refine field_no_invariant_isotropic hodd A σ hσ1 hσ2 d hd W hW0 hWiso ?_
  intro g hg
  refine mulVec_mem_of_proj_mem (hNW (hN (mem_fixSub.mpr ?_)))
  rw [fieldAlpha_proj, mem_fixOf.mp hg]

theorem coreField_cross {F : Type} [Field F] [Finite F] (hodd : ringChar F ≠ 2) (A : gsp 2 F)
    (σ : F ≃+* F) (hσ1 : σ ≠ 1) (hσ2 : σ ^ 2 = 1) (d : Fˣ)
    (hd : (A : GL (Fin 2 ⊕ Fin 2) F) * glFieldEquiv (Fin 2 ⊕ Fin 2) σ (A : GL (Fin 2 ⊕ Fin 2) F) =
      Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) d)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpl : ringChar F ≠ p)
    {X : Subgroup (StatedProj (StatedSp 2 F))} (h : PConfig (conjAut 2 F A * fieldAut 2 F σ) p X) :
    False := by
  classical
  obtain ⟨hXp, hX1, -, hN⟩ := h
  have hoddc : Odd (Nat.card F) := by
    have : Fintype F := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two hodd)
  obtain ⟨hqs, -⟩ := fixOf_conjSp_fieldSp hoddc A σ hσ2 hσ1 d hd
  have hE : Group.IsPerfect (fixOf (conjSp 2 F A * fieldSp 2 F σ)) := hqs.1
  have hEN : ∀ e ∈ fixOf (conjSp 2 F A * fieldSp 2 F σ),
      proj 2 F e ∈ normalizer (X : Set (StatedProj (StatedSp 2 F))) := by
    intro e he
    apply hN
    rw [mem_fixSub, fieldAlpha_proj, mem_fixOf.mp he]
  obtain ⟨X₀, -, hmap, -, hcent⟩ := cross_centralizes hodd hp2 hpl hXp hE hEN
  apply hX1
  rw [← hmap, eq_bot_iff]
  rintro _ ⟨z, hz, rfl⟩
  have hzs : z ∈ spScalars 2 F :=
    field_centralizer_scalar hodd A σ hσ1 hσ2 d hd z (fun g hg => (hcent z hz g hg).symm)
  rw [Subgroup.mem_bot, ← MonoidHom.mem_ker, ker_proj]
  exact hzs

theorem coreField_thm : CoreField := by
  intro F _ _ hodd A σ hσ1 hσ2 ⟨d, hd⟩ _ p _ hp2 X h
  by_cases hpc : ringChar F = p
  · exact coreField_defining A σ hσ1 hσ2 d hd hp2 hpc h
  · exact coreField_cross hodd A σ hσ1 hσ2 d hd hp2 hpc h

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
