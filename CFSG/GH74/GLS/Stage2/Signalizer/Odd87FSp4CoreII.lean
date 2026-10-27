module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSp4Def
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSp4X
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSp4II

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSp4

theorem coreII_cross {F : Type} [Field F] [Finite F] (hodd : ringChar F ≠ 2) (A : gsp 2 F) (d : Fˣ)
    (hAA : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = (d : F) • 1)
    (hdm : (d : F) = (multiplierUnit A : F)) (hsq : ∀ l : F, l ^ 2 ≠ (multiplierUnit A : F))
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpl : ringChar F ≠ p)
    {X : Subgroup (StatedProj (StatedSp 2 F))} (h : PConfig (conjAut 2 F A) p X) : False := by
  classical
  obtain ⟨hXp, hX1, -, hN⟩ := h
  have hℓ : (ringChar F).Prime := CharP.prime_ringChar F
  have : Fintype F := Fintype.ofFinite F
  have : CharP F (ringChar F) := ringChar.charP F
  obtain ⟨n, -, hqn⟩ := FiniteField.card F (ringChar F)
  have hK : Nat.card F = ringChar F ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hqn
  have hd0 : (d : F) ≠ 0 := d.ne_zero
  have hdsq : ∀ l : F, l ^ 2 ≠ (d : F) := by rw [hdm]; exact hsq
  have hμ : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)ᵀ * formJ 2 F *
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = (d : F) • formJ 2 F := by
    rw [hdm]; exact multiplierUnit_spec A
  obtain ⟨hqs, -⟩ := fixOf_conjSp_nonsquare hℓ hodd n.pos hK A hd0 hdsq hAA hμ
  have hE : Group.IsPerfect (fixOf (conjSp 2 F A)) := hqs.1
  have hEN : ∀ e ∈ fixOf (conjSp 2 F A),
      proj 2 F e ∈ normalizer (X : Set (StatedProj (StatedSp 2 F))) := by
    intro e he
    apply hN
    rw [mem_fixSub, conjAut_proj, mem_fixOf.mp he]
  obtain ⟨X₀, -, hmap, -, hcent⟩ := cross_centralizes hodd hp2 hpl hXp hE hEN
  apply hX1
  rw [← hmap, eq_bot_iff]
  rintro _ ⟨z, hz, rfl⟩
  have hzs : z ∈ spScalars 2 F :=
    typeII_centralizer_scalar hodd A d hAA hdm hsq z (fun g hg => (hcent z hz g hg).symm)
  rw [Subgroup.mem_bot, ← MonoidHom.mem_ker, ker_proj]
  exact hzs

theorem coreII_thm : CoreII := by
  intro F _ _ hodd A d hAA hdm hsq p _ hp2 X h
  by_cases hpc : ringChar F = p
  · exact coreII_defining A d hAA hdm hsq hp2 hpc h
  · exact coreII_cross hodd A d hAA hdm hsq hp2 hpc h

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
