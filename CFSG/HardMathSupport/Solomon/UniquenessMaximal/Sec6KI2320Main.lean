module

public import CFSG.HardMathSupport.Solomon.Coordinator.C25L34
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BL34
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320L
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320Red
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320SL
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.RankThree.PartTwo.KFacts.L34
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open CFSG.HardMathSupport.Solomon.Coordinator (c25Fix c25GammaCl exists_equiv_projectiveSL
  l3b34_isElemAbelian_map)

local notation "conjAut'" => CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut

theorem goodGamma_le_c25GammaCl {Y : Type} [Group Y] [Finite Y] (A : Subgroup (MulAut Y)) :
    goodGamma A ≤ c25GammaCl A := by
  refine iSup_le fun S => iSup_le fun hS => iSup_le fun K => iSup_le fun hK => ?_
  have : K ≤ GLAPPrimeCoreOf 3 (c25Fix S) ⊔ GLAPLayer 3 (c25Fix S) := by
    rcases hK with h | h
    · exact le_sup_of_le_left (le_glaPPrimeCoreOf_of_normalPrime h)
    · exact le_sup_of_le_right (le_glaPLayer_of_normalSimple h)
  exact this.trans (le_iSup₂_of_le S hS le_rfl)

theorem top_le_goodGamma_P {k : Type} [Field k] (hk : Nat.card k = 4) {A : Subgroup (MulAut (projectiveSL 3 k))}
    (hA : IsElemAbelian 3 A) (h9 : Nat.card A = 9)
    (hinn : ¬ A ≤ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range) :
    ⊤ ≤ goodGamma A := by
  obtain ⟨u, hu, g, i, hi, hAeq⟩ := exists_conj_pglSylowMax hk hA h9 hinn
  have htop : ⊤ ≤ goodGamma (pglSylowMax u i) := by
    rcases hi with rfl | rfl
    · exact top_le_goodGamma_M0 hk hu
    · exact top_le_goodGamma_M2 hk hu
  have := top_le_goodGamma_map (conjAut' 3 k g) htop
  rwa [congr_toMonoidHom_eq_conj, ← hAeq] at this

theorem l34_holds (Y : Type) [Group Y] [Finite Y] (hY : IsLThreeFour Y)
    (A : Subgroup (MulAut Y)) (hA : IsElemAbelian 3 A) (h9 : Nat.card A = 9)
    (hinn : ¬ A ≤ CFSG.HardMathSupport.Solomon.LocalBalance.innerAut Y) :
    ⊤ ≤ c25GammaCl A := by
  obtain ⟨k, hkF, hkcard, ⟨φ⟩⟩ := exists_equiv_projectiveSL hY
  set ψ := MulAut.congr φ with hψ
  have hAP : IsElemAbelian 3 (A.map ψ.toMonoidHom) := l3b34_isElemAbelian_map ψ hA
  have h9P : Nat.card (A.map ψ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective ψ.injective, h9]
  have hinnP : ¬ A.map ψ.toMonoidHom ≤
      (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range := by
    intro hle
    apply hinn
    intro α hα
    obtain ⟨p, hp⟩ := hle ⟨α, hα, rfl⟩
    refine ⟨φ.symm p, ψ.injective ?_⟩
    have hp' : MulAut.conj p = ψ α := hp
    rw [← hp']
    ext x
    simp [hψ, MulAut.congr_apply]
  have htop := top_le_goodGamma_P hkcard hAP h9P hinnP
  exact (top_le_goodGamma_of_map φ rfl htop).trans (goodGamma_le_c25GammaCl A)

theorem top_le_goodGamma_SL {k : Type} [Field k] (hk : Nat.card k = 4)
    {A : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 3) k))}
    (hA : IsElemAbelian 3 A) (h9 : Nat.card A = 9)
    (hinn : ¬ A ≤ (MulAut.conj : Matrix.SpecialLinearGroup (Fin 3) k →*
      MulAut (Matrix.SpecialLinearGroup (Fin 3) k)).range) :
    ⊤ ≤ goodGamma A := by
  obtain ⟨u, hu, g, i, hi, M', hM, hAeq⟩ := exists_lift hk hA h9 hinn
  have htop : ⊤ ≤ goodGamma M' := by
    rcases hi with rfl | rfl
    · exact top_le_goodGamma_sl_M0 hk hu hM
    · exact top_le_goodGamma_sl_M2 hk hu hM
  have := top_le_goodGamma_map
    (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 k g) htop
  rwa [← hAeq] at this

theorem sl34_holds (Y : Type) [Group Y] [Finite Y] (hY : IsSLThreeFour Y)
    (A : Subgroup (MulAut Y)) (hA : IsElemAbelian 3 A) (h9 : Nat.card A = 9)
    (hinn : ¬ A ≤ CFSG.HardMathSupport.Solomon.LocalBalance.innerAut Y) :
    ⊤ ≤ c25GammaCl A := by
  obtain ⟨k, hkF, -, hkcard, ⟨e⟩⟩ := hY
  let φ : Y ≃* Matrix.SpecialLinearGroup (Fin 3) k :=
    e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 k).symm
  set ψ := MulAut.congr φ with hψ
  have hAP : IsElemAbelian 3 (A.map ψ.toMonoidHom) := l3b34_isElemAbelian_map ψ hA
  have h9P : Nat.card (A.map ψ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective ψ.injective, h9]
  have hinnP : ¬ A.map ψ.toMonoidHom ≤ (MulAut.conj : Matrix.SpecialLinearGroup (Fin 3) k →*
      MulAut (Matrix.SpecialLinearGroup (Fin 3) k)).range := by
    intro hle
    apply hinn
    intro α hα
    obtain ⟨p, hp⟩ := hle ⟨α, hα, rfl⟩
    refine ⟨φ.symm p, ψ.injective ?_⟩
    have hp' : MulAut.conj p = ψ α := hp
    rw [← hp']
    ext x
    simp [hψ, MulAut.congr_apply]
  have htop := top_le_goodGamma_SL hkcard hAP h9P hinnP
  exact (top_le_goodGamma_of_map φ rfl htop).trans (goodGamma_le_c25GammaCl A)

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.HardMathSupport.Solomon.Coordinator

theorem input23_20Facts_proved : Input23_20Facts where
  l34 := fun Y _ _ hY A hA h9 hinn => Sec6KI2320.l34_holds Y hY A hA h9 hinn
  sl34 := fun Y _ _ hY A hA h9 hinn => Sec6KI2320.sl34_holds Y hY A hA h9 hinn

theorem input23_20_proved : Input23_20 := input23_20_of_facts input23_20Facts_proved

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
