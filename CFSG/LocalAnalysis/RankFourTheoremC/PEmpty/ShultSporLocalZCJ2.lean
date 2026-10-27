module

public import CFSG.Sporadic.Bridge.J2
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ShultSporLocalZCCheck

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Sporadic.Bridge.J2 CFSG.Blueprint.NativeSporadic

@[expose] def j2a : GL (Fin 14) (ZMod 5) :=
  ⟨toM mA, toM mA, by rw [← toM_mulL wfM_seeds.1 wfM_seeds.1, mulL_seeds.1, toM_idL],
    by rw [← toM_mulL wfM_seeds.1 wfM_seeds.1, mulL_seeds.1, toM_idL]⟩

@[expose] def j2b : GL (Fin 14) (ZMod 5) :=
  ⟨toM mB, toM mB2, by rw [← toM_mulL wfM_seeds.2.1 wfM_seeds.2.2, mulL_seeds.2.1, toM_idL],
    by rw [← toM_mulL wfM_seeds.2.2 wfM_seeds.2.1, mulL_seeds.2.2, toM_idL]⟩

theorem j2a_eq : j2a = uA :=
  Units.ext rfl

theorem j2b_eq : j2b = uB :=
  Units.ext rfl

@[expose] def glKey (x : GL (Fin 14) (ZMod 5)) : ℕ :=
  (List.finRange 14).foldl (fun h j => h * 5 + (x.val 0 j).val) 0

instance zcKeyGL : ZCKey (GL (Fin 14) (ZMod 5)) :=
  ⟨glKey⟩

theorem closure_j2ab : Subgroup.closure ({j2a, j2b} : Set (GL (Fin 14) (ZMod 5))) = seedGroup := by
  rw [j2a_eq, j2b_eq]

theorem card_seedGroup : Nat.card seedGroup = 604800 := by
  obtain ⟨e⟩ := nonempty_mulEquiv
  refine le_antisymm ?_ le_card_seedGroup
  rw [← Nat.card_congr nativeEquiv.toEquiv, Nat.card_congr e.toEquiv]
  exact tauCeti_finite_card_le.2

theorem card_closure_j2ab :
    Nat.card ↥(Subgroup.closure ({j2a, j2b} : Set (GL (Fin 14) (ZMod 5)))) = 604800 := by
  rw [closure_j2ab]
  exact card_seedGroup

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
