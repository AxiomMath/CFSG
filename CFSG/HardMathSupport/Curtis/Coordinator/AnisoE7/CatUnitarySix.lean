module

public import CFSG.LieType.SeitzGeneration.Defs
public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.A5Nonabelian
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryWitness

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

open CFSG.LieType.SeitzGeneration

theorem isSimpleGroup_cat_twistedA_five_simple {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid) :
    IsSimpleGroup (Cat ⟨.twistedA 5 q, hv⟩) := by
  set ℓ := TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 5 q, hv⟩ with hℓ
  set f := TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 5 q, hv⟩ with hf
  have hU := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField ℓ f
    (TauCeti.ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA 5 q, hv⟩)
  have : Fact ℓ.Prime := ⟨hU.prime⟩
  have hqcard : ℓ ^ f = q.card := by
    simp [hℓ, hf, TauCeti.ValidLieTypeIndex.characteristic,
      TauCeti.ValidLieTypeIndex.fieldExponent, TauCeti.PrimePower.card_def]
  have hfin := hU.finite
  have hK : Nat.card (GaloisField ℓ (2 * f)) = (ℓ ^ f) ^ 2 := by
    rw [hU.card, ← pow_mul, mul_comm]
  have hnq : (5 + 1, ℓ ^ f) ≠ (3, 2) := by
    intro h
    simp only [Prod.mk.injEq] at h
    omega
  have hsimple := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU
    (GaloisField ℓ (2 * f)) ℓ f hK 6 (by norm_num) hnq
  change IsSimpleGroup (TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 5 q, hv⟩)
  exact (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 5 q hv).isSimpleGroup

theorem isSimpleGroup_cat_twistedA_five {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid) :
    IsSimpleGroup (Cat ⟨.twistedA 5 q, hv⟩) ∧ ∃ a b : Cat ⟨.twistedA 5 q, hv⟩, a * b ≠ b * a := by
  refine ⟨isSimpleGroup_cat_twistedA_five_simple hv, ?_⟩
  set ℓ := TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 5 q, hv⟩ with hℓ
  set f := TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 5 q, hv⟩ with hf
  have hU := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField ℓ f
    (TauCeti.ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA 5 q, hv⟩)
  have : Fact ℓ.Prime := ⟨hU.prime⟩
  have hfin := hU.finite
  have hK : Nat.card (GaloisField ℓ (2 * f)) = (ℓ ^ f) ^ 2 := by
    rw [hU.card, ← pow_mul, mul_comm]
  have hnq : (6, ℓ ^ f) ≠ (3, 2) := by
    intro h
    simp only [Prod.mk.injEq] at h
    omega
  obtain ⟨a, b, hne⟩ := exists_noncommuting_statedProj_statedSU
    (GaloisField ℓ (2 * f)) ℓ f hK 6 (by norm_num) hnq
  refine ⟨
    (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 5 q hv).symm a,
    (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 5 q hv).symm b, fun h => hne ?_⟩
  have := congrArg (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 5 q hv) h
  simpa using this

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

end
