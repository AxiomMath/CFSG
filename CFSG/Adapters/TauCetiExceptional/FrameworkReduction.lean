module

public import CFSG.Adapters.TauCetiExceptional.Interface
public import CFSG.LocalAnalysis.ComponentClassification.QuaternionComponentClassical

public section

namespace CFSG.TauCetiBridge

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti

theorem orthogonalReverse : OrthogonalReverse := fun _ _ n p f _ =>
  ⟨CFSG.ComponentClassification.QuaternionComponent.classicalModel_of_statedClassicalModel
      .POmegaOdd n p f,
    CFSG.ComponentClassification.QuaternionComponent.classicalModel_of_statedClassicalModel
      .POmegaPlus n p f,
    CFSG.ComponentClassification.QuaternionComponent.classicalModel_of_statedClassicalModel
      .POmegaMinus n p f⟩

theorem componentType_oddLieType_of_typewise (hB : TypewiseBridges) (X : Type) [Group X]
    (h : CFSG.Blueprint.OddLieType X) : CFSG.Assembly.ComponentType.OddLieType X :=
  componentType_oddLieType_of_blueprint hB orthogonalReverse X h

structure ChevalleyBridges : Prop where
  g2 : UntwistedBridge .G2 LieTypeIndex.G2
  f4 : UntwistedBridge .F4 LieTypeIndex.F4
  e6 : UntwistedBridge .E6 LieTypeIndex.E6
  e7 : UntwistedBridge .E7 LieTypeIndex.E7
  e8 : UntwistedBridge .E8 LieTypeIndex.E8
  twistedE6 : TwistedBridge .E6 LieTypeIndex.twistedE6
  trialityD4 : TwistedBridge .D4 LieTypeIndex.trialityD4

theorem exists_index_of_chevalleyExceptional (hB : ChevalleyBridges) {X : Type} [Group X]
    {t : StatedLieTag} {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ht : t ∈ chevalleyExceptionalTags) (h : ChevalleyExceptionalModel X t p f) :
    ∃ d : ValidLieTypeIndex, CFSG.Models.NamesTag d.1 t p f ∧ Nonempty (X ≃* d.Group) := by
  obtain ⟨hadm, hm⟩ := h
  have hf : 1 ≤ f := hadm.2.1
  let q : PrimePower := ⟨p, f, hp, hf⟩
  have hq : q.card = p ^ f := PrimePower.card_def q
  have hp2' : q.p ≠ 2 := hp2
  cases t <;> simp only [chevalleyExceptionalTags, Finset.mem_insert,
    Finset.mem_singleton, reduceCtorEq, or_false, false_or] at ht
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.G2 q).Valid := by
      refine (LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
      · simpa [LieTypeIndex.inStandardRange_iff, hq] using hadm.2.2.2
      · simp [LieTypeIndex.isDuplicateRepresentative_iff]
    obtain ⟨b⟩ := hB.g2 q hv hp2' K (by rw [hK, hq])
    exact ⟨⟨_, hv⟩, ⟨rfl, rfl⟩, ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.F4 q).Valid := by simp
    obtain ⟨b⟩ := hB.f4 q hv hp2' K (by rw [hK, hq])
    exact ⟨⟨_, hv⟩, ⟨rfl, rfl⟩, ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.E6 q).Valid := by simp
    obtain ⟨b⟩ := hB.e6 q hv hp2' K (by rw [hK, hq])
    exact ⟨⟨_, hv⟩, ⟨rfl, rfl⟩, ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.E7 q).Valid := by simp
    obtain ⟨b⟩ := hB.e7 q hv hp2' K (by rw [hK, hq])
    exact ⟨⟨_, hv⟩, ⟨rfl, rfl⟩, ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.E8 q).Valid := by simp
    obtain ⟨b⟩ := hB.e8 q hv hp2' K (by rw [hK, hq])
    exact ⟨⟨_, hv⟩, ⟨rfl, rfl⟩, ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.twistedE6 q).Valid := by simp
    obtain ⟨b⟩ := hB.twistedE6 q hv hp2' K (by rw [hK, hq]) σ
      (fun x => by rw [hq]; exact hσ x)
    exact ⟨⟨_, hv⟩, ⟨rfl, rfl⟩, ⟨e.trans b⟩⟩
  · obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hm
    have hv : (LieTypeIndex.trialityD4 q).Valid := by simp
    obtain ⟨b⟩ := hB.trialityD4 q hv hp2' K (by rw [hK, hq]) σ
      (fun x => by rw [hq]; exact hσ x)
    exact ⟨⟨_, hv⟩, ⟨rfl, rfl⟩, ⟨e.trans b⟩⟩

theorem componentType_oddLieType_of_chevalleyExceptional (hB : ChevalleyBridges) (G : Type)
    [Group G] (t : StatedLieTag) (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (_hadm : StatedLieAdmissible t 0 p f) (ht : t ∈ chevalleyExceptionalTags)
    (h : ChevalleyExceptionalModel G t p f) : CFSG.Assembly.ComponentType.OddLieType G := by
  obtain ⟨d, hd, he⟩ := exists_index_of_chevalleyExceptional hB hp hp2 ht h
  refine .inr ⟨d, ?_, ?_, he⟩ <;> obtain ⟨⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
    _ | _ | _ | _ | _, _⟩⟩ := d <;> cases t <;>
    simp_all [CFSG.Models.NamesTag, CFSG.Assembly.ComponentType.IsExceptionalIndex]

theorem models_oddLieType_of_chevalleyExceptional (hB : ChevalleyBridges) {X : Type} [Group X]
    {t : StatedLieTag} {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ht : t ∈ chevalleyExceptionalTags) (h : ChevalleyExceptionalModel X t p f) :
    CFSG.Models.OddLieType X :=
  ⟨t, 0, p, f, hp2, h.1, Or.inr ⟨rfl, exists_index_of_chevalleyExceptional hB hp hp2 ht h⟩⟩

end CFSG.TauCetiBridge
