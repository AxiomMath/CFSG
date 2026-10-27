module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedReverse

public section

namespace CFSG.TauCetiBridge

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti

@[expose] def UntwistedBridge (τ : Tag) (c : PrimePower → LieTypeIndex) : Prop :=
  ∀ (q : PrimePower) (hv : (c q).Valid), q.p ≠ 2 →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = q.card →
      Nonempty (AdjointQuotient τ K ≃* ValidLieTypeIndex.Group ⟨c q, hv⟩)

@[expose] def TwistedBridge (t : TwistTag) (c : PrimePower → LieTypeIndex) : Prop :=
  ∀ (q : PrimePower) (hv : (c q).Valid), q.p ≠ 2 →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = q.card ^ t.order →
      ∀ σ : K →+* K, (∀ x, σ x = x ^ q.card) →
        Nonempty (CFSG.Blueprint.DerivedCentralQuotient (twistedFixedGroup t K σ) ≃*
          ValidLieTypeIndex.Group ⟨c q, hv⟩)

@[expose] def ReeG2Bridge : Prop :=
  ∀ (a : ℕ) (hv : (LieTypeIndex.reeG2 a).Valid) (K : Type) [Field K] [Finite K],
    Nat.card K = 3 ^ (2 * a + 1) →
      Nonempty (CFSG.Blueprint.DerivedCentralQuotient (reeFixedGroup .G2 K reeG2Perm
          fun i => if i ∈ reeG2Long then 3 ^ a else 3 ^ (a + 1)) ≃*
        ValidLieTypeIndex.Group ⟨.reeG2 a, hv⟩)

structure TypewiseBridges : Prop where
  g2 : UntwistedBridge .G2 LieTypeIndex.G2
  f4 : UntwistedBridge .F4 LieTypeIndex.F4
  e6 : UntwistedBridge .E6 LieTypeIndex.E6
  e7 : UntwistedBridge .E7 LieTypeIndex.E7
  e8 : UntwistedBridge .E8 LieTypeIndex.E8
  twistedE6 : TwistedBridge .E6 LieTypeIndex.twistedE6
  trialityD4 : TwistedBridge .D4 LieTypeIndex.trialityD4
  reeG2 : ReeG2Bridge

@[expose] def OrthogonalReverse : Prop :=
  ∀ (G : Type) [Group G] (n p f : ℕ) [Fact p.Prime],
    (StatedClassicalModel G .POmegaOdd n p f →
        CFSG.Assembly.ComponentType.ClassicalModel G .POmegaOdd n p f) ∧
      (StatedClassicalModel G .POmegaPlus n p f →
        CFSG.Assembly.ComponentType.ClassicalModel G .POmegaPlus n p f) ∧
      (StatedClassicalModel G .POmegaMinus n p f →
        CFSG.Assembly.ComponentType.ClassicalModel G .POmegaMinus n p f)

structure GeckMatch (τ : Tag) (t : DynkinType) (ht : t.Valid) where
  lab : Fin (t.geckDim ht) ≃ Label τ
  node : Fin t.rank ≃ Fin τ.rank
  sgn : Fin (t.geckDim ht) → ℤˣ
  matrix_inl : ∀ (A : Type) [CommRing A] (i : Fin t.rank) (c : A) (r s : Fin (t.geckDim ht)),
    ((t.geckRootSubgroupPoints ht (.inl i) A (Multiplicative.ofAdd c) :
        Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) :
          Matrix (Fin (t.geckDim ht)) (Fin (t.geckDim ht)) A) r s =
      ((sgn r : ℤ) : A) * xOp τ A (node i) c (Finsupp.single (lab s) (1 : A)) (lab r) *
        ((sgn s : ℤ) : A)
  matrix_inr : ∀ (A : Type) [CommRing A] (i : Fin t.rank) (c : A) (r s : Fin (t.geckDim ht)),
    ((t.geckRootSubgroupPoints ht (.inr i) A (Multiplicative.ofAdd c) :
        Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) :
          Matrix (Fin (t.geckDim ht)) (Fin (t.geckDim ht)) A) r s =
      ((sgn r : ℤ) : A) * yOp τ A (node i) c (Finsupp.single (lab s) (1 : A)) (lab r) *
        ((sgn s : ℤ) : A)

theorem exists_index_of_exceptional (hB : TypewiseBridges) {X : Type} [Group X]
    {t : StatedLieTag} {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : (t ∈ chevalleyExceptionalTags ∧ ChevalleyExceptionalModel X t p f) ∨
      (t ∈ reeTitsTags ∧ ReeTitsModel X t p f)) :
    ∃ d : ValidLieTypeIndex, CFSG.Models.NamesTag d.1 t p f ∧ Nonempty (X ≃* d.Group) := by
  rcases h with ⟨ht, hadm, hm⟩ | ⟨ht, hadm, a, hfa, hm⟩
  · have hf : 1 ≤ f := hadm.2.1
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
  · cases t <;> simp only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton,
      reduceCtorEq, or_false, false_or] at ht
    · obtain ⟨-, -, -, rfl, -, h3⟩ := hadm
      obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
      have ha : 1 ≤ a := by omega
      have hv : (LieTypeIndex.reeG2 a).Valid := by
        refine (LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
        · simpa [LieTypeIndex.inStandardRange_iff] using ha
        · simp [LieTypeIndex.isDuplicateRepresentative_iff]
      obtain ⟨b⟩ := hB.reeG2 a hv K (by rw [hK, hfa])
      exact ⟨⟨_, hv⟩, ⟨rfl, hfa⟩, ⟨e.trans b⟩⟩
    · exact absurd hadm.2.2.2.1 hp2
    · exact absurd hadm.2.2.2.1 hp2

theorem models_oddLieType_of_blueprint (hB : TypewiseBridges) (X : Type) [Group X]
    (h : CFSG.Blueprint.OddLieType X) : CFSG.Models.OddLieType X := by
  obtain ⟨t, n, p, f, hp, hp2, hadm, hL⟩ := h
  rcases hL with ⟨_, hc⟩ | ⟨rfl, he⟩ | ⟨rfl, hr⟩ | ⟨-, -, hs⟩
  · exact ⟨t, n, p, f, hp2, hadm, Or.inl hc⟩
  · exact ⟨t, 0, p, f, hp2, hadm,
      Or.inr ⟨rfl, exists_index_of_exceptional hB hp hp2 (.inl he)⟩⟩
  · exact ⟨t, 0, p, f, hp2, hadm,
      Or.inr ⟨rfl, exists_index_of_exceptional hB hp hp2 (.inr hr)⟩⟩
  · exact absurd hs.1 hp2

theorem componentType_oddLieType_of_blueprint (hB : TypewiseBridges)
    (hO : OrthogonalReverse) (X : Type) [Group X] (h : CFSG.Blueprint.OddLieType X) :
    CFSG.Assembly.ComponentType.OddLieType X := by
  obtain ⟨t, n, p, f, hp, hp2, hadm, hL⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  open CFSG.ComponentClassification.ClassicalModelStatedBridge in
  rcases hL with ⟨ht, hc⟩ | ⟨rfl, he⟩ | ⟨rfl, hr⟩ | ⟨-, -, hs⟩
  · cases t <;> simp only [classicalTags, Finset.mem_insert, Finset.mem_singleton,
      reduceCtorEq, or_false, false_or] at ht
    · exact .inl ⟨.PSL, n, p, f, inferInstance, hp2, classicalModel_psl_of_stated hc⟩
    · exact .inl ⟨.PSU, n, p, f, inferInstance, hp2, classicalModel_psu_of_stated hc⟩
    · exact .inl ⟨.PSp, n, p, f, inferInstance, hp2, classicalModel_psp_of_stated hc⟩
    · exact .inl ⟨.POmegaOdd, n, p, f, inferInstance, hp2, (hO X n p f).1 hc⟩
    · exact .inl ⟨.POmegaPlus, n, p, f, inferInstance, hp2, (hO X n p f).2.1 hc⟩
    · exact .inl ⟨.POmegaMinus, n, p, f, inferInstance, hp2, (hO X n p f).2.2 hc⟩
  all_goals first
    | exact absurd hs.1 hp2
    | skip
  · obtain ⟨d, hd, he'⟩ := exists_index_of_exceptional hB hp hp2 (.inl he)
    refine .inr ⟨d, ?_, ?_, he'⟩ <;> obtain ⟨⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
      _ | _ | _ | _ | _, _⟩⟩ := d <;> cases t <;>
      simp_all [CFSG.Models.NamesTag, CFSG.Assembly.ComponentType.IsExceptionalIndex]
  · obtain ⟨d, hd, he'⟩ := exists_index_of_exceptional hB hp hp2 (.inr hr)
    refine .inr ⟨d, ?_, ?_, he'⟩ <;> obtain ⟨⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
      _ | _ | _ | _ | _, _⟩⟩ := d <;> cases t <;>
      simp_all [CFSG.Models.NamesTag, CFSG.Assembly.ComponentType.IsExceptionalIndex]

end CFSG.TauCetiBridge
