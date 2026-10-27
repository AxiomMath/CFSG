module

public import CFSG.LieType.OutStructureG2
public import CFSG.LieType.OutStructureF4
public import CFSG.LieType.OutStructureD
public import CFSG.LieType.OutStructureE78
public import CFSG.LieType.OutStructureSuzuki
public import CFSG.LieType.OutStructureRee
public import CFSG.LieType.OutStructureSmall
public import CFSG.LieType.OutStructureBCD

public section

namespace CFSG.LieType.OutStructure

open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def I713ClauseFree (i : TauCeti.CFSGIndex) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) →
    Nonempty (K ≃* i.Group) → ∀ p : ℕ, p.Prime → p ≠ 2 →
        (¬ p ∣ Nat.card (Outer K)) ∨
        (∃ F : Subgroup (MulAut K), (CFSG.ComponentClassification.OuterAutomorphisms.inner K ⊔ F).Normal ∧ IsCyclic ↥F ∧ F ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner K = ⊥ ∧
          ¬ p ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner K ⊔ F).index ∧
          ∀ x : MulAut K, (∃ k : ℕ, x ^ (p ^ k) = 1) → x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner K ⊔ F) ∨
        (p = 3 ∧ IsCyclic (Outer K) ∧ OuterPElementLifts K p)

theorem i713ClauseFree_cyclic (p : ℕ) (hp : p.Prime) :
    I713ClauseFree (TauCeti.CFSGIndex.cyclic p hp) := by
  intro K _ _ _ hnab ⟨e⟩ _ _ _
  obtain ⟨a, b, hab⟩ := hnab
  exact absurd (e.injective (by
    rw [map_mul, map_mul]
    exact mul_comm _ _)) hab

theorem i713ClauseFree_alternating (n : ℕ) (hn : 5 ≤ n) :
    I713ClauseFree (TauCeti.CFSGIndex.alternating n hn) := by
  intro K _ _ _ _ ⟨e⟩ p hp hp2
  exact i713_alternating hn e hp hp2

theorem i713ClauseFree_sporadic
    (s : TauCeti.SporadicName) :
    I713ClauseFree (TauCeti.CFSGIndex.sporadic s) := by
  intro K _ _ hK hnab ⟨e⟩ p hp hp2
  exact Or.inl (i713_of_mulEquiv_sporadic hK hnab e hp hp2)

section G2

open CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.UnbalancedCatalog

theorem i713ClauseFree_lie_G2
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid) :
    I713ClauseFree (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩) := by
  intro K _ _ _ _ ⟨eK⟩ p hp _
  have : Finite (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group :=
    Finite.of_equiv K eK.toEquiv
  have h3 : 3 ≤ q.p ^ q.exponent := by
    have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    simpa only [TauCeti.LieTypeIndex.inStandardRange_iff, TauCeti.PrimePower.card_def] using h
  have hm : ChevalleyExceptionalModel (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group .G2
      q.p q.exponent := by
    by_cases hq2 : q.p = 2
    · refine ⟨⟨q.prime_p, q.exponent_pos, rfl, h3⟩, ?_⟩
      exact CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hq2 (MulEquiv.refl _)
    · exact CFSG.RankThree.PartTwo.Sec4.Census.chevalleyExceptionalModel_G2_of_odd q hv hq2
  obtain ⟨L, hLfield, hLfin, hLcard, ⟨eL⟩⟩ :=
    nonempty_mulEquiv_adjointGroup .G2 hm.2
  let := hLfield
  let := hLfin
  have : Finite (adjointGroup Tag.G2 L) := Subtype.finite
  exact Or.inr (Or.inl (exists_fieldPart_of_mulEquiv (eK.trans eL)
    (exists_fieldPart_adjointGroup_G2 q.prime_p q.exponent_pos L hLcard h3 hp)))

end G2

section F4

open CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LocalAnalysis.ComponentInitial

theorem i713ClauseFree_lie_F4
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.F4 q).Valid) :
    I713ClauseFree (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩) := by
  intro K _ _ _ _ ⟨eK⟩ p hp _
  have : Finite (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩).Group :=
    Finite.of_equiv K eK.toEquiv
  have hm : ChevalleyExceptionalModel (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩).Group .F4
      q.p q.exponent := by
    have : Fact q.p.Prime := ⟨q.prime_p⟩
    have hcard : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
      GaloisField.card q.p q.exponent q.exponent_pos.ne'
    have hqcard : Nat.card (GaloisField q.p q.exponent) = q.card :=
      hcard.trans (TauCeti.PrimePower.card_def q).symm
    refine ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, ?_⟩
    by_cases hq2 : q.p = 2
    · obtain ⟨e⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_F4 q hv hq2
        (GaloisField q.p q.exponent) hqcard
      exact ⟨GaloisField q.p q.exponent, inferInstance, inferInstance, hcard, ⟨e.symm⟩⟩
    · obtain ⟨e⟩ := CFSG.TauCetiBridge.untwistedBridge_F4 q hv hq2
        (GaloisField q.p q.exponent) hqcard
      exact ⟨GaloisField q.p q.exponent, inferInstance, inferInstance, hcard, ⟨e.symm⟩⟩
  obtain ⟨L, hLfield, hLfin, hLcard, ⟨eL⟩⟩ :=
    nonempty_mulEquiv_adjointGroup .F4 hm.2
  let := hLfield
  let := hLfin
  have : Finite (adjointGroup Tag.F4 L) := Subtype.finite
  exact Or.inr (Or.inl (exists_fieldPart_of_mulEquiv (eK.trans eL)
    (exists_fieldPart_adjointGroup_F4 q.prime_p q.exponent_pos L hLcard hp)))

end F4

section TrialityD4

open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.Adapters.CatalogueFieldBridges

theorem i713ClauseFree_lie_trialityD4
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) :
    I713ClauseFree (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩) := by
  intro K _ _ _ _ ⟨eK⟩ p hp _
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let L := GaloisField q.p (3 * q.exponent)
  have hLcardp : Nat.card L = (q.p ^ q.exponent) ^ 3 := by
    rw [GaloisField.card q.p (3 * q.exponent)
      (Nat.mul_ne_zero (by norm_num) q.exponent_pos.ne'), ← pow_mul, mul_comm]
  have hLcard : Nat.card L = q.card ^ 3 := by
    rw [hLcardp, TauCeti.PrimePower.card_def]
  let σ : L ≃+* L := iterateFrobeniusEquiv L q.p q.exponent
  have hσdef : ∀ c : L, σ c = c ^ (q.p ^ q.exponent) := fun c =>
    iterateFrobeniusEquiv_def _ _ _ _
  have hσ : ∀ c : L, σ c = c ^ q.card := fun c => by
    rw [hσdef c, TauCeti.PrimePower.card_def]
  obtain ⟨e⟩ := nonempty_catEquiv_graphFixedRootGroup_trialityD4 (q := q) hv
    (K := L) hLcard σ hσ
  obtain ⟨F, hnorm, hcyc, hbot, htop⟩ :=
    exists_fieldPart_graphFixedRootGroup_trialityD4 (p := q.p) q.prime_p q.exponent_pos
      L hLcardp σ hσdef
  refine Or.inr (Or.inl (exists_fieldPart_of_mulEquiv (eK.trans e)
    ⟨F, ?_, hcyc, hbot, ?_, ?_⟩))
  · rw [htop]; exact Subgroup.normal_top
  · rw [htop, Subgroup.index_top]; exact hp.not_dvd_one
  · intro x hx
    rw [htop]
    exact Subgroup.mem_top x

end TrialityD4

section E78

open CFSG.LieType.Chevalley
open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem i713ClauseFree_lie_E7
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E7 q).Valid) :
    I713ClauseFree (TauCeti.CFSGIndex.lie ⟨.E7 q, hv⟩) := by
  intro K _ _ _ _ ⟨eK⟩ p hp hp2
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Finite (TauCeti.CFSGIndex.lie ⟨.E7 q, hv⟩).Group :=
    Finite.of_equiv K eK.toEquiv
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card q.p q.exponent q.exponent_pos.ne'
  have hqcard : Nat.card (GaloisField q.p q.exponent) = q.card :=
    hcard.trans (TauCeti.PrimePower.card_def q).symm
  have hm : ChevalleyExceptionalModel (TauCeti.CFSGIndex.lie ⟨.E7 q, hv⟩).Group .E7
      q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, ?_⟩
    by_cases hq2 : q.p = 2
    · obtain ⟨e⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_E7 q hv hq2
        (GaloisField q.p q.exponent) hqcard
      exact ⟨GaloisField q.p q.exponent, inferInstance, inferInstance, hcard, ⟨e.symm⟩⟩
    · obtain ⟨e⟩ := CFSG.TauCetiBridge.untwistedBridge_E7 q hv hq2
        (GaloisField q.p q.exponent) hqcard
      exact ⟨GaloisField q.p q.exponent, inferInstance, inferInstance, hcard, ⟨e.symm⟩⟩
  obtain ⟨L, hLfield, hLfin, hLcard, ⟨eL⟩⟩ :=
    nonempty_mulEquiv_adjointGroup .E7 hm.2
  let := hLfield
  let := hLfin
  have : Finite (adjointGroup Tag.E7 L) := Subtype.finite
  exact Or.inr (Or.inl (exists_fieldPart_of_mulEquiv (eK.trans eL)
    (exists_fieldPart_adjointGroup_E7 q.prime_p q.exponent_pos L hLcard hp hp2)))

theorem i713ClauseFree_lie_E8
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E8 q).Valid) :
    I713ClauseFree (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩) := by
  intro K _ _ _ _ ⟨eK⟩ p hp hp2
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Finite (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩).Group :=
    Finite.of_equiv K eK.toEquiv
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card q.p q.exponent q.exponent_pos.ne'
  have hqcard : Nat.card (GaloisField q.p q.exponent) = q.card :=
    hcard.trans (TauCeti.PrimePower.card_def q).symm
  have hm : ChevalleyExceptionalModel (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩).Group .E8
      q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, ?_⟩
    by_cases hq2 : q.p = 2
    · obtain ⟨e⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_E8 q hv hq2
        (GaloisField q.p q.exponent) hqcard
      exact ⟨GaloisField q.p q.exponent, inferInstance, inferInstance, hcard, ⟨e.symm⟩⟩
    · obtain ⟨e⟩ := CFSG.TauCetiBridge.untwistedBridge_E8 q hv hq2
        (GaloisField q.p q.exponent) hqcard
      exact ⟨GaloisField q.p q.exponent, inferInstance, inferInstance, hcard, ⟨e.symm⟩⟩
  obtain ⟨L, hLfield, hLfin, hLcard, ⟨eL⟩⟩ :=
    nonempty_mulEquiv_adjointGroup .E8 hm.2
  let := hLfield
  let := hLfin
  have : Finite (adjointGroup Tag.E8 L) := Subtype.finite
  exact Or.inr (Or.inl (exists_fieldPart_of_mulEquiv (eK.trans eL)
    (exists_fieldPart_adjointGroup_E8 q.prime_p q.exponent_pos L hLcard hp hp2)))

end E78

section Suzuki

open CFSG.Blueprint CFSG.LieType.Ree
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki

theorem i713ClauseFree_lie_twistedB2
    (m : ℕ) (hv : (TauCeti.LieTypeIndex.suzuki m).Valid) :
    I713ClauseFree (TauCeti.CFSGIndex.lie ⟨.suzuki m, hv⟩) := by
  intro K _ _ _ _ ⟨eK⟩ p hp _
  obtain ⟨-, a, ha, L, hLfield, hLfin, hf, hLcard, ⟨eL⟩⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index m hv
  let : Field L := hLfield
  let : Finite L := hLfin
  have hLcard' : Nat.card L = 2 ^ (2 * a + 1) := by rw [hLcard, hf]
  exact Or.inr (Or.inl (exists_fieldPart_of_mulEquiv (eK.trans eL)
    (exists_fieldPart_suzukiGroup ha hLcard' hp)))

end Suzuki

section Ree

open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.LieType.Ree

theorem i713ClauseFree_lie_twistedF4
    (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid) :
    I713ClauseFree (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩) := by
  intro K _ _ _ _ ⟨eK⟩ p hp _
  obtain ⟨X, hXfield, hXfin, hXchar, hm, hXcard, -, ⟨eL⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_reeGamma_equiv_cat hv
  let := hXfield
  let := hXfin
  let := hXchar
  have : Finite (CFSG.Blueprint.Chevalley.ModGL ReeTag.F4.tag X) :=
    CFSG.LieType.Chevalley.finite_modGL
  have : Finite (ReeTag.F4.reeGamma X m) := Subtype.finite
  exact Or.inr (Or.inl (exists_fieldPart_of_mulEquiv (eK.trans eL)
    (exists_fieldPart_reeF4 hm hXcard hp)))

end Ree

section Small

open CFSG.ComponentClassification.LiteratureLocal.SmallRee
open CFSG.LieType.Ree
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem i713ClauseFree_lie_twistedG2
    (a : ℕ) (hv : (TauCeti.LieTypeIndex.reeG2 a).Valid) :
    I713ClauseFree (TauCeti.CFSGIndex.lie ⟨.reeG2 a, hv⟩) := by
  intro K _ _ _ _ ⟨eK⟩ p hp _
  have hmodel : CFSG.Blueprint.ReeTitsModel
      (TauCeti.CFSGIndex.lie ⟨.reeG2 a, hv⟩).Group .twistedG2 3 (2 * a + 1) :=
    CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 a ⟨hv, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨b, L, hLfield, hLfin, hLchar, hb, hLcard, ⟨eL⟩⟩ :=
    CFSG.RankThree.Chevalley.exists_mulEquiv_reeGamma_G2_of_reeTitsModel hmodel
  let := hLfield
  let := hLfin
  let := hLchar
  have : Finite (ModGL ReeTag.G2.tag L) := finite_modGL
  have : Finite (ReeTag.G2.reeGamma L b) := Subtype.finite
  exact Or.inr (Or.inl (exists_fieldPart_of_mulEquiv (eK.trans eL)
    (exists_fieldPart_reeGamma hb hLcard hp)))

theorem i713ClauseFree_lie_Tits
    (hv : TauCeti.LieTypeIndex.tits.Valid) :
    I713ClauseFree (TauCeti.CFSGIndex.lie ⟨.tits, hv⟩) := by
  intro K _ _ _ _ ⟨e⟩ p hp hp2
  exact Or.inl (CFSG.AGLEmbedding.not_dvd_card_outer_tits hv e hp hp2)

end Small

theorem i713ClauseFree_lie_C (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.C r q).Valid) :
    I713ClauseFree (TauCeti.CFSGIndex.lie ⟨.C r q, hv⟩) := by
  intro K _ _ _ _ ⟨eK⟩ p hp hp2
  have hr : 3 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1 |>.1
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.card :=
    (GaloisField.card q.p q.exponent q.exponent_pos.ne').trans
      (TauCeti.PrimePower.card_def q).symm
  obtain ⟨eC⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_C_of_statedProj
    (r := r) hv (k := GaloisField q.p q.exponent) hcard
  have hfieldPart := exists_fieldPart_statedProj_sp (r := r) hr
    (GaloisField q.p q.exponent) (p := p) hp hp2
  exact Or.inr (Or.inl (exists_fieldPart_of_mulEquiv (eK.trans eC.symm) hfieldPart))

theorem i713ClauseFree_lie_B_even (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.B r q).Valid) (hq2 : q.p = 2) (hr3 : 3 ≤ r) :
    I713ClauseFree (TauCeti.CFSGIndex.lie ⟨.B r q, hv⟩) := by
  intro K _ _ _ _ ⟨eK⟩ p hp hp2
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.card :=
    (GaloisField.card q.p q.exponent q.exponent_pos.ne').trans
      (TauCeti.PrimePower.card_def q).symm
  obtain ⟨eB⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_B_of_statedProj
    (r := r) hv hq2 hr3 (k := GaloisField q.p q.exponent) hcard
  have hfieldPart := exists_fieldPart_statedProj_sp (r := r) hr3
    (GaloisField q.p q.exponent) (p := p) hp hp2
  exact Or.inr (Or.inl (exists_fieldPart_of_mulEquiv (eK.trans eB.symm) hfieldPart))

theorem i713ClauseFree_lie_B2 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.B 2 q).Valid) :
    I713ClauseFree (TauCeti.CFSGIndex.lie ⟨.B 2 q, hv⟩) := by
  intro K _ _ _ _ ⟨eK⟩ p hp hp2
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.card :=
    (GaloisField.card q.p q.exponent q.exponent_pos.ne').trans
      (TauCeti.PrimePower.card_def q).symm
  obtain ⟨eB⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_B2_of_statedProj
    hv (k := GaloisField q.p q.exponent) hcard
  have hfieldPart := exists_fieldPart_statedProj_sp_two
    (GaloisField q.p q.exponent) (p := p) hp hp2
  exact Or.inr (Or.inl (exists_fieldPart_of_mulEquiv (eK.trans eB.symm) hfieldPart))

end CFSG.LieType.OutStructure
