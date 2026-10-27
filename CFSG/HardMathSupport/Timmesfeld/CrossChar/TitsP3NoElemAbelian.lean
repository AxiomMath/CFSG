module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Assembly
public import CFSG.RankThree.PartTwo.Census.Carrier.TitsCert
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
public import CFSG.LieType.SeitzGeneration.ExcVacuousTits

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.RankThree.PartTwo.Census.Carrier CFSG.LieType.Ree CFSG.TauCetiBridge.ReeF4

theorem three_le_pRank_of_elemAbelian27 {H : Type*} [Group H] [Finite H] {E : Subgroup H}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hc : Nat.card E = 27) :
    3 ≤ CFSG.Assembly.pRank 3 (⊤ : Subgroup H) := by
  refine le_csSup ⟨Nat.card H, ?_⟩ ⟨E, le_top, ⟨hE.1, hE.2⟩, by rw [hc]; norm_num⟩
  rintro k ⟨F, -, -, hF⟩
  have h1 : 3 ^ k ≤ Nat.card H := hF ▸ Subgroup.card_le_card_group F
  exact (Nat.lt_pow_self (by norm_num : 1 < 3)).le.trans h1

section Tits


theorem nonempty_catTits_equiv_commutator (hv : TauCeti.LieTypeIndex.tits.Valid) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K ReeTag.F4.prime),
      Nat.card K = 2 ∧ Subgroup.center (commutator (reeFixed ReeTag.F4 K 0)) = ⊥ ∧
      Nonempty (Cat ⟨.tits, hv⟩ ≃* commutator (reeFixed ReeTag.F4 K 0)) := by
  have hfin : ∀ d : TauCeti.TitsLieIndex, Finite d.1.fixedField := fun _ => inferInstance
  have hchar : ∀ d : TauCeti.TitsLieIndex, CharP d.1.fixedField 2 := fun _ => inferInstance
  have := hfin TauCeti.TitsLieIndex.of
  have := hchar TauCeti.TitsLieIndex.of
  obtain ⟨e₁⟩ := nonempty_candidate_equiv_tits TauCeti.TitsLieIndex.of
  have hK := card_fixedField_tits TauCeti.TitsLieIndex.of
  have hZ : Subgroup.center (commutator (reeFixed ReeTag.F4
      TauCeti.TitsLieIndex.of.1.fixedField 0)) = ⊥ :=
    CFSG.LocalAnalysis.ComponentInitial.center_commutator_reeFixed_eq_bot hK
  let e₂ : commutator (reeFixed ReeTag.F4 TauCeti.TitsLieIndex.of.1.fixedField 0) ⧸
      Subgroup.center (commutator (reeFixed ReeTag.F4 TauCeti.TitsLieIndex.of.1.fixedField 0))
      ≃* commutator (reeFixed ReeTag.F4 TauCeti.TitsLieIndex.of.1.fixedField 0) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact ⟨TauCeti.TitsLieIndex.of.1.fixedField, inferInstance, inferInstance, inferInstance, hK,
    hZ, ⟨e₁.trans e₂⟩⟩

theorem no_elemAbelian27_cat_tits (hv : TauCeti.LieTypeIndex.tits.Valid)
    {E : Subgroup (Cat ⟨.tits, hv⟩)} (hE : CFSG.Open.IsElemAbelian 3 E) (hc : Nat.card E = 27) :
    False := by
  obtain ⟨K, _, _, _, hK, -, ⟨e⟩⟩ := nonempty_catTits_equiv_commutator hv
  let f : Cat ⟨.tits, hv⟩ →* reeFixed ReeTag.F4 K 0 :=
    ((commutator (reeFixed ReeTag.F4 K 0)).subtype).comp e.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have : Finite (reeFixed ReeTag.F4 K 0) := inferInstance
  have hcm : Nat.card (E.map f) = 27 := by
    rw [← Nat.card_congr (E.equivMapOfInjective f hf).toEquiv]
    exact hc
  have h3 := three_le_pRank_of_elemAbelian27 (E := E.map f) ⟨?_, ?_⟩ hcm
  · have := Tits.pRank_three_reeFixed hK
    omega
  · refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨_, ⟨a, ha, rfl⟩⟩ := a
    obtain ⟨_, ⟨b, hb, rfl⟩⟩ := b
    have := hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact Subtype.ext (by simpa [← map_mul] using congrArg (fun z => f z.1) this)
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE.2 a ha, map_one]

theorem titsNoElemAbelian27 :
    TitsNoElemAbelian27 := by
  intro hv D hD hcard
  obtain ⟨hT, hOut⟩ := CFSG.LieType.SeitzGeneration.card_cat_tits_outer hv
  have hcop : Nat.Coprime (Nat.card D)
      (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (Cat ⟨.tits, hv⟩))) := by
    rw [hcard, hOut]
    norm_num
  have hin := CFSG.LieType.SeitzGeneration.le_inner_of_coprime_card_outer hcop
  obtain ⟨K, _, _, _, hK, hZ, ⟨e⟩⟩ := nonempty_catTits_equiv_commutator hv
  have hinj : Function.Injective (MulAut.conj : Cat ⟨.tits, hv⟩ →* MulAut (Cat ⟨.tits, hv⟩)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    have hgc : g ∈ Subgroup.center (Cat ⟨.tits, hv⟩) := by
      rw [Subgroup.mem_center_iff]
      intro x
      have := congrArg (fun φ : MulAut (Cat ⟨.tits, hv⟩) => φ x) (MonoidHom.mem_ker.1 hg)
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    have hge : e g ∈ Subgroup.center (commutator (reeFixed ReeTag.F4 K 0)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hgc x]
    rw [hZ, Subgroup.mem_bot] at hge
    exact (Subgroup.mem_bot).2 (e.injective (hge.trans (map_one e).symm))
  have hEc : Nat.card (D.comap (MulAut.conj : Cat ⟨.tits, hv⟩ →* _)) = 27 := by
    rw [← hcard, Nat.card_congr
      ((D.comap (MulAut.conj : Cat ⟨.tits, hv⟩ →* _)).equivMapOfInjective _ hinj).toEquiv,
      Subgroup.map_comap_eq_self hin]
  refine no_elemAbelian27_cat_tits hv (E := D.comap (MulAut.conj : Cat ⟨.tits, hv⟩ →* _))
    ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩ hEc
  · refine Subtype.ext (hinj ?_)
    have := hD.1.is_comm.comm ⟨_, a.2⟩ ⟨_, b.2⟩
    simpa using congrArg Subtype.val this
  · apply hinj
    rw [map_pow, map_one]
    exact hD.2 _ hx

theorem crossCharFamAt_tits_three_proved :
    CrossCharFamAt .tits fun _ p => p = 3 :=
  crossCharFamAt_tits_three titsNoElemAbelian27

end Tits

end CFSG.HardMathSupport.Timmesfeld.CrossChar
