module

public import CFSG.HardMathSupport.Lang.E6Descent.LiftCentral
public import CFSG.HardMathSupport.Lang.E6Descent.CenterE6
public import CFSG.HardMathSupport.Lang.E6Descent.SylowX
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanFixedThreeReduce

public section

namespace CFSG.HardMathSupport.Lang.E6Descent

open TauCeti CFSG.Open CFSG.AGLEmbedding.FixedThree

theorem rank_transport {A B : Type} [Group A] [Group B] (e : A ≃* B) {E : Subgroup B}
    (hE : IsElemAbelian 3 E) (h27 : 27 ≤ Nat.card E) :
    ∃ Eb : Subgroup A, IsElemAbelian 3 Eb ∧ 27 ≤ Nat.card Eb := by
  have := hE.1
  refine ⟨E.map e.symm.toMonoidHom, ⟨inferInstance, ?_⟩, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    show e.symm y ^ 3 = 1
    rw [← map_pow, hE.2 y hy, map_one]
  · rwa [Subgroup.card_map_of_injective e.symm.injective]

theorem fixedThreeE6_of_inputs (hB : RankBoundTStar)
    (hGA : CFSG.Open.GriessAllModelsStatement) (hE6 : ∀ (q : PrimePower) (hv : (LieTypeIndex.E6
        q).Valid), 3 ∣ q.card - 1 → (∃ E : Subgroup (CFSGIndex.lie ⟨.E6 q, hv⟩).Group, IsElemAbelian
        3 E ∧ 27 ≤ Nat.card E) ∧ 3 ^ 4 ∣ Nat.card (CFSGIndex.lie ⟨.E6 q, hv⟩).Group)
    (hTw : ∀ (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid), 3 ∣ q.card + 1 → (∃ E :
        Subgroup (CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group, IsElemAbelian 3 E ∧ 27 ≤ Nat.card E) ∧ 3
        ^ 4 ∣ Nat.card (CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group) : FixedThreeE6 := by
  intro X _ _ L hL hZ hcen hfam u hu3 huN hout
  have hZ3 : Nat.card (Subgroup.center ↥L) = 3 := card_center_eq_three_E6 hGA hL hZ hcen hfam
  have hK : (∃ Eb : Subgroup (↥L ⧸ Subgroup.center ↥L), IsElemAbelian 3 Eb ∧ 27 ≤ Nat.card Eb) ∧
      3 ^ 4 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
    rcases hfam with ⟨q, hv, ⟨e⟩, h3q⟩ | ⟨q, hv, ⟨e⟩, h3q⟩
    · obtain ⟨⟨E, hEel, hE27⟩, hord⟩ := hE6 q hv h3q
      exact ⟨rank_transport e hEel hE27, by rwa [Nat.card_congr e.toEquiv]⟩
    · obtain ⟨⟨E, hEel, hE27⟩, hord⟩ := hTw q hv h3q
      exact ⟨rank_transport e hEel hE27, by rwa [Nat.card_congr e.toEquiv]⟩
  obtain ⟨⟨Eb, hEbel, hEb27⟩, hord⟩ := hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Tb, hTb⟩ := Sylow.exists_subgroup_card_pow_prime 3 hord
  have hTbp : IsPGroup 3 Tb := IsPGroup.of_card hTb
  have hEbp : IsPGroup 3 Eb := fun g => ⟨1, Subtype.ext (by simpa using hEbel.2 g g.2)⟩
  have hhu : u ∉ L := fun hu => by
    obtain ⟨l, hl, hne⟩ := hout u hu
    exact hne rfl
  have hZp : IsPGroup 3 (centerX L) :=
    hZ.of_equiv (Subgroup.equivMapOfInjective _ L.subtype L.subtype_injective)
  have hZc : Nat.card (centerX L) ≤ 3 := by rw [card_centerX, hZ3]
  have hcard : Nat.card (centerX L) = 3 := by rw [card_centerX, hZ3]
  have hmain := exists_noncentral_fixed_of_sylow hB (L := L) (Z := centerX L)
    (F₀ := liftToX L Eb) (T₀ := liftToX L Tb) centerX_le
    (fun z hz l hl => (mem_centerX.1 hz).2 l hl)
    (fun y hy hc => mem_centerX.2 ⟨hy, hc⟩) hZp hZc hu3 huN hhu
    (liftToX_le Eb) (centerX_le_liftToX Eb) (isPGroup_liftToX hZ hEbp)
    (liftToX_comm (fun a ha b hb => by
      have := hEbel.1
      exact setLike_mul_comm ha hb)) (liftToX_exp hEbel.2)
    (by rw [card_liftToX, card_centerX]; nlinarith)
    (liftToX_le Tb) (isPGroup_liftToX hZ hTbp)
    (by rw [card_liftToX, card_centerX, hTb]; nlinarith)
  obtain ⟨y, hyL, hyp, hyu, hyZ⟩ := hmain
  refine Or.inl ⟨y, hyL, hyp, hyu, ?_⟩
  by_contra hall
  push Not at hall
  exact hyZ (mem_centerX.2 ⟨hyL, hall⟩)

end CFSG.HardMathSupport.Lang.E6Descent
