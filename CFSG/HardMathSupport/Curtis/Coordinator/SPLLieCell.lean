module

public import CFSG.HardMathSupport.Curtis.Coordinator.SPLTorusFamilies
public import CFSG.HardMathSupport.Curtis.Coordinator.SPLLieInner
public import CFSG.HardMathSupport.Curtis.Coordinator.SPLLieOutRank

public section

open CFSG.AGLEmbedding CFSG.ComponentClassification.OuterAutomorphisms

namespace CFSG.HardMathSupport.Curtis.Coordinator

@[expose] def SPLLieInnerCell : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex), IsClassicalOrG2Index d.1 →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ∀ (p r : ℕ), p.Prime → p ≠ 2 → r.Prime → r ∣ p ^ 2 + 1 → ¬ r ∣ p ^ 2 - 1 →
    ∀ (Ē : Subgroup S) (ζ γ : MulAut S), CFSG.Open.IsElemAbelian p Ē → Nat.card Ē = p ^ 4 →
      ζ ^ p = 1 → (∀ x ∈ Ē, ζ x = x) → Group.IsSolvable ↥(autFix ζ) →
      (∃ k : ℕ, γ ^ r ^ k = 1) → (∀ x ∈ Ē, γ x ∈ Ē) → γ * ζ = ζ * γ → (∃ x ∈ Ē, γ x ≠ x) → False

theorem autConj_mul_conj_mul_inv {S : Type*} [Group S] (ζ : MulAut S) (x : S) :
    ζ * MulAut.conj x * ζ⁻¹ = MulAut.conj (ζ x) := by
  ext y
  simp [MulAut.conj_apply]

section Cell


theorem kFactSPLBlockTorusCaseBLie_of_cell (hcell : SPLLieInnerCell) :
    KFactSPLBlockTorusCaseBLie := by
  intro Y _ _ L p r hL hp hp2 hr hdvd hndvd ⟨d, hd, ⟨e⟩⟩ _ _ u c T X hu hup hunC hsolv hTN hTC hXT
    hTX hcomm hpow hidx hcN hcC hcr hcT hnt
  have : Group.IsPerfect L := hL.1.1
  obtain ⟨E, ζ, γ, hdata⟩ := exists_splAutData L p r hp hp2 hr hdvd hndvd u c T X hu hup hsolv hTN
    hTC hTX hcomm hpow hidx hcN hcC hcr hcT hnt
  have hs : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hL.1.2.1
  have hnab := hL.1.2.2
  have hZ : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.center_eq_bot_of_simple hnab
  have hinj := conj_injective_of_center_eq_bot' hZ
  have hEinn : E ≤ CFSG.AGLEmbedding.ParabAutIrr.inn (↥L ⧸ Subgroup.center ↥L) :=
    hdata.le_inn (outPTwoGen_of_lie d hd e hp hp2)
  set S := ↥L ⧸ Subgroup.center ↥L
  let Eb : Subgroup S := E.comap (MulAut.conj : S →* MulAut S)
  have hmem : ∀ x : S, x ∈ Eb ↔ MulAut.conj x ∈ E := fun x => Iff.rfl
  have hmapEb : Eb.map (MulAut.conj : S →* MulAut S) = E := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.2 hEinn
  refine hcell S d hd ⟨e⟩ p r hp hp2 hr hdvd hndvd Eb ζ γ ?_ ?_ hdata.zeta_pow ?_ hdata.solv
    hdata.gamma_pow ?_ hdata.gamma_zeta ?_
  · refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply hinj
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact hdata.comm_eq ((hmem _).1 x.2) ((hmem _).1 y.2)
    · apply hinj
      rw [map_pow, map_one]
      exact hdata.elem.2 _ ((hmem x).1 hx)
  · have h1 := Nat.card_congr (Subgroup.equivMapOfInjective Eb _ hinj).toEquiv
    rw [hmapEb] at h1
    rw [h1]
    exact hdata.card
  · intro x hx
    apply hinj
    rw [← autConj_mul_conj_mul_inv, mul_inv_eq_iff_eq_mul]
    exact hdata.zeta_comm _ ((hmem x).1 hx)
  · intro x hx
    rw [hmem, ← autConj_mul_conj_mul_inv]
    exact hdata.gamma_norm _ ((hmem x).1 hx)
  · obtain ⟨a, ha, hne⟩ := hdata.gamma_act
    obtain ⟨x, hx⟩ := hEinn ha
    refine ⟨x, (hmem x).2 (hx ▸ ha), fun hxx => hne ?_⟩
    rw [← hx, autConj_mul_conj_mul_inv, hxx]

end Cell

end CFSG.HardMathSupport.Curtis.Coordinator
