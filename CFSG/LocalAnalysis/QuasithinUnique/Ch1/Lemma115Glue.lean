module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Quotient
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Transport

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def SimpleInspection (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (β : K ≃* K), InvDatum K β → Subgroup.center K = ⊥ →
    P K → InvCases K β

@[expose] def IsCoverSporadicName (s : TauCeti.SporadicName) : Prop :=
  s = .M12 ∨ s = .M22 ∨ s = .J2 ∨ s = .HS ∨ s = .Ru

@[expose] def InnerCover (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (α : L ≃* L), InvDatum L α → IsInnerAut α →
    Subgroup.center L ≠ ⊥ → P (L ⧸ Subgroup.center L) →
    IsL34OrG24 (L ⧸ Subgroup.center L) ∨
      ∃ s : TauCeti.SporadicName, IsCoverSporadicName s ∧
        Nonempty ((L ⧸ Subgroup.center L) ≃* NativeSporadic.Carrier s)

@[expose] def AltOuterCover : Prop :=
  ∀ (L : Type) [Group L] [Finite L] (α : L ≃* L), InvDatum L α →
    ((∃ (φ : (L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin 6)) (σ : Equiv.Perm (Fin 6)),
        σ.IsSwap ∧ PermAction α φ σ) ∨
      (∃ (φ : (L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin 7)) (σ : Equiv.Perm (Fin 7)),
        σ.cycleType = {2, 2, 2} ∧ PermAction α φ σ)) →
    Nat.card (Subgroup.center L) = 1 ∨ Nat.card (Subgroup.center L) = 3

section Glue

variable {L : Type} [Group L] [Finite L] {α : L ≃* L}

@[expose] noncomputable def mulEquivQuotientOfCenterEqBot (h : Subgroup.center L = ⊥) :
    L ≃* L ⧸ Subgroup.center L :=
  QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq h.symm)

omit [Finite L] in
theorem mulEquivQuotientOfCenterEqBot_apply (h : Subgroup.center L = ⊥) (x : L) :
    mulEquivQuotientOfCenterEqBot h x = QuotientGroup.mk x := rfl

theorem InvDatum.pCore_eq_center_of_inner (h : InvDatum L α) (hi : IsInnerAut α) :
    CFSG.pCore 2 L = Subgroup.center L :=
  pCore_eq_center_of_isPGroup_center h.quasisimple (h.isPGroup_center_of_inner hi)

theorem InvDatum.invCases_of_innerCover (h : InvDatum L α) (hi : IsInnerAut α)
    (hz : Subgroup.center L ≠ ⊥)
    (hc : IsL34OrG24 (L ⧸ Subgroup.center L) ∨
      ∃ s : TauCeti.SporadicName, IsCoverSporadicName s ∧
        Nonempty ((L ⧸ Subgroup.center L) ≃* NativeSporadic.Carrier s)) :
    InvCases L α := by
  have hpc := h.pCore_eq_center_of_inner hi
  have e : (L ⧸ CFSG.pCore 2 L) ≃* (L ⧸ Subgroup.center L) :=
    QuotientGroup.quotientMulEquivOfEq hpc
  rcases hc with hc | ⟨s, hs, ⟨e'⟩⟩
  · exact Or.inr (Or.inl ⟨hz, hpc.symm, IsL34OrG24.of_mulEquiv e hc, hi⟩)
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨s, ?_, ⟨e.trans e'⟩⟩,
      h.isTwoCentralInnerAut_of_inner hi⟩))))
    rcases hs with rfl | rfl | rfl | rfl | rfl <;> simp [IsLemma115SporadicName]

end Glue

theorem invCases_of_inspections {P : ∀ (X : Type) [Group X], Prop} (hS : SimpleInspection P)
    (hI : InnerCover P) (hA : AltOuterCover) {L : Type} [Group L] [Finite L] {α : L ≃* L}
    (h : InvDatum L α) (hP : P (L ⧸ Subgroup.center L)) : InvCases L α := by
  have hKc : Subgroup.center (L ⧸ Subgroup.center L) = ⊥ :=
    center_quotient_eq_bot h.quasisimple
  have hK : InvCases (L ⧸ Subgroup.center L) (quotAut α) := hS _ (quotAut α) h.quotient hKc hP
  let ψ : (L ⧸ Subgroup.center L) ≃* (L ⧸ Subgroup.center L) ⧸
      Subgroup.center (L ⧸ Subgroup.center L) :=
    mulEquivQuotientOfCenterEqBot hKc
  have hψ : ∀ k, ψ k = QuotientGroup.mk k := fun k => rfl
  rcases hK with ⟨hs, hm, hβ⟩ | ⟨hzK, -⟩ | ⟨φ, σ, hZK, hσ, hp⟩ | ⟨φ, σ, hZK, hσ, hp⟩ |
    ⟨hm, hβ⟩ | ⟨⟨s, hs, ⟨e'⟩⟩, hβ⟩
  ·
    have hi : IsInnerAut α := h.isInnerAut_of_quotAut_inner hβ
    by_cases hz : Subgroup.center L = ⊥
    · let e := mulEquivQuotientOfCenterEqBot hz
      exact Or.inl ⟨e.isSimpleGroup_congr.mpr hs, Lemma115LieCharTwo.of_mulEquiv e hm, hi⟩
    · exact h.invCases_of_innerCover hi hz (hI L α h hi hz hP)
  · exact absurd hKc hzK
  ·
    have hperm : PermAction α (ψ.trans φ) σ := fun x => by
      have := hp (QuotientGroup.mk x)
      rw [quotAut_mk] at this
      simpa [hψ] using this
    have hcard : Nat.card (Subgroup.center L) = 1 ∨ Nat.card (Subgroup.center L) = 3 :=
      hA L α h (Or.inl ⟨ψ.trans φ, σ, hσ, hperm⟩)
    exact Or.inr (Or.inr (Or.inl ⟨ψ.trans φ, σ, hcard, hσ, hperm⟩))
  ·
    have hperm : PermAction α (ψ.trans φ) σ := fun x => by
      have := hp (QuotientGroup.mk x)
      rw [quotAut_mk] at this
      simpa [hψ] using this
    have hcard : Nat.card (Subgroup.center L) = 1 ∨ Nat.card (Subgroup.center L) = 3 :=
      hA L α h (Or.inr ⟨ψ.trans φ, σ, hσ, hperm⟩)
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ψ.trans φ, σ, hcard, hσ, hperm⟩)))
  ·
    have hi : IsInnerAut α := h.isInnerAut_of_quotAut_inner hβ
    by_cases hz : Subgroup.center L = ⊥
    · let e := mulEquivQuotientOfCenterEqBot hz
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Lemma115ModelE.of_mulEquiv e hm, hi⟩))))
    · exact h.invCases_of_innerCover hi hz (hI L α h hi hz hP)
  ·
    have hi : IsInnerAut α := h.isInnerAut_of_quotAut_inner (by
      obtain ⟨l, hl, -⟩ := hβ
      exact ⟨l, hl⟩)
    have hpc := h.pCore_eq_center_of_inner hi
    have hpcK : CFSG.pCore 2 (L ⧸ Subgroup.center L) = ⊥ := by
      rw [pCore_eq_center_of_isPGroup_center (isQuasisimple_quotient h.quasisimple)
        (by rw [hKc]; exact IsPGroup.of_bot), hKc]
    let eK : (L ⧸ CFSG.pCore 2 L) ≃* (L ⧸ Subgroup.center L) :=
      QuotientGroup.quotientMulEquivOfEq hpc
    let eK' : (L ⧸ Subgroup.center L) ≃* (L ⧸ Subgroup.center L) ⧸
        CFSG.pCore 2 (L ⧸ Subgroup.center L) :=
      (QuotientGroup.quotientBot.symm).trans (QuotientGroup.quotientMulEquivOfEq hpcK.symm)
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨s, hs, ⟨(eK.trans eK').trans e'⟩⟩,
      h.isTwoCentralInnerAut_of_inner hi⟩))))

end CFSG.QuasithinUnique.Ch1
