module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8Transfer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def KD264F8FamLn (e : TauCeti.LieTypeIndex) : Prop :=
  ∃ n : ℕ, ∃ q : TauCeti.PrimePower, e = .A n q ∧ 3 ≤ n ∧ n ≤ 6 ∧ q.card = 8

@[expose] def KD264F8FamSp (e : TauCeti.LieTypeIndex) : Prop :=
  (∃ q : TauCeti.PrimePower, e = .B 3 q ∧ q.card = 8) ∨
    (∃ q : TauCeti.PrimePower, e = .C 3 q ∧ q.card = 8)

@[expose] def KD264F8FamOm (e : TauCeti.LieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, e = .twistedD 4 q ∧ q.card = 8

@[expose] def KD264F8Hyp (S : Type) [Group S] [Finite S] (A : Subgroup (MulAut S)) : Prop :=
  IsElemAbelian 3 A ∧ 3 ≤ CFSG.Open.pRank 3 A ∧ CFSG.Open.pRank 3 A ≤ 4 ∧
    CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ CFSG.Open.pRank 3 A ∧
    (∀ a ∈ A, a ∉ (MulAut.conj : S →* MulAut S).range →
        ∀ E : Subgroup S, E ≤ fixSubgroup a → IsElemAbelian 3 E →
          CFSG.Open.pRank 3 E + 1 ≤ CFSG.Open.pRank 3 A) ∧
    ¬ A ≤ innAutDerived S

@[expose] def KD264F8Datum (S : Type) [Group S] (A : Subgroup (MulAut S)) : Prop :=
  ∃ b ∈ A, ∃ c ∈ A, b ∉ innAutDerived S ∧ c ∈ innAutDerived S ∧ c ≠ 1 ∧
    ∃ H : Subgroup S, H ≤ fixSubgroup b ∧ H ≤ fixSubgroup c ∧
      IsSubnormal H (⨅ f ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers c, fixSubgroup f) ∧
      CFSG.Open.IsQuasisimple ↥H ∧ 3 ∣ Nat.card (↥H ⧸ Subgroup.center ↥H)

@[expose] def KD264F8Cls : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group],
    ¬ IsChevSimple 3 (TauCeti.CFSGIndex.lie d).Group → ¬ k2Lie 3 d.1 → ¬ k3Lie d.1 →
    overEight d.1 →
    ¬ (∃ q : TauCeti.PrimePower, d.1 = .trialityD4 q) →
    ¬ (∃ n : ℕ, ∃ q : TauCeti.PrimePower, d.1 = .twistedA n q ∧ 3 ∣ n + 1) →
    ¬ (∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q) →
    ∀ A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group),
      KD264F8Hyp (TauCeti.CFSGIndex.lie d).Group A →
      KD264F8FamLn d.1 ∨ KD264F8FamSp d.1 ∨ KD264F8FamOm d.1

@[expose] def KD264F8Kernel (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group],
    ¬ IsChevSimple 3 (TauCeti.CFSGIndex.lie d).Group → ¬ k2Lie 3 d.1 → ¬ k3Lie d.1 →
    overEight d.1 → P d.1 →
    ∀ A : Subgroup (MulAut (TauCeti.CFSGIndex.lie d).Group),
      KD264F8Hyp (TauCeti.CFSGIndex.lie d).Group A →
      KD264F8Datum (TauCeti.CFSGIndex.lie d).Group A

@[expose] def KD264F8KerLn : Prop := KD264F8Kernel KD264F8FamLn

@[expose] def KD264F8KerSp : Prop := KD264F8Kernel KD264F8FamSp

@[expose] def KD264F8KerOm : Prop := KD264F8Kernel KD264F8FamOm

theorem kd264F8_good_of_datum {S : Type} [Group S] [Finite S] {A : Subgroup (MulAut S)}
    (hA : IsElemAbelian 3 A) (h : KD264F8Datum S A) : ∃ F ≤ A, Nat.card F = 9 ∧ IsGood 3 F := by
  obtain ⟨b, hb, c, hc, hbI, hcI, hc1, H, hHb, hHc, hsub, hq, hdvd⟩ := h
  exact kd264F8_exists_good hA hb hc hc1 (fun hbc => hbI ((Subgroup.zpowers_le.2 hcI) hbc))
    hHb hHc hsub hq hdvd

theorem kd264F8Row_of_pieces (hCls : KD264F8Cls) (hLn : KD264F8KerLn) (hSp : KD264F8KerSp)
    (hOm : KD264F8KerOm) : KD264F8Row := by
  intro d _ hk1 hk2 hk3 hov hTri hTwA hTwE6 A hA h3 h4 hm3 hout hnot
  have hyp : KD264F8Hyp (TauCeti.CFSGIndex.lie d).Group A := ⟨hA, h3, h4, hm3, hout, hnot⟩
  rcases hCls d hk1 hk2 hk3 hov hTri hTwA hTwE6 A hyp with h | h | h
  · exact kd264F8_good_of_datum hA (hLn d hk1 hk2 hk3 hov h A hyp)
  · exact kd264F8_good_of_datum hA (hSp d hk1 hk2 hk3 hov h A hyp)
  · exact kd264F8_good_of_datum hA (hOm d hk1 hk2 hk3 hov h A hyp)

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
