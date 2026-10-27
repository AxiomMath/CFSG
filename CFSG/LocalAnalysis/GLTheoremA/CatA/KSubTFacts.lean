module

public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsGamma

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KSubT

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S10

theorem catalogIs_mono {S : Type} [Group S] {Q Q' : TauCeti.CFSGIndex → Prop}
    (hQ : ∀ i, Q i → Q' i) (h : catalogIs S Q) : catalogIs S Q' := by
  obtain ⟨i, hi, e⟩ := h
  exact ⟨i, hQ i hi, e⟩

theorem catalogIs_or {S : Type} [Group S] {Q Q' : TauCeti.CFSGIndex → Prop}
    (h : catalogIs S (fun i => Q i ∨ Q' i)) : catalogIs S Q ∨ catalogIs S Q' := by
  obtain ⟨i, hi, e⟩ := h
  rcases hi with hq | hq
  · exact Or.inl ⟨i, hq, e⟩
  · exact Or.inr ⟨i, hq, e⟩

theorem stdSub_of_u4 {i : TauCeti.CFSGIndex} (h : S9.isU4two i) : S10.isStdSubList i := by
  unfold S10.isStdSubList
  exact Or.inl h

theorem stdSub_of_u5 {i : TauCeti.CFSGIndex} (h : S9.isU5two i) : S10.isStdSubList i := by
  unfold S10.isStdSubList
  exact Or.inr (Or.inl h)

theorem stdSub_of_sp6 {i : TauCeti.CFSGIndex} (h : S9.isSp6two i) : S10.isStdSubList i := by
  unfold S10.isStdSubList
  exact Or.inr (Or.inr (Or.inl h))

theorem stdSub_of_a6 {i : TauCeti.CFSGIndex} (h : S10.isA6 i) : S10.isStdSubList i := by
  unfold S10.isStdSubList
  exact Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem stdSub_of_l2 {i : TauCeti.CFSGIndex} (h : S10.isL2eight i) : S10.isStdSubList i := by
  unfold S10.isStdSubList
  exact Or.inr (Or.inr (Or.inr (Or.inr h)))

@[expose] def CompFact (T Q : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (J B : Subgroup H) (d : H),
    CFSG.Open.IsQuasisimple ↥J → catalogIs (PSimple 3 J) T → d ∈ B → InnDiagOn 3 B J →
    d ^ 3 = 1 → d ∉ Subgroup.centralizer (J : Set H) →
    ∀ K : Subgroup H, CFSG.Open.IsComponentOf K (J ⊓ Subgroup.centralizer ({d} : Set H)) →
      catalogIs (↥K ⧸ Subgroup.center ↥K) Q

@[expose] def CompFactSp8 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (J B : Subgroup H) (d : H),
    CFSG.Open.IsQuasisimple ↥J → catalogIs (PSimple 3 J) S9.isSp8two → d ∈ B →
    InnDiagOn 3 B J → d ^ 3 = 1 → d ∉ Subgroup.centralizer (J : Set H) →
    ∀ K : Subgroup H, CFSG.Open.IsComponentOf K (J ⊓ Subgroup.centralizer ({d} : Set H)) →
      catalogIs (↥K ⧸ Subgroup.center ↥K) (fun i => S9.isU4two i ∨ S9.isSp6two i ∨ S10.isA6 i) ∧
        (catalogIs (↥K ⧸ Subgroup.center ↥K) S10.isA6 → catalogIs ↥K S10.isA6)

@[expose] def ListDistinct : Prop :=
  (∀ (S : Type) [Group S] [Finite S], catalogIs S S9.isU4two → catalogIs S S10.isA6 → False) ∧
  (∀ (S : Type) [Group S] [Finite S], catalogIs S S9.isU5two → catalogIs S S10.isA6 → False) ∧
  (∀ (S : Type) [Group S] [Finite S], catalogIs S S10.isA6 → catalogIs S S10.isL2eight → False) ∧
  (∀ (S : Type) [Group S] [Finite S], catalogIs S S9.isU4two → catalogIs S S10.isL2eight → False) ∧
  (∀ (S : Type) [Group S] [Finite S], catalogIs S S9.isSp6two → catalogIs S S10.isL2eight → False)

end CFSG.LocalAnalysis.GLTheoremA.KSubT
