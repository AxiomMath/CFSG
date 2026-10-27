module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDescPlan
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.CoverToCatalog

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA TauCeti

@[expose] def LvData (p : ℕ) (S : Type) [Group S] : Prop :=
  IsChevSimple p S ∨ catalogIs S (k2 p)

theorem lvData_of_level_ne_four {p : ℕ} (hK3 : K3NotChev2At) {Y : Type} [Group Y] [Finite Y]
    {K B : Subgroup Y} (h : KHyp p K B) (hlev : fullCoverLevel p ↥K ≠ 4) :
    LvData p (↥K ⧸ Subgroup.center ↥K) := by
  by_contra hn
  apply hlev
  have h1 : ¬ K1Cover p ↥K := fun hk => hn (Or.inl hk.2)
  have h2 : ¬ K2Cover p ↥K := fun hk => hn (Or.inr (k2Cover_imp_catalogIs p hk))
  have h3 : ¬ K3Cover p ↥K := fun hk => hK3 p ↥K hk h.chev
  unfold fullCoverLevel
  rw [if_neg h1, if_neg h2, if_neg h3]

@[expose] def SolvesAt (p : ℕ) (d : ValidLieTypeIndex) : Prop :=
  p.Prime → p ≠ 2 → ∀ (Y : Type) [Group Y] [Finite Y] (K B : Subgroup Y), KHyp p K B →
    Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (CFSGIndex.lie d).Group) →
      Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) < p ^ 3 →
        KConcl p K B ∨ ∃ D J : Subgroup Y, DescData p K B D J

theorem kDescFamRes_of_solves {p : ℕ} {Q : CFSGIndex → Prop} (hK3 : K3NotChev2At)
    (hlv : p.Prime → p ≠ 2 → ∀ (S : Type) [Group S] [Finite S], catalogIs S Q → LvData p S →
      ∃ d : ValidLieTypeIndex, Nonempty (S ≃* (CFSGIndex.lie d).Group) ∧ SolvesAt p d)
    (htd : p.Prime → p ≠ 2 → ∀ (Y : Type) [Group Y] [Finite Y] (K B : Subgroup Y), KHyp p K B →
      catalogIs (↥K ⧸ Subgroup.center ↥K) Q →
      Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) < p ^ 3 → TD4Exc p K B →
      KConcl p K B ∨ ∃ D J : Subgroup Y, DescData p K B D J) :
    KDescFamRes p Q := by
  intro hp hp2 Y _ _ K B h hc hcB hor
  rcases hor with hlev | hT
  · obtain ⟨d, he, hd⟩ := hlv hp hp2 (↥K ⧸ Subgroup.center ↥K) hc
      (lvData_of_level_ne_four hK3 h hlev)
    exact hd hp hp2 Y K B h he hcB
  · exact htd hp hp2 Y K B h hc hcB hT

theorem kDescFamRes_of_noLvData {p : ℕ} {Q : CFSGIndex → Prop} (hK3 : K3NotChev2At)
    (hlv : p.Prime → p ≠ 2 → ∀ (S : Type) [Group S] [Finite S], catalogIs S Q → ¬ LvData p S)
    (hno : ∀ (S : Type) [Group S], catalogIs S Q → ¬ catalogIs S (onLie isTrialityD4Big)) :
    KDescFamRes p Q := by
  refine kDescFamRes_of_solves hK3 (fun hp hp2 S _ _ hS hL => absurd hL (hlv hp hp2 S hS)) ?_
  intro hp hp2 Y _ _ K B _ hc _ hT
  exact absurd hT.2.2.2.1 (hno _ hc)

end CFSG.LocalAnalysis.GLTheoremA.HDesc
