module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I106TE27Lift
public import CFSG.Sporadic.Bridge.J3Surj
public import Certificates.Certificate810202
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84.E27

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge
open CFSG.Sporadic.Bridge.TwoGen CFSG.Sporadic.Bridge.TwoGen.Native
open CFSG.Sporadic.J3 (a b J rep_a rep_b faithful j3Facts)
open CFSG.Sporadic.J3.Native (j3Data)

section Words

variable {G : Type*} [Group G] (x : ℕ → G)

theorem wordProd_append (u v : List (ℕ × Bool)) :
    wordProd x (u ++ v) = wordProd x u * wordProd x v := by
  simp only [wordProd, List.map_append, List.prod_append]

theorem wordProd_invW (w : List (ℕ × Bool)) :
    wordProd x (J3E27.invW w) = (wordProd x w)⁻¹ := by
  induction w with
  | nil => simp [wordProd, J3E27.invW]
  | cons l w ih =>
    have e : J3E27.invW (l :: w) = J3E27.invW w ++ [(l.1, !l.2)] := by
      simp [J3E27.invW]
    rw [e, wordProd_append, ih]
    obtain ⟨i, s⟩ := l
    cases s <;> simp [wordProd]

end Words

theorem e27Lifts_J :
    E27Lifts (J j3Data) := by
  obtain ⟨h0, h1, h2, c01, c02, c12, hSW2, hSX3, hTW1, hTW2, hTX3, hinj⟩ :=
    Certificates.certificate810202 _ _ _ _ _ rfl rfl rfl rfl rfl
  have hSW1 : wordProd (img2 (a j3Data) (b j3Data)) J3E27.wordS *
      wordProd (img2 (a j3Data) (b j3Data)) J3E27.wordW1 *
      (wordProd (img2 (a j3Data) (b j3Data)) J3E27.wordS)⁻¹ =
      wordProd (img2 (a j3Data) (b j3Data)) J3E27.wordW2 := by
    rw [J3E27.wordW2, wordProd_append, wordProd_append, wordProd_invW]
  exact e27Lifts_of_pairs c01 c02 c12 h0 h1 h2 hinj ⟨_, hTW1⟩ ⟨_, hTW2⟩ ⟨_, hSX3⟩
    (Or.inr (Or.inr ⟨_, hSW1, hSW2⟩)) (Or.inl ⟨_, hTW1, hTX3⟩) (Or.inl ⟨_, hTW2, hTX3⟩)

theorem e27Lifts_j3 :
    E27Lifts (TauCeti.CFSGIndex.sporadic .J3).Group := by
  have h : E27Lifts CFSG.Blueprint.NativeSporadic.J3 :=
    E27Lifts.of_mulEquiv (G := J j3Data) (G' := CFSG.Blueprint.NativeSporadic.J3)
      CFSG.Sporadic.Bridge.J3.nativeEquiv.symm e27Lifts_J
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  exact E27Lifts.of_mulEquiv (G := CFSG.Blueprint.NativeSporadic.J3)
    (G' := TauCeti.SporadicName.J3.Group) e h

end CFSG.LocalAnalysis.GLTheoremA.S8.L84.E27
