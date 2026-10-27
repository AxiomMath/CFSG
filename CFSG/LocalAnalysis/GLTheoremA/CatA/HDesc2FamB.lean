module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Res

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint TauCeti CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

@[expose] def OutAbelianAt (d : ValidLieTypeIndex) : Prop :=
  commutator (MulAut (CFSGIndex.lie d).Group) ≤ inner (CFSGIndex.lie d).Group

theorem fam_linear {S : Type} [Group S] (h : catalogIs S fLinear) :
    ∃ (n : ℕ) (q : PrimePower) (hv : (LieTypeIndex.A n q).Valid), q.p = 2 ∧ ¬ (n = 1 ∧ q.card = 8) ∧
      Nonempty (S ≃* (CFSGIndex.lie ⟨.A n q, hv⟩).Group) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie dd =>
    obtain ⟨d, hv⟩ := dd
    cases d with
    | A n q => exact ⟨n, q, hv, hi.1, hi.2, ⟨e⟩⟩
    | _ => exact hi.elim

theorem fam_unitary {S : Type} [Group S] (h : catalogIs S fUnitary) :
    ∃ (n : ℕ) (q : PrimePower) (hv : (LieTypeIndex.twistedA n q).Valid), q.p = 2 ∧
      ¬ (n = 2 ∧ q.card = 8) ∧ ¬ (n = 3 ∧ q.card = 2) ∧ ¬ (n = 4 ∧ q.card = 2) ∧
      Nonempty (S ≃* (CFSGIndex.lie ⟨.twistedA n q, hv⟩).Group) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie dd =>
    obtain ⟨d, hv⟩ := dd
    cases d with
    | twistedA n q => exact ⟨n, q, hv, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2, ⟨e⟩⟩
    | _ => exact hi.elim

theorem fam_symplectic {S : Type} [Group S] (h : catalogIs S fSymplectic) :
    ∃ (n : ℕ) (q : PrimePower) (hv : (LieTypeIndex.B n q).Valid), q.p = 2 ∧ ¬ (n = 3 ∧ q.card = 2) ∧
      Nonempty (S ≃* (CFSGIndex.lie ⟨.B n q, hv⟩).Group) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie dd =>
    obtain ⟨d, hv⟩ := dd
    cases d with
    | B n q => exact ⟨n, q, hv, hi.1, hi.2, ⟨e⟩⟩
    | _ => exact hi.elim

theorem fam_g2 {S : Type} [Group S] (h : catalogIs S fG2) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid), q.p = 2 ∧
      Nonempty (S ≃* (CFSGIndex.lie ⟨.G2 q, hv⟩).Group) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie dd =>
    obtain ⟨d, hv⟩ := dd
    cases d with
    | G2 q => exact ⟨q, hv, hi, ⟨e⟩⟩
    | _ => exact hi.elim

theorem fam_reeTits {S : Type} [Group S] (h : catalogIs S fReeTits) :
    ∃ (m : ℕ) (hv : (LieTypeIndex.reeF4 m).Valid),
      Nonempty (S ≃* (CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie dd =>
    obtain ⟨d, hv⟩ := dd
    cases d with
    | reeF4 m => exact ⟨m, hv, ⟨e⟩⟩
    | _ => exact hi.elim

@[expose] def Td4Ob (p : ℕ) (Q : CFSGIndex → Prop) : Prop :=
  p.Prime → p ≠ 2 → ∀ (Y : Type) [Group Y] [Finite Y] (K B : Subgroup Y), KHyp p K B →
    catalogIs (↥K ⧸ Subgroup.center ↥K) Q →
    Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set Y)) < p ^ 3 → TD4Exc p K B →
    KConcl p K B ∨ ∃ D J : Subgroup Y, DescData p K B D J

theorem htd_of_alt (hT : TD4Alt) {Q : CFSGIndex → Prop} {p : ℕ} : Td4Ob p Q :=
  fun hp hp2 Y _ _ K B h _ hcB hT' => hT p hp hp2 Y K B h hcB hT'

theorem char_A {n : ℕ} {q : PrimePower} (hq : q.p = 2) : (LieTypeIndex.A n q).characteristic = 2 := by
  simpa using hq

theorem h5_of_three {d : ValidLieTypeIndex} : ¬ ((3 : ℕ) = 5 ∧ d.1 = .suzuki 2) := by
  rintro ⟨h, -⟩
  omega

theorem htits_of_three {d : ValidLieTypeIndex} : ¬ ((3 : ℕ) = 5 ∧ d.1 = .tits) := by
  rintro ⟨h, -⟩
  omega

end CFSG.LocalAnalysis.GLTheoremA.HDesc
