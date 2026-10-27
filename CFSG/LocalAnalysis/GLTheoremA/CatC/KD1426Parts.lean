module

public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.CoverToCatalog

public section

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremA

@[expose] def isAlt1426 : TauCeti.CFSGIndex → Prop
  | .alternating n _ => n = 7 ∨ n = 10
  | _ => False

@[expose] def isSpor1426 : TauCeti.CFSGIndex → Prop
  | .sporadic s => s = .M12 ∨ s = .M22
  | _ => False

@[expose] def KD1426With (P : TauCeti.CFSGIndex → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K B : Subgroup Y), K.Normal → CFSG.Open.IsQuasisimple ↥K →
    catalogIs (↥K ⧸ Subgroup.center ↥K) P →
    GLAPPrimeCore 3 ↥K = ⊥ → fullCoverLevel 3 ↥K = 3 →
    IsElemAbelian 3 B → K ⊔ B = ⊤ → 3 ^ 4 ≤ Nat.card B → IsMaxRankIn 3 B ⊤ →
    B ⊓ Subgroup.centralizer (K : Set Y) ≠ ⊥ →
    (∀ E : Subgroup Y, E ≤ B → IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      GLAPLayer 3 (K ⊓ Subgroup.centralizer (E : Set Y)) = ⊥) →
    (catalogIs (↥K ⧸ Subgroup.center ↥K) isM12 → ∃ U : Subgroup Y, U ≤ K ∧ U ≠ ⊥ ∧
      IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set Y)) →
    Nat.card B = 3 ^ 4 ∧ ∃ A T : Subgroup Y, A ≤ B ∧ IsElemAbelian 3 A ∧ Nat.card A = 9 ∧
      GLAPComponent 3 (K ⊓ Subgroup.centralizer (A : Set Y))
        (GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y))) ∧
      catalogIs (PSimple 3 (GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y)))) k3NoA10 ∧
      (∀ b ∈ B, b ∈ Subgroup.centralizer
          ((GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y)) : Subgroup Y) : Set Y) ↔ b ∈ A) ∧
      T ≤ GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y)) ∧ IsElemAbelian 2 T ∧
      Nat.card T = 4 ∧ B ≤ Subgroup.normalizer (T : Set Y) ∧ ⁅B, T⁆ = T ∧
      GLAPPrimeCore 3 ↥(GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set Y))) = ⊥

@[expose] def KD1426Alt : Prop := KD1426With isAlt1426

@[expose] def KD1426Spor : Prop := KD1426With isSpor1426

@[expose] def KD1426Lie : Prop := KD1426With (onLie k3Lie)

theorem k3Cover_of_fullCoverLevel_three {Q : Type} [Group Q] (h : fullCoverLevel 3 Q = 3) :
    K3Cover 3 Q := by
  unfold fullCoverLevel at h
  split_ifs at h with h1 h2 h3
  · norm_num at h
  · norm_num at h
  · exact h3
  · norm_num at h

theorem kd1426Cat_of_parts (hA : KD1426Alt) (hS : KD1426Spor) (hL : KD1426Lie) : KD1426Cat := by
  intro Y _ _ K B hKn hq hcore hlev hB hKB hcard hmax hC hH hM
  obtain ⟨i, hi, ⟨eK⟩⟩ := k3Cover_imp_catalogIs (k3Cover_of_fullCoverLevel_three hlev)
  cases i with
  | cyclic p hp => exact hi.elim
  | alternating n h =>
    exact hA Y K B hKn hq ⟨.alternating n h, hi.2, ⟨eK⟩⟩ hcore hlev hB hKB hcard hmax hC hH hM
  | lie d =>
    exact hL Y K B hKn hq ⟨.lie d, hi.2, ⟨eK⟩⟩ hcore hlev hB hKB hcard hmax hC hH hM
  | sporadic s =>
    exact hS Y K B hKn hq ⟨.sporadic s, hi.2, ⟨eK⟩⟩ hcore hlev hB hKB hcard hmax hC hH hM

end CFSG.LocalAnalysis.GLTheoremA

end
