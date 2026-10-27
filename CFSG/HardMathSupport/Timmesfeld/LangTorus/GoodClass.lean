module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodTables
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodGraph
public import CFSG.Sporadic.He.Setup

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration
open scoped Matrix

set_option linter.unusedSectionVars false

@[expose] def RhoIs {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
    (M : List (List ℤ)) : Prop :=
  ∀ γ, IsRoot τ γ → S.ρ γ = toMat τ.rank M *ᵥ γ

section Arith

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)

theorem three_le_q_of_ne_two (h2 : S.D.q ≠ 2) : 3 ≤ S.D.q := by
  have := S.hqpow.1.one_lt
  omega

theorem orderOf_two_ne {p e : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (he : e = 1 ∨ e = 2 ∨ e = 4 ∨ e = 6) : orderOf (((2 : ℕ)) : ZMod p) ≠ e := by
  intro h
  have hd := dvd_pow_sub_one_of_orderOf hp (by norm_num : 0 < 2) h dvd_rfl
  have hsmall : ∀ a : ℕ, p ∣ a → 0 < a → a < 7 → False := fun a ha ha0 ha7 =>
    absurd (Nat.le_of_dvd ha0 ha) (by omega)
  rcases he with rfl | rfl | rfl | rfl
  · exact hsmall 1 (by simpa using hd) (by norm_num) (by norm_num)
  · exact hsmall 3 (by simpa using hd) (by norm_num) (by norm_num)
  · have h15 : p ∣ 3 * 5 := by norm_num at hd ⊢; exact hd
    rcases (Nat.Prime.dvd_mul hp).1 h15 with h3 | h5
    · exact hsmall 3 h3 (by norm_num) (by norm_num)
    · have := Nat.le_of_dvd (by norm_num) h5
      omega
  · have h63 : p ∣ 7 * (3 * 3) := by norm_num at hd ⊢; exact hd
    rcases (Nat.Prime.dvd_mul hp).1 h63 with h7 | h9
    · have hp7' : p = 7 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h7
      subst hp7'
      have h3 : orderOf (((2 : ℕ)) : ZMod 7) ∣ 3 := orderOf_dvd_of_pow_eq_one (by decide)
      rw [h] at h3
      omega
    · rcases (Nat.Prime.dvd_mul hp).1 h9 with h | h <;>
        exact hsmall 3 h (by norm_num) (by norm_num)

theorem three_le_q_of_class (hp7 : 7 ≤ p) {e : ℕ} (he : e = 1 ∨ e = 2 ∨ e = 4 ∨ e = 6)
    (hord : orderOf ((S.D.q : ℕ) : ZMod p) = e) : 3 ≤ S.D.q := by
  refine three_le_q_of_ne_two S fun h2 => ?_
  rw [h2] at hord
  exact orderOf_two_ne S.hp hp7 he hord

end Arith

section Untwisted

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

section E8

theorem setupRigid_E8_of_check (S : LangSetup .E8 L p) (hp7 : 7 ≤ p) (hAlg : S.IsAlgebraic)
    {M : List (List ℤ)} {e : ℕ} {cert : List (ℕ × ℕ × ℕ)} (hq3 : 3 ≤ S.D.q)
    (he : orderOf ((S.D.q : ℕ) : ZMod p) = e) (hρ : RhoIs S M)
    (h : classCheck Tag.E8.rank (cartanList Tag.E8) M Tag.E8.artifactRoots e cert = true) :
    SetupRigid S :=
  setupRigid_E8_of_goodRoots S (by omega) hAlg
    (goodRootsGenerate_of_classCheck S (Or.inr (Or.inr (Or.inr rfl))) (toMat_cartanList _) hρ hq3
      hp7 he h)

theorem setupRigid_E8_two (S : LangSetup .E8 L p) (hp7 : 7 ≤ p) (hAlg : S.IsAlgebraic)
    (he : orderOf ((S.D.q : ℕ) : ZMod p) = 2) (hρ : RhoIs S e8TwoMat) : SetupRigid S :=
  setupRigid_E8_of_check S hp7 hAlg (three_le_q_of_class S hp7 (Or.inr (Or.inl rfl)) he) he hρ
    e8Two_classCheck

theorem setupRigid_E8_four (S : LangSetup .E8 L p) (hp7 : 7 ≤ p) (hAlg : S.IsAlgebraic)
    (he : orderOf ((S.D.q : ℕ) : ZMod p) = 4) (hρ : RhoIs S e8FourMat) : SetupRigid S :=
  setupRigid_E8_of_check S hp7 hAlg
    (three_le_q_of_class S hp7 (Or.inr (Or.inr (Or.inl rfl))) he) he hρ e8Four_classCheck

@[expose] def SmallQ_E8_eight : Prop :=
  ∀ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup .E8 L p), 7 ≤ p →
    S.IsAlgebraic → orderOf ((S.D.q : ℕ) : ZMod p) = 8 → RhoIs S e8EightMat → S.D.q = 2 →
    SetupRigid S

theorem setupRigid_E8_eight_of_three_le (S : LangSetup .E8 L p) (hp7 : 7 ≤ p)
    (hAlg : S.IsAlgebraic) (hq3 : 3 ≤ S.D.q) (he : orderOf ((S.D.q : ℕ) : ZMod p) = 8)
    (hρ : RhoIs S e8EightMat) : SetupRigid S :=
  setupRigid_E8_of_check S hp7 hAlg hq3 he hρ e8Eight_classCheck

theorem setupRigid_E8_eight (hS : SmallQ_E8_eight) (S : LangSetup .E8 L p) (hp7 : 7 ≤ p)
    (hAlg : S.IsAlgebraic) (he : orderOf ((S.D.q : ℕ) : ZMod p) = 8)
    (hρ : RhoIs S e8EightMat) : SetupRigid S := by
  by_cases h2 : S.D.q = 2
  · exact hS S hp7 hAlg he hρ h2
  · exact setupRigid_E8_eight_of_three_le S hp7 hAlg (three_le_q_of_ne_two S h2) he hρ

end E8

section E7

theorem setupRigid_E7_of_check (S : LangSetup .E7 L p) (hp7 : 7 ≤ p) (hAlg : S.IsAlgebraic)
    {M : List (List ℤ)} {e : ℕ} {cert : List (ℕ × ℕ × ℕ)} (hq3 : 3 ≤ S.D.q)
    (he : orderOf ((S.D.q : ℕ) : ZMod p) = e) (hρ : RhoIs S M)
    (h : classCheck Tag.E7.rank (cartanList Tag.E7) M Tag.E7.artifactRoots e cert = true) :
    SetupRigid S :=
  setupRigid_E7_of_goodRoots S (by omega) hAlg
    (goodRootsGenerate_of_classCheck S (Or.inr (Or.inr (Or.inl rfl))) (toMat_cartanList _) hρ hq3
      hp7 he h)

theorem setupRigid_E7_two (S : LangSetup .E7 L p) (hp7 : 7 ≤ p) (hAlg : S.IsAlgebraic)
    (he : orderOf ((S.D.q : ℕ) : ZMod p) = 2) (hρ : RhoIs S e7TwoMat) : SetupRigid S :=
  setupRigid_E7_of_check S hp7 hAlg (three_le_q_of_class S hp7 (Or.inr (Or.inl rfl)) he) he hρ
    e7Two_classCheck

@[expose] def SmallQ_E7_three : Prop :=
  ∀ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup .E7 L p), 7 ≤ p →
    S.IsAlgebraic → orderOf ((S.D.q : ℕ) : ZMod p) = 3 → RhoIs S e7ThreeMat → S.D.q = 2 →
    SetupRigid S

theorem setupRigid_E7_three_of_three_le (S : LangSetup .E7 L p) (hp7 : 7 ≤ p)
    (hAlg : S.IsAlgebraic) (hq3 : 3 ≤ S.D.q) (he : orderOf ((S.D.q : ℕ) : ZMod p) = 3)
    (hρ : RhoIs S e7ThreeMat) : SetupRigid S :=
  setupRigid_E7_of_check S hp7 hAlg hq3 he hρ e7Three_classCheck

theorem setupRigid_E7_three (hS : SmallQ_E7_three) (S : LangSetup .E7 L p) (hp7 : 7 ≤ p)
    (hAlg : S.IsAlgebraic) (he : orderOf ((S.D.q : ℕ) : ZMod p) = 3)
    (hρ : RhoIs S e7ThreeMat) : SetupRigid S := by
  by_cases h2 : S.D.q = 2
  · exact hS S hp7 hAlg he hρ h2
  · exact setupRigid_E7_three_of_three_le S hp7 hAlg (three_le_q_of_ne_two S h2) he hρ

theorem setupRigid_E7_six (S : LangSetup .E7 L p) (hp7 : 7 ≤ p) (hAlg : S.IsAlgebraic)
    (he : orderOf ((S.D.q : ℕ) : ZMod p) = 6) (hρ : RhoIs S e7SixMat) : SetupRigid S :=
  setupRigid_E7_of_check S hp7 hAlg
    (three_le_q_of_class S hp7 (Or.inr (Or.inr (Or.inr rfl))) he) he hρ e7Six_classCheck

end E7

end Untwisted

section Twisted

variable {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

section D4

theorem setupRigid_triD4_of_check (S : LangSetup TwistTag.D4.tag L p) (hp7 : 7 ≤ p)
    (hΦ : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.D4 L Fr)
    (hAlg : S.IsAlgebraic) {M : List (List ℤ)} {e : ℕ} {cert : List (ℕ × ℕ × ℕ)}
    (hq3 : 3 ≤ S.D.q) (he : orderOf ((S.D.q : ℕ) : ZMod p) = e) (hρ : RhoIs S M)
    (h : classCheck Tag.D4.rank (cartanList Tag.D4) M Tag.D4.artifactRoots e cert = true)
    (hP : NoTriCosetCentralizes TwistTag.D4.tag L (diagramMap TwistTag.D4 L)) : SetupRigid S :=
  setupRigid_triD4_of_goodRoots S hΦ hAlg
    (goodRootsGenerate_of_classCheck S (Or.inl rfl) (toMat_cartanList _) hρ hq3 hp7 he h) hP

theorem setupRigid_triD4_one (S : LangSetup TwistTag.D4.tag L p) (hp7 : 7 ≤ p)
    (hΦ : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.D4 L Fr)
    (hAlg : S.IsAlgebraic) (he : orderOf ((S.D.q : ℕ) : ZMod p) = 1) (hρ : RhoIs S triD4OneMat) : SetupRigid S :=
  setupRigid_triD4_of_check S hp7 hΦ hAlg (three_le_q_of_class S hp7 (Or.inl rfl) he) he hρ
    triD4One_classCheck noTriCosetCentralizes_D4

theorem setupRigid_triD4_two (S : LangSetup TwistTag.D4.tag L p) (hp7 : 7 ≤ p)
    (hΦ : ∃ Fr : L →+* L, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.D4 L Fr)
    (hAlg : S.IsAlgebraic) (he : orderOf ((S.D.q : ℕ) : ZMod p) = 2) (hρ : RhoIs S triD4TwoMat) : SetupRigid S :=
  setupRigid_triD4_of_check S hp7 hΦ hAlg
    (three_le_q_of_class S hp7 (Or.inr (Or.inl rfl)) he) he hρ triD4Two_classCheck
    noTriCosetCentralizes_D4

end D4

end Twisted

end CFSG.HardMathSupport.Timmesfeld.LangTorus
