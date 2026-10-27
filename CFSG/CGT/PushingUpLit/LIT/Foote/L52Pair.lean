module

public import CFSG.CGT.PushingUpLit.LIT.Foote.TightAux
public import CFSG.CGT.PushingUpLit.LIT.Foote.L51
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Transport

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.CGT.PushingUpLit CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3 (Theorem3Statement Frame SylowFrame)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem commutator_eq_bot_of_action (h3 : Theorem3Statement) {A B T : Subgroup G}
    (hA : QBlock A) (hB : TightlyEmbedded B) (hodd : Odd (Nat.card ↥(A ⊓ B)))
    (hT : IsSylowOf 2 T (B ⊓ Subgroup.normalizer (A : Set G))) (hT1 : T ≠ ⊥)
    (hcmp : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ A → Q ≤ Subgroup.normalizer (B : Set G) →
      Nat.card Q ≤ Nat.card T) : ⁅T, A⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTpg : IsPGroup 2 T := hT.isPGroup
  have hTN : T ≤ Subgroup.normalizer (A : Set G) := hT.le.trans inf_le_right
  have hTB : T ≤ B := hT.le.trans inf_le_left
  have hTA : T ⊓ A = ⊥ :=
    two_subgroup_of_odd_eq_bot (T ⊓ A) (A ⊓ B) hTpg.to_inf_left hodd
      (le_inf inf_le_right (inf_le_left.trans hTB))
  have hF : Frame A T := ⟨hTN, hTA, hTpg⟩
  obtain ⟨S, hS⟩ := hF.exists_sylowFrame
  have hTle : T ≤ B ⊓ (A ⊔ T) := le_inf hTB le_sup_right
  have hPeven : Even (Nat.card ↥(B ⊓ (A ⊔ T))) := even_card_of_isPGroup hTpg hT1 hTle
  have htight := tightlyEmbedded_inf_subgroupOf (H := A ⊔ T) hB hPeven
  have hLK : B ⊓ (A ⊔ T) ≤ B ⊓ Subgroup.normalizer (A : Set G) :=
    inf_le_inf_left B (sup_le Subgroup.le_normalizer hTN)
  have hPsyl : IsSylowOf 2 T (B ⊓ (A ⊔ T)) := hT.of_le hTle hLK
  refine lemma_5_1 h3 hA hT1 hS hPsyl inf_le_right htight ?_
  set X := S ⊓ Subgroup.normalizer (T : Set G) with hX
  have hTX : T ≤ X := le_inf hS.le Subgroup.le_normalizer
  have hXpg : IsPGroup 2 X := hS.sylow.isPGroup.to_inf_left
  set Q := X ⊓ A with hQ
  have hQcomm : ∀ q ∈ Q, ∀ t ∈ T, q * t = t * q := by
    intro q hq t ht
    obtain ⟨hqX, hqA⟩ := Subgroup.mem_inf.1 hq
    have hqN : q ∈ Subgroup.normalizer (T : Set G) := (Subgroup.mem_inf.1 hqX).2
    have h1 : q * t * q⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 hqN t).1 ht
    have h2 : t * q⁻¹ * t⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 (hTN ht) q⁻¹).1 (A.inv_mem hqA)
    have hc : q * t * q⁻¹ * t⁻¹ ∈ T ⊓ A :=
      ⟨T.mul_mem h1 (T.inv_mem ht), by
        have := A.mul_mem hqA h2
        simpa [mul_assoc] using this⟩
    rw [hTA, Subgroup.mem_bot] at hc
    calc q * t = (q * t * q⁻¹ * t⁻¹) * (t * q) := by group
      _ = t * q := by rw [hc, one_mul]
  have hQN : Q ≤ Subgroup.normalizer (B : Set G) := fun q hq =>
    mem_normalizer_of_commute hB hTpg hT1 hTB (hQcomm q hq)
  have hQcard : Nat.card Q ≤ Nat.card T :=
    hcmp Q (hXpg.to_inf_left) inf_le_right hQN
  let f : ↥T × ↥Q → ↥X := fun p =>
    ⟨(p.1 : G) * (p.2 : G), X.mul_mem (hTX p.1.2) (Subgroup.mem_inf.1 p.2.2).1⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, hxX⟩
    have hxS : x ∈ S := (Subgroup.mem_inf.1 hxX).1
    have hxTA : x ∈ T ⊔ A := by
      rw [sup_comm]
      exact hS.sylow.le hxS
    obtain ⟨t, ht, a, ha, hta⟩ := exists_mul_of_mem_sup hTN hxTA
    have haX : a ∈ X := by
      have : a = t⁻¹ * x := by rw [← hta]; group
      rw [this]
      exact X.mul_mem (X.inv_mem (hTX ht)) hxX
    exact ⟨(⟨t, ht⟩, ⟨a, Subgroup.mem_inf.2 ⟨haX, ha⟩⟩), Subtype.ext hta⟩
  have hXcard : Nat.card X ≤ Nat.card T * Nat.card Q := by
    have := Nat.card_le_card_of_surjective f hf
    rwa [Nat.card_prod] at this
  have hmul := Subgroup.relIndex_mul_card T X
  rw [inf_eq_left.2 hTX] at hmul
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have hrel : T.relIndex X ≤ Nat.card Q := by
    refine Nat.le_of_mul_le_mul_right ?_ hTpos
    rw [hmul, mul_comm]
    exact hXcard
  exact hrel.trans hQcard

theorem commutator_eq_bot_of_pair (h3 : Theorem3Statement) {A B TA TB : Subgroup G}
    (hA : QBlock A) (hBq : QBlock B) (hAt : TightlyEmbedded A) (hBt : TightlyEmbedded B)
    (hodd : Odd (Nat.card ↥(A ⊓ B))) (hcard : Nat.card A = Nat.card B)
    (hTA : IsSylowOf 2 TA (A ⊓ Subgroup.normalizer (B : Set G)))
    (hTB : IsSylowOf 2 TB (B ⊓ Subgroup.normalizer (A : Set G))) (hTB1 : TB ≠ ⊥)
    (hle : Nat.card TA ≤ Nat.card TB) : ⁅A, B⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : ⁅TB, A⁆ = ⊥ :=
    commutator_eq_bot_of_action h3 hA hBt hodd hTB hTB1 fun Q hQ hQA hQN =>
      (card_le_of_isSylowOf hTA (le_inf hQA hQN) hQ).trans hle
  have hTBC : TB ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1
  have hAN : A ≤ Subgroup.normalizer (B : Set G) := fun a ha =>
    mem_normalizer_of_commute hBt hTB.isPGroup hTB1 (hTB.le.trans inf_le_left) fun t ht =>
      Subgroup.mem_centralizer_iff.1 (hTBC ht) a ha
  have hTA' : IsSylowOf 2 TA A := by
    have := hTA
    rwa [inf_eq_left.2 hAN] at this
  have hTA1 : TA ≠ ⊥ := ne_bot_of_isSylowOf_even hTA' hAt.1
  have hTBle : Nat.card TB ≤ Nat.card TA := by
    obtain ⟨PB, hPB⟩ := exists_isSylowOf 2 B
    have h1' := card_le_of_isSylowOf hPB (hTB.le.trans inf_le_left) hTB.isPGroup
    rw [hPB.card_eq, ← hcard, ← hTA'.card_eq] at h1'
    exact h1'
  have h4 : ⁅TA, B⁆ = ⊥ :=
    commutator_eq_bot_of_action h3 hBq hAt (by rwa [inf_comm]) hTA hTA1 fun Q hQ hQB hQN =>
      (card_le_of_isSylowOf hTB (le_inf hQB hQN) hQ).trans hTBle
  exact commutator_eq_bot_of_sylow hA.perfect hTA' hAN h4

theorem commutator_conj_eq_bot (h3 : Theorem3Statement) {J : Subgroup G} (hJ : QBlock J)
    (hJt : TightlyEmbedded J) {g : G} (hg : g ∉ Subgroup.normalizer (J : Set G))
    (heven : Even (Nat.card ↥(rightConjugate J g ⊓ Subgroup.normalizer (J : Set G)))) :
    ⁅J, rightConjugate J g⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBq : QBlock (rightConjugate J g) := hJ.conj g
  have hBt : TightlyEmbedded (rightConjugate J g) := tightlyEmbedded_conj hJt g
  have hodd : Odd (Nat.card ↥(J ⊓ rightConjugate J g)) := hJt.2 g hg
  have hcard : Nat.card J = Nat.card (rightConjugate J g) := (rightConjugate_card J g).symm
  obtain ⟨TA, hTA⟩ := exists_isSylowOf 2
    (J ⊓ Subgroup.normalizer ((rightConjugate J g : Subgroup G) : Set G))
  obtain ⟨TB, hTB⟩ := exists_isSylowOf 2 (rightConjugate J g ⊓ Subgroup.normalizer (J : Set G))
  have hTB1 : TB ≠ ⊥ := ne_bot_of_isSylowOf_even hTB heven
  rcases le_or_gt (Nat.card TA) (Nat.card TB) with hle | hlt
  · exact commutator_eq_bot_of_pair h3 hJ hBq hJt hBt hodd hcard hTA hTB hTB1 hle
  · have hTA1 : TA ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hlt
      have := Nat.card_pos (α := TB)
      omega
    have := commutator_eq_bot_of_pair h3 hBq hJ hBt hJt (by rwa [inf_comm]) hcard.symm hTB hTA
      hTA1 hlt.le
    rwa [Subgroup.commutator_comm]

end CFSG.CGT.PushingUpLit.LIT.Foote
