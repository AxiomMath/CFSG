module

public import CFSG.LargeExtraspecial.S4TwoH
public import CFSG.LargeExtraspecial.S4TwoPSL
public import CFSG.LargeExtraspecial.S3cMain
public import CFSG.LargeExtraspecial.S4TwoA
public import CFSG.LargeExtraspecial.S4TwoD
public import CFSG.LargeExtraspecial.S4TwoG
public import CFSG.LargeExtraspecial.S4TwoInput

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module CFSG.CGT.Timmesfeld75 CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem card_Form2L : Nat.card (Form2L S.Mbar (LM S g)) = Nat.card (S.Lbar g) := by
  have hinj : Function.Injective (QuotientGroup.mk' (CFSG.pCore 2 (M0 S g))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', pCore_M0_eq_bot]
  rw [← card_LM0]
  exact Subgroup.card_map_of_injective hinj

theorem eq_four_of_two_pow_le {w : ℕ} (h4 : 4 ≤ w) (h : 2 ^ (w - 1) ≤ 2 * w) : w = 4 := by
  by_contra hne
  have h5 : 5 ≤ w := by omega
  have hlt := Nat.lt_two_pow_self (n := w - 4)
  have hpow : 2 ^ (w - 1) = 8 * 2 ^ (w - 4) := by
    rw [show w - 1 = 3 + (w - 4) by omega, pow_add]
    norm_num
  omega

theorem lemma_4_2_core (hBen : BenderConjCountInput) (hWT : WeaklyClosedTITransitive.{0})
    (H : Hyp4 S g) (C : Cons311 S g) (hNo : NoA2 S g) (hirr : ¬ S.IsReducible) {Q' : Type}
    [Group Q'] [Finite Q'] (ψ : M0 S g ≃* Q') {T : Subgroup Q'}
    (hψ : (LM0 S g).map ψ.toMonoidHom = T) (hstd : StdPair Q' T) :
    S.width = 4 ∧ (StatedClassicalModel (M0 S g) .PSL 2 2 3 ∨
      Nonempty (M0 S g ≃* alternatingGroup (Fin 9))) := by
  have hn4 := four_le_width H C
  have h2n := two_mul_width_le_card_Lbar H
  have hcL := C.card_Lbar
  have hcT : Nat.card T = Nat.card (S.Lbar g) := by
    rw [← hψ, Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, card_LM0]
  have hmeet : (∀ x : Q', conjSubgroup x T ⊓ normalizer (T : Set Q') ≠ ⊥) → False := by
    intro h
    refine hirr (isReducible_of_meet H C (meet_of_mulEquiv ψ ?_))
    rw [hψ]
    exact h
  have hbender : ConjTwoTransitive Q' T →
      Nat.card (Set.range fun x : Q' => conjSubgroup x T) ≤ 2 * S.width + 1 := by
    intro h2
    have h2' : ConjTwoTransitive (M0 S g) (LM0 S g) := by
      refine conjTwoTransitive_of_mulEquiv ψ ?_
      rw [hψ]
      exact h2
    rcases isReducible_or_card_conj_le H C h2' with h | h
    · exact absurd h hirr
    · rwa [card_conj_of_mulEquiv ψ, hψ] at h
  have hpslmeet : ∀ (m : ℕ) (K' : Type) [Field K'] [Finite K'] (f : ℕ), 3 ≤ m →
      Nat.card K' = 2 ^ f → (Q' ≃* StatedProj (StatedSL m K')) → False := by
    intro m K' _ _ f hm hK e
    obtain ⟨-, hTe⟩ := hstd.of_psl hm K' hK e
    apply hmeet
    have hin := pslTransvectionMeetInput m K' hm
    rcases hTe with ⟨c, hc0, hc⟩ | ⟨a, ha0, ha⟩
    · refine meet_of_mulEquiv e ?_
      rw [hc]
      exact hin.1 c hc0
    · refine meet_of_mulEquiv e ?_
      rw [ha]
      exact hin.2 a ha0
  have hNo' : ¬ S.HasTypeAInL g := fun ⟨α, h1, h2, h3⟩ => hNo α h1 h2 h3
  rw [hcL] at h2n
  rcases hstd.listGroup with ⟨m, s, hm, hs, hmod⟩ | ⟨s, hs, hmod⟩ | ⟨s, hso, hs, hmod⟩ |
      ⟨k, hk6, hk9, ⟨eA⟩⟩ | hM | hM | hM
  · rcases Nat.lt_or_ge m 3 with hm3 | hm3
    ·
      obtain rfl : m = 2 := by omega
      obtain ⟨hTq, -, h2, ⟨S'', hN⟩⟩ := hstd.of_psl2 hmod
      have hsyl := card_sylow_le_card_conj S'' hN
      have hcount := (hBen Q').1 s hmod
      have hb := hbender h2
      rw [hcT, hcL] at hTq
      have hw : S.width = 4 := eq_four_of_two_pow_le hn4 (by omega)
      have hs3 : s = 3 := by
        rw [hw] at hTq
        have h' : 2 ^ s = 2 ^ 3 := hTq.symm.trans (by norm_num)
        exact Nat.pow_right_injective le_rfl h'
      refine ⟨hw, Or.inl ?_⟩
      subst hs3
      exact statedClassicalModel_PSL_of_mulEquiv ψ hmod
    · obtain ⟨-, K', hF, hfin, hK', ⟨e⟩⟩ := hmod
      exact (hpslmeet m K' s hm3 hK' e).elim
  ·
    exfalso
    obtain ⟨hTq, -, h2, ⟨S'', hN⟩⟩ := hstd.of_psu3 hs hmod
    have hsyl := card_sylow_le_card_conj S'' hN
    have hcount := (hBen Q').2.2 s hs hmod
    have hb := hbender h2
    rw [hcT, hcL] at hTq
    have hlt : 2 ^ s < 2 ^ (3 * s) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  ·
    exfalso
    obtain ⟨hTq, -, h2, ⟨S'', hN⟩⟩ := hstd.of_sz hso hs hmod
    have hsyl := card_sylow_le_card_conj S'' hN
    have hcount := (hBen Q').2.1 s hso hs hmod
    have hb := hbender h2
    rw [hcT, hcL] at hTq
    have hlt : 2 ^ s < 2 ^ (2 * s) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  ·
    have hTk := hstd.card_alternating hk6 hk9 ⟨eA⟩
    rw [hcT, hcL] at hTk
    rcases Nat.lt_or_ge k 8 with hk8 | hk8
    · exfalso
      have hk7 : k ≤ 7 := by omega
      simp only [hk7, ↓reduceIte] at hTk
      omega
    have hk7 : ¬ k ≤ 7 := by omega
    simp only [hk7, ↓reduceIte] at hTk
    have hw : S.width = 4 := eq_four_of_two_pow_le hn4 (by omega)
    rcases Nat.lt_or_ge k 9 with hk9' | hk9'
    · exfalso
      obtain rfl : k = 8 := by omega
      obtain ⟨e⟩ := nonempty_mulEquiv_psl_of_alternating_eight eA
      exact hpslmeet 4 (ZMod 2) 1 (by norm_num) (by simp) e
    · obtain rfl : k = 9 := by omega
      exact ⟨hw, Or.inr ⟨ψ.trans eA⟩⟩
  all_goals
    exfalso
    have hT16 := hstd.card_sporadic (by tauto)
    rw [hcT, hcL] at hT16
    have hw5 : S.width = 5 := by
      have := Nat.pow_right_injective le_rfl (hT16.trans (by norm_num : (16 : ℕ) = 2 ^ 4))
      omega
    exact S.false_of_width_eq_five hWT hw5 H.conj_mem H.conj_ne hNo' hirr

theorem lemma_4_2 (hF2 : Form2StrongStmt) (hBen : BenderConjCountInput)
    (hWT : WeaklyClosedTITransitive.{0}) (H : Hyp4 S g)
    (C : Cons311 S g) (hNo : NoA2 S g)
    (hTI : ∀ h : S.M, S.Lbar ((h : G) * g) ⊓ S.Lbar g = ⊥ ∨ S.Lbar ((h : G) * g) = S.Lbar g)
    (hirr : ¬ S.IsReducible) :
    S.width = 4 ∧ (StatedClassicalModel (M0 S g) .PSL 2 2 3 ∨
      Nonempty (M0 S g ≃* alternatingGroup (Fin 9))) := by
  have h2n := two_mul_width_le_card_Lbar H
  have hn4 := four_le_width H C
  have hcard0 := card_Form2L (S := S) (g := g)
  rcases hF2 S.Mbar (LM S g) (isWC_Lbar H C hTI) with ⟨hle, -⟩ | ⟨-, -, -, -, hstd⟩
  · exfalso
    rw [hcard0] at hle
    omega
  by_cases hz : center (Form2Q S.Mbar (LM S g)) = ⊥
  · obtain ⟨ψ, hψ⟩ := exists_mulEquiv_Form2Q hz
    exact lemma_4_2_core hBen hWT H C hNo hirr ψ hψ hstd
  · exact absurd (isReducible_of_center_Form2Q_ne_bot H hz) hirr

end CFSG.LargeExtraspecial.S4
