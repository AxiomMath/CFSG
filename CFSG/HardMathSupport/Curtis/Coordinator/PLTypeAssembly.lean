module

public import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeReduceCases
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPLType
import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsSpTwo
import CFSG.Quasithin.Vol2.Ch12Sec2Lem8Cases

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Curtis.Coordinator.PLType

open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock NineThreeThree barM blockPL kFactSpTwoSimple_holds
  kFactSpTwoPerfect_of_simple nonempty_quotient_pCore_mulEquiv_of_bot)
open CFSG.Quasithin.H13.Lem8 (center_eq_bot_of_mulEquiv center_alternatingGroup_eq_bot
  card_alternatingGroup_fin)

theorem eq_of_mul_pred_eq {k m : ℕ} (hm : 2 ≤ m) (h : k * (k - 1) = m * (m - 1)) : k = m := by
  obtain ⟨a, rfl⟩ : ∃ a, m = a + 2 := ⟨m - 2, by omega⟩
  rcases k with _ | _ | j
  · simp at h
  · simp at h
  · have h' : (j + 2) * (j + 1) = (a + 2) * (a + 1) := by simpa using h
    by_contra hne
    rcases Nat.lt_or_gt_of_ne (show j + 2 ≠ a + 2 by omega) with hlt | hgt
    · nlinarith
    · nlinarith

theorem mul_pred_ne_three {k : ℕ} (h : k * (k - 1) = 3) : False := by
  have hk : k < 4 := by
    by_contra hk
    have : 4 * 3 ≤ k * (k - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  interval_cases k <;> simp at h

theorem pCore_two_eq_bot_of_simple_of_perfect {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hperf : commutator Q = ⊤) : CFSG.pCore 2 Q = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (CFSG.pCore 2 Q).Normal := CFSG.pCore_normal (p := 2) (G := Q)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 Q) with h | h
  · exact h
  · exfalso
    have hP : IsPGroup 2 Q := by
      have h1 := CFSG.pCore_isPGroup (p := 2) (G := Q)
      rw [h] at h1
      exact IsPGroup.of_equiv h1 Subgroup.topEquiv
    have hZ := hP.center_nontrivial
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with hc | hc
    · exact (Subgroup.nontrivial_iff_ne_bot _).mp hZ hc
    · have hcomm : ∀ a b : Q, a * b = b * a := fun a b =>
        Subgroup.mem_center_iff.mp (hc ▸ Subgroup.mem_top b) a
      have h1 : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        exact hcomm y x
      rw [← commutator_def] at h1
      exact bot_ne_top (h1.symm.trans hperf)

section Clauses

variable {X P : Type} [Group X] [Group P]

theorem conj_orth [Finite P] (hT : TauCetiOrthFacts) (hA : AltTypeExcl) (hB : SpTypeB)
    (hsh : BlockShape X P) {m : ℕ} {d : TauCeti.ValidLieTypeIndex}
    (hd : ∃ q : TauCeti.PrimePower, q.card = 2 ∧ (d.1 = .D m q ∨ d.1 = .twistedD m q))
    (hm : 4 ≤ m) (e : X ≃* (TauCeti.CFSGIndex.lie d).Group) :
    ∃ d' : TauCeti.ValidLieTypeIndex,
      (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d'.1 = .B (m - 1) q) ∧
      Nonempty (P ⧸ CFSG.pCore 2 P ≃* (TauCeti.CFSGIndex.lie d').Group) := by
  rcases hsh with ⟨⟨e6⟩, -⟩ | ⟨k, hk, ⟨eP⟩⟩ | ⟨n, hn, ⟨eA⟩, -⟩
  · exact ((hA 6 (by norm_num)).1 m d hd).false (e6.symm.trans e) |>.elim
  · rw [Nat.card_congr e.toEquiv, (hT.1 m d hd).2] at hk
    obtain rfl : k = m := (eq_of_mul_pred_eq (by omega) hk.symm)
    obtain ⟨d', hd', ⟨eS⟩⟩ := hB (k - 1) (by omega)
    have hsimp := (kFactSpTwoSimple_holds (k - 1) d' (by omega) hd').1
    have hperf := kFactSpTwoPerfect_of_simple kFactSpTwoSimple_holds (k - 1) d' (by omega) hd'
    let ePY : P ≃* (TauCeti.CFSGIndex.lie d').Group := eP.trans eS
    have : Finite (TauCeti.CFSGIndex.lie d').Group := Finite.of_equiv P ePY.toEquiv
    have := hsimp
    obtain ⟨φ⟩ := nonempty_quotient_pCore_mulEquiv_of_bot ePY
      (pCore_two_eq_bot_of_simple_of_perfect hperf)
    exact ⟨d', hd', ⟨φ⟩⟩
  · exact ((hA n hn).1 m d hd).false (eA.symm.trans e) |>.elim

theorem conj_unitary (hT : TauCetiOrthFacts) (hA : AltTypeExcl) (hS : SpSmall)
    (hsh : BlockShape X P) {d : TauCeti.ValidLieTypeIndex}
    (hd : ∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .twistedA 3 q)
    (e : X ≃* (TauCeti.CFSGIndex.lie d).Group) : Nonempty (P ≃* Equiv.Perm (Fin 6)) := by
  rcases hsh with ⟨⟨e6⟩, -⟩ | ⟨k, hk, ⟨eP⟩⟩ | ⟨n, hn, ⟨eA⟩, -⟩
  · exact ((hA 6 (by norm_num)).2.1 d hd).false (e6.symm.trans e) |>.elim
  · rw [Nat.card_congr e.toEquiv, (hT.2 d hd).2] at hk
    have h25920 : (25920 : ℕ).factorization 2 = 6 := by decide +kernel
    rw [h25920] at hk
    obtain rfl : k = 3 := eq_of_mul_pred_eq (m := 3) (by norm_num) hk.symm
    obtain ⟨eS⟩ := hS.2
    exact ⟨eP.trans eS⟩
  · exact ((hA n hn).2.1 d hd).false (eA.symm.trans e) |>.elim

theorem conj_alt (hA : AltTypeExcl) (hsh : BlockShape X P) {n : ℕ} (hn : 5 ≤ n)
    (e : X ≃* alternatingGroup (Fin n)) :
    (n = 6 ∧ Nonempty (P ≃* Equiv.Perm (Fin 4))) ∨
      (∃ k : ℕ, (Nat.card (alternatingGroup (Fin n))).factorization 2 = k * (k - 1) ∧
        Nonempty (P ≃* ↥(CFSG.Open.StatedSp (k - 1) (ZMod 2)))) ∨
      Nonempty (P ≃* Equiv.Perm (Fin (n - 2))) := by
  rcases hsh with ⟨⟨e6⟩, ⟨eP⟩⟩ | ⟨k, hk, ⟨eP⟩⟩ | ⟨m, hm, ⟨eA⟩, ⟨eP⟩⟩
  · exact Or.inl ⟨((hA n hn).2.2 6 (by norm_num) ⟨e.symm.trans e6⟩), ⟨eP⟩⟩
  · rw [Nat.card_congr e.toEquiv] at hk
    exact Or.inr (Or.inl ⟨k, hk, ⟨eP⟩⟩)
  · obtain rfl : n = m := (hA n hn).2.2 m hm ⟨e.symm.trans eA⟩
    exact Or.inr (Or.inr ⟨eP⟩)

theorem conj_alt_five (hA : AltTypeExcl) (hS : SpSmall) (hsh : BlockShape X P)
    (e : X ≃* alternatingGroup (Fin 5)) : Nonempty (P ≃* Equiv.Perm (Fin 3)) := by
  rcases conj_alt hA hsh (n := 5) le_rfl e with ⟨h, -⟩ | ⟨k, hk, ⟨eP⟩⟩ | ⟨eP⟩
  · omega
  · rw [card_alternatingGroup_fin (by norm_num)] at hk
    have h60 : (Nat.factorial 5 / 2).factorization 2 = 2 := by decide +kernel
    rw [h60] at hk
    obtain rfl : k = 2 := eq_of_mul_pred_eq (m := 2) (by norm_num) hk.symm
    obtain ⟨eS⟩ := hS.1
    exact ⟨eP.trans eS⟩
  · exact eP

theorem conj_alt_six (hA : AltTypeExcl) (hsh : BlockShape X P)
    (e : X ≃* alternatingGroup (Fin 6)) : Nonempty (P ≃* Equiv.Perm (Fin 4)) := by
  rcases conj_alt hA hsh (n := 6) (by norm_num) e with ⟨-, h⟩ | ⟨k, hk, -⟩ | eP
  · exact h
  · rw [card_alternatingGroup_fin (by norm_num)] at hk
    have h360 : (Nat.factorial 6 / 2).factorization 2 = 3 := by decide +kernel
    rw [h360] at hk
    exact (mul_pred_ne_three hk.symm).elim
  · exact eP

theorem conj_alt_eight (hA : AltTypeExcl) (hS : SpSmall) (hsh : BlockShape X P)
    (e : X ≃* alternatingGroup (Fin 8)) : Nonempty (P ≃* Equiv.Perm (Fin 6)) := by
  rcases conj_alt hA hsh (n := 8) (by norm_num) e with ⟨h, -⟩ | ⟨k, hk, ⟨eP⟩⟩ | ⟨eP⟩
  · omega
  · rw [card_alternatingGroup_fin (by norm_num)] at hk
    have h20160 : (Nat.factorial 8 / 2).factorization 2 = 6 := by decide +kernel
    rw [h20160] at hk
    obtain rfl : k = 3 := eq_of_mul_pred_eq (m := 3) (by norm_num) hk.symm
    obtain ⟨eS⟩ := hS.2
    exact ⟨eP.trans eS⟩
  · exact eP

end Clauses

theorem citedBlockTransvectionPLType_of_cells
    (hO : OrthTransvectionCent) (hSym : SymTransvectionCent) (hSp : SpFourTransvectionCent)
    (h2 : OrthTwoPart) (hT : TauCetiOrthFacts) (hA : AltTypeExcl) (hB : SpTypeB)
    (hS : SpSmall) : CFSG.AGLEmbedding.CitedBlockTransvectionPLType := by
  intro G _ _ M S L hK hAs hL _ _ h3
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro m d hd he
    obtain ⟨e⟩ := he
    have hm : 4 ≤ m := by
      obtain ⟨q, -, hd | hd⟩ := hd
      · have h := d.2
        rw [hd] at h
        exact (TauCeti.LieTypeIndex.inStandardRange_iff _).1
          ((TauCeti.LieTypeIndex.valid_iff _).1 h).1
      · have h := d.2
        rw [hd] at h
        exact (TauCeti.LieTypeIndex.inStandardRange_iff _).1
          ((TauCeti.LieTypeIndex.valid_iff _).1 h).1
    have hZ := center_eq_bot_of_mulEquiv e (hT.1 m d hd).1
    exact conj_orth hT hA hB (block_shape hO hSym hSp h2 hK hAs hL h3 hZ) hd hm e
  · intro d hd he
    obtain ⟨e⟩ := he
    have hZ := center_eq_bot_of_mulEquiv e (hT.2 d hd).1
    exact conj_unitary hT hA hS (block_shape hO hSym hSp h2 hK hAs hL h3 hZ) hd e
  · rintro ⟨e⟩
    have hZ := center_eq_bot_of_mulEquiv e (center_alternatingGroup_eq_bot (n := 5) le_rfl)
    exact conj_alt_five hA hS (block_shape hO hSym hSp h2 hK hAs hL h3 hZ) e
  · rintro ⟨e⟩
    have hZ := center_eq_bot_of_mulEquiv e (center_alternatingGroup_eq_bot (n := 6) (by norm_num))
    exact conj_alt_six hA (block_shape hO hSym hSp h2 hK hAs hL h3 hZ) e
  · rintro ⟨e⟩
    have hZ := center_eq_bot_of_mulEquiv e (center_alternatingGroup_eq_bot (n := 8) (by norm_num))
    exact conj_alt_eight hA hS (block_shape hO hSym hSp h2 hK hAs hL h3 hZ) e

end CFSG.HardMathSupport.Curtis.Coordinator.PLType
