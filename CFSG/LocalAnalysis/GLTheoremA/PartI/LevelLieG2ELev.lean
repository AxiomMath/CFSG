module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieG2EOrd
public import CFSG.LocalAnalysis.GLTheoremA.CatC.LieCompHolds

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieG2E

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.I1420

theorem kLevel_le_two_of_k2 {T : Type} [Group T] (h : catalogIs T (k2 3)) : kLevel 3 T ≤ 2 := by
  unfold kLevel
  split_ifs <;> first | omega | exact absurd h ‹_›

theorem primePower_p_eq {q : TauCeti.PrimePower} {r e : ℕ} (hr : r.Prime) (he : e ≠ 0)
    (hq : q.card = r ^ e) : q.p = r := by
  have h1 : q.p ∣ r ^ e := by
    rw [← hq, TauCeti.PrimePower.card_def]
    exact dvd_pow_self q.p q.exponent_pos.ne'
  exact (Nat.prime_dvd_prime_iff_eq q.prime_p hr).1 (q.prime_p.dvd_of_dvd_pow h1)

theorem kLevel_le_two_of_chev {T : Type} [Group T] (h : IsChevSimple 3 T) : kLevel 3 T ≤ 2 := by
  unfold kLevel
  rw [if_pos h]
  norm_num



open TauCeti in
theorem level_of_chev2 {T : Type} [Group T] [Finite T] (hT : IsChevSimple 2 T)
    (hd : Nat.card T ∣ Nbig) : kLevel 3 T ≤ 2 ∨ (49 ∣ Nat.card T ∧ 73 ∣ Nat.card T) := by
  rcases hT with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | cyclic _ _ => exact hi.elim
    | alternating _ _ => exact hi.elim
    | sporadic _ => exact hi.elim
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      have hchar : d.characteristic = 2 := hi
      have hcard : Nat.card T = lieOrderFormula d := lieOrderBridge_holds ⟨d, hv⟩ T ⟨e⟩
      rcases classify hv hchar (hcard ▸ hd) with ⟨q, rfl, hq8 | hq512⟩ | ⟨q, rfl, hq8⟩ |
        ⟨q, rfl, hq8⟩ | ⟨q, rfl, hq8⟩ | ⟨q, rfl, hq2⟩
      · refine Or.inl (kLevel_le_two_of_chev (Or.inr ⟨.lie ⟨.A 1 q, hv⟩, ?_, ⟨e⟩⟩))
        exact Or.inr ⟨hq8, rfl⟩
      · exact Or.inl (kLevel_le_two_of_k2 ⟨.lie ⟨.A 1 q, hv⟩, ⟨rfl, by rw [hq512]; norm_num⟩, ⟨e⟩⟩)
      · refine Or.inr ?_
        rw [hcard]
        simp only [lieOrderFormula, hq8]
        decide +kernel
      · have hp : q.p = 2 := by simpa using hchar
        have hex : q.exponent = 3 := by
          have h1 : q.card = 2 ^ q.exponent := by rw [PrimePower.card_def, hp]
          have : 2 ^ q.exponent = 2 ^ 3 := by rw [← h1, hq8]; norm_num
          exact Nat.pow_right_injective (le_refl 2) this
        exact Or.inl (kLevel_le_two_of_k2 ⟨.lie ⟨.twistedA 2 q, hv⟩,
          ⟨rfl, hp, by rw [hex]; decide, by rw [hex]; norm_num⟩, ⟨e⟩⟩)
      · exact Or.inl (kLevel_le_two_of_k2 ⟨.lie ⟨.G2 q, hv⟩, ⟨rfl, hq8⟩, ⟨e⟩⟩)
      · exact Or.inl (kLevel_le_two_of_k2 ⟨.lie ⟨.trialityD4 q, hv⟩, ⟨rfl, hq2⟩, ⟨e⟩⟩)
  · cases i with
    | cyclic _ _ => exact hi.elim
    | sporadic _ => exact hi.elim
    | alternating n hn =>
      exfalso
      haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
      have hcard : Nat.card T = n.factorial / 2 := by
        rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
          Fintype.card_fin]
      have h5 : 5 ∣ Nat.card T := by
        rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rw [hcard] <;> decide
      have h5N : 5 ∣ Nbig := h5.trans hd
      revert h5N
      unfold Nbig
      decide
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | A n q =>
        rcases n with _ | _ | n
        · exact hi.elim
        · rcases hi with ⟨hq7, -⟩ | ⟨-, h23⟩
          · exact Or.inl (kLevel_le_two_of_k2 ⟨.lie ⟨.A 1 q, hv⟩,
              ⟨rfl, by rw [hq7]; norm_num⟩, ⟨e⟩⟩)
          · omega
        · exact hi.elim
      | twistedA n q =>
        rcases n with _ | _ | _ | _ | n
        · exact hi.elim
        · exact hi.elim
        · obtain ⟨hq3, -⟩ := hi
          have hp3 : q.p = 3 := by
            have h1 : q.p ∣ 3 := by
              rw [← hq3, PrimePower.card_def]
              exact dvd_pow_self q.p q.exponent_pos.ne'
            exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 h1
          exact Or.inl (kLevel_le_two_of_chev
            (Or.inl ⟨.lie ⟨.twistedA 2 q, hv⟩, by simpa [onLie] using hp3, ⟨e⟩⟩))
        · obtain ⟨-, h23⟩ := hi
          omega
        · exact hi.elim
      | _ => exact hi.elim


open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.LocalAnalysis.GLTheoremB

theorem fixSubgroup_one {K : Type*} [Group K] : fixSubgroup (1 : MulAut K) = ⊤ := by
  ext x
  rw [mem_fixSubgroup]
  simp

theorem downLe_of_chev2 {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (idx : TauCeti.ValidLieTypeIndex)
    (e : S ≃* (TauCeti.CFSGIndex.lie idx).Group) (hchar : idx.1.characteristic = 2)
    (hSN : Nat.card S ∣ Nbig) (hS : kLevel 3 S ≤ 2)
    (hbad : ∀ β : MulAut S, β ^ 3 = 1 → β ≠ 1 →
      ¬ (49 ∣ Nat.card ↥(fixSubgroup β) ∧ 73 ∣ Nat.card ↥(fixSubgroup β))) :
    DownLe 3 2 S := by
  intro β hβ I hI
  by_cases h1 : β = 1
  · subst h1
    rw [fixSubgroup_one] at hI
    obtain ⟨f⟩ := chevQ_pSimple_top_equiv Nat.prime_three hna hI
    rw [kLevel_congr 3 f]
    exact hS
  · have hlc := lieComp_holds S ‹_› hna idx ⟨e⟩ β hβ I hI
    have hchev : IsChevSimple 2 (PSimple 3 I) := by
      have := hlc.1.chev
      have hc : lieIndexChar idx.1 = 2 := by
        cases idx using Subtype.rec with
        | _ d hv => cases d <;> first | exact hchar | simp_all [lieIndexChar]
      rw [hc] at this
      exact this
    haveI : Finite ↥I := Finite.of_injective _ (Subgroup.subtype_injective I)
    have hT1 : Nat.card (PSimple 3 I) ∣ Nat.card (PQuot 3 I) := Subgroup.card_quotient_dvd_card _
    have hT2 : Nat.card (PQuot 3 I) ∣ Nat.card ↥I := Subgroup.card_quotient_dvd_card _
    have hT3 : Nat.card ↥I ∣ Nat.card ↥(fixSubgroup β) := Subgroup.card_dvd_of_le hI.1
    have hT4 : Nat.card ↥(fixSubgroup β) ∣ Nat.card S := Subgroup.card_subgroup_dvd_card _
    have hcT : Nat.card (PSimple 3 I) ∣ Nat.card ↥(fixSubgroup β) := hT1.trans (hT2.trans hT3)
    haveI : Finite (PSimple 3 I) := inferInstance
    rcases level_of_chev2 hchev (hcT.trans (hT4.trans hSN)) with h | ⟨h49, h73⟩
    · exact h
    · exact absurd ⟨h49.trans hcT, h73.trans hcT⟩ (hbad β hβ h1)

end CFSG.LocalAnalysis.GLTheoremA.LevelLieG2E
