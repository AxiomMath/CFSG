module

public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.LinearCovers

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

namespace FullCover

section

open TauCeti

theorem simpleCoverList_of_center_eq_bot {Q : Type} [Group Q] {P : CFSGIndex → Prop}
    (hbot : Subgroup.center Q = ⊥) (h : catalogIs (Q ⧸ Subgroup.center Q) P) :
    SimpleCoverList Q P := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  exact ⟨hbot, i, hi, ⟨((QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hbot.symm)).trans e)⟩⟩

theorem coverListed_lie {d : LieTypeIndex} {hv : d.Valid}
    (h : CoverListed (CFSGIndex.lie ⟨d, hv⟩)) :
    (∃ q, d = LieTypeIndex.A 2 q) ∨ (∃ q, d = LieTypeIndex.twistedA 2 q) ∨
      (∃ q, d = LieTypeIndex.twistedA 5 q ∧ q.card = 2) := by
  cases d with
  | A r q =>
    left
    refine ⟨q, ?_⟩
    rcases r with _ | _ | _ | r <;> first | rfl | exact h.elim
  | twistedA r q =>
    rcases r with _ | _ | _ | _ | _ | _ | r
    · exact h.elim
    · exact h.elim
    · exact Or.inr (Or.inl ⟨q, rfl⟩)
    · exact h.elim
    · exact h.elim
    · exact Or.inr (Or.inr ⟨q, rfl, h⟩)
    · exact h.elim
  | _ => exact h.elim

theorem k2HatIndex_of_k2 {i : CFSGIndex} (hi : k2 3 i)
    (h : k2HatIndex 3 i ∨ k3HatIndex 3 i) : k2HatIndex 3 i := by
  cases i with
  | cyclic _ _ => exact hi.elim
  | lie _ => exact h.elim (fun h => h.elim) fun h => h.elim
  | alternating n _ =>
    rcases h with h | h
    · exact h.elim
    · obtain ⟨-, rfl⟩ := h
      rcases hi with ⟨-, h | h⟩ | ⟨h, -⟩
      · omega
      · omega
      · omega
  | sporadic s =>
    rcases h with h | h
    · exact h
    · obtain ⟨-, rfl⟩ := h
      exact hi.elim

theorem k3HatIndex_of_k3 {i : CFSGIndex} (hi : k3 3 i)
    (h : k2HatIndex 3 i ∨ k3HatIndex 3 i) : k3HatIndex 3 i := by
  cases i with
  | cyclic _ _ => exact hi.elim
  | lie _ => exact h.elim (fun h => h.elim) fun h => h.elim
  | alternating n _ =>
    rcases h with h | h
    · exact h.elim
    · exact h
  | sporadic s =>
    rcases h with h | h
    · obtain ⟨-, hs⟩ := h
      obtain ⟨-, hs'⟩ := hi
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hs' with h | h <;> cases h
    · exact h

theorem three_dvd_card_sub_one_of_listed {q : PrimePower} {hv : (LieTypeIndex.A 2 q).Valid}
    (hi : k2 3 (CFSGIndex.lie ⟨LieTypeIndex.A 2 q, hv⟩) ∨
      k3 3 (CFSGIndex.lie ⟨LieTypeIndex.A 2 q, hv⟩)) : 3 ∣ q.card - 1 := by
  rcases hi with (⟨-, hq2, hev⟩ | ⟨h, -⟩) | ⟨-, h6⟩
  · have := three_dvd_two_pow_sub_one_of_even hev
    rwa [PrimePower.card_def, hq2]
  · omega
  · have h6' : q.card % 6 = 1 := h6
    omega

theorem three_dvd_card_add_one_of_listed {q : PrimePower} {hv : (LieTypeIndex.twistedA 2 q).Valid}
    (hi : k2 3 (CFSGIndex.lie ⟨LieTypeIndex.twistedA 2 q, hv⟩) ∨
      k3 3 (CFSGIndex.lie ⟨LieTypeIndex.twistedA 2 q, hv⟩)) : 3 ∣ q.card + 1 := by
  rcases hi with ⟨-, hq2, hodd, -⟩ | ⟨-, h6⟩
  · have := three_dvd_two_pow_add_one_of_odd hodd
    rwa [PrimePower.card_def, hq2]
  · have h6' : q.card % 6 = 5 := h6
    omega

end

end FullCover

open FullCover

variable {p : ℕ}

theorem catalogIs_imp_k2Cover (hM : ListedMultiplierBound p) (hH : HatOddMultiplierBound)
    {Q : Type} [Group Q] [Finite Q] (hQ : CFSG.Open.IsQuasisimple Q)
    (hZ : IsPGroup p (Subgroup.center Q)) (h : catalogIs (Q ⧸ Subgroup.center Q) (k2 p)) :
    K2Cover p Q := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  refine ⟨hQ, ?_⟩
  by_cases hbot : Subgroup.center Q = ⊥
  · exact Or.inl (simpleCoverList_of_center_eq_bot hbot ⟨i, hi, ⟨e⟩⟩)
  obtain ⟨hp3, hZ3, hlist⟩ := hM i (Or.inl hi) Q hQ (centralProj e) (centralProj_surjective e)
    (centralProj_ker e) hZ hbot
  subst hp3
  have hmain : ∀ (j : TauCeti.ValidLieTypeIndex),
      ∀ e' : Q ⧸ Subgroup.center Q ≃* (TauCeti.CFSGIndex.lie j).Group,
        k2 3 (TauCeti.CFSGIndex.lie j) → CoverListed (TauCeti.CFSGIndex.lie j) →
          K2LinearCover 3 Q := by
    rintro ⟨d, hv⟩ e' hi' hlist'
    rcases coverListed_lie hlist' with ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl, hq2⟩
    · have hfl := fullLinearCover_false_of_cover hM q hv (Or.inl hi')
        (three_dvd_card_sub_one_of_listed (Or.inl hi')) hQ e' hZ3
      rcases hi' with ⟨-, hp2, hev⟩ | ⟨h13, -⟩
      · refine ⟨rfl, Or.inl ⟨q.exponent, q.exponent_pos, hev, ?_⟩⟩
        rwa [show q.card = 2 ^ q.exponent by rw [TauCeti.PrimePower.card_def, hp2]] at hfl
      · omega
    · have hfl := fullLinearCover_true_of_cover hM q hv (Or.inl hi')
        (three_dvd_card_add_one_of_listed (Or.inl hi')) hQ e' hZ3
      obtain ⟨-, hp2, hodd, hgt⟩ := hi'
      refine ⟨rfl, Or.inr (Or.inl ⟨q.exponent, hgt, hodd, ?_⟩)⟩
      rwa [show q.card = 2 ^ q.exponent by rw [TauCeti.PrimePower.card_def, hp2]] at hfl
    · exact ⟨rfl, Or.inr (Or.inr (fullLinearCover_true_six_of_cover hM q hv (Or.inl hi') hq2 hQ e'
        hZ3))⟩
  cases i with
  | cyclic _ _ => exact hi.elim
  | lie j => exact Or.inr (Or.inr (Or.inl (hmain j e hi hlist)))
  | alternating n hn =>
    exact Or.inr (Or.inr (Or.inr ⟨_, k2HatIndex_of_k2 hi hlist,
      maximalOddCover_of_oddBound _ hQ (centralProj e) (centralProj_surjective e)
        (centralProj_ker e) hZ3 (hH _ hlist), hZ3⟩))
  | sporadic s =>
    exact Or.inr (Or.inr (Or.inr ⟨_, k2HatIndex_of_k2 hi hlist,
      maximalOddCover_of_oddBound _ hQ (centralProj e) (centralProj_surjective e)
        (centralProj_ker e) hZ3 (hH _ hlist), hZ3⟩))

theorem catalogIs_imp_k3Cover (hM : ListedMultiplierBound p) (hH : HatOddMultiplierBound)
    {Q : Type} [Group Q] [Finite Q] (hQ : CFSG.Open.IsQuasisimple Q)
    (hZ : IsPGroup p (Subgroup.center Q)) (h : catalogIs (Q ⧸ Subgroup.center Q) (k3 p)) :
    K3Cover p Q := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  refine ⟨hQ, ?_⟩
  by_cases hbot : Subgroup.center Q = ⊥
  · exact Or.inl (simpleCoverList_of_center_eq_bot hbot ⟨i, hi, ⟨e⟩⟩)
  obtain ⟨hp3, hZ3, hlist⟩ := hM i (Or.inr hi) Q hQ (centralProj e) (centralProj_surjective e)
    (centralProj_ker e) hZ hbot
  subst hp3
  have hmain : ∀ (j : TauCeti.ValidLieTypeIndex),
      ∀ e' : Q ⧸ Subgroup.center Q ≃* (TauCeti.CFSGIndex.lie j).Group,
        k3 3 (TauCeti.CFSGIndex.lie j) → CoverListed (TauCeti.CFSGIndex.lie j) →
          K3LinearCover 3 Q := by
    rintro ⟨d, hv⟩ e' hi' hlist'
    rcases coverListed_lie hlist' with ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl, hq2⟩
    · have hfl := fullLinearCover_false_of_cover hM q hv (Or.inr hi')
        (three_dvd_card_sub_one_of_listed (Or.inr hi')) hQ e' hZ3
      obtain ⟨-, h6⟩ := hi'
      have h6' : q.card % 6 = 1 := h6
      rw [TauCeti.PrimePower.card_def] at h6' hfl
      exact ⟨rfl, q.p, q.exponent, q.prime_p, q.exponent_pos, Or.inl ⟨h6', hfl⟩⟩
    · have hfl := fullLinearCover_true_of_cover hM q hv (Or.inr hi')
        (three_dvd_card_add_one_of_listed (Or.inr hi')) hQ e' hZ3
      obtain ⟨-, h6⟩ := hi'
      have h6' : q.card % 6 = 5 := h6
      rw [TauCeti.PrimePower.card_def] at h6' hfl
      exact ⟨rfl, q.p, q.exponent, q.prime_p, q.exponent_pos, Or.inr ⟨h6', hfl⟩⟩
    · exact (hi'.2 : False).elim
  cases i with
  | cyclic _ _ => exact hi.elim
  | lie j => exact Or.inr (Or.inl (hmain j e hi hlist))
  | alternating n hn =>
    exact Or.inr (Or.inr ⟨_, k3HatIndex_of_k3 hi hlist,
      maximalOddCover_of_oddBound _ hQ (centralProj e) (centralProj_surjective e)
        (centralProj_ker e) hZ3 (hH _ hlist), hZ3⟩)
  | sporadic s =>
    exact Or.inr (Or.inr ⟨_, k3HatIndex_of_k3 hi hlist,
      maximalOddCover_of_oddBound _ hQ (centralProj e) (centralProj_surjective e)
        (centralProj_ker e) hZ3 (hH _ hlist), hZ3⟩)

end CFSG.LocalAnalysis.GLTheoremA
