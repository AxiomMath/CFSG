module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Inputs
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55AltMult
public import CFSG.HardMathSupport.Solomon.Coordinator.T112MCover

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29

open Subgroup

theorem isQuasisimple_of_open_altTriple {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  have hperf : Group.IsPerfect Q := ⟨h.1⟩
  refine ⟨hperf, h.2, ?_⟩
  by_contra hab
  have hcomm : ∀ x y : Q ⧸ center Q, x * y = y * x := by
    intro x y
    by_contra hne
    exact hab ⟨x, y, hne⟩
  have hsimple : IsSimpleGroup (Q ⧸ center Q) := h.2
  have hperf' : Group.IsPerfect (Q ⧸ center Q) :=
    Group.IsPerfect.ofSurjective (G := Q) (G' := Q ⧸ center Q) (f := QuotientGroup.mk' (center Q))
      (QuotientGroup.mk'_surjective _)
  have hbot : _root_.commutator (Q ⧸ center Q) = ⊥ := by
    rw [_root_.commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hcomm y x
  have htop : (⊤ : Subgroup (Q ⧸ center Q)) = ⊥ :=
    (Group.IsPerfect.commutator_eq_top (G := Q ⧸ center Q)).symm.trans hbot
  have := hsimple.toNontrivial
  obtain ⟨x, hx⟩ := exists_ne (1 : Q ⧸ center Q)
  have hxbot : x ∈ (⊥ : Subgroup (Q ⧸ center Q)) := htop ▸ Subgroup.mem_top x
  exact hx (Subgroup.mem_bot.mp hxbot)

theorem card_abelian_le_nine_of_card_dvd {L : Type} [Group L] [Finite L] {A : Subgroup L}
    (hA : IsPGroup 3 A) (hL : Nat.card L ∣ 180) : Nat.card A ≤ 9 := by
  obtain ⟨k, hk⟩ := hA.exists_card_eq
  have hd : Nat.card A ∣ Nat.card L := Subgroup.card_subgroup_dvd_card A
  have h180 : 3 ^ k ∣ 180 := hk ▸ hd.trans hL
  by_contra hlt
  have hk3 : 3 ≤ k := by
    by_contra hk3
    have : k ≤ 2 := by omega
    have : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
    omega
  have h27 : 27 ∣ 3 ^ k := by
    have : 3 ^ 3 ∣ 3 ^ k := pow_dvd_pow 3 hk3
    simpa using this
  have := h27.trans h180
  omega

theorem card_abelian_le_nine_of_sylow {L : Type} [Group L] [Finite L] {A : Subgroup L}
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {R : Subgroup L} (hAR : A ≤ R)
    (h27 : Nat.card R = 27) (hnab : ∃ r ∈ R, ∃ s ∈ R, r * s ≠ s * r) : Nat.card A ≤ 9 := by
  by_contra hlt
  have hd : Nat.card A ∣ 27 := h27 ▸ Subgroup.card_dvd_of_le hAR
  have hA27 : Nat.card A = 27 := by
    have hle : Nat.card A ≤ 27 := Nat.le_of_dvd (by norm_num) hd
    interval_cases h : Nat.card A <;> first | rfl | (exfalso; omega) | skip
    all_goals omega
  have hRA : A = R := Subgroup.eq_of_le_of_card_ge hAR (by omega)
  obtain ⟨r, hr, s, hs, hrs⟩ := hnab
  exact hrs (hAc r (hRA ▸ hr) s (hRA ▸ hs))

theorem altTripleCoverAbelianBound_holds : AltTripleCoverAbelianBound := by
  intro L _ _ hq hZ hAlt A hA hAc
  obtain ⟨n, hn5, ⟨e⟩⟩ := hAlt
  have hcard : Nat.card L = Nat.card (alternatingGroup (Fin n)) * 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center L),
      Nat.card_congr e.toEquiv, hZ]
  by_cases hn8 : 8 ≤ n
  · exfalso
    have hd := CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.card_center_dvd_of_alt
      (isQuasisimple_of_open_altTriple hq) hn5 e
    rw [CFSG.Alternating.Multipliers.card_hopfMultiplier_alternatingGroup hn8, hZ] at hd
    omega
  · have hn : n = 5 ∨ n = 6 ∨ n = 7 := by omega
    obtain ⟨R, hAR⟩ := hA.exists_le_sylow
    rcases hn with rfl | rfl | rfl
    · have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
        rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        decide
      exact card_abelian_le_nine_of_card_dvd hA (by rw [hcard, h60])
    · have hQ : Nat.card (alternatingGroup (Fin 6)) = 3 ^ 2 * 40 := by
        rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        decide
      obtain ⟨h27, hnab, -⟩ := CFSG.HardMathSupport.Solomon.Coordinator.t112m_sylow_cover
        hq.1 hZ e hQ (by norm_num) R
      exact card_abelian_le_nine_of_sylow hAc hAR h27 hnab
    · have hQ : Nat.card (alternatingGroup (Fin 7)) = 3 ^ 2 * 280 := by
        rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        decide
      obtain ⟨h27, hnab, -⟩ := CFSG.HardMathSupport.Solomon.Coordinator.t112m_sylow_cover
        hq.1 hZ e hQ (by norm_num) R
      exact card_abelian_le_nine_of_sylow hAc hAR h27 hnab

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29
