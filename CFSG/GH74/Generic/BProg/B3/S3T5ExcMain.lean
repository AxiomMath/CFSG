module

public import CFSG.GH74.Generic.BProg.B3.S3T5Exc
public import CFSG.GH74.Generic.BProg.B3.S3T2A15
public import CFSG.GH74.Generic.BProg.B3.S3T5Main
public import CFSG.GH74.Generic.BProg.B3.S3T5AnBal
public import CFSG.GH74.Generic.BProg.B3.S3T5L3

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3T5X

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  Subgroup
open CFSG.GH74.Generic.S3 (IsExcB2 ExcOrder excOrder_alternating)
open scoped MatrixGroups

theorem isExcB2_of_center (hF : GenericKnownFacts) {G : Type} [Group G] [Finite G]
    {X J : Subgroup G} (hJ : IsPCompIn 2 X J) {n : ℕ} (hn7 : 7 ≤ n) (hn11 : n ≤ 11)
    (hA : Nonempty (kBar J ⧸ center (kBar J) ≃* alternatingGroup (Fin n)))
    (hZ : center (kBar J) ≠ ⊥) : IsExcB2 (kBar J) := by
  have hq : IsQuasisimple (kBar J) := TwoThin.isQuasisimple_hat hJ
  have hO : pPrimeCore 2 (kBar J) = ⊥ := CFSG.GH74.GLS.pPrimeCore_quotient_eq_bot ↥J
  have hZ2 : IsPGroup 2 ↥(center (kBar J)) :=
    (isPGroup_two_center_of_subnormal hO Subgroup.IsSubnormal.top).of_equiv
      (Subgroup.centerCongr Subgroup.topEquiv)
  have hle := hF.alt_cover n hn7 hn11 (kBar J) hq hZ2 hA
  have hcard : Nat.card (center (kBar J)) = 2 := by
    have := (Subgroup.one_lt_card_iff_ne_bot (center (kBar J))).2 hZ
    omega
  have hcov : IsDoubleCoverOfAlt (kBar J) n := ⟨hq, hcard, hA⟩
  refine ⟨⟨⟨hq, Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn7, hn11, hcov⟩)))⟩, hZ⟩, ?_⟩
  rintro ⟨F, _, _, -, ⟨e⟩⟩
  obtain ⟨eA⟩ := hA
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center (kBar J))
  rw [hcard, Nat.card_congr eA.toEquiv] at h1
  have h2 : Nat.card (kBar J) = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, ← Nat.card_congr (specialLinearGroupEquivStatedSL 2 F).toEquiv,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  exact ExcOrder.two_mul_ne (excOrder_alternating hn7 hn11) (Nat.card F)
    (by rw [← h2, h1, mul_comm])

section Leaves

theorem centerA11_proved
    : ∀ (G : Type) [Group G] [Finite G], S3T2A15.CenterA11 G := by
  intro G _ _ x K hyp _ hc h3 t J hJ hA
  by_contra hZ
  exact false_of_excB2Pair hyp hc h3 hJ (isExcB2_of_center (genericKnownFacts_of_griess
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds) hJ.2.2 (by norm_num)
    le_rfl hA hZ)

theorem centerA7_proved
    : ∀ (G : Type) [Group G] [Finite G], S3T2A15.CenterA7 G := by
  intro G _ _ x K hyp _ hc h3 t J hJ hA
  by_contra hZ
  exact false_of_excB2Pair hyp hc h3 hJ (isExcB2_of_center (genericKnownFacts_of_griess
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds) hJ.2.2 le_rfl
    (by norm_num) hA hZ)

theorem noTwoA11Obs52_proved
    : ∀ (G : Type) [Group G] [Finite G], S3T5.NoTwoA11Obs52 G := by
  intro G _ _ x K A B b D J hyp hnoAlt hc hSD hsrc hext hB4 h hcov
  have h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K) := by
    obtain ⟨p, f, hp, hp2, hq, hL | hU⟩ := hSD
    · exact ⟨p, f, hp, hp2, hq, Or.inl hL.1⟩
    · exact ⟨p, f, hp, hp2, hq, Or.inr hU.1⟩
  have hILo : IsILo 2 b J := by
    refine ⟨h.b_ord, ?_, h.comp⟩
    calc oBound 2 = 3 := rfl
      _ ≤ pRank 2 ↥B := by omega
      _ ≤ pRank 2 ↥(centralizer ({b} : Set G)) :=
        C3.Layer1.Back.pRank_mono' (S3T5.W.B_le_centralizer h)
  have hZ : center (↥J ⧸ pPrimeCore 2 ↥J) ≠ ⊥ := by
    intro hbot
    have h2 := hcov.2.1
    rw [hbot, Subgroup.card_bot] at h2
    exact absurd h2 (by norm_num)
  exact hZ (centerA11_proved G x K hyp hnoAlt hc h3 b J hILo hcov.2.2)

theorem tab52w_proved
    : ∀ (G : Type) [Group G] [Finite G], Tab52w G := fun G _ _ =>
  S3T5.tab52w_of_leaves altLocBal2_proved S3T5L3.l3OuterOddCore_proved (noTwoA11Obs52_proved G)

end Leaves

end S3T5X

end CFSG.GH74.Generic.BProg.B3
