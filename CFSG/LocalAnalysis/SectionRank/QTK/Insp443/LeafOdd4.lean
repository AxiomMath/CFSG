module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.OddGeneric
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.OddCentre
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.ProjSixteen
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.LeafPSp43
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.LeafG2Odd
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Assembly

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Blueprint

@[expose] def O3Facts : Prop :=
  ∀ (ι F : Type) [Fintype ι] [DecidableEq ι] [Field F], (2 : F) ≠ 0 → Fintype.card ι = 4 →
    ∀ H : Subgroup (GL ι F),
      (∀ E : Subgroup (StatedProj H), IsElemAbelian 2 E → Nat.card E ≤ 16) ∧
      ∀ E : Subgroup (StatedProj H), IsElemAbelian 2 E → Nat.card E = 16 →
        ∀ h : H, (QuotientGroup.mk h : StatedProj H) ∈ E →
          (QuotientGroup.mk h : StatedProj H) ≠ 1 → Matrix.trace ((h : GL ι F) : Matrix ι ι F) = 0

@[expose] def U43Covers : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (L V MK : Subgroup K), KConf K L V MK → CentralKer L V →
    StatedClassicalModel (K ⧸ Subgroup.center K) .PSU 4 3 1 → Subgroup.center K ≠ ⊥ →
      ConclK K L V MK

theorem two_ne_zero_of_odd_card {F : Type} [Field F] [Finite F] (hF : Odd (Nat.card F)) :
    (2 : F) ≠ 0 := by
  haveI := Fintype.ofFinite F
  refine Ring.two_ne_zero fun h => ?_
  have h2 := FiniteField.even_card_iff_char_two.mp h
  rw [Fintype.card_eq_nat_card] at h2
  exact (Nat.not_even_iff_odd.mpr hF) (Nat.even_iff.mpr h2)

theorem rankFour_statedProj (hO3 : O3Facts) {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (h2 : (2 : F) ≠ 0) (hι : Fintype.card ι = 4) (H : Subgroup (GL ι F)) :
    (∀ E : Subgroup (StatedProj H), IsElemAbelian 2 E → Nat.card E ≤ 16) ∧
      ∀ E : Subgroup (StatedProj H), IsElemAbelian 2 E → Nat.card E = 16 →
        Subgroup.centralizer (E : Set (StatedProj H)) ≤ E ∧
          ∀ n ∈ Subgroup.normalizer (E : Set (StatedProj H)),
            (∀ x ∈ E, n ^ 7 * x * (n ^ 7)⁻¹ = x) → ∀ x ∈ E, n * x * n⁻¹ = x := by
  obtain ⟨hle, htr⟩ := hO3 ι F h2 hι H
  refine ⟨hle, fun E hE h16 => ?_⟩
  have hspan := span_liftMats_eq_top_of_trace h2 hι h16 (htr E hE h16)
  exact ⟨centralizer_le_of_span_liftMats hE (by rw [h16, hι] <;> norm_num) hspan,
    conj_eq_of_pow_seven_of_span_liftMats hE h16 hspan⟩

theorem KConf.conclK_of_statedProj
    (hO3 : O3Facts)
    {K : Type} [Group K] [Finite K] {L V MK : Subgroup K} (h : KConf K L V MK)
    (hF : CentralKer L V) (hZ : Subgroup.center K = ⊥) {ι F : Type} [Fintype ι]
    [DecidableEq ι] [Field F] (h2 : (2 : F) ≠ 0) (hι : Fintype.card ι = 4)
    {H : Subgroup (GL ι F)} (e : K ⧸ Subgroup.center K ≃* StatedProj H) : ConclK K L V MK := by
  obtain ⟨hle, h16⟩ := rankFour_statedProj hO3 h2 hι H
  let eK : K ≃* StatedProj H :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e
  exact h.conclK_of_rankFour hF (card_le_sixteen_of_mulEquiv eK hle)
    (sixteen_of_mulEquiv eK h16)

theorem forKF_PSp4odd
    (hO3 : O3Facts) :
    ForKF (fun S _ => ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ StatedClassicalModel S .PSp 2 p 1) := by
  intro K _ _ L V MK hK hF ⟨p, hp, hp5, hS⟩
  obtain ⟨-, F, hFld, hFin, hcard, ⟨e⟩⟩ := hS
  letI := hFld
  rw [pow_one] at hcard
  have hZ := center_eq_bot_of_psp4 hK.quasisimple hK.odd_card_center (by omega) e
  exact hK.conclK_of_statedProj hO3 hF hZ
    (two_ne_zero_of_odd_card (by rw [hcard]; exact hp.odd_of_ne_two (by omega))) (by simp) e

theorem forKF_L4odd
    (hO3 : O3Facts) :
    ForKF (fun S _ => ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ StatedClassicalModel S .PSL 4 p 1) := by
  intro K _ _ L V MK hK hF ⟨p, hp, hp2, hS⟩
  obtain ⟨-, F, hFld, hFin, hcard, ⟨e⟩⟩ := hS
  letI := hFld
  rw [pow_one] at hcard
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hZ := center_eq_bot_of_psl4 hK.quasisimple hK.odd_card_center (by omega) e
  exact hK.conclK_of_statedProj hO3 hF hZ
    (two_ne_zero_of_odd_card (by rw [hcard]; exact hp.odd_of_ne_two hp2)) (by simp) e

theorem forKF_U4odd
    (hO3 : O3Facts) :
    ForKF (fun S _ => ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ StatedClassicalModel S .PSU 4 p 1) := by
  intro K _ _ L V MK hK hF ⟨p, hp, hp5, hS⟩
  obtain ⟨-, F, hFld, hFin, hcard, ⟨e⟩⟩ := hS
  letI := hFld
  have hZ := center_eq_bot_of_psu4 hK.quasisimple hK.odd_card_center hcard
    (by rw [pow_one]; omega) (by rw [pow_one]; exact hp.isPrimePow) e
  exact hK.conclK_of_statedProj hO3 hF hZ
    (two_ne_zero_of_odd_card (by rw [hcard]; exact ((hp.odd_of_ne_two (by omega)).pow).pow))
    (by simp) e

theorem forKF_U43
    (hO3 : O3Facts)
    (hU43 : U43Covers) : ForKF (fun S _ => StatedClassicalModel S .PSU 4 3 1) := by
  intro K _ _ L V MK hK hF hS
  by_cases hZ : Subgroup.center K = ⊥
  · obtain ⟨-, F, hFld, hFin, hcard, ⟨e⟩⟩ := hS
    letI := hFld
    exact hK.conclK_of_statedProj hO3 hF hZ
      (two_ne_zero_of_odd_card (by rw [hcard]; decide)) (by simp) e
  · exact hU43 K L V MK hK hF hS hZ

theorem for_PSp4odd
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hO3 : O3Facts) :
    For (fun S _ => ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ StatedClassicalModel S .PSp 2 p 1) := by
  intro G _ _ T M L B Tp VB K hH ⟨p, hp, hp2, hS⟩
  rcases (show p = 3 ∨ 5 ≤ p by
    have := hp.two_le
    rcases (show p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h
    · exact Or.inl h
    · exact absurd (h ▸ hp) (by decide)
    · exact Or.inr h) with rfl | hp5
  · exact for_PSp43 h37 h38 h39 G T M L B Tp VB K hH hS
  · exact For.of_forKF h37 h38 h39 (forKF_PSp4odd hO3) G T M L B Tp VB K hH ⟨p, hp, hp5, hS⟩

theorem for_L4odd
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hO3 : O3Facts) :
    For (fun S _ => ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ (∃ a : ℕ, p = 2 ^ a + 1) ∧
      StatedClassicalModel S .PSL 4 p 1) :=
  For.mono (fun _ _ ⟨p, hp, hp2, _, hS⟩ => ⟨p, hp, hp2, hS⟩)
    (For.of_forKF h37 h38 h39 (forKF_L4odd hO3))

theorem for_U4odd
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hO3 : O3Facts)
    (hU43 : U43Covers) :
    For (fun S _ => ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ (∃ b : ℕ, p + 1 = 2 ^ b) ∧
      StatedClassicalModel S .PSU 4 p 1) := by
  intro G _ _ T M L B Tp VB K hH ⟨p, hp, hp2, _, hS⟩
  rcases (show p = 3 ∨ 5 ≤ p by
    have := hp.two_le
    rcases (show p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h
    · exact Or.inl h
    · exact absurd (h ▸ hp) (by decide)
    · exact Or.inr h) with rfl | hp5
  · exact For.of_forKF h37 h38 h39 (forKF_U43 hO3 hU43) G T M L B Tp VB K hH hS
  · exact For.of_forKF h37 h38 h39 (forKF_U4odd hO3) G T M L B Tp VB K hH ⟨p, hp, hp5, hS⟩

theorem for_itemOdd_of_O3
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hO3 : O3Facts)
    (hU43 : U43Covers) : For ItemOdd :=
  for_itemOdd_of (for_PSp4odd h37 h38 h39 hO3) (for_G2odd h37 h38 h39) (for_L4odd h37 h38 h39 hO3)
    (for_U4odd h37 h38 h39 hO3 hU43)

end CFSG.SectionRank.QTK.Insp443

end
