module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.ExceptionalModels
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.Adapters.TauCetiExceptional.B1Exceptional
public import CFSG.Models.Blueprint
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3

open CFSG CFSG.Open Subgroup
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)

theorem kd291_not_dvd_lieOrderDivisor {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (t : StatedLieTag)
    (n : ℕ) {f : ℕ} (hf : 1 ≤ f) : ¬ p ∣ lieOrderDivisor t n (p ^ f) := by
  have hn1 : ¬ p ∣ 1 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hn2 : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hn3 : ¬ p ∣ 3 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hn4 : ¬ p ∣ 4 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hq : p ∣ p ^ f := dvd_pow_self p (by omega)
  have hpf : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  cases t
  case PSL =>
    intro h
    have h' : p ∣ Nat.gcd n (p ^ f - 1) := h
    have h1 : p ∣ p ^ f - 1 := dvd_trans h' (Nat.gcd_dvd_right _ _)
    have h2 : p ∣ p ^ f - 1 + 1 := by rw [Nat.sub_add_cancel hpf]; exact hq
    exact hn1 ((Nat.dvd_add_right h1).mp h2)
  case PSU =>
    intro h
    have h' : p ∣ Nat.gcd n (p ^ f + 1) := h
    have h1 : p ∣ p ^ f + 1 := dvd_trans h' (Nat.gcd_dvd_right _ _)
    exact hn1 ((Nat.dvd_add_right hq).mp h1)
  case PSp =>
    intro h
    have h' : p ∣ Nat.gcd 2 (p ^ f - 1) := h
    exact hn2 (dvd_trans h' (Nat.gcd_dvd_left _ _))
  case POmegaOdd =>
    intro h
    have h' : p ∣ 2 := h
    exact hn2 h'
  case POmegaPlus =>
    intro h
    have h' : p ∣ Nat.gcd 4 ((p ^ f) ^ n - 1) := h
    exact hn4 (dvd_trans h' (Nat.gcd_dvd_left _ _))
  case POmegaMinus =>
    intro h
    have h' : p ∣ Nat.gcd 4 ((p ^ f) ^ n + 1) := h
    exact hn4 (dvd_trans h' (Nat.gcd_dvd_left _ _))
  case E6 =>
    intro h
    have h' : p ∣ Nat.gcd 3 (p ^ f - 1) := h
    exact hn3 (dvd_trans h' (Nat.gcd_dvd_left _ _))
  case E7 =>
    intro h
    have h' : p ∣ Nat.gcd 2 (p ^ f - 1) := h
    exact hn2 (dvd_trans h' (Nat.gcd_dvd_left _ _))
  case twistedE6 =>
    intro h
    have h' : p ∣ Nat.gcd 3 (p ^ f + 1) := h
    exact hn3 (dvd_trans h' (Nat.gcd_dvd_left _ _))
  all_goals (intro h; exact hn1 h)

theorem kd291_four_le_pRank_of_lieModel {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {L : Type} [Group L]
    [Finite L]
    {t : StatedLieTag} {n f : ℕ} (hf : 5 ≤ f)
    (h : CFSG.Blueprint.LieModel L t n p f) : 4 ≤ Open.pRank p (⊤ : Subgroup L) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hadm := h.admissible
  rcases h with ⟨-, hcl⟩ | ⟨-, ht, hmod⟩ | ⟨-, ht, hmod⟩ | ⟨-, rfl, -⟩
  ·
    obtain ⟨-, -, hcases⟩ := CFSG.SectionRank.classical_model_rank (by omega) hcl
    rcases hcases with ⟨-, h1 | h1 | h1⟩ | ⟨-, h1 | h1⟩ | ⟨-, h1 | h1⟩ | h1 <;> omega
  ·
    have hcases : t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6 ∨
        t = .trialityD4 := by
      revert ht; cases t <;> decide
    obtain ⟨-, hm⟩ := hmod
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h2 : CFSG.Blueprint.UntwistedChevalleyModel L .G2 (p ^ f) := hm
      have := CFSG.SectionRank.three_mul_le_pRank_of_G2Model h2
      omega
    · have h2 : CFSG.Blueprint.UntwistedChevalleyModel L .F4 (p ^ f) := hm
      have := CFSG.SectionRank.four_mul_le_pRank_of_untwistedModel (by simp) h2
      omega
    · have h2 : CFSG.Blueprint.UntwistedChevalleyModel L .E6 (p ^ f) := hm
      have := CFSG.SectionRank.four_mul_le_pRank_of_untwistedModel (by simp) h2
      omega
    · have h2 : CFSG.Blueprint.UntwistedChevalleyModel L .E7 (p ^ f) := hm
      have := CFSG.SectionRank.four_mul_le_pRank_of_untwistedModel (by simp) h2
      omega
    · have h2 : CFSG.Blueprint.UntwistedChevalleyModel L .E8 (p ^ f) := hm
      have := CFSG.SectionRank.four_mul_le_pRank_of_untwistedModel (by simp) h2
      omega
    · have h2 : CFSG.Blueprint.TwistedChevalleyModel L .E6 (p ^ f) := hm
      exact CFSG.SectionRank.four_le_pRank_of_twistedE6Model (by omega) h2
    · have h2 : CFSG.Blueprint.TwistedChevalleyModel L .D4 (p ^ f) := hm
      exact CFSG.SectionRank.four_le_pRank_of_trialityD4Model (by omega) h2
  ·
    exfalso
    have hcases : t = .twistedG2 ∨ t = .twistedF4 ∨ t = .Tits := by
      revert ht; cases t <;> decide
    rcases hcases with rfl | rfl | rfl
    · obtain ⟨-, -, -, hp3, -, -⟩ := hadm
      omega
    · obtain ⟨-, -, -, hp2, -, -⟩ := hadm
      omega
    · obtain ⟨-, -, -, hp2, -⟩ := hadm
      omega
  ·
    exfalso
    obtain ⟨-, -, -, hp2, -, -⟩ := hadm
    omega

theorem kd291_aux_LM_exceptional {L : Type} [Group L] {t : StatedLieTag} {p f : ℕ}
    (ht : t ∈ CFSG.Blueprint.chevalleyExceptionalTags)
    (hm : CFSG.Blueprint.ChevalleyExceptionalModel L t p f) :
    CFSG.Blueprint.LieModel L t 0 p f :=
  Or.inr (Or.inl ⟨rfl, ht, hm⟩)

theorem kd291_lieModel_of_charp {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {L : Type} [Group L]
    (d : TauCeti.ValidLieTypeIndex) (hd : d.1.characteristic = p)
    (e : L ≃* (TauCeti.CFSGIndex.lie d).Group) :
    ∃ (t : StatedLieTag) (n f : ℕ), t ≠ .Tits ∧ CFSG.Blueprint.LieModel L t n p f := by
  obtain ⟨idx, hv⟩ := d
  cases idx with
  | A r q =>
    have hd' : q.p = p := (TauCeti.LieTypeIndex.characteristic_A r q).symm.trans hd
    subst hd'
    exact ⟨.PSL, r + 1, q.exponent, by decide,
      CFSG.Models.LieModel.toBlueprint (by decide) (CFSG.Models.lieModel_A r q hv e)⟩
  | twistedA r q =>
    have hc : (TauCeti.LieTypeIndex.twistedA r q).characteristic = p := hd
    subst hc
    exact ⟨.PSU, r + 1, TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩,
      by decide, CFSG.Models.LieModel.toBlueprint (by decide)
        (CFSG.Models.lieModel_twistedA r q hv e)⟩
  | B r q =>
    have hd' : q.p = p := (TauCeti.LieTypeIndex.characteristic_B r q).symm.trans hd
    subst hd'
    rcases CFSG.Models.lieModel_B r q hv e with h | h
    · exact ⟨.PSp, r, q.exponent, by decide, CFSG.Models.LieModel.toBlueprint (by decide) h⟩
    · exact ⟨.POmegaOdd, r, q.exponent, by decide,
        CFSG.Models.LieModel.toBlueprint (by decide) h⟩
  | C r q =>
    have hd' : q.p = p := (TauCeti.LieTypeIndex.characteristic_C r q).symm.trans hd
    subst hd'
    exact ⟨.PSp, r, q.exponent, by decide,
      CFSG.Models.LieModel.toBlueprint (by decide) (CFSG.Models.lieModel_C r q hv e)⟩
  | D r q =>
    have hd' : q.p = p := (TauCeti.LieTypeIndex.characteristic_D r q).symm.trans hd
    subst hd'
    exact ⟨.POmegaPlus, r, q.exponent, by decide,
      CFSG.Models.LieModel.toBlueprint (by decide) (CFSG.Models.lieModel_D r q hv e)⟩
  | twistedD r q =>
    have hd' : q.p = p := (TauCeti.LieTypeIndex.characteristic_twistedD r q).symm.trans hd
    subst hd'
    exact ⟨.POmegaMinus, r, q.exponent, by decide,
      CFSG.Models.LieModel.toBlueprint (by decide) (CFSG.Models.lieModel_twistedD r q hv e)⟩
  | E6 q =>
    have hd' : q.p = p := (TauCeti.LieTypeIndex.characteristic_E6 q).symm.trans hd
    subst hd'
    have hq : q.p ≠ 2 := by omega
    exact ⟨.E6, 0, q.exponent, by decide,
      kd291_aux_LM_exceptional (t := .E6) (p := q.p) (f := q.exponent) (by decide)
        ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
          CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.chevalleyBridges.e6
            q hv hq e⟩⟩
  | E7 q =>
    have hd' : q.p = p := (TauCeti.LieTypeIndex.characteristic_E7 q).symm.trans hd
    subst hd'
    have hq : q.p ≠ 2 := by omega
    exact ⟨.E7, 0, q.exponent, by decide,
      kd291_aux_LM_exceptional (t := .E7) (p := q.p) (f := q.exponent) (by decide)
        ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
          CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.chevalleyBridges.e7
            q hv hq e⟩⟩
  | E8 q =>
    have hd' : q.p = p := (TauCeti.LieTypeIndex.characteristic_E8 q).symm.trans hd
    subst hd'
    have hq : q.p ≠ 2 := by omega
    exact ⟨.E8, 0, q.exponent, by decide,
      kd291_aux_LM_exceptional (t := .E8) (p := q.p) (f := q.exponent) (by decide)
        ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
          CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.chevalleyBridges.e8
            q hv hq e⟩⟩
  | F4 q =>
    have hd' : q.p = p := (TauCeti.LieTypeIndex.characteristic_F4 q).symm.trans hd
    subst hd'
    have hq : q.p ≠ 2 := by omega
    exact ⟨.F4, 0, q.exponent, by decide,
      kd291_aux_LM_exceptional (t := .F4) (p := q.p) (f := q.exponent) (by decide)
        ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
          CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.chevalleyBridges.f4
            q hv hq e⟩⟩
  | G2 q =>
    have hd' : q.p = p := (TauCeti.LieTypeIndex.characteristic_G2 q).symm.trans hd
    subst hd'
    have hq : q.p ≠ 2 := by omega
    have h3 : 3 ≤ q.p ^ q.exponent :=
      Nat.le_trans (by omega : 3 ≤ q.p) (Nat.le_self_pow q.exponent_pos.ne' q.p)
    exact ⟨.G2, 0, q.exponent, by decide,
      kd291_aux_LM_exceptional (t := .G2) (p := q.p) (f := q.exponent) (by decide)
        ⟨⟨q.prime_p, q.exponent_pos, rfl, h3⟩,
          CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.chevalleyBridges.g2
            q hv hq e⟩⟩
  | twistedE6 q =>
    have hd' : q.p = p := (TauCeti.LieTypeIndex.characteristic_twistedE6 q).symm.trans hd
    subst hd'
    have hq : q.p ≠ 2 := by omega
    exact ⟨.twistedE6, 0, q.exponent, by decide,
      kd291_aux_LM_exceptional (t := .twistedE6) (p := q.p) (f := q.exponent) (by decide)
        ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
          CFSG.TauCetiBridge.twistedModel_of_bridge
            CFSG.TauCetiBridge.chevalleyBridges.twistedE6 q hv hq (by decide) e⟩⟩
  | trialityD4 q =>
    have hd' : q.p = p := (TauCeti.LieTypeIndex.characteristic_trialityD4 q).symm.trans hd
    subst hd'
    have hq : q.p ≠ 2 := by omega
    exact ⟨.trialityD4, 0, q.exponent, by decide,
      kd291_aux_LM_exceptional (t := .trialityD4) (p := q.p) (f := q.exponent) (by decide)
        ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
          CFSG.TauCetiBridge.twistedModel_of_bridge
            CFSG.TauCetiBridge.chevalleyBridges.trialityD4 q hv hq (by decide) e⟩⟩
  | suzuki m =>
    exfalso
    have h2 : (2 : ℕ) = p := (TauCeti.LieTypeIndex.characteristic_suzuki m).symm.trans hd
    omega
  | reeG2 m =>
    exfalso
    have h3 : (3 : ℕ) = p := (TauCeti.LieTypeIndex.characteristic_reeG2 m).symm.trans hd
    omega
  | reeF4 m =>
    exfalso
    have h2 : (2 : ℕ) = p := (TauCeti.LieTypeIndex.characteristic_reeF4 m).symm.trans hd
    omega
  | tits =>
    exfalso
    have h2 : (2 : ℕ) = p := TauCeti.LieTypeIndex.characteristic_tits.symm.trans hd
    omega

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3
