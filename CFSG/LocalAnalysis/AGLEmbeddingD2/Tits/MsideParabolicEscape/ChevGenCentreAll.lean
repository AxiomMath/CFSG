module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenThree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenMult
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGenSU
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeCatalog

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.GN
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabHub.ParabThreeInv CFSG.QuasithinUnique
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg

section Generic

variable {W : Type} [Group W] [Finite W] {S₀ : Subgroup W}

theorem psSet_of_family {L : Subgroup W} {m : ℕ} {Q : Subgroup W → Prop}
    {P : Fin m → Subgroup W}
    (hmin : ∀ i, CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsMinOverBorel L S₀ (P i))
    (hgen : L = ⨆ i, pElementSubgroup 2 (P i)) (hQ : ∀ i, Q (P i)) :
    ∃ Ps : Set (Subgroup W), (∀ P ∈ Ps, IsMinOverBorel L S₀ P) ∧
      L = ⨆ P ∈ Ps, pElementSubgroup 2 P ∧ ∀ P ∈ Ps, Q P := by
  refine ⟨Set.range P, ?_, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact hmin i
  · rw [hgen]
    refine le_antisymm (iSup_le fun i => ?_) (iSup₂_le fun Q hQ => ?_)
    · exact le_iSup₂ (f := fun (Q : Subgroup W) (_ : Q ∈ Set.range P) => pElementSubgroup 2 Q)
        (P i) ⟨i, rfl⟩
    · obtain ⟨i, rfl⟩ := hQ
      exact le_iSup (fun i => pElementSubgroup 2 (P i)) i
  · rintro _ ⟨i, rfl⟩
    exact hQ i

theorem centre_of_three_of_noFive {L : Subgroup W} {Ps : Set (Subgroup W)}
    (h3 : ∀ P ∈ Ps, ∃ x ∈ pElementSubgroup 2 P, orderOf x = 3 ∧
      x ∉ (Subgroup.center ↥L).map L.subtype)
    (h5 : ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ Nat.card (Subgroup.center ↥L)) :
    ∀ P ∈ Ps, ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card (Subgroup.center ↥L) →
      ∃ x ∈ pElementSubgroup 2 P, orderOf x = p ∧ x ∉ (Subgroup.center ↥L).map L.subtype := by
  intro P hP p hp hp2 hpZ
  by_cases hp3 : p = 3
  · subst hp3
    exact h3 P hP
  · exfalso
    refine h5 p hp ?_ hpZ
    have := hp.two_le
    have h4 : p ≠ 4 := by rintro rfl; exact absurd hp (by norm_num)
    omega

end Generic


set_option linter.unusedSectionVars false


theorem kFactChevGenCentre_of_griess (hGA : CFSG.Open.GriessAllModelsStatement) :
    KFactChevGenCentre := by
  intro Y _ _ L S₀ hL hcl hS
  by_cases h5 : ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ∣ Nat.card (Subgroup.center ↥L)
  · obtain ⟨Ps, hmin, hgen, h3⟩ := kFactChevGenThree_proved Y L S₀ hL hcl hS
    exact ⟨Ps, hmin, hgen, centre_of_three_of_noFive h3 h5⟩
  · push_neg at h5
    obtain ⟨p5, hp5, hp5ge, hp5Z⟩ := h5
    have hcl' := hcl
    rcases hcl with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, hdq, ⟨e⟩⟩
    · obtain ⟨dd, hv⟩ := d
      cases dd with
      | A r q =>
        change q.p = 2 at hd
        have : Fact q.p.Prime := ⟨q.prime_p⟩
        have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hd
        have hmod := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
        rw [hd] at hmod
        have hK : Nat.card (GaloisField q.p q.exponent) = 2 ^ q.exponent := by
          rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', hd]
        obtain ⟨P, hmin, hgen, hcen⟩ := chevGen_centre_of_nodes hL hS
          (borelQuotient_sl
            ((CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv).symm.trans e.symm))
          (fun i => HasSL2Node.hasInvolThree (hasSL2Node_sl i))
          (fun i p hp hp5 hpZ => oddNode_of_hasSL2Node (hasSL2Node_sl i) hp (by omega) (by
            rw [hK]
            exact (centre_dvd_psl hGA hL (MulEquiv.refl _) ⟨hmod.1, Or.inl hmod⟩ hp hp5 hpZ).trans
              (CFSG.AGLEmbedding.ParabPrime.sub_one_dvd_and_add_one_dvd _ Nat.one_le_two_pow).1))
        exact psSet_of_family hmin hgen hcen
      | twistedA r q =>
        change q.p = 2 at hd
        have hmod := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
        rw [hd] at hmod
        have hmod' := hmod
        obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e'⟩⟩ := hmod
        have := Fintype.ofFinite F
        have : CharP F 2 := charP_of_card_eq_prime_pow (f := q.exponent * 2)
          (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
        obtain ⟨ζ, hζ⟩ := CFSG.LieType.Universal.Unitary.exists_traceZero_ne_zero hcard
        obtain ⟨P, hmin, hgen, hcen⟩ := chevGen_centre_of_nodes hL hS
          (borelQuotient_su hcard (by omega) ζ hζ e')
          (fun i => hasInvolThree_su hcard i)
          (fun i p hp hp5 hpZ => oddNode_su hcard hn i hp (by omega)
            (centre_dvd_psu hGA hL (MulEquiv.refl _) ⟨hmod'.1, Or.inl hmod'⟩ hp hp5 hpZ))
        exact psSet_of_family hmin hgen hcen
      | B r q =>
        exfalso
        change q.p = 2 at hd
        have hr := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
          ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
        by_cases h2 : r = 2
        · subst h2
          have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
          rw [hd] at h
          exact centre_false_of_tag hGA hL (MulEquiv.refl _) (Or.inl rfl) ⟨h.1, Or.inl h⟩ hp5 hp5ge
            hp5Z
        · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hd
            (by omega) e
          rw [hd] at h
          exact centre_false_of_tag hGA hL (MulEquiv.refl _) (Or.inl rfl) ⟨h.1, Or.inl h⟩ hp5 hp5ge
            hp5Z
      | C r q => exact hd.elim
      | D r q =>
        exfalso
        change q.p = 2 at hd
        have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hd e
        rw [hd] at h
        exact centre_false_of_tag hGA hL (MulEquiv.refl _) (Or.inr (Or.inl rfl)) ⟨h.1, Or.inl h⟩
          hp5 hp5ge hp5Z
      | twistedD r q =>
        exfalso
        change q.p = 2 at hd
        have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hd e
        rw [hd] at h
        exact centre_false_of_tag hGA hL (MulEquiv.refl _) (Or.inr (Or.inr (Or.inl rfl)))
          ⟨h.1, Or.inl h⟩ hp5 hp5ge hp5Z
      | G2 q =>
        exfalso
        change q.p = 2 at hd
        have hq3 : 3 ≤ q.card :=
          (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
        have hcard : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hd]
        have hL' : CFSG.Models.LieModel (↥L ⧸ Subgroup.center ↥L) .G2 0 2 q.exponent :=
          ⟨⟨Nat.prime_two, q.exponent_pos, rfl, by rw [← hcard]; exact hq3⟩,
            Or.inr ⟨rfl, ⟨⟨.G2 q, hv⟩, ⟨hd, rfl⟩, ⟨e⟩⟩⟩⟩
        exact centre_false_of_tag hGA hL (MulEquiv.refl _)
          (Or.inr (Or.inr (Or.inr rfl))) hL' hp5 hp5ge hp5Z
      | _ => exact hd.elim
    · exfalso
      rcases hn with rfl | rfl | rfl
      · exact CFSG.AGLEmbedding.ParabPrime.not_dvd_card_center_alt hL (Or.inl rfl) e hp5 hp5ge hp5Z
      · exact CFSG.AGLEmbedding.ParabPrime.not_dvd_card_center_alt hL (Or.inr rfl) e hp5 hp5ge hp5Z
      · have hL8 : CFSG.Blueprint.LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 4 2 1 :=
          (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff _).2 ⟨e⟩
        rcases hL8 with ⟨-, h⟩ | ⟨hn, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
        · have := centre_dvd_psl hGA hL (MulEquiv.refl _) ⟨h.1, Or.inl h⟩ hp5 hp5ge hp5Z
          have h1 : p5 ∣ 1 := by simpa using this
          exact hp5.one_lt.ne' (Nat.dvd_one.1 h1)
        all_goals exact absurd hn (by norm_num)
    · exfalso
      rcases hdq with ⟨q, hq, hdq⟩ | ⟨q, hq, hdq⟩
      · obtain ⟨dd, hv⟩ := d
        simp only at hdq
        subst hdq
        obtain ⟨hp7, hf⟩ := primePower_eq_of_card_eq Nat.prime_seven hq
        have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
        rw [hp7, hf] at h
        have := Nat.le_of_dvd (by norm_num)
          (hp5Z.trans (CFSG.AGLEmbedding.ParabPrime.card_center_dvd_two_of_psl_seven hGA hL h))
        omega
      · obtain ⟨dd, hv⟩ := d
        simp only at hdq
        subst hdq
        obtain ⟨hp3, hf⟩ := primePower_eq_of_card_eq Nat.prime_three hq
        have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
        rw [hp3, hf] at h
        have := Nat.le_of_dvd (by norm_num)
          (hp5Z.trans (CFSG.AGLEmbedding.ParabPrime.card_center_dvd_one_of_psu_three_three hGA hL h))
        omega

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ChevGen
