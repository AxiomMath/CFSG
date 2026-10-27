module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighDiagLinear
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighDiagField

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh2

open CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding
  CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh

@[expose] def SeitzGoodOuterHighUnitaryDiag : Prop :=
  SeitzGoodOuterHighAt fun d p =>
    ∃ (m : ℕ) (q : TauCeti.PrimePower), d.1 = .twistedA m q ∧ p ∣ Nat.gcd (m + 1) (q.card + 1)

@[expose] def SeitzGoodOuterHighD4Three : Prop :=
  SeitzGoodOuterHighAt fun d p => p = 3 ∧ ∃ q : TauCeti.PrimePower, d.1 = .D 4 q

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel in
@[expose] def SeitzGoodOuterHighUnitaryInndiag : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (m : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA m q).Valid), p ∣ Nat.gcd (m + 1) (q.card + 1) →
    p ≠ q.p → ¬ P1ThreeLieList p ⟨.twistedA m q, hv⟩ → ¬ ExcIndex p (.twistedA m q) →
    ∀ (K : Type) [Field K] (h : UnitaryFieldData q.p q.exponent K),
    (∃ F : Subgroup (primeFormP h (idGram K (m + 1))), IsElemAbelian p F ∧ Nat.card F = p ^ 3) →
    ∀ E : Subgroup (MulAut (primeFormP h (idGram K (m + 1)))), IsElemAbelian p E →
      Nat.card E = p ^ 3 → E ≤ primeFormD h (idGram K (m + 1)) →
      ¬ E ≤ (MulAut.conj : primeFormP h (idGram K (m + 1)) →*
        MulAut (primeFormP h (idGram K (m + 1)))).range →
      seitzHyperGamma p E = ⊤

theorem seitzGoodOuterHighAt_linearDiag (hS : KFactSeitzRankTwo) :
    SeitzGoodOuterHighAt fun d p =>
      ∃ (m : ℕ) (q : TauCeti.PrimePower), d.1 = .A m q ∧ p ∣ Nat.gcd (m + 1) (q.card - 1) := by
  intro p hp hp2 S _ _ _ _ d hP he hpd _ _ _ _ E hE hc _
  obtain ⟨d, hv⟩ := d
  obtain ⟨m, q, hd, hg⟩ := hP
  simp only at hd
  subst hd
  have hpq : p ≠ q.p := by simpa using hpd
  have hpm : p ∣ m + 1 := (Nat.dvd_gcd_iff.1 hg).1
  have hpq1 : p ∣ q.card - 1 := (Nat.dvd_gcd_iff.1 hg).2
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hm : 2 ≤ m := by
    have := Nat.le_of_dvd (by omega) hpm
    omega
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hKq : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  have hcardK : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [hKq, TauCeti.PrimePower.card_def]
  let e : Cat ⟨.A m q, hv⟩ ≃* projectiveSL (m + 1) (GaloisField q.p q.exponent) :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (m + 1) _)
  obtain ⟨ψ⟩ := he
  let θ : S ≃* projectiveSL (m + 1) (GaloisField q.p q.exponent) := ψ.trans e
  have hE' : IsElemAbelian p (E.map (MulAut.congr θ).toMonoidHom) := isElemAbelian_map_congr θ hE
  have hc' : Nat.card (E.map (MulAut.congr θ).toMonoidHom) = p ^ 3 := (card_map_congr θ E).trans hc
  have hpK : (p : GaloisField q.p q.exponent) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff (GaloisField q.p q.exponent) q.p p).1 h
    exact hpq ((Nat.prime_dvd_prime_iff_eq q.prime_p hp).1 this).symm
  have hpK1 : p ∣ Nat.card (GaloisField q.p q.exponent) - 1 := by
    rw [hcardK]
    exact hpq1
  have htop : seitzHyperGamma p (E.map (MulAut.congr θ).toMonoidHom) = ⊤ := by
    by_cases hlin : E.map (MulAut.congr θ).toMonoidHom ≤
        linearAutGroup (m + 1) (GaloisField q.p q.exponent)
    · exact seitzHyperGamma_eq_top_of_le_linearAut (by omega) hp hp2 hpK hpK1 hE' hc' hlin
    · exact seitzHyperGamma_eq_top_of_not_le_linearAut hS hm q.prime_p q.exponent_pos hKq hp hp2
        hpq hpK1 hE' hc' hlin
  exact CFSG.RankThree.PartTwo.Sec4.Res6L364.seitzHyperGamma_eq_top_of_map θ
    (MulAut.congr θ).toMonoidHom (fun a x => by simp [MulAut.congr_apply])
    (MulAut.congr θ).injective htop

section Unitary

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.Classical

theorem excIndex_twistedA_eight_of_dvd {m : ℕ} {q : TauCeti.PrimePower} (hq : q.card = 8)
    (h3 : 3 ∣ m + 1) : ExcIndex 3 (.twistedA m q) := by
  obtain ⟨hp2, he3⟩ := eq_two_three_of_card_eight (by rw [← TauCeti.PrimePower.card_def, hq])
  have hq8 : IsTwoPow q 3 := ⟨hp2, he3⟩
  obtain ⟨k, hk⟩ := h3
  refine Or.inr ⟨rfl, ?_⟩
  rcases (by omega : k = 1 ∨ k = 2 ∨ 3 ≤ k) with rfl | rfl | hk3
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hq8, Or.inl (by omega)⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hq8, Or.inr (by omega)⟩)))))
  · exact Or.inr (Or.inl ⟨Or.inr hq8, k, hk3, hk⟩)

theorem seitzGoodOuterHighUnitaryDiag_of_inndiag
    (hS : KFactSeitzRankTwo) (hI : SeitzGoodOuterHighUnitaryInndiag) :
    SeitzGoodOuterHighUnitaryDiag := by
  intro p hp hp2 S _ _ _ _ d hP he hpd hl hx _ hcube E hE hc hout
  obtain ⟨d, hv⟩ := d
  obtain ⟨m, q, hd, hg⟩ := hP
  simp only at hd
  subst hd
  have hpq : p ≠ q.p := by simpa using hpd
  have hpm : p ∣ m + 1 := (Nat.dvd_gcd_iff.1 hg).1
  have hpq1 : p ∣ q.card + 1 := (Nat.dvd_gcd_iff.1 hg).2
  have hm : 2 ≤ m := TauCeti.LieTypeIndex.two_le_of_twistedA_inStandardRange
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  obtain ⟨-, -, -, hne, K, _, h, ⟨θ₀⟩⟩ := exists_primeFormP_of_statedClassicalModel_PSU
    (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m q hv (MulEquiv.refl _))
  obtain ⟨ψ⟩ := he
  let θ := ψ.trans θ₀
  have hE' : IsElemAbelian p (E.map (MulAut.congr θ).toMonoidHom) := isElemAbelian_map_congr θ hE
  have hc' : Nat.card (E.map (MulAut.congr θ).toMonoidHom) = p ^ 3 := (card_map_congr θ E).trans hc
  have htop : seitzHyperGamma p (E.map (MulAut.congr θ).toMonoidHom) = ⊤ := by
    by_cases hD : E.map (MulAut.congr θ).toMonoidHom ≤ primeFormD h (idGram K (m + 1))
    · refine hI p hp hp2 m q hv hg hpq hl hx K h ?_ _ hE' hc' hD
        (not_le_range_conj_map_congr θ hout)
      obtain ⟨F, hF, hFc⟩ := hcube
      exact ⟨F.map θ.toMonoidHom, CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hF _,
        by rw [Subgroup.card_map_of_injective θ.injective, hFc]⟩
    · have hq8 : ¬ (p = 3 ∧ q.p ^ q.exponent = 8) := by
        rintro ⟨rfl, h8⟩
        exact hx (excIndex_twistedA_eight_of_dvd (by rw [TauCeti.PrimePower.card_def]; exact h8)
          hpm)
      have hpq1' : p ∣ q.p ^ q.exponent + 1 := by
        rw [← TauCeti.PrimePower.card_def]
        exact hpq1
      exact seitzHyperGamma_eq_top_of_not_le_primeFormD hS h hm hne hp hp2 hpq hpq1' hq8 hE' hc' hD
  exact CFSG.RankThree.PartTwo.Sec4.Res6L364.seitzHyperGamma_eq_top_of_map θ
    (MulAut.congr θ).toMonoidHom (fun a x => by simp [MulAut.congr_apply])
    (MulAut.congr θ).injective htop

end Unitary

theorem seitzGoodOuterHighClassicalDiag_of_rest
    (hS : KFactSeitzRankTwo) (hU : SeitzGoodOuterHighUnitaryDiag)
    (hD : SeitzGoodOuterHighD4Three) : SeitzGoodOuterHighClassicalDiag :=
  SeitzGoodOuterHighAt.of_cover (fun _ _ h => h) (seitzGoodOuterHighAt_linearDiag hS)
    (SeitzGoodOuterHighAt.of_cover (fun _ _ h => h) hU hD)

theorem seitzGoodOuterHighClassicalDiag_of_inndiag
    (hS : KFactSeitzRankTwo) (hI : SeitzGoodOuterHighUnitaryInndiag)
    (hD : SeitzGoodOuterHighD4Three) : SeitzGoodOuterHighClassicalDiag :=
  seitzGoodOuterHighClassicalDiag_of_rest hS (seitzGoodOuterHighUnitaryDiag_of_inndiag hS hI) hD

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh2

end
