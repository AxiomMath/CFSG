module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.InndiagInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.InndiagLinear
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.InndiagExc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Basic
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeBstar
public import CFSG.LocalAnalysis.StandardType.GGSmallKGInputsTwE6
public import CFSG.RankThree.PartOne.F106.OddRadTools
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicExcTw
public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicExcSz
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestG2
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTwF4
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.Quasithin.G2U

private theorem rk2_labelAll_self (lab : GLALabel) :
    Rk2LabelAll lab fun R _ I F => ∀ Q' : CFSG.Assembly.LargeEvenRawCont,
      Q' R I F → GLARawDatum lab Q' := by
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  cases t <;> dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
  all_goals try split_ifs at hQ ⊢
  all_goals first
    | (obtain ⟨K, i1, i2, hK, b, c, hbc, hq⟩ := hQ
       exact ⟨K, i1, i2, hK, b, c, hbc,
         ⟨hq, fun Q' hQ' => ⟨K, i1, i2, hK, b, c, hbc, hQ'⟩⟩⟩)
    | (obtain ⟨K, i1, i2, hK, hq⟩ := hQ
       exact ⟨K, i1, i2, hK, ⟨hq, fun Q' hQ' => ⟨K, i1, i2, hK, hQ'⟩⟩⟩)

section Certificates

theorem rk2DiagIndexInput : Rk2DiagIndexInput := by
  intro lab hlab htag p hp hp2 hpd
  rcases htag with hA | htwA | hE6 | htwE6 | hB2 | hG2 | hF4
  · exact rk2_pSubgroup_le_inn_linear hlab hA hp hp2 hpd
  · exact rk2_pSubgroup_le_inn_unitary hlab htwA hp hp2 hpd
  · exact rk2_inndiagExc hlab (Or.inl hE6) hp hp2 hpd
  · exact rk2_inndiagExc hlab (Or.inr (Or.inl htwE6)) hp hp2 hpd
  · exact rk2_inndiagExc hlab (Or.inr (Or.inr (Or.inl hB2))) hp hp2 hpd
  · exact rk2_inndiagExc hlab (Or.inr (Or.inr (Or.inr (Or.inl hG2)))) hp hp2 hpd
  · exact rk2_inndiagExc hlab (Or.inr (Or.inr (Or.inr (Or.inr hF4)))) hp hp2 hpd

theorem rk2E6InnerDiagBound_holds :
    ∀ (lab : GLALabel), GLAInLambda2 lab → (lab.tag = .E6 ∨ lab.tag = .twE6) →
      3 ∣ rk2DiagIndex lab →
        Rk2LabelAll lab fun R _ I _ => IsSimpleGroup R →
          ∀ E : Subgroup (MulAut R),
            E ≤ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R)) →
              IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 6 := by
  intro lab hlab htag h3idx
  obtain ⟨t, l, n⟩ := lab
  rcases htag with rfl | rfl
  · intro Q hQ
    dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hF, hFin, hK, hQK⟩ := hQ
    letI : Field K := hF
    letI : Finite K := hFin
    haveI : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
    let H := LargeEvenChevH (LargeEvenCartanE 6) K false
    let R := LargeEvenCenterQuot H
    let Isub : Subgroup (MulAut R) :=
      Subgroup.closure (LargeEvenInnSet R ∪ LargeEvenChevDiagImage (LargeEvenCartanE 6) K H)
    have hclosure : Subgroup.closure
        (LargeEvenChevIDImage (LargeEvenCartanE 6) K H ∪ LargeEvenInnSet R) ≤ Isub := by
      rw [Subgroup.closure_le]
      exact Set.union_subset (fun _ hx => hx) (fun _ hx => Subgroup.subset_closure (Or.inl hx))
    have h3K : 3 ∣ Nat.card K - 1 := by
      rw [hK]
      exact h3idx.trans (Nat.gcd_dvd_right 3 (2 ^ n - 1))
    refine ⟨K, hF, hFin, hK, hQK, ?_⟩
    intro _ E hE hEel
    have hEI : E ≤ Isub := hE.trans hclosure
    exact (TableBExc.E6Three.card_le_and_normalizes_E6_three K h3K hEel
      (fun φ hφ => hEI hφ)).1
  · intro Q hQ
    dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hF, hFin, hK, hQK⟩ := hQ
    letI : Field K := hF
    letI : Finite K := hFin
    let H := LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n
    let R := LargeEvenCenterQuot H
    let Isub : Subgroup (MulAut R) :=
      Subgroup.closure (LargeEvenInnSet R ∪ LargeEvenChevDiagImage (LargeEvenCartanE 6) K H)
    have hclosure : Subgroup.closure
        (LargeEvenChevIDImage (LargeEvenCartanE 6) K H ∪ LargeEvenInnSet R) ≤ Isub := by
      rw [Subgroup.closure_le]
      exact Set.union_subset (fun _ hx => hx) (fun _ hx => Subgroup.subset_closure (Or.inl hx))
    have h3sub : 3 ∣ 2 ^ n + 1 := h3idx.trans (Nat.gcd_dvd_right 3 (2 ^ n + 1))
    refine ⟨K, hF, hFin, hK, hQK, ?_⟩
    intro _ E hE hEel
    have hEI : E ≤ Isub := hE.trans hclosure
    exact CFSG.StandardType.ggTwE6ThreeInndiagRankInput_holds K n hlab.1 hK h3sub E hEel
      (fun φ hφ => hEI hφ)

theorem rk2_pSubgroup_le_inn' {lab : GLALabel} (hlab : GLAInLambda2 lab) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpd : ¬ p ∣ rk2DiagIndex lab) :
    Rk2LabelAll lab fun R _ I _ => ∀ E : Subgroup (MulAut R),
      E ≤ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R)) → IsPGroup p E →
        E ≤ (MulAut.conj : R →* MulAut R).range :=
  rk2_pSubgroup_le_inn rk2DiagIndexInput hlab hp hp2 hpd

theorem rk2_card_le_of_le_inndiag' {lab : GLALabel} (hlab : GLAInLambda2 lab) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpd : ¬ p ∣ rk2DiagIndex lab) :
    Rk2LabelAll lab fun R _ I _ => ∀ (hfin : Finite R), IsSimpleGroup R →
      ∀ E : Subgroup (MulAut R),
        E ≤ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R)) →
          IsElemAbelian p E →
            Nat.card E ≤ p ^ @CFSG.Open.pRank p R _ hfin (⊤ : Subgroup R) :=
  rk2_card_le_of_le_inndiag rk2DiagIndexInput hlab hp hp2 hpd

private theorem rk2LabelAll_mono {lab : GLALabel} {P Q : CFSG.Assembly.LargeEvenRawCont}
    (hPQ : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), P R I F → Q R I F)
    (hP : Rk2LabelAll lab P) : Rk2LabelAll lab Q := by
  intro Q0 hQ0
  exact rk2_rawDatum_mono (fun R _ I F h => ⟨h.1, hPQ R I F h.2⟩) (hP Q0 hQ0)

theorem rk2_isLabel_of_rawDatum {lab : GLALabel} (hlab : GLAInLambda2 lab) :
    Rk2LabelAll lab fun R _ _ _ => IsSimpleGroup R →
      (∃ a b : R, a * b ≠ b * a) → Rk2IsLabel R lab := by
  refine rk2LabelAll_mono (fun R _ I F hself => ?_) (rk2_labelAll_self lab)
  intro hs hnab
  have hZ : Subgroup.center R = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center R) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have ha : a ∈ Subgroup.center R := by rw [h]; exact Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  let θ : R ⧸ Subgroup.center R ≃* R :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hcomm : commutator R = ⊤ :=
    (CFSG.RankThree.PartOne.F106.isPerfect_of_simple_nonabelian hnab).commutator_eq_top
  exact ⟨hcomm, lab, hlab, hself _ ⟨hs, hnab, θ, rfl⟩⟩

private theorem rk2LabelAll_and {lab : GLALabel} {P Q : CFSG.Assembly.LargeEvenRawCont}
    (hP : Rk2LabelAll lab P) (hQ : Rk2LabelAll lab Q) :
    Rk2LabelAll lab fun R _ I F => P R I F ∧ Q R I F := by
  intro Q0 hQ0
  have h1 : GLARawDatum lab (fun R _ I F => Q0 R I F ∧ P R I F) := hP Q0 hQ0
  have h2 : GLARawDatum lab
      (fun R _ I F => (Q0 R I F ∧ P R I F) ∧ Q R I F) := hQ _ h1
  exact rk2_rawDatum_mono (fun R _ I F h => ⟨h.1.1, h.1.2, h.2⟩) h2

private theorem rk2Mult_E6_three {l n : ℕ} (h3 : 3 ∣ 2 ^ n - 1) :
    rk2Mult ⟨.E6, l, n⟩ (rk2Ord 3 n) = 6 := by
  rw [rk2Ord_eq_one_iff.mpr h3]
  norm_num [rk2Mult, rk2Cnt]

private theorem rk2Mult_twE6_three {l n : ℕ} (h3 : 3 ∣ 2 ^ n + 1) :
    rk2Mult ⟨.twE6, l, n⟩ (rk2Ord 3 n) = 6 := by
  rw [rk2Ord_eq_two_iff Nat.prime_three (by norm_num) |>.mpr h3]
  norm_num [rk2Mult, rk2Cnt]

private theorem rk2InnRank_of_dvd_E6 {lab : GLALabel}
    (hlab : GLAInLambda2 lab) (htag : lab.tag = .E6 ∨ lab.tag = .twE6)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ∣ rk2DiagIndex lab) :
    Rk2LabelAll lab fun R _ I _ => IsSimpleGroup R → ∀ E : Subgroup (MulAut R),
      E ≤ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R)) →
        IsElemAbelian p E → Nat.card E ≤ p ^ rk2Mult lab (rk2Ord p lab.n) := by
  obtain ⟨t, l, n⟩ := lab
  rcases htag with rfl | rfl
  · have hp3dvd : p ∣ 3 := hpd.trans (by simpa [rk2DiagIndex] using Nat.gcd_dvd_left 3 (2 ^ n - 1))
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hp3dvd
    have h3idx : 3 ∣ rk2DiagIndex ⟨.E6, l, n⟩ := by simpa [hp3] using hpd
    have h3 : 3 ∣ 2 ^ n - 1 := h3idx.trans (Nat.gcd_dvd_right 3 (2 ^ n - 1))
    have h := rk2E6InnerDiagBound_holds ⟨.E6, l, n⟩ hlab (Or.inl rfl) h3idx
    refine rk2LabelAll_mono (fun R _ I F hP => ?_) h
    intro hs E hE hEel
    subst hp3
    simpa [rk2Mult_E6_three h3] using hP hs E hE hEel
  · have hp3dvd : p ∣ 3 := by
      simpa [rk2DiagIndex] using hpd.trans (Nat.gcd_dvd_left 3 (2 ^ n + 1))
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hp3dvd
    have h3idx : 3 ∣ rk2DiagIndex ⟨.twE6, l, n⟩ := by simpa [hp3] using hpd
    have h3 : 3 ∣ 2 ^ n + 1 := h3idx.trans (Nat.gcd_dvd_right 3 (2 ^ n + 1))
    have h := rk2E6InnerDiagBound_holds ⟨.twE6, l, n⟩ hlab (Or.inr rfl) h3idx
    refine rk2LabelAll_mono (fun R _ I F hP => ?_) h
    intro hs E hE hEel
    subst hp3
    simpa [rk2Mult_twE6_three h3] using hP hs E hE hEel

private theorem rk2InnRank_of_not_dvd (h : Rk2KRank)
    {lab : GLALabel} (hlab : GLAInLambda2 lab) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpd : ¬ p ∣ rk2DiagIndex lab) :
    Rk2LabelAll lab fun R _ I _ => Finite R → IsSimpleGroup R → ∀ E : Subgroup (MulAut R),
      E ≤ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R)) →
        IsElemAbelian p E → Nat.card E ≤ p ^ rk2Mult lab (rk2Ord p lab.n) := by
  have hcard := rk2_card_le_of_le_inndiag' hlab hp hp2 hpd
  have hInn := rk2_pSubgroup_le_inn' hlab hp hp2 hpd
  have hK : Rk2LabelAll lab fun R _ _ _ => ∀ (hfin : Finite R), IsSimpleGroup R →
      Rk2IsLabel R lab →
        p ^ @CFSG.Open.pRank p R _ hfin (⊤ : Subgroup R) ≤
          p ^ rk2Mult lab (rk2Ord p lab.n) := by
    intro Q hQ
    refine rk2_rawDatum_mono (fun R _ I F hq => ⟨hq, ?_⟩) hQ
    intro hfin hs hlabel
    exact Nat.pow_le_pow_right hp.pos (h R lab p hlabel hp hp2)
  have hK' : Rk2LabelAll lab fun R _ _ _ => ∀ (hfin : Finite R), IsSimpleGroup R →
      (∃ a b : R, a * b ≠ b * a) →
        p ^ @CFSG.Open.pRank p R _ hfin (⊤ : Subgroup R) ≤
          p ^ rk2Mult lab (rk2Ord p lab.n) := by
    have h_and := rk2LabelAll_and (rk2_isLabel_of_rawDatum hlab) hK
    exact rk2LabelAll_mono (fun R _ I F h => by
      intro hfin hs hnab
      exact h.2 hfin hs (h.1 hs hnab)) h_and
  have hAll := rk2LabelAll_and (rk2LabelAll_and hcard hK') hInn
  refine rk2LabelAll_mono (fun R _ I F h => ?_) hAll
  intro hfin hs E hE hEel
  by_cases hab : ∀ a b : R, a * b = b * a
  · have hInnE : E ≤ (MulAut.conj : R →* MulAut R).range := h.2 E hE hEel.isPGroup
    have hInnBot : (MulAut.conj : R →* MulAut R).range = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨r, rfl⟩
      ext s
      rw [MulAut.conj_apply, MulAut.one_apply, hab r s]
      group
    have hEbot : E = ⊥ := by
      rw [eq_bot_iff]
      intro e he
      have hmem : e ∈ (MulAut.conj : R →* MulAut R).range := hInnE he
      rwa [hInnBot] at hmem
    rw [hEbot, Subgroup.card_bot]
    exact Nat.one_le_pow _ _ hp.pos
  · have hnab : ∃ a b : R, a * b ≠ b * a := by
      push Not at hab
      exact hab
    exact (h.1.1 hfin hs E hE hEel).trans (h.1.2 hfin hs hnab)

theorem rk2_rawDatum_finite {lab : GLALabel} (hlab : GLAInLambda2 lab) :
    Rk2LabelAll lab fun R _ _ _ => Finite R := by
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  cases t
  · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeLinear] at hQ ⊢
    obtain ⟨K, hF, hFin, hK, hq⟩ := hQ
    exact ⟨K, hF, hFin, hK, hq, by
      letI : Field K := hF
      letI : Finite K := hFin
      infer_instance⟩
  · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeUnitary] at hQ ⊢
    obtain ⟨K, hF, hFin, hK, hq⟩ := hQ
    exact ⟨K, hF, hFin, hK, hq, by
      letI : Field K := hF
      letI : Finite K := hFin
      infer_instance⟩
  · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeSymplectic] at hQ ⊢
    obtain ⟨K, hF, hFin, hK, hq⟩ := hQ
    exact ⟨K, hF, hFin, hK, hq, by
      letI : Field K := hF
      letI : Finite K := hFin
      infer_instance⟩
  · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeSymplectic] at hQ ⊢
    obtain ⟨K, hF, hFin, hK, hq⟩ := hQ
    exact ⟨K, hF, hFin, hK, hq, by
      letI : Field K := hF
      letI : Finite K := hFin
      infer_instance⟩
  · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    split_ifs at hQ ⊢
    · obtain ⟨K, hF, hFin, hK, hq⟩ := hQ
      exact ⟨K, hF, hFin, hK, hq, by
        letI : Field K := hF
        letI : Finite K := hFin
        infer_instance⟩
    · obtain ⟨K, hF, hFin, hK, hq⟩ := hQ
      exact ⟨K, hF, hFin, hK, hq, by
        letI : Field K := hF
        letI : Finite K := hFin
        infer_instance⟩
  · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    split_ifs at hQ ⊢
    · obtain ⟨K, hF, hFin, hK, hq⟩ := hQ
      exact ⟨K, hF, hFin, hK, hq, by
        letI : Field K := hF
        letI : Finite K := hFin
        infer_instance⟩
    · obtain ⟨K, hF, hFin, hK, hq⟩ := hQ
      exact ⟨K, hF, hFin, hK, hq, by
        letI : Field K := hF
        letI : Finite K := hFin
        infer_instance⟩
    · obtain ⟨K, hF, hFin, hK, b, c, hbc, hq⟩ := hQ
      exact ⟨K, hF, hFin, hK, b, c, hbc, hq, by
        letI : Field K := hF
        letI : Finite K := hFin
        infer_instance⟩
  · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ ⊢
    obtain ⟨K, hF, hFin, hK, hq⟩ := hQ
    exact ⟨K, hF, hFin, hK, hq, by
      letI : Field K := hF
      letI : Finite K := hFin
      exact TableBExc.finite_recipeGroup .E6 K⟩
  · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ ⊢
    obtain ⟨K, hF, hFin, hK, hq⟩ := hQ
    exact ⟨K, hF, hFin, hK, hq, by
      letI : Field K := hF
      letI : Finite K := hFin
      exact TableBExc.finite_recipeGroup .E7 K⟩
  · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ ⊢
    obtain ⟨K, hF, hFin, hK, hq⟩ := hQ
    exact ⟨K, hF, hFin, hK, hq, by
      letI : Field K := hF
      letI : Finite K := hFin
      exact TableBExc.finite_recipeGroup .E8 K⟩
  · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ ⊢
    obtain ⟨K, hF, hFin, hK, hq⟩ := hQ
    exact ⟨K, hF, hFin, hK, hq, by
      letI : Field K := hF
      letI : Finite K := hFin
      exact TableBF4.finite_recipeGroup (K := K)⟩
  · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeTwisted] at hQ ⊢
    obtain ⟨K, hF, hFin, hK, hq⟩ := hQ
    exact ⟨K, hF, hFin, hK, hq, by
      letI : Field K := hF
      letI : Finite K := hFin
      exact TwE6Delta.finite_recipeR hK⟩
  · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeTwisted] at hQ ⊢
    obtain ⟨K, hF, hFin, hK, hq⟩ := hQ
    exact ⟨K, hF, hFin, hK, hq, by
      letI : Field K := hF
      letI : Finite K := hFin
      exact (finite_ggPSections_recipe_triD4 hlab.1 K hK (p := 3)
        Nat.prime_three (by norm_num)).1⟩
  · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeChevalley] at hQ ⊢
    obtain ⟨K, hF, hFin, hK, hq⟩ := hQ
    exact ⟨K, hF, hFin, hK, hq, by
      letI : Field K := hF
      letI : Finite K := hFin
      exact TableBExc.finite_recipeGroup .G2 K⟩
  · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeSuzuki] at hQ ⊢
    obtain ⟨K, hF, hFin, hK, hq⟩ := hQ
    exact ⟨K, hF, hFin, hK, hq, by
      letI : Field K := hF
      letI : Finite K := hFin
      have : Finite (LargeEvenSzGroup ((n - 1) / 2) K) := Subtype.finite
      infer_instance⟩
  · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeTwF4Inherited] at hQ ⊢
    obtain ⟨K, hF, hFin, hK, hq⟩ := hQ
    exact ⟨K, hF, hFin, hK, hq, by
      letI : Field K := hF
      letI : Finite K := hFin
      have hn3 : 3 ≤ n := by simpa [GLAInLambda2] using hlab.2.2.2
      exact (finite_ggPSections_recipe_twF4 (by omega : 1 ≤ (n - 1) / 2) K hK
        (p := 3) Nat.prime_three (by norm_num)).1⟩
  · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, hF, hFin, hK, hq⟩ := hQ
    exact ⟨K, hF, hFin, hK, hq, by
      letI : Field K := hF
      letI : Finite K := hFin
      infer_instance⟩
  · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeG2Derived] at hQ ⊢
    obtain ⟨K, hF, hFin, hK, hq⟩ := hQ
    exact ⟨K, hF, hFin, hK, hq, by
      letI : Field K := hF
      letI : Finite K := hFin
      obtain ⟨e⟩ := TableBExcSmallRest.nonempty_g2der_equiv_su3 K hK
      have : Finite (StatedSU 3 3 F9) := Nat.finite_of_card_ne_zero (by
        rw [CFSG.LinearGroups.UnitaryThreeOverNine.card_statedSU card_F9]; norm_num)
      exact Finite.of_equiv _ e.symm.toEquiv⟩
  · dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeTwF4Inherited] at hQ ⊢
    obtain ⟨K, hF, hFin, hK, hq⟩ := hQ
    have hn1 : n = 1 := hlab.2.2
    subst hn1
    have hK2 : Nat.card K = 2 := by
      rw [hK]
      norm_num
    exact ⟨K, hF, hFin, hK, hq, by
      letI : Field K := hF
      letI : Finite K := hFin
      have hm : CFSG.Blueprint.ReeTitsModel
          (LargeEvenCenterQuot (LargeEvenTwF4H 0 K)) .Tits 2 1 :=
        ⟨⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩, 0, rfl,
          reeTitsRelationModel_largeEven 0 hK2⟩
      obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv _ 2 1 hm
      exact Finite.of_equiv _ e.symm.toEquiv⟩

theorem rk2InnRank_of_kRank (h : Rk2KRank) : Rk2InnRank := by
  intro lab hlab _ p hp hp2
  by_cases hpd : p ∣ rk2DiagIndex lab
  · obtain ⟨t, l, n⟩ := lab
    cases t
    · have hpdiv : p ∣ 2 ^ n - 1 := hpd.trans (Nat.gcd_dvd_right (l + 1) (2 ^ n - 1))
      have hlin := rk2_inndiag_card_le_linear (lab := ⟨.A, l, n⟩) hlab rfl hp hp2 hpdiv
      exact rk2LabelAll_mono (fun R _ I F hP => hP) hlin
    · have hpdiv : p ∣ 2 ^ n + 1 := hpd.trans (Nat.gcd_dvd_right (l + 1) (2 ^ n + 1))
      have huni := rk2_inndiag_card_le_unitary (lab := ⟨.twA, l, n⟩) hlab rfl hp hp2 hpdiv
      exact rk2LabelAll_mono (fun R _ I F hP => hP) huni
    · exfalso; exact hp.not_dvd_one (by simpa [rk2DiagIndex] using hpd)
    · exfalso; exact hp.not_dvd_one (by simpa [rk2DiagIndex] using hpd)
    · exfalso; exact hp.not_dvd_one (by simpa [rk2DiagIndex] using hpd)
    · exfalso; exact hp.not_dvd_one (by simpa [rk2DiagIndex] using hpd)
    · exact rk2InnRank_of_dvd_E6 hlab (Or.inl rfl) hp hp2 hpd
    · exfalso; exact hp.not_dvd_one (by simpa [rk2DiagIndex] using hpd)
    · exfalso; exact hp.not_dvd_one (by simpa [rk2DiagIndex] using hpd)
    · exfalso; exact hp.not_dvd_one (by simpa [rk2DiagIndex] using hpd)
    · exact rk2InnRank_of_dvd_E6 hlab (Or.inr rfl) hp hp2 hpd
    · exfalso; exact hp.not_dvd_one (by simpa [rk2DiagIndex] using hpd)
    · exfalso; exact hp.not_dvd_one (by simpa [rk2DiagIndex] using hpd)
    · exfalso; exact hp.not_dvd_one (by simpa [rk2DiagIndex] using hpd)
    · exfalso; exact hp.not_dvd_one (by simpa [rk2DiagIndex] using hpd)
    · exfalso; exact hp.not_dvd_one (by simpa [rk2DiagIndex] using hpd)
    · exfalso; exact hp.not_dvd_one (by simpa [rk2DiagIndex] using hpd)
    · exfalso; exact hp.not_dvd_one (by simpa [rk2DiagIndex] using hpd)
  · have hb := rk2InnRank_of_not_dvd h hlab hp hp2 hpd
    have hf := rk2_rawDatum_finite hlab
    have h_and := rk2LabelAll_and hf hb
    exact rk2LabelAll_mono (fun R _ I F hq => by
      intro hs E hE hEel
      exact hq.2 hq.1 hs E hE hEel) h_and

end Certificates

end CFSG.LocalAnalysis.GLTheoremA
