module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420Facts2
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti

private theorem lieIndex_isD4of {S : Type} [Group S] {r : ℕ} (h : catalogIs S (S8.isD4of r)) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.D 4 q).Valid), q.card = r ∧
      Nonempty (S ≃* ValidLieTypeIndex.Group ⟨.D 4 q, hv⟩) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex h
  cases d with
  | D r' q =>
    rcases r' with _ | _ | _ | _ | _ | r'
    · exact hP.elim
    · exact hP.elim
    · exact hP.elim
    · exact hP.elim
    · exact ⟨q, hv, hP, ⟨e⟩⟩
    · exact hP.elim
  | _ => exact hP.elim

private theorem lieIndex_isG2of {S : Type} [Group S] {r : ℕ} (h : catalogIs S (S8.isG2of r)) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid), q.card = r ∧
      Nonempty (S ≃* ValidLieTypeIndex.Group ⟨.G2 q, hv⟩) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex h
  cases d with
  | G2 q => exact ⟨q, hv, hP, ⟨e⟩⟩
  | _ => exact hP.elim

private theorem lieIndex_isTD4of {S : Type} [Group S] {r : ℕ} (h : catalogIs S (isTD4of r)) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid), q.card = r ∧
      Nonempty (S ≃* ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex h
  cases d with
  | trialityD4 q => exact ⟨q, hv, hP, ⟨e⟩⟩
  | _ => exact hP.elim

private theorem card_center_eq_one_of_dvd {Y : Type} [Group Y] [Finite Y]
    (h3 : ∀ z ∈ Subgroup.center Y, ∃ n : ℕ, z ^ 3 ^ n = 1) {m : ℕ}
    (hd : Nat.card (Subgroup.center Y) ∣ m) (hm : ¬ 3 ∣ m) :
    Nat.card (Subgroup.center Y) = 1 := by
  by_contra hne
  have hpos : 0 < Nat.card (Subgroup.center Y) := Nat.card_pos
  haveI : Nontrivial (Subgroup.center Y) :=
    Finite.one_lt_card_iff_nontrivial.1 (by omega)
  have hZ : IsPGroup 3 (Subgroup.center Y) := by
    intro g
    obtain ⟨n, hn⟩ := h3 g.1 g.2
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  exact CFSG.LocalAnalysis.GLTheoremA.false_of_pGroup_dvd Nat.prime_three hZ hd hm

theorem i1432Cent_holds :
    I1432Cent := by
  intro Y _ _ hY h3 hcat
  have hGA : CFSG.Open.GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  rcases hcat with h | h | h | h
  ·
    obtain ⟨q, hv, hq, ⟨e⟩⟩ := lieIndex_isD4of h
    obtain ⟨h1, h2⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq Nat.prime_three
      (s := 3) (by norm_num) (hq.trans (by norm_num))
    have hm := CFSG.Models.lieModel_D 4 q hv e
    rw [h1, h2] at hm
    have hdvd := CFSG.LocalAnalysis.GLTheoremA.card_center_dvd_of_table hGA hY hm
      (a := 2) (b := 2) (c := 1) (d := 1) (by decide) (by decide) (by norm_num)
    exact card_center_eq_one_of_dvd h3 hdvd (by norm_num)
  ·
    obtain ⟨q, hv, hq, ⟨e⟩⟩ := lieIndex_isG2of h
    obtain ⟨h1, h2⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq Nat.prime_three
      (s := 3) (by norm_num) (hq.trans (by norm_num))
    have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
    have hqc : q.card = q.p ^ q.exponent := PrimePower.card_def q
    have hm : CFSG.Models.LieModel (Y ⧸ Subgroup.center Y) .G2 0 q.p q.exponent :=
      CFSG.Models.lieModel_of_namesTag (t := .G2) (p := q.p) (f := q.exponent)
        ⟨q.prime_p, q.exponent_pos, rfl, hqc ▸ hr⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ e
    rw [h1, h2] at hm
    have hdvd := CFSG.LocalAnalysis.GLTheoremA.card_center_dvd_of_table hGA hY hm
      (a := 1) (b := 1) (c := 1) (d := 1) (by decide) (by decide) (by norm_num)
    exact Nat.dvd_one.1 (hdvd.trans (by norm_num))
  ·
    obtain ⟨q, hv, hq, ⟨e⟩⟩ := lieIndex_isD4of h
    obtain ⟨h1, h2⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq Nat.prime_three
      (s := 1) (by norm_num) (hq.trans (by norm_num))
    have hm := CFSG.Models.lieModel_D 4 q hv e
    rw [h1, h2] at hm
    have hdvd := CFSG.LocalAnalysis.GLTheoremA.card_center_dvd_of_table hGA hY hm
      (a := 2) (b := 2) (c := 1) (d := 1) (by decide) (by decide) (by norm_num)
    exact card_center_eq_one_of_dvd h3 hdvd (by norm_num)
  ·
    obtain ⟨q, hv, hq, ⟨e⟩⟩ := lieIndex_isTD4of h
    have hm : CFSG.Models.LieModel (Y ⧸ Subgroup.center Y) .trialityD4 0 q.p q.exponent :=
      CFSG.Models.lieModel_of_namesTag (t := .trialityD4) (p := q.p) (f := q.exponent)
        ⟨q.prime_p, q.exponent_pos, rfl⟩ ⟨_, hv⟩ ⟨rfl, rfl⟩ e
    have hdvd := CFSG.LocalAnalysis.GLTheoremA.card_center_dvd_of_table hGA hY hm
      (a := 1) (b := 1) (c := 1) (d := 1) rfl rfl (by norm_num)
    exact Nat.dvd_one.1 (hdvd.trans (by norm_num))

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
