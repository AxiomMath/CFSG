module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167CDefs
import CFSG.LieType.Steinberg.CentralExt.GriessOmegaEightTwo
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.OddCoversLift
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerLinear
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerTwD

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

private theorem pFreeCover_of_isOmPA_aux1 {S : Type} [Group S] {p : ℕ}
    (hS : ¬ p ∣ Nat.card (CFSG.Open.griessHopfMultiplier S)) : PFreeCover p S := by
  rintro X _ _ hX ⟨e⟩ hp
  have hperf : Group.IsPerfect X := Group.isPerfect_def.mpr hX.1
  have hdvd := CFSG.Quasithin.B69K.OddCovers.card_center_dvd_hopfMultiplier hperf e
  rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess S).toEquiv] at hdvd
  exact hS (hp.trans hdvd)

section


private theorem pFreeCover_of_isOmPA_aux2 {X : Type} [Group X] {ℓ n : ℕ}
    (h : CFSG.Open.StatedClassicalModel X .POmegaPlus ℓ 2 n) (hn : 1 ≤ n) (hℓ : 4 ≤ ℓ) :
    Nat.card (CFSG.Open.griessHopfMultiplier X) ∣ 4 := by
  by_cases h41 : ℓ = 4 ∧ n = 1
  · obtain ⟨rfl, rfl⟩ := h41
    have hLM : CFSG.Models.LieModel X .POmegaPlus 4 2 1 := ⟨h.1, Or.inl h⟩
    obtain ⟨-, ⟨eM⟩⟩ :=
      CFSG.LieType.Steinberg.CentralExt.GriessClassical.pomegaPlus_four_two_row hLM
    have hg : CFSG.Blueprint.Multiplier.genericOrders .POmegaPlus 4 2 1 = (1, 1) := by
      simp only [CFSG.Blueprint.Multiplier.genericOrders]
      rw [if_pos (even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega)))]
    have he : CFSG.Blueprint.Multiplier.exceptionalOrders .POmegaPlus 4 2 1 = (2, 2) := by
      decide
    rw [Nat.card_congr eM.toEquiv,
      _root_.CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_generic_exceptional', hg, he]
    norm_num
  · have hn' : 2 ≤ n ∨ 5 ≤ ℓ := by
      rcases (show n = 1 ∨ 2 ≤ n by omega) with hn1 | hn2
      · right; omega
      · left; exact hn2
    exact CFSG.LocalAnalysis.GLTheoremA.card_griess_pomegaPlus_dvd_four h hn'

theorem pFreeCover_of_isOmPA {S : Type} [Group S] {p n k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 4 ≤ n)
    (hk : 1 ≤ k) (h : catalogIs S (isOmPA n (2 ^ k))) : PFreeCover p S := by
  apply pFreeCover_of_isOmPA_aux1
  intro hdiv
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  unfold isOmPA at hi
  rcases hi with hi | ⟨hn3, -⟩
  · unfold isOmP at hi
    cases i with
    | cyclic _ _ => simp [onLie] at hi
    | alternating _ _ => simp [onLie] at hi
    | sporadic _ => simp [onLie] at hi
    | lie d =>
      obtain ⟨t, hv⟩ := d
      cases t with
      | D r q =>
        simp only [onLie] at hi
        obtain ⟨hr, hqc⟩ := hi
        obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := k) hk
          (hqc.trans (by norm_num))
        have hm : CFSG.Models.LieModel S .POmegaPlus n 2 k := by
          simpa [h1, h2, hr] using CFSG.Models.lieModel_D r q hv e
        have hSC : CFSG.Open.StatedClassicalModel S .POmegaPlus n 2 k :=
          CFSG.Models.LieModel.statedClassicalModel hm (by decide)
        have h4 : Nat.card (CFSG.Open.griessHopfMultiplier S) ∣ 4 :=
          pFreeCover_of_isOmPA_aux2 hSC hk hn
        have h24 : p ∣ 4 := hdiv.trans h4
        have hp2' : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
          (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h24))
        exact hp2 hp2'
      | _ => simp [onLie] at hi
  · omega

theorem pFreeCover_of_isOmMA {S : Type} [Group S] {p n k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 4 ≤ n)
    (hk : 1 ≤ k) (h : catalogIs S (isOmMA n (2 ^ k))) : PFreeCover p S := by
  apply pFreeCover_of_isOmPA_aux1
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  unfold isOmMA at hi
  rcases hi with hi | ⟨hn3, -⟩
  · unfold isOmM at hi
    cases i with
    | cyclic _ _ => simp [onLie] at hi
    | alternating _ _ => simp [onLie] at hi
    | sporadic _ => simp [onLie] at hi
    | lie d =>
      obtain ⟨t, hv⟩ := d
      cases t with
      | twistedD r q =>
        simp only [onLie] at hi
        obtain ⟨hr, hqc⟩ := hi
        obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := k) hk
          (hqc.trans (by norm_num))
        have hm : CFSG.Models.LieModel S .POmegaMinus n 2 k := by
          simpa [h1, h2, hr] using CFSG.Models.lieModel_twistedD r q hv e
        have hSC : CFSG.Open.StatedClassicalModel S .POmegaMinus n 2 k :=
          CFSG.Models.LieModel.statedClassicalModel hm (by decide)
        rw [CFSG.LocalAnalysis.GLTheoremA.card_griessHopfMultiplier_pomegaMinus_eq_one hk hSC]
        exact hp.not_dvd_one
      | _ => simp [onLie] at hi
  · omega

end

theorem pFreeCover_of_isLnA_two {S : Type} [Group S] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 5 ≤ n)
    (h : catalogIs S (isLnA n 2)) : PFreeCover p S := by
  apply pFreeCover_of_isOmPA_aux1
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  unfold isLnA at hi
  rcases hi with hi | hs | hs | hs | hs
  · cases i with
    | cyclic _ _ => simp [onLie] at hi
    | alternating _ _ => simp [onLie] at hi
    | sporadic _ => simp [onLie] at hi
    | lie d =>
      obtain ⟨t, hv⟩ := d
      cases t with
      | A r q =>
        simp only [onLie, isLnEps] at hi
        obtain ⟨hr, hq⟩ := hi
        obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
          (hq.trans (by norm_num))
        have hm : CFSG.Models.LieModel S .PSL n 2 1 := by
          simpa [h1, h2, hr] using CFSG.Models.lieModel_A r q hv e
        have hSC : CFSG.Open.StatedClassicalModel S .PSL n 2 1 :=
          CFSG.Models.LieModel.statedClassicalModel hm (by decide)
        obtain ⟨-, K, hfield, hfinite, hKcard, ⟨eK⟩⟩ := hSC
        letI : Field K := hfield
        letI : Finite K := hfinite
        haveI : Fintype K := Fintype.ofFinite K
        have hcard : Fintype.card K = 2 := by
          rw [Fintype.card_eq_nat_card, hKcard]; norm_num
        rw [Nat.card_congr
            (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr eK).toEquiv,
          CFSG.LocalAnalysis.GLTheoremA.card_hopfMultiplier_statedProj_of_five_le (F := K) (d := n) hn,
          hcard]
        simpa using hp.not_dvd_one
      | _ => simp [onLie, isLnEps] at hi
  · omega
  · omega
  · omega
  · omega

theorem pFreeCover_five_of_isLnA_six_four {S : Type} [Group S] (h : catalogIs S (isLnA 6 4)) :
    PFreeCover 5 S := by
  apply pFreeCover_of_isOmPA_aux1
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  unfold isLnA at hi
  rcases hi with hi | hs | hs | hs | hs
  · cases i with
    | cyclic _ _ => simp [onLie] at hi
    | alternating _ _ => simp [onLie] at hi
    | sporadic _ => simp [onLie] at hi
    | lie d =>
      obtain ⟨t, hv⟩ := d
      cases t with
      | A r q =>
        simp only [onLie, isLnEps] at hi
        obtain ⟨hr, hq⟩ := hi
        obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 2) (by norm_num)
          (hq.trans (by norm_num))
        have hm : CFSG.Models.LieModel S .PSL 6 2 2 := by
          simpa [h1, h2, hr] using CFSG.Models.lieModel_A r q hv e
        have hSC : CFSG.Open.StatedClassicalModel S .PSL 6 2 2 :=
          CFSG.Models.LieModel.statedClassicalModel hm (by decide)
        obtain ⟨-, K, hfield, hfinite, hKcard, ⟨eK⟩⟩ := hSC
        letI : Field K := hfield
        letI : Finite K := hfinite
        haveI : Fintype K := Fintype.ofFinite K
        have hcard : Fintype.card K = 4 := by
          rw [Fintype.card_eq_nat_card, hKcard]; norm_num
        rw [Nat.card_congr
            (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr eK).toEquiv,
          CFSG.LocalAnalysis.GLTheoremA.card_hopfMultiplier_statedProj_of_five_le (F := K) (d := 6)
            (by norm_num),
          hcard]
        norm_num
      | _ => simp [onLie, isLnEps] at hi
  · omega
  · omega
  · omega
  · omega

end CFSG.LocalAnalysis.GLTheoremA.I167

end
