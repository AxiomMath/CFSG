module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourJComp
public import CFSG.Quasithin.H13.NQCatL2LieParabolic
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtY15111Triple
public import CFSG.Quasithin.EmptyFaithful.S146zYFSBase
public import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.AGLEmbedding Subgroup CFSG.QuasithinUnique
open scoped MatrixGroups

theorem perfectCore_isPSL_of_parabolic {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hn : 2 ≤ n)
    (eY : Y ≃* PSL(3, GaloisField 2 n)) {T J : Subgroup Y} (hT : IsSylowTwoOf T ⊤)
    (hle : Subgroup.normalizer (T : Set Y) ≤ J) (hne : J ≠ Subgroup.normalizer (T : Set Y))
    (htop : J ≠ ⊤) :
    T ≤ CFSG.Quasithin.perfectCore J ∧
      CFSG.Quasithin.IsPSL 2 2 n
        (CFSG.Quasithin.ModO2 (CFSG.Quasithin.perfectCore J)) := by
  have hn0 : n ≠ 0 := by omega
  have hSCM : StatedClassicalModel Y .PSL 3 2 n :=
    statedClassicalModel_psl_three_of_mulEquiv hn0 eY
  have hSL : CFSG.Quasithin.H13.IsSL3Ch5 n Y := Or.inl (Or.inl ⟨by decide, hSCM⟩)
  obtain ⟨P, -, hmax, hP, -⟩ :=
    CFSG.Quasithin.H13.NQCat.factL2LieParabolic_holds Y n hn (Or.inl hSL) T hT
  obtain ⟨Q, hQcov, hJQ⟩ := (eq_top_or_exists_le_coatom J).resolve_left htop
  have hQcov' : Q ⋖ ⊤ := covBy_top_iff.mpr hQcov
  obtain ⟨j, rfl⟩ := (hmax Q (hle.trans hJQ)).mp hQcov'
  rcases (hP j).1.eq_or_eq hle hJQ with hEq | hEq
  · exact absurd hEq hne
  · rw [hEq]
    exact (hP j).2

private theorem card_eq_168_of_psl_three_two {Y : Type} [Group Y]
    (eY : Y ≃* PSL(3, GaloisField 2 1)) : Nat.card Y = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two
    (statedClassicalModel_psl_three_of_mulEquiv (by norm_num) eY)

private theorem card_eq_eight_of_isSylowTwoOf_top {Y : Type} [Group Y] [Finite Y]
    {T : Subgroup Y} (hT : IsSylowTwoOf T ⊤) (hY : Nat.card Y = 168) :
    Nat.card T = 8 := by
  have h := CFSG.Quasithin.S146zY.card_isSylowTwoOf_top (X := Y) hT (a := 3) (m := 21)
    (by norm_num) (by rw [hY]; norm_num)
  simpa using h

private theorem three_dvd_card_of_parabolic {Y : Type} [Group Y] [Finite Y]
    (eY : Y ≃* PSL(3, GaloisField 2 1)) {T J : Subgroup Y} (hT : IsSylowTwoOf T ⊤)
    (hle : Subgroup.normalizer (T : Set Y) ≤ J) (hne : J ≠ Subgroup.normalizer (T : Set Y)) :
    3 ∣ Nat.card J := by
  obtain ⟨T', hT'⟩ := CFSG.AGLEmbedding.exists_sylow_of_isSylowTwoOf_top hT
  have hle' : Subgroup.normalizer ((T' : Subgroup Y) : Set Y) ≤ J := by
    rw [hT']; exact hle
  have hne' : J ≠ Subgroup.normalizer ((T' : Subgroup Y) : Set Y) := by
    rw [hT']; exact hne
  exact CFSG.AGLEmbedding.ParabHub.threeDvd_sl_psl (m := 2) eY.symm T' J hle' hne'

private theorem card_eq_24_of_parabolic {Y : Type} [Group Y] [Finite Y] {T J : Subgroup Y}
    (hY : Nat.card Y = 168) (hTcard : Nat.card T = 8) (hTle : T ≤ J) (htop : J ≠ ⊤)
    (h3 : 3 ∣ Nat.card J) : Nat.card J = 24 := by
  have h8 : 8 ∣ Nat.card J := by
    rw [← hTcard]
    exact Subgroup.card_dvd_of_le hTle
  have hJdvd : Nat.card J ∣ 168 := by
    have h := Subgroup.card_dvd_of_le (le_top : J ≤ ⊤)
    rwa [Subgroup.card_top, hY] at h
  have hJlt : Nat.card J < 168 := by
    have h := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr htop)
    rwa [Subgroup.card_top, hY] at h
  have h24 : 24 ∣ Nat.card J := by
    simpa using (by norm_num : Nat.Coprime 8 3).mul_dvd_of_dvd_of_dvd h8 h3
  obtain ⟨k, hk⟩ := h24
  obtain ⟨t, ht⟩ := hJdvd
  have hkt : k * t = 7 := by
    refine Nat.eq_of_mul_eq_mul_left (n := 24) (by norm_num) ?_
    calc 24 * (k * t) = (24 * k) * t := by ring
      _ = Nat.card J * t := by rw [← hk]
      _ = 168 := ht.symm
      _ = 24 * 7 := by norm_num
  have hkdvd : k ∣ 7 := ⟨t, hkt.symm⟩
  rcases (by norm_num : Nat.Prime 7).eq_one_or_self_of_dvd k hkdvd with h1 | h7
  · rw [hk, h1, Nat.mul_one]
  · exfalso
    have h : Nat.card J = 168 := by rw [hk, h7]
    omega

private theorem relIndex_eq_three_of_card_eq_24 {Y : Type} [Group Y] [Finite Y]
    {T J : Subgroup Y} (hTcard : Nat.card T = 8) (hTle : T ≤ J)
    (hJcard : Nat.card J = 24) : T.relIndex J = 3 := by
  have h := Subgroup.card_mul_index (T.subgroupOf J)
  rw [show Nat.card ↥(T.subgroupOf J) = Nat.card T from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTle).toEquiv,
    hTcard, show (T.subgroupOf J).index = T.relIndex J from rfl,
    show Nat.card ↥J = Nat.card J from rfl, hJcard] at h
  omega

theorem quot_perm_three_of_parabolic {Y : Type} [Group Y] [Finite Y]
    (eY : Y ≃* PSL(3, GaloisField 2 1)) {T J : Subgroup Y} (hT : IsSylowTwoOf T ⊤)
    (hle : Subgroup.normalizer (T : Set Y) ≤ J) (hne : J ≠ Subgroup.normalizer (T : Set Y))
    (htop : J ≠ ⊤) : Nonempty (↥J ⧸ CFSG.pCore 2 ↥J ≃* Equiv.Perm (Fin 3)) := by
  have hYcard : Nat.card Y = 168 := card_eq_168_of_psl_three_two eY
  have hTcard : Nat.card T = 8 := card_eq_eight_of_isSylowTwoOf_top hT hYcard
  have hTle : T ≤ J := Subgroup.le_normalizer.trans hle
  have h3 : 3 ∣ Nat.card J := three_dvd_card_of_parabolic eY hT hle hne
  have hJcard : Nat.card J = 24 := card_eq_24_of_parabolic hYcard hTcard hTle htop h3
  have hrel : T.relIndex J = 3 := relIndex_eq_three_of_card_eq_24 hTcard hTle hJcard
  have hnorm : ¬ J ≤ Subgroup.normalizer (T : Set Y) := fun h => hne (le_antisymm h hle)
  exact CFSG.Quasithin.Y15111.nonempty_perm_equiv_of_relIndex_three hT.2.1 hTle hrel hnorm

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
