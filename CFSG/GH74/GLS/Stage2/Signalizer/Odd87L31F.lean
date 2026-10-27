module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31FM11
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31FLie

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local

theorem l31f_section_alt_ly {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    (hctx : Stage2Ctx G z Kind.ly S) {s : G} (hs : orderOf s = 2) {Y : Type} [Group Y]
    [IsSimpleGroup Y] (hns : ¬ Group.IsSolvable Y)
    (hsec : IsSection Y ↥(centralizer ({s} : Set G))) :
    ∃ n : ℕ, (n = 10 ∨ n = 11) ∧ IsDoubleCoverOfAlt (CentralizerBar z) n ∧
      IsSection Y (alternatingGroup (Fin n)) := by
  have hd := hctx.data
  cases hd with
  | ly h =>
    obtain ⟨n, hn, hS⟩ := h
    refine ⟨n, hn, hS.cover, ?_⟩
    obtain ⟨c, hc⟩ := isConj_iff.mp (hS.one_class z s hctx.orderOf_z hs)
    obtain ⟨e⟩ := cenConj_nonempty c hc
    exact isSection_alt_of_cover hS.cover hns (isSection_bar z hns (IsSection.of_equiv e hsec))

private theorem l31f_center_eq_bot_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : center X = ⊥) : center Y = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := e.surjective y
  have hx : x ∈ center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply e.injective
    simpa using Subgroup.mem_center_iff.mp hy (e g)
  rw [h, Subgroup.mem_bot] at hx
  rw [hx, map_one]
  exact one_mem _

private theorem l31f_isSimpleGroup_of_center_eq_bot {Y : Type} [Group Y] (hq : IsQuasisimple Y)
    (hZ : center Y = ⊥) : IsSimpleGroup Y := by
  have : IsSimpleGroup (Y ⧸ center Y) := hq.2.1
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup

private theorem l31f_not_isSolvable_of_simple {Y : Type} [Group Y] (hq : IsQuasisimple Y)
    [IsSimpleGroup Y] : ¬ Group.IsSolvable Y := by
  have := hq.1
  exact Group.IsPerfect.not_isSolvable Y

theorem l31_f_core (hInv : InvSec)
    {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G} (hctx : Stage2Ctx G z k S)
    {s : G} (hs : orderOf s = 2) {Y : Type} [Group Y] (hq : IsQuasisimple Y)
    (hsec : IsSection Y ↥(centralizer ({s} : Set G)))
    (hf : NativeSporadic.IsSporadic Y .M11 ∨
      ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ (Odd (p ^ f) ∨ p ^ f = 4) ∧
        (LieModel Y .PSL 3 p f ∨ LieModel Y .PSU 3 p f)) :
    NativeSporadic.IsSporadic Y .M11 ∧ IsDoubleCoverOfAlt (CentralizerBar z) 11 := by
  rcases hf with hM | ⟨p, f, hp, hf1, hq4, hL | hU⟩
  ·
    obtain ⟨e⟩ := hM
    have hcard : Nat.card Y = Nat.card ↥NativeSporadic.M11 := Nat.card_congr e.toEquiv
    have hZ : center Y = ⊥ := l31f_center_eq_bot_of_equiv e.symm l31f_center_m11_eq_bot
    have : IsSimpleGroup Y := l31f_isSimpleGroup_of_center_eq_bot hq hZ
    have hns : ¬ Group.IsSolvable Y := l31f_not_isSolvable_of_simple hq
    have hd : Nat.card Y ∣ Nat.factorial 11 := hcard ▸ l31f_card_m11_dvd_factorial
    have h11 : 11 ∣ Nat.card Y := hcard ▸ l31f_eleven_dvd_card_m11
    have h8 : 8 ∣ Nat.card Y := hcard ▸ l31f_eight_dvd_card_m11
    refine ⟨⟨e⟩, ?_⟩
    by_cases hk : k = Kind.ly
    · subst hk
      obtain ⟨n, hn, hcov, hA⟩ := l31f_section_alt_ly hctx hs hns hsec
      have h11n : 11 ∣ Nat.factorial n :=
        h11.trans (hA.card_dvd.trans (card_alt_dvd_factorial n (by omega)))
      have h11le : 11 ≤ n := (Nat.Prime.dvd_factorial (by norm_num)).mp h11n
      have hn11 : n = 11 := by omega
      rwa [hn11] at hcov
    · exact absurd (hInv G z k S hctx s hs Y hns hsec) (l31f_not_kindFactorAll_m11 hk hd h11 h8)
  ·
    exfalso
    obtain ⟨-, hsimp⟩ := CFSG.LieType.Simplicity.fam_PSL_simplicity Y 3 p f
      (CFSG.GH74.statedClassicalModel_of_lieModel (by norm_num) hL)
    have : IsSimpleGroup Y := hsimp
    have hns : ¬ Group.IsSolvable Y := l31f_not_isSolvable_of_simple hq
    exact l31f_not_kindFactorAll_psl3 k hp hf1 hq4 hL (hInv G z k S hctx s hs Y hns hsec)
  ·
    exfalso
    obtain ⟨-, hsimp⟩ := CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity Y 3 p f
      (CFSG.GH74.statedClassicalModel_of_lieModel (by norm_num) hU)
    have : IsSimpleGroup Y := hsimp
    have hns : ¬ Group.IsSolvable Y := l31f_not_isSolvable_of_simple hq
    exact l31f_not_kindFactorAll_psu3 k hp hf1 hq4 hU (hInv G z k S hctx s hs Y hns hsec)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
