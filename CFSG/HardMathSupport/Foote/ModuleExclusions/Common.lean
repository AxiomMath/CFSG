module

public import CFSG.CGT.PushingUpLit.CGT6M.FiveInspCover

public section

namespace CFSG.HardMathSupport.Foote.ModuleExclusions

open CFSG CFSG.Open CFSG.CGT.PushingUpLit.CGT6M

theorem statedModel_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    {t : StatedLieTag} {n p f : ℕ} (h : StatedClassicalModel G t n p f) :
    StatedClassicalModel H t n p f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e h

theorem charP_five_of_card {K : Type} [Field K] [Finite K] {f : ℕ} (h : Nat.card K = 5 ^ f) :
    CharP K 5 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact charP_of_card_eq_prime_pow (p := 5) (f := f) (by rw [← Nat.card_eq_fintype_card]; exact h)

theorem five_not_dvd_center_aux (hGA : CFSG.Open.GriessAllModelsStatement) {L : Type}
    [Group L] [Finite L] (hq : CFSG.IsQuasisimple L) {t : CFSG.Assembly.LowTwoRank.StatedLieTag}
    {n f : ℕ} (hf : 1 ≤ f)
    (hmod : CFSG.Assembly.LowTwoRank.StatedClassicalModel (L ⧸ Subgroup.center L) t n 5 f) :
    ¬ 5 ∣ Nat.card (Subgroup.center L) := by
  intro h5
  have hd := CFSG.RankThree.PartOne.card_center_dvd_of_model hGA hq hmod
  have h5f : 5 ∣ 5 ^ f := dvd_pow_self 5 (by omega)
  have hpos : 0 < 5 ^ f := by positivity
  rcases CFSG.RankThree.PartOne.prime_dvd_table Nat.prime_five (by norm_num) (h5.trans hd) with
    ⟨-, -, h⟩ | ⟨-, -, h⟩
  · have h1 := Nat.dvd_sub h5f h
    have h2 : 5 ^ f - (5 ^ f - 1) = 1 := by omega
    rw [h2] at h1
    omega
  · have h1 := (Nat.dvd_add_right h5f).mp h
    omega

theorem five_not_dvd_center_of_model (hGA : CFSG.Open.GriessAllModelsStatement) {L : Type}
    [Group L] [Finite L] (hq : CFSG.IsQuasisimple L) {t : StatedLieTag} {n f : ℕ} (hf : 1 ≤ f)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) t n 5 f) :
    ¬ 5 ∣ Nat.card (Subgroup.center L) := by
  cases t
  · exact five_not_dvd_center_aux hGA hq (t := .PSL) hf hmod
  · exact five_not_dvd_center_aux hGA hq (t := .PSU) hf hmod
  · exact five_not_dvd_center_aux hGA hq (t := .PSp) hf hmod
  · exact five_not_dvd_center_aux hGA hq (t := .POmegaOdd) hf hmod
  · exact five_not_dvd_center_aux hGA hq (t := .POmegaPlus) hf hmod
  · exact five_not_dvd_center_aux hGA hq (t := .POmegaMinus) hf hmod
  all_goals exact hmod.2.elim

theorem coverInv_of_inverts (hGA : CFSG.Open.GriessAllModelsStatement) {Q : Type} [Group Q]
    {t : StatedLieTag} {n f : ℕ} (hf : 1 ≤ f) (hQ : StatedClassicalModel Q t n 5 f)
    (hinv : ∀ w : Q, w ≠ 1 → w * w = 1 → InvData Q w) : CoverInv Q :=
  coverInv_of_data hinv fun L _ _ hq hodd he =>
    five_not_dvd_center_of_model hGA (isQuasisimple_of_open hq) hf
      (statedModel_of_mulEquiv he.some.symm hQ)

end CFSG.HardMathSupport.Foote.ModuleExclusions
