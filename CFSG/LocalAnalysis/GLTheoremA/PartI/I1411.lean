module

public import CFSG.LocalAnalysis.GLTheoremA.ExcClubList
public import CFSG.LocalAnalysis.GLTheoremA.PartI.Transfer

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def KDClub : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y), catalogIs ↥K clubIndex →
    ∀ y ∈ Subgroup.normalizer (K : Set Y), y ^ 3 = 1 →
      ¬ K ≤ Subgroup.centralizer ({y} : Set Y) →
      ∀ J : Subgroup Y, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set Y)) J →
        Nat.card (Subgroup.center (PQuot 3 J)) = 1 ∧ catalogIs (PSimple 3 J) clubIndex

section Reduction

theorem nonempty_pQuot_equiv_pSimple {p : ℕ} {G' : Type} [Group G'] {K : Subgroup G'}
    (h : Nat.card (Subgroup.center (PQuot p K)) = 1) : Nonempty (PQuot p K ≃* PSimple p K) := by
  have h1 : Subgroup.center (PQuot p K) = ⊥ := Subgroup.card_eq_one.1 h
  exact ⟨(QuotientGroup.quotientBot (G := PQuot p K)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq h1.symm)⟩

theorem clubData_congr {p : ℕ} {G' G'' : Type} [Group G'] [Group G''] {J : Subgroup G'}
    {J' : Subgroup G''} (e : PQuot p J ≃* PQuot p J') :
    (Nat.card (Subgroup.center (PQuot p J)) = 1 ∧ catalogIs (PSimple p J) clubIndex) ↔
      (Nat.card (Subgroup.center (PQuot p J')) = 1 ∧ catalogIs (PSimple p J') clubIndex) := by
  have hc : Nat.card (Subgroup.center (PQuot p J)) = Nat.card (Subgroup.center (PQuot p J')) :=
    Nat.card_congr (Subgroup.centerCongr e).toEquiv
  have f : PSimple p J ≃* PSimple p J' := QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  rw [hc, catalogIs_congr f]

variable {G : Type} [Group G] [Finite G]

theorem i1411At_of_kdClub (hClub : KDClub) {p : ℕ} (hp : p.Prime) : I1411At G p := by
  intro X K y hK hyp hyN J hJ hclub
  have h3 : p = 3 := hclub.1
  subst h3
  have hy3 : IsPGroup 3 (Subgroup.zpowers y) := isPGroup_zpowers_of_pow_eq_one hyp
  by_cases hCM : CentMod 3 K y
  · obtain ⟨-, hall, -, -, -, ⟨e⟩⟩ := glaPLayer_inf_centralizer hp hK hy3 hCM
    rw [hall J hJ]
    exact (isClubType_congr ⟨e.symm⟩).1 hclub
  · obtain ⟨Q, _, _, K', y', ⟨eK⟩, hnorm, hpow, hnc, hcomp⟩ :=
      exists_pQuot_transfer hp hy3 hyN
    obtain ⟨eS⟩ := nonempty_pQuot_equiv_pSimple hclub.2.1
    have hcat : catalogIs ↥K' clubIndex := (catalogIs_congr (eK.trans eS)).2 hclub.2.2
    obtain ⟨J', hJ', ⟨eJ⟩⟩ := hcomp J hJ
    exact ⟨rfl, (clubData_congr eJ).2
      (hClub Q K' hcat y' hnorm (hpow 3 hyp) (fun h => hCM (hnc h)) J' hJ')⟩

end Reduction

end CFSG.LocalAnalysis.GLTheoremA
