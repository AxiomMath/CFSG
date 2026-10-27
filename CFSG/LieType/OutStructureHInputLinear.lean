module

public import CFSG.GroupTheory.FixedPointQuotientCard
public import CFSG.LieType.OutStructureActionMap
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

public section

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace CFSG.LieType.OutStructure

theorem pRank_autFixedSubgroup_congr {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    {p : ℕ} (hp : 1 < p) (e : G ≃* H) (a : MulAut G) :
    CFSG.Open.pRank p (CFSG.autFixedSubgroup a) =
      CFSG.Open.pRank p (CFSG.autFixedSubgroup (MulAut.congr e a)) := by
  have hmap : (CFSG.autFixedSubgroup a).map e.toMonoidHom ≤
      CFSG.autFixedSubgroup (MulAut.congr e a) := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : a y = y := CFSG.mem_autFixedSubgroup.mp hy
    refine CFSG.mem_autFixedSubgroup.mpr ?_
    change e (a (e.symm (e y))) = e y
    rw [e.symm_apply_apply, hy']
  have h1 : CFSG.Open.pRank p (CFSG.autFixedSubgroup a) ≤
      CFSG.Open.pRank p (CFSG.autFixedSubgroup (MulAut.congr e a)) :=
    (CFSG.SectionRank.pRank_le_map hp e.toMonoidHom e.injective _).trans
      (CFSG.SectionRank.pRank_mono hp hmap)
  have hmap' : (CFSG.autFixedSubgroup (MulAut.congr e a)).map e.symm.toMonoidHom ≤
      CFSG.autFixedSubgroup a := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : MulAut.congr e a y = y := CFSG.mem_autFixedSubgroup.mp hy
    refine CFSG.mem_autFixedSubgroup.mpr ?_
    have h2 : e (a (e.symm y)) = e (e.symm y) := by
      rw [show e (a (e.symm y)) = MulAut.congr e a y from rfl, hy', e.apply_symm_apply]
    exact e.injective h2
  have h2 : CFSG.Open.pRank p (CFSG.autFixedSubgroup (MulAut.congr e a)) ≤
      CFSG.Open.pRank p (CFSG.autFixedSubgroup a) :=
    (CFSG.SectionRank.pRank_le_map hp e.symm.toMonoidHom e.symm.injective _).trans
      (CFSG.SectionRank.pRank_mono hp hmap')
  exact le_antisymm h1 h2

variable {X : Type*} [Group X] [Finite X] {L : Subgroup X} [L.Normal] {p : ℕ}

theorem quotientAut_conjNormal_eq_conjHom (x : X) :
    CFSG.quotientAut (MulAut.conjNormal (H := L) x) = conjHom (L := L) x := by
  ext y
  obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥L) y
  rw [CFSG.quotientAut_mk, conjHom_apply, conjOnCenterQuotient_apply]

theorem autFixedSubgroup_quotientAut_eq_map (hp : p.Prime) (α : MulAut ↥L) (hαp : α ^ p = 1)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥L)) :
    CFSG.autFixedSubgroup (CFSG.quotientAut α) =
      (CFSG.autFixedSubgroup α).map (QuotientGroup.mk' (Subgroup.center ↥L)) := by
  have hordα : orderOf α ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hαp
  have hcopα : Nat.Coprime (orderOf α) (Nat.card (Subgroup.center ↥L)) := by
    rcases (Nat.dvd_prime hp).mp hordα with h1 | hp'
    · rw [h1]; exact Nat.coprime_one_left _
    · rw [hp']; exact hp.coprime_iff_not_dvd.mpr hZ
  let A := Subgroup.zpowers α
  let Z : Subgroup ↥L := Subgroup.center ↥L
  have hcardA : Nat.card A = orderOf α := Nat.card_zpowers α
  have hcopZ : Nat.Coprime (Nat.card A) (Nat.card Z) := by
    rw [hcardA]; exact hcopα
  letI : Z.Characteristic := Subgroup.centerCharacteristic
  letI hInv : CFSG.IsInvariant A ↥L Z := CFSG.isInvariant_of_characteristic Z
  letI : IsMulCommutative Z := Subgroup.center.isMulCommutative (G := ↥L)
  letI : MulDistribMulAction A (↥L ⧸ Z) :=
    CFSG.quotientMulDistribMulAction (A := A) (G := ↥L) Z hInv
  have hC : CFSG.fixedPointSubgroup A ↥L = CFSG.autFixedSubgroup α := by
    simpa [A] using CFSG.fixedPointSubgroup_zpowers_eq_autFixedSubgroup (J := ↥L) α
  have hQ : CFSG.fixedPointSubgroup A (↥L ⧸ Z) =
      CFSG.autFixedSubgroup (CFSG.quotientAut α) := by
    simpa [A, Z] using CFSG.fixedPointSubgroup_quotient_eq_autFixedSubgroup (J := ↥L) α
  have hquot : CFSG.fixedPointSubgroup A (↥L ⧸ Z) =
      (CFSG.fixedPointSubgroup A ↥L).map (QuotientGroup.mk' Z) :=
    CFSG.fixedPointSubgroup_quotient_eq_map_of_isMulCommutative (G := ↥L) (A := A) Z hInv hcopZ
  rw [hQ, hC] at hquot
  exact hquot

end CFSG.LieType.OutStructure
