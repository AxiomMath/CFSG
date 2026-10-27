module

public import CFSG.ClassicalInvolution.Q3.Q3PlanSplit
public import CFSG.ClassicalInvolution.Q3.Q3PlanTags

public section

namespace CFSG.ClassicalInvolution.Q3

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.ModelFacts
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

section Sp

variable {F : Type} [Field F] {m : ℕ} {z : StatedSp m F}

theorem longRootGroup_inf_complGroup_eq_bot (h2 : (2 : F) ≠ 0) (hz : z * z = 1) :
    longRootGroup z ⊓ complGroup z = ⊥ := by
  refine eq_bot_iff.mpr fun x ⟨hx1, hx2⟩ => ?_
  rw [Subgroup.mem_bot]
  have h1 := (mem_longRootGroup_iff_mat h2 hz).mp hx1
  have h2' := (mem_complGroup_iff_mat h2 hz).mp hx2
  have hsum : mat m F x * (ePlus (mat m F z) + eMinus (mat m F z)) =
      ePlus (mat m F z) + eMinus (mat m F z) := by
    rw [Matrix.mul_add, h1, h2']
  have hone : ePlus (mat m F z) + eMinus (mat m F z) = 1 := by
    unfold ePlus eMinus
    rw [← smul_add]
    have : (1 + mat m F z) + (1 - mat m F z) = (2 : F) • (1 : Matrix (Fin m ⊕ Fin m)
        (Fin m ⊕ Fin m) F) := by
      rw [two_smul]
      abel
    rw [this, smul_smul, inv_mul_cancel₀ h2, one_smul]
  rw [hone, Matrix.mul_one] at hsum
  apply mat_injective
  rw [hsum, map_one]

end Sp

section Main

private theorem natCard_galoisField_three : Nat.card (GaloisField 3 1) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [GaloisField.card 3 1 (by norm_num)]
  norm_num

private theorem two_ne_zero_galoisField_three : (2 : GaloisField 3 1) ≠ 0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h0
  have : ringChar (GaloisField 3 1) ∣ 2 := ringChar.dvd (by simpa using h0)
  rw [ringChar.eq (GaloisField 3 1) 3] at this
  omega

theorem open_isQuasisimple_statedSp_three {a : ℕ} (ha : 2 ≤ a) :
    CFSG.Open.IsQuasisimple (StatedSp a (GaloisField 3 1)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (GaloisField 3 1) = 3 ^ 1 := GaloisField.card 3 1 (by norm_num)
  have hadm : StatedLieAdmissible .PSp a 3 1 := ⟨Nat.prime_three, le_rfl, ha, fun h' => by
    have := congrArg Prod.snd h'
    simp only at this
    omega⟩
  exact open_isQuasisimple
    (CFSG.LieType.Universal.Symplectic.isQuasisimple_of_admissible a (GaloisField 3 1) hadm hcard)

theorem isLongRootSp2_of_isClassicalMember3 {m : ℕ}
    {L : Subgroup (StatedSp m (GaloisField 3 1))} {z : StatedSp m (GaloisField 3 1)}
    (h : IsClassicalMember3 L z) (hO : classicalInvolutionOddCore L = ⊥) : IsLongRootSp2 L z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set F := GaloisField 3 1 with hFdef
  have hF3 : Nat.card F = 3 := natCard_galoisField_three
  have h2 : (2 : F) ≠ 0 := two_ne_zero_galoisField_three
  obtain ⟨eL⟩ := h.nonempty_equiv_sl2 hO
  let e : SL(2, ZMod 3) ≃* L := eL.symm
  obtain ⟨e3⟩ := nonempty_mulEquiv_sl2Three_of_natCard_eq_three hF3
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.orderOf_eq_two, pow_two] at this
  have hz1 : z ≠ 1 := h.ne_one
  obtain ⟨S, g, hg⟩ := exists_mul_eq_stdInv h2 hzz
  have hzg : z = g * stdInv F S * g⁻¹ := by rw [← hg]; group
  have hLC : ∀ x ∈ L, x * z = z * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le h.subnormal hx)
  have hLsup : L ≤ longRootGroup z ⊔ complGroup z := fun x hx => by
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_commute h2 hzz (hLC x hx)
    exact Subgroup.mul_mem_sup ha hb
  have hcomm : ∀ x ∈ longRootGroup z, ∀ y ∈ complGroup z, x * y = y * x :=
    fun x hx y hy => commute_of_mem_longRootGroup_of_mem_complGroup h2 hzz hx hy
  have hinf : longRootGroup z ⊓ complGroup z = ⊥ := longRootGroup_inf_complGroup_eq_bot h2 hzz
  have hAC : longRootGroup z ≤ Subgroup.centralizer ({z} : Set (StatedSp m F)) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_mem_longRootGroup h2 hzz hx)
  have hBC : complGroup z ≤ Subgroup.centralizer ({z} : Set (StatedSp m F)) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_mem_complGroup h2 hzz hx)
  have hsub : IsSubnormal L (longRootGroup z ⊔ complGroup z) := by
    have := isSubnormal_inf h.subnormal (longRootGroup z ⊔ complGroup z)
    rwa [inf_eq_left.mpr hLsup, inf_eq_right.mpr (sup_le hAC hBC)] at this
  have hzA : z ∈ longRootGroup z := mem_longRootGroup_self h2 hzz
  have hSa : 1 ≤ S.card := by
    by_contra hlt
    have hS : S = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hS
    rw [stdInv_empty, mul_one] at hg
    exact hz1 (mul_right_cancel (hg.trans (one_mul g).symm))
  obtain ⟨eAm⟩ := nonempty_mulEquiv_longRootGroup_sp h2 hzg
  obtain ⟨eAp⟩ := nonempty_mulEquiv_complGroup_sp h2 hzg
  have hB : Subsingleton (complGroup z) ∨
      (CFSG.Open.IsQuasisimple (complGroup z) ∧ IsPGroup 2 (Subgroup.center (complGroup z))) ∨
      Nonempty (SL(2, ZMod 3) ≃* complGroup z) := by
    generalize (Sᶜ).card = b at eAp
    rcases Nat.lt_or_ge b 2 with hb | hb
    · rcases Nat.lt_or_ge b 1 with hb0 | hb1
      · left
        obtain rfl : b = 0 := by omega
        have : Subsingleton (StatedSp 0 F) := subsingleton_statedSp_zero
        exact eAp.surjective.subsingleton
      · right
        right
        obtain rfl : b = 1 := by omega
        exact ⟨e3.symm.trans ((longBlockEquivOne (K := F)).trans eAp)⟩
    · right
      left
      exact ⟨CFSG.ComponentClassification.Components.quasisimple_of_equiv eAp.symm
        (open_isQuasisimple_statedSp_three hb),
        (CenterExp.of_mulEquiv eAp.symm
          (centerExp_statedSp b 1 F (by rw [hF3]; norm_num))).isPGroup⟩
  have hLA : L ≤ longRootGroup z :=
    le_of_isSubnormal_of_commute hcomm hinf e hLsup hsub hB h.mem hz1 hzA
  have hLA' : IsSubnormal L (longRootGroup z) := by
    have := isSubnormal_inf h.subnormal (longRootGroup z)
    rwa [inf_eq_left.mpr hLA, inf_eq_right.mpr hAC] at this
  have hS1 : S.card = 1 := by
    by_contra hne
    exact not_isQuasisimple_of_member3 e hLA hLA'
      (CFSG.ComponentClassification.Components.quasisimple_of_equiv eAm.symm
        (open_isQuasisimple_statedSp_three (by omega)))
  have hcard : Nat.card (longRootGroup z) = 24 := by
    have h1 := Nat.card_congr eAm.toEquiv
    rw [hS1] at h1
    calc Nat.card (longRootGroup z) = Nat.card (StatedSp 1 F) := h1.symm
      _ = Nat.card SL(2, F) := (Nat.card_congr (longBlockEquivOne (K := F)).toEquiv).symm
      _ = Nat.card SL(2, ZMod 3) := Nat.card_congr e3.toEquiv
      _ = 24 := natCard_sl2Three
  have : Finite (longRootGroup z) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hLeq : L = longRootGroup z := eq_of_le_of_natCard_le e hLA hcard.le
  obtain ⟨k, rfl⟩ := Finset.card_eq_one.mp hS1
  rw [stdInv_singleton] at hzg
  refine ⟨k, g, ?_, hzg⟩
  rw [hLeq, hzg, longRootGroup_conj, longRootGroup_longInv h2, longRootSp2_eq_suppGroup]

theorem classicalMembersFundamental3Tag_PSp : ClassicalMembersFundamental3Tag .PSp := by
  intro n hp hFT hadm L z hL hO
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨P, hP, hLP⟩ := (exists_isLongRootSp2_iff two_ne_zero_galoisField_three L).mp
    ⟨z, isLongRootSp2_of_isClassicalMember3 hL hO⟩
  exact (mem_fundamentalSubgroups_PSp_iff hadm L).mpr ⟨P, hP, hLP⟩

end Main

end CFSG.ClassicalInvolution.Q3
