module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDClub.Reduce
public import CFSG.Sporadic.Bridge.M22
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3Mathieu
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporCard

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem kdClubAt_m22 :
    KDClubAt (TauCeti.SporadicName.M22.Group) := by
  classical
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  refine kdClubAt_congr e ?_
  apply kdClubAt_of_solvable
  intro α hα1 hα3
  have hcen : Subgroup.center ↥CFSG.Blueprint.NativeSporadic.M22 = ⊥ :=
    CFSG.Sporadic.Schreier.m22_center_eq_bot'
  have hOut : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      ↥CFSG.Blueprint.NativeSporadic.M22) ≤ 2 := by
    have hinj :=
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.conj_injective_of_center_eq_bot hcen
    have hi : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner
        ↥CFSG.Blueprint.NativeSporadic.M22) = Nat.card ↥CFSG.Blueprint.NativeSporadic.M22 :=
      (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    have hm := Subgroup.card_mul_index (H := CFSG.ComponentClassification.OuterAutomorphisms.inner
        ↥CFSG.Blueprint.NativeSporadic.M22)
    rw [hi] at hm
    have hmul := CFSG.Sporadic.Schreier.m22_mulAut_card
    have hpos : 0 < Nat.card ↥CFSG.Blueprint.NativeSporadic.M22 := Nat.card_pos
    have key : Nat.card ↥CFSG.Blueprint.NativeSporadic.M22 * Nat.card
        (CFSG.ComponentClassification.OuterAutomorphisms.Outer
          ↥CFSG.Blueprint.NativeSporadic.M22) ≤
        Nat.card ↥CFSG.Blueprint.NativeSporadic.M22 * 2 := by
      calc _ = Nat.card (MulAut ↥CFSG.Blueprint.NativeSporadic.M22) := hm
        _ ≤ 2 * Nat.card ↥CFSG.Blueprint.NativeSporadic.M22 := hmul
        _ = _ := mul_comm _ _
    exact Nat.le_of_mul_le_mul_left key hpos
  obtain ⟨a, rfl, ha3⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_conj_of_pow
    Nat.prime_three (by norm_num) hcen hOut α hα3
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hα1 (map_one MulAut.conj)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hperm : orderOf (a : Equiv.Perm (Fin 22)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime ha3 ha1
  have hc36 : ∀ c < CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m22S3Data.cases.size,
      CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m22S3Data.cases[c]!.card = 36 := by
    decide +kernel
  obtain ⟨c, hc, hcard⟩ := CFSG.HardMathSupport.Solomon.Coordinator.B3S3.check_card_sound
    CFSG.HardMathSupport.Solomon.Coordinator.B3S3.m22S3Data
    CFSG.HardMathSupport.Solomon.Coordinator.rep_m22A
    CFSG.HardMathSupport.Solomon.Coordinator.rep_m22B
    Certificates.certificate13511.2.2.1 (a : Equiv.Perm (Fin 22)) a.2 hperm
  have hC : Nat.card ↥(Subgroup.centralizer ({(a : Equiv.Perm (Fin 22))} :
      Set (Equiv.Perm (Fin 22))) ⊓ CFSG.Blueprint.NativeSporadic.M22) = 36 :=
    hcard.trans (hc36 c hc)
  have hcardC : Nat.card ↥(Subgroup.centralizer ({a} : Set ↥CFSG.Blueprint.NativeSporadic.M22))
      = 36 := by
    have h1 := Subgroup.card_map_of_injective
      (K := Subgroup.centralizer ({a} : Set ↥CFSG.Blueprint.NativeSporadic.M22))
      CFSG.Blueprint.NativeSporadic.M22.subtype_injective
    rw [CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_subtype] at h1
    rw [← h1]
    exact hC
  have hfin : Fintype.card ↥(Subgroup.centralizer ({a} : Set ↥CFSG.Blueprint.NativeSporadic.M22))
      = 2 ^ 2 * 3 ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hcardC] <;> norm_num
  have hfix : CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns.fixSub (MulAut.conj a) =
      Subgroup.centralizer ({a} : Set ↥CFSG.Blueprint.NativeSporadic.M22) := by
    ext x
    rw [CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns.mem_fixSub, MulAut.conj_apply,
      mul_inv_eq_iff_eq_mul, Subgroup.mem_centralizer_singleton_iff]
    exact eq_comm
  rw [hfix]
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
    Nat.prime_two Nat.prime_three (by norm_num) hfin

end CFSG.LocalAnalysis.GLTheoremA
