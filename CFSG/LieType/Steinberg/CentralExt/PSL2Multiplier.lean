module

public import CFSG.LieType.Steinberg.CentralExt.SL2CentrallyClosed
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

open Matrix
open scoped MatrixGroups

namespace CFSG.LieType.Steinberg.CentralExt.SL2Closed

theorem card_rootsOfUnity_two {k : Type} [Field k] [Fintype k] :
    Nat.card (rootsOfUnity 2 k) = Nat.gcd 2 (Fintype.card k - 1) := by
  have hle : Nat.card (rootsOfUnity 2 k) ≤ 2 := card_rootsOfUnity k 2
  have hval : ∀ u : kˣ, u ∈ rootsOfUnity 2 k ↔ (u : k) ^ 2 = 1 := fun u => by
    rw [mem_rootsOfUnity, ← Units.val_inj, Units.val_pow_eq_pow_val, Units.val_one]
  by_cases h2 : ringChar k = 2
  · have : CharP k 2 := ringChar.of_eq h2
    have h1 : ∀ u ∈ rootsOfUnity 2 k, u = 1 := by
      intro u hu
      have hu' : ((u : k) - 1) ^ 2 = 0 := by
        rw [sub_pow_char (R := k) (p := 2) (u : k) 1, (hval u).1 hu, one_pow, sub_self]
      exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 hu'))
    have hcard : Nat.card (rootsOfUnity 2 k) = 1 := by
      rw [Nat.card_eq_one_iff_exists]
      exact ⟨1, fun u => Subtype.ext (h1 u u.2)⟩
    have heven := FiniteField.even_card_of_char_two h2
    rw [hcard]
    have : Odd (Fintype.card k - 1) := by
      have h1 : 1 ≤ Fintype.card k := Fintype.card_pos
      rw [Nat.odd_iff]
      omega
    exact (Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.2 this)).symm
  · have hne : (-1 : k) ≠ 1 := Ring.neg_one_ne_one_of_char_ne_two h2
    have hmem : (-1 : kˣ) ∈ rootsOfUnity 2 k := by
      rw [hval]
      simp
    have h2le : 2 ≤ Nat.card (rootsOfUnity 2 k) := by
      have hne' : (rootsOfUnity 2 k) ≠ ⊥ := by
        intro h
        have : (-1 : kˣ) ∈ (⊥ : Subgroup kˣ) := h ▸ hmem
        rw [Subgroup.mem_bot] at this
        have h' := congrArg Units.val this
        rw [Units.val_neg, Units.val_one] at h'
        exact hne h'
      exact (Subgroup.one_lt_card_iff_ne_bot _).2 hne'
    have hodd := FiniteField.odd_card_of_char_ne_two h2
    have : Even (Fintype.card k - 1) := by
      rw [Nat.even_iff]
      have h1 : 1 ≤ Fintype.card k := Fintype.card_pos
      omega
    rw [le_antisymm hle h2le, Nat.gcd_eq_left (even_iff_two_dvd.1 this)]

theorem psl_two_hopfMultiplier
    {k : Type} [Field k] [Fintype k] (hk : 5 ≤ Fintype.card k) (hk9 : Fintype.card k ≠ 9) :
    commutator PSL(2, k) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier PSL(2, k) ≃*
        Multiplicative (ZMod (Nat.gcd 2 (Fintype.card k - 1)))) := by
  have hk' : 5 ≤ Nat.card k := by rwa [← Fintype.card_eq_nat_card]
  have hk9' : Nat.card k ≠ 9 := by rwa [← Fintype.card_eq_nat_card]
  set q : SpecialLinearGroup (Fin 2) k →* PSL(2, k) :=
    QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) k))
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hker : q.ker = Subgroup.center (SpecialLinearGroup (Fin 2) k) := QuotientGroup.ker_mk' _
  have : Group.IsPerfect (SpecialLinearGroup (Fin 2) k) :=
    LinearGroups.special_linear_dimension_two_perfect (exists_four_of_five_le hk')
  have hperf : Group.IsPerfect PSL(2, k) := Group.IsPerfect.ofSurjective hq
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  obtain ⟨e⟩ := sl2_hopfMultiplier_mulEquiv_ker hk' hk9' q hq hker.le
  have hroots : rootsOfUnity (max (Fintype.card (Fin 2)) 1) k = rootsOfUnity 2 k := by simp
  let e2 : q.ker ≃* rootsOfUnity 2 k :=
    (MulEquiv.subgroupCongr hker).trans ((SpecialLinearGroup.center_equiv_rootsOfUnity).trans
      (MulEquiv.subgroupCongr hroots))
  have hcyc : IsCyclic (rootsOfUnity 2 k) := inferInstance
  rw [← card_rootsOfUnity_two]
  exact ⟨(CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).trans
    (e.trans (e2.trans (zmodCyclicMulEquiv hcyc).symm))⟩

end CFSG.LieType.Steinberg.CentralExt.SL2Closed

