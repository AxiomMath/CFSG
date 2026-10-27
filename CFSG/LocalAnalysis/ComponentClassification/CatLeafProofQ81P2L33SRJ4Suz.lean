module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33SRCommon
public import CFSG.Sporadic.Co2Schreier.OddCore
public import CFSG.Sporadic.Schreier.J4SOutOdd
public import CFSG.Sporadic.SuzOddCore.SmallAut

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.SR

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.J4Schreier CFSG.Sporadic.SuzOddCore

theorem not_isPGroup_of_mul_card_eq {G : Type*} [Group G] [Finite G] {K C : Subgroup G}
    (hKC : K ≤ C) {s n : ℕ} (h : Nat.card ↥K * s = n) (hs : 0 < s) (h3 : 3 ∣ n / s) :
    ¬ IsPGroup 2 ↥C := by
  refine not_isPGroup_of_le hKC (not_isPGroup_of_three_dvd ?_)
  rwa [← h, Nat.mul_div_cancel _ hs] at h3

theorem j4_eta_centralizer_not_isPGroup :
    ¬ IsPGroup 2 ↥(centralizer ({η 1} : Set ↥CFSG.Sporadic.J4.J)) ∧
      ¬ IsPGroup 2 ↥(centralizer ({η 14} : Set ↥CFSG.Sporadic.J4.J)) := by
  obtain ⟨-, -, -, h1, h14, -⟩ := QT_unique_J4_local_normal_module_irreducible
  have c1 := card_H_inf_centralizer (η_mem_N 1) h1
  have c14 := card_H_inf_centralizer (η_mem_N 14) h14
  rw [card_H] at c1 c14
  exact ⟨not_isPGroup_of_mul_card_eq inf_le_right c1 (by norm_num) (by norm_num),
    not_isPGroup_of_mul_card_eq inf_le_right c14 (by norm_num) (by norm_num)⟩

theorem sporNoTwoFix_J4 :
    SporNoTwoFix .J4 := by
  intro Y _ _ ⟨e⟩
  have e' : Y ≃* ↥CFSG.Sporadic.J4.J :=
    e.trans (CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat)
  have hsY : IsSimpleGroup Y :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J4.isSimpleGroup_J4 e
  have hZ : center Y = ⊥ := center_eq_bot_of_not_prime hsY
    ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J4.card_J4) (by norm_num)
  have hodd : Odd (Nat.card (OuterAutomorphisms.Outer Y)) := by
    rw [Nat.card_congr (@OuterAutomorphisms.equivalence Y _ _ (Subgroup.toGroup _) e').toEquiv]
    exact CTU_J4_outer_automorphism_group_odd_order
  obtain ⟨hc1, hc14⟩ := j4_eta_centralizer_not_isPGroup
  have hC : ∀ t : Y, orderOf t = 2 → ¬ IsPGroup 2 ↥(centralizer ({t} : Set Y)) := by
    intro t ht
    have hs : orderOf (e' t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
    obtain ⟨-, g, hg⟩ := CTU_J4_every_inner_involution_conjugate_into_local_binary_subgroup _ hs
    have h1 : ¬ IsPGroup 2 ↥(centralizer ({e' t} : Set ↥CFSG.Sporadic.J4.J)) := by
      rcases hg with hg | hg
      · exact not_isPGroup_centralizer_of_isConj
          ((@isConj_iff _ (Subgroup.toGroup _) _ _).mpr ⟨g, hg⟩).symm hc1
      · exact not_isPGroup_centralizer_of_isConj
          ((@isConj_iff _ (Subgroup.toGroup _) _ _).mpr ⟨g, hg⟩).symm hc14
    exact @not_isPGroup_of_mulEquiv _ _ _ (Subgroup.toGroup _)
      (@CFSG.Sporadic.Co2Schreier.centralizerMap Y _ _ (Subgroup.toGroup _) e' t) h1
  intro α hα
  have hα2 : α ^ 2 = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
  obtain ⟨t, rfl⟩ := mem_inner_of_odd_outer hodd hα2
  exact not_isPGroup_fixedPoints_conj hZ hC hα

theorem sporNoTwoFix_Suz :
    SporNoTwoFix .Suz := by
  refine sporNoTwoFix_of_mulEquiv (P := ↥suzM) suzEquivM fun α hα => ?_
  set x : suzT := (MulEquiv.ofBijective suzConjT suzConjT_bijective).symm α with hxdef
  have hxα : suzConjT x = α :=
    (MulEquiv.ofBijective suzConjT suzConjT_bijective).apply_symm_apply α
  have hx : ∀ m : suzM, ((α m : suzM) : Equiv.Perm (Fin 1782)) =
      x * m * (x : Equiv.Perm (Fin 1782))⁻¹ := by
    intro m
    rw [← hxα, suzConjT_apply]
  have hxo : orderOf (x : Equiv.Perm (Fin 1782)) = 2 := by
    rw [Subgroup.orderOf_coe, ← orderOf_injective suzConjT suzConjT_injective x, hxα, hα]
  refine not_isPGroup_fixedPoints_of_conj hx ?_
  obtain ⟨i, ⟨hi, c, hc, he⟩, -⟩ := suzT_involution_class x.2 hxo
  rw [← he]
  refine not_isPGroup_inf_centralizer_conj_of_normalizes (fun h hh => suzT_conj_mem' hc hh) ?_
  have hE := invE_eq_centM hi
  rw [centM] at hE
  rw [inf_comm, ← hE]
  apply not_isPGroup_of_three_dvd
  rw [card_invE hi]
  interval_cases i <;> simp [invInnerOrders]

end CFSG.ComponentClassification.HarrisLit.L33.SR
