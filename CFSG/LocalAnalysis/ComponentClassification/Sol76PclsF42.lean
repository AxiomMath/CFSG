module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsMain

public section

namespace CFSG.ComponentClassification.Sol76T13.R12.Pcls

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.CentralExt CFSG.LocalAnalysis.ComponentInitial.F4FieldTwoCover
open scoped commutatorElement

abbrev f42RootE2m4 : Fin Tag.F4.rank → ℤ := ![1, 1, 0, 0]

theorem f42CoverInput :
    F42CoverInput := by
  intro Q _ _ hQ hO hL z hzZ hz2
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := GriessNative.chevalley_of_lieModel hL (by decide)
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  have : CharP K 2 := GriessNative.charP_two_of_card le_rfl hK rfl
  let eA : AdjointQuotient .F4 K ≃* adjointGroup .F4 K :=
    (QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans QuotientGroup.quotientBot
  let f : Q ⧸ center Q ≃* adjointGroup .F4 K := e.trans eA
  set η : Q →* adjointGroup .F4 K := f.toMonoidHom.comp (QuotientGroup.mk' (center Q)) with hη
  have hηs : Function.Surjective η := f.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = center Q := ker_quotientMap f
  have hr1 : IsRoot .F4 vL1 := isRoot_of_ofFn (by decide +kernel)
  have hr2 : IsRoot .F4 vL2 := isRoot_of_ofFn (by decide +kernel)
  obtain ⟨a, ha, ha2⟩ := exists_lift_mul_self_xr hK2 hηs hker.le hr1
  obtain ⟨b, hb, hb2⟩ := exists_lift_mul_self_xr hK2 hηs hker.le hr2
  have hab : a * b = b * a := (liftsCommute_longRow hK2 hηs hker.le b a hb ha).symm
  have hxr1 : ∀ r, xr (K := K) r ≠ 1 := fun r h => by
    have h' : pinnedX .F4 K r 1 = pinnedX .F4 K r 0 := by
      rw [pinnedX_zero]
      exact congrArg Subtype.val h
    exact one_ne_zero (pinnedX_injective .F4 K r h')
  have hne : xr (K := K) vL1 ≠ xr vL2 := by
    intro h
    obtain ⟨-, hc⟩ := xr_commutatorElement_obtuse (K := K) hK2 (r := f42RootE2m4) (s := vL1)
      (rootPair_of_ofFn (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    have hcomm := xr_commute (K := K) hK2 (r := f42RootE2m4) (s := vL2)
      (rootPair_of_ofFn (by decide +kernel)) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
    apply hxr1 (f42RootE2m4 + vL1)
    rw [← hc, h, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm
  have hxx : xr (K := K) vL1 * xr vL2 ≠ 1 := fun h => by
    have h1 := eq_inv_of_mul_eq_one_left h
    rw [inv_eq_of_mul_eq_one_right (xr_mul_self hK2 hr2)] at h1
    exact hne h1
  have hz1 : z ≠ 1 := by rintro rfl; rw [orderOf_one] at hz2; omega
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  exact three_le_pRank_of_four_group (τ := MonoidHom.id Q) (πG := η) (πQ := η) (fun _ => rfl)
    ha2 hb2 hab (by rw [ha]; exact hxr1 _) (by rw [hb]; exact hxr1 _)
    (by rw [map_mul, ha, hb]; exact hxx) hzZ hzz hz1
    (by rw [← MonoidHom.mem_ker, hker]; exact hzZ)

end CFSG.ComponentClassification.Sol76T13.R12.Pcls
