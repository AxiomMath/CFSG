module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12InputsS8
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModBurn
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModFacX
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModOrd3

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial

theorem sec12S8Mod_fixed_pow {G : Type} [Group G] {V : Subgroup G} (hV : IsElemAb2 V 8)
    (q : MulAut ↥V) : ∃ k : ℕ, Nat.card {v : ↥V // q v = v} = 2 ^ k := by
  let K : Subgroup ↥V := MonoidHom.eqLocus q.toMonoidHom (MonoidHom.id ↥V)
  have hK : Nat.card K ∣ 2 ^ 8 := by
    rw [← hV.2]
    exact Subgroup.card_subgroup_dvd_card K
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hK
  refine ⟨k, ?_⟩
  rw [← hk]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun v => Iff.rfl)

theorem asc82S8NoL34X_of : Asc82S8NoL34X := by
  intro G _ V X V1 V2 Z hV hsup hinf hA5 hn1 hn2 hXZ hL
  have hmod := LieModel.statedClassicalModel_of_ne_zero (by norm_num : (3 : ℕ) ≠ 0) hL
  obtain ⟨-, K, hK, hKfin, hcard, ⟨e⟩⟩ := hmod
  have hk4 : Nat.card K = 4 := by rw [hcard]; norm_num
  let e' : ↥Z ≃* LinearFlag.projectiveSL 3 K :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq (LinearFlag.scalars_eq_center 3 K)).trans
      (projectiveSpecialLinearGroupEquivStatedProj 3 K)).symm
  have hZcard : Nat.card ↥Z = 20160 := by
    rw [Nat.card_congr e'.toEquiv]
    exact CFSG.RankThree.PartTwo.KFacts.L34.card_projectiveSL hk4
  haveI : Finite ↥Z := Nat.finite_of_card_ne_zero (by rw [hZcard]; norm_num)
  haveI : Finite ↥V := Nat.finite_of_card_ne_zero (by rw [hV.2]; positivity)
  obtain ⟨g, h, hgX, hhX, hg5, hgfix, hh3, hh1, hhfix⟩ :=
    sec12S8Mod_facX hV hsup hinf hA5 hn1 hn2
  have hhZ : h ∈ Z := hXZ hhX
  have hord : orderOf (⟨h, hhZ⟩ : ↥Z) = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime (Subtype.ext hh3) fun h1 => hh1 (congrArg Subtype.val h1)
  have hconj : ∀ a b : ↥Z, orderOf a = 3 → orderOf b = 3 → IsConj a b := by
    intro a b ha hb
    have ha' : orderOf (e' a) = 3 := by rw [MulEquiv.orderOf_eq]; exact ha
    have hb' : orderOf (e' b) = 3 := by rw [MulEquiv.orderOf_eq]; exact hb
    obtain ⟨c, hc⟩ := isConj_iff.1 (sec12S8Mod_conj3 hk4 ha' hb')
    refine isConj_iff.2 ⟨e'.symm c, e'.injective ?_⟩
    simpa [map_mul, map_inv] using hc
  exact sec12S8Mod_burn (Q := ↥Z) (Ω := ↥V) hZcard hV.2 hconj ⟨h, hhZ⟩ hord hhfix
    fun q => sec12S8Mod_fixed_pow hV (q : MulAut ↥V)

end CFSG.OddStandard.SmallF3.Omega
