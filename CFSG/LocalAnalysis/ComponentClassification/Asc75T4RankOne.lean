module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4RankOneBasic
public import CFSG.LocalAnalysis.ComponentClassification.AS76bExistBasic
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Main
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Assembly

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix
open CFSG.SignalizerFunctor.Helpers
open CFSG.Open (aschbacherThm5Core)

namespace RankOne

variable {G : Type} [Group G] [Finite G]

theorem not_shape_bar {Q T S : Subgroup G} (hK : twoPrimeLayerIn Q ≠ oddCoreIn Q)
    (h4 : ¬ HasFourGroup (twoPrimeLayerIn Q)) (hm : 1 < CFSG.Open.pRank 2 Q)
    (hS : IsSylowOf 2 S (Q ⊔ T)) (hTH : T ≤ normalizer (Q : Set G))
    (hshape : IsCyclic (bar Q S ⊓ bar Q Q : Subgroup (Bar Q)) ∨
      AschbacherTheorem3.IsQuaternionTwoGroup (bar Q S ⊓ bar Q Q) ∨
      AschbacherTheorem3.IsDihedralTwoGroup (bar Q S ⊓ bar Q Q)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQT : Q ⊔ T ≤ normalizer (Q : Set G) := sup_le le_normalizer hTH
  have hSQ : IsSylowOf 2 (S ⊓ Q) Q := hS.inf_of_le_normalizer le_sup_left hQT
  have hRN : S ⊓ Q ≤ normalizer (Q : Set G) := inf_le_right.trans le_normalizer
  have hbar : bar Q (S ⊓ Q) = bar Q S ⊓ bar Q Q :=
    bar_inf_of_core_le (AschbacherTheorem5.core_le Q)
  let e : (S ⊓ Q : Subgroup G) ≃* (bar Q S ⊓ bar Q Q : Subgroup (Bar Q)) :=
    (barEquiv hSQ.isPGroup hRN).trans (MulEquiv.subgroupCongr hbar)
  obtain ⟨E, hER, hE, hE4⟩ := hasFourGroup_of_isSylowOf hSQ (hasFourGroup_of_one_lt_pRank hm)
  have hKQT : Q ⊔ T ≤ normalizer (twoPrimeLayerIn Q : Set G) :=
    sup_le (normalIn_le_normalizer (twoPrimeLayerIn_normalIn Q))
      (hTH.trans (normalizer_le_normalizer_twoPrimeLayerIn Q))
  have hZ : IsSylowOf 2 (S ⊓ twoPrimeLayerIn Q) (twoPrimeLayerIn Q) :=
    hS.inf_of_le_normalizer ((twoPrimeLayerIn_le Q).trans le_sup_left) hKQT
  have hZR : S ⊓ twoPrimeLayerIn Q ≤ S ⊓ Q := inf_le_inf_left S (twoPrimeLayerIn_le Q)
  have hZc : ¬ IsCyclic (S ⊓ twoPrimeLayerIn Q : Subgroup G) := fun hc =>
    not_isSolvable_twoPrimeLayerIn hK (isSolvable_of_isSylowOf_isCyclic hZ hc)
  have hZ4 : ¬ HasFourGroup (S ⊓ twoPrimeLayerIn Q) := fun h => h4 (h.mono inf_le_right)
  rcases hshape with hc | ⟨n, hn, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩
  · have : IsCyclic (S ⊓ Q : Subgroup G) :=
      isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
    exact not_isCyclic_of_fourGroup hER hE hE4 this
  · exact false_of_le_cyclic_or_quaternion hER (TwoGroups.isElemAbelian_of_sq hE) hE4
      (Or.inr ⟨n, hn, ⟨e.trans f⟩⟩)
  · exact hZc (isCyclic_of_le_isDihedral ⟨n, hn, ⟨e.trans f⟩⟩ hZR hZ4)

theorem commutator_mem_oddCoreIn (h3 : AschbacherTheorem3.Theorem3Statement) {Q : Subgroup G}
    (htight : TightlyEmbedded Q) (hK : twoPrimeLayerIn Q ≠ oddCoreIn Q)
    (h4 : ¬ HasFourGroup (twoPrimeLayerIn Q)) (hno3 : ¬ Thm4Case3 Q)
    (hm : 1 < CFSG.Open.pRank 2 Q) {g : G} (hg : g ∉ normalizer (Q : Set G)) {T : Subgroup G}
    (hT : IsSylowOf 2 T (rightConjugate Q g ⊓ normalizer (Q : Set G))) (hT1 : T ≠ ⊥) :
    ∀ t ∈ T, ∀ k ∈ twoPrimeLayerIn Q, t * k * t⁻¹ * k⁻¹ ∈ oddCoreIn Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ normalizer (Q : Set G) := hT.le.trans inf_le_right
  obtain ⟨S, hS, hTS, -, hconc⟩ := exists_thm3Conclusion h3 htight hg hT hT1
  have hQn : bar Q Q ≤ normalizer (bar Q Q : Set (Bar Q)) := le_normalizer
  have hTn : bar Q T ≤ normalizer (bar Q Q : Set (Bar Q)) := bar_le_normalizer hTH le_normalizer
  have hSn : bar Q S ≤ normalizer (bar Q Q : Set (Bar Q)) := by
    refine (bar_mono Q hS.le).trans ?_
    rw [bar_sup le_normalizer hTH]
    exact sup_le hQn hTn
  have hS2 : IsPGroup 2 (bar Q S) := isPGroup_bar hS.isPGroup
  have hTSb : bar Q T ≤ bar Q S := bar_mono Q hTS
  suffices hW : ∃ W : Subgroup (Bar Q), IsPGroup 2 W ∧ bar Q T ≤ W ∧
      W ≤ normalizer (bar Q Q : Set (Bar Q)) ∧ bar Q Q ≤ normalizer (W : Set (Bar Q)) by
    obtain ⟨W, hW2, hTW, hWN, hNW⟩ := hW
    have hWs : Group.IsSolvable W := by
      have := hW2.isNilpotent
      infer_instance
    exact commutator_mem_oddCoreIn_of_solvable hTH hWs hTW hWN hNW
  rcases hconc with ⟨-, hshape, -⟩ | h2 | h3' | ⟨x, hx, -, -, -, -, hN4, -, -⟩ |
      ⟨hN5, -, -, -, -, -, -⟩
  · exact (not_shape_bar hK h4 hm hS hTH hshape).elim
  · exact ⟨bar Q T, isPGroup_bar hT.isPGroup, le_rfl, hTn, le_sup_left.trans h2⟩
  · exact (noThm3Alt3_of_not_thm4Case3 htight hno3 g hg T hT h3').elim
  · exact ⟨_, hS2.to_le (relative_weak_closure_le _ _ _),
      subgroup_le_relative_weak_closure _ _ _ hTSb, (relative_weak_closure_le _ _ _).trans hSn,
      le_sup_left.trans hN4⟩
  · exact ⟨_, hS2.to_le (relative_weak_closure_le _ _ _),
      subgroup_le_relative_weak_closure _ _ _ hTSb, (relative_weak_closure_le _ _ _).trans hSn,
      le_sup_left.trans hN5⟩

theorem exists_nonabelian_le_centralizer {Q T : Subgroup G} (hK : twoPrimeLayerIn Q ≠ oddCoreIn Q)
    (h4 : ¬ HasFourGroup (twoPrimeLayerIn Q)) (hT2 : IsPGroup 2 T)
    (hTH : T ≤ normalizer (Q : Set G))
    (hc : ∀ t ∈ T, ∀ k ∈ twoPrimeLayerIn Q, t * k * t⁻¹ * k⁻¹ ∈ oddCoreIn Q) :
    ∃ Z : Subgroup G, Z ≤ twoPrimeLayerIn Q ⊓ centralizer (T : Set G) ∧ IsPGroup 2 Z ∧
      ∃ a ∈ Z, ∃ b ∈ Z, a * b ≠ b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcov : twoPrimeLayerIn Q ≤
      (twoPrimeLayerIn Q ⊓ centralizer (T : Set G)) ⊔ oddCoreIn Q :=
    coversLayer_of_commutator hT2 hTH hc
  have hns : ¬ Group.IsSolvable (twoPrimeLayerIn Q ⊓ centralizer (T : Set G) : Subgroup G) := by
    intro hs
    have hOs : Group.IsSolvable (oddCoreIn Q) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (odd_card_oddCoreIn Q)
    have hle : twoPrimeLayerIn Q ⊓ centralizer (T : Set G) ≤ normalizer (oddCoreIn Q : Set G) :=
      inf_le_left.trans ((twoPrimeLayerIn_le Q).trans
        (normalIn_le_normalizer (oddCoreIn_normalIn Q)))
    have := isSolvable_sup_of_le_normalizer hle hs hOs
    exact not_isSolvable_twoPrimeLayerIn hK
      (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hcov))
  obtain ⟨Z, hZ⟩ := exists_isSylowOf 2 (twoPrimeLayerIn Q ⊓ centralizer (T : Set G))
  have hZc : ¬ IsCyclic Z := fun hz => hns (isSolvable_of_isSylowOf_isCyclic hZ hz)
  have hZ4 : ¬ HasFourGroup Z := fun h => h4 (h.mono (hZ.le.trans inf_le_left))
  refine ⟨Z, hZ.le, hZ.isPGroup, ?_⟩
  by_contra hab
  push Not at hab
  exact hZc (AschbacherTheorem3.isCyclic_of_pRank_le_one hZ.isPGroup
    ⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩ fun hlt => hZ4 (hasFourGroup_of_one_lt_pRank hlt))

theorem exists_isSylowOf_le_normalizer_of_nonabelian (h3 : AschbacherTheorem3.Theorem3Statement)
    {Q : Subgroup G} (htight : TightlyEmbedded Q) (hno3 : ¬ Thm4Case3 Q) {g : G}
    (hg : g ∉ normalizer (Q : Set G)) {U : Subgroup G}
    (hU : IsSylowOf 2 U (Q ⊓ normalizer (rightConjugate Q g : Set G)))
    (hab : ∃ a ∈ U, ∃ b ∈ U, a * b ≠ b * a) :
    ∃ S : Subgroup G, IsSylowOf 2 S (rightConjugate Q g) ∧ S ≤ normalizer (Q : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q' := rightConjugate Q g with hQ'
  have htight' : TightlyEmbedded Q' := rightConjugate_tightlyEmbedded Q htight g
  have hno3' : ¬ Thm4Case3 Q' := not_thm4Case3_rightConjugate hno3 g
  have hQQ : rightConjugate Q' g⁻¹ = Q := by
    rw [hQ', rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
  have hg' : g⁻¹ ∉ normalizer (Q' : Set G) := by
    intro h
    apply hg
    rw [← rightConjugate_eq_self_iff] at h ⊢
    rw [hQQ] at h
    exact h.symm
  have hU' : IsSylowOf 2 U (rightConjugate Q' g⁻¹ ⊓ normalizer (Q' : Set G)) := by
    rw [hQQ]
    exact hU
  have hUN : U ≤ normalizer (Q' : Set G) := hU.le.trans inf_le_right
  have hUQ : U ≤ Q := hU.le.trans inf_le_left
  have hU2 : IsPGroup 2 U := hU.isPGroup
  obtain ⟨a, ha, b, hb, hab'⟩ := hab
  have hU1 : U ≠ ⊥ := by
    intro h
    rw [h, mem_bot] at ha
    exact hab' (by rw [ha, one_mul, mul_one])
  have hnc : ¬ ∀ x ∈ bar Q' U, ∀ y ∈ bar Q' U, x * y = y * x := fun h =>
    hab' (mul_comm_of_bar hU2 hUN h ha hb)
  obtain ⟨S, hS, hUS, hUQ', hconc⟩ := exists_thm3Conclusion h3 htight' hg' hU' hU1
  rcases hconc with ⟨hcyc, -, -⟩ | h2 | h3' | ⟨-, -, -, -, -, -, -, habel, -⟩ |
      ⟨-, -, -, -, ⟨e⟩, -, -⟩
  · exfalso
    exact hnc fun x hx y hy => congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : bar Q' U) ⟨y, hy⟩)
  ·
    have hQn : bar Q' Q' ≤ normalizer (bar Q' U : Set (Bar Q')) := le_sup_left.trans h2
    have hUn : bar Q' U ≤ normalizer (bar Q' Q' : Set (Bar Q')) :=
      bar_le_normalizer hUN le_normalizer
    have hinf : bar Q' Q' ⊓ bar Q' U = ⊥ := by
      rw [inf_comm, ← bar_inf_of_core_le (AschbacherTheorem5.core_le Q'), hUQ']
      ext x
      simp only [mem_bar_iff, mem_bot]
      constructor
      · rintro ⟨h, hh, rfl⟩
        have : h = 1 := Subtype.ext hh
        rw [this, map_one]
      · rintro rfl
        exact ⟨1, rfl, map_one _⟩
    have hR : IsSylowOf 2 (S ⊓ Q') Q' :=
      hS.inf_of_le_normalizer le_sup_left (sup_le le_normalizer hUN)
    refine ⟨S ⊓ Q', hR, ?_⟩
    obtain ⟨⟨u, huU⟩, hu⟩ := exists_prime_orderOf_dvd_card' (G := U) 2
      (two_dvd_card_of_ne_bot hU2 hU1)
    rw [Subgroup.orderOf_mk] at hu
    have hCu := centralizer_le_of_involution htight (hUQ huU) hu
    intro r hr
    apply hCu
    rw [mem_centralizer_singleton_iff]
    have hrQ' : r ∈ Q' := (mem_inf.mp hr).2
    have hrS : r ∈ S := (mem_inf.mp hr).1
    let r' : normalizer (Q' : Set G) := ⟨r, le_normalizer hrQ'⟩
    let u' : normalizer (Q' : Set G) := ⟨u, hUN huU⟩
    have h1 : toBar Q' r' * toBar Q' u' = toBar Q' u' * toBar Q' r' :=
      commute_of_inf_eq_bot hQn hUn hinf (toBar_mem_bar Q' (h := r') hrQ')
        (toBar_mem_bar Q' (h := u') huU)
    have hcore : r⁻¹ * u⁻¹ * r * u ∈ aschbacherThm5Core Q' :=
      (commutator_mem_core_iff Q' r' u').mpr h1
    have hmem : r⁻¹ * u⁻¹ * r * u ∈ S ⊓ Q' := by
      refine mem_inf.mpr ⟨mul_mem (mul_mem (mul_mem (inv_mem hrS) (inv_mem (hUS huU))) hrS)
        (hUS huU), ?_⟩
      have hur : u⁻¹ * r * u ∈ Q' := by
        have := (mem_normalizer_iff.mp (inv_mem (hUN huU)) r).mp hrQ'
        simpa using this
      have heq : r⁻¹ * u⁻¹ * r * u = r⁻¹ * (u⁻¹ * r * u) := by group
      rw [heq]
      exact mul_mem (inv_mem hrQ') hur
    have h1' : r⁻¹ * u⁻¹ * r * u = 1 := eq_one_of_mem_of_mem hR.isPGroup
      (AschbacherTheorem5.core_odd Q') hmem hcore
    calc r * u = u * r * (r⁻¹ * u⁻¹ * r * u) := by group
      _ = u * r := by rw [h1', mul_one]
  · exact (noThm3Alt3_of_not_thm4Case3 htight' hno3' g⁻¹ hg' U hU' h3').elim
  · exfalso
    exact hnc fun x hx y hy => congrArg Subtype.val (habel.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  · exfalso
    refine hnc fun x hx y hy => ?_
    set x' := e.symm ⟨x, hx⟩
    set y' := e.symm ⟨y, hy⟩
    have hxy : x' * y' = y' * x' := by
      apply Subtype.ext
      have hy'W := (mem_inf.mp y'.2).1
      have hx'C := (mem_inf.mp x'.2).2
      exact (mem_centralizer_iff.mp hx'C _ hy'W).symm
    have h := congrArg e hxy
    rw [map_mul, map_mul] at h
    simp only [x', y', MulEquiv.apply_symm_apply] at h
    exact congrArg Subtype.val h

end RankOne

theorem stepRankOne (h3 : AschbacherTheorem3.Theorem3Statement) : StepRankOne := by
  intro G _ _ Q _ htight hK h4 _ hno3 _ hm g hg heven
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 (rightConjugate Q g ⊓ normalizer (Q : Set G))
  have hT1 : T ≠ ⊥ := isSylowOf_ne_bot_of_even hT heven
  have hTH : T ≤ normalizer (Q : Set G) := hT.le.trans inf_le_right
  have hTQg : T ≤ rightConjugate Q g := hT.le.trans inf_le_left
  have hc := RankOne.commutator_mem_oddCoreIn h3 htight hK h4 hno3 hm hg hT hT1
  obtain ⟨Z, hZle, hZ2, a, ha, b, hb, hab⟩ :=
    RankOne.exists_nonabelian_le_centralizer hK h4 hT.isPGroup hTH hc
  obtain ⟨⟨t, htT⟩, ht⟩ := exists_prime_orderOf_dvd_card' (G := T) 2
    (RankOne.two_dvd_card_of_ne_bot hT.isPGroup hT1)
  rw [Subgroup.orderOf_mk] at ht
  have hZN : Z ≤ normalizer (rightConjugate Q g : Set G) := by
    intro z hz
    refine centralizer_le_of_involution (rightConjugate_tightlyEmbedded Q htight g) (hTQg htT) ht ?_
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.mp (mem_inf.mp (hZle hz)).2 t htT).symm
  have hZQ : Z ≤ Q := hZle.trans (inf_le_left.trans (twoPrimeLayerIn_le Q))
  obtain ⟨U, hU, hZU⟩ := AschbacherTheorem3.exists_isSylowOf_le hZ2 (le_inf hZQ hZN)
  exact RankOne.exists_isSylowOf_le_normalizer_of_nonabelian h3 htight hno3 hg hU
    ⟨a, hZU ha, b, hZU hb, hab⟩

end CFSG.ComponentClassification.Asc75T4
