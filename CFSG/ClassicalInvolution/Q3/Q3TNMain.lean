module

public import CFSG.ClassicalInvolution.Q3.Q3TNCore2
public import CFSG.ClassicalInvolution.Q3.Q3B2
public import CFSG.ClassicalInvolution.Q3.Q3TNZ
public import CFSG.ClassicalInvolution.Q3.Q3UMain

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.LocalCores
open CFSG.ComponentClassification
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem mem_centralizer_of_commutator_mem_center {T : Subgroup Y} (hT : IsComponentOf T ⊤)
    {g : Y} (h : ∀ t ∈ T, ⁅t, g⁆ ∈ Subgroup.center Y) :
    g ∈ Subgroup.centralizer (T : Set Y) := by
  have hle : ⁅T, Subgroup.zpowers g⁆ ≤ Subgroup.center Y := by
    rw [Subgroup.commutator_le]
    intro t ht x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hc := h t ht
    have hcg : Commute ⁅t, g⁆ g := (Subgroup.mem_center_iff.mp hc g).symm
    have h1 : t * g * t⁻¹ = ⁅t, g⁆ * g := by rw [commutatorElement_def]; group
    have h2 : t * g ^ n * t⁻¹ = ⁅t, g⁆ ^ n * g ^ n := by rw [← conj_zpow, h1, hcg.mul_zpow]
    have h3 : ⁅t, g ^ n⁆ = ⁅t, g⁆ ^ n := by
      rw [commutatorElement_def, h2]
      group
    rw [h3]
    exact Subgroup.zpow_mem _ hc n
  have hdouble : ⁅⁅T, Subgroup.zpowers g⁆, T⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b _
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hle ha) b).symm
  have hperf : Group.IsPerfect T := ⟨hT.2.2.1⟩
  have hTg := perfect_double_commutator hperf hdouble
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have hmem := Subgroup.commutator_mem_commutator ht (Subgroup.mem_zpowers g)
  rw [hTg, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact hmem

omit [Finite Y] in
theorem mem_normalizer_of_conjSub_eq {T : Subgroup Y} {g : Y} (h : conjSub g T = T) :
    g ∈ Subgroup.normalizer (T : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have := conj_mem_conjSub (n := g) hy
    rwa [h] at this
  · intro hy
    rw [← h, mem_conjSub_iff] at hy
    simpa [mul_assoc] using hy

theorem le_normalizer_of_tight (hO : classicalInvolutionOddCore Y = ⊥) {z : Y} {L : Subgroup Y}
    (hz : IsClassicalMember3 L z) {T : Subgroup Y} (hT : IsComponentOf T ⊤) (hTL : T ⊔ L = ⊤)
    (hTz : ¬ T ≤ Subgroup.centralizer ({z} : Set Y)) : L ≤ Subgroup.normalizer (T : Set Y) := by
  set π := QuotientGroup.mk' (Subgroup.center Y) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : ∀ y : Y, π y = 1 ↔ y ∈ Subgroup.center Y := fun y => QuotientGroup.eq_one_iff y
  have hzc : z ∉ Subgroup.center Y := fun h => hTz fun t _ =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp h t)
  have hL := hz.map_centerQuotient hO hzc
  have hTnk : ¬ T ≤ π.ker := by
    intro hle
    exact not_forall_commute_of_isComponent hT fun x hx a _ =>
      Subgroup.mem_center_iff.mp ((hker x).mp (hle hx)) a
  have hT' : IsComponentOf (T.map π) ⊤ := LocalComponents.image hT π hπs hTnk
  have hTc' : IsComponent (T.map π) := (isComponent_iff_open _).mpr hT'
  have hTz' : ¬ T.map π ≤ Subgroup.centralizer ({π z} : Set _) := by
    intro hle
    have hcz := mem_centralizer_of_commutator_mem_center hT (g := z) fun t ht => by
      refine (hker _).mp ?_
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle ⟨t, ht, rfl⟩)
    exact hTz fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hcz t ht)
  have hzN := hL.mem_normalizer_of_isComponent hT'
  have hev : Even (Nat.card (T.map π)) := by
    by_contra hodd
    exact Q3B.not_isSolvable_of_isComponentOf hT'
      (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.not_even_iff_odd.mp hodd))
  have hzz : π z * π z = 1 := by rw [← pow_two]; exact hL.sq_eq_one
  have hev' := Balance.LocalBalance.even_card_inf_centralizer_of_even hzz
    (fun x hx => (Subgroup.mem_normalizer_iff.mp hzN x).mp hx) hev
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev')
  have hxo : orderOf (x : Y ⧸ Subgroup.center Y) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  have hx2 : (x : Y ⧸ Subgroup.center Y) * x = 1 := by
    rw [← pow_two, ← hxo]
    exact pow_orderOf_eq_one _
  have hxc : (x : Y ⧸ Subgroup.center Y) ∉ Subgroup.centralizer (T.map π : Set _) := by
    intro hxc
    obtain ⟨y, hyT, hyx⟩ := x.2.1
    have hyc := mem_centralizer_of_commutator_mem_center hT (g := y) fun t ht => by
      refine (hker _).mp ?_
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, hyx]
      exact Subgroup.mem_centralizer_iff.mp hxc _ ⟨t, ht, rfl⟩
    have hy1 : π y = 1 := (hker y).mpr (inf_centralizer_le_center hO hz hT hTL hTz ⟨hyT, hyc⟩)
    rw [hyx] at hy1
    rw [hy1, orderOf_one] at hxo
    omega
  refine le_of_forall_oddPrimePow_mem hz fun g hgL p k hp hp2 hg => ?_
  by_contra hgN
  have hgT : conjSub g T ≠ T := fun h => hgN (mem_normalizer_of_conjSub_eq h)
  have hgodd : Odd (orderOf (π g)) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp
      ((orderOf_map_dvd π g).trans (orderOf_dvd_of_pow_eq_one hg))
    rw [hj]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hgT' : conjSub (π g) (T.map π) ≠ T.map π := by
    intro h
    have hmap : conjSub (π g) (T.map π) = (conjSub g T).map π := by
      ext w
      simp only [conjSub, Subgroup.mem_map]
      constructor
      · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
        exact ⟨g * t * g⁻¹, ⟨t, ht, rfl⟩, by simp [MulAut.conj_apply]⟩
      · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
        exact ⟨π t, ⟨t, ht, rfl⟩, by simp [MulAut.conj_apply]⟩
    have hgTc : IsComponent (conjSub g T) :=
      isComponent_map_mulEquiv (MulAut.conj g) ((isComponent_iff_open T).mpr hT)
    have hcomm : ⁅conjSub g T, T⁆ = ⊥ :=
      (distinct_components_commute hgTc ((isComponent_iff_open T).mpr hT)).resolve_left hgT
    have hbot : ⁅T.map π, T.map π⁆ = ⊥ := by
      have h1 : ⁅(conjSub g T).map π, T.map π⁆ = ⊥ := by
        rw [← Subgroup.map_commutator, hcomm, Subgroup.map_bot]
      rwa [← hmap, h] at h1
    have : Group.IsPerfect (T.map π) := ⟨hT'.2.2.1⟩
    have hbot' : T.map π = ⊥ := by rw [← Subgroup.commutator_eq_self (H := T.map π)]; exact hbot
    have : Nontrivial (T.map π) := Quasisimple.nontrivial hT'.2.2
    exact (Subgroup.nontrivial_iff_ne_bot _).mp this hbot'
  exact core_false hL hTc' hTz' x.2.1 (Subgroup.mem_centralizer_singleton_iff.mp x.2.2) hx2 hxc
    (Subgroup.mem_map_of_mem π hgL) hgodd hgT'

theorem tightNormalizesComponentConn_proved : Q3B.TightNormalizesComponentConn :=
  fun _ _ _ _ hO _ _ hz _ hT hTL _ _ hTz => le_normalizer_of_tight hO hz hT hTL hTz

theorem tightNormalizesComponent_proved : TightNormalizesComponent :=
  fun _ _ _ _ hO _ _ hz _ hT hTL hTz => le_normalizer_of_tight hO hz hT hTL hTz

end CFSG.ClassicalInvolution.Q3.Q3T
