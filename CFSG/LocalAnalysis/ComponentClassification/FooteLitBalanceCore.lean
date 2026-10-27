module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm32Tools
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitRankOneBranch
public import CFSG.Adapters.GeneralizedFitting
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitOddCoreReduction

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem eq_one_of_mem_isPGroup_of_mem_odd {P Y : Subgroup H} (hP : IsPGroup 2 P)
    (hY : Odd (Nat.card Y)) {x : H} (hxP : x ∈ P) (hxY : x ∈ Y) : x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
  have hk' : x ^ 2 ^ k = 1 := by
    have h := congrArg Subtype.val hk
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h
  have hodd := odd_orderOf_of_mem_of_odd hY hxY
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk')
  rcases j with _ | j
  · rw [pow_zero] at hj
    exact orderOf_eq_one_iff.mp hj
  · rw [hj] at hodd
    exact absurd hodd (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero j⟩))

theorem commute_of_commute_centralizer {Q : Subgroup H} [Q.Normal] (hQ : IsPGroup 2 Q) {a y : H}
    (ha : orderOf a = 2) (hay : a * y = y * a) (hy : Odd (orderOf y))
    (hfix : ∀ q ∈ Q, q * a = a * q → y * q = q * y) : ∀ q ∈ Q, y * q = q * y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB : IsPGroup 2 (zpowers a) := isPGroup_zpowers_of_orderOf ha
  have hya : Commute y a := (Commute.eq (Commute.symm (show Commute a y from hay)))
  have h := ThompsonAB.coprime_eq_one 2 hQ hB
    ((MulAut.conjNormal (H := Q)).comp (zpowers a).subtype) (MulAut.conjNormal y)
    (fun e => by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp e.2
      have hcomm : y * (e : H) = (e : H) * y := by rw [← hk]; exact (hya.zpow_right k).eq
      show MulAut.conjNormal y * MulAut.conjNormal (e : H) =
        MulAut.conjNormal (e : H) * MulAut.conjNormal y
      rw [← map_mul, ← map_mul, hcomm])
    (fun m hm => by
      have h1 := congrArg Subtype.val (hm ⟨a, mem_zpowers a⟩)
      change ((MulAut.conjNormal a m : Q) : H) = m at h1
      rw [MulAut.conjNormal_apply] at h1
      have h2 : (m : H) * a = a * m := by
        calc (m : H) * a = a * (m : H) * a⁻¹ * a := by rw [h1]
          _ = a * m := by group
      apply Subtype.ext
      rw [MulAut.conjNormal_apply, hfix m m.2 h2]
      group)
    (orderOf y) (by rw [← map_pow, pow_orderOf_eq_one, map_one]) (Nat.coprime_two_right.mpr hy)
  intro q hq
  have h1 := congrArg (fun φ : MulAut Q => ((φ ⟨q, hq⟩ : Q) : H)) h
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
  calc y * q = y * q * y⁻¹ * y := by group
    _ = q * y := by rw [h1]

theorem le_pPrimeCore_of_commutator_le {a : H} (ha : orderOf a = 2) {X : Subgroup H}
    (hX : X ≤ oddCoreOfCentralizer a)
    (hcomp : ∀ L : Subgroup H, IsPComponent 2 L → ⁅X, L⁆ ≤ oddCoreIn L) :
    X ≤ pPrimeCore 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := pPrimeCore 2 H with hN
  set π := QuotientGroup.mk' N with hπ
  have hNq : pPrimeCore 2 (H ⧸ N) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  set Xq := X.map π with hXq
  have hXodd : Odd (Nat.card X) :=
    Odd.of_dvd_nat (odd_card_oddCoreOfCentralizer a) (card_dvd_of_le hX)
  have hXqodd : Odd (Nat.card Xq) := Odd.of_dvd_nat hXodd (Subgroup.card_map_dvd (H := X) π)
  have hE : ∀ K : Subgroup (H ⧸ N), CFSG.Open.IsComponentOf K ⊤ →
      K ≤ centralizer (Xq : Set (H ⧸ N)) := by
    intro K hK
    have hKc : CFSG.IsComponent K := ⟨CatalogueBAlternating.quasisimple_iff_native.mpr hK.2.2,
      (Adapters.isSubnormal_top_iff K).mp hK.2.1⟩
    obtain ⟨L, hL, rfl⟩ := LocalAnalysis.ComponentInitial.exists_isPComponent_of_isComponent 2 hKc
    have hLsub : L.IsSubnormal := by
      obtain ⟨-, -, h, -, -⟩ := id hL
      exact h
    have hLO : oddCoreIn L ≤ N := Walter.map_pPrimeCore_le_of_isSubnormal hLsub
    rintro _ ⟨l, hl, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    have h1 : ⁅x, l⁆ ∈ N := hLO (hcomp L hL (commutator_mem_commutator hx hl))
    have h2 : π ⁅x, l⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr h1
    rwa [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
  have hF : ∀ M : Subgroup (H ⧸ N), M.Normal ∧ Group.IsNilpotent M →
      M ≤ centralizer (Xq : Set (H ⧸ N)) := by
    rintro M ⟨hMn, hMnil⟩
    have hMp : IsPGroup 2 M := isPGroup_of_nilpotent_normal M hMn hMnil hNq
    intro m hm
    rw [mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    have hxO := hX hx
    have hxa : x * a = a * x :=
      mem_centralizer_singleton_iff.mp (oddCoreOfCentralizer_le_centralizer a hxO)
    have hay : π a * π x = π x * π a := by rw [← map_mul, ← map_mul, hxa]
    have hyodd : Odd (orderOf (π x)) := odd_orderOf_of_mem_of_odd hXqodd (mem_map_of_mem π hx)
    have hOodd : Odd (Nat.card ((oddCoreOfCentralizer a).map π)) :=
      Odd.of_dvd_nat (odd_card_oddCoreOfCentralizer a)
        (Subgroup.card_map_dvd (H := oddCoreOfCentralizer a) π)
    refine commute_of_commute_centralizer hMp (orderOf_mk_eq_two ha) hay hyodd
      (fun q hq hqa => ?_) m hm
    have hqC : q ∈ (centralizer ({a} : Set H)).map π := by
      rw [map_centralizer_mk ha, mem_centralizer_singleton_iff]
      exact hqa
    obtain ⟨c, hc, rfl⟩ := mem_map.mp hqC
    have h1 : ⁅x, c⁆ ∈ oddCoreOfCentralizer a := by
      rw [show ⁅x, c⁆ = x * (c * x⁻¹ * c⁻¹) by rw [commutatorElement_def]; group]
      exact mul_mem hxO ((mem_normalizer_iff.mp (mem_normalizer_oddCoreOfCentralizer hc) _).mp
        (inv_mem hxO))
    have h2 : ⁅π x, π c⁆ ∈ M := by
      rw [commutatorElement_def]
      exact mul_mem (hMn.conj_mem _ hq (π x)) (inv_mem hq)
    have h3 : ⁅π x, π c⁆ ∈ (oddCoreOfCentralizer a).map π := by
      rw [← map_commutatorElement]
      exact mem_map_of_mem π h1
    have h4 := eq_one_of_mem_isPGroup_of_mem_odd hMp hOodd h2 h3
    rwa [commutatorElement_eq_one_iff_mul_comm] at h4
  have hFstar : Xq ≤ centralizer (CFSG.Open.genFittingFStar (H ⧸ N) : Set (H ⧸ N)) := by
    rw [le_centralizer_iff]
    exact sup_le (sSup_le fun M hM => hF M hM) (sSup_le fun K hK => hE K hK)
  have hXF : Xq ≤ CFSG.Open.genFittingFStar (H ⧸ N) :=
    hFstar.trans (Adapters.generalized_fitting_self_centralizing _)
  have hFn : (CFSG.Open.genFittingFStar (H ⧸ N)).Normal := by
    have h := GorensteinWalter.generalizedFittingSubgroupOf_isNormalIn (⊤ : Subgroup (H ⧸ N))
    rw [← Adapters.genFittingFStar_eq] at h
    exact ⟨fun k hk g => h.2 g (mem_top g) k hk⟩
  set Z := centralizer (CFSG.Open.genFittingFStar (H ⧸ N) : Set (H ⧸ N)) ⊓
    CFSG.Open.genFittingFStar (H ⧸ N) with hZ
  have hZn : Z.Normal := inferInstance
  have hZnil : Group.IsNilpotent Z := by
    refine Group.IsNilpotent.mk ⟨1, ?_⟩
    rw [Subgroup.upperCentralSeries_one, eq_top_iff]
    intro z _
    rw [mem_center_iff]
    intro w
    exact Subtype.ext (mem_centralizer_iff.mp (mem_inf.mp z.2).1 w (mem_inf.mp w.2).2)
  have hZp : IsPGroup 2 Z := isPGroup_of_nilpotent_normal Z hZn hZnil hNq
  have hXZ : Xq ≤ Z := le_inf hFstar hXF
  intro x hx
  have h1 : π x = 1 :=
    eq_one_of_mem_isPGroup_of_mem_odd hZp hXqodd (hXZ (mem_map_of_mem π hx)) (mem_map_of_mem π hx)
  exact (QuotientGroup.eq_one_iff x).mp h1

end CFSG.ComponentClassification.FooteLit
