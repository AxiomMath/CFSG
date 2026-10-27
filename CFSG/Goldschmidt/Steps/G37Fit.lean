module

public import CFSG.Walter.W67.Section6.Core61
import CFSG.Goldschmidt.Steps.Completion
import CFSG.Goldschmidt.Steps.G36Setup
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Goldschmidt.Steps.G37Quot

public section

namespace CFSG.Goldschmidt.G37

open CFSG.GorensteinWalter
open CFSG.Open (goldschmidtOddCore goldschmidtLayer)
open scoped commutatorElement

section Join

variable {G : Type} [Group G]

theorem commutator_sup_le_of_comm {N E : Subgroup G}
    (hE : E ≤ Subgroup.normalizer (N : Set G)) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) :
    ⁅N ⊔ E, N ⊔ E⁆ ≤ N := by
  have hR : N ⊔ E ≤ Subgroup.normalizer (N : Set G) := sup_le Subgroup.le_normalizer hE
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hconj : ∀ g ∈ Subgroup.normalizer (N : Set G), ∀ z ∈ N, g * z * g⁻¹ ∈ N :=
    fun g hg z hz => (Subgroup.mem_normalizer_iff.mp hg z).mp hz
  have hcomm : ∀ z ∈ N, ∀ g ∈ Subgroup.normalizer (N : Set G), z * g * z⁻¹ * g⁻¹ ∈ N := by
    intro z hz g hg
    rw [show z * g * z⁻¹ * g⁻¹ = z * (g * z⁻¹ * g⁻¹) by group]
    exact N.mul_mem hz (hconj g hg _ (N.inv_mem hz))
  obtain ⟨w, hw, n, hn, rfl⟩ := mem_sup_of_le_normalizer hE (sup_comm N E ▸ hx)
  obtain ⟨w', hw', n', hn', rfl⟩ := mem_sup_of_le_normalizer hE (sup_comm N E ▸ hy)
  have e : ⁅w * n, w' * n'⁆ = (w * (n * (w' * n') * n⁻¹ * (w' * n')⁻¹) * w⁻¹) *
      (w * w' * n' * w⁻¹ * n'⁻¹ * w'⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e, hEc w hw w' hw',
    show w' * w * n' * w⁻¹ * n'⁻¹ * w'⁻¹ = w' * (w * n' * w⁻¹ * n'⁻¹) * w'⁻¹ by group]
  refine N.mul_mem (hconj w (hE hw) _ (hcomm n hn _ (hR hy))) (hconj w' (hE hw') _ ?_)
  exact N.mul_mem (hconj w (hE hw) _ hn') (N.inv_mem hn')

theorem isMulCommutative_sylow_of_commutator_le [Finite G] {R V : Subgroup G}
    (hRR : ⁅R, R⁆ ≤ V) (hV : Odd (Nat.card V)) (S : Sylow 2 R) :
    IsMulCommutative (S : Subgroup R) := by
  have hS2 : IsPGroup 2 ((S : Subgroup R).map R.subtype) := S.isPGroup'.map _
  have hSV : V ⊓ (S : Subgroup R).map R.subtype = ⊥ := inf_eq_bot_of_odd_of_isPGroup hV hS2
  refine ⟨⟨fun x y => ?_⟩⟩
  have hc : ⁅(((x : R) : G)), (((y : R) : G))⁆ ∈ V ⊓ (S : Subgroup R).map R.subtype := by
    refine Subgroup.mem_inf.mpr ⟨hRR (Subgroup.commutator_mem_commutator (x : R).2 (y : R).2),
      ⟨⁅(x : R), (y : R)⁆, ?_, rfl⟩⟩
    rw [commutatorElement_def]
    exact (S : Subgroup R).mul_mem ((S : Subgroup R).mul_mem ((S : Subgroup R).mul_mem x.2 y.2)
      ((S : Subgroup R).inv_mem x.2)) ((S : Subgroup R).inv_mem y.2)
  rw [hSV, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  exact Subtype.ext (Subtype.ext hc)

end Join

variable {G : Type} [Group G] [Finite G]

theorem fittingSubgroupOf_le_of_le_normalizer {H V : Subgroup G} (hVH : V ≤ H)
    (hHV : H ≤ Subgroup.normalizer (V : Set G)) :
    CFSG.fittingSubgroupOf V ≤ CFSG.fittingSubgroupOf H :=
  le_fittingSubgroupOf_of_isNormalIn_nilpotent ((CFSG.fittingSubgroupOf_le V).trans hVH)
    ⟨(CFSG.fittingSubgroupOf_le V).trans hVH, fun _ hh k hk =>
      (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_fitting V (hHV hh)) k).mp hk⟩
    (CFSG.fittingSubgroupOf_isNilpotent V)

theorem commutator_oddFit_le_fitting {H X : Subgroup G} {a : G} (haH : a ∈ H) (ha2 : a ^ 2 = 1)
    (ha1 : a ≠ 1) (hXH : X ≤ H)
    (hXa : H ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G))
    (hYa : ⁅oddCoreOf (CFSG.fittingSubgroupOf X), Subgroup.zpowers a⁆ ≤ oddCoreOf H) :
    ⁅oddCoreOf (CFSG.fittingSubgroupOf X), Subgroup.zpowers a⁆ ≤ CFSG.fittingSubgroupOf H := by
  set Y := oddCoreOf (CFSG.fittingSubgroupOf X) with hY
  set V := oddCoreOf H with hV
  have hVH : V ≤ H := Subgroup.map_subtype_le _
  have hHV : H ≤ Subgroup.normalizer (V : Set G) := Completion.le_normalizer_oddCoreOf H
  have hVodd : Odd (Nat.card V) := Completion.odd_card_oddCoreOf H
  have hYX : Y ≤ X := oddFit_le X
  have hYH : Y ≤ H := hYX.trans hXH
  have haC : a ∈ H ⊓ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_inf.mpr ⟨haH, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have haY : a ∈ Subgroup.normalizer (Y : Set G) :=
    (hXa.trans (normalizer_le_normalizer_oddFit X)) haC
  have hHF : H ≤ Subgroup.normalizer (CFSG.fittingSubgroupOf H : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_fitting H)
  set Z := Subgroup.zpowers a with hZ
  set R := V ⊔ Z with hR
  have hZV : Z ≤ Subgroup.normalizer (V : Set G) := Subgroup.zpowers_le.mpr (hHV haH)
  have hZc : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow_self a i j).eq
  have hRH : R ≤ H := sup_le hVH (Subgroup.zpowers_le.mpr haH)
  have hRs : Group.IsSolvable R :=
    CFSG.Walter.W67.Sec6.isSolvable_sup_of_comm hZV hZc (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hVodd)
  have hSyl : ∀ S : Sylow 2 R, IsMulCommutative (S : Subgroup R) :=
    isMulCommutative_sylow_of_commutator_le (commutator_sup_le_of_comm hZV hZc) hVodd
  have haR : a ∈ R := Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  have hZR : Z ≤ R := le_sup_right
  set t : R := ⟨a, haR⟩ with ht
  have htinv : BenderSuzuki.PFAppendixIII.IsInvolution t :=
    ⟨fun h => ha1 (congrArg Subtype.val h), Subtype.ext (by rw [Subgroup.coe_pow]; exact ha2)⟩
  have hzt : Subgroup.zpowers t = Z.subgroupOf R := by
    apply Subgroup.map_injective R.subtype_injective
    rw [MonoidHom.map_zpowers, Subgroup.map_subgroupOf_eq_of_le hZR]
    rfl
  have hFY : CFSG.fittingSubgroupOf Y = Y := by
    have : Group.IsNilpotent Y := isNilpotent_oddFit X
    have htop : CFSG.fittingSubgroup Y = ⊤ := le_antisymm le_top
      (le_sSup ⟨Subgroup.normal_top, (Group.nilpotent_of_mulEquiv Subgroup.topEquiv.symm)⟩)
    rw [CFSG.fittingSubgroupOf, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← hFY, (show CFSG.fittingSubgroupOf Y = _ from
    CFSG.GorensteinWalter.fittingSubgroupOf_eq_iSup_qCoreOf Y), ← sSup_range]
  refine CFSG.Walter.commutator_sSup_le _ _ _ (fun P hP => ?_) (fun P hP => ?_)
  swap
  · obtain ⟨q, rfl⟩ := hP
    exact (qCoreOf_le Y _).trans (hYH.trans hHF)
  obtain ⟨q, rfl⟩ := hP
  have hp : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
  have : Fact q.1.1.Prime := ⟨hp⟩
  set p := q.1.1 with hpdef
  have hPY : qCoreOf Y p ≤ Y := qCoreOf_le Y p
  have hPp : IsPGroup p (qCoreOf Y p) := qCoreOf_isPGroup Y p
  have hPodd : Odd (Nat.card (qCoreOf Y p)) :=
    (odd_card_oddFit X).of_dvd_nat (Subgroup.card_dvd_of_le hPY)
  have hp2 : p ≠ 2 := by
    intro h
    have h3 : p ∣ Nat.card Y := Nat.dvd_of_mem_primeFactors q.1.2
    rw [h] at h3
    exact (Nat.not_even_iff_odd.mpr (odd_card_oddFit X)) (even_iff_two_dvd.mpr h3)
  have haP : a ∈ Subgroup.normalizer (qCoreOf Y p : Set G) :=
    CFSG.Walter.normalizer_le_normalizer_map_of_characteristic _ haY
  set U := ⁅qCoreOf Y p, Z⁆ with hU
  have hUP : U ≤ qCoreOf Y p := CFSG.Walter.commutator_zpowers_le_of_mem_normalizer haP
  have hUV : U ≤ V := (Subgroup.commutator_mono hPY le_rfl).trans hYa
  have hUR : U ≤ R := hUV.trans le_sup_left
  have hUp : IsPGroup p U := hPp.to_le hUP
  have hcop : Nat.Coprime (Nat.card Z) (Nat.card (qCoreOf Y p)) := by
    have h1 : Nat.card Z ∣ 2 := by
      rw [hZ, Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one ha2
    exact Nat.Coprime.coprime_dvd_left h1 (Nat.coprime_two_left.mpr hPodd)
  have hUcomm : ⁅U, Z⁆ = U := le_antisymm
    (CFSG.Walter.commutator_zpowers_le_of_mem_normalizer
      (CFSG.Walter.mem_normalizer_commutator haP (Subgroup.le_normalizer (Subgroup.mem_zpowers a))))
    (CFSG.Walter.commutator_le_commutator_commutator _ _ (Subgroup.zpowers_le.mpr haP) hcop)
  have hUinv : Subgroup.centralizer ({t} : Set R) ≤
      Subgroup.normalizer ((U.subgroupOf R : Subgroup R) : Set R) := by
    intro x hx
    rw [← Subgroup.subgroupOf_normalizer_eq hUR]
    have hxa : (x : G) ∈ H ⊓ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hRH x.2, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hx))⟩
    have hxP : (x : G) ∈ Subgroup.normalizer (qCoreOf Y p : Set G) :=
      CFSG.Walter.normalizer_le_normalizer_map_of_characteristic _
        ((hXa.trans (normalizer_le_normalizer_oddFit X)) hxa)
    have hxZ : (x : G) ∈ Subgroup.normalizer (Z : Set G) := by
      apply Subgroup.centralizer_le_normalizer
      rw [hZ, CFSG.Walter.centralizer_zpowers_eq']
      exact (Subgroup.mem_inf.mp hxa).2
    exact CFSG.Walter.mem_normalizer_commutator hxP hxZ
  have hUcomm' : ⁅U.subgroupOf R, Subgroup.zpowers t⁆ = U.subgroupOf R := by
    rw [hzt, ← subgroupOf_commutator hUR hZR, hUcomm]
  have hUp' : IsPGroup p (U.subgroupOf R) := hUp.of_equiv (Subgroup.subgroupOfEquivOfLe hUR).symm
  have h := bender1970_2_4_solvable_oddP_selfCommutator_le_pCore (U.subgroupOf R) p hRs hp
    (hp.odd_of_ne_two hp2) hSyl htinv hUp' hUinv hUcomm'
  set Q := (CFSG.pCore p R).map R.subtype with hQ
  have hUQ : U ≤ Q := by
    have := Subgroup.map_mono (f := R.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hUR] at this
  have hRQ : R ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_map_subtype (CFSG.pCore p R)
  have hQV : Q ⊓ V ≤ qCoreOf V p := by
    have hn : ((Q ⊓ V).subgroupOf V).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr fun v hv =>
        Subgroup.inf_normalizer_le_normalizer_inf
          ⟨hRQ (Subgroup.mem_sup_left hv), Subgroup.le_normalizer hv⟩
    have hpg : IsPGroup p ((Q ⊓ V).subgroupOf V) :=
      ((CFSG.pCore_isPGroup.map R.subtype).to_le inf_le_left).of_equiv
        (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
    have h1 : (Q ⊓ V).subgroupOf V ≤ CFSG.pCore p V := le_sSup ⟨hn, hpg⟩
    have h2 := Subgroup.map_mono (f := V.subtype) h1
    rwa [Subgroup.map_subgroupOf_eq_of_le inf_le_right] at h2
  exact (le_inf hUQ hUV).trans (hQV.trans ((qCoreOf_le_fittingSubgroupOf V p hp).trans
    (fittingSubgroupOf_le_of_le_normalizer hVH hHV)))

end CFSG.Goldschmidt.G37
