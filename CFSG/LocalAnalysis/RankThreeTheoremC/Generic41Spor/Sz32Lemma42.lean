module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32L42Second
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupTits
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupSz32
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Lemma42Generic
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32L42W1
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma44
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3ConjGeneric
import CFSG.LocalAnalysis.RankFourTheoremC.PPointPlane
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Misc
import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers
import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PSU3.Aut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T GenericComponentClass)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem sz32_plane_sup {U : Subgroup G} {x w : G} (hUel : IsElemAbelian 5 U) (hUcard : Nat.card U = 5 ^ 2)
    (hxU : x ∈ U) (hwU : w ∈ U) (hx1 : x ≠ 1) (hwx : w ∉ zpowers x) :
    zpowers x ⊔ zpowers w = U := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hxo : orderOf x = 5 := orderOf_eq_prime (hUel.2 x hxU) hx1
  have hle : zpowers x ⊔ zpowers w ≤ U := sup_le (zpowers_le.2 hxU) (zpowers_le.2 hwU)
  have hdvd : Nat.card (zpowers x ⊔ zpowers w : Subgroup G) ∣ 5 ^ 2 := by
    rw [← hUcard]
    exact Subgroup.card_dvd_of_le hle
  have h5le : 5 ≤ Nat.card (zpowers x ⊔ zpowers w : Subgroup G) := by
    have := Subgroup.card_le_of_le (le_sup_left : zpowers x ≤ zpowers x ⊔ zpowers w)
    rwa [Nat.card_zpowers, hxo] at this
  have hgt : 5 < Nat.card (zpowers x ⊔ zpowers w : Subgroup G) := by
    by_contra hcon
    have h5 : Nat.card (zpowers x ⊔ zpowers w : Subgroup G) = 5 := by omega
    have hEq : zpowers x = zpowers x ⊔ zpowers w :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [Nat.card_zpowers, hxo, h5])
    exact hwx (hEq ▸ (le_sup_right : zpowers w ≤ zpowers x ⊔ zpowers w) (mem_zpowers w))
  obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 hdvd
  have hi2 : i = 2 := by
    interval_cases i <;> simp_all
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hUcard, hi', hi2])


theorem sz32_lemma42 (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hClass : GenericComponentClass G) (hTits : TitsFacts) (hA10 : A10Facts)
    (hMcL : ExtraFacts IsMcLType 5 McLShape) (hJ4 : ExtraFacts IsJ4Type 11 J4Shape)
    (hSz : Sz32Facts) (hc : PointConfig IsSz32Type G 5 P M x J) {a c y : G}
    (hP : Sz32Struct P x J a c y) (hL : Sz32Lines P x (a ^ 5)) (hZ : Sz32ZFacts P M x (a ^ 5))
    {U : Subgroup G} (hU : Sz32Plane P x a c y U) :
    ∀ u ∈ U, u ∉ Subgroup.zpowers x → Subgroup.centralizer ({u} : Set G) ≤ M := by
  intro u hu hux
  by_contra hbad
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hfacts : Sz32QFacts (P : Subgroup G) a c y x := hP.facts
  have hVP : sz32Om a c y ≤ (P : Subgroup G) := hfacts.Om_le
  have hVel : IsElemAbelian 5 (sz32Om a c y) := hfacts.Om_elem
  have hVcard : Nat.card (sz32Om a c y) = 5 ^ 3 := hfacts.Om_card
  have hZV : sz32Z a c ≤ sz32Om a c y := le_sup_left
  have hZcard : Nat.card (sz32Z a c) = 5 ^ 2 := hfacts.Z_card
  have hZeq : zpowers (a ^ 5) ⊔ zpowers x = sz32Z a c := by rw [hfacts.x_eq]; rfl
  have hxZ : x ∈ sz32Z a c := hZeq ▸ (mem_sup_right (mem_zpowers x))
  have heZ : a ^ 5 ∈ sz32Z a c := hZeq ▸ (mem_sup_left (mem_zpowers _))
  have hx1 : x ≠ 1 := hc.generic.2.1.2.1
  have hxp : x ^ 5 = 1 := hc.generic.2.1.2.2.1
  have hxM : x ∈ M := hc.generic.2.1.1
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  have hZwc : ∀ h : G, (sz32Z a c).map (MulAut.conj h).toMonoidHom ≤ (P : Subgroup G) →
      (sz32Z a c).map (MulAut.conj h).toMonoidHom = sz32Z a c := by
    intro h hh
    have := hZ.Z_wc h (by rw [hZeq]; exact hh)
    rwa [hZeq] at this
  have hW1 : ∀ b ∈ sz32Om a c y, b ∉ sz32Z a c → ∀ g : G, g * b * g⁻¹ ∉ sz32Z a c :=
    fun b hb hbZ g => sz32_W1 hVP hVel hVcard hfacts.Om_all hZV hfacts.center hZwc hb hbZ g
  have hUabs := hU.abs
  have hUV : U ≤ sz32Om a c y := hUabs.le_Om
  have hUP : U ≤ (P : Subgroup G) := hU.le_P
  have hUM : U ≤ M := hUP.trans hPM
  have hUel : IsElemAbelian 5 U := hUabs.elem
  have hUcard : Nat.card U = 5 ^ 2 := hUabs.card
  have hxU : x ∈ U := hUabs.mem
  have hUZ : ∀ w ∈ U, w ∉ zpowers x → w ∉ sz32Z a c := by
    intro w hwU hwx hwZ
    have : w ∈ U ⊓ sz32Z a c := ⟨hwU, hwZ⟩
    rw [hUabs.inf_Z] at this
    exact hwx this
  haveI : IsMulCommutative (sz32Om a c y) := hVel.1
  have hVc : ∀ p ∈ sz32Om a c y, ∀ q ∈ sz32Om a c y, p * q = q * p := fun p hp q hq =>
    congrArg Subtype.val (mul_comm' (⟨p, hp⟩ : sz32Om a c y) ⟨q, hq⟩)
  have hxo : orderOf x = 5 := orderOf_eq_prime hxp hx1
  have hCw : ∀ w ∈ U, w ∉ zpowers x → ¬ centralizer ({w} : Set G) ≤ M := by
    intro w hwU hwx hCw
    have hsup := sz32_plane_sup hUel hUcard hxU hwU hx1 hwx
    have huj : u ∈ zpowers x ⊔ zpowers w := hsup ▸ hu
    have hcomm : ∀ s ∈ zpowers x, ∀ t ∈ zpowers w, s * t = t * s := fun s hs t ht =>
      hVc s (hUV (zpowers_le.2 hxU hs)) t (hUV (zpowers_le.2 hwU ht))
    obtain ⟨s, hs, t, ht, hst⟩ := spw_mem_sup_of_commute hcomm huj
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hs
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 ht
    have hw5 : w ^ 5 = 1 := hUel.2 w hwU
    have hwi1 : w ^ i ≠ 1 := by
      intro h1
      apply hux
      rw [hst, h1, mul_one]
      exact mem_zpowers_iff.2 ⟨j, rfl⟩
    have hwiU : w ^ i ∈ U := U.zpow_mem hwU i
    have hwix : w ^ i ∉ zpowers x := by
      intro hmem
      apply hux
      rw [hst]
      exact (zpowers x).mul_mem (mem_zpowers_iff.2 ⟨j, rfl⟩) hmem
    have hwiZ : w ^ i ∉ sz32Z a c := hUZ _ hwiU hwix
    obtain ⟨q, hqP, hq⟩ := hfacts.shear (w ^ i) (hUV hwiU) hwiZ (x ^ j)
      (zpow_mem hxZ j)
    have hwio : orderOf (w ^ i) = 5 := by
      refine orderOf_eq_prime ?_ hwi1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw5, one_zpow]
    have hwo : orderOf w = 5 := orderOf_eq_prime hw5 (fun h1 => hwx (h1 ▸ one_mem _))
    have hwmem : w ∈ zpowers (w ^ i) :=
      spw_mem_zpowers_of_mem_zpowers hwio hwo (mem_zpowers_iff.2 ⟨i, rfl⟩)
    apply hbad
    intro g hg
    have hgu : g * u = u * g := mem_centralizer_singleton_iff.1 hg
    have hst' : u = w ^ i * x ^ j := by
      rw [hst]
      exact hcomm (x ^ j) (mem_zpowers_iff.2 ⟨j, rfl⟩) (w ^ i) (mem_zpowers_iff.2 ⟨i, rfl⟩)
    have hu_eq : u = q * w ^ i * q⁻¹ := by rw [hq, ← hst']
    have hg1 : (q⁻¹ * g * q) * w ^ i = w ^ i * (q⁻¹ * g * q) := by
      have h1 : q * w ^ i * q⁻¹ * g = g * (q * w ^ i * q⁻¹) := by rw [← hu_eq]; exact hgu.symm
      calc (q⁻¹ * g * q) * w ^ i = q⁻¹ * (g * (q * w ^ i * q⁻¹)) * q := by group
        _ = q⁻¹ * (q * w ^ i * q⁻¹ * g) * q := by rw [h1]
        _ = w ^ i * (q⁻¹ * g * q) := by group
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hwmem
    have hg2 : (q⁻¹ * g * q) * w = w * (q⁻¹ * g * q) := by
      rw [← hk]
      exact ((show Commute (q⁻¹ * g * q) (w ^ i) from hg1).zpow_right k).eq
    have hmem2 : q⁻¹ * g * q ∈ centralizer ({w} : Set G) :=
      mem_centralizer_singleton_iff.2 hg2
    have hM3 : q⁻¹ * g * q ∈ M := hCw hmem2
    have hqM : q ∈ M := hPM hqP
    have : g = q * (q⁻¹ * g * q) * q⁻¹ := by group
    rw [this]
    exact M.mul_mem (M.mul_mem hqM hM3) (M.inv_mem hqM)
  have hLO : ∀ w ∈ U, w ∉ zpowers x → IsLargeObstruction 5 M w := by
    intro w hwU hwx
    have hw1 : w ≠ 1 := fun h => hwx (h ▸ one_mem _)
    have hVC : sz32Om a c y ≤ centralizer ({w} : Set G) := by
      intro v hv
      exact mem_centralizer_singleton_iff.2 (hVc v hv w (hUV hwU))
    exact ⟨hUM hwU, hw1, hUel.2 w hwU,
      CFSG.SectionRank.le_pRank (by norm_num) hVC hVel hVcard, hCw w hwU hwx⟩
  have hA10pt : ∀ w ∈ U, w ∉ zpowers x → ∃ m ∈ M, ∃ J' : Subgroup G,
      PointConfig IsA10Type G 5 P M (MulAut.conj m w) J' := by
    intro w hwU hwx
    obtain ⟨m, hmM, hmP, hgen⟩ := exists_conj_isGenericPoint hS hU0 hc.sigma hc.core (hLO w hwU hwx)
    have hw5 : w ^ 5 = 1 := hUel.2 w hwU
    have hu5 : (MulAut.conj m w) ^ 5 = 1 := by rw [← map_pow, hw5, map_one]
    have huV : MulAut.conj m w ∈ sz32Om a c y := hfacts.Om_all _ hmP hu5
    have huZ : MulAut.conj m w ∉ sz32Z a c := by
      rw [MulAut.conj_apply]
      exact hW1 w (hUV hwU) (hUZ w hwU hwx) m
    have hSu : u3S P (MulAut.conj m w) = sz32Om a c y := by
      apply le_antisymm
      · rintro q ⟨hqP, hqC⟩
        exact hfacts.cent_le _ huV huZ q hqP (mem_centralizer_singleton_iff.1 hqC)
      · intro v hv
        exact ⟨hVP hv, mem_centralizer_singleton_iff.2 (hVc v hv _ huV)⟩
    exact ⟨m, hmM, sz32_second_point_A10 hS hClass hTits hA10 hMcL hJ4 hSz hc.sigma hc.core hc.fail
      hc.larger hVP hVel hVcard hZV hZcard hxZ heZ hx1 hL.lines hgen huV huZ hSu⟩
  have hM2loc : IsTwoLocal M := hc.core.1.1
  set T₀ : Subgroup G := pCoreOf 2 M with hT₀
  have hT₀2 : IsPGroup 2 T₀ := CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 M
  have hMT₀ : M ≤ normalizer (T₀ : Set G) :=
    CFSG.PreuniquenessRankFour.Helpers.subgroup_normalizes_pCoreOf 2 M
  have hO2R : T₀ ≤ rankThreePrimeCore 5 M :=
    CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.pCoreOf_two_le_relPPrimeCore (by norm_num) M
  have hcop : Nat.Coprime 5 (Nat.card T₀) := by
    obtain ⟨b, hb⟩ := hT₀2.exists_card_eq
    rw [hb]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hgood : ∀ w ∈ U, w ∉ zpowers x → ∀ t ∈ T₀, t * w = w * t → t = 1 := by
    intro w hwU hwx t ht hcomm
    obtain ⟨m, hmM, J', hc'⟩ := hA10pt w hwU hwx
    have hmt : MulAut.conj m t ∈ T₀ := (mem_normalizer_iff.1 (hMT₀ hmM) t).1 ht
    have hX := a10_cor47 hS hD1 hU0 hA10 hc' (zpowers (MulAut.conj m t))
      (hT₀2.to_le (zpowers_le.2 hmt)) ((zpowers_le.2 hmt).trans hO2R)
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 (by rw [← map_mul, ← map_mul, hcomm])))
    have h1 : MulAut.conj m t = 1 := by
      have := mem_zpowers (MulAut.conj m t)
      rw [hX] at this
      exact mem_bot.1 this
    simpa using h1
  have hgood2 : ∀ v ∈ U, v ≠ 1 → T₀ ⊓ centralizer ({v} : Set G) ≤ centralizer ({x} : Set G) := by
    intro v hvU hv1
    by_cases hvx : v ∈ zpowers x
    · have hvz : zpowers v = zpowers x := Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hvx)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime (hUel.2 v hvU) hv1, hxo])
      have hxv : x ∈ zpowers v := by rw [hvz]; exact mem_zpowers x
      obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hxv
      intro g hg
      have hgv : g * v = v * g := mem_centralizer_singleton_iff.1 hg.2
      rw [mem_centralizer_singleton_iff, ← hj]
      exact ((show Commute g v from hgv).zpow_right j).eq
    · intro g hg
      have hg1 : g = 1 := hgood v hvU hvx g hg.1 (mem_centralizer_singleton_iff.1 hg.2)
      rw [hg1]
      exact one_mem _
  have hT₀C : T₀ ≤ centralizer ({x} : Set G) :=
    CFSG.LocalAnalysis.RankFourTheoremC.le_of_forall_inf_centralizer_le_plane Nat.prime_five hUel
      hUcard (fun d hd => hMT₀ (hUM hd)) hcop hgood2
  have hxT : x ∈ T₀ := hS.charTwo M hM2loc
    ⟨hxM, mem_centralizer_iff.mpr fun t ht => mem_centralizer_singleton_iff.mp (hT₀C ht)⟩
  obtain ⟨k, hk⟩ := hT₀2 ⟨x, hxT⟩
  have h2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h5 : orderOf x ∣ 5 := orderOf_dvd_of_pow_eq_one hxp
  have hcoprime : Nat.Coprime 5 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
  exact hx1 (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one (hcoprime.gcd_eq_one ▸ Nat.dvd_gcd h5 h2)))

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
