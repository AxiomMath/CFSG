module

public import CFSG.LocalAnalysis.OddStandard.AltStdWeakSec
public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootData

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup AltStdBal

section Top

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ} {z : G}

theorem mem_zpowers_of_two_element (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) {c : G}
    (hc : c ∈ centralizer (L : Set G) ⊓ centralizer ({z} : Set G)) {k : ℕ}
    (hck : c ^ 2 ^ k = 1) : c ∈ zpowers z := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := centralizer (L : Set G) ⊓ centralizer ({z} : Set G) with hM
  have hQz : zpowers z = Q := Subgroup.eq_of_le_of_card_ge (zpowers_le.2 d.mem)
    (by rw [hQ2, Nat.card_zpowers, d.order])
  have hQM : Q ≤ M := by
    rw [← hQz, zpowers_le]
    exact ⟨d.le d.mem, mem_centralizer_singleton_iff.2 rfl⟩
  have hMK : M ≤ centralizer (L : Set G) := inf_le_left
  have hi : ¬ 2 ∣ (Q.subgroupOf M).index := by
    intro h2
    apply d.odd_index
    exact h2.trans (Dvd.intro _ (relIndex_mul_relIndex Q M (centralizer (L : Set G)) hQM hMK))
  have hQp : IsPGroup 2 (Q.subgroupOf M) := d.pgroup.of_equiv (subgroupOfEquivOfLe hQM).symm
  have hQn : (Q.subgroupOf M).Normal := by
    refine ⟨fun q hq m => ?_⟩
    have hq' : (q : G) ∈ zpowers z := by rw [hQz]; exact hq
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hq'
    have hmz : (m : G) * z = z * m := (mem_centralizer_singleton_iff.1 m.2.2)
    have hcomm : (m : G) * q = q * m := by
      rw [← hj]
      exact ((Commute.zpow_right (show Commute (m : G) z from hmz) j)).eq
    show (m : G) * q * (m : G)⁻¹ ∈ Q
    rw [hcomm, mul_inv_cancel_right]
    exact hq
  let S : Sylow 2 M := hQp.toSylow hi
  have hSeq : (S : Subgroup M) = Q.subgroupOf M := IsPGroup.toSylow_coe hQp hi
  have hSn : (S : Subgroup M).Normal := by rw [hSeq]; exact hQn
  let c' : M := ⟨c, hc⟩
  have hc'k : c' ^ 2 ^ k = 1 := Subtype.ext (by simpa using hck)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hc'k)
  have hcp : IsPGroup 2 (zpowers c') := IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  have := hSn
  have hsup : IsPGroup 2 ((S : Subgroup M) ⊔ zpowers c' : Subgroup M) :=
    S.isPGroup'.to_sup_of_normal_left hcp
  have heq := S.is_maximal' hsup le_sup_left
  have hcS : c' ∈ (S : Subgroup M) := heq ▸ (le_sup_right (a := (S : Subgroup M)))
    (mem_zpowers c')
  rw [hSeq] at hcS
  have : c ∈ Q := hcS
  rw [← hQz] at this
  exact this

theorem weakShape_of_cyc (hstd : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (e : L ≃* alternatingGroup (Fin n)) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) :
    WeakShape z L n :=
  ⟨d.order, ⟨e⟩,
    (CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hstd
      (d.le d.mem) d.order).2.1,
    (CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hstd
      (d.le d.mem) d.order).1,
    fun _ hc _ hck => mem_zpowers_of_two_element d hQ2 hc hck⟩

end Top

section Root

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {z : G}

omit [Finite G] in
theorem centralizer_corr_ne_top (hsimple : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (e : L ≃* alternatingGroup (Fin n)) {S : Finset (Fin n)} (hS : 3 ≤ S.card) :
    centralizer (corr (X := G) e (altSub S) : Set G) ≠ ⊤ := by
  intro htop
  have hZ : center G = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (center G) with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (Subgroup.mem_center_iff.1 (h1 ▸ mem_top b) a)
  obtain ⟨eR⟩ := exists_equiv_corr_altSub (X := G) e S
  obtain ⟨x, hx3⟩ := exists_orderOf_three (by omega : 3 ≤ S.card)
  set r : G := ((eR.symm x : corr (X := G) e (altSub S)) : G) with hr
  have hrc : r ∈ center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ centralizer (corr (X := G) e (altSub S) : Set G) := htop ▸ mem_top g
    exact (mem_centralizer_iff.1 hg r (eR.symm x).2).symm
  rw [hZ, mem_bot] at hrc
  have hord : orderOf r = 3 := by
    rw [hr, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hx3]
  rw [hrc, orderOf_one] at hord
  omega

theorem rootData_of_weakShape (hlookup : AltComponentLookup)
    (hHN : CFSG.ComponentClassification.RestrictedStd.Spor.HNLocalComponentsInput)
    (hOut : CFSG.RankThree.PartOne.SporadicOuterOrderLeTwoSimple)
    (hFour : CFSG.ComponentClassification.RestrictedStd.Spor.FourExactOuterInput)
    (hS : StandardSetting G L) {Q : Subgroup G} (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (e : L ≃* alternatingGroup (Fin n)) {S : Finset (Fin n)} (hS4 : 4 ≤ S.card)
    (hSc : 9 ≤ n - S.card) :
    RootData L z (rootGroup e S) (corr (X := G) e (altSub Sᶜ)) (n - S.card) := by
  have hW := weakShape_of_cyc hS.standard e d hQ2
  have hz : z ∈ centralizer (corr (X := G) e (altSub S) : Set G) := by
    rw [mem_centralizer_iff]
    intro r hr
    exact mem_centralizer_singleton_iff.1 (hW.le_cent (corr_le e _ hr))
  have hKC : CFSG.SectionRank.IsKGroupCat (Sec G (corr (X := G) e (altSub S))) :=
    (isKGroupCat_of_kProper hS.kProper _
      (centralizer_corr_ne_top hS.simple hS.nonab e (by omega))).quotient _
  refine ⟨hz, exactShape_section_root_of_weakShape hlookup hHN hOut hFour hW e hS4 hSc hz hKC, ?_⟩
  intro c hcL
  refine mem_sup_left ?_
  have hcR : (c : G) ∈ centralizer (corr (X := G) e (altSub S) : Set G) := c.2
  have h1 := perm_mem_centralizer_of_mem_centralizer_corr e (altSub_le_alternatingGroup S)
    hcL hcR
  have h2 : ((e ⟨c, hcL⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ∈
      altSub Sᶜ := by
    rw [← centralizer_altSub_inf_alt hS4]
    exact Subgroup.mem_inf.2 ⟨h1, (e ⟨c, hcL⟩).2⟩
  exact mem_corr_of_perm_mem e hcL h2

theorem rootData_of_weakShape_three (hlookup : AltComponentLookup)
    (hHN : CFSG.ComponentClassification.RestrictedStd.Spor.HNLocalComponentsInput)
    (hOut : CFSG.RankThree.PartOne.SporadicOuterOrderLeTwoSimple)
    (hFour : CFSG.ComponentClassification.RestrictedStd.Spor.FourExactOuterInput)
    (hS : StandardSetting G L) {Q : Subgroup G} (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (e : L ≃* alternatingGroup (Fin n)) {S : Finset (Fin n)} (hS3 : S.card = 3)
    (hSc : 9 ≤ n - S.card) :
    RootData L z (rootGroup e S) (corr (X := G) e (altSub Sᶜ)) (n - S.card) := by
  have hW := weakShape_of_cyc hS.standard e d hQ2
  have hz : z ∈ centralizer (corr (X := G) e (altSub S) : Set G) := by
    rw [mem_centralizer_iff]
    intro r hr
    exact mem_centralizer_singleton_iff.1 (hW.le_cent (corr_le e _ hr))
  have hKC : CFSG.SectionRank.IsKGroupCat (Sec G (corr (X := G) e (altSub S))) :=
    (isKGroupCat_of_kProper hS.kProper _
      (centralizer_corr_ne_top hS.simple hS.nonab e (by omega))).quotient _
  refine ⟨hz, exactShape_section_three_of_weakShape hlookup hHN hOut hFour hW e hS3 hSc hz hKC,
    ?_⟩
  intro c hcL
  have hRO : rootGroup (G := G) e S ≤ oddCoreOf (centralizer (rootGroup (G := G) e S : Set G)) :=
    corr_altSub_le_oddCoreOf e hS3
  have hcR : (c : G) ∈ centralizer (corr (X := G) e (altSub S) : Set G) := c.2
  have h1 := perm_mem_centralizer_of_mem_centralizer_corr e (altSub_le_alternatingGroup S)
    hcL hcR
  obtain ⟨r, hr, s, hs, hrs⟩ := (mem_centralizer_altSub_card_three_iff hS3).1 h1
  have hrA : r ∈ alternatingGroup (Fin n) := altSub_le_alternatingGroup S hr
  have hsgn : Equiv.Perm.sign s = 1 := by
    have h2 := Equiv.Perm.mem_alternatingGroup.1 (e ⟨c, hcL⟩).2
    rw [hrs, map_mul, (mem_altSub.1 hr).1, one_mul] at h2
    exact h2
  have hsA : s ∈ altSub Sᶜ :=
    mem_altSub.2 ⟨hsgn, fun i hi => hs i (by simpa using hi)⟩
  have hsA' : s ∈ alternatingGroup (Fin n) := altSub_le_alternatingGroup _ hsA
  have hcomm : r * s = s * r := comm_altSub_fixSub hr hs
  set cr : L := e.symm ⟨r, hrA⟩ with hcr
  set cs : L := e.symm ⟨s, hsA'⟩ with hcs
  have hecr : e cr = ⟨r, hrA⟩ := by simp [hcr]
  have hecs : e cs = ⟨s, hsA'⟩ := by simp [hcs]
  have hcr_mem : (cr : G) ∈ rootGroup (G := G) e S := mem_corr_of_mem (by rw [hecr]; exact hr)
  have hcs_mem : (cs : G) ∈ corr (X := G) e (altSub Sᶜ) :=
    mem_corr_of_mem (by rw [hecs]; exact hsA)
  have hceq : (⟨c, hcL⟩ : L) = cs * cr := by
    apply e.injective
    rw [map_mul, hecs, hecr]
    apply Subtype.ext
    show ((e ⟨c, hcL⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) = s * r
    rw [hrs, hcomm]
  have hceqG : (c : G) = cs * cr := congrArg Subtype.val hceq
  obtain ⟨hcrH, hcrO⟩ := mem_oddCoreOf_iff.1 (hRO hcr_mem)
  have hcsH : (cs : G) ∈ centralizer (rootGroup (G := G) e S : Set G) := by
    have : (cs : G) = c * (cr : G)⁻¹ := by rw [hceqG]; group
    rw [this]
    exact mul_mem c.2 (inv_mem hcrH)
  have : c = ⟨cs, hcsH⟩ * ⟨cr, hcrH⟩ := Subtype.ext hceqG
  rw [this]
  exact mul_mem_sup hcs_mem hcrO

end Root

end CFSG.OddStandard.AltStdSec
