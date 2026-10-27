module

public import CFSG.ClassicalInvolution.Q3.TL3Ident
public import CFSG.ClassicalInvolution.TwoGroupCase.Fusion
public import CFSG.ClassicalInvolution.Q3.Basic

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution
open scoped MatrixGroups commutatorElement

section Helpers

variable {G : Type*} [Group G] [Finite G]

theorem mem_oddCoreImg_of_le {R J : Subgroup G} (hRJ : R ≤ J) {w : G} (hwR : w ∈ R)
    (hwJ : w ∈ oddCoreImg J) : w ∈ oddCoreImg R := by
  set N : Subgroup R := (oddCoreImg J).subgroupOf R with hN
  have hNn : N.Normal := by
    refine ⟨fun u hu r => ?_⟩
    rw [hN, Subgroup.mem_subgroupOf] at hu ⊢
    have hrJ : (r : G) ∈ Subgroup.normalizer (J : Set G) := Subgroup.le_normalizer (hRJ r.2)
    have := conj_mem_oddCoreImg hrJ hu
    simpa using this
  have hNodd : Odd (Nat.card N) := by
    have hle : N.map R.subtype ≤ oddCoreImg J := by
      rintro _ ⟨u, hu, rfl⟩
      exact hu
    have h1 : Nat.card (N.map R.subtype) = Nat.card N :=
      Subgroup.card_map_of_injective R.subtype_injective
    rw [← h1]
    exact (odd_natCard_oddCoreImg J).of_dvd_nat (Subgroup.card_dvd_of_le hle)
  have hle : N ≤ oddCore R := le_sSup ⟨hNn, hNodd⟩
  have hmem : (⟨w, hwR⟩ : R) ∈ oddCore R := hle (Subgroup.mem_subgroupOf.mpr hwJ)
  exact ⟨⟨w, hwR⟩, hmem, rfl⟩

end Helpers

theorem mem_oddCore_of_isPGroup_quotient {J : Type*} [Group J]
    (h : IsPGroup 2 (J ⧸ oddCore J)) {x : J} {k : ℕ} (hx : x ^ 3 ^ k = 1) : x ∈ oddCore J := by
  set y : J ⧸ oddCore J := (x : J ⧸ oddCore J) with hy
  have h3 : y ^ 3 ^ k = 1 := by rw [hy, ← QuotientGroup.mk_pow, hx, QuotientGroup.mk_one]
  obtain ⟨m, hm⟩ := h y
  have hcop : Nat.Coprime (2 ^ m) (3 ^ k) := by
    apply Nat.Coprime.pow
    norm_num
  have hd : orderOf y ∣ 1 := by
    have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hm) (orderOf_dvd_of_pow_eq_one h3)
    rwa [hcop] at this
  have hy1 : y = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  exact (QuotientGroup.eq_one_iff x).mp hy1


section Main

theorem isClassicalMember3_of_subnormal {G : Type} [Group G] [Finite G] {R : Subgroup G}
    (S : Sylow 2 R) (hS : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2)) {t : G}
    (ht : t ∈ (S : Subgroup R).map R.subtype) (hto : orderOf t = 2)
    (hRC : R ≤ Subgroup.centralizer ({t} : Set G))
    (hRn : (R.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal)
    (h2 : IsPGroup 2 (R ⧸ classicalInvolutionOddCore R))
    {x : G} (hxC : x ∈ Subgroup.centralizer ({t} : Set G)) {k : ℕ} (hx3 : x ^ 3 ^ k = 1)
    (hxR : ∃ r ∈ R, ⁅x, r⁆ ∉ oddCoreImg R)
    (hsub : IsSubnormal
      (R ⊔ Subgroup.zpowers x ⊔ oddCoreImg (Subgroup.centralizer ({t} : Set G)))
      (Subgroup.centralizer ({t} : Set G))) :
    IsClassicalMember3
      (R ⊔ Subgroup.zpowers x ⊔ oddCoreImg (Subgroup.centralizer ({t} : Set G))) t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := Subgroup.centralizer ({t} : Set G) with hC
  set O : Subgroup G := oddCoreImg C with hO
  set J : Subgroup G := R ⊔ Subgroup.zpowers x ⊔ O with hJ
  have hOC : O ≤ C := oddCoreImg_le C
  have hRJ : R ≤ J := le_sup_left.trans le_sup_left
  have hXJ : Subgroup.zpowers x ≤ J := le_sup_right.trans le_sup_left
  have hOJ : O ≤ J := le_sup_right
  have hxJ : x ∈ J := hXJ (Subgroup.mem_zpowers x)
  have hJC : J ≤ C := sup_le (sup_le hRC (Subgroup.zpowers_le.mpr hxC)) hOC
  have hCR : C ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRC).mp hRn
  have hconjO : ∀ g ∈ C, ∀ o ∈ O, g * o * g⁻¹ ∈ O := fun g hg o ho =>
    conj_mem_oddCoreImg (Subgroup.le_normalizer hg) ho
  set R' : Subgroup J := R.subgroupOf J with hR'
  set O' : Subgroup J := O.subgroupOf J with hO'
  set X' : Subgroup J := (Subgroup.zpowers x).subgroupOf J with hX'
  have hR'n : R'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRJ).mpr (hJC.trans hCR)
  have hO'n : O'.Normal := ⟨fun u hu j => by
    rw [hO', Subgroup.mem_subgroupOf] at hu ⊢
    simpa using hconjO (j : G) (hJC j.2) (u : G) hu⟩
  have htop : R' ⊔ X' ⊔ O' = ⊤ := by
    rw [hR', hX', hO', ← Subgroup.subgroupOf_sup hRJ hXJ,
      ← Subgroup.subgroupOf_sup (sup_le hRJ hXJ) hOJ]
    exact Subgroup.subgroupOf_self J
  have hKX : (R' ⊔ O') ⊔ X' = ⊤ := by rw [sup_right_comm]; exact htop
  have hodd : Odd R'.index := by
    have h1 : R'.relIndex (R' ⊔ O') * (R' ⊔ O').relIndex ⊤ = R'.relIndex ⊤ :=
      Subgroup.relIndex_mul_relIndex _ _ _ le_sup_left le_top
    rw [Subgroup.relIndex_top_right, Subgroup.relIndex_top_right] at h1
    rw [← h1]
    refine Odd.mul ?_ ?_
    · rw [Subgroup.relIndex_sup_left O' R']
      have hcard : Nat.card O' = Nat.card O :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOJ).toEquiv
      have hd : R'.relIndex O' ∣ Nat.card O' := Subgroup.index_dvd_card (R'.subgroupOf O')
      rw [hcard] at hd
      exact (odd_natCard_oddCoreImg C).of_dvd_nat hd
    · have e := Subgroup.relIndex_sup_left X' (R' ⊔ O')
      rw [hKX, Subgroup.relIndex_top_right] at e
      rw [e]
      have hcard : Nat.card X' = orderOf x := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXJ).toEquiv, Nat.card_zpowers]
      have hd : (R' ⊔ O').relIndex X' ∣ Nat.card X' :=
        Subgroup.index_dvd_card ((R' ⊔ O').subgroupOf X')
      rw [hcard] at hd
      have h3 : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hx3
      exact (Odd.pow (by decide : Odd 3)).of_dvd_nat (hd.trans h3)
  have hRsolv : Group.IsSolvable R := by
    have hO : Group.IsSolvable (classicalInvolutionOddCore R) :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ (CFSG.ComponentClassification.OddCore.odd_card R)
    have hq : Group.IsSolvable (R ⧸ classicalInvolutionOddCore R) :=
      have := h2.isNilpotent
      inferInstance
    exact Group.isSolvable_of_subgroup_quotient (classicalInvolutionOddCore R)
  have hR'solv : Group.IsSolvable R' :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hRJ).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hRJ).injective
  have hJsolv : Group.IsSolvable J := by
    have hq : Group.IsSolvable (J ⧸ R') :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ (by
        rw [← Subgroup.index_eq_card]
        exact hodd)
    exact Group.isSolvable_of_subgroup_quotient R'
  let φ : R ≃* R' := (Subgroup.subgroupOfEquivOfLe hRJ).symm
  let T : Sylow 2 R' := S.mapSurjective (f := φ.toMonoidHom) φ.surjective
  have hT : Nonempty ((T : Subgroup R') ≃* QuaternionGroup 2) := by
    obtain ⟨e⟩ := hS
    have hTc : (T : Subgroup R') = (S : Subgroup R).map φ.toMonoidHom :=
      Sylow.coe_mapSurjective φ.surjective S
    exact ⟨(MulEquiv.subgroupCongr hTc).trans
      ((MulEquiv.subgroupMap φ (S : Subgroup R)).symm.trans e)⟩
  have hnot : ¬ IsPGroup 2 (J ⧸ oddCore J) := by
    intro hP
    obtain ⟨r, hrR, hr⟩ := hxR
    apply hr
    have hxo : (⟨x, hxJ⟩ : J) ∈ oddCore J :=
      mem_oddCore_of_isPGroup_quotient hP (k := k) (Subtype.ext hx3)
    have hrJ : r ∈ J := hRJ hrR
    have hcomm : ⁅x, r⁆ = x * (r * x⁻¹ * r⁻¹) := by
      rw [commutatorElement_def]; group
    have hwJ : ⁅x, r⁆ ∈ oddCoreImg J := by
      have hn : (oddCore J).Normal := inferInstance
      have h1 : (⟨r, hrJ⟩ : J) * (⟨x, hxJ⟩ : J)⁻¹ * (⟨r, hrJ⟩ : J)⁻¹ ∈ oddCore J := by
        have := hn.conj_mem _ ((oddCore J).inv_mem hxo) ⟨r, hrJ⟩
        simpa [mul_assoc] using this
      refine ⟨_, (oddCore J).mul_mem hxo h1, ?_⟩
      rw [hcomm]; rfl
    have hwR : ⁅x, r⁆ ∈ R := by
      have hxr : x * r * x⁻¹ ∈ R := by
        have := (Subgroup.mem_normalizer_iff.mp (hCR hxC) r).mp hrR
        simpa using this
      rw [commutatorElement_def]
      exact R.mul_mem hxr (R.inv_mem hrR)
    exact mem_oddCoreImg_of_le hRJ hwR hwJ
  refine ⟨hto, hRJ (Subgroup.map_subtype_le _ ht), hsub, ?_⟩
  exact nonempty_mulEquiv_sl2Three_of_normal_odd_index R' hodd T hT hnot

end Main

end CFSG.ClassicalInvolution.Q3
