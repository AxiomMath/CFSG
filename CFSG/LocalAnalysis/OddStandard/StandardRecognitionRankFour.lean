module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Standard
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveStrong
public import CFSG.Mathlib.GroupTheory.ConjCentralizer
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.SteinbergBKOrderTwoCentralizerStandard
public import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI

public section

namespace CFSG.LocalAnalysis.OddStandard

open Subgroup
open CFSG.OddStandard.SmallF3.Omega

private theorem eq_bot_of_isPGroup_two_of_odd_card_le {G : Type*} [Group G] [Finite G]
    {A Z : Subgroup G} (hA : IsPGroup 2 A) (hZ : Odd (Nat.card Z)) (hAZ : A ≤ Z) :
    A = ⊥ := by
  obtain ⟨k, hk⟩ := hA.exists_card_eq
  have hAodd : Odd (Nat.card A) :=
    Odd.of_dvd_nat hZ (Subgroup.card_dvd_of_le hAZ)
  have hk0 : k = 0 := by
    by_contra hk0
    have heven : Even (2 ^ k) := Nat.even_pow.mpr ⟨even_two, hk0⟩
    exact (Nat.not_even_iff_odd.mpr hAodd) (hk ▸ heven)
  rw [Subgroup.eq_bot_iff_card, hk, hk0, pow_zero]

theorem standardComponentIsStandard_of_pRank_le_one_centralizer
    {G : Type} [Group G] [Finite G] {x : G} (hx : orderOf x = 2)
    {P : Subgroup G} (hP : IsComponentIn P (Subgroup.centralizer ({x} : Set G)))
    (hPrank : 2 ≤ CFSG.pRank 2 ↥P)
    (hDrank : CFSG.pRank 2 (Subgroup.centralizer (P : Set G)) ≤ 1) :
    CFSG.Open.standardComponentIsStandard P := by
  classical
  let D : Subgroup G := Subgroup.centralizer (P : Set G)
  have hPrankOpen : 2 ≤ CFSG.Open.pRank 2 P := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup P,
      ← CFSG.SectionRank.pRank_eq_open_pRank_top 2 ↥P]
    exact hPrank
  have hDrankOpen : CFSG.Open.pRank 2 D ≤ 1 := by
    have hDrank' : CFSG.pRank 2 ↥D ≤ 1 := by simpa [D] using hDrank
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup D,
      ← CFSG.SectionRank.pRank_eq_open_pRank_top 2 ↥D]
    exact hDrank'
  have hxD : x ∈ D := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact Subgroup.mem_centralizer_singleton_iff.mp (hP.le hp)

  have h2 : ComponentAtCentralInvolutions P := by
    intro t ht2 htD
    obtain ⟨c, hcD, hc⟩ :=
      CFSG.ComponentClassification.AschbacherTheorem5.SectionSix.Strong.conj_of_pRank_le_one
        (K := D) hDrankOpen hxD hx htD ht2
    have hPfix : P.map (MulAut.conj c⁻¹).toMonoidHom = P :=
      CFSG.LocalAnalysis.SteinbergBK.map_conj_eq_self_of_mem_centralizer
        (J := P) (k := c⁻¹) (by simpa [D] using D.inv_mem hcD)
    have htEq : t = c⁻¹ * x * c := by
      have h := congrArg (fun y : G => c⁻¹ * y * c) hc
      simpa [mul_assoc] using h
    have hcentEq : (Subgroup.centralizer ({x} : Set G)).map
        (MulAut.conj c⁻¹).toMonoidHom = Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.map_conj_centralizer_singleton]
      simp only [inv_inv]
      rw [← htEq]
    have hPmap := hP.map_mulEquiv (MulAut.conj c⁻¹)
    rwa [hPfix, hcentEq] at hPmap

  have h4 : ∀ g : G, ⁅P, P.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
    intro g hcomm
    let Pg : Subgroup G := P.map (MulAut.conj g).toMonoidHom
    change ⁅P, Pg⁆ = ⊥ at hcomm
    have hPgD : Pg ≤ D := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      exact (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hp) y hy).symm
    have hPgRank : CFSG.Open.pRank 2 Pg = CFSG.Open.pRank 2 P := by
      refine le_antisymm ?_ (CFSG.SectionRank.pRank_le_map (p := 2) (by norm_num)
        (MulAut.conj g).toMonoidHom (MulAut.conj g).injective P)
      have hmap : Pg.map (MulAut.conj g⁻¹).toMonoidHom = P := by
        change (P.map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj g⁻¹).toMonoidHom = P
        rw [Subgroup.map_map]
        have hcomp : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
            MonoidHom.id G := by
          ext y
          change MulAut.conj g⁻¹ (MulAut.conj g y) = y
          rw [MulAut.conj_apply, MulAut.conj_apply]
          group
        rw [hcomp, Subgroup.map_id]
      calc
        CFSG.Open.pRank 2 Pg
            ≤ CFSG.Open.pRank 2 (Pg.map (MulAut.conj g⁻¹).toMonoidHom) :=
              CFSG.SectionRank.pRank_le_map (p := 2) (by norm_num) _
                (MulAut.conj g⁻¹).injective Pg
        _ = CFSG.Open.pRank 2 P := by rw [hmap]
    have hle : CFSG.Open.pRank 2 Pg ≤ CFSG.Open.pRank 2 D :=
      CFSG.SectionRank.pRank_mono (by norm_num) hPgD
    rw [hPgRank] at hle
    omega

  exact CFSG.OddStandard.SmallF3.Omega.standard_of_componentAtCentralInvolutions
    ⟨x, hx, hP⟩ h2 h4

theorem isStandardSubgroup_of_pRank_le_one_centralizer
    {G : Type} [Group G] [Finite G] {x : G} (hx : orderOf x = 2)
    {P : Subgroup G} (hP : IsComponentIn P (Subgroup.centralizer ({x} : Set G)))
    (hPrank : 2 ≤ CFSG.pRank 2 ↥P)
    (hDrank : CFSG.pRank 2 (Subgroup.centralizer (P : Set G)) ≤ 1) :
    CFSG.IsStandardSubgroup P :=
  CFSG.Open.standardComponentIsStandard.isStandardSubgroup
    (standardComponentIsStandard_of_pRank_le_one_centralizer hx hP hPrank hDrank)

theorem standardComponentIsStandard_of_pRank_le_four_of_actualE8
    {G : Type} [Group G] [Finite G] {x : G} (hx : orderOf x = 2)
    {P : Subgroup G} (hP : IsComponentIn P (Subgroup.centralizer ({x} : Set G)))
    (hZ : Odd (Nat.card (Subgroup.center P)))
    {A : Subgroup G} (hAP : A ≤ P) (hA : CFSG.Open.IsElemAbelian 2 A)
    (hA8 : Nat.card A = 8) (hPr : CFSG.pRank 2 G ≤ 4) :
    CFSG.Open.standardComponentIsStandard P := by
  classical
  let D : Subgroup G := Subgroup.centralizer (P : Set G)
  have hPrOpen : CFSG.Open.pRank 2 (⊤ : Subgroup G) ≤ 4 := by
    rwa [← CFSG.SectionRank.pRank_eq_open_pRank_top (p := 2) G]
  have hcenterMapOdd : Odd (Nat.card ((Subgroup.center P).map P.subtype)) := by
    rw [Subgroup.card_map_of_injective P.subtype_injective]
    exact hZ
  have hxD : x ∈ D := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact Subgroup.mem_centralizer_singleton_iff.mp (hP.le hp)
  have hDrank : CFSG.Open.twoRank D ≤ 1 := by
    by_contra hle
    have h2 : 2 ≤ CFSG.Open.twoRank D := by omega
    obtain ⟨B, -, hBe, hBcard⟩ :=
      CFSG.SectionRank.exists_pRank (G := D) (p := 2) (by norm_num) (⊤ : Subgroup D)
    have hBcard' : Nat.card B = 2 ^ CFSG.Open.twoRank D := by
      simpa [CFSG.Open.twoRank] using hBcard
    have hdvd : 2 ^ 2 ∣ Nat.card B := by
      rw [hBcard']
      exact Nat.pow_dvd_pow 2 h2
    obtain ⟨K, hKcard⟩ :=
      @Sylow.exists_subgroup_card_pow_prime ↥B _ _ 2 (n := 2) ⟨Nat.prime_two⟩ hdvd
    let Kd : Subgroup D := K.map B.subtype
    let B4 : Subgroup G := Kd.map D.subtype
    have hKdE : CFSG.Open.IsElemAbelian 2 Kd :=
      hBe.mono (Subgroup.map_subtype_le K)
    have hKdCard : Nat.card Kd = 4 := by
      rw [Subgroup.card_map_of_injective B.subtype_injective]
      norm_num at hKcard ⊢
      exact hKcard
    have hB4E : CFSG.Open.IsElemAbelian 2 B4 := by
      simpa [B4] using hKdE.map D.subtype
    have hB4Card : Nat.card B4 = 4 := by
      rw [Subgroup.card_map_of_injective D.subtype_injective]
      exact hKdCard
    have hB4D : B4 ≤ D := by
      exact Subgroup.map_subtype_le Kd
    have hcommAB : ∀ a ∈ A, ∀ b ∈ B4, a * b = b * a := by
      intro a ha b hb
      exact Subgroup.mem_centralizer_iff.mp (hB4D hb) a (hAP ha)
    have hIntLeCenter : A ⊓ B4 ≤ (Subgroup.center P).map P.subtype := by
      rintro z hz
      rw [Subgroup.mem_inf] at hz
      have hzP : z ∈ P := hAP hz.1
      refine ⟨⟨z, hzP⟩, ?_, rfl⟩
      change (⟨z, hzP⟩ : P) ∈ Subgroup.center P
      rw [Subgroup.mem_center_iff]
      intro p
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hB4D hz.2) p p.2)
    have hIntBot : A ⊓ B4 = ⊥ :=
      eq_bot_of_isPGroup_two_of_odd_card_le
        (hA.isPGroup.to_le (inf_le_left : A ⊓ B4 ≤ A)) hcenterMapOdd hIntLeCenter
    have hE32E : CFSG.Open.IsElemAbelian 2 (A ⊔ B4) :=
      hA.sup_of_commute hB4E hcommAB
    have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B4 hcommAB).1
    rw [hIntBot, Subgroup.card_bot, mul_one, hA8, hB4Card] at hprod
    norm_num at hprod
    have hE32Card : Nat.card ↥(A ⊔ B4) = 32 := hprod
    have h5 : 5 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup G) :=
      CFSG.SectionRank.le_pRank (by norm_num) le_top hE32E (by
        rw [hE32Card]
        norm_num)
    omega

  have hDrankP : CFSG.pRank 2 (Subgroup.centralizer (P : Set G)) ≤ 1 := by
    have hDrankTop : CFSG.Open.pRank 2 (⊤ : Subgroup D) ≤ 1 := by
      simpa [CFSG.Open.twoRank] using hDrank
    have hDrank' : CFSG.pRank 2 ↥D ≤ 1 := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top 2 ↥D]
      exact hDrankTop
    simpa [D] using hDrank'
  have hPrank : 2 ≤ CFSG.pRank 2 ↥P := by
    have hPrank3 : 3 ≤ CFSG.Open.pRank 2 P :=
      CFSG.SectionRank.le_pRank (p := 2) (by norm_num) hAP hA (by
        rw [hA8]
        norm_num)
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top 2 ↥P,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup P]
    omega
  exact standardComponentIsStandard_of_pRank_le_one_centralizer hx hP hPrank hDrankP

theorem isStandardSubgroup_of_pRank_le_four_of_actualE8
    {G : Type} [Group G] [Finite G] {x : G} (hx : orderOf x = 2)
    {P : Subgroup G} (hP : IsComponentIn P (Subgroup.centralizer ({x} : Set G)))
    (hZ : Odd (Nat.card (Subgroup.center P)))
    {A : Subgroup G} (hAP : A ≤ P) (hA : CFSG.Open.IsElemAbelian 2 A)
    (hA8 : Nat.card A = 8) (hPr : CFSG.pRank 2 G ≤ 4) :
    CFSG.IsStandardSubgroup P :=
  CFSG.Open.standardComponentIsStandard.isStandardSubgroup
    (standardComponentIsStandard_of_pRank_le_four_of_actualE8
      hx hP hZ hAP hA hA8 hPr)

end CFSG.LocalAnalysis.OddStandard

end
