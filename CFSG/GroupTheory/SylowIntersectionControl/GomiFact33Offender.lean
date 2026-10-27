module

public import CFSG.CGT.PushingUpLit.BHS.FourSymA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
import CFSG.Goldschmidt.Steps.G53Tools
import CFSG.GroupTheory.ThompsonAxB
import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.TransvectionPair
import CFSG.Quasithin.Background.FixVZPowersMem
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.F6GoldschmidtList
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
import CFSG.Goldschmidt.Statements
import CFSG.Goldschmidt.StatementsG2
import CFSG.Goldschmidt.StatementsH
import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyStatements
import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion
import CFSG.Walter.Bender1970.S1
import CFSG.Walter.Bender1970.S2
import CFSG.Walter.Bender1970.S3
import CFSG.Walter.PSL2Facts
import Certificates.Certificate1
import Certificates.Certificate10
import Certificates.Certificate100
import Certificates.Certificate101
import Certificates.Certificate102
import Certificates.Certificate103
import Certificates.Certificate104
import Certificates.Certificate105
import Certificates.Certificate106
import Certificates.Certificate107
import Certificates.Certificate108
import Certificates.Certificate109
import Certificates.Certificate11
import Certificates.Certificate12
import Certificates.Certificate2
import Certificates.Certificate3
import Certificates.Certificate4
import Certificates.Certificate42
import Certificates.Certificate44
import Certificates.Certificate5
import Certificates.Certificate6
import Certificates.Certificate7
import Certificates.Certificate8
import Certificates.Certificate9
import Certificates.Certificate96
import Certificates.Certificate97
import Certificates.Certificate98
import Certificates.Certificate99

public section

namespace CFSG.GroupTheory

open CFSG.CGT.PushingUpLit.BHS (IsTransv)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (Pset PstarSet)

variable {W : Type} [CommGroup W] [Finite W]

open CFSG.Quasithin (fixV mem_fixV mem_fixV_zpowers_iff_apply IsElemAbelian2)
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit (exists_isTransvCentred)

private theorem exists_hyperplane_noncomm {A R : Subgroup (MulAut W)} (hA : IsElemAbelian2 A)
    (hR : Odd (Nat.card R)) (hAR : A ≤ Subgroup.normalizer (R : Set (MulAut W)))
    (hnc : ¬ A ≤ Subgroup.centralizer (R : Set (MulAut W))) :
    ∃ B ≤ A, (B.subgroupOf A).index = 2 ∧ ∃ t ∈ A, ∃ r ∈ R,
      r ∈ Subgroup.centralizer (B : Set (MulAut W)) ∧ r * t ≠ t * r := by
  obtain ⟨t, htA, htR⟩ := Set.not_subset.mp hnc
  have ht1 : t ≠ 1 := fun h => htR (h ▸ Subgroup.one_mem _)
  have hA' : CFSG.Open.IsElemAbelian 2 A :=
    ⟨⟨⟨fun a b => Subtype.ext (hA.1 a a.2 b b.2)⟩⟩, hA.2⟩
  have htD : ⁅Subgroup.zpowers t, R⁆ ≠ ⊥ := by
    rw [Ne, Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.zpowers_le]
    exact htR
  obtain ⟨B, hBA, hBi, hB⟩ :=
    CFSG.Goldschmidt.G53.exists_hyperplane_commutator_ne_bot hA' htA ht1 hAR hR htD
  rw [Ne, Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.zpowers_le,
    Subgroup.mem_centralizer_iff] at hB
  push Not at hB
  obtain ⟨r, ⟨hrR, hrB⟩, hrt⟩ := hB
  exact ⟨B, hBA, hBi, t, htA, r, hrR, hrB, hrt⟩

omit [Finite W] in
private theorem card_eq_two_mul_of_index {A B : Subgroup (MulAut W)} (hBA : B ≤ A)
    (hBi : (B.subgroupOf A).index = 2) : Nat.card A = 2 * Nat.card B := by
  rw [← (B.subgroupOf A).card_mul_index, hBi,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv, mul_comm]

private theorem exists_moved_fixV {B : Subgroup (MulAut W)} (hW : ∀ w : W, w ^ 2 = 1)
    (hB : ∀ b ∈ B, b ^ 2 = 1) {x : MulAut W} (hx : Odd (orderOf x))
    (hxB : ∀ b ∈ B, b * x = x * b) (hx1 : x ≠ 1) : ∃ w ∈ fixV B, x w ≠ w := by
  by_contra hcon
  push Not at hcon
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWp : IsPGroup 2 W := fun w => ⟨1, by simpa using hW w⟩
  have hBp : IsPGroup 2 B := fun b => ⟨1, Subtype.ext (by simpa using hB b b.2)⟩
  have hodd : ¬ 2 ∣ Nat.card (Subgroup.zpowers x) := by
    rw [Nat.card_zpowers]
    exact fun h => (Nat.not_even_iff_odd.mpr hx) (even_iff_two_dvd.mpr h)
  have hcomm : ∀ (a : Subgroup.zpowers x) (b : B),
      (Subgroup.zpowers x).subtype a * B.subtype b =
        B.subtype b * (Subgroup.zpowers x).subtype a := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact ((Commute.zpow_right (hxB b hb) k).eq).symm
  have hfix : ∀ (a : Subgroup.zpowers x) (w : W), (∀ b : B, B.subtype b w = w) →
      (Subgroup.zpowers x).subtype a w = w := fun a w hw =>
    (mem_fixV_zpowers_iff_apply.mpr (hcon w fun b hb => hw ⟨b, hb⟩)) a a.2
  have h := CFSG.GroupTheory.thompson_A_times_B hWp hodd hBp _ _ hcomm hfix
    ⟨x, Subgroup.mem_zpowers x⟩
  exact hx1 h

omit [Finite W] in
private theorem exists_moved_of_inverts {U : Subgroup W} {t x : MulAut W} (ht : t * t = 1)
    (htx : t * x * t⁻¹ = x⁻¹) (hx : Odd (orderOf x)) (hxU : ∀ w ∈ U, x w ∈ U)
    (hmove : ∃ w ∈ U, x w ≠ w) : ∃ w ∈ U, t w ≠ w := by
  by_contra hcon
  push Not at hcon
  obtain ⟨w, hw, hxw⟩ := hmove
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have h1 : t (x (t⁻¹ w)) = x⁻¹ w := by
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, htx]
  rw [htinv, hcon w hw, hcon _ (hxU w hw)] at h1
  have hsq : x * x ∈ MulAction.stabilizer (MulAut W) w := by
    rw [MulAction.mem_stabilizer_iff]
    change x (x w) = w
    rw [h1, MulAut.apply_inv_self]
  obtain ⟨m, hm⟩ := hx
  have hpow : (x * x) ^ (m + 1) = x := by
    rw [← sq, ← pow_mul, show 2 * (m + 1) = orderOf x + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have h2 := (Subgroup.pow_mem _ hsq (m + 1))
  rw [hpow, MulAction.mem_stabilizer_iff] at h2
  exact hxw h2

private theorem two_mul_card_le {S U : Subgroup W} (hSU : S ≤ U) (h : ∃ w ∈ U, w ∉ S) :
    2 * Nat.card S ≤ Nat.card U := by
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hSU
  obtain ⟨w, hwU, hwS⟩ := h
  have hlt : Nat.card S < Nat.card U :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hSU fun he => hwS (he ▸ hwU))
  have hS : 0 < Nat.card S := Nat.card_pos
  rcases k with _ | _ | k
  · rw [hk] at hlt; omega
  · rw [hk] at hlt; omega
  · rw [hk]; nlinarith

private theorem exists_isTransv_of_card (hW : ∀ w : W, w ^ 2 = 1) {t : MulAut W}
    (ht : t * t = 1) (ht1 : t ≠ 1)
    (hcard : Nat.card W ≤ 2 * Nat.card (fixV (Subgroup.zpowers t))) : ∃ u, IsTransv t u := by
  obtain ⟨u, h1, h2, hu, -, hstep⟩ :=
    exists_isTransvCentred (fun v => by rw [← sq]; exact hW v) ht ht1 hcard
  exact ⟨u, ⟨h2, h1, hu, hstep⟩⟩

omit [Finite W] in
private theorem exists_inverted {R : Subgroup (MulAut W)} {t r : MulAut W} (ht : t * t = 1)
    (htR : t ∈ Subgroup.normalizer (R : Set (MulAut W))) (hrR : r ∈ R) (hrt : r * t ≠ t * r) :
    ∃ x ∈ R, x ≠ 1 ∧ t * x * t⁻¹ = x⁻¹ ∧
      ∀ b : MulAut W, b * r = r * b → b * t = t * b → b * x = x * b := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  refine ⟨r⁻¹ * (t * r * t⁻¹), mul_mem (inv_mem hrR)
    ((Subgroup.mem_normalizer_iff.mp htR r).mp hrR), fun h => hrt ?_, ?_, ?_⟩
  · have h' := (inv_mul_eq_one.mp h).symm
    calc r * t = t * r * t⁻¹ * t := by rw [h']
      _ = t * r := by group
  · calc t * (r⁻¹ * (t * r * t⁻¹)) * t⁻¹ = t * r⁻¹ * t * r * (t * t) := by rw [htinv]; group
      _ = (r⁻¹ * (t * r * t⁻¹))⁻¹ := by
        rw [ht, mul_one]; simp only [mul_inv_rev, inv_inv, htinv, mul_assoc]
  · intro b hbr hbt
    have h1 : Commute b r := hbr
    have h2 : Commute b t := hbt
    exact h1.inv_right.mul_right ((h2.mul_right h1).mul_right h2.inv_right)

private theorem two_mul_card_fixV_le (hW : ∀ w : W, w ^ 2 = 1) {A B : Subgroup (MulAut W)}
    (hBA : B ≤ A) (hB : ∀ b ∈ B, b ^ 2 = 1) {t x : MulAut W} (htA : t ∈ A) (ht : t * t = 1)
    (htx : t * x * t⁻¹ = x⁻¹) (hx : Odd (orderOf x)) (hx1 : x ≠ 1)
    (hxB : ∀ b ∈ B, b * x = x * b) : 2 * Nat.card (fixV A) ≤ Nat.card (fixV B) := by
  have hxU : ∀ w ∈ fixV B, x w ∈ fixV B := fun w hw => mem_fixV.mpr fun b hb => by
    rw [← MulAut.mul_apply, hxB b hb, MulAut.mul_apply, mem_fixV.mp hw b hb]
  obtain ⟨w, hw, htw⟩ :=
    exists_moved_of_inverts ht htx hx hxU (exists_moved_fixV hW hB hx hxB hx1)
  exact two_mul_card_le (fun v hv => mem_fixV.mpr fun b hb => mem_fixV.mp hv b (hBA hb))
    ⟨w, hw, fun h => htw (mem_fixV.mp h t htA)⟩

theorem exists_isTransv_of_mem_pstarSet (hW : ∀ w : W, w ^ 2 = 1) {Y A R : Subgroup (MulAut W)}
    (hA : A ∈ PstarSet Y) (hR : Odd (Nat.card R))
    (hAR : A ≤ Subgroup.normalizer (R : Set (MulAut W)))
    (hnc : ¬ A ≤ Subgroup.centralizer (R : Set (MulAut W))) :
    ∃ (a : MulAut W) (u : W), A = Subgroup.zpowers a ∧ IsTransv a u := by
  obtain ⟨⟨hAY, -, hAe, hAoff⟩, hmin⟩ := hA
  obtain ⟨B, hBA, hBi, t, htA, r, hrR, hrB, hrt⟩ := exists_hyperplane_noncomm hAe hR hAR hnc
  have ht2 : t * t = 1 := by rw [← sq]; exact hAe.2 t htA
  have htB : t ∉ B := fun h => hrt (Subgroup.mem_centralizer_iff.mp hrB t h).symm
  obtain ⟨x, hxR, hx1, htx, hxc⟩ := exists_inverted ht2 (hAR htA) hrR hrt
  have hxodd : Odd (orderOf x) := by
    have h := hR.of_dvd_nat (orderOf_dvd_natCard (⟨x, hxR⟩ : R))
    rwa [Subgroup.orderOf_mk] at h
  have hlt := two_mul_card_fixV_le hW hBA (fun b hb => hAe.2 b (hBA hb)) htA ht2 htx hxodd hx1
    fun b hb => hxc b (Subgroup.mem_centralizer_iff.mp hrB b hb) (hAe.1 b (hBA hb) t htA)
  have hcardA := card_eq_two_mul_of_index hBA hBi
  have hoff := hAoff B hBA
  have heq : Nat.card A * Nat.card (fixV A) = Nat.card B * Nat.card (fixV B) := by
    refine le_antisymm ?_ hoff
    calc Nat.card A * Nat.card (fixV A) = Nat.card B * (2 * Nat.card (fixV A)) := by
          rw [hcardA]; ring
      _ ≤ Nat.card B * Nat.card (fixV B) := Nat.mul_le_mul_left _ hlt
  have hBbot : B = ⊥ := by
    by_contra hB
    have hBP : B ∈ Pset Y := ⟨hBA.trans hAY, hB,
      ⟨fun a ha b hb => hAe.1 a (hBA ha) b (hBA hb), fun a ha => hAe.2 a (hBA ha)⟩,
      fun B' hB' => (hAoff B' (hB'.trans hBA)).trans heq.le⟩
    exact htB (hmin B hBP hBA heq ▸ htA)
  subst hBbot
  have ht1 : t ≠ 1 := fun h => htB (h ▸ Subgroup.one_mem _)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAz : A = Subgroup.zpowers t := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr htA) ?_).symm
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [sq, ht2]) ht1, hcardA, Subgroup.card_bot]
  have hfixbot : fixV (⊥ : Subgroup (MulAut W)) = ⊤ :=
    eq_top_iff.mpr fun w _ => mem_fixV.mpr fun b hb => by rw [Subgroup.mem_bot.mp hb]; rfl
  rw [hfixbot, Subgroup.card_top, Subgroup.card_bot, one_mul, hcardA, Subgroup.card_bot,
    hAz] at hoff
  obtain ⟨u, hu⟩ := exists_isTransv_of_card hW ht2 ht1 hoff
  exact ⟨t, u, hAz, hu⟩

end CFSG.GroupTheory
