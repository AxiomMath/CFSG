module

public import CFSG.Open.Defs
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Quasithin.Background.Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43A6
import CFSG.LocalAnalysis.GL83PartI.I_28_3_S3
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3Rest
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43E9R
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43E9Core
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43Lift
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43W
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43Rank
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43Comm
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Lemma42
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6VIOrder3
import CFSG.LocalAnalysis.RankThreeTheoremC.WreathThompson
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6SylowProved
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6ActProved
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6Struct
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34f
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43A6Point
import CFSG.RankThree.PartOne.S9.Planes.Basic
import CFSG.RankThree.PartTwo.Sec11.Wreath
import CFSG.LocalAnalysis.AGLEmbedding.Signalizer
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltThreeRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ScalarTorus
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Survivor
public import CFSG.LocalAnalysis.AGLEmbeddingD2.ThreeStrong
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6Residues
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1End
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Abstract
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityKFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
import CFSG.Quasithin.Background.D14Normal
import CFSG.Quasithin.Background.D2
import CFSG.Quasithin.Background.D2Dihedral
import CFSG.Quasithin.Background.F1Amalgam
import CFSG.Quasithin.Background.F2Equiv
import CFSG.Quasithin.EmptyFaithful.QTKELocal
import CFSG.Quasithin.EmptyFaithful.S141Statements
import CFSG.Quasithin.EmptyFaithful.Skeleton
import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorNormalizer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Aux

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem sq_eq_inv {a : G} (h : a ^ 3 = 1) : a ^ 2 = a⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h)

noncomputable def cX (X : Subgroup G) (g : G) : ℕ :=
  Nat.card (X ⊓ centralizer ({g} : Set G) : Subgroup G)

theorem centralizer_inv_eq (a : G) : centralizer ({a⁻¹} : Set G) = centralizer ({a} : Set G) := by
  ext z
  simp only [mem_centralizer_singleton_iff]
  exact (Commute.inv_right_iff (a := z) (b := a))

theorem cX_sq (X : Subgroup G) {a : G} (h : a ^ 3 = 1) : cX X (a ^ 2) = cX X a := by
  rw [cX, cX, sq_eq_inv h, centralizer_inv_eq]

theorem burnside_cX {E X : Subgroup G} [Fintype E] (hEX : E ≤ normalizer (X : Set G)) :
    ∃ N : ℕ, ∑ g : E, cX X (g : G) = N * Nat.card E := by
  classical
  let φ : ↥E →* MulAut ↥X := X.normalizerMonoidHom.comp (Subgroup.inclusion hEX)
  let _ : MulAction ↥E ↥X := MulAction.compHom ↥X φ
  have hsmul : ∀ (k : ↥E) (x : ↥X), ((k • x : ↥X) : G) = (k : G) * (x : G) * (k : G)⁻¹ :=
    fun k x => Subgroup.normalizerMonoidHom_apply_apply_coe X (Subgroup.inclusion hEX k) x
  have hfix : ∀ k : ↥E, Nat.card (MulAction.fixedBy ↥X k) = cX X (k : G) := by
    intro k
    have hmem1 : ∀ x : ↥X, k • x = x → (x : G) ∈ Subgroup.centralizer ({(k : G)} : Set G) := by
      intro x hx
      have h1 := hsmul k x
      rw [hx] at h1
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (x : G) * (k : G) = ((k : G) * (x : G) * (k : G)⁻¹) * (k : G) := by rw [← h1]
        _ = (k : G) * (x : G) := by group
    have hmem2 : ∀ x : ↥X, (x : G) ∈ Subgroup.centralizer ({(k : G)} : Set G) → k • x = x := by
      intro x hx
      apply Subtype.ext
      rw [hsmul]
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp hx
      calc (k : G) * (x : G) * (k : G)⁻¹ = ((x : G) * (k : G)) * (k : G)⁻¹ := by rw [← h1]
        _ = (x : G) := by group
    exact Nat.card_congr
      { toFun := fun x => ⟨(x.1 : G), Subgroup.mem_inf.mpr ⟨x.1.2, hmem1 x.1 x.2⟩⟩
        invFun := fun y => ⟨⟨(y : G), (Subgroup.mem_inf.mp y.2).1⟩,
          hmem2 ⟨(y : G), (Subgroup.mem_inf.mp y.2).1⟩ (Subgroup.mem_inf.mp y.2).2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  have : ∀ g : ↥E, Fintype (MulAction.fixedBy ↥X g) := fun g => Fintype.ofFinite _
  have : Fintype (Quotient (MulAction.orbitRel ↥E ↥X)) := Fintype.ofFinite _
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (G := ↥E) (X := ↥X)
  refine ⟨Fintype.card (Quotient (MulAction.orbitRel ↥E ↥X)), ?_⟩
  have h1 : ∀ g : ↥E, Fintype.card (MulAction.fixedBy ↥X g) = cX X (g : G) := fun g => by
    rw [← Nat.card_eq_fintype_card, hfix g]
  simp only [h1] at hburn
  rw [hburn, Nat.card_eq_fintype_card]

theorem pair_bijective {a b : G} (hab : a * b = b * a) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hind : zpowers a ⊓ zpowers b = ⊥) :
    Function.Bijective (fun p : Fin 3 × Fin 3 =>
      (⟨a ^ (p.1 : ℕ) * b ^ (p.2 : ℕ), mul_mem (pow_mem (mem_sup_left (mem_zpowers a)) _)
        (pow_mem (mem_sup_right (mem_zpowers b)) _)⟩ : ↥(zpowers a ⊔ zpowers b))) := by
  have hao : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hbo : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hc : Commute a b := hab
  constructor
  · rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have h' : a ^ (i : ℕ) * b ^ (j : ℕ) = a ^ (i' : ℕ) * b ^ (j' : ℕ) := congrArg Subtype.val h
    have h'' : a ^ ((i : ℕ) : ℤ) * b ^ ((j : ℕ) : ℤ) = a ^ ((i' : ℕ) : ℤ) * b ^ ((j' : ℕ) : ℤ) := by
      simpa only [zpow_natCast] using h'
    have e1 := e9r_zpow_eq_of_mul_eq hind h''
    have h3 : b ^ ((j : ℕ) : ℤ) * a ^ ((i : ℕ) : ℤ) = b ^ ((j' : ℕ) : ℤ) * a ^ ((i' : ℕ) : ℤ) := by
      rw [← (hc.zpow_zpow ((i : ℕ) : ℤ) ((j : ℕ) : ℤ)).eq, ← (hc.zpow_zpow ((i' : ℕ) : ℤ)
        ((j' : ℕ) : ℤ)).eq]
      exact h''
    have e2 := e9r_zpow_eq_of_mul_eq (by rw [inf_comm]; exact hind) h3
    have d1 := a6vi_zpow_eq_of_three hao e1
    have d2 := a6vi_zpow_eq_of_three hbo e2
    have hi := i.2
    have hi' := i'.2
    have hj := j.2
    have hj' := j'.2
    have : (i : ℕ) = i' := by omega
    have : (j : ℕ) = j' := by omega
    exact Prod.ext (Fin.ext (by assumption)) (Fin.ext (by assumption))
  · rintro ⟨g, hg⟩
    have hTZ : ∀ t ∈ zpowers a, ∀ c ∈ zpowers b, t * c = c * t := by
      intro t ht c hc'
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp ht
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hc'
      exact (hc.zpow_zpow m n).eq
    obtain ⟨t, ht, c, hc', rfl⟩ := u3l42_decomp hTZ hg
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp ht
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hc'
    have ha3' : a ^ (3 : ℤ) = 1 := by
      rw [show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, ha3]
    have hb3' : b ^ (3 : ℤ) = 1 := by
      rw [show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hb3]
    have hm : a ^ m = a ^ ((m % 3).toNat) := by
      rw [zpow_eq_zpow_emod m ha3', ← zpow_natCast,
        Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
    have hn : b ^ n = b ^ ((n % 3).toNat) := by
      rw [zpow_eq_zpow_emod n hb3', ← zpow_natCast,
        Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
    refine ⟨(⟨(m % 3).toNat, by omega⟩, ⟨(n % 3).toNat, by omega⟩), ?_⟩
    apply Subtype.ext
    simp only
    rw [hm, hn]

theorem centralizer_one_inf (X : Subgroup G) : cX X 1 = Nat.card X := by
  rw [cX]
  have : X ⊓ centralizer ({(1 : G)} : Set G) = X :=
    inf_eq_left.mpr (fun x _ => Subgroup.mem_centralizer_singleton_iff.mpr (by simp))
  rw [this]

theorem fourth_line_centralizes {X : Subgroup G} {a b : G}
    (hX : IsElemAbelian 2 X) (haX : a ∈ normalizer (X : Set G))
    (hbX : b ∈ normalizer (X : Set G)) (hab : a * b = b * a) (ha3 : a ^ 3 = 1)
    (hb3 : b ^ 3 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hind : zpowers a ⊓ zpowers b = ⊥)
    (h₁ : Nat.card (⁅X, zpowers a⁆ : Subgroup G) = 4)
    (h₂ : Nat.card (⁅X, zpowers b⁆ : Subgroup G) = 4)
    (h₃ : Nat.card (⁅X, zpowers (a * b)⁆ : Subgroup G) = 4) :
    ∀ x ∈ X, (a * b ^ 2) * x = x * (a * b ^ 2) := by
  classical
  have hc : Commute a b := hab
  set d : G := a * b ^ 2 with hd
  have hab3 : (a * b) ^ 3 = 1 := by rw [hc.mul_pow, ha3, hb3, one_mul]
  have hd3 : d ^ 3 = 1 := by
    rw [hd, (hc.pow_right 2).mul_pow, ha3, ← pow_mul, mul_comm 2 3, pow_mul, hb3, one_pow, one_mul]
  have hdX : d ∈ normalizer (X : Set G) := mul_mem haX (pow_mem hbX 2)
  have habX : a * b ∈ normalizer (X : Set G) := mul_mem haX hbX
  have hXp : IsPGroup 2 ↥X := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hX.2 _ x.2)⟩
  obtain ⟨n, hn⟩ := hXp.exists_card_eq
  have hXcard : Nat.card X = 2 ^ n := hn
  have hca : 4 * cX X a = Nat.card X := by
    have := GL83.I28_3S3.card_commutator_mul_card_centralizer hX haX ha3
    rw [h₁] at this; exact this
  have hcb : 4 * cX X b = Nat.card X := by
    have := GL83.I28_3S3.card_commutator_mul_card_centralizer hX hbX hb3
    rw [h₂] at this; exact this
  have hcab : 4 * cX X (a * b) = Nat.card X := by
    have := GL83.I28_3S3.card_commutator_mul_card_centralizer hX habX hab3
    rw [h₃] at this; exact this
  set r : ℕ := Nat.card (⁅X, zpowers d⁆ : Subgroup G) with hr
  have hrd : r * cX X d = Nat.card X :=
    GL83.I28_3S3.card_commutator_mul_card_centralizer hX hdX hd3
  have hr16 : r ≤ 16 := by
    have hia : (centralizer ({a} : Set G)).relIndex X = 4 := by
      have := Subgroup.relIndex_mul_card (H := centralizer ({a} : Set G)) (K := X)
      rw [inf_comm] at this
      change _ * cX X a = _ at this
      have hpos : 0 < cX X a := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_right hpos (this.trans hca.symm)
    have hib : (centralizer ({b} : Set G)).relIndex X = 4 := by
      have := Subgroup.relIndex_mul_card (H := centralizer ({b} : Set G)) (K := X)
      rw [inf_comm] at this
      change _ * cX X b = _ at this
      have hpos : 0 < cX X b := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_right hpos (this.trans hcb.symm)
    have hle : centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G) ≤
        centralizer ({d} : Set G) := by
      intro z hz
      obtain ⟨hza, hzb⟩ := Subgroup.mem_inf.mp hz
      rw [mem_centralizer_singleton_iff] at hza hzb ⊢
      have h1 : Commute z a := hza
      have h2 : Commute z b := hzb
      exact ((h1.mul_right (h2.pow_right 2))).eq
    have hne : ((centralizer ({a} : Set G)) ⊓ centralizer ({b} : Set G)).relIndex X ≠ 0 := by
      intro h0
      have := Subgroup.relIndex_mul_card
        (H := (centralizer ({a} : Set G)) ⊓ centralizer ({b} : Set G)) (K := X)
      rw [h0, zero_mul] at this
      exact (Nat.card_pos (α := X)).ne' this.symm
    have h3 := Subgroup.relIndex_le_of_le_left hle hne
    have h4 := Subgroup.relIndex_inf_le (H := centralizer ({a} : Set G))
      (K := centralizer ({b} : Set G)) (L := X)
    have hid : (centralizer ({d} : Set G)).relIndex X = r := by
      have := Subgroup.relIndex_mul_card (H := centralizer ({d} : Set G)) (K := X)
      rw [inf_comm] at this
      change _ * cX X d = _ at this
      have hpos : 0 < cX X d := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_right hpos (this.trans hrd.symm)
    rw [hid] at h3
    rw [hia, hib] at h4
    omega
  set E : Subgroup G := zpowers a ⊔ zpowers b with hE
  have hEX : E ≤ normalizer (X : Set G) := sup_le (zpowers_le.mpr haX) (zpowers_le.mpr hbX)
  haveI : Fintype E := Fintype.ofFinite _
  obtain ⟨N, hN⟩ := burnside_cX hEX
  have hψ := pair_bijective hab ha3 hb3 ha1 hb1 hind
  have hE9 : Nat.card E = 9 := by
    have := Nat.card_eq_of_bijective _ hψ
    rw [← this]
    simp
  have hsum := Fintype.sum_bijective _ hψ
    (fun p : Fin 3 × Fin 3 => cX X (a ^ (p.1 : ℕ) * b ^ (p.2 : ℕ)))
    (fun g : E => cX X (g : G)) (fun p => rfl)
  rw [hN, hE9, Fintype.sum_prod_type] at hsum
  simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one,
    one_mul, mul_one] at hsum
  have hsq_ab : a ^ 2 * b ^ 2 = (a * b) ^ 2 := (hc.mul_pow 2).symm
  have hd2 : d ^ 2 = a ^ 2 * b := by
    rw [hd, (hc.pow_right 2).mul_pow, ← pow_mul, show 2 * 2 = 1 + 3 by norm_num, pow_add, hb3,
      mul_one, pow_one]
  have e1 : cX X (b ^ 2) = cX X b := cX_sq X hb3
  have e2 : cX X (a ^ 2) = cX X a := cX_sq X ha3
  have e3 : cX X (a ^ 2 * b ^ 2) = cX X (a * b) := by rw [hsq_ab]; exact cX_sq X hab3
  have e4 : cX X (a ^ 2 * b) = cX X d := by rw [← hd2]; exact cX_sq X hd3
  rw [e1, e2, e3, e4, centralizer_one_inf] at hsum
  rw [← hd] at hsum
  have hlin : Nat.card X + 2 * cX X a + 2 * cX X b + 2 * cX X (a * b) + 2 * cX X d = N * 9 := by
    omega
  clear hsum
  have hdvd : r ∣ 2 ^ n := ⟨cX X d, by rw [← hXcard, hrd]⟩
  have hcdvd : cX X d ∣ 2 ^ n := ⟨r, by rw [← hXcard, ← hrd, mul_comm]⟩
  have h3c : ¬ 3 ∣ cX X d := fun h3 => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three (h3.trans hcdvd)
    omega
  obtain ⟨m, hm, hrm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hm4 : m ≤ 4 := by
    by_contra hcon
    have : 2 ^ 5 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hr1 : r = 1 := by
    interval_cases m
    · simpa using hrm
    all_goals
      simp at hrm
      rw [hrm] at hrd
      omega
  have hcard1 : Nat.card (⁅X, zpowers d⁆ : Subgroup G) = 1 := hr1
  have hbot : (⁅X, zpowers d⁆ : Subgroup G) = ⊥ := Subgroup.eq_bot_of_card_eq _ hcard1
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
  intro x hx
  exact (mem_centralizer_iff.mp (hbot hx) d (mem_zpowers d))

section Monomial

variable {H : Type*} [Group H]

theorem monomial_pair {e₂ e₃ u v : H} (c23 : Commute e₂ e₃)
    (h23 : zpowers e₂ ⊓ zpowers e₃ = ⊥) (he₂1 : e₂ ≠ 1) (he₃1 : e₃ ≠ 1)
    (hu : u ∈ zpowers e₂ ∨ u ∈ zpowers e₃) (hv : v ∈ zpowers e₂ ∨ v ∈ zpowers e₃)
    (huv : u * v = e₂ * e₃) : (u = e₂ ∧ v = e₃) ∨ (u = e₃ ∧ v = e₂) := by
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exfalso
    have h1 : e₂⁻¹ * (u * v) ∈ zpowers e₂ :=
      mul_mem (inv_mem (mem_zpowers e₂)) (mul_mem hu hv)
    rw [huv, inv_mul_cancel_left] at h1
    have h2 : e₃ ∈ zpowers e₂ ⊓ zpowers e₃ := ⟨h1, mem_zpowers e₃⟩
    rw [h23] at h2
    exact he₃1 (mem_bot.mp h2)
  · left
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hu
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hv
    have h1 : e₂ ^ i * e₃ ^ j = e₂ ^ (1 : ℤ) * e₃ ^ (1 : ℤ) := by simpa using huv
    have h2 := e9r_zpow_eq_of_mul_eq h23 h1
    have h3 : e₃ ^ j * e₂ ^ i = e₃ ^ (1 : ℤ) * e₂ ^ (1 : ℤ) := by
      rw [← (c23.zpow_zpow i j).eq, ← (c23.zpow_zpow 1 1).eq]
      exact h1
    have h4 := e9r_zpow_eq_of_mul_eq (by rw [inf_comm]; exact h23) h3
    exact ⟨by simpa using h2, by simpa using h4⟩
  · right
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hu
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hv
    have h1 : e₃ ^ j * e₂ ^ i = e₃ ^ (1 : ℤ) * e₂ ^ (1 : ℤ) := by
      rw [huv]
      simpa using c23.eq
    have h2 := e9r_zpow_eq_of_mul_eq (by rw [inf_comm]; exact h23) h1
    have h3 : e₂ ^ i * e₃ ^ j = e₂ ^ (1 : ℤ) * e₃ ^ (1 : ℤ) := by
      rw [(c23.zpow_zpow i j).eq, (c23.zpow_zpow 1 1).eq]
      exact h1
    have h4 := e9r_zpow_eq_of_mul_eq h23 h3
    exact ⟨by simpa using h2, by simpa using h4⟩
  · exfalso
    have h1 : (u * v) * e₃⁻¹ ∈ zpowers e₃ :=
      mul_mem (mul_mem hu hv) (inv_mem (mem_zpowers e₃))
    rw [huv, mul_inv_cancel_right] at h1
    have h2 : e₂ ∈ zpowers e₂ ⊓ zpowers e₃ := ⟨mem_zpowers e₂, h1⟩
    rw [h23] at h2
    exact he₂1 (mem_bot.mp h2)

theorem monomial_conj {e₁ e₂ e₃ y : H} (c23 : Commute e₂ e₃)
    (h23 : zpowers e₂ ⊓ zpowers e₃ = ⊥) (hT : (zpowers e₂ ⊔ zpowers e₃) ⊓ zpowers e₁ = ⊥)
    (he₂1 : e₂ ≠ 1) (he₃1 : e₃ ≠ 1)
    (hy1 : y * e₁ * y⁻¹ = e₁) (hy23 : y * (e₂ * e₃) * y⁻¹ = e₂ * e₃)
    (h2 : y * e₂ * y⁻¹ ∈ zpowers e₁ ∨ y * e₂ * y⁻¹ ∈ zpowers e₂ ∨ y * e₂ * y⁻¹ ∈ zpowers e₃)
    (h3 : y * e₃ * y⁻¹ ∈ zpowers e₁ ∨ y * e₃ * y⁻¹ ∈ zpowers e₂ ∨ y * e₃ * y⁻¹ ∈ zpowers e₃) :
    (y * e₂ * y⁻¹ = e₂ ∧ y * e₃ * y⁻¹ = e₃) ∨ (y * e₂ * y⁻¹ = e₃ ∧ y * e₃ * y⁻¹ = e₂) := by
  have hy1' : y⁻¹ * e₁ * y = e₁ := by
    calc y⁻¹ * e₁ * y = y⁻¹ * (y * e₁ * y⁻¹) * y := by rw [hy1]
      _ = e₁ := by group
  have hnot : ∀ w : H, w ∈ zpowers e₂ ⊔ zpowers e₃ → y * w * y⁻¹ ∈ zpowers e₁ → w = 1 := by
    intro w hw hwy
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hwy
    have hw' : w = e₁ ^ k := by
      calc w = y⁻¹ * (y * w * y⁻¹) * y := by group
        _ = y⁻¹ * e₁ ^ k * y := by rw [hk]
        _ = (y⁻¹ * e₁ * y) ^ k := by
          have := conj_zpow (i := k) (a := y⁻¹) (b := e₁)
          rw [inv_inv] at this
          exact this.symm
        _ = e₁ ^ k := by rw [hy1']
    have hmem : w ∈ (zpowers e₂ ⊔ zpowers e₃) ⊓ zpowers e₁ :=
      ⟨hw, by rw [hw']; exact zpow_mem_zpowers e₁ k⟩
    rw [hT] at hmem
    exact mem_bot.mp hmem
  have h2' : y * e₂ * y⁻¹ ∈ zpowers e₂ ∨ y * e₂ * y⁻¹ ∈ zpowers e₃ := by
    rcases h2 with h | h | h
    · exact absurd (hnot e₂ (mem_sup_left (mem_zpowers e₂)) h) he₂1
    · exact Or.inl h
    · exact Or.inr h
  have h3' : y * e₃ * y⁻¹ ∈ zpowers e₂ ∨ y * e₃ * y⁻¹ ∈ zpowers e₃ := by
    rcases h3 with h | h | h
    · exact absurd (hnot e₃ (mem_sup_right (mem_zpowers e₃)) h) he₃1
    · exact Or.inl h
    · exact Or.inr h
  have huv : (y * e₂ * y⁻¹) * (y * e₃ * y⁻¹) = e₂ * e₃ := by
    rw [← hy23]; group
  exact monomial_pair c23 h23 he₂1 he₃1 h2' h3' huv

end Monomial

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Aux

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Aux

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin
  CFSG.Quasithin.F53Push CFSG.ABGLocalTools Subgroup
open scoped Pointwise

section Bar

variable {G : Type} [Group G] (M O : Subgroup G) [(O.subgroupOf M).Normal]

open Classical in
noncomputable def bar (g : G) : M ⧸ O.subgroupOf M :=
  if h : g ∈ M then QuotientGroup.mk ⟨g, h⟩ else 1

variable {M O}

theorem bar_mul {g h : G} (hg : g ∈ M) (hh : h ∈ M) :
    bar M O (g * h) = bar M O g * bar M O h := by
  unfold bar
  rw [dif_pos hg, dif_pos hh, dif_pos (M.mul_mem hg hh)]
  rfl

theorem bar_one : bar M O (1 : G) = 1 := by
  unfold bar
  rw [dif_pos M.one_mem]
  rfl

theorem bar_inv {g : G} (hg : g ∈ M) : bar M O g⁻¹ = (bar M O g)⁻¹ := by
  unfold bar
  rw [dif_pos hg, dif_pos (M.inv_mem hg)]
  rfl

theorem bar_zpow {g : G} (hg : g ∈ M) (n : ℤ) : bar M O (g ^ n) = (bar M O g) ^ n := by
  unfold bar
  rw [dif_pos hg, dif_pos (M.zpow_mem hg n)]
  rfl

theorem bar_pow {g : G} (hg : g ∈ M) (n : ℕ) : bar M O (g ^ n) = (bar M O g) ^ n := by
  have := bar_zpow (O := O) hg (n : ℤ)
  simpa only [zpow_natCast] using this

theorem bar_eq_one_iff {g : G} (hg : g ∈ M) : bar M O g = 1 ↔ g ∈ O := by
  unfold bar
  rw [dif_pos hg, QuotientGroup.eq_one_iff, mem_subgroupOf]

theorem bar_eq_iff {g h : G} (hg : g ∈ M) (hh : h ∈ M) :
    bar M O g = bar M O h ↔ g⁻¹ * h ∈ O := by
  rw [← inv_mul_eq_one, ← bar_inv hg, ← bar_mul (M.inv_mem hg) hh, bar_eq_one_iff
    (M.mul_mem (M.inv_mem hg) hh)]

theorem bar_conj {y g : G} (hy : y ∈ M) (hg : g ∈ M) :
    bar M O (y * g * y⁻¹) = bar M O y * bar M O g * (bar M O y)⁻¹ := by
  rw [bar_mul (M.mul_mem hy hg) (M.inv_mem hy), bar_mul hy hg, bar_inv hy]

theorem comm_mem_of_commute {y k : G} (hy : y ∈ M) (hk : k ∈ M)
    (hc : Commute (bar M O y) (bar M O k)) : y * k * y⁻¹ * k⁻¹ ∈ O := by
  rw [← bar_eq_one_iff (M.mul_mem (M.mul_mem (M.mul_mem hy hk) (M.inv_mem hy)) (M.inv_mem hk)),
    bar_mul (M.mul_mem (M.mul_mem hy hk) (M.inv_mem hy)) (M.inv_mem hk),
    bar_mul (M.mul_mem hy hk) (M.inv_mem hy), bar_mul hy hk, bar_inv hy, bar_inv hk]
  calc bar M O y * bar M O k * (bar M O y)⁻¹ * (bar M O k)⁻¹
      = bar M O k * bar M O y * (bar M O y)⁻¹ * (bar M O k)⁻¹ := by rw [hc.eq]
    _ = 1 := by group

theorem bar_mem_zpowers {e q : G} (he : e ∈ M) (hq : q ∈ zpowers e) :
    bar M O q ∈ zpowers (bar M O e) := by
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hq
  rw [bar_zpow he m]
  exact zpow_mem_zpowers _ m

end Bar

section BN

variable {G : Type} [Group G] [Finite G]

theorem bn_card_four {M O U₂ Y : Subgroup G} (hOM : O ≤ M) (hMO : M ≤ normalizer (O : Set G))
    (hO3 : ¬ 3 ∣ Nat.card O) (hO₂ : pCoreOf 2 M ≤ O) (hF : CharTwo M)
    (hY2 : IsPGroup 2 Y) (hYM : Y ≤ M) (hYO : IsSylowOf 2 (Y ⊓ O) O)
    (hU₂M : U₂ ≤ M) (hU₂card : Nat.card U₂ = 3) (hU₂3 : ∀ k ∈ U₂, k ^ 3 = 1)
    (hYU₂ : Y ≤ normalizer ((U₂ ⊔ O : Subgroup G) : Set G))
    (hnt : ∃ y ∈ Y, ∃ b ∈ U₂ ⊔ O, y * b * y⁻¹ * b⁻¹ ∉ O)
    (hrank : ∀ C : Subgroup G, C ≤ Y → C ≠ ⊥ → (C.subgroupOf Y).Characteristic →
      ¬ U₂ ≤ (normalizer (C : Set G) ⊓ M) ⊔ O) :
    Nat.card (⁅omegaOneCenterOf (pCoreOf 2 M), U₂⁆ : Subgroup G) = 4 := by
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYO' : Y ≤ normalizer (O : Set G) := hYM.trans hMO
  have hO₂Y : pCoreOf 2 M ≤ Y ⊓ O :=
    e9_le_of_normal hO₂
      (hOM.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M))
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M) hYO
  have hU₂O : U₂ ≤ normalizer (O : Set G) := hU₂M.trans hMO
  have hB₂O : (U₂ ⊔ O : Subgroup G) ≤ normalizer (O : Set G) :=
    sup_le hU₂O Subgroup.le_normalizer
  have hB₂M : (U₂ ⊔ O : Subgroup G) ≤ M := sup_le hU₂M hOM
  obtain ⟨T₂, hST₂, hT₂B, hYT₂, hT₂O, hT₂sup⟩ := l43_exists_lift (O := O) (B := U₂ ⊔ O)
    (Y := Y) le_sup_right hB₂O hYU₂ hYO' hY2 hO3
    (fun b hb => e9_pow_three_mem_sup hU₂O hU₂3 hb) hYO
  have hT₂M : T₂ ≤ M := hT₂B.trans hB₂M
  have hT₂N : T₂ ≤ normalizer (O : Set G) := hT₂B.trans hB₂O
  have hT₂S : T₂ ≤ normalizer ((Y ⊓ O : Subgroup G) : Set G) := by
    have := e9_le_normalizer_inf (A := T₂) (C := O) Subgroup.le_normalizer hT₂N
    rwa [hT₂O] at this
  have hYS : Y ≤ normalizer ((Y ⊓ O : Subgroup G) : Set G) :=
    e9_le_normalizer_inf Subgroup.le_normalizer hYO'
  have hU₂O' : U₂ ⊓ O = ⊥ := e9_inf_eq_bot hU₂3 hO3
  have hcard1 := e9_card_sup_mul_card_inf hU₂O
  rw [hU₂O', Subgroup.card_bot, hU₂card, mul_one] at hcard1
  have hcard2 := e9_card_sup_mul_card_inf hT₂N
  rw [hT₂sup, hT₂O, hcard1] at hcard2
  have hOpos : 0 < Nat.card O := Nat.card_pos
  have hT₃ : Nat.card T₂ = 3 * Nat.card (Y ⊓ O : Subgroup G) := by
    apply Nat.eq_of_mul_eq_mul_right hOpos
    rw [← hcard2]
    ring
  have hnt₂ : ∃ y ∈ Y, ∃ t ∈ T₂, y * t * y⁻¹ * t⁻¹ ∉ Y ⊓ O := by
    obtain ⟨y₁, hy₁, b₁, hb₁, hnt'⟩ := hnt
    have hb₁' : b₁ ∈ (T₂ : Set G) * (O : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right T₂ O hT₂N]
      rw [hT₂sup]
      exact hb₁
    obtain ⟨t, ht, o, ho, hto⟩ := hb₁'
    have hb₁eq : b₁ = t * o := hto.symm
    refine ⟨y₁, hy₁, t, ht, fun hmem => hnt' ?_⟩
    have hc : y₁ * t * y₁⁻¹ * t⁻¹ ∈ O := hmem.2
    have e : y₁ * b₁ * y₁⁻¹ * b₁⁻¹ =
        (y₁ * t * y₁⁻¹ * t⁻¹) * (t * (y₁ * o * y₁⁻¹ * o⁻¹) * t⁻¹) := by
      rw [hb₁eq]
      group
    rw [e]
    have hyo : y₁ * o * y₁⁻¹ * o⁻¹ ∈ O :=
      O.mul_mem ((mem_normalizer_iff.mp (hYO' hy₁) o).mp ho) (O.inv_mem ho)
    exact O.mul_mem hc ((mem_normalizer_iff.mp (hT₂N ht) _).mp hyo)
  obtain ⟨hWsyl, hWcard, hWq⟩ := l43_wStructure hY2 inf_le_left hST₂ hT₂S hYS hYT₂ hT₃ hnt₂
  have hWM : T₂ ⊔ Y ≤ M := sup_le hT₂M hYM
  have hO₂W : pCoreOf 2 M ≤ T₂ ⊔ Y := hO₂Y.trans (inf_le_left.trans le_sup_right)
  have hFW : CharTwo (T₂ ⊔ Y) := charTwo_of_core_le hF hO₂W hWM
  have hO₂' : pCoreOf 2 M ≤ pCoreOf 2 (T₂ ⊔ Y) :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 (pCoreOf 2 M) (T₂ ⊔ Y) hO₂W
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hO₂W).mpr
        (hWM.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M)))
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
  have hnc : NoCharNormal Y (T₂ ⊔ Y) := by
    intro C hCY hC1 hCch hWC
    refine hrank C hCY hC1 hCch ?_
    have hT₂H : T₂ ≤ normalizer (C : Set G) ⊓ M := le_inf (le_sup_left.trans hWC) hT₂M
    calc U₂ ≤ T₂ ⊔ O := by rw [hT₂sup]; exact le_sup_left
      _ ≤ _ := sup_le_sup_right hT₂H O
  have h3T₂ : 3 ∣ Nat.card T₂ := ⟨Nat.card (Y ⊓ O : Subgroup G), hT₃⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 h3T₂
  have huG : orderOf (u : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hu
  have hu3 : (u : G) ^ 3 = 1 := by rw [← huG]; exact pow_orderOf_eq_one _
  have hu1 : (u : G) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at huG
    omega
  have huW : (u : G) ∈ T₂ ⊔ Y := mem_sup_left u.2
  have h4 := GL83.baumann_niles_s3 hWsyl hFW hWq hnc huW hu3 hu1
  have hX := l43_card_commutator_omegaOneCenter hWM huW hu3 hu1 hF hO₂' h4
  have hXN : M ≤ normalizer ((omegaOneCenterOf (pCoreOf 2 M) : Subgroup G) : Set G) :=
    l43_normalizer_omegaOneCenter
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M)
  have huB₂ : (u : G) ∈ U₂ ⊔ O := hT₂B u.2
  obtain ⟨k, hk, hkw⟩ := e9r_exists_conj_zpowers_eq hU₂O hO3 hU₂card huB₂ hu3 hu1
  have := l43_card_commutator_conj hXN (m := k⁻¹) (u := (u : G)) (M.inv_mem (hB₂M hk))
  rw [inv_inv, hkw] at this
  exact this.trans hX

end BN

section Basics

variable {G : Type} [Group G]

theorem isElemAbelian_zpowers {e : G} (he : e ^ 3 = 1) : IsElemAbelian 3 (zpowers e) := by
  refine ⟨IsMulCommutative.of_setLike_mul_comm fun a ha b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
    exact ((Commute.refl e).zpow_zpow i j).eq
  · obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he, one_zpow]

theorem isElemAbelian_sup {A B : Subgroup G} (hA : IsElemAbelian 3 A) (hB : IsElemAbelian 3 B)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : IsElemAbelian 3 (A ⊔ B) := by
  have hdec : ∀ g ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, g = a * b := fun g hg => u3l42_decomp hAB hg
  refine ⟨IsMulCommutative.of_setLike_mul_comm fun u hu v hv => ?_, fun g hg => ?_⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := hdec u hu
    obtain ⟨a', ha', b', hb', rfl⟩ := hdec v hv
    have hAc := hA.1
    have hBc := hB.1
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [hAB a' ha' b hb]
      _ = (a * a') * (b * b') := by group
      _ = (a' * a) * (b' * b) := by
        rw [setLike_mul_comm ha ha', setLike_mul_comm hb hb']
      _ = a' * (a * b') * b := by group
      _ = a' * (b' * a) * b := by rw [hAB a ha b' hb']
      _ = a' * b' * (a * b) := by group
  · obtain ⟨a, ha, b, hb, rfl⟩ := hdec g hg
    rw [(show Commute a b from hAB a ha b hb).mul_pow, hA.2 a ha, hB.2 b hb, one_mul]

end Basics

section Frame

variable {G : Type} [Group G] [Finite G]

abbrev Qf (x e₂ e₃ : G) : Subgroup G := zpowers x ⊔ (zpowers e₂ ⊔ zpowers e₃)

structure VITriple (x e₂ e₃ : G) : Prop where
  x_pow : x ^ 3 = 1
  e₂_pow : e₂ ^ 3 = 1
  e₃_pow : e₃ ^ 3 = 1
  x_ne : x ≠ 1
  e₂_ne : e₂ ≠ 1
  e₃_ne : e₃ ≠ 1
  comm_x₂ : x * e₂ = e₂ * x
  comm_x₃ : x * e₃ = e₃ * x
  comm_23 : e₂ * e₃ = e₃ * e₂
  ind_23 : zpowers e₂ ⊓ zpowers e₃ = ⊥
  ind_x : (zpowers e₂ ⊔ zpowers e₃) ⊓ zpowers x = ⊥

structure A6VIFrame (M O : Subgroup G) (x e₂ e₃ t ρ : G) (s : ℤ) : Prop extends
    VITriple x e₂ e₃ where
  O_le : O ≤ M
  O_norm : M ≤ normalizer (O : Set G)
  O_cop : ¬ 3 ∣ Nat.card O
  O₂_le : pCoreOf 2 M ≤ O
  O₂_ne : pCoreOf 2 M ≠ ⊥
  charTwo : CharTwo M
  D1 : ∀ Y₀ : Subgroup G, Y₀ ≠ ⊥ → IsPGroup 2 Y₀ →
    3 ≤ CFSG.Open.pRank 3 (normalizer (Y₀ : Set G) ⊓ M) → normalizer (Y₀ : Set G) ≤ M
  x_mem : x ∈ M
  e₂_mem : e₂ ∈ M
  e₃_mem : e₃ ∈ M
  t_mem : t ∈ M
  t_x : t * x * t⁻¹ = e₂
  t_e₂ : t * e₂ * t⁻¹ = e₃
  t_e₃ : t * e₃ * t⁻¹ = x
  ρ_mem : ρ ∈ M
  ρ_x : ρ * x * ρ⁻¹ = x
  ρ_e₂ : ρ * e₂ * ρ⁻¹ = e₃ ^ s
  ρ_e₃ : ρ * e₃ * ρ⁻¹ = e₂ ^ (-s)
  s_cases : s = 1 ∨ s = -1
  lines : ∀ g : G, g * x * g⁻¹ ∈ Qf x e₂ e₃ →
    g * x * g⁻¹ ∈ zpowers x ∨ g * x * g⁻¹ ∈ zpowers e₂ ∨ g * x * g⁻¹ ∈ zpowers e₃

namespace VITriple

variable {x e₂ e₃ : G} (h : VITriple x e₂ e₃)

include h

theorem T_le_cent : zpowers e₂ ⊔ zpowers e₃ ≤ centralizer ({x} : Set G) :=
  sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr h.comm_x₂.symm))
    (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr h.comm_x₃.symm))

theorem x_T : ∀ a ∈ zpowers x, ∀ b ∈ zpowers e₂ ⊔ zpowers e₃, a * b = b * a := by
  intro a ha b hb
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
  exact (Commute.zpow_left (mem_centralizer_singleton_iff.mp (h.T_le_cent hb)).symm i).eq

theorem T_comm_gen : ∀ a ∈ zpowers e₂, ∀ b ∈ zpowers e₃, a * b = b * a := by
  intro a ha b hb
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
  exact (((show Commute e₂ e₃ from h.comm_23).zpow_zpow i j)).eq

theorem T_el : IsElemAbelian 3 (zpowers e₂ ⊔ zpowers e₃) :=
  isElemAbelian_sup (isElemAbelian_zpowers h.e₂_pow) (isElemAbelian_zpowers h.e₃_pow) h.T_comm_gen

theorem Q_el : IsElemAbelian 3 (Qf x e₂ e₃) :=
  isElemAbelian_sup (isElemAbelian_zpowers h.x_pow) h.T_el h.x_T

theorem Q_comm : ∀ a ∈ Qf x e₂ e₃, ∀ b ∈ Qf x e₂ e₃, a * b = b * a := fun a ha b hb => by
  have := h.Q_el.1
  exact setLike_mul_comm ha hb

theorem Q_exp : ∀ q ∈ Qf x e₂ e₃, q ^ 3 = 1 := h.Q_el.2

theorem x_nmem_T : x ∉ zpowers e₂ ⊔ zpowers e₃ := fun hx => by
  have : x ∈ (zpowers e₂ ⊔ zpowers e₃) ⊓ zpowers x := ⟨hx, mem_zpowers x⟩
  rw [h.ind_x] at this
  exact h.x_ne (mem_bot.mp this)

theorem e₃_nmem : e₃ ∉ zpowers e₂ := fun he => by
  have : e₃ ∈ zpowers e₂ ⊓ zpowers e₃ := ⟨he, mem_zpowers e₃⟩
  rw [h.ind_23] at this
  exact h.e₃_ne (mem_bot.mp this)

theorem T_card : Nat.card (zpowers e₂ ⊔ zpowers e₃ : Subgroup G) = 9 := by
  have hcx : Nat.card (zpowers e₂) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime h.e₂_pow h.e₂_ne]
  have hcm : ∀ e ∈ zpowers e₂, e * e₃ = e₃ * e := fun e he =>
    h.T_comm_gen e he e₃ (mem_zpowers e₃)
  rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three (zpowers e₂) h.e₃_pow
    h.e₃_nmem hcm, hcx]

theorem Q_card : Nat.card (Qf x e₂ e₃) = 27 := by
  have hcm : ∀ e ∈ zpowers e₂ ⊔ zpowers e₃, e * x = x * e := fun e he =>
    (h.x_T x (mem_zpowers x) e he).symm
  have hQ : Qf x e₂ e₃ = (zpowers e₂ ⊔ zpowers e₃) ⊔ zpowers x := sup_comm _ _
  rw [hQ, CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three
    (zpowers e₂ ⊔ zpowers e₃) h.x_pow h.x_nmem_T hcm, h.T_card]

end VITriple

namespace A6VIFrame

variable {M O : Subgroup G} {x e₂ e₃ t ρ : G} {s : ℤ} (h : A6VIFrame M O x e₂ e₃ t ρ s)

include h

theorem Q_le_M : Qf x e₂ e₃ ≤ M :=
  sup_le (zpowers_le.mpr h.x_mem) (sup_le (zpowers_le.mpr h.e₂_mem) (zpowers_le.mpr h.e₃_mem))

theorem Q_le_N : Qf x e₂ e₃ ≤ normalizer (O : Set G) := h.Q_le_M.trans h.O_norm

theorem Q_inf_O : Qf x e₂ e₃ ⊓ O = ⊥ := e9_inf_eq_bot h.Q_exp h.O_cop

end A6VIFrame

end Frame

section Lines

variable {G : Type} [Group G] [Finite G]

theorem zpowers_eq_of_mem {e z : G} (he3 : e ^ 3 = 1) (he1 : e ≠ 1) (hz : z ∈ zpowers e)
    (hz1 : z ≠ 1) : zpowers z = zpowers e := by
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hz
  have hz3 : (e ^ m) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he3, one_zpow]
  have hzo : orderOf (e ^ m) = 3 := orderOf_eq_prime hz3 hz1
  have heo : orderOf e = 3 := orderOf_eq_prime he3 he1
  refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hz) ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, hzo, heo]

end Lines

section CentAux

variable {G : Type} [Group G]

theorem conj_mem_centralizer_aux {X : Subgroup G} {m z : G} (hm : m ∈ normalizer (X : Set G))
    (hz : z ∈ centralizer (X : Set G)) : m * z * m⁻¹ ∈ centralizer (X : Set G) := by
  rw [mem_centralizer_iff]
  intro g hg
  have hg' : m⁻¹ * g * m ∈ X := by
    have := (mem_normalizer_iff.mp (inv_mem hm) g).mp hg
    simpa using this
  have := mem_centralizer_iff.mp hz _ hg'
  calc g * (m * z * m⁻¹) = m * ((m⁻¹ * g * m) * z) * m⁻¹ := by group
    _ = m * (z * (m⁻¹ * g * m)) * m⁻¹ := by rw [this]
    _ = m * z * m⁻¹ * g := by group

end CentAux

namespace A6VIFrame

section LinesFrame

variable {G : Type} [Group G] [Finite G]
variable {M O : Subgroup G} {x e₂ e₃ t ρ : G} {s : ℤ} (h : A6VIFrame M O x e₂ e₃ t ρ s)

include h

theorem e₃_eq : e₃ = (t * t) * x * (t * t)⁻¹ := by
  rw [← h.t_e₂, ← h.t_x]; group

theorem conj_mem_lines {y q g : G} (hy : y ∈ M)
    (hyN : y ∈ normalizer ((Qf x e₂ e₃ ⊔ O : Subgroup G) : Set G)) (hq : q = g * x * g⁻¹)
    (hqQ : q ∈ Qf x e₂ e₃) :
    ∃ q' ∈ Qf x e₂ e₃, ∃ o ∈ O, y * q * y⁻¹ = q' * o ∧
      (q' ∈ zpowers x ∨ q' ∈ zpowers e₂ ∨ q' ∈ zpowers e₃) := by
  have hQM := h.Q_le_M
  have hw : y * q * y⁻¹ ∈ Qf x e₂ e₃ ⊔ O :=
    (mem_normalizer_iff.mp hyN q).mp (mem_sup_left hqQ)
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (Qf x e₂ e₃) O h.Q_le_N
  have hw' : y * q * y⁻¹ ∈ ((Qf x e₂ e₃ : Subgroup G) : Set G) * (O : Set G) := by
    rw [← hset]; exact hw
  obtain ⟨q', hq', o, ho, hqo'⟩ := hw'
  have hqo : q' * o = y * q * y⁻¹ := hqo'
  refine ⟨q', hq', o, ho, hqo.symm, ?_⟩
  have hq3 : q ^ 3 = 1 := h.Q_exp q hqQ
  have hq1 : q ≠ 1 := by
    intro h1
    apply h.x_ne
    have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [this, ← hq, h1]; group
  have hw3 : (y * q * y⁻¹) ^ 3 = 1 := by rw [conj_pow, hq3, mul_one, mul_inv_cancel]
  have hw1 : y * q * y⁻¹ ≠ 1 := by
    intro h1
    apply hq1
    have : q = y⁻¹ * (y * q * y⁻¹) * y := by group
    rw [this, h1]; group
  have hq'3 : q' ^ 3 = 1 := h.Q_exp q' hq'
  have hq'1 : q' ≠ 1 := by
    intro h1
    rw [h1, one_mul] at hqo
    have hwo : orderOf (y * q * y⁻¹) = 3 := orderOf_eq_prime hw3 hw1
    have hdvd : orderOf (⟨o, ho⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hqo, hwo] at hdvd
    exact h.O_cop hdvd
  have hq'o : orderOf q' = 3 := orderOf_eq_prime hq'3 hq'1
  have hU3 : Nat.card (zpowers q') = 3 := by rw [Nat.card_zpowers, hq'o]
  have hq'M : q' ∈ M := hQM hq'
  have hUN : zpowers q' ≤ normalizer (O : Set G) :=
    (zpowers_le.mpr hq'M).trans h.O_norm
  have hwU : y * q * y⁻¹ ∈ zpowers q' ⊔ O := by
    rw [← hqo]; exact mul_mem_sup (mem_zpowers q') ho
  obtain ⟨k, hk, hkw⟩ := e9r_exists_conj_zpowers_eq hUN h.O_cop hU3 hwU hw3 hw1
  have hz : k⁻¹ * (y * q * y⁻¹) * k = (k⁻¹ * y * g) * x * (k⁻¹ * y * g)⁻¹ := by
    rw [hq]; group
  have hzU : k⁻¹ * (y * q * y⁻¹) * k ∈ zpowers q' := by
    rw [← hkw]; exact mem_zpowers _
  have hQ' : zpowers q' ≤ Qf x e₂ e₃ := zpowers_le.mpr hq'
  have hzQ : (k⁻¹ * y * g) * x * (k⁻¹ * y * g)⁻¹ ∈ Qf x e₂ e₃ := by
    rw [← hz]; exact hQ' hzU
  have hlin := h.lines (k⁻¹ * y * g) hzQ
  rw [← hz] at hlin
  have hz1 : k⁻¹ * (y * q * y⁻¹) * k ≠ 1 := by
    intro h1
    apply hw1
    have : y * q * y⁻¹ = k * (k⁻¹ * (y * q * y⁻¹) * k) * k⁻¹ := by group
    rw [this, h1]; group
  have key : ∀ e : G, e ^ 3 = 1 → e ≠ 1 → k⁻¹ * (y * q * y⁻¹) * k ∈ zpowers e →
      q' ∈ zpowers e := fun e he3 he1 hze => by
    have h' := zpowers_eq_of_mem he3 he1 hze hz1
    have : zpowers q' = zpowers e := hkw.symm.trans h'
    rw [← this]; exact mem_zpowers q'
  rcases hlin with hl | hl | hl
  · exact Or.inl (key x h.x_pow h.x_ne hl)
  · exact Or.inr (Or.inl (key e₂ h.e₂_pow h.e₂_ne hl))
  · exact Or.inr (Or.inr (key e₃ h.e₃_pow h.e₃_ne hl))


section WithBar

variable [(O.subgroupOf M).Normal]

theorem bar_inj {q₁ q₂ : G} (h₁ : q₁ ∈ Qf x e₂ e₃) (h₂ : q₂ ∈ Qf x e₂ e₃)
    (hb : bar M O q₁ = bar M O q₂) : q₁ = q₂ := by
  have hM := h.Q_le_M
  have h1 := (bar_eq_iff (hM h₁) (hM h₂)).mp hb
  have h2 : q₁⁻¹ * q₂ ∈ Qf x e₂ e₃ ⊓ O :=
    ⟨(Qf x e₂ e₃).mul_mem ((Qf x e₂ e₃).inv_mem h₁) h₂, h1⟩
  rw [h.Q_inf_O, mem_bot, inv_mul_eq_one] at h2
  exact h2

theorem bar_conj_mem_lines {y q g : G} (hy : y ∈ M)
    (hyN : y ∈ normalizer ((Qf x e₂ e₃ ⊔ O : Subgroup G) : Set G)) (hq : q = g * x * g⁻¹)
    (hqQ : q ∈ Qf x e₂ e₃) :
    bar M O y * bar M O q * (bar M O y)⁻¹ ∈ zpowers (bar M O x) ∨
      bar M O y * bar M O q * (bar M O y)⁻¹ ∈ zpowers (bar M O e₂) ∨
      bar M O y * bar M O q * (bar M O y)⁻¹ ∈ zpowers (bar M O e₃) := by
  have hQM := h.Q_le_M
  obtain ⟨q', hq', o, ho, hqo, hlin⟩ := h.conj_mem_lines hy hyN hq hqQ
  have hq'M : q' ∈ M := hQM hq'
  have hoM : o ∈ M := h.O_le ho
  have hb : bar M O y * bar M O q * (bar M O y)⁻¹ = bar M O q' := by
    rw [← bar_conj hy (hQM hqQ), hqo, bar_mul hq'M hoM, (bar_eq_one_iff hoM).mpr ho, mul_one]
  rw [hb]
  rcases hlin with hl | hl | hl
  · exact Or.inl (bar_mem_zpowers h.x_mem hl)
  · exact Or.inr (Or.inl (bar_mem_zpowers h.e₂_mem hl))
  · exact Or.inr (Or.inr (bar_mem_zpowers h.e₃_mem hl))


theorem dichotomy_bar {y : G} (hy : y ∈ M)
    (hyN : y ∈ normalizer ((Qf x e₂ e₃ ⊔ O : Subgroup G) : Set G))
    (hyx : x⁻¹ * (y * x * y⁻¹) ∈ O) (hyw : (e₂ * e₃)⁻¹ * (y * (e₂ * e₃) * y⁻¹) ∈ O) :
    (bar M O y * bar M O e₂ * (bar M O y)⁻¹ = bar M O e₂ ∧
        bar M O y * bar M O e₃ * (bar M O y)⁻¹ = bar M O e₃) ∨
      (bar M O y * bar M O e₂ * (bar M O y)⁻¹ = bar M O e₃ ∧
        bar M O y * bar M O e₃ * (bar M O y)⁻¹ = bar M O e₂) := by
  have hxM := h.x_mem
  have h2M := h.e₂_mem
  have h3M := h.e₃_mem
  have hxQ : x ∈ Qf x e₂ e₃ := mem_sup_left (mem_zpowers x)
  have h2Q : e₂ ∈ Qf x e₂ e₃ := mem_sup_right (mem_sup_left (mem_zpowers e₂))
  have h3Q : e₃ ∈ Qf x e₂ e₃ := mem_sup_right (mem_sup_right (mem_zpowers e₃))
  have h23M : e₂ * e₃ ∈ M := M.mul_mem h2M h3M
  have hyM' : ∀ g ∈ M, y * g * y⁻¹ ∈ M := fun g hg => M.mul_mem (M.mul_mem hy hg) (M.inv_mem hy)
  have c23 : Commute (bar M O e₂) (bar M O e₃) := by
    show bar M O e₂ * bar M O e₃ = bar M O e₃ * bar M O e₂
    rw [← bar_mul h2M h3M, ← bar_mul h3M h2M, h.comm_23]
  have hcomm_img : ∀ a ∈ zpowers (bar M O e₂), ∀ c ∈ zpowers (bar M O e₃), a * c = c * a := by
    intro a ha c hc
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc
    exact (c23.zpow_zpow i j).eq
  have h23 : zpowers (bar M O e₂) ⊓ zpowers (bar M O e₃) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hz₂, hz₃⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hz₂
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hz₃
    rw [← bar_zpow h2M]
    have heq : e₃ ^ j = e₂ ^ i := h.bar_inj (zpow_mem h3Q j) (zpow_mem h2Q i) (by
      rw [bar_zpow h3M, bar_zpow h2M]; exact hj)
    have hmem : e₂ ^ i ∈ zpowers e₂ ⊓ zpowers e₃ :=
      ⟨zpow_mem_zpowers e₂ i, heq ▸ zpow_mem_zpowers e₃ j⟩
    rw [h.ind_23] at hmem
    rw [mem_bot.mp hmem, bar_one]
    exact one_mem _
  have hT : (zpowers (bar M O e₂) ⊔ zpowers (bar M O e₃)) ⊓ zpowers (bar M O x) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzT, hzx⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨a', ha', c', hc', hz'⟩ := u3l42_decomp hcomm_img hzT
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha'
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc'
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hzx
    rw [← bar_zpow hxM] at hm
    rw [← bar_zpow h2M, ← bar_zpow h3M, ← bar_mul (M.zpow_mem h2M i) (M.zpow_mem h3M j)] at hz'
    have heq : e₂ ^ i * e₃ ^ j = x ^ m := h.bar_inj
      (mul_mem (zpow_mem h2Q i) (zpow_mem h3Q j)) (zpow_mem hxQ m) (hz'.symm.trans hm.symm)
    have hmem : x ^ m ∈ (zpowers e₂ ⊔ zpowers e₃) ⊓ zpowers x :=
      ⟨heq ▸ mul_mem (mem_sup_left (zpow_mem_zpowers e₂ i)) (mem_sup_right (zpow_mem_zpowers e₃ j)),
        zpow_mem_zpowers x m⟩
    rw [h.ind_x] at hmem
    rw [← hm, mem_bot.mp hmem, bar_one]
    exact one_mem _
  have he₂1 : bar M O e₂ ≠ 1 := by
    intro h1
    have := (bar_eq_one_iff h2M).mp h1
    have h2 : e₂ ∈ Qf x e₂ e₃ ⊓ O := ⟨h2Q, this⟩
    rw [h.Q_inf_O, mem_bot] at h2
    exact h.e₂_ne h2
  have he₃1 : bar M O e₃ ≠ 1 := by
    intro h1
    have := (bar_eq_one_iff h3M).mp h1
    have h2 : e₃ ∈ Qf x e₂ e₃ ⊓ O := ⟨h3Q, this⟩
    rw [h.Q_inf_O, mem_bot] at h2
    exact h.e₃_ne h2
  have hy1 : bar M O y * bar M O x * (bar M O y)⁻¹ = bar M O x := by
    have := (bar_eq_iff hxM (hyM' x hxM)).mpr hyx
    rw [bar_conj hy hxM] at this
    exact this.symm
  have hy23 : bar M O y * (bar M O e₂ * bar M O e₃) * (bar M O y)⁻¹ =
      bar M O e₂ * bar M O e₃ := by
    have := (bar_eq_iff h23M (hyM' _ h23M)).mpr hyw
    rw [bar_conj hy h23M, bar_mul h2M h3M] at this
    exact this.symm
  have hl2 := h.bar_conj_mem_lines hy hyN h.t_x.symm h2Q
  have hl3 := h.bar_conj_mem_lines hy hyN (q := e₃) h.e₃_eq h3Q
  exact monomial_conj c23 h23 hT he₂1 he₃1 hy1 hy23 hl2 hl3

end WithBar

theorem false_of_central {Y : Subgroup G} (hY2 : IsPGroup 2 Y) (hYM : Y ≤ M)
    (hYO : IsSylowOf 2 (Y ⊓ O) O)
    (hYB : Y ≤ normalizer ((Qf x e₂ e₃ ⊔ O : Subgroup G) : Set G))
    (hcomm : ∀ y ∈ Y, ∀ k ∈ Qf x e₂ e₃, y * k * y⁻¹ * k⁻¹ ∈ O)
    (hrank : ¬ Qf x e₂ e₃ ≤ (normalizer (Y : Set G) ⊓ M) ⊔ O) : False := by
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQO : Qf x e₂ e₃ ≤ normalizer (O : Set G) := h.Q_le_N
  have hYO' : Y ≤ normalizer (O : Set G) := hYM.trans h.O_norm
  have hBO : (Qf x e₂ e₃ ⊔ O : Subgroup G) ≤ normalizer (O : Set G) :=
    sup_le hQO Subgroup.le_normalizer
  have hBM : (Qf x e₂ e₃ ⊔ O : Subgroup G) ≤ M := sup_le h.Q_le_M h.O_le
  obtain ⟨T, hST, hTB, hYT, hTO, hTsup⟩ := l43_exists_lift (O := O) (B := Qf x e₂ e₃ ⊔ O)
    (Y := Y) le_sup_right hBO hYB hYO' hY2 h.O_cop
    (fun b hb => e9_pow_three_mem_sup hQO h.Q_exp hb) hYO
  have hcomm' := e9_comm_mem_sup hQO hYO' hcomm
  have hTY : ∀ t ∈ T, ∀ y ∈ Y, t * y * t⁻¹ ∈ Y := by
    intro t ht y hy
    have h1 : y * t * y⁻¹ * t⁻¹ ∈ O := hcomm' y hy t (hTB ht)
    have h2 : t * y * t⁻¹ * y⁻¹ ∈ O := by
      have := O.inv_mem h1
      have e : (y * t * y⁻¹ * t⁻¹)⁻¹ = t * y * t⁻¹ * y⁻¹ := by group
      rwa [e] at this
    have h3 : t * y * t⁻¹ * y⁻¹ ∈ T := by
      have e : t * y * t⁻¹ * y⁻¹ = t * (y * t⁻¹ * y⁻¹) := by group
      rw [e]
      exact T.mul_mem ht ((mem_normalizer_iff.mp (hYT hy) t⁻¹).mp (T.inv_mem ht))
    have h4 : t * y * t⁻¹ * y⁻¹ ∈ Y ⊓ O := hTO ▸ ⟨h3, h2⟩
    have e : t * y * t⁻¹ = (t * y * t⁻¹ * y⁻¹) * y := by group
    rw [e]
    exact Y.mul_mem h4.1 hy
  have hTN : T ≤ normalizer (Y : Set G) := by
    intro t ht
    rw [mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hTY t ht y hy, fun hy => ?_⟩
    have := hTY t⁻¹ (T.inv_mem ht) _ hy
    have e : t⁻¹ * (t * y * t⁻¹) * t⁻¹⁻¹ = y := by group
    rwa [e] at this
  refine hrank ?_
  calc Qf x e₂ e₃ ≤ Qf x e₂ e₃ ⊔ O := le_sup_left
    _ = T ⊔ O := hTsup.symm
    _ ≤ (normalizer (Y : Set G) ⊓ M) ⊔ O :=
      sup_le_sup_right (le_inf hTN (hTB.trans hBM)) O


theorem false_of_four {X : Subgroup G} (hXel : IsElemAbelian 2 X)
    (hXN : M ≤ normalizer (X : Set G))
    (h4 : Nat.card (⁅X, zpowers (e₂ * e₃⁻¹)⁆ : Subgroup G) = 4) : False := by
  have hxQ : x ∈ Qf x e₂ e₃ := mem_sup_left (mem_zpowers x)
  have h2Q : e₂ ∈ Qf x e₂ e₃ := mem_sup_right (mem_sup_left (mem_zpowers e₂))
  have h3Q : e₃ ∈ Qf x e₂ e₃ := mem_sup_right (mem_sup_right (mem_zpowers e₃))
  have hQM := h.Q_le_M
  set a : G := e₂ * e₃⁻¹ with ha
  set b : G := e₃ * x⁻¹ with hb
  have haQ : a ∈ Qf x e₂ e₃ := mul_mem h2Q (inv_mem h3Q)
  have hbQ : b ∈ Qf x e₂ e₃ := mul_mem h3Q (inv_mem hxQ)
  have hta : t * a * t⁻¹ = b := by
    have : t * a * t⁻¹ = (t * e₂ * t⁻¹) * (t * e₃ * t⁻¹)⁻¹ := by rw [ha]; group
    rw [this, h.t_e₂, h.t_e₃]
  have htb : t * b * t⁻¹ = x * e₂⁻¹ := by
    have : t * b * t⁻¹ = (t * e₃ * t⁻¹) * (t * x * t⁻¹)⁻¹ := by rw [hb]; group
    rw [this, h.t_e₃, h.t_x]
  have hab_eq : a * b = (x * e₂⁻¹)⁻¹ := by rw [ha, hb]; group
  have hcard_b : Nat.card (⁅X, zpowers b⁆ : Subgroup G) = 4 := by
    have := l43_card_commutator_conj hXN (m := t) (u := a) h.t_mem
    rw [hta] at this
    rw [this]; exact h4
  have hcard_c : Nat.card (⁅X, zpowers (x * e₂⁻¹)⁆ : Subgroup G) = 4 := by
    have := l43_card_commutator_conj hXN (m := t) (u := b) h.t_mem
    rw [htb] at this
    rw [this]; exact hcard_b
  have hcard_ab : Nat.card (⁅X, zpowers (a * b)⁆ : Subgroup G) = 4 := by
    rw [hab_eq, Subgroup.zpowers_inv]; exact hcard_c
  have ha3 : a ^ 3 = 1 := h.Q_exp a haQ
  have hb3 : b ^ 3 = 1 := h.Q_exp b hbQ
  have ha1 : a ≠ 1 := by
    intro h1
    have h2 : e₂ = e₃ := by
      have : e₂ * e₃⁻¹ = 1 := h1
      exact mul_inv_eq_one.mp this
    have : e₂ ∈ zpowers e₂ ⊓ zpowers e₃ := ⟨mem_zpowers e₂, h2 ▸ mem_zpowers e₃⟩
    rw [h.ind_23] at this
    exact h.e₂_ne (mem_bot.mp this)
  have hb1 : b ≠ 1 := by
    intro h1
    have h2 : e₃ = x := by
      have : e₃ * x⁻¹ = 1 := h1
      exact mul_inv_eq_one.mp this
    exact h.x_nmem_T (h2 ▸ mem_sup_right (mem_zpowers e₃))
  have hcab : a * b = b * a := h.Q_comm a haQ b hbQ
  have hind : zpowers a ⊓ zpowers b = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hza, hzb⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hza
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hzb
    have c23 : Commute e₂ e₃⁻¹ := ((show Commute e₂ e₃ from h.comm_23).inv_right)
    have cx3 : Commute e₃ x⁻¹ := ((show Commute x e₃ from h.comm_x₃).symm.inv_right)
    have e1 : a ^ i = x ^ (0 : ℤ) * e₂ ^ i * e₃ ^ (-i) := by
      rw [ha, c23.mul_zpow, inv_zpow', zpow_zero, one_mul]
    have e2 : b ^ j = x ^ (-j) * e₂ ^ (0 : ℤ) * e₃ ^ j := by
      rw [hb, cx3.mul_zpow, inv_zpow', zpow_zero, mul_one]
      exact (((show Commute x e₃ from h.comm_x₃).zpow_zpow (-j) j).eq).symm
    have hnf : x ^ (0 : ℤ) * e₂ ^ i * e₃ ^ (-i) = x ^ (-j) * e₂ ^ (0 : ℤ) * e₃ ^ j := by
      rw [← e1, ← e2, hj]
    obtain ⟨-, hnf2, -⟩ := a6vi_normal_form_eq h.ind_x h.ind_23 hnf
    have hd2 := a6vi_zpow_eq_of_three (orderOf_eq_prime h.e₂_pow h.e₂_ne) hnf2
    have hd3 : e₃ ^ (-i) = e₃ ^ (0 : ℤ) :=
      a6vi_zpow_eq_of_dvd h.e₃_pow (by simpa using (show (3 : ℤ) ∣ -i by simpa using hd2.neg_right))
    rw [e1, hnf2, hd3]
    simp
  have hXaN : a ∈ normalizer (X : Set G) := hXN (hQM haQ)
  have hXbN : b ∈ normalizer (X : Set G) := hXN (hQM hbQ)
  have hfl := fourth_line_centralizes hXel hXaN hXbN hcab ha3 hb3 ha1 hb1 hind h4 hcard_b hcard_ab
  set Z : Subgroup G := centralizer (X : Set G) with hZ
  have hd0Z : a * b ^ 2 ∈ Z := by
    rw [hZ, mem_centralizer_iff]
    intro g hg
    exact (hfl g hg).symm
  have hxx : x⁻¹ * x⁻¹ = x := by
    have h1 : x⁻¹ * x⁻¹ = (x ^ 2)⁻¹ := by group
    rw [h1, sq_eq_inv h.x_pow, inv_inv]
  have hcx3' : x⁻¹ * e₃ = e₃ * x⁻¹ := (((show Commute x e₃ from h.comm_x₃).inv_left).eq)
  have hd0 : a * b ^ 2 = e₂ * e₃ * x := by
    calc a * b ^ 2 = e₂ * (e₃⁻¹ * e₃) * x⁻¹ * e₃ * x⁻¹ := by rw [ha, hb, pow_two]; group
      _ = e₂ * (x⁻¹ * e₃) * x⁻¹ := by group
      _ = e₂ * (e₃ * x⁻¹) * x⁻¹ := by rw [hcx3']
      _ = e₂ * e₃ * (x⁻¹ * x⁻¹) := by group
      _ = e₂ * e₃ * x := by rw [hxx]
  rw [hd0] at hd0Z
  have hρN : ρ ∈ normalizer (X : Set G) := hXN h.ρ_mem
  have hρd : ρ * (e₂ * e₃ * x) * ρ⁻¹ = e₃ ^ s * e₂ ^ (-s) * x := by
    have : ρ * (e₂ * e₃ * x) * ρ⁻¹ = (ρ * e₂ * ρ⁻¹) * (ρ * e₃ * ρ⁻¹) * (ρ * x * ρ⁻¹) := by group
    rw [this, h.ρ_e₂, h.ρ_e₃, h.ρ_x]
  have hd1Z : e₃ ^ s * e₂ ^ (-s) * x ∈ Z := by
    rw [← hρd]
    exact conj_mem_centralizer_aux hρN hd0Z
  have hquot : (e₂ * e₃ * x) * (e₃ ^ s * e₂ ^ (-s) * x)⁻¹ ∈ Z := Z.mul_mem hd0Z (Z.inv_mem hd1Z)
  have hconjZ : ∀ z ∈ Z, t * z * t⁻¹ ∈ Z := fun z hz =>
    conj_mem_centralizer_aux (hXN h.t_mem) hz
  have hcube : ∀ e : G, e ^ 3 = 1 → e * e ∈ Z → e ∈ Z := by
    intro e he hee
    have : e = (e * e) * (e * e) := by
      calc e = e ^ 3 * e := by rw [he, one_mul]
        _ = e ^ 4 := by rw [← pow_succ]
        _ = e ^ 2 * e ^ 2 := by rw [← pow_add]
        _ = (e * e) * (e * e) := by rw [pow_two]
    rw [this]
    exact Z.mul_mem hee hee
  have hall : e₂ ∈ Z ∧ e₃ ∈ Z ∧ x ∈ Z := by
    rcases h.s_cases with rfl | rfl
    · have h1 : (e₂ * e₃ * x) * (e₃ ^ (1 : ℤ) * e₂ ^ (-(1 : ℤ)) * x)⁻¹ = e₂ * e₂ := by
        rw [zpow_one, zpow_neg_one]
        calc (e₂ * e₃ * x) * (e₃ * e₂⁻¹ * x)⁻¹ = e₂ * (e₃ * e₂) * e₃⁻¹ := by group
          _ = e₂ * (e₂ * e₃) * e₃⁻¹ := by rw [← h.comm_23]
          _ = e₂ * e₂ := by group
      rw [h1] at hquot
      have h2Z : e₂ ∈ Z := hcube e₂ h.e₂_pow hquot
      have h3Z : e₃ ∈ Z := by rw [← h.t_e₂]; exact hconjZ _ h2Z
      have hxZ : x ∈ Z := by rw [← h.t_e₃]; exact hconjZ _ h3Z
      exact ⟨h2Z, h3Z, hxZ⟩
    · have h1 : (e₂ * e₃ * x) * (e₃ ^ (-1 : ℤ) * e₂ ^ (-(-1 : ℤ)) * x)⁻¹ = e₃ * e₃ := by
        rw [zpow_neg_one, neg_neg, zpow_one]
        calc (e₂ * e₃ * x) * (e₃⁻¹ * e₂ * x)⁻¹ = e₂ * e₃ * e₂⁻¹ * e₃ := by group
          _ = e₃ * e₂ * e₂⁻¹ * e₃ := by rw [h.comm_23]
          _ = e₃ * e₃ := by group
      rw [h1] at hquot
      have h3Z : e₃ ∈ Z := hcube e₃ h.e₃_pow hquot
      have hxZ : x ∈ Z := by rw [← h.t_e₃]; exact hconjZ _ h3Z
      have h2Z : e₂ ∈ Z := by rw [← h.t_x]; exact hconjZ _ hxZ
      exact ⟨h2Z, h3Z, hxZ⟩
  obtain ⟨h2Z, h3Z, -⟩ := hall
  have haZ : a ∈ Z := Z.mul_mem h2Z (Z.inv_mem h3Z)
  have hbot : (⁅zpowers a, X⁆ : Subgroup G) = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact zpowers_le.mpr haZ
  rw [Subgroup.commutator_comm, hbot, Subgroup.card_bot] at h4
  omega


theorem e₂_e₃_mem_sup :
    e₂ ∈ zpowers (e₂ * e₃) ⊔ zpowers (e₂ * e₃⁻¹) ∧
      e₃ ∈ zpowers (e₂ * e₃) ⊔ zpowers (e₂ * e₃⁻¹) := by
  have hA : e₂ * e₃ ∈ zpowers (e₂ * e₃) ⊔ zpowers (e₂ * e₃⁻¹) := mem_sup_left (mem_zpowers _)
  have hB : e₂ * e₃⁻¹ ∈ zpowers (e₂ * e₃) ⊔ zpowers (e₂ * e₃⁻¹) := mem_sup_right (mem_zpowers _)
  have hc : e₃ * e₂ = e₂ * e₃ := h.comm_23.symm
  have h22 : e₂ * e₂ = (e₂ * e₃) * (e₂ * e₃⁻¹) := by
    calc e₂ * e₂ = e₂ * (e₃ * e₂) * e₃⁻¹ := by rw [hc]; group
      _ = (e₂ * e₃) * (e₂ * e₃⁻¹) := by group
  have h33 : e₃ * e₃ = (e₂ * e₃) * (e₂ * e₃⁻¹)⁻¹ := by
    calc e₃ * e₃ = e₃ * (e₂ * e₃) * e₂⁻¹ := by rw [← hc]; group
      _ = (e₂ * e₃) * (e₂ * e₃⁻¹)⁻¹ := by rw [show e₃ * (e₂ * e₃) = e₂ * (e₃ * e₃) by
          rw [← mul_assoc, hc, mul_assoc]]; group
  have hcube : ∀ e : G, e ^ 3 = 1 → e * e ∈ zpowers (e₂ * e₃) ⊔ zpowers (e₂ * e₃⁻¹) →
      e ∈ zpowers (e₂ * e₃) ⊔ zpowers (e₂ * e₃⁻¹) := by
    intro e he hee
    have : e = (e * e) * (e * e) := by
      calc e = e ^ 3 * e := by rw [he, one_mul]
        _ = e ^ 4 := by rw [← pow_succ]
        _ = e ^ 2 * e ^ 2 := by rw [← pow_add]
        _ = (e * e) * (e * e) := by rw [pow_two]
    rw [this]
    exact mul_mem hee hee
  exact ⟨hcube e₂ h.e₂_pow (by rw [h22]; exact mul_mem hA hB),
    hcube e₃ h.e₃_pow (by rw [h33]; exact mul_mem hA (inv_mem hB))⟩


theorem false_of_small {Y : Subgroup G} (hY2 : IsPGroup 2 Y) (hYM : Y ≤ M)
    (hYO : IsSylowOf 2 (Y ⊓ O) O)
    (hYB : Y ≤ normalizer ((Qf x e₂ e₃ ⊔ O : Subgroup G) : Set G))
    (hxY : x ∈ normalizer (Y : Set G))
    (hwY : e₂ * e₃ ∈ normalizer (Y : Set G))
    (hsmall : ∀ Y₀ : Subgroup G, Y₀ ≤ Y → Y₀ ≠ ⊥ → (Y₀.subgroupOf Y).Characteristic →
      CFSG.Open.pRank 3 (normalizer (Y₀ : Set G) ⊓ M) < 3) : False := by
  haveI : (O.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.O_le).mpr h.O_norm
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxQ : x ∈ Qf x e₂ e₃ := mem_sup_left (mem_zpowers x)
  have h2Q : e₂ ∈ Qf x e₂ e₃ := mem_sup_right (mem_sup_left (mem_zpowers e₂))
  have h3Q : e₃ ∈ Qf x e₂ e₃ := mem_sup_right (mem_sup_right (mem_zpowers e₃))
  have hwQ : e₂ * e₃ ∈ Qf x e₂ e₃ := mul_mem h2Q h3Q
  have hxM := h.x_mem
  have h2M := h.e₂_mem
  have h3M := h.e₃_mem
  have hQO : Qf x e₂ e₃ ≤ normalizer (O : Set G) := h.Q_le_N
  have hYO' : Y ≤ normalizer (O : Set G) := hYM.trans h.O_norm
  have hYB_O : Y ⊓ (Qf x e₂ e₃ ⊔ O) ≤ O := e9_inf_sup_le hQO h.Q_exp hY2
  have hrankQ : ∀ Y₀ : Subgroup G, Y₀ ≤ Y → Y₀ ≠ ⊥ → (Y₀.subgroupOf Y).Characteristic →
      ¬ Qf x e₂ e₃ ≤ (normalizer (Y₀ : Set G) ⊓ M) ⊔ O := by
    intro Y₀ hle hne hch hEle
    have h3 := l43_three_le_pRank_of_le_sup (H := normalizer (Y₀ : Set G) ⊓ M) (O := O)
      (E := Qf x e₂ e₃) (inf_le_right.trans h.O_norm) h.O_cop h.Q_el h.Q_card hEle
    exact absurd h3 (not_le.mpr (hsmall Y₀ hle hne hch))
  have hO₂Y : pCoreOf 2 M ≤ Y ⊓ O :=
    e9_le_of_normal h.O₂_le
      (h.O_le.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M))
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M) hYO
  have hYne : Y ≠ ⊥ := by
    intro hY
    apply h.O₂_ne
    rw [eq_bot_iff]
    intro g hg
    have := (hO₂Y hg).1
    rw [hY] at this
    exact this
  have hYchar : (Y.subgroupOf Y).Characteristic := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  have hyU : ∀ u ∈ Qf x e₂ e₃, u ∈ normalizer (Y : Set G) → ∀ y ∈ Y, u⁻¹ * (y * u * y⁻¹) ∈ O := by
    intro u hu huY y hy
    apply hYB_O
    refine ⟨?_, ?_⟩
    · have e : u⁻¹ * (y * u * y⁻¹) = (u⁻¹ * y * u) * y⁻¹ := by group
      rw [e]
      have h1 : u⁻¹ * y * u ∈ Y := by
        have := (mem_normalizer_iff.mp (inv_mem huY) y).mp hy
        simpa using this
      exact Y.mul_mem h1 (Y.inv_mem hy)
    · have hyu : y * u * y⁻¹ ∈ Qf x e₂ e₃ ⊔ O :=
        (mem_normalizer_iff.mp (hYB hy) u).mp (mem_sup_left hu)
      exact Subgroup.mul_mem _ (mem_sup_left ((Qf x e₂ e₃).inv_mem hu)) hyu
  have hdich := fun y (hy : y ∈ Y) => h.dichotomy_bar (hYM hy) (hYB hy) (hyU x hxQ hxY y hy)
    (hyU _ hwQ hwY y hy)
  by_cases hsw : ∃ y₁ ∈ Y, bar M O y₁ * bar M O e₂ * (bar M O y₁)⁻¹ = bar M O e₃ ∧
      bar M O y₁ * bar M O e₃ * (bar M O y₁)⁻¹ = bar M O e₂
  swap
  ·
    push Not at hsw
    refine h.false_of_central hY2 hYM hYO hYB ?_ (hrankQ Y le_rfl hYne hYchar)
    intro y hy k hk
    have hyM := hYM hy
    have hid : bar M O y * bar M O e₂ * (bar M O y)⁻¹ = bar M O e₂ ∧
        bar M O y * bar M O e₃ * (bar M O y)⁻¹ = bar M O e₃ := by
      rcases hdich y hy with hh | hh
      · exact hh
      · exact absurd hh.2 (hsw y hy hh.1)
    have cx : Commute (bar M O y) (bar M O x) := by
      have := (bar_eq_iff hxM (M.mul_mem (M.mul_mem hyM hxM) (M.inv_mem hyM))).mpr
        (hyU x hxQ hxY y hy)
      rw [bar_conj hyM hxM] at this
      show bar M O y * bar M O x = bar M O x * bar M O y
      calc bar M O y * bar M O x = (bar M O y * bar M O x * (bar M O y)⁻¹) * bar M O y := by
            group
        _ = bar M O x * bar M O y := by rw [← this]
    have c2 : Commute (bar M O y) (bar M O e₂) := by
      show bar M O y * bar M O e₂ = bar M O e₂ * bar M O y
      calc bar M O y * bar M O e₂ = (bar M O y * bar M O e₂ * (bar M O y)⁻¹) * bar M O y := by
            group
        _ = bar M O e₂ * bar M O y := by rw [hid.1]
    have c3 : Commute (bar M O y) (bar M O e₃) := by
      show bar M O y * bar M O e₃ = bar M O e₃ * bar M O y
      calc bar M O y * bar M O e₃ = (bar M O y * bar M O e₃ * (bar M O y)⁻¹) * bar M O y := by
            group
        _ = bar M O e₃ * bar M O y := by rw [hid.2]
    obtain ⟨a, ha, c, hc, rfl⟩ := u3l42_decomp h.x_T hk
    obtain ⟨a', ha', c', hc', rfl⟩ := u3l42_decomp h.T_comm_gen hc
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp ha'
    obtain ⟨l, rfl⟩ := mem_zpowers_iff.mp hc'
    have hkM : x ^ i * (e₂ ^ j * e₃ ^ l) ∈ M := by
      exact M.mul_mem (M.zpow_mem hxM i) (M.mul_mem (M.zpow_mem h2M j) (M.zpow_mem h3M l))
    refine comm_mem_of_commute hyM hkM ?_
    rw [bar_mul (M.zpow_mem hxM i) (M.mul_mem (M.zpow_mem h2M j) (M.zpow_mem h3M l)),
      bar_mul (M.zpow_mem h2M j) (M.zpow_mem h3M l), bar_zpow hxM, bar_zpow h2M, bar_zpow h3M]
    exact (cx.zpow_right i).mul_right ((c2.zpow_right j).mul_right (c3.zpow_right l))
  · obtain ⟨y₁, hy₁, hs2, hs3⟩ := hsw
    set u₂ : G := e₂ * e₃⁻¹ with hu₂
    have hu₂Q : u₂ ∈ Qf x e₂ e₃ := mul_mem h2Q (inv_mem h3Q)
    have hu₂M : u₂ ∈ M := h.Q_le_M hu₂Q
    have hu₂3 : u₂ ^ 3 = 1 := h.Q_exp u₂ hu₂Q
    have hu₂1 : u₂ ≠ 1 := by
      intro h1
      have h2 : e₂ = e₃ := mul_inv_eq_one.mp h1
      have : e₂ ∈ zpowers e₂ ⊓ zpowers e₃ := ⟨mem_zpowers e₂, h2 ▸ mem_zpowers e₃⟩
      rw [h.ind_23] at this
      exact h.e₂_ne (mem_bot.mp this)
    set U₂ : Subgroup G := zpowers u₂ with hU₂
    have hU₂card : Nat.card U₂ = 3 := by
      rw [hU₂, Nat.card_zpowers, orderOf_eq_prime hu₂3 hu₂1]
    have hU₂3' : ∀ k ∈ U₂, k ^ 3 = 1 := (isElemAbelian_zpowers hu₂3).2
    have hU₂M' : U₂ ≤ M := zpowers_le.mpr hu₂M
    have hbu₂ : bar M O u₂ = bar M O e₂ * (bar M O e₃)⁻¹ := by
      rw [hu₂, bar_mul h2M (M.inv_mem h3M), bar_inv h3M]
    have hbconj : ∀ y ∈ Y, bar M O (y * u₂ * y⁻¹) = bar M O u₂ ∨
        bar M O (y * u₂ * y⁻¹) = (bar M O u₂)⁻¹ := by
      intro y hy
      have hyM := hYM hy
      rw [bar_conj hyM hu₂M, hbu₂]
      have e : bar M O y * (bar M O e₂ * (bar M O e₃)⁻¹) * (bar M O y)⁻¹ =
          (bar M O y * bar M O e₂ * (bar M O y)⁻¹) *
            (bar M O y * bar M O e₃ * (bar M O y)⁻¹)⁻¹ := by group
      rw [e]
      rcases hdich y hy with ⟨k2, k3⟩ | ⟨k2, k3⟩
      · left; rw [k2, k3]
      · right; rw [k2, k3]; group
    have hyuM : ∀ y ∈ Y, y * u₂ * y⁻¹ ∈ M := fun y hy =>
      M.mul_mem (M.mul_mem (hYM hy) hu₂M) (M.inv_mem (hYM hy))
    have hkey : ∀ y ∈ Y, y * u₂ * y⁻¹ ∈ U₂ ⊔ O := by
      intro y hy
      rcases hbconj y hy with hb | hb
      · have h1 := (bar_eq_iff hu₂M (hyuM y hy)).mp hb.symm
        have e : y * u₂ * y⁻¹ = u₂ * (u₂⁻¹ * (y * u₂ * y⁻¹)) := by group
        rw [e]; exact mul_mem_sup (mem_zpowers u₂) h1
      · have hb' : bar M O (u₂⁻¹) = bar M O (y * u₂ * y⁻¹) := by rw [bar_inv hu₂M, hb]
        have h1 := (bar_eq_iff (M.inv_mem hu₂M) (hyuM y hy)).mp hb'
        have e : y * u₂ * y⁻¹ = u₂⁻¹ * (u₂⁻¹⁻¹ * (y * u₂ * y⁻¹)) := by group
        rw [e]; exact mul_mem_sup (inv_mem (mem_zpowers u₂)) h1
    have hkey' : ∀ y ∈ Y, ∀ b ∈ U₂ ⊔ O, y * b * y⁻¹ ∈ U₂ ⊔ O := by
      intro y hy b hb
      have hset := Subgroup.coe_mul_of_left_le_normalizer_right U₂ O (hU₂M'.trans h.O_norm)
      have hb' : b ∈ (U₂ : Set G) * (O : Set G) := by rw [← hset]; exact hb
      obtain ⟨u, hu, o, ho, rfl⟩ := hb'
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hu
      have e : y * (u₂ ^ k * o) * y⁻¹ = (y * u₂ * y⁻¹) ^ k * (y * o * y⁻¹) := by
        rw [conj_zpow]; group
      show y * (u₂ ^ k * o) * y⁻¹ ∈ U₂ ⊔ O
      rw [e]
      exact Subgroup.mul_mem _ (zpow_mem (hkey y hy) k)
        (mem_sup_right ((mem_normalizer_iff.mp (hYO' hy) o).mp ho))
    have hYU₂ : Y ≤ normalizer ((U₂ ⊔ O : Subgroup G) : Set G) := by
      intro y hy
      rw [mem_normalizer_iff]
      intro b
      refine ⟨hkey' y hy b, fun hb => ?_⟩
      have := hkey' y⁻¹ (Y.inv_mem hy) _ hb
      have e : y⁻¹ * (y * b * y⁻¹) * y⁻¹⁻¹ = b := by group
      rwa [e] at this
    have hnt : ∃ y ∈ Y, ∃ b ∈ U₂ ⊔ O, y * b * y⁻¹ * b⁻¹ ∉ O := by
      refine ⟨y₁, hy₁, u₂, mem_sup_left (mem_zpowers u₂), fun hmem => ?_⟩
      have hy₁M := hYM hy₁
      have hb₁ : bar M O (y₁ * u₂ * y₁⁻¹) = (bar M O u₂)⁻¹ := by
        rw [bar_conj hy₁M hu₂M, hbu₂]
        have e : bar M O y₁ * (bar M O e₂ * (bar M O e₃)⁻¹) * (bar M O y₁)⁻¹ =
            (bar M O y₁ * bar M O e₂ * (bar M O y₁)⁻¹) *
              (bar M O y₁ * bar M O e₃ * (bar M O y₁)⁻¹)⁻¹ := by group
        rw [e, hs2, hs3]; group
      have h1 := (bar_eq_one_iff (M.mul_mem (hyuM y₁ hy₁) (M.inv_mem hu₂M))).mpr hmem
      rw [bar_mul (hyuM y₁ hy₁) (M.inv_mem hu₂M), hb₁, bar_inv hu₂M] at h1
      have hb3 : (bar M O u₂) ^ 3 = 1 := by
        rw [← bar_pow hu₂M, hu₂3, bar_one]
      have hb1 : bar M O u₂ = 1 := by
        calc bar M O u₂ = (bar M O u₂) ^ 3 * ((bar M O u₂)⁻¹ * (bar M O u₂)⁻¹) := by group
          _ = 1 := by rw [hb3, h1, mul_one]
      have := (bar_eq_one_iff hu₂M).mp hb1
      have h2 : u₂ ∈ Qf x e₂ e₃ ⊓ O := ⟨hu₂Q, this⟩
      rw [h.Q_inf_O, mem_bot] at h2
      exact hu₂1 h2
    have hrankU : ∀ C : Subgroup G, C ≤ Y → C ≠ ⊥ → (C.subgroupOf Y).Characteristic →
        ¬ U₂ ≤ (normalizer (C : Set G) ⊓ M) ⊔ O := by
      intro C hCY hC1 hCch hU
      have hxC : x ∈ normalizer (C : Set G) := l43_normalizer_le_of_characteristic hCY hCch hxY
      have hwC : e₂ * e₃ ∈ normalizer (C : Set G) :=
        l43_normalizer_le_of_characteristic hCY hCch hwY
      have hNM : zpowers (e₂ * e₃) ≤ (normalizer (C : Set G) ⊓ M) ⊔ O :=
        le_sup_of_le_left (zpowers_le.mpr (mem_inf.mpr ⟨hwC, M.mul_mem h2M h3M⟩))
      have hxNM : zpowers x ≤ (normalizer (C : Set G) ⊓ M) ⊔ O :=
        le_sup_of_le_left (zpowers_le.mpr (mem_inf.mpr ⟨hxC, hxM⟩))
      refine hrankQ C hCY hC1 hCch ?_
      have hS : zpowers (e₂ * e₃) ⊔ zpowers (e₂ * e₃⁻¹) ≤ (normalizer (C : Set G) ⊓ M) ⊔ O :=
        sup_le hNM hU
      exact sup_le hxNM (sup_le (zpowers_le.mpr (hS h.e₂_e₃_mem_sup.1))
        (zpowers_le.mpr (hS h.e₂_e₃_mem_sup.2)))
    have hbn := bn_card_four h.O_le h.O_norm h.O_cop h.O₂_le h.charTwo hY2 hYM hYO hU₂M' hU₂card
      hU₂3' hYU₂ hnt hrankU
    exact h.false_of_four (l43_isElemAbelian_omegaOneCenter
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M))
      (l43_normalizer_omegaOneCenter
        (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M)) hbn


theorem normalizer_le_of_big {Y : Subgroup G} (hY2 : IsPGroup 2 Y)
    (hbig : ∃ Y₀ : Subgroup G, Y₀ ≤ Y ∧ Y₀ ≠ ⊥ ∧ (Y₀.subgroupOf Y).Characteristic ∧
      3 ≤ CFSG.Open.pRank 3 (normalizer (Y₀ : Set G) ⊓ M)) : normalizer (Y : Set G) ≤ M := by
  obtain ⟨Y₀, hle, hne, hch, hr⟩ := hbig
  exact (l43_normalizer_le_of_characteristic hle hch).trans (h.D1 Y₀ hne (hY2.to_le hle) hr)

theorem normalizer_le {Y : Subgroup G} (hY2 : IsPGroup 2 Y) (hYM : Y ≤ M)
    (hYO : IsSylowOf 2 (Y ⊓ O) O)
    (hYB : Y ≤ normalizer ((Qf x e₂ e₃ ⊔ O : Subgroup G) : Set G))
    (hxY : x ∈ normalizer (Y : Set G))
    (hwY : e₂ * e₃ ∈ normalizer (Y : Set G)) : normalizer (Y : Set G) ≤ M := by
  by_cases hbig : ∃ Y₀ : Subgroup G, Y₀ ≤ Y ∧ Y₀ ≠ ⊥ ∧ (Y₀.subgroupOf Y).Characteristic ∧
      3 ≤ CFSG.Open.pRank 3 (normalizer (Y₀ : Set G) ⊓ M)
  · exact h.normalizer_le_of_big hY2 hbig
  · push Not at hbig
    exact (h.false_of_small hY2 hYM hYO hYB hxY hwY hbig).elim

end LinesFrame

end A6VIFrame

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Aux

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Aux

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup
open CFSG.RankThree.PartTwo.Sec11 (W33)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem abelian27_unique {P : Subgroup G}
    (e : P ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) {A B : Subgroup G}
    (hAP : A ≤ P) (hBP : B ≤ P) (hA : IsMulCommutative A) (hB : IsMulCommutative B)
    (hAc : Nat.card A = 27) (hBc : Nat.card B = 27) : A = B := by
  let ι : (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)) →* G :=
    P.subtype.comp e.symm.toMonoidHom
  have hιinj : Function.Injective ι := P.subtype_injective.comp e.symm.injective
  have hιsurj : ∀ b ∈ P, ∃ w, ι w = b := fun b hb => ⟨e ⟨b, hb⟩, by simp [ι]⟩
  let A₀ : Subgroup (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)) :=
    (RegularWreathProduct.rightHom : Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3) →*
      Multiplicative (ZMod 3)).ker
  have hcomap_card : ∀ B : Subgroup G, B ≤ P → Nat.card (B.comap ι) = Nat.card B := by
    intro B hB
    have hrange : B ≤ ι.range := fun b hb => hιsurj b (hB hb)
    calc Nat.card (B.comap ι) = Nat.card ((B.comap ι).map ι) :=
          (Subgroup.card_map_of_injective hιinj).symm
      _ = Nat.card B := by rw [Subgroup.map_comap_eq_self hrange]
  have key : ∀ C : Subgroup G, C ≤ P → IsMulCommutative C → Nat.card C = 27 →
      C.comap ι = A₀ := by
    intro C hCP hC hCc
    have := Subgroup.comap_injective_isMulCommutative C hιinj
    have hle : C.comap ι ≤ A₀ := by
      by_contra hnle
      have := wreath_card_le_nine_of_not_le_ker (X := C.comap ι) inferInstance hnle
      rw [hcomap_card C hCP, hCc] at this
      omega
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcomap_card C hCP, hCc, wreath_card_ker])
  have hA' := key A hAP hA hAc
  have hB' := key B hBP hB hBc
  have hAr : A ≤ ι.range := fun b hb => hιsurj b (hAP hb)
  have hBr : B ≤ ι.range := fun b hb => hιsurj b (hBP hb)
  rw [← Subgroup.map_comap_eq_self hAr, ← Subgroup.map_comap_eq_self hBr, hA', hB']

theorem vi_lines {P : Subgroup G} {x : G} {J : Subgroup G}
    (hP3 : IsPGroup 3 P) (hP81 : Nat.card P = 81) (hxP : x ∈ P) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hxJ : x ∉ J) (hQab : IsMulCommutative (P ⊓ centralizer ({x} : Set G) : Subgroup G))
    (hQcard : Nat.card (P ⊓ centralizer ({x} : Set G) : Subgroup G) = 27)
    (hDcard : Nat.card (P ⊓ J : Subgroup G) = 9)
    (hfus : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤
        P ⊓ centralizer ({x} : Set G) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x ∨
        (zpowers x).map (MulAut.conj g).toMonoidHom ≤ J) :
    ∃ t e₂ e₃ : G, t ∈ P ∧ e₂ = t * x * t⁻¹ ∧ e₃ = t * e₂ * t⁻¹ ∧ t * e₃ * t⁻¹ = x ∧
      e₂ ∈ P ⊓ J ∧ e₃ ∈ P ⊓ J ∧ e₂ ^ 3 = 1 ∧ e₃ ^ 3 = 1 ∧ e₂ ≠ 1 ∧ e₃ ≠ 1 ∧
      e₂ * x = x * e₂ ∧ e₃ * x = x * e₃ ∧ e₂ * e₃ = e₃ * e₂ ∧
      zpowers e₂ ⊓ zpowers e₃ = ⊥ ∧ (zpowers e₂ ⊔ zpowers e₃) ⊓ zpowers x = ⊥ ∧
      ∀ g : G, g * x * g⁻¹ ∈ P ⊓ centralizer ({x} : Set G) →
        g * x * g⁻¹ ∈ zpowers x ∨ g * x * g⁻¹ ∈ zpowers e₂ ∨ g * x * g⁻¹ ∈ zpowers e₃ := by
  classical
  have hf3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q : Subgroup G := P ⊓ centralizer ({x} : Set G) with hQ
  have hQP : Q ≤ P := inf_le_left
  have hxQ : x ∈ Q := ⟨hxP, mem_centralizer_singleton_iff.mpr rfl⟩
  have hQcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb => setLike_mul_comm ha hb
  obtain ⟨t, htP, htQ⟩ : ∃ t ∈ P, t ∉ Q := by
    by_contra hcon
    push Not at hcon
    have hle : P ≤ Q := fun g hg => hcon g hg
    have := Subgroup.card_le_of_le hle
    rw [hP81, hQcard] at this
    omega
  have hindex : (Q.subgroupOf P).index = 3 := by
    have h1 := Subgroup.relIndex_mul_card (H := Q) (K := P)
    rw [inf_of_le_left hQP, hQcard, hP81] at h1
    have : Q.relIndex P = 3 := by omega
    exact this
  have hnormQ : (Q.subgroupOf P).Normal := by
    refine Subgroup.normal_of_index_eq_minFac_card ?_
    rw [hindex, show Nat.card ↥P = 81 from hP81]
    norm_num
  have hconjQ : ∀ g ∈ P, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := by
    intro g hg q hq
    have := hnormQ.conj_mem ⟨q, hQP hq⟩ (mem_subgroupOf.mpr hq) ⟨g, hg⟩
    exact mem_subgroupOf.mp this
  have ht3 : t ^ 3 ∈ Q := by
    have := Subgroup.pow_index_mem (Q.subgroupOf P) (⟨t, htP⟩ : P)
    rw [hindex] at this
    exact mem_subgroupOf.mp this
  have hP3' : ∀ g ∈ P, ∃ m : ℕ, g ^ (3 ^ m) = 1 := by
    intro g hg
    obtain ⟨m, hm⟩ := hP3 ⟨g, hg⟩
    exact ⟨m, congrArg Subtype.val hm⟩
  have hclaimA : ∀ g ∈ P, g ∉ Q → g * x * g⁻¹ ∉ zpowers x := by
    intro g hg hgQ hux
    obtain ⟨m, hm⟩ := hP3' g hg
    have := p34_conj_eq_of_pow hx1 hx3 hm hux
    apply hgQ
    refine ⟨hg, mem_centralizer_singleton_iff.mpr ?_⟩
    calc g * x = (g * x * g⁻¹) * g := by group
      _ = x * g := by rw [this]
  have ht2 : t * t ∈ P := mul_mem htP htP
  have ht2Q : t * t ∉ Q := by
    intro h2
    apply htQ
    have e : t = t ^ 3 * (t * t)⁻¹ := by rw [pow_three]; group
    rw [e]
    exact Q.mul_mem ht3 (Q.inv_mem h2)
  have htinvQ : t⁻¹ ∉ Q := fun h1 => htQ (by simpa using Q.inv_mem h1)
  have htinvP : t⁻¹ ∈ P := inv_mem htP
  obtain ⟨e₂, he₂⟩ : ∃ e₂ : G, e₂ = t * x * t⁻¹ := ⟨_, rfl⟩
  obtain ⟨e₃, he₃⟩ : ∃ e₃ : G, e₃ = t * e₂ * t⁻¹ := ⟨_, rfl⟩
  have he₃' : e₃ = (t * t) * x * (t * t)⁻¹ := by rw [he₃, he₂]; group
  have he₂Q : e₂ ∈ Q := by rw [he₂]; exact hconjQ t htP x hxQ
  have he₃Q : e₃ ∈ Q := by rw [he₃]; exact hconjQ t htP e₂ he₂Q
  have ht3x : t * e₃ * t⁻¹ = x := by
    have h1 : t ^ 3 * x * (t ^ 3)⁻¹ = x := by
      have hc : t ^ 3 ∈ centralizer ({x} : Set G) := (ht3 : t ^ 3 ∈ Q).2
      have := mem_centralizer_singleton_iff.mp hc
      rw [this]; group
    have h2 : t * e₃ * t⁻¹ = t ^ 3 * x * (t ^ 3)⁻¹ := by rw [he₃, he₂, pow_three]; group
    rw [h2, h1]
  have hx3' : e₂ ^ 3 = 1 := by rw [he₂, conj_pow, hx3, mul_one, mul_inv_cancel]
  have hx3'' : e₃ ^ 3 = 1 := by rw [he₃, conj_pow, hx3', mul_one, mul_inv_cancel]
  have he₂1 : e₂ ≠ 1 := by
    intro h1
    apply hx1
    have : x = t⁻¹ * e₂ * t := by rw [he₂]; group
    rw [this, h1]; group
  have he₃1 : e₃ ≠ 1 := by
    intro h1
    apply he₂1
    have : e₂ = t⁻¹ * e₃ * t := by rw [he₃]; group
    rw [this, h1]; group
  have hlineJ : ∀ g ∈ P, g ∉ Q → g * x * g⁻¹ ∈ J := by
    intro g hg hgQ
    have hle : (zpowers x).map (MulAut.conj g).toMonoidHom ≤ Q := by
      rw [MonoidHom.map_zpowers]
      refine zpowers_le.mpr ?_
      exact hconjQ g hg x hxQ
    rcases hfus g hle with h1 | h1
    · exfalso
      apply hclaimA g hg hgQ
      have : g * x * g⁻¹ ∈ (zpowers x).map (MulAut.conj g).toMonoidHom := ⟨x, mem_zpowers x, rfl⟩
      rwa [h1] at this
    · have : g * x * g⁻¹ ∈ (zpowers x).map (MulAut.conj g).toMonoidHom := ⟨x, mem_zpowers x, rfl⟩
      exact h1 this
  have he₂J : e₂ ∈ J := by rw [he₂]; exact hlineJ t htP htQ
  have he₃J : e₃ ∈ J := by rw [he₃']; exact hlineJ (t * t) ht2 ht2Q
  have he₂D : e₂ ∈ P ⊓ J := ⟨hQP he₂Q, he₂J⟩
  have he₃D : e₃ ∈ P ⊓ J := ⟨hQP he₃Q, he₃J⟩
  have hxJ' : ∀ b : ℤ, x ^ b ∈ J → x ^ b = 1 := by
    intro b hb
    by_contra hb1
    apply hxJ
    have h1 := zpowers_eq_of_mem hx3 hx1 (zpow_mem_zpowers x b) hb1
    have hx' : x ∈ zpowers (x ^ b) := h1.symm ▸ mem_zpowers x
    exact (zpowers_le.mpr hb) hx'
  have hc2x : e₂ * x = x * e₂ := hQcomm e₂ he₂Q x hxQ
  have hc3x : e₃ * x = x * e₃ := hQcomm e₃ he₃Q x hxQ
  have hc23 : e₂ * e₃ = e₃ * e₂ := hQcomm e₂ he₂Q e₃ he₃Q
  have he₃nmem : e₃ ∉ zpowers e₂ := by
    intro he
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp he
    have hx_eq : x = (t * x * t⁻¹) ^ (k * k) := by
      calc x = t * e₃ * t⁻¹ := ht3x.symm
        _ = t * e₂ ^ k * t⁻¹ := by rw [hk]
        _ = (t * e₂ * t⁻¹) ^ k := by rw [conj_zpow]
        _ = e₃ ^ k := by rw [← he₃]
        _ = (e₂ ^ k) ^ k := by rw [hk]
        _ = e₂ ^ (k * k) := by rw [← zpow_mul]
        _ = (t * x * t⁻¹) ^ (k * k) := by rw [he₂]
    have h1 : t⁻¹ * x * t = x ^ (k * k) := by
      calc t⁻¹ * x * t = t⁻¹ * (t * x * t⁻¹) ^ (k * k) * t := by rw [← hx_eq]
        _ = (t⁻¹ * (t * x * t⁻¹) * t) ^ (k * k) := by
          have := conj_zpow (i := k * k) (a := t⁻¹) (b := t * x * t⁻¹)
          rw [inv_inv] at this
          exact this.symm
        _ = x ^ (k * k) := by group
    apply hclaimA t⁻¹ htinvP htinvQ
    rw [inv_inv, h1]
    exact zpow_mem_zpowers x _
  have hind23 : zpowers e₂ ⊓ zpowers e₃ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hz2, hz3⟩ := Subgroup.mem_inf.mp hz
    by_contra hz1
    have hz1' : z ≠ 1 := fun h1 => hz1 (by rw [h1]; exact one_mem _)
    have h2 := zpowers_eq_of_mem hx3' he₂1 hz2 hz1'
    have h3 := zpowers_eq_of_mem hx3'' he₃1 hz3 hz1'
    apply he₃nmem
    rw [← h2, h3]
    exact mem_zpowers e₃
  have hT_J : zpowers e₂ ⊔ zpowers e₃ ≤ P ⊓ J :=
    sup_le (zpowers_le.mpr he₂D) (zpowers_le.mpr he₃D)
  have hindx : (zpowers e₂ ⊔ zpowers e₃) ⊓ zpowers x = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzT, hzx⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨b, rfl⟩ := mem_zpowers_iff.mp hzx
    have := hxJ' b (hT_J hzT).2
    rw [this]
    exact one_mem _
  have hcomm_pair : ∀ a ∈ zpowers e₂, ∀ b ∈ zpowers e₃, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
    exact ((show Commute e₂ e₃ from hc23).zpow_zpow i j).eq
  have hTcard : Nat.card (zpowers e₂ ⊔ zpowers e₃ : Subgroup G) = 9 := by
    have hcx : Nat.card (zpowers e₂) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hx3' he₂1]
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three (zpowers e₂) hx3''
      he₃nmem (fun e he => hcomm_pair e he e₃ (mem_zpowers e₃)), hcx]
  have hTD : zpowers e₂ ⊔ zpowers e₃ = P ⊓ J :=
    Subgroup.eq_of_le_of_card_ge hT_J (by rw [hTcard, hDcard])
  suffices hlines : ∀ g : G, g * x * g⁻¹ ∈ Q → g * x * g⁻¹ ∈ zpowers x ∨
      g * x * g⁻¹ ∈ zpowers e₂ ∨ g * x * g⁻¹ ∈ zpowers e₃ by
    exact ⟨t, e₂, e₃, htP, he₂, he₃, ht3x, he₂D, he₃D, hx3', hx3'', he₂1, he₃1, hc2x, hc3x, hc23,
      hind23, hindx, hlines⟩
  intro g hgQ
  have hle : (zpowers x).map (MulAut.conj g).toMonoidHom ≤ Q := by
    rw [MonoidHom.map_zpowers]
    exact zpowers_le.mpr hgQ
  rcases hfus g hle with h1 | h1
  · left
    have : g * x * g⁻¹ ∈ (zpowers x).map (MulAut.conj g).toMonoidHom := ⟨x, mem_zpowers x, rfl⟩
    rwa [h1] at this
  · right
    have hzJ : g * x * g⁻¹ ∈ J :=
      h1 (⟨x, mem_zpowers x, rfl⟩ : g * x * g⁻¹ ∈ (zpowers x).map (MulAut.conj g).toMonoidHom)
    have hzT : g * x * g⁻¹ ∈ zpowers e₂ ⊔ zpowers e₃ := by
      rw [hTD]; exact ⟨hQP hgQ, hzJ⟩
    obtain ⟨u, hu, v, hv, huv⟩ := u3l42_decomp hcomm_pair hzT
    obtain ⟨a, rfl⟩ := mem_zpowers_iff.mp hu
    obtain ⟨b, rfl⟩ := mem_zpowers_iff.mp hv
    have hzt : t * (g * x * g⁻¹) * t⁻¹ = (t * g) * x * (t * g)⁻¹ := by group
    have htz : t * (g * x * g⁻¹) * t⁻¹ = e₃ ^ a * x ^ b := by
      have e : t * (e₂ ^ a * e₃ ^ b) * t⁻¹ = (t * e₂ ^ a * t⁻¹) * (t * e₃ ^ b * t⁻¹) := by group
      rw [huv, e, ← conj_zpow, ← conj_zpow, ← he₃, ht3x]
    have hztQ : t * (g * x * g⁻¹) * t⁻¹ ∈ Q := hconjQ t htP _ hgQ
    have hle' : (zpowers x).map (MulAut.conj (t * g)).toMonoidHom ≤ Q := by
      rw [MonoidHom.map_zpowers]
      refine zpowers_le.mpr ?_
      show (t * g) * x * (t * g)⁻¹ ∈ Q
      rw [← hzt]; exact hztQ
    have he₃a : ∀ c : ℤ, e₃ ^ c ∈ J := fun c => J.zpow_mem he₃J c
    rcases hfus (t * g) hle' with h2 | h2
    ·
      have hmem : (t * g) * x * (t * g)⁻¹ ∈ zpowers x := by
        have : (t * g) * x * (t * g)⁻¹ ∈ (zpowers x).map (MulAut.conj (t * g)).toMonoidHom :=
          ⟨x, mem_zpowers x, rfl⟩
        rwa [h2] at this
      rw [← hzt, htz] at hmem
      have h3 : e₃ ^ a ∈ zpowers x := by
        have : e₃ ^ a = (e₃ ^ a * x ^ b) * (x ^ b)⁻¹ := by group
        rw [this]
        exact mul_mem hmem (inv_mem (zpow_mem_zpowers x b))
      obtain ⟨c, hc⟩ := mem_zpowers_iff.mp h3
      have h4 : x ^ c = 1 := hxJ' c (hc ▸ he₃a a)
      have h5 : e₃ ^ a = 1 := by rw [← hc, h4]
      have h6 := a6vi_zpow_eq_of_three (orderOf_eq_prime hx3'' he₃1) (h5.trans (zpow_zero e₃).symm)
      have h7 : e₂ ^ a = 1 := by
        have := a6vi_zpow_eq_of_dvd hx3' (a := a) (b := 0) (by simpa using h6)
        rw [this, zpow_zero]
      rw [huv, h7, one_mul]
      exact Or.inr (zpow_mem_zpowers e₃ b)
    · have hmem : (t * g) * x * (t * g)⁻¹ ∈ J :=
        h2 (⟨x, mem_zpowers x, rfl⟩ :
          (t * g) * x * (t * g)⁻¹ ∈ (zpowers x).map (MulAut.conj (t * g)).toMonoidHom)
      rw [← hzt, htz] at hmem
      have h3 : x ^ b ∈ J := by
        have : x ^ b = (e₃ ^ a)⁻¹ * (e₃ ^ a * x ^ b) := by group
        rw [this]
        exact J.mul_mem (J.inv_mem (he₃a a)) hmem
      have h4 := hxJ' b h3
      have h5 := a6vi_zpow_eq_of_three (orderOf_eq_prime hx3 hx1) (h4.trans (zpow_zero x).symm)
      have h7 : e₃ ^ b = 1 := by
        have := a6vi_zpow_eq_of_dvd hx3'' (a := b) (b := 0) (by simpa using h5)
        rw [this, zpow_zero]
      rw [huv, h7, mul_one]
      exact Or.inl (zpow_mem_zpowers e₂ a)

theorem three_not_dvd_sq_add_one (a : ℤ) : ¬ (3 : ℤ) ∣ a * a + 1 := by
  intro h
  have h0 := Int.mul_emod a a 3
  have : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  rcases this with h1 | h1 | h1 <;> rw [h1] at h0 <;> omega

theorem rot_arith {a b : ℤ} (ha : ¬ (3 : ℤ) ∣ a) (hab : (3 : ℤ) ∣ b * a + 1) :
    (a % 3 = 1 ∧ b % 3 = 2) ∨ (a % 3 = 2 ∧ b % 3 = 1) := by
  have h0 := Int.mul_emod b a 3
  have : a % 3 = 1 ∨ a % 3 = 2 := by omega
  rcases this with h1 | h1 <;> rw [h1] at h0 <;> omega

theorem vi_rotation {D J : Subgroup G} {x e₂ e₃ t ρ : G} (he₂D : e₂ ∈ D) (he₃D : e₃ ∈ D)
    (hDJ : D ≤ J) (hxJ' : ∀ b : ℤ, x ^ b ∈ J → x ^ b = 1)
    (hlines : ∀ g : G, g * x * g⁻¹ ∈ D → g * x * g⁻¹ ∈ zpowers x ∨ g * x * g⁻¹ ∈ zpowers e₂ ∨
      g * x * g⁻¹ ∈ zpowers e₃)
    (he₂ : e₂ = t * x * t⁻¹) (he₃ : e₃ = t * e₂ * t⁻¹)
    (he₂3 : e₂ ^ 3 = 1) (he₃3 : e₃ ^ 3 = 1) (he₂1 : e₂ ≠ 1) (he₃1 : e₃ ≠ 1)
    (hind : zpowers e₂ ⊓ zpowers e₃ = ⊥)
    (hρN : ρ ∈ normalizer (D : Set G)) (hrot : ∀ a ∈ D, ρ * (ρ * a * ρ⁻¹) * ρ⁻¹ = a⁻¹) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ρ * e₂ * ρ⁻¹ = e₃ ^ s ∧ ρ * e₃ * ρ⁻¹ = e₂ ^ (-s) := by
  have hD2 : ρ * e₂ * ρ⁻¹ ∈ D := (mem_normalizer_iff.mp hρN e₂).mp he₂D
  have hD3 : ρ * e₃ * ρ⁻¹ ∈ D := (mem_normalizer_iff.mp hρN e₃).mp he₃D
  have hc2 : ρ * e₂ * ρ⁻¹ = (ρ * t) * x * (ρ * t)⁻¹ := by rw [he₂]; group
  have hc3 : ρ * e₃ * ρ⁻¹ = (ρ * (t * t)) * x * (ρ * (t * t))⁻¹ := by rw [he₃, he₂]; group
  have hnot1 : ∀ z : G, ρ * z * ρ⁻¹ = 1 → z = 1 := by
    intro z hz
    have : z = ρ⁻¹ * (ρ * z * ρ⁻¹) * ρ := by group
    rw [this, hz]; group
  have hz2 := hlines (ρ * t) (by rw [← hc2]; exact hD2)
  have hz3 := hlines (ρ * (t * t)) (by rw [← hc3]; exact hD3)
  rw [← hc2] at hz2
  rw [← hc3] at hz3
  have hxl : ∀ z ∈ D, z ∈ zpowers x → z = 1 := by
    intro z hzD hzx
    obtain ⟨b, rfl⟩ := mem_zpowers_iff.mp hzx
    exact hxJ' b (hDJ hzD)
  have ho2 : orderOf e₂ = 3 := orderOf_eq_prime he₂3 he₂1
  have ho3 : orderOf e₃ = 3 := orderOf_eq_prime he₃3 he₃1
  have zrep : ∀ {e z : G}, z ∈ zpowers e → ∃ k : ℤ, z = e ^ k := fun h =>
    (mem_zpowers_iff.mp h).imp fun _ hk => hk.symm
  obtain ⟨a, ha⟩ : ∃ a : ℤ, ρ * e₂ * ρ⁻¹ = e₃ ^ a := by
    rcases hz2 with h | h | h
    · exact absurd (hnot1 e₂ (hxl _ hD2 h)) he₂1
    · obtain ⟨a, ha⟩ := zrep h
      exfalso
      have hr := hrot e₂ he₂D
      have h1 : ρ * (ρ * e₂ * ρ⁻¹) * ρ⁻¹ = e₂ ^ (a * a) := by
        calc ρ * (ρ * e₂ * ρ⁻¹) * ρ⁻¹ = ρ * e₂ ^ a * ρ⁻¹ := by rw [← ha]
          _ = (ρ * e₂ * ρ⁻¹) ^ a := (conj_zpow (i := a) (a := ρ) (b := e₂)).symm
          _ = (e₂ ^ a) ^ a := by rw [← ha]
          _ = e₂ ^ (a * a) := by rw [← zpow_mul]
      rw [h1] at hr
      have h2 : e₂ ^ (a * a) = e₂ ^ (-1 : ℤ) := by rw [hr, zpow_neg_one]
      have := a6vi_zpow_eq_of_three ho2 h2
      exact three_not_dvd_sq_add_one a (by simpa [sub_neg_eq_add] using this)
    · exact zrep h
  obtain ⟨b, hb⟩ : ∃ b : ℤ, ρ * e₃ * ρ⁻¹ = e₂ ^ b := by
    rcases hz3 with h | h | h
    · exact absurd (hnot1 e₃ (hxl _ hD3 h)) he₃1
    · exact zrep h
    · exfalso
      obtain ⟨c, hc⟩ := zrep h
      have hr := hrot e₂ he₂D
      have h1 : ρ * (ρ * e₂ * ρ⁻¹) * ρ⁻¹ = e₃ ^ (c * a) := by
        calc ρ * (ρ * e₂ * ρ⁻¹) * ρ⁻¹ = ρ * e₃ ^ a * ρ⁻¹ := by rw [ha]
          _ = (ρ * e₃ * ρ⁻¹) ^ a := (conj_zpow (i := a) (a := ρ) (b := e₃)).symm
          _ = (e₃ ^ c) ^ a := by rw [hc]
          _ = e₃ ^ (c * a) := by rw [← zpow_mul]
      rw [h1] at hr
      have hmem : e₂ ∈ zpowers e₂ ⊓ zpowers e₃ := by
        refine Subgroup.mem_inf.mpr ⟨mem_zpowers e₂, ?_⟩
        have : e₂ = (e₃ ^ (c * a))⁻¹ := by rw [hr, inv_inv]
        rw [this]
        exact inv_mem (zpow_mem_zpowers e₃ _)
      rw [hind] at hmem
      exact he₂1 (mem_bot.mp hmem)
  have hr := hrot e₂ he₂D
  have h1 : ρ * (ρ * e₂ * ρ⁻¹) * ρ⁻¹ = e₂ ^ (b * a) := by
    calc ρ * (ρ * e₂ * ρ⁻¹) * ρ⁻¹ = ρ * e₃ ^ a * ρ⁻¹ := by rw [ha]
      _ = (ρ * e₃ * ρ⁻¹) ^ a := (conj_zpow (i := a) (a := ρ) (b := e₃)).symm
      _ = (e₂ ^ b) ^ a := by rw [hb]
      _ = e₂ ^ (b * a) := by rw [← zpow_mul]
  rw [h1] at hr
  have h2 : e₂ ^ (b * a) = e₂ ^ (-1 : ℤ) := by rw [hr, zpow_neg_one]
  have h3 := a6vi_zpow_eq_of_three ho2 h2
  have hna : ¬ (3 : ℤ) ∣ a := by
    intro hdvd
    have h4 : ρ * e₂ * ρ⁻¹ = 1 := by
      rw [ha, a6vi_zpow_eq_of_dvd he₃3 (a := a) (b := 0) (by simpa using hdvd), zpow_zero]
    exact he₂1 (hnot1 e₂ h4)
  have harith := rot_arith hna (by simpa [sub_neg_eq_add] using h3)
  rcases harith with ⟨h5, h6⟩ | ⟨h5, h6⟩
  · refine ⟨1, Or.inl rfl, ?_, ?_⟩
    · rw [ha]; exact a6vi_zpow_eq_of_dvd he₃3 (by omega)
    · rw [hb]; exact a6vi_zpow_eq_of_dvd he₂3 (by omega)
  · refine ⟨-1, Or.inr rfl, ?_, ?_⟩
    · rw [ha]; exact a6vi_zpow_eq_of_dvd he₃3 (by omega)
    · rw [hb]; exact a6vi_zpow_eq_of_dvd he₂3 (by omega)

theorem exists_conj_into_P {P : Sylow 3 G} {O K₁ : Subgroup G}
    (hPO : (P : Subgroup G) ≤ normalizer (O : Set G)) (hK₁W : K₁ ≤ (P : Subgroup G) ⊔ O)
    (hK₁p : IsPGroup 3 K₁) : ∃ o ∈ O, ∀ y ∈ K₁, o * y * o⁻¹ ∈ (P : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set W : Subgroup G := (P : Subgroup G) ⊔ O with hW
  have hPsylW : IsSylowOf 3 (P : Subgroup G) W :=
    isSylowOf_iff.mpr ⟨le_sup_left, P.isPGroup', fun hdvd => P.not_dvd_index
      (hdvd.trans (Subgroup.relIndex_dvd_index_of_le le_sup_left))⟩
  obtain ⟨Q, hQ⟩ := (hK₁p.comap_subtype (K := W)).exists_le_sylow
  set T : Subgroup G := (Q : Subgroup W).map W.subtype with hT
  have hTsyl : IsSylowOf 3 T W := ⟨Q, rfl⟩
  have hK₁T : K₁ ≤ T := fun y hy => ⟨⟨y, hK₁W hy⟩, hQ hy, rfl⟩
  obtain ⟨k, hkW, hk⟩ := hTsyl.exists_mem_conj hPsylW
  have hkmul : k ∈ ((P : Subgroup G) : Set G) * (O : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (P : Subgroup G) O hPO]
    exact hkW
  obtain ⟨p, hpP, o, hoO, rfl⟩ := hkmul
  refine ⟨o, hoO, fun y hy => ?_⟩
  have h1 : (p * o)⁻¹ * (p * o * y * (p * o)⁻¹) * (p * o) ∈ T := by
    rw [show (p * o)⁻¹ * (p * o * y * (p * o)⁻¹) * (p * o) = y by group]
    exact hK₁T hy
  have h2 : p * o * y * (p * o)⁻¹ ∈ (P : Subgroup G) := (hk _).mpr h1
  have h3 : o * y * o⁻¹ = p⁻¹ * (p * o * y * (p * o)⁻¹) * p := by group
  rw [h3]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hpP) h2) hpP

theorem vi_QO_norm {P : Sylow 3 G} {M O D : Subgroup G} {x e₂ e₃ t : G}
    (φ : (P : Subgroup G) ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)))
    (hPM : (P : Subgroup G) ≤ M) (hMO : M ≤ normalizer (O : Set G))
    (hQP : Qf x e₂ e₃ ≤ (P : Subgroup G)) (hQel : IsElemAbelian 3 (Qf x e₂ e₃))
    (hQcard : Nat.card (Qf x e₂ e₃) = 27)
    (hC1 : ∀ m ∈ M, ∀ q ∈ D, m * q * m⁻¹ ∈ (P : Subgroup G) ⊔ O)
    (he₂D : e₂ ∈ D) (he₃D : e₃ ∈ D) (htP : t ∈ (P : Subgroup G)) (ht3 : t * e₃ * t⁻¹ = x) :
    M ≤ normalizer ((Qf x e₂ e₃ ⊔ O : Subgroup G) : Set G) := by
  have hf3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPO : (P : Subgroup G) ≤ normalizer (O : Set G) := hPM.trans hMO
  have htM : t ∈ M := hPM htP
  have hxQ : x ∈ Qf x e₂ e₃ := mem_sup_left (mem_zpowers x)
  have h2Q : e₂ ∈ Qf x e₂ e₃ := mem_sup_right (mem_sup_left (mem_zpowers e₂))
  have h3Q : e₃ ∈ Qf x e₂ e₃ := mem_sup_right (mem_sup_right (mem_zpowers e₃))
  have hQM : Qf x e₂ e₃ ≤ M := hQP.trans hPM
  have hQcomm : IsMulCommutative (Qf x e₂ e₃) := hQel.1
  have hconj : ∀ m ∈ M, ∀ q ∈ Qf x e₂ e₃, m * q * m⁻¹ ∈ (P : Subgroup G) ⊔ O := by
    intro m hm q hq
    have hle : Qf x e₂ e₃ ≤ ((P : Subgroup G) ⊔ O).comap (MulAut.conj m).toMonoidHom := by
      refine sup_le (zpowers_le.mpr ?_) (sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_))
      · show m * x * m⁻¹ ∈ ((P : Subgroup G) ⊔ O)
        rw [← ht3, show m * (t * e₃ * t⁻¹) * m⁻¹ = (m * t) * e₃ * (m * t)⁻¹ by group]
        exact hC1 _ (M.mul_mem hm htM) e₃ he₃D
      · show m * e₂ * m⁻¹ ∈ ((P : Subgroup G) ⊔ O)
        exact hC1 m hm e₂ he₂D
      · show m * e₃ * m⁻¹ ∈ ((P : Subgroup G) ⊔ O)
        exact hC1 m hm e₃ he₃D
    exact hle hq
  have hstar : ∀ m ∈ M, ∀ a ∈ Qf x e₂ e₃, m * a * m⁻¹ ∈ Qf x e₂ e₃ ⊔ O := by
    intro m hm a ha
    set K₁ : Subgroup G := (Qf x e₂ e₃).map (MulAut.conj m).toMonoidHom with hK₁
    have hK₁W : K₁ ≤ (P : Subgroup G) ⊔ O := by
      rintro _ ⟨k, hk, rfl⟩
      exact hconj m hm k hk
    have hK₁p : IsPGroup 3 K₁ := (elementary_isPGroup 3 _ hQel).map (MulAut.conj m).toMonoidHom
    obtain ⟨o, hoO, hoy⟩ := exists_conj_into_P hPO hK₁W hK₁p
    set K₂ : Subgroup G := (Qf x e₂ e₃).map (MulAut.conj (o * m)).toMonoidHom with hK₂
    have hK₂P : K₂ ≤ (P : Subgroup G) := by
      rintro _ ⟨k, hk, rfl⟩
      have := hoy _ ⟨k, hk, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using this
    have hK₂comm : IsMulCommutative K₂ := Subgroup.map_isMulCommutative _ _
    have hK₂c : Nat.card K₂ = 27 := by
      rw [hK₂, Subgroup.card_map_of_injective (MulAut.conj (o * m)).injective]
      exact hQcard
    have hK₂Q : K₂ = Qf x e₂ e₃ := abelian27_unique φ hK₂P hQP hK₂comm hQcomm hK₂c hQcard
    have hg : (o * m) * a * (o * m)⁻¹ ∈ Qf x e₂ e₃ := by
      rw [← hK₂Q]
      exact ⟨a, ha, rfl⟩
    obtain ⟨a', ha'K, ha'eq⟩ : ∃ a' ∈ Qf x e₂ e₃, a' = (o * m) * a * (o * m)⁻¹ := ⟨_, hg, rfl⟩
    have hmam : m * a * m⁻¹ = o⁻¹ * a' * o := by
      rw [ha'eq]
      group
    have hOnorm : ∀ g ∈ M, ∀ w ∈ O, g * w * g⁻¹ ∈ O := fun g hg w hw =>
      (mem_normalizer_iff.mp (hMO hg) w).mp hw
    have h4 : a'⁻¹ * o⁻¹ * a' ∈ O := by
      have := hOnorm a'⁻¹ (M.inv_mem (hQM ha'K)) o⁻¹ (O.inv_mem hoO)
      simpa using this
    have h5 : o⁻¹ * a' * o = a' * (a'⁻¹ * o⁻¹ * a') * o := by group
    rw [hmam, h5]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (mem_sup_left ha'K) (mem_sup_right h4))
      (mem_sup_right hoO)
  have hmap : ∀ m ∈ M, ∀ y ∈ Qf x e₂ e₃ ⊔ O, m * y * m⁻¹ ∈ Qf x e₂ e₃ ⊔ O := by
    intro m hm y hy
    have hle : (Qf x e₂ e₃ ⊔ O).map (MulAut.conj m).toMonoidHom ≤ Qf x e₂ e₃ ⊔ O := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨k, hk, rfl⟩
        exact hstar m hm k hk
      · rintro _ ⟨o', ho', rfl⟩
        exact mem_sup_right ((mem_normalizer_iff.mp (hMO hm) o').mp ho')
    exact hle ⟨y, hy, rfl⟩
  intro m hm
  rw [mem_normalizer_iff]
  intro y
  refine ⟨fun hy => hmap m hm y hy, fun hy => ?_⟩
  have h1 := hmap m⁻¹ (M.inv_mem hm) _ hy
  have e : m⁻¹ * (m * y * m⁻¹) * m⁻¹⁻¹ = y := by group
  rwa [e] at h1

section Plane

variable {G : Type} [Group G] [Finite G]

theorem vi_plane_inV {P : Sylow 3 G} {x e₂ e₃ : G} {J : Subgroup G} (hT : VITriple x e₂ e₃)
    (hxJ : x ∉ J) (hxP : x ∈ (P : Subgroup G)) (he₂D : e₂ ∈ (P : Subgroup G) ⊓ J)
    (he₃D : e₃ ∈ (P : Subgroup G) ⊓ J) (hJC : J ≤ centralizer ({x} : Set G))
    (hlines : ∀ g : G, g * x * g⁻¹ ∈ (P : Subgroup G) ⊓ centralizer ({x} : Set G) →
      g * x * g⁻¹ ∈ zpowers x ∨ g * x * g⁻¹ ∈ zpowers e₂ ∨ g * x * g⁻¹ ∈ zpowers e₃) :
    A6InV 3 P J x (zpowers x ⊔ zpowers (e₂ * e₃)) := by
  have hf3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxQ : x ∈ Qf x e₂ e₃ := mem_sup_left (mem_zpowers x)
  have h2Q : e₂ ∈ Qf x e₂ e₃ := mem_sup_right (mem_sup_left (mem_zpowers e₂))
  have h3Q : e₃ ∈ Qf x e₂ e₃ := mem_sup_right (mem_sup_right (mem_zpowers e₃))
  have hQfQ : Qf x e₂ e₃ ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G) := by
    have hDQ : (P : Subgroup G) ⊓ J ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G) :=
      le_inf inf_le_left (inf_le_right.trans hJC)
    exact sup_le (zpowers_le.mpr ⟨hxP, mem_centralizer_singleton_iff.mpr rfl⟩)
      (sup_le (zpowers_le.mpr (hDQ he₂D)) (zpowers_le.mpr (hDQ he₃D)))
  set w : G := e₂ * e₃ with hw
  have hwQ : w ∈ Qf x e₂ e₃ := mul_mem h2Q h3Q
  have hw3 : w ^ 3 = 1 := hT.Q_exp w hwQ
  have hw1 : w ≠ 1 := by
    intro h1
    have h2 : e₂ = e₃⁻¹ := eq_inv_of_mul_eq_one_left h1
    have : e₂ ∈ zpowers e₂ ⊓ zpowers e₃ :=
      Subgroup.mem_inf.mpr ⟨mem_zpowers e₂, h2 ▸ inv_mem (mem_zpowers e₃)⟩
    rw [hT.ind_23] at this
    exact hT.e₂_ne (mem_bot.mp this)
  have hwT : w ∈ zpowers e₂ ⊔ zpowers e₃ := mul_mem_sup (mem_zpowers e₂) (mem_zpowers e₃)
  have hwnx : w ∉ zpowers x := by
    intro hwx
    have : w ∈ (zpowers e₂ ⊔ zpowers e₃) ⊓ zpowers x := Subgroup.mem_inf.mpr ⟨hwT, hwx⟩
    rw [hT.ind_x] at this
    exact hw1 (mem_bot.mp this)
  have hxw : ∀ a ∈ zpowers x, ∀ b ∈ zpowers w, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
    exact ((show Commute x w from hT.Q_comm x hxQ w hwQ).zpow_zpow i j).eq
  have hUQ : zpowers x ⊔ zpowers w ≤ Qf x e₂ e₃ := sup_le (zpowers_le.mpr hxQ) (zpowers_le.mpr hwQ)
  refine ⟨hUQ.trans hQfQ, isElemAbelian_sup (isElemAbelian_zpowers hT.x_pow)
    (isElemAbelian_zpowers hw3) hxw, ?_, mem_sup_left (mem_zpowers x), ?_⟩
  · have hcx : Nat.card (zpowers x) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hT.x_pow hT.x_ne]
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three (zpowers x) hw3 hwnx
      (fun e he => hxw e he w (mem_zpowers w)), hcx]
    norm_num
  · intro g hg
    have hwJ : w ∈ J := J.mul_mem (he₂D.2) (he₃D.2)
    have hwU : w ∈ zpowers x ⊔ zpowers w := mem_sup_right (mem_zpowers w)
    have hwmem : w ∈ (zpowers x).map (MulAut.conj g).toMonoidHom := by
      rw [hg]; exact ⟨hwU, hwJ⟩
    rw [MonoidHom.map_zpowers] at hwmem
    have hgx : g * x * g⁻¹ ∈ zpowers x ⊔ zpowers w := by
      have : g * x * g⁻¹ ∈ (zpowers x).map (MulAut.conj g).toMonoidHom := ⟨x, mem_zpowers x, rfl⟩
      rw [hg] at this
      exact this.1
    have hgx1 : g * x * g⁻¹ ≠ 1 := by
      intro h1
      apply hT.x_ne
      have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [this, h1]; group
    have hgx3 : (g * x * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hT.x_pow, mul_one, mul_inv_cancel]
    have hlin := hlines g (hUQ.trans hQfQ hgx)
    have hwcyc : w ∈ zpowers (g * x * g⁻¹) := by simpa using hwmem
    have key : ∀ e : G, e ^ 3 = 1 → e ≠ 1 → g * x * g⁻¹ ∈ zpowers e → w ∈ zpowers e := by
      intro e he3 he1 hze
      have h1 := zpowers_eq_of_mem he3 he1 hze hgx1
      rw [← h1]; exact hwcyc
    rcases hlin with hl | hl | hl
    · exact hwnx (key x hT.x_pow hT.x_ne hl)
    · have hwe := key e₂ hT.e₂_pow hT.e₂_ne hl
      have : e₃ ∈ zpowers e₂ ⊓ zpowers e₃ := by
        refine Subgroup.mem_inf.mpr ⟨?_, mem_zpowers e₃⟩
        have : e₃ = e₂⁻¹ * w := by rw [hw]; group
        rw [this]
        exact mul_mem (inv_mem (mem_zpowers e₂)) hwe
      rw [hT.ind_23] at this
      exact hT.e₃_ne (mem_bot.mp this)
    · have hwe := key e₃ hT.e₃_pow hT.e₃_ne hl
      have : e₂ ∈ zpowers e₂ ⊓ zpowers e₃ := by
        refine Subgroup.mem_inf.mpr ⟨mem_zpowers e₂, ?_⟩
        have : e₂ = w * e₃⁻¹ := by rw [hw]; group
        rw [this]
        exact mul_mem hwe (inv_mem (mem_zpowers e₃))
      rw [hT.ind_23] at this
      exact hT.e₂_ne (mem_bot.mp this)

end Plane

section FrameConstruction

variable {G : Type} [Group G] [Finite G]

theorem a6vi_frame (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsA6Normal M x J)
    (h34S : A6Prop34S 3 P J x)
    (hnwc : ¬ LineWeaklyClosed x ((P : Subgroup G) ⊓ centralizer ({x} : Set G))) :
    ∃ (e₂ e₃ t ρ : G) (s : ℤ),
      A6VIFrame M (GLBPrimeCore 3 M) x e₂ e₃ t ρ s ∧
      Qf x e₂ e₃ = (P : Subgroup G) ⊓ centralizer ({x} : Set G) ∧
      ((∀ m ∈ M, ∀ q ∈ (P : Subgroup G) ⊓ J,
        m * q * m⁻¹ ∈ (P : Subgroup G) ⊔ GLBPrimeCore 3 M) →
        M ≤ normalizer ((Qf x e₂ e₃ ⊔ GLBPrimeCore 3 M : Subgroup G) : Set G)) ∧
      A6InV 3 P J x (zpowers x ⊔ zpowers (e₂ * e₃)) := by
  classical
  have hf3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA1 : A6SylowData := a6SylowData_proved
  obtain ⟨⟨hQab, -, hfus⟩, -, hShapeVI⟩ := h34S
  obtain ⟨hWr, -, hQc⟩ := hShapeVI hnwc
  obtain ⟨φ⟩ := hWr
  have hP81 : Nat.card (P : Subgroup G) = 81 := by
    rw [Nat.card_congr φ.toEquiv]
    exact CFSG.RankThree.PartTwo.Sec11.card_wreath
  have hQc27 : Nat.card ((P : Subgroup G) ⊓ centralizer ({x} : Set G) : Subgroup G) = 27 := by
    rw [hQc]; norm_num
  obtain ⟨hxP, hxLO, -, -⟩ := id hgen
  obtain ⟨hxM, hx1, hx3, -, -⟩ := id hxLO
  have hxJ : x ∉ J := a6_x_not_mem_J hS hU0 hp hM hgen hJ
  have hDcard : Nat.card ((P : Subgroup G) ⊓ J : Subgroup G) = 9 := by
    have := (a6_T_data hS hU0 hA1 hp hM hgen hJ).2.2
    rw [this]; norm_num
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hp hM).1
  obtain ⟨t, e₂, e₃, htP, he₂, he₃, ht3x, he₂D, he₃D, he₂3, he₃3, he₂1, he₃1, hc2x, hc3x, hc23,
    hind23, hindx, hlines⟩ := vi_lines P.isPGroup' hP81 hxP hx1 hx3 hxJ hQab hQc27 hDcard hfus
  have hxJ' : ∀ b : ℤ, x ^ b ∈ J → x ^ b = 1 := by
    intro b hb
    by_contra hb1
    apply hxJ
    have h1 := zpowers_eq_of_mem hx3 hx1 (zpow_mem_zpowers x b) hb1
    have hx' : x ∈ zpowers (x ^ b) := h1.symm ▸ mem_zpowers x
    exact (zpowers_le.mpr hb) hx'
  have hT : VITriple x e₂ e₃ :=
    { x_pow := hx3, e₂_pow := he₂3, e₃_pow := he₃3, x_ne := hx1, e₂_ne := he₂1, e₃_ne := he₃1
      comm_x₂ := hc2x.symm, comm_x₃ := hc3x.symm, comm_23 := hc23, ind_23 := hind23,
      ind_x := hindx }
  have hDQ : (P : Subgroup G) ⊓ J ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G) :=
    le_inf inf_le_left (inf_le_right.trans hJ.le_centralizer)
  have hQfQ : Qf x e₂ e₃ ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G) := by
    refine sup_le (zpowers_le.mpr ⟨hxP, mem_centralizer_singleton_iff.mpr rfl⟩)
      (sup_le (zpowers_le.mpr (hDQ he₂D)) (zpowers_le.mpr (hDQ he₃D)))
  have hO₂ne : pCoreOf 2 M ≠ ⊥ := by
    obtain ⟨S, hSne, hS2, hSM⟩ := hM.1.1
    have hSleM : S ≤ M := by rw [hSM]; exact Subgroup.le_normalizer
    intro hbot
    apply hSne
    rw [eq_bot_iff]
    have := normal_pGroup_le_pCoreOf 2 S M hSleM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hSleM).mpr hSM.le) hS2
    exact this.trans hbot.le
  obtain ⟨ρ, hρC, hρN, hρrot⟩ := a6_exists_rotation hgen hJ
  have hρM : ρ ∈ M := (a6l43_point_facts hS hU0 hA1 hp hM hgen hJ).1 hρN
  have hρx : ρ * x * ρ⁻¹ = x := by
    rw [mem_centralizer_singleton_iff.mp hρC]; group
  obtain ⟨s, hs, hρ₂, hρ₃⟩ := vi_rotation (D := (P : Subgroup G) ⊓ J) (J := J) he₂D he₃D
    inf_le_right hxJ' (fun g hg => hlines g (hDQ hg)) he₂ he₃ he₂3 he₃3 he₂1 he₃1 hind23 hρN
    hρrot
  have hframe : A6VIFrame M (GLBPrimeCore 3 M) x e₂ e₃ t ρ s :=
    { toVITriple := hT
      O_le := glbPrimeCore_le 3 M
      O_norm := le_normalizer_glbPrimeCore 3 M
      O_cop := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (glbPrimeCore_coprime 3 M)
      O₂_le := pCoreOf_le_glbPrimeCore Nat.prime_two (by norm_num) M
      O₂_ne := hO₂ne
      charTwo := hS.charTwo M hM.1.1
      D1 := fun Y₀ hne h2 hr =>
        le_of_three_le_pRank_inf hD1 hp hM ⟨Y₀, hne, h2, rfl⟩ hr
      x_mem := hxM
      e₂_mem := hPM he₂D.1
      e₃_mem := hPM he₃D.1
      t_mem := hPM htP
      t_x := he₂.symm
      t_e₂ := he₃.symm
      t_e₃ := ht3x
      ρ_mem := hρM
      ρ_x := hρx
      ρ_e₂ := hρ₂
      ρ_e₃ := hρ₃
      s_cases := hs
      lines := fun g hg => hlines g (hQfQ hg) }
  have hQeq : Qf x e₂ e₃ = (P : Subgroup G) ⊓ centralizer ({x} : Set G) :=
    Subgroup.eq_of_le_of_card_ge hQfQ (by rw [hT.Q_card, hQc27])
  refine ⟨e₂, e₃, t, ρ, s, hframe, hQeq, fun hC1 => ?_,
    vi_plane_inV hT hxJ hxP he₂D he₃D hJ.le_centralizer hlines⟩
  exact vi_QO_norm φ hPM (le_normalizer_glbPrimeCore 3 M) (hQfQ.trans inf_le_left)
    hT.Q_el hT.Q_card hC1 he₂D he₃D htP ht3x

end FrameConstruction


end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Aux

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.ABGLocalTools Subgroup CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Aux

@[expose] def A6VICase2 (G : Type) [Group G] [Finite G] : Prop :=
  GenericA6At G fun p P M x J => A6Prop34S p P J x →
    ¬ LineWeaklyClosed x ((P : Subgroup G) ⊓ centralizer ({x} : Set G)) →
    ¬ (∀ m ∈ M, ∀ q ∈ (P : Subgroup G) ⊓ J,
      m * q * m⁻¹ ∈ (P : Subgroup G) ⊔ GLBPrimeCore p M) →
    ∀ U : Subgroup G, A6InV p P J x U → ∀ Y : Subgroup G, IsPGroup 2 Y → Y ≤ M →
      U ≤ normalizer (Y : Set G) → IsSylowOf 2 (Y ⊓ GLBPrimeCore p M) (GLBPrimeCore p M) →
      ¬ Y ≤ normalizer
        ((((P : Subgroup G) ⊓ centralizer ({x} : Set G)) ⊔ GLBPrimeCore p M : Subgroup G) :
          Set G) →
      (∀ Y₀ : Subgroup G, Y₀ ≤ Y → Y₀ ≠ ⊥ → (Y₀.subgroupOf Y).Characteristic →
        CFSG.Open.pRank p (normalizer (Y₀ : Set G) ⊓ M) < 3) → False

theorem gl83P3A6_of_case2 {G : Type} [Group G] [Finite G] (hS : Setting G) (hD1 : TheoremD1 G)
    (hU0 : FullCoreLocal G) (hC2 : A6VICase2 G) : GL83GenericPrimeThreeA6Lemma43VI G := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ h34 hnwc
  subst hp3
  have hJ : IsA6Normal M x J :=
    ⟨hJC, hCJ, hperf, hnot, hlt, hmin, Q, inferInstance, ψ, hψ, hker, hQ⟩
  obtain ⟨e₂, e₃, t, ρ, s, hframe, hQeq, hQO, hU⟩ := a6vi_frame hS hU0 hD1 hp hM hgen hJ h34 hnwc
  refine ⟨zpowers x ⊔ zpowers (e₂ * e₃), hU, ?_⟩
  intro Y hY2 hYM hUY hYO
  by_cases hbig : ∃ Y₀ : Subgroup G, Y₀ ≤ Y ∧ Y₀ ≠ ⊥ ∧ (Y₀.subgroupOf Y).Characteristic ∧
      3 ≤ CFSG.Open.pRank 3 (normalizer (Y₀ : Set G) ⊓ M)
  · exact hframe.normalizer_le_of_big hY2 hbig
  · push Not at hbig
    by_cases hYN : Y ≤ normalizer ((Qf x e₂ e₃ ⊔ GLBPrimeCore 3 M : Subgroup G) : Set G)
    · exact (hframe.false_of_small hY2 hYM hYO hYN (hUY (mem_sup_left (mem_zpowers x)))
        (hUY (mem_sup_right (mem_zpowers _))) hbig).elim
    · have hC1 : ¬ ∀ m ∈ M, ∀ q ∈ (P : Subgroup G) ⊓ J,
          m * q * m⁻¹ ∈ (P : Subgroup G) ⊔ GLBPrimeCore 3 M :=
        fun hC1 => hYN (hYM.trans (hQO hC1))
      rw [hQeq] at hYN
      exact (hC2 3 hp P M hM hfail hIH x hgen rfl J hJC hCJ hperf hlt hmin hnot Q ψ hψ hker hQ h34
        hnwc hC1 _ hU Y hY2 hYM hUY hYO hYN hbig).elim

theorem gl83P3A6_holds :
    ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G → FullCoreLocal G →
      A6VICase2 G → GL83GenericPrimeThreeA6Lemma43VI G :=
  fun _ _ _ hS hD1 hU0 hC2 => gl83P3A6_of_case2 hS hD1 hU0 hC2

end CFSG.LocalAnalysis.RankThreeTheoremC
