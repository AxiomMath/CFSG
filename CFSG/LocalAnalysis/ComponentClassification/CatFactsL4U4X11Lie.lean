module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4X11Ord
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBasic
public import CFSG.LocalAnalysis.ComponentClassification.PComponentNormalizerEnlargement
public import CFSG.ClassicalGroups.Symplectic.Simple
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X11R
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Sporadic.Presentation.Common
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate8033
public import Certificates.Certificate9130

public section

namespace CFSG.ComponentClassification.GSThmB.X11

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem lieSylowExponent_pos {t : StatedLieTag} {n p f : ℕ} (h : StatedLieAdmissible t n p f) :
    1 ≤ CatLeaf.lieSylowExponent t n ∧
      (CatLeaf.lieSylowExponent t n = 1 → t = .PSL ∧ n = 2) := by
  obtain ⟨-, -, h⟩ := h
  cases t <;> simp only [CatLeaf.lieSylowExponent] at h ⊢
  case PSL =>
    obtain ⟨hn, -⟩ := h
    have h1 : 2 ≤ n * (n - 1) := by
      calc 2 = 2 * 1 := rfl
        _ ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
    refine ⟨by omega, fun h1' => ⟨by trivial, ?_⟩⟩
    by_contra hne
    have h3 : 3 ≤ n := by omega
    have : 6 ≤ n * (n - 1) := by
      calc 6 = 3 * 2 := rfl
        _ ≤ n * (n - 1) := Nat.mul_le_mul h3 (by omega)
    omega
  case PSU =>
    obtain ⟨hn, -⟩ := h
    have : 6 ≤ n * (n - 1) := by
      calc 6 = 3 * 2 := rfl
        _ ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
    exact ⟨by omega, fun h1 => absurd h1 (by omega)⟩
  case PSp =>
    obtain ⟨hn, -⟩ := h
    have : 4 ≤ n ^ 2 := by nlinarith
    exact ⟨by omega, fun h1 => absurd h1 (by omega)⟩
  case POmegaOdd =>
    obtain ⟨hn, -⟩ := h
    have : 9 ≤ n ^ 2 := by nlinarith
    exact ⟨by omega, fun h1 => absurd h1 (by omega)⟩
  case POmegaPlus =>
    have : 12 ≤ n * (n - 1) := by
      calc 12 = 4 * 3 := rfl
        _ ≤ n * (n - 1) := Nat.mul_le_mul h (by omega)
    exact ⟨by omega, fun h1 => absurd h1 (by omega)⟩
  case POmegaMinus =>
    have : 12 ≤ n * (n - 1) := by
      calc 12 = 4 * 3 := rfl
        _ ≤ n * (n - 1) := Nat.mul_le_mul h (by omega)
    exact ⟨by omega, fun h1 => absurd h1 (by omega)⟩
  all_goals exact ⟨by norm_num, fun h1 => absurd h1 (by norm_num)⟩

theorem eq_three_of_card (hO : CatLeaf.LieOrderFormulasInput) {X : Type} [Group X]
    {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p f) (h : Blueprint.LieModel X t n p f)
    (hc : Nat.card X = 25920) : p = 3 := by
  obtain ⟨-, hord, hfac⟩ := hO X t n p f hadm h
  obtain ⟨hN1, hN⟩ := lieSylowExponent_pos hadm
  have hf : 1 ≤ f := hadm.2.1
  rw [hc] at hord hfac
  have hpos : 1 ≤ (25920 : ℕ).factorization p := by
    rw [hfac]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hdvd : p ∣ 25920 := Nat.dvd_of_factorization_pos (by omega)
  have h235 : p = 2 ∨ p = 3 ∨ p = 5 := by
    have e : (25920 : ℕ) = 2 ^ 6 * 3 ^ 4 * 5 := by norm_num
    rw [e] at hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
    · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
          (hp.dvd_of_dvd_pow h2))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
          (hp.dvd_of_dvd_pow h2)))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h1))
  rcases h235 with rfl | rfl | rfl
  · exact absurd rfl hp2
  · rfl
  · exfalso
    have h25 : ¬ 5 ^ 2 ∣ 25920 := by norm_num
    have hle : (25920 : ℕ).factorization 5 < 2 := by
      by_contra hcon
      exact h25 ((Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) (by norm_num)).mpr
        (by omega))
    have hNf : CatLeaf.lieSylowExponent t n * f = 1 := by
      have := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega : CatLeaf.lieSylowExponent t n
        ≠ 0) (by omega : f ≠ 0))
      omega
    have hN1' : CatLeaf.lieSylowExponent t n = 1 := Nat.eq_one_of_mul_eq_one_right hNf
    have hf1 : f = 1 := Nat.eq_one_of_mul_eq_one_left hNf
    obtain ⟨rfl, rfl⟩ := hN hN1'
    subst hf1
    rw [show CatLeaf.lieOrderDivisor .PSL 2 (5 ^ 1) = 2 by decide,
      show CatLeaf.lieOrderNumerator .PSL 2 (5 ^ 1) = 120 by decide] at hord
    omega

theorem center_eq_pPrimeCore {L : Type*} [Group L] [Finite L] (hq : IsQuasisimple L)
    (hO : pPrimeCore 2 L ≠ ⊤) (hZ : center (L ⧸ pPrimeCore 2 L) = ⊥) :
    center L = pPrimeCore 2 L := by
  apply le_antisymm
  · intro z hz
    have : (QuotientGroup.mk z : L ⧸ pPrimeCore 2 L) ∈ center (L ⧸ pPrimeCore 2 L) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp hz g]
    rw [hZ, mem_bot, QuotientGroup.eq_one_iff] at this
    exact this
  · exact (CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hq
      inferInstance).resolve_left hO

theorem center_eq_bot_of_perfect {X : Type*} [Group X] [IsSimpleGroup X]
    (hp : Group.IsPerfect X) : center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
  · exact h
  · exfalso
    have hc : commutator X = ⊥ := by
      rw [eq_bot_iff, commutator_def, commutator_le]
      intro x _ y _
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp (h ▸ mem_top y) x)]
      exact one_mem _
    have h1 : (⊤ : Subgroup X) = ⊥ := by
      rw [← hc]
      exact hp.commutator_eq_top.symm
    exact (IsSimpleGroup.toNontrivial (G := X)).exists_pair_ne.elim fun a ha =>
      ha.elim fun b hab => hab (by
        have ha' : a ∈ (⊥ : Subgroup X) := h1 ▸ mem_top a
        have hb' : b ∈ (⊥ : Subgroup X) := h1 ▸ mem_top b
        rw [mem_bot] at ha' hb'
        rw [ha', hb'])

variable {G : Type} [Group G] [Finite G] {N : Subgroup G}

theorem KConf.eq_three
    (hGLS : CatLeaf.GLS3OddLieAutComponentsInput)
    (hO : CatLeaf.LieOrderFormulasInput) (h : KConf G N) {t : StatedLieTag} {n p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hadm : StatedLieAdmissible t n p f)
    (hm : Blueprint.LieModel ↥N t n p f) : p = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hNn, hC, hs, b, K, hb, hKN, hKb, hKc, hKm⟩ := h
  have hcK : Nat.card (↥K ⧸ pPrimeCore 2 ↥K) = 25920 := card_of_lieModel_psp_four_three hKm
  let σ : MulAut ↥N := MulAut.conjNormal b
  have hσapp : ∀ y : ↥N, ((σ y : ↥N) : G) = b * (y : G) * b⁻¹ := fun y => rfl
  have hbb : b * b = 1 := by rw [← pow_two, ← hb, pow_orderOf_eq_one]
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => Subtype.ext (by
    change b * (b * (y : G) * b⁻¹) * b⁻¹ = y
    rw [hbi, ← mul_assoc, ← mul_assoc, hbb, one_mul, mul_assoc, hbb, mul_one])
  have hσ1 : σ ≠ 1 := by
    intro h1
    have hbC : b ∈ centralizer (N : Set G) := by
      rw [mem_centralizer_iff]
      intro x hx
      have h2 := congrArg (fun φ : MulAut ↥N => ((φ ⟨x, hx⟩ : ↥N) : G)) h1
      change b * x * b⁻¹ = x at h2
      calc x * b = b * x * b⁻¹ * b := by rw [h2]
        _ = b * x := by group
    rw [hC, mem_bot] at hbC
    rw [hbC, orderOf_one] at hb
    exact absurd hb (by norm_num)
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  have hfixmem : ∀ y : ↥N, y ∈ fixedSubgroup σ ↔ (y : G) ∈ centralizer ({b} : Set G) := by
    intro y
    change σ y = y ↔ _
    rw [mem_centralizer_singleton_iff, ← Subtype.coe_inj, hσapp]
    constructor
    · intro h
      calc (y : G) * b = b * (y : G) * b⁻¹ * b := by rw [h]
        _ = b * (y : G) := by group
    · intro h
      rw [← h, mul_inv_cancel_right]
  have hfix : (fixedSubgroup σ).map N.subtype = centralizer ({b} : Set G) ⊓ N := by
    ext x
    simp only [mem_map, mem_inf, subtype_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(hfixmem y).mp hy, y.2⟩
    · rintro ⟨hx, hxN⟩
      exact ⟨⟨x, hxN⟩, (hfixmem ⟨x, hxN⟩).mpr hx, rfl⟩
  have hK'F : K.subgroupOf N ≤ fixedSubgroup σ := fun y hy =>
    (hfixmem y).mpr (hKb (mem_subgroupOf.mp hy))
  set L := (K.subgroupOf N).subgroupOf (fixedSubgroup σ) with hLdef
  have hL : IsPComponent 2 L := by
    rw [hLdef, Burgoyne.isPComponent_subgroupOf_map_iff 2 Nat.prime_two N.subtype_injective,
      hfix, subgroupOf_map_subtype, inf_eq_left.mpr hKN]
    exact CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hKb hKN) inf_le_left hKc
  let eL : ↥L ≃* ↥K := (subgroupOfEquivOfLe hK'F).trans (subgroupOfEquivOfLe hKN)
  have eO : ↥L ⧸ pPrimeCore 2 ↥L ≃* ↥K ⧸ pPrimeCore 2 ↥K :=
    QuotientGroup.congr _ _ eL (pPrimeCore_map_iso 2 eL)
  have hcL : Nat.card (↥L ⧸ pPrimeCore 2 ↥L) = 25920 := (Nat.card_congr eO.toEquiv).trans hcK
  have hna : ∃ x y : ↥N, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    have hnorm : (K.subgroupOf N).Normal :=
      ⟨fun x hx g => by rwa [hcon g x, mul_inv_cancel_right]⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.subgroupOf N) with h1 | h1
    · have hK1 : Nat.card ↥K = 1 := by
        rw [← Nat.card_congr (subgroupOfEquivOfLe hKN).toEquiv, h1, card_bot]
      have := Subgroup.card_quotient_dvd_card (pPrimeCore 2 ↥K)
      rw [hcK, hK1] at this
      exact absurd (Nat.le_of_dvd one_pos this) (by norm_num)
    · apply hσ1
      refine MulEquiv.ext fun y => ?_
      have hy : y ∈ K.subgroupOf N := h1 ▸ mem_top y
      exact hK'F hy
  have hodd : Blueprint.OddLieType ↥N := ⟨t, n, p, f, hp, hp2, hadm, hm⟩
  have hq : IsQuasisimple ↥L :=
    CatLeaf.fixedTwoComponentsQuasisimple_of_oddLieType hna hodd σ hσσ hσ1 L hL
  have hcomp : IsComponent L := ⟨hq, hL.choose_spec.2.1⟩
  rcases hGLS ↥N t n p f hp hp2 hadm hm σ hσ2 L hcomp with ⟨t', n', f', hadm', hm'⟩ |
      ⟨hp3, -⟩
  ·
    have hO1 : pPrimeCore 2 ↥L ≠ ⊤ := by
      intro htop
      have h1 : (pPrimeCore 2 ↥L).index = 1 := Subgroup.index_eq_one.mpr htop
      have h2 : Nat.card (↥L ⧸ pPrimeCore 2 ↥L) = (pPrimeCore 2 ↥L).index := rfl
      omega
    have hsK : IsSimpleGroup (↥K ⧸ pPrimeCore 2 ↥K) :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ 2 3 1
        (GH74.statedClassicalModel_of_lieModel (by norm_num) hKm)
    have hsL : IsSimpleGroup (↥L ⧸ pPrimeCore 2 ↥L) := (MulEquiv.isSimpleGroup_congr eO).mpr hsK
    have hpL : Group.IsPerfect (↥L ⧸ pPrimeCore 2 ↥L) := by
      have hP := hq.1
      refine ⟨?_⟩
      have h := Subgroup.map_commutator (⊤ : Subgroup ↥L) ⊤ (QuotientGroup.mk' (pPrimeCore 2 ↥L))
      rw [show ⁅(⊤ : Subgroup ↥L), ⊤⁆ = ⊤ from hP.commutator_eq_top,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h
      exact h.symm
    have hZ := center_eq_bot_of_perfect hpL
    have hcZ : Nat.card (↥L ⧸ center ↥L) = 25920 := by
      rw [← hcL]
      exact Nat.card_congr (QuotientGroup.quotientMulEquivOfEq
        (center_eq_pPrimeCore hq hO1 hZ)).toEquiv
    exact eq_three_of_card hO hp hp2 hadm' hm' hcZ
  · exact hp3

end CFSG.ComponentClassification.GSThmB.X11
