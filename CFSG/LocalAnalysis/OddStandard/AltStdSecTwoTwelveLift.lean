module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecTwoRoot
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarHN
public import CFSG.Sporadic.HNSchreier.Intrinsic
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.Statements
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.OddStandard.AltStdBalOuter
public import CFSG.LocalAnalysis.OddStandard.Solomon75Goldschmidt
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Reduce
public import CFSG.Milestones.SG_two_signalizer_completeness
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.StronglyEmbedded.TheoremSE.BenderLowRank
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup

section Lift

variable {G : Type} [Group G] [Finite G]

theorem exists_lift_of_twoSec {x : G} (hx2 : x * x = 1) (hx1 : x ≠ 1) {y : G}
    (hy : y ∈ centralizer ({x} : Set G)) (hyodd : Odd (orderOf y))
    {T : Subgroup (TwoSec x)} (hT : IsPGroup 2 T)
    (hTy : T ≤ centralizer ({(QuotientGroup.mk ⟨y, hy⟩ : TwoSec x)} : Set (TwoSec x))) :
    ∃ P : Subgroup G, IsPGroup 2 P ∧ P ≤ centralizer ({x} : Set G) ∧
      P ≤ centralizer ({y} : Set G) ∧ Nat.card P = 2 * Nat.card T := by
  set N : Subgroup ↥(centralizer ({x} : Set G)) := zpowers (selfC x) with hN
  set That := T.comap (QuotientGroup.mk' N) with hThat
  set P : Subgroup G := That.map (centralizer ({x} : Set G)).subtype with hP
  have hNcard : Nat.card N = 2 := by
    rw [hN, Nat.card_zpowers]
    unfold selfC
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  have hPcard : Nat.card P = 2 * Nat.card T := by
    rw [hP, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hThat,
      card_comap_mk' N T, hNcard, mul_comm]
  refine ⟨P, ?_, ?_, ?_, hPcard⟩
  · obtain ⟨k, hk⟩ := hT.exists_card_eq
    exact IsPGroup.of_card (n := k + 1) (by rw [hPcard, hk, pow_succ]; ring)
  · rintro _ ⟨c, -, rfl⟩
    exact c.2
  · rintro _ ⟨c, hc, rfl⟩
    have hc' : (QuotientGroup.mk c : TwoSec x) ∈ T := hc
    have h1 := mem_centralizer_singleton_iff.1 (hTy hc')
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at h1
    have h2 := QuotientGroup.eq.1 h1
    have hyx : y * x = x * y := mem_centralizer_singleton_iff.1 hy
    rw [mem_centralizer_singleton_iff]
    rcases (mem_zpowers_selfC_iff hx2).1 h2 with h3 | h3
    · have h4 : ((c : G) * y)⁻¹ * (y * c) = 1 := h3
      exact inv_mul_eq_one.1 h4
    · exfalso
      have h4 : ((c : G) * y)⁻¹ * (y * c) = x := h3
      have e1 : (c : G)⁻¹ * y * c = y * x := by
        calc (c : G)⁻¹ * y * c = (c : G)⁻¹ * (((c : G) * y) * (((c : G) * y)⁻¹ * (y * c))) := by
              group
          _ = y * x := by rw [h4]; group
      obtain ⟨k, hk⟩ := hyodd
      have hy1 : y ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one y
      have hx' : x ^ (2 * k + 1) = x := by
        rw [pow_succ, pow_mul, pow_two, hx2, one_pow, one_mul]
      have hp1 : ((c : G)⁻¹ * y * c) ^ (2 * k + 1) = 1 := by
        have hconj := conj_pow (a := (c : G)⁻¹) (b := y) (i := 2 * k + 1)
        rw [inv_inv] at hconj
        rw [hconj, hy1, mul_one, inv_mul_cancel]
      rw [e1, (show Commute y x from hyx).mul_pow, hy1, one_mul, hx'] at hp1
      exact hx1 hp1

end Lift

section Wreath

variable {X : Type} [Group X] [Finite X]

theorem exists_two_subgroup_of_wreath {t : X} {A : Subgroup X} {m : ℕ} (hm : 4 ≤ m)
    (hW : WreathOutcome t A m) {r : X} (hr : r ∈ A) {D : Subgroup X} (hDA : D ≤ A)
    (hDr : D ≤ centralizer ({r} : Set X)) {k : ℕ} (hk : 2 ^ k ∣ Nat.card D) :
    ∃ T : Subgroup X, IsPGroup 2 T ∧ T ≤ centralizer ({r} : Set X) ∧ Nat.card T = 2 ^ (2 * k) := by
  classical
  obtain ⟨K, hKc, hKne, -, ⟨eK⟩, hdiag⟩ := hW
  set K' : Subgroup X := K.map (MulAut.conj t).toMonoidHom with hK'
  have hK'c : CFSG.IsComponent K' := CFSG.LocalCores.isComponent_map_mulEquiv _ hKc
  have hc : ⁅K, K'⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hKc hK'c).resolve_left fun h => hKne h.symm
  have hKK' : K ≤ centralizer (K' : Set X) := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc
  have hcomm : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.1 (hKK' ha) b hb).symm
  have hcen : center K = ⊥ := center_eq_bot_of_alt hm eK
  have hconjK' : ∀ a ∈ K, t * a * t⁻¹ ∈ K' := fun a ha => ⟨a, ha, by simp [MulAut.conj_apply]⟩
  have hKK'bot : ∀ a ∈ K, a ∈ K' → a = 1 := by
    intro a ha ha'
    have hac : (⟨a, ha⟩ : K) ∈ center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcomm g g.2 a ha')
    rw [hcen, Subgroup.mem_bot] at hac
    exact congrArg Subtype.val hac
  set ψ : ↥K →* X :=
    { toFun := fun k => (k : X) * (t * k * t⁻¹)
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [Subgroup.coe_mul]
        have h1 := hcomm b b.2 _ (hconjK' a a.2)
        calc (a : X) * b * (t * (a * b) * t⁻¹) = a * (b * (t * a * t⁻¹)) * (t * b * t⁻¹) := by
              group
          _ = a * ((t * a * t⁻¹) * b) * (t * b * t⁻¹) := by rw [h1]
          _ = a * (t * a * t⁻¹) * (b * (t * b * t⁻¹)) := by group } with hψ
  have hψapp : ∀ k : ↥K, ψ k = (k : X) * (t * k * t⁻¹) := fun _ => rfl
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    rw [hψapp] at hk
    have h1 : (k : X) = (t * k * t⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left hk
    have h2 : (k : X) ∈ K' := by rw [h1]; exact inv_mem (hconjK' k k.2)
    exact Subtype.ext (hKK'bot k k.2 h2)
  have hψrange : ∀ a ∈ A, ∃ k : ↥K, ψ k = a := by
    intro a ha
    have ha' : a ∈ (A : Set X) := ha
    rw [hdiag] at ha'
    obtain ⟨k, hk, rfl⟩ := ha'
    exact ⟨⟨k, hk⟩, rfl⟩
  set D₁ : Subgroup ↥K := D.comap ψ with hD₁
  have hD₁card : Nat.card D₁ = Nat.card D := by
    have hle : D ≤ ψ.range := fun a ha => by
      obtain ⟨k, hk⟩ := hψrange a (hDA ha)
      exact ⟨k, hk⟩
    have h1 : D₁.map ψ = D := Subgroup.map_comap_eq_self hle
    rw [← h1, Subgroup.card_map_of_injective hψinj]
  obtain ⟨kr, hkr⟩ := hψrange r hr
  have hD₁r : ∀ d ∈ D₁, (d : X) * kr = kr * d := by
    intro d hd
    have hd' : ψ d ∈ D := hd
    have h1 := mem_centralizer_singleton_iff.1 (hDr hd')
    rw [← hkr, ← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (hψinj h1)
  have hcommr1 : ∀ d ∈ D₁, (d : X) * r = r * d := by
    intro d hd
    rw [← hkr, hψapp]
    have h1 := hD₁r d hd
    have h2 := hcomm d d.2 _ (hconjK' kr kr.2)
    calc (d : X) * (kr * (t * kr * t⁻¹)) = (d * kr) * (t * kr * t⁻¹) := by group
      _ = (kr * d) * (t * kr * t⁻¹) := by rw [h1]
      _ = kr * (d * (t * kr * t⁻¹)) := by group
      _ = kr * ((t * kr * t⁻¹) * d) := by rw [h2]
      _ = kr * (t * kr * t⁻¹) * d := by group
  have hcommr2 : ∀ d ∈ D₁, (t * d * t⁻¹) * r = r * (t * d * t⁻¹) := by
    intro d hd
    rw [← hkr, hψapp]
    have h1 := hD₁r d hd
    have h3 : (t * d * t⁻¹) * (t * kr * t⁻¹) = (t * kr * t⁻¹) * (t * d * t⁻¹) := by
      calc (t * d * t⁻¹) * (t * kr * t⁻¹) = t * ((d : X) * kr) * t⁻¹ := by group
        _ = t * ((kr : X) * d) * t⁻¹ := by rw [h1]
        _ = (t * kr * t⁻¹) * (t * d * t⁻¹) := by group
    have h2 := hcomm kr kr.2 _ (hconjK' d d.2)
    calc (t * d * t⁻¹) * (kr * (t * kr * t⁻¹)) = ((t * d * t⁻¹) * kr) * (t * kr * t⁻¹) := by group
      _ = (kr * (t * d * t⁻¹)) * (t * kr * t⁻¹) := by rw [h2]
      _ = kr * ((t * d * t⁻¹) * (t * kr * t⁻¹)) := by group
      _ = kr * ((t * kr * t⁻¹) * (t * d * t⁻¹)) := by rw [h3]
      _ = kr * (t * kr * t⁻¹) * (t * d * t⁻¹) := by group
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := Sylow.exists_subgroup_card_pow_prime 2 (hD₁card ▸ hk)
  set α : ↥P₀ →* X := K.subtype.comp (D₁.subtype.comp P₀.subtype) with hα
  set β : ↥P₀ →* X := (MulAut.conj t).toMonoidHom.comp α with hβ
  have hαK : ∀ p, α p ∈ K := fun p => ((p : ↥D₁) : ↥K).2
  have hβK' : ∀ p, β p ∈ K' := fun p => hconjK' _ (hαK p)
  have hβapp : ∀ p, β p = t * α p * t⁻¹ := fun p => by simp [hβ, MulAut.conj_apply]
  have hαβ : ∀ p q, Commute (α p) (β q) := fun p q => hcomm _ (hαK p) _ (hβK' q)
  set Φ := α.noncommCoprod β hαβ with hΦ
  have hαinj : Function.Injective α := (Subgroup.subtype_injective _).comp
    ((Subgroup.subtype_injective _).comp (Subgroup.subtype_injective _))
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨p, q⟩ hpq
    have h1 : α p * β q = 1 := hpq
    have h2 : α p = (β q)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : α p = 1 := hKK'bot _ (hαK p) (by rw [h2]; exact inv_mem (hβK' q))
    have hp : p = 1 := hαinj (h3.trans (map_one α).symm)
    have hq : β q = 1 := by rw [h3, one_mul] at h1; exact h1
    have hq' : q = 1 := by
      apply hαinj
      rw [hβapp] at hq
      rw [map_one]
      calc α q = t⁻¹ * (t * α q * t⁻¹) * t := by group
        _ = 1 := by rw [hq]; group
    exact Prod.ext hp hq'
  refine ⟨Φ.range, ?_, ?_, ?_⟩
  · refine IsPGroup.of_card (n := 2 * k) ?_
    rw [Nat.card_congr (MonoidHom.ofInjective hΦinj).toEquiv.symm, Nat.card_prod, hP₀, ← pow_add]
    ring_nf
  · rintro _ ⟨⟨p, q⟩, rfl⟩
    rw [mem_centralizer_singleton_iff]
    change α p * β q * r = r * (α p * β q)
    have h1 := hcommr1 _ ((p : ↥D₁)).2
    have h2 := hcommr2 _ ((q : ↥D₁)).2
    have h1' : α p * r = r * α p := h1
    have h2' : β q * r = r * β q := by rw [hβapp]; exact h2
    calc α p * β q * r = α p * (β q * r) := by group
      _ = α p * (r * β q) := by rw [h2']
      _ = (α p * r) * β q := by group
      _ = (r * α p) * β q := by rw [h1']
      _ = r * (α p * β q) := by group
  · rw [Nat.card_congr (MonoidHom.ofInjective hΦinj).toEquiv.symm, Nat.card_prod, hP₀, ← pow_add]
    ring_nf

end Wreath

section HN


set_option maxRecDepth 20000 in
open CFSG.Sporadic.HNSchreier CFSG.RankThree.PartOne.HNRed in
theorem card_centralizer_three_of_hn {W : Type*} [Group W] [Finite W]
    (e : W ≃* CFSG.Blueprint.NativeSporadic.HN) {x u : W} (hx : orderOf x = 3)
    (hu : orderOf u = 7) (hxu : x * u = u * x) :
    Nat.card (centralizer ({x} : Set W)) = 544320 := by
  have e' : W ≃* JH := e.trans hnEquivJ
  have hs' : orderOf (e' x) = 3 := by rw [MulEquiv.orderOf_eq]; exact hx
  have hcard := @card_centralizer_of_mulEquiv W ↥JH _ inferInstance e' x
  have h7 : 7 ∣ Nat.card (centralizer ({x} : Set W)) := by
    have hu' : u ∈ centralizer ({x} : Set W) := mem_centralizer_singleton_iff.2 hxu.symm
    have h1 := orderOf_dvd_natCard (⟨u, hu'⟩ : centralizer ({x} : Set W))
    rwa [Subgroup.orderOf_mk, hu] at h1
  rw [← hcard] at h7 ⊢
  have h544 : Nat.card (CJ (sJ 0)) = 544320 := card_CJ_s1
  have h29160 : Nat.card (CJ (sJ 2)) = 29160 := card_CJ_s3
  rcases (order_three_classes (e' x)).1 hs' with h | h
  · obtain ⟨c, hc⟩ := isConj_iff.1 h
    rw [← hc, card_centralizer_conj]
    exact h544
  · exfalso
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    rw [← hc, card_centralizer_conj, h29160] at h7
    revert h7
    decide

theorem exists_two_subgroup_of_hnOutcome {X : Type} [Group X] [Finite X] {t : X} (hHN : HNOutcome t)
    {r c : X} (hr : orderOf r = 3) (hc : orderOf c = 7) (hrc : r * c = c * r) :
    ∃ T : Subgroup X, IsPGroup 2 T ∧ T ≤ centralizer ({r} : Set X) ∧ Nat.card T = 2 ^ 6 := by
  obtain ⟨W, -, hWi, -, ⟨eW⟩⟩ := hHN
  have hrW : r ∈ W := mem_of_odd_of_index_two hWi (by rw [hr]; decide)
  have hcW : c ∈ W := mem_of_odd_of_index_two hWi (by rw [hc]; decide)
  have hC := card_centralizer_three_of_hn eW (x := ⟨r, hrW⟩) (u := ⟨c, hcW⟩)
    (by rw [Subgroup.orderOf_mk]; exact hr) (by rw [Subgroup.orderOf_mk]; exact hc)
    (Subtype.ext hrc)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₀, hT₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(centralizer
    ({(⟨r, hrW⟩ : W)} : Set W))) 2 (n := 6) (by rw [hC]; norm_num)
  set T : Subgroup X := (T₀.map (centralizer ({(⟨r, hrW⟩ : W)} : Set W)).subtype).map W.subtype
    with hT
  have hTcard : Nat.card T = 2 ^ 6 := by
    rw [hT, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hT₀]
  refine ⟨T, IsPGroup.of_card hTcard, ?_, hTcard⟩
  rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
  rw [mem_centralizer_singleton_iff]
  exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 w.2)

end HN

end CFSG.OddStandard.AltStdSec
