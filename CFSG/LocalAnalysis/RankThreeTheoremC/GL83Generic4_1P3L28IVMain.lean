module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28WCDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28IVLines
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28IVYoshida
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28IVQP
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28IVCube
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28ShapeShear
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34f
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Lemma43E9Core
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Lemma42

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup

variable {G : Type} [Group G] [Finite G]

theorem l28iv_prop34S (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (K1 : StronglyEmbeddedRankTwoKFactNoBM) (K2 : StronglyEmbeddedCyclicOuterKFact)
    (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree) (hno : NoExcludedSection3 G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hL : KFactsL34Full) (hA1 : A6SylowData) (hA3 : A6BorelCore) (hE1 : KFactL28Three)
    (hE3 : KFactL28BorelCore) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G}
    (hJ : IsL28Normal M x J) : L28Prop34SNoWC 3 P J x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hxP, hxLO, hQsyl, -⟩ := id hgen
  obtain ⟨-, hx1, hx3, -, -⟩ := id hxLO
  have hxJ : x ∉ J := l28_x_not_mem_J hS hU0 hp hM hgen hJ
  have hJC := hJ.le_centralizer
  obtain ⟨hZQ, hxZ, hTZ, hcomm, hZc⟩ := l28iv_Z_facts hS hU0 hE1 hp hM hgen hJ
  obtain ⟨t₀, hT, ht₀⟩ := l28iv_T_cyclic hS hU0 hE1 hp hM hgen hJ
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set T : Subgroup G := (P : Subgroup G) ⊓ J with hTdef
  set Z : Subgroup G := l28ivZ P x J with hZdef
  set u : G := t₀ ^ 3 with hu
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have h9 : t₀ ^ 9 = 1 := by rw [← ht₀]; exact pow_orderOf_eq_one t₀
  have ht₀T : t₀ ∈ T := by rw [hT]; exact mem_zpowers t₀
  have huT : u ∈ T := by rw [hT]; exact pow_mem (mem_zpowers t₀) 3
  have hu3 : u ^ 3 = 1 := by rw [hu, ← pow_mul, show 3 * 3 = 9 from rfl, h9]
  have hu1 : u ≠ 1 := by
    intro h
    have := orderOf_le_of_pow_eq_one (by norm_num : 0 < 3) h
    omega
  have huo : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hxu : x ∉ zpowers u := fun h => hxJ (zpowers_le.mpr huT.2 h)
  have hTcyc : IsCyclic ↥T := by rw [hT]; infer_instance
  have hZT : ∀ z ∈ T, z ∈ Z → z = 1 := fun z hzT hzZ => by
    have : z ∈ T ⊓ Z := ⟨hzT, hzZ⟩
    rwa [hTZ, mem_bot] at this
  have hD := fun g hg => l28iv_conj_cases hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA1 hA3 hE1 hE3
    hp hM hgen hJ hT ht₀ (g := g) hg
  have hPC : (P : Subgroup G) ≤ C := l28iv_le_centralizer P.isPGroup' hxP hx3 hx1 hxu hu3 hD
  have hQP : (P : Subgroup G) ⊓ C = P := inf_eq_left.mpr hPC
  obtain ⟨g, hgQ, hgu⟩ : ∃ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤
      (P : Subgroup G) ⊓ C ∧ g * x * g⁻¹ ∈ zpowers u := by
    by_contra hno'
    push Not at hno'
    exact l28iv_false_of_wc hS hU0 hE1 hp hM hgen hJ fun g hg =>
      (hD g hg).resolve_right (hno' g hg)
  set y₀ : G := g * x * g⁻¹ with hy₀
  have hy₀1 : y₀ ≠ 1 := by
    intro h
    apply hx1
    have : x = g⁻¹ * y₀ * g := by rw [hy₀]; group
    rw [this, h]
    group
  have hTN : ∀ w ∈ (P : Subgroup G), ∀ t ∈ T, w * t * w⁻¹ ∈ T := fun w hw t ht =>
    ⟨(P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem hw ht.1) ((P : Subgroup G).inv_mem hw),
      (mem_normalizer_iff.mp (hJ.centralizer_le (hPC hw)) t).mp ht.2⟩
  have hZN : ∀ w ∈ (P : Subgroup G), ∀ z ∈ Z, w * z * w⁻¹ ∈ Z := by
    intro w hw z hz
    obtain ⟨hzC, hzP, h1⟩ := mem_l28ivZ.mp hz
    refine mem_l28ivZ.mpr ⟨hPC ((P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem hw hzP)
      ((P : Subgroup G).inv_mem hw)), (P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem hw hzP)
      ((P : Subgroup G).inv_mem hw), ?_⟩
    have e : (⟨w * z * w⁻¹, hPC ((P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem hw hzP)
        ((P : Subgroup G).inv_mem hw))⟩ : C) = ⟨w, hPC hw⟩ * ⟨z, hzC⟩ * (⟨w, hPC hw⟩ : C)⁻¹ :=
      Subtype.ext rfl
    rw [e, map_mul, map_mul, h1, mul_one, map_inv, mul_inv_cancel]
  have hucen : ∀ w ∈ (P : Subgroup G), w * u = u * w := by
    intro w hw
    obtain ⟨m, hm⟩ := P.isPGroup' ⟨w, hw⟩
    have hwm : w ^ (3 ^ m) = 1 := congrArg Subtype.val hm
    have h1 : w * u * w⁻¹ ∈ zpowers u := by
      refine mem_zpowers_of_isCyclic_of_pow_three hTcyc huT (hTN w hw u huT) hu1 hu3 ?_
      rw [conj_pow, hu3, mul_one, mul_inv_cancel]
    have h2 := CFSG.LocalAnalysis.RankThreeTheoremC.p34_conj_eq_of_pow hu1 hu3 hwm h1
    calc w * u = (w * u * w⁻¹) * w := by group
      _ = u * w := by rw [h2]
  have hy₀cen : ∀ a ∈ (P : Subgroup G) ⊓ C, a * y₀ = y₀ * a := by
    intro a ha
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hgu
    rw [← hk]
    exact (Commute.zpow_right (show Commute a u from hucen a ha.1) k).eq
  obtain ⟨n, hnN, hnx⟩ := l28iv_exists_normalizer_conj hQsyl hy₀cen
  rw [hQP] at hnN
  have hnN' : n⁻¹ ∈ normalizer ((P : Subgroup G) : Set G) := inv_mem hnN
  obtain ⟨y, hyQ, hy3, hyout⟩ := l28iv_exists_outside hS hU0 hE1 hp hM hgen hJ
  have hyP : y ∈ (P : Subgroup G) := hyQ.1
  have hyt₀ : y * t₀ * y⁻¹ ≠ t₀ := by
    obtain ⟨t, htT, hyt⟩ := l28iv_exists_moved hS hU0 hE1 hp hM hgen hJ hyP (hPC hyP) hyout
    intro h
    apply hyt
    have htz : t ∈ zpowers t₀ := by rw [← hT]; exact htT
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp htz
    rw [← conj_zpow, h]
  have hCT : ∀ a ∈ T, y * a * y⁻¹ = a → a ∈ zpowers u := by
    intro a haT hya
    by_contra hau
    have hao : orderOf a = 9 := by
      have hd : orderOf a ∣ 9 := by
        have := Subgroup.orderOf_dvd_natCard T haT
        rwa [hT, Nat.card_zpowers, ht₀] at this
      have hd' : orderOf a = 1 ∨ orderOf a = 3 ∨ orderOf a = 9 := by
        have : orderOf a ∈ Nat.divisors 9 := Nat.mem_divisors.mpr ⟨hd, by norm_num⟩
        have h9d : Nat.divisors 9 = {1, 3, 9} := by decide
        rw [h9d] at this
        simpa using this
      rcases hd' with h | h | h
      · exact absurd (mem_zpowers_of_isCyclic_of_pow_three hTcyc huT haT hu1 hu3
          (by rw [orderOf_eq_one_iff.mp h, one_pow])) hau
      · exact absurd (mem_zpowers_of_isCyclic_of_pow_three hTcyc huT haT hu1 hu3
          (by rw [← h]; exact pow_orderOf_eq_one a)) hau
      · exact h
    have hTa : T = zpowers a := by
      refine (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr haT) ?_).symm
      rw [Nat.card_zpowers, hao, hT, Nat.card_zpowers, ht₀]
    apply hyt₀
    have ht₀a : t₀ ∈ zpowers a := by rw [← hTa]; exact ht₀T
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp ht₀a
    rw [← hk, ← conj_zpow, hya]
  have hTNorm : ∀ w ∈ (P : Subgroup G), w ∈ normalizer (T : Set G) := fun w hw => by
    rw [mem_normalizer_iff]
    intro t
    refine ⟨fun ht => hTN w hw t ht, fun ht => ?_⟩
    have := hTN w⁻¹ (inv_mem hw) _ ht
    rwa [show w⁻¹ * (w * t * w⁻¹) * w⁻¹⁻¹ = t by group] at this
  have hZNorm : ∀ w ∈ (P : Subgroup G), w ∈ normalizer (Z : Set G) := fun w hw => by
    rw [mem_normalizer_iff]
    intro z
    refine ⟨fun hz => hZN w hw z hz, fun hz => ?_⟩
    have := hZN w⁻¹ (inv_mem hw) _ hz
    rwa [show w⁻¹ * (w * z * w⁻¹) * w⁻¹⁻¹ = z by group] at this
  have hTZN : ∀ w ∈ (P : Subgroup G), w ∈ normalizer ((T ⊔ Z : Subgroup G) : Set G) :=
    fun w hw => Subgroup.inf_normalizer_le_normalizer_sup T Z ⟨hTNorm w hw, hZNorm w hw⟩
  have hTZP : T ⊔ Z ≤ (P : Subgroup G) := sup_le inf_le_left (hZQ.trans inf_le_left)
  have hTNZ : T ≤ normalizer (Z : Set G) := fun t ht =>
    Subgroup.centralizer_le_normalizer _
      (mem_centralizer_iff.mpr fun z hz => (hcomm t ht z hz).symm)
  have hTc9 : Nat.card T = 9 := by rw [hT, Nat.card_zpowers, ht₀]
  have hcardTZ : Nat.card ↥(T ⊔ Z) = 9 * Nat.card Z := by
    have h := e9_card_sup_mul_card_inf hTNZ
    rw [hTZ, Subgroup.card_bot, mul_one, hTc9] at h
    exact h
  have hy1 : y ≠ 1 := fun h => hyout (h ▸ one_mem _)
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hyzp : zpowers y ⊓ (T ⊔ Z) = ⊥ := by
    have hdvd : Nat.card ↥(zpowers y ⊓ (T ⊔ Z)) ∣ 3 := by
      rw [← hyo, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exfalso
      have heq : zpowers y ⊓ (T ⊔ Z) = zpowers y :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, Nat.card_zpowers, hyo])
      exact hyout ((heq ▸ inf_le_right : zpowers y ≤ T ⊔ Z) (mem_zpowers y))
  have hcardyTZ : Nat.card ↥(zpowers y ⊔ (T ⊔ Z)) = 3 * Nat.card ↥(T ⊔ Z) := by
    have h := e9_card_sup_mul_card_inf (zpowers_le.mpr (hTZN y hyP))
    rw [hyzp, Subgroup.card_bot, mul_one, Nat.card_zpowers, hyo] at h
    exact h
  have hcardle := l28iv_card_le hS hU0 hE1 hp hM hgen hJ
  rw [hQP] at hcardle
  have hPeq : zpowers y ⊔ (T ⊔ Z) = (P : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge (sup_le (zpowers_le.mpr hyP) hTZP)
      (by rw [hcardyTZ]; exact hcardle)
  have hPy : (P : Subgroup G) ≤ zpowers y ⊔ (T ⊔ Z) := hPeq.ge
  have hyN : y ∈ normalizer (T : Set G) := hTNorm y hyP
  have hcubeZ : ∀ w ∈ (P : Subgroup G), (∀ a ∈ (P : Subgroup G), a * w = w * a) →
      w ^ 3 ∈ Z ∧ ∃ a ∈ zpowers u, ∃ c ∈ Z, w = a * c := by
    intro w hwP hwc
    have hwTZ : w ∈ T ⊔ Z := by
      by_contra h
      obtain ⟨t, htT, hwt⟩ := l28iv_exists_moved hS hU0 hE1 hp hM hgen hJ hwP (hPC hwP) h
      apply hwt
      rw [← hwc t htT.1]
      group
    obtain ⟨a, haT, c, hcZ, rfl⟩ := u3l42_decomp hcomm hwTZ
    have hya : y * a * y⁻¹ = a := by
      have h1 := hwc y hyP
      have hYA : y * a * y⁻¹ = a * c * (y * c * y⁻¹)⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq]
        calc y * a * y⁻¹ * (y * c * y⁻¹) = y * (a * c) * y⁻¹ := by group
          _ = (a * c) * y * y⁻¹ := by rw [h1]
          _ = a * c := by group
      have hmemZ : c * (y * c * y⁻¹)⁻¹ ∈ Z := Z.mul_mem hcZ (Z.inv_mem (hZN y hyP c hcZ))
      have hcomm' := hcomm a haT _ hmemZ
      have h3 : (y * a * y⁻¹) * a⁻¹ = c * (y * c * y⁻¹)⁻¹ := by
        calc (y * a * y⁻¹) * a⁻¹ = a * (c * (y * c * y⁻¹)⁻¹) * a⁻¹ := by rw [hYA]; group
          _ = (c * (y * c * y⁻¹)⁻¹) * a * a⁻¹ := by rw [hcomm']
          _ = c * (y * c * y⁻¹)⁻¹ := by group
      have hmemT : (y * a * y⁻¹) * a⁻¹ ∈ T := T.mul_mem (hTN y hyP a haT) (T.inv_mem haT)
      have := hZT _ hmemT (h3 ▸ hmemZ)
      exact mul_inv_eq_one.mp this
    have hau := hCT a haT hya
    have ha3 : a ^ 3 = 1 := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hau
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu3, one_zpow]
    refine ⟨?_, a, hau, c, hcZ, rfl⟩
    rw [Commute.mul_pow (show Commute a c from hcomm a haT c hcZ) 3, ha3, one_mul]
    exact pow_mem hcZ 3
  have hkey : ∀ w ∈ (P : Subgroup G), (∀ a ∈ (P : Subgroup G), a * w = w * a) →
      w ^ 3 ∈ zpowers x → w ^ 3 = 1 := by
    intro w hwP hwc hw3
    have hnwP : n * w * n⁻¹ ∈ (P : Subgroup G) := (mem_normalizer_iff.mp hnN w).mp hwP
    have hnwc : ∀ a ∈ (P : Subgroup G), a * (n * w * n⁻¹) = (n * w * n⁻¹) * a := by
      intro a ha
      have ha' : n⁻¹ * a * n ∈ (P : Subgroup G) := by
        have := (mem_normalizer_iff.mp hnN' a).mp ha
        rwa [inv_inv] at this
      have h1 := hwc _ ha'
      calc a * (n * w * n⁻¹) = n * ((n⁻¹ * a * n) * w) * n⁻¹ := by group
        _ = n * (w * (n⁻¹ * a * n)) * n⁻¹ := by rw [h1]
        _ = (n * w * n⁻¹) * a := by group
    have h1 := (hcubeZ _ hnwP hnwc).1
    rw [conj_pow] at h1
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hw3
    have hy₀T : y₀ ∈ T := (zpowers_le.mpr huT) hgu
    have h2 : n * w ^ 3 * n⁻¹ ∈ T := by
      rw [← hk, ← conj_zpow, hnx]
      exact zpow_mem hy₀T k
    have h3 := hZT _ h2 h1
    have e : w ^ 3 = n⁻¹ * (n * w ^ 3 * n⁻¹) * n := by group
    rw [e, h3]
    group
  have hZp : IsPGroup 3 ↥Z := P.isPGroup'.to_le (hZQ.trans inf_le_left)
  obtain ⟨kZ, hkZ⟩ := hZp.exists_card_eq
  have hZcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := by
    let _ := hZc.commGroup
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥Z) ⟨b, hb⟩)
  have hk2 : 2 ≤ kZ := by
    by_contra hlt
    push Not at hlt
    have h3d : 3 ∣ Nat.card Z := by
      have := Subgroup.orderOf_dvd_natCard Z hxZ
      rwa [hxo] at this
    have hk1 : kZ = 1 := by
      rcases Nat.lt_or_ge kZ 1 with h | h
      · exfalso
        rw [show kZ = 0 by omega, pow_zero] at hkZ
        rw [hkZ] at h3d
        norm_num at h3d
      · omega
    have hZx : Z = zpowers x := (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hxZ)
      (by rw [hkZ, hk1, Nat.card_zpowers, hxo]; norm_num)).symm
    have hcen : ∀ w ∈ (P : Subgroup G), ∀ c ∈ Z, w * c = c * w := by
      intro w hw c hc
      rw [hZx] at hc
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
      exact (Commute.zpow_right (show Commute w x from mem_centralizer_singleton_iff.mp
        (hPC hw)) k).eq
    have hZ3 : ∀ c ∈ Z, c ^ 3 = 1 := by
      intro c hc
      rw [hZx] at hc
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
    have hcube := l28iv_cube_mem hcomm hy3 hyN hcen hZ3 hPy hyP hTZP
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hgu
    have he : (t₀ ^ 3) ^ k = (t₀ ^ k) ^ 3 := by
      rw [← zpow_natCast t₀ 3, ← zpow_mul, ← zpow_natCast (t₀ ^ k) 3, ← zpow_mul, mul_comm]
    have hx : x = (n⁻¹ * t₀ ^ k * n⁻¹⁻¹) ^ 3 := by
      have h1 : x = n⁻¹ * y₀ * n := by rw [hy₀, ← hnx]; group
      rw [conj_pow, h1, ← hk, hu, he, inv_inv]
    have ht₀P : t₀ ∈ (P : Subgroup G) := (Subgroup.mem_inf.mp ht₀T).1
    have hwP : n⁻¹ * t₀ ^ k * n⁻¹⁻¹ ∈ (P : Subgroup G) :=
      (mem_normalizer_iff.mp hnN' _).mp (zpow_mem ht₀P k)
    have := hcube _ hwP
    rw [← hx] at this
    exact hxJ this.2
  have hk2' : kZ ≤ 2 := by
    by_contra hlt
    push Not at hlt
    obtain ⟨z₀', hz₀'⟩ := hZc.exists_generator
    set z₀ : G := (z₀' : G) with hz₀
    have hZeq : Z = zpowers z₀ := by
      refine le_antisymm (fun g hg => ?_) (zpowers_le.mpr z₀'.2)
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hz₀' ⟨g, hg⟩)
      exact mem_zpowers_iff.mpr ⟨k, by rw [hz₀]; simpa using congrArg Subtype.val hk⟩
    have hz₀o : orderOf z₀ = 3 ^ kZ := by rw [← Nat.card_zpowers, ← hZeq, hkZ]
    have hyz : y * z₀ * y⁻¹ ∈ zpowers z₀ := by rw [← hZeq]; exact hZN y hyP z₀ z₀'.2
    have hfix := l28iv_fix_cube (by omega) hz₀o hy3 hyz
    have hz3Z : z₀ ^ 3 ∈ Z := pow_mem z₀'.2 3
    have hz3c : ∀ a ∈ (P : Subgroup G), a * z₀ ^ 3 = z₀ ^ 3 * a := by
      have hle : zpowers y ⊔ (T ⊔ Z) ≤ centralizer ({z₀ ^ 3} : Set G) := by
        refine sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr ?_))
          (sup_le (fun t ht => mem_centralizer_singleton_iff.mpr (hcomm t ht _ hz3Z))
            (fun c hc => mem_centralizer_singleton_iff.mpr (hZcomm c hc _ hz3Z)))
        calc y * z₀ ^ 3 = (y * z₀ ^ 3 * y⁻¹) * y := by group
          _ = z₀ ^ 3 * y := by rw [hfix]
      intro a ha
      exact mem_centralizer_singleton_iff.mp (hle (hPy ha))
    set w : G := (z₀ ^ 3) ^ (3 ^ (kZ - 3)) with hw
    have hwP : w ∈ (P : Subgroup G) := pow_mem ((hZQ hz3Z).1) _
    have hwc : ∀ a ∈ (P : Subgroup G), a * w = w * a := fun a ha =>
      (Commute.pow_right (show Commute a (z₀ ^ 3) from hz3c a ha) _).eq
    have hw3 : w ^ 3 = z₀ ^ (3 ^ (kZ - 1)) := by
      rw [hw, ← pow_mul, ← pow_mul]
      congr 1
      have : kZ - 1 = (kZ - 3) + 2 := by omega
      rw [this, pow_add]
      ring
    have hw31 : w ^ 3 ≠ 1 := by
      rw [hw3]
      intro h
      have h1 := orderOf_dvd_of_pow_eq_one h
      rw [hz₀o] at h1
      have h2 := Nat.le_of_dvd (by positivity) h1
      have h3 : 3 ^ (kZ - 1) < 3 ^ kZ := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have hwZ : w ∈ Z := by
      rw [hZeq, hw]
      exact pow_mem (pow_mem (mem_zpowers z₀) 3) _
    have hw33 : (w ^ 3) ^ 3 = 1 := by
      rw [hw3, ← pow_mul, show 3 ^ (kZ - 1) * 3 = 3 ^ kZ by
        rw [← pow_succ]; congr 1; omega, ← hz₀o, pow_orderOf_eq_one]
    have hw3x : w ^ 3 ∈ zpowers x :=
      mem_zpowers_of_isCyclic_of_pow_three hZc hxZ (pow_mem hwZ 3) hx1 hx3 hw33
    exact hw31 (hkey w hwP hwc hw3x)
  have hZc9 : Nat.card Z = 9 := by rw [hkZ, show kZ = 2 by omega]; norm_num
  have hux : u * x = x * u := hcomm u huT x hxZ
  have hplane := plane_zpowers_sup (x := x) (k := u) hx3 hu1 hu3 hxu hux
  have hZPeq : L28Z (P : Subgroup G) = zpowers u ⊔ zpowers x := by
    apply le_antisymm
    · intro w hw
      have hwP := l28Z_le _ hw
      have hwc : ∀ a ∈ (P : Subgroup G), a * w = w * a := fun a ha => l28z_comm hw ha
      obtain ⟨-, a, hau, c, hcZ, rfl⟩ := hcubeZ w hwP hwc
      have hcx : c ∈ zpowers x := by
        by_contra hcx
        have hac : ∀ b ∈ (P : Subgroup G), b * c = c * b := by
          intro b hb
          have h1 : Commute b (a * c) := hwc b hb
          have h2 : Commute b a := by
            obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hau
            exact Commute.zpow_right (show Commute b u from hucen b hb) k
          have hc' : Commute b (a⁻¹ * (a * c)) := h2.inv_right.mul_right h1
          have e : a⁻¹ * (a * c) = c := by group
          rw [e] at hc'
          exact hc'.eq
        have hcP : c ∈ (P : Subgroup G) := (hZQ hcZ).1
        have hc9 : c ^ 9 = 1 := by
          have h1 := Subgroup.orderOf_dvd_natCard Z hcZ
          rw [hZc9] at h1
          exact orderOf_dvd_iff_pow_eq_one.mp h1
        have hc33 : (c ^ 3) ^ 3 = 1 := by rw [← pow_mul]; exact hc9
        have hc3x : c ^ 3 ∈ zpowers x :=
          mem_zpowers_of_isCyclic_of_pow_three hZc hxZ (pow_mem hcZ 3) hx1 hx3 hc33
        exact hcx (mem_zpowers_of_isCyclic_of_pow_three hZc hxZ hcZ hx1 hx3
          (hkey c hcP hac hc3x))
      exact Subgroup.mul_mem_sup hau hcx
    · refine sup_le (zpowers_le.mpr (mem_l28Z_of_comm huT.1 fun a ha => hucen a ha))
        (zpowers_le.mpr (mem_l28Z_of_comm hxP fun a ha =>
          mem_centralizer_singleton_iff.mp (hPC ha)))
  have hZPcard : Nat.card (L28Z (P : Subgroup G)) = 3 ^ 2 := by rw [hZPeq]; exact hplane.2
  have hplaneQ : zpowers u ⊔ zpowers x ≤ T ⊔ Z :=
    sup_le ((zpowers_le.mpr huT).trans le_sup_left) ((zpowers_le.mpr hxZ).trans le_sup_right)
  have hZPiff : ∀ a : G, a ∈ L28Z (P : Subgroup G) ↔ a ∈ T ⊔ Z ∧ a ^ 3 = 1 := by
    intro a
    rw [hZPeq]
    constructor
    · intro ha
      exact ⟨hplaneQ ha, hplane.1.2 a ha⟩
    · rintro ⟨ha, ha3⟩
      exact l28iv_mem_plane_of_pow_three hT ht₀ hZc hxZ hx1 hx3 hTZ hcomm ha ha3
  have hcardP : Nat.card (P : Subgroup G) = 3 ^ 5 := by
    rw [← hPeq, hcardyTZ, hcardTZ, hZc9]
    norm_num
  refine ⟨⟨hPC, hZPcard, ?_, ?_⟩, hcardP, T ⊔ Z, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht ht3
    rw [hZPeq]
    exact mem_sup_left (mem_zpowers_of_isCyclic_of_pow_three hTcyc huT ht hu1 hu3 ht3)
  · intro w hw hw3 hwZ
    by_cases hwTZ : w ∈ T ⊔ Z
    · exact absurd ((hZPiff w).mpr ⟨hwTZ, hw3⟩) hwZ
    · exact l28iv_outerOn_of_not_mem hS hU0 hE1 hp hM hgen hJ hw (hPC hw) hwTZ
  · exact lt_of_le_of_ne hTZP fun h => hyout (by rw [h]; exact hyP)
  · intro R hR hRP
    have h1 : Nat.card R ∣ 3 ^ 5 := hcardP ▸ Subgroup.card_dvd_of_le hRP
    have h2 : Nat.card ↥(T ⊔ Z) < Nat.card R := Subgroup.card_lt_of_lt hR
    rw [hcardTZ, hZc9] at h2
    obtain ⟨i, hi, hRc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
    have hi5 : i = 5 := by
      by_contra hne
      have h4 : 3 ^ i ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [hRc] at h2
      norm_num at h2 h4
      omega
    exact Subgroup.eq_of_le_of_card_ge hRP (by rw [hRc, hi5, hcardP])
  ·
    have hTcI : IsCyclic ↥T := hTcyc
    have hZcI : IsCyclic ↥Z := hZc
    have hZ9card : Nat.card (Multiplicative (ZMod (3 ^ 2))) = 3 ^ 2 := by simp
    let eT : Multiplicative (ZMod (3 ^ 2)) ≃* ↥T :=
      mulEquivOfCyclicCardEq (by rw [hZ9card, hTc9]; norm_num)
    let eZ : Multiplicative (ZMod (3 ^ 2)) ≃* ↥Z :=
      mulEquivOfCyclicCardEq (by rw [hZ9card, hZc9]; norm_num)
    let f : Multiplicative (ZMod (3 ^ 2)) →* G := T.subtype.comp eT.toMonoidHom
    let f' : Multiplicative (ZMod (3 ^ 2)) →* G := Z.subtype.comp eZ.toMonoidHom
    have hff : ∀ m n, Commute (f m) (f' n) := fun m n => hcomm _ (eT m).2 _ (eZ n).2
    let φ := f.noncommCoprod f' hff
    have hφ : ∀ mn, φ mn = (eT mn.1 : G) * (eZ mn.2 : G) := fun mn => rfl
    have hinj : Function.Injective φ := by
      rw [injective_iff_map_eq_one]
      rintro ⟨a, b⟩ hab
      rw [hφ] at hab
      have h1 : (eT a : G) = (eZ b : G)⁻¹ := eq_inv_of_mul_eq_one_left hab
      have h2 : (eT a : G) = 1 := hZT _ (eT a).2 (by rw [h1]; exact inv_mem (eZ b).2)
      have h3 : (eZ b : G) = 1 := by
        rw [h2] at h1
        exact inv_eq_one.mp h1.symm
      have ha : a = 1 := eT.injective (Subtype.ext (by rw [h2, map_one]; rfl))
      have hb : b = 1 := eZ.injective (Subtype.ext (by rw [h3, map_one]; rfl))
      rw [ha, hb]
      rfl
    have hrange : φ.range = T ⊔ Z := by
      apply le_antisymm
      · rintro _ ⟨⟨a, b⟩, rfl⟩
        rw [hφ]
        exact Subgroup.mul_mem_sup (eT a).2 (eZ b).2
      · apply sup_le
        · intro t ht
          refine ⟨(eT.symm ⟨t, ht⟩, 1), ?_⟩
          rw [hφ]
          simp
        · intro z hz
          refine ⟨(1, eZ.symm ⟨z, hz⟩), ?_⟩
          rw [hφ]
          simp
    exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm⟩
  · exact ⟨zpowers y, zpowers_le.mpr hyP, by rw [inf_comm]; exact hyzp,
      by rw [sup_comm]; exact hPeq⟩
  · refine ⟨T, Z, ?_, ?_, hTZ, rfl, fun w hw => hTNorm w hw, fun w hw => hZNorm w hw⟩
    · intro h
      apply hu1
      have : u ∈ T := huT
      rw [h, mem_bot] at this
      exact this
    · intro h
      apply hx1
      have : x ∈ Z := hxZ
      rw [h, mem_bot] at this
      exact this
  · exact hZPiff

theorem GL83GenericPrimeThreeL28Prop34SNoWC.of_kfacts (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD1 : TheoremD1 G) (K1 : StronglyEmbeddedRankTwoKFactNoBM)
    (K2 : StronglyEmbeddedCyclicOuterKFact) (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree)
    (hno : NoExcludedSection3 G) (hKM : CFSG.AGLEmbeddingD2.KFactM11Three)
    (hKA : KFactM11TwoSignalizer) (hL : KFactsL34Full) (hA1 : A6SylowData) (hA3 : A6BorelCore)
    (hE1 : KFactL28Three) (hE3 : KFactL28BorelCore) : GL83GenericPrimeThreeL28Prop34SNoWC G := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ
  subst hp3
  exact l28iv_prop34S hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA1 hA3 hE1 hE3 hp hM hgen
    ⟨hJC, hCJ, hperf, hnot, hlt, hmin, Q, inferInstance, ψ, hψ, hker, hQ⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
