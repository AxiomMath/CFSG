module

public import CFSG.LocalAnalysis.GH72.G3bFour
import CFSG.LocalAnalysis.GH72.G3cFourteen
import CFSG.LocalAnalysis.GH72.GL42Bridge
import CFSG.LocalAnalysis.GH72.Sec4M0
import CFSG.GroupTheory.ThompsonIndexTwo
import CFSG.RankThree.GF2n.Tim77.Sec414Basic
public import CFSG.LocalAnalysis.GH72.G3cFusion

public section

namespace CFSG.GH72

open Subgroup
open CFSG.CGT.Foote81L6 (card_sup_of_le_normalizer le_normalizer_of_comm
  mem_sup_iff_of_le_normalizer)

namespace G3bFourOdd

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec3Setting G)

theorem eq_of_isConj_of_mem_center
    (hN : ∀ n ∈ normalizer ((𝔖.S : Subgroup G) : Set G),
      ∀ x ∈ (𝔖.S : Subgroup G) ⊓ centralizer (𝔖.S : Set G), n * x * n⁻¹ = x)
    {x y : G} (hx : x ∈ (𝔖.S : Subgroup G) ⊓ centralizer (𝔖.S : Set G))
    (hy : y ∈ (𝔖.S : Subgroup G) ⊓ centralizer (𝔖.S : Set G)) (hxy : IsConj x y) : x = y := by
  obtain ⟨g, hg⟩ := isConj_iff.1 hxy
  have hy' : g⁻¹⁻¹ * x * g⁻¹ ∈ centralizer (𝔖.S : Set G) := by
    rw [inv_inv, hg]
    exact (mem_inf.1 hy).2
  obtain ⟨n, hn, hnx⟩ :=
    Sylow.conj_eq_normalizer_conj_of_mem_centralizer 𝔖.S x g⁻¹ (mem_inf.1 hx).2 hy'
  have h := hN n⁻¹ (inv_mem hn) x hx
  rw [inv_inv] at h hnx
  rw [← hg, hnx, h]

theorem exists_odd_mem_normalizer_not_mem_centralizer {A : Subgroup G} (hAS : A ≤ 𝔖.S)
    (hA : IsE16 A) {c z : G} (hcA : c ∈ A) (hzA : z ∈ A) (hzS : (𝔖.S : Subgroup G) ≤ C z)
    (hcz : c ≠ z) (hconj : IsConj c z) :
    ∃ y ∈ normalizer (A : Set G), Odd (orderOf y) ∧ y ∉ centralizer (A : Set G) := by
  obtain ⟨g, hgA, hgc⟩ := G3cF.exists_mem_normalizer_conj_eq 𝔖 hAS hA hcA hzS hconj
  by_contra hcon
  have hO2 : O2 (normalizer (A : Set G)) ≤ centralizer (A : Set G) :=
    twoResidualOf_le_of_forall fun y hy hyo => by
      by_contra h
      exact hcon ⟨y, hy, hyo, h⟩
  have hNeq := G3cF.sup_twoResidualOf_eq (𝔖.decomp.isSylowOf_normalizer_e16 hAS hA)
  have hgi : g⁻¹ ∈ centralizer (A : Set G) ⊔ ((𝔖.S : Subgroup G) ⊓ normalizer (A : Set G)) := by
    have h : g⁻¹ ∈ normalizer (A : Set G) := inv_mem hgA
    rw [← hNeq, sup_comm] at h
    exact (sup_le_sup_right hO2 _) h
  have hTN : (𝔖.S : Subgroup G) ⊓ normalizer (A : Set G) ≤
      normalizer (centralizer (A : Set G) : Set G) := fun t ht =>
    G4b.mem_normalizer_centralizer (mem_inf.1 ht).2
  obtain ⟨c₀, hc₀, t, ht, he⟩ := (mem_sup_iff_of_le_normalizer hTN).1 hgi
  have hc₀z : c₀ * z = z * c₀ := (mem_centralizer_iff.1 hc₀ z hzA).symm
  have htz : t * z = z * t := mem_centralizer_singleton_iff.1 (hzS (mem_inf.1 ht).1)
  apply hcz
  calc c = g⁻¹ * (g * c * g⁻¹) * g := by group
    _ = g⁻¹ * z * g⁻¹⁻¹ := by rw [hgc, inv_inv]
    _ = c₀ * (t * z * t⁻¹) * c₀⁻¹ := by rw [he]; group
    _ = z := by rw [htz, mul_inv_cancel_right, hc₀z, mul_inv_cancel_right]

theorem exists_fixed_four (h₁ : IsKleinFour 𝔖.S₁)
    (h₂ : ∀ x ∈ 𝔖.S₂, ∀ y ∈ 𝔖.S₂, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (hfus : ∀ x ∈ (𝔖.S : Subgroup G) ⊓ centralizer (𝔖.S : Set G),
      ∀ y ∈ (𝔖.S : Subgroup G) ⊓ centralizer (𝔖.S : Set G), IsConj x y → x = y)
    {z : G} (hzS₂ : z ∈ 𝔖.S₂) (hzord : orderOf z = 2)
    (hZ₂ : 𝔖.S₂ ⊓ centralizer (𝔖.S₂ : Set G) = zpowers z) {A : Subgroup G} (hAS : A ≤ 𝔖.S)
    (hA : IsE16 A) :
    ∃ V : Subgroup G, V ≤ (𝔖.S : Subgroup G) ⊓ centralizer (𝔖.S : Set G) ∧ V ≤ A ∧
      Nat.card V = 4 ∧ z ∉ V ∧ ∀ v ∈ V, ∀ a ∈ A, IsConj a v → a = v := by
  set Z : Subgroup G := (𝔖.S : Subgroup G) ⊓ centralizer (𝔖.S : Set G) with hZdef
  have hzC : z ∈ centralizer (𝔖.S : Set G) := Sec3Setting.central_of_mem_center_S₂ 𝔖 hzS₂ hZ₂
  have hcen : ∀ w ∈ Z, (𝔖.S : Subgroup G) ≤ C w := fun w hw s hs =>
    mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 (mem_inf.1 hw).2) s hs)
  have hzZ : z ∈ Z := mem_inf.2 ⟨𝔖.decomp.le_right hzS₂, hzC⟩
  have hZA : Z ≤ A := fun w hw => 𝔖.decomp.center_le hAS hA (mem_inf.1 hw).1 (hcen w hw)
  have hzA : z ∈ A := hZA hzZ
  obtain ⟨-, -, hV₂⟩ := 𝔖.decomp.e16_split hAS hA
  have hV₂4 : IsKleinFour ↥(A ⊓ 𝔖.S₂) := isKleinFour_of_isFourIn hV₂
  obtain ⟨c, hcV, hc1, hcz⟩ := exists_mem_kleinFour_ne hV₂4 (mem_inf.2 ⟨hzA, hzS₂⟩)
  have hc2 : orderOf c = 2 := G4b.orderOf_eq_two_of_isE16 hA (mem_inf.1 hcV).1 hc1
  have hconj : IsConj c z := h₂ c (mem_inf.1 hcV).2 z hzS₂ hc2 hzord
  obtain ⟨y, hyN, hyodd, hyC⟩ := exists_odd_mem_normalizer_not_mem_centralizer 𝔖 hAS hA
    (mem_inf.1 hcV).1 hzA (hcen z hzZ) hcz hconj
  have hQK : zpowers y ≤ normalizer (A : Set G) := zpowers_le.2 hyN
  have hodd : Odd ((centralizer (A : Set G)).relIndex (zpowers y)) :=
    hyodd.of_dvd_nat (by rw [← Nat.card_zpowers]; exact relIndex_dvd_card _ _)
  have hQ1 : (centralizer (A : Set G)).relIndex (zpowers y) ≠ 1 := fun h =>
    hyC (relIndex_eq_one.1 h (mem_zpowers y))
  have hWK : ∀ w ∈ Z, ∀ k ∈ normalizer (A : Set G), k * w * k⁻¹ ∈ Z → k * w * k⁻¹ = w :=
    fun w hw k _ hkw => (hfus w hw _ hkw (isConj_iff.2 ⟨k, rfl⟩)).symm
  obtain ⟨-, h4, hFW, hKF, -, -⟩ := conj_orbits_of_isolated_subgroup hA le_rfl hQK hodd hQ1 hZA
    (Sec3Setting.center_S_card 𝔖 h₁ hzS₂ hzord hZ₂) hWK
  refine ⟨A ⊓ centralizer (normalizer (A : Set G) : Set G), by rw [hKF]; exact hFW,
    inf_le_left, by rw [hKF]; exact h4, fun hzV => ?_, fun v hv a ha hav => ?_⟩
  ·
    obtain ⟨g, hgA, hgc⟩ := G3cF.exists_mem_normalizer_conj_eq 𝔖 hAS hA (mem_inf.1 hcV).1
      (hcen z hzZ) hconj
    have hgz : g * z = z * g := mem_centralizer_iff.1 (mem_inf.1 hzV).2 g hgA
    apply hcz
    calc c = g⁻¹ * (g * c * g⁻¹) * g := by group
      _ = z := by rw [hgc, mul_assoc, ← hgz, inv_mul_cancel_left]
  ·
    have hvZ : v ∈ Z := by
      have h : v ∈ A ⊓ centralizer (zpowers y : Set G) := by rw [← hKF]; exact hv
      exact hFW h
    obtain ⟨n, hnA, hna⟩ := G3cF.exists_mem_normalizer_conj_eq 𝔖 hAS hA ha (hcen v hvZ) hav
    have hnv : n * v = v * n := mem_centralizer_iff.1 (mem_inf.1 hv).2 n hnA
    calc a = n⁻¹ * (n * a * n⁻¹) * n := by group
      _ = v := by rw [hna, mul_assoc, ← hnv, inv_mul_cancel_left]

theorem exists_isolated (h₁ : IsKleinFour 𝔖.S₁)
    (h₂ : ∀ x ∈ 𝔖.S₂, ∀ y ∈ 𝔖.S₂, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (hfus : ∀ x ∈ (𝔖.S : Subgroup G) ⊓ centralizer (𝔖.S : Set G),
      ∀ y ∈ (𝔖.S : Subgroup G) ⊓ centralizer (𝔖.S : Set G), IsConj x y → x = y)
    {z : G} (hzS₂ : z ∈ 𝔖.S₂) (hzord : orderOf z = 2)
    (hZ₂ : 𝔖.S₂ ⊓ centralizer (𝔖.S₂ : Set G) = zpowers z) :
    ∃ t ∈ (𝔖.S : Subgroup G) ⊓ centralizer (𝔖.S : Set G), t ≠ 1 ∧ t ≠ z ∧
      ∀ x ∈ (𝔖.S : Subgroup G), IsConj x t → x = t := by
  set Z : Subgroup G := (𝔖.S : Subgroup G) ⊓ centralizer (𝔖.S : Set G) with hZdef
  obtain ⟨Arep, hArep, hcover, -⟩ := 𝔖.decomp.e16_classes_of_isKleinFour h₁
  obtain ⟨V₀, hV₀Z, -, hV₀4, hzV₀, hV₀fix⟩ :=
    exists_fixed_four 𝔖 h₁ h₂ hfus hzS₂ hzord hZ₂ (hArep 0).1 (hArep 0).2
  obtain ⟨V₁, hV₁Z, -, hV₁4, -, hV₁fix⟩ :=
    exists_fixed_four 𝔖 h₁ h₂ hfus hzS₂ hzord hZ₂ (hArep 1).1 (hArep 1).2
  have hne : V₀ ⊓ V₁ ≠ ⊥ := by
    intro h
    have hcomm : ∀ a ∈ V₀, ∀ b ∈ V₁, a * b = b * a := fun a ha b hb =>
      (mem_centralizer_iff.1 (mem_inf.1 (hV₀Z ha)).2 b (mem_inf.1 (hV₁Z hb)).1).symm
    have hcard := card_sup_of_le_normalizer (le_normalizer_of_comm hcomm) h
    have hle := card_le_of_le (sup_le hV₀Z hV₁Z)
    rw [hcard, hV₀4, hV₁4, Sec3Setting.center_S_card 𝔖 h₁ hzS₂ hzord hZ₂] at hle
    omega
  obtain ⟨⟨t, ht⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have htZ : t ∈ Z := hV₀Z (mem_inf.1 ht).1
  have htt : t * t = 1 := Sec3Setting.center_S_sq_eq_one 𝔖 h₁ hzS₂ hzord hZ₂ t htZ
  refine ⟨t, htZ, ht1', fun h => hzV₀ (h ▸ (mem_inf.1 ht).1), fun x hx hxt => ?_⟩
  obtain ⟨g, hg⟩ := isConj_iff.1 hxt
  have hxx : x * x = 1 := by
    have e : x = g⁻¹ * t * g := by rw [← hg]; group
    rw [e]
    calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [htt]; group
  obtain ⟨E, hES, hE, hxE⟩ := 𝔖.decomp.exists_e16_mem hx hxx
  obtain ⟨j, s, hsS, hsE⟩ := hcover E hES hE
  have hsx : s * x * s⁻¹ ∈ Arep j := by
    rw [← hsE]
    exact ⟨x, hxE, rfl⟩
  have hconj : IsConj (s * x * s⁻¹) t := (isConj_iff.2 ⟨s, rfl⟩).symm.trans hxt
  have hts : s * t = t * s := (mem_centralizer_iff.1 (mem_inf.1 htZ).2 s hsS)
  have key : s * x * s⁻¹ = t := by
    fin_cases j
    · exact hV₀fix t (mem_inf.1 ht).1 _ hsx hconj
    · exact hV₁fix t (mem_inf.1 ht).2 _ hsx hconj
  calc x = s⁻¹ * (s * x * s⁻¹) * s := by group
    _ = t := by rw [key, mul_assoc, ← hts, inv_mul_cancel_left]

theorem exists_mem_normalizer_not_mem_centralizer_center (h₁ : IsKleinFour 𝔖.S₁)
    (h₂ : ∀ x ∈ 𝔖.S₂, ∀ y ∈ 𝔖.S₂, orderOf x = 2 → orderOf y = 2 → IsConj x y) :
    ∃ n ∈ normalizer ((𝔖.S : Subgroup G) : Set G),
      ∃ x ∈ (𝔖.S : Subgroup G) ⊓ centralizer (𝔖.S : Set G), n * x * n⁻¹ ≠ x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  have hN : ∀ n ∈ normalizer ((𝔖.S : Subgroup G) : Set G),
      ∀ x ∈ (𝔖.S : Subgroup G) ⊓ centralizer (𝔖.S : Set G), n * x * n⁻¹ = x :=
    fun n hn x hx => by
      by_contra h
      exact hcon ⟨n, hn, x, hx, h⟩
  have hfus := fun x hx y hy hxy => eq_of_isConj_of_mem_center 𝔖 hN (x := x) (y := y) hx hy hxy
  obtain ⟨z, hzS₂, hzord, hZ₂⟩ := Sec3Setting.exists_central_involution_S₂ 𝔖
  obtain ⟨t, htZ, ht1, htz, hiso⟩ := exists_isolated 𝔖 h₁ h₂ hfus hzS₂ hzord hZ₂
  have htS : t ∈ (𝔖.S : Subgroup G) := (mem_inf.1 htZ).1
  have htt : t * t = 1 := Sec3Setting.center_S_sq_eq_one 𝔖 h₁ hzS₂ hzord hZ₂ t htZ
  obtain ⟨s, hs, w, hw, hsw⟩ := 𝔖.decomp.mem_iff.1 htS
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [one_mul] at hsw
    have h : t ∈ ((𝔖.S : Subgroup G) ⊓ centralizer (𝔖.S : Set G)) ⊓ 𝔖.S₂ :=
      mem_inf.2 ⟨htZ, hsw ▸ hw⟩
    rw [Sec3Setting.center_S_inf_S₂ 𝔖 h₁ hzS₂ hZ₂] at h
    rcases (CFSG.Timmesfeld.Bridge.mem_zpowers_iff_of_orderOf_eq_two hzord).mp h with h' | h'
    · exact ht1 h'
    · exact htz h'
  obtain ⟨s', hs', hs'1, hs's⟩ := exists_mem_kleinFour_ne h₁ hs
  have hs's' : s' * s' = 1 := by rw [← sq]; exact sq_eq_one_of_mem_kleinFour h₁ hs'
  set U : Subgroup G := zpowers s' ⊔ 𝔖.S₂ with hU
  have hs'S₁ : zpowers s' ≤ 𝔖.S₁ := zpowers_le.2 hs'
  have hUS : U ≤ 𝔖.S := sup_le (hs'S₁.trans 𝔖.decomp.le_left) 𝔖.decomp.le_right
  have hcomm₁ : ∀ a ∈ 𝔖.S₁, ∀ b ∈ 𝔖.S₂, a * b = b * a := fun a ha b hb => 𝔖.decomp.comm ha hb
  have hcardU : Nat.card U = 2 * Nat.card 𝔖.S₂ := by
    rw [hU, card_sup_of_le_normalizer
      (le_normalizer_of_comm fun a ha b hb => hcomm₁ a (hs'S₁ ha) b hb), Nat.card_zpowers,
      orderOf_eq_prime (by rw [sq]; exact hs's') hs'1]
    refine eq_bot_iff.2 fun g hg => ?_
    have h : g ∈ 𝔖.S₁ ⊓ 𝔖.S₂ := mem_inf.2 ⟨hs'S₁ (mem_inf.1 hg).1, (mem_inf.1 hg).2⟩
    rwa [𝔖.decomp.inf_eq] at h
  have hcardS : Nat.card (𝔖.S : Subgroup G) = 4 * Nat.card 𝔖.S₂ := by
    rw [← 𝔖.decomp.sup_eq, card_sup_of_le_normalizer (le_normalizer_of_comm hcomm₁)
      𝔖.decomp.inf_eq, h₁.card_four]
  have hUidx : U.relIndex 𝔖.S = 2 := by
    have h := relIndex_mul_card U (𝔖.S : Subgroup G)
    rw [inf_eq_left.2 hUS, hcardU, hcardS] at h
    have hpos : 0 < Nat.card 𝔖.S₂ := Nat.card_pos
    nlinarith
  have htU : t ∉ U := by
    intro h
    have hsU : s ∈ U := by
      have h' := U.mul_mem h (U.inv_mem (mem_sup_right hw : w ∈ U))
      rwa [hsw, mul_inv_cancel_right] at h'
    have hsz : s ∈ zpowers s' := by
      rw [← 𝔖.decomp.sup_inf_left hs'S₁ le_rfl]
      exact mem_inf.2 ⟨hsU, hs⟩
    rcases CFSG.CGT.Foote81L6.TStruct.eq_one_or_eq_of_mem_zpowers hs's' hsz with h' | h'
    · exact hs1 h'
    · exact hs's h'.symm
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact htt) ht1
  obtain ⟨N, hNn, hNidx⟩ := CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson
    (T := (𝔖.S : Subgroup G)) (U := U) 𝔖.S.isPGroup' 𝔖.S.not_dvd_index hUS hUidx htS htU
    (fun y _ hyU => by
      have hy1 : y ≠ 1 := fun h => hyU (h ▸ one_mem U)
      have hpos := orderOf_pos y
      have hne : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.1 h)
      omega)
    (fun g hg => htU (by
      have h := hiso _ (hUS hg) (isConj_iff.2 ⟨g, by group⟩)
      rwa [h] at hg))
  exact 𝔖.noIndexTwo N hNn hNidx

theorem exists_odd_mem_normalizer_not_mem_centralizer_center (h₁ : IsKleinFour 𝔖.S₁)
    (h₂ : ∀ x ∈ 𝔖.S₂, ∀ y ∈ 𝔖.S₂, orderOf x = 2 → orderOf y = 2 → IsConj x y) :
    ∃ u ∈ normalizer ((𝔖.S : Subgroup G) : Set G), Odd (orderOf u) ∧
      ∃ x ∈ (𝔖.S : Subgroup G) ⊓ centralizer (𝔖.S : Set G), u * x * u⁻¹ ≠ x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn, x, hx, hnx⟩ := exists_mem_normalizer_not_mem_centralizer_center 𝔖 h₁ h₂
  obtain ⟨a, b, hab, ⟨k, hk⟩, hodd⟩ := G4b.exists_zpow_mul_zpow n
  obtain ⟨p, hp⟩ : ∃ p : G, p = n ^ a := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : G, q = n ^ b := ⟨_, rfl⟩
  rw [← hp, ← hq] at hab
  rw [← hp] at hk
  rw [← hq] at hodd
  have hpN : p ∈ normalizer ((𝔖.S : Subgroup G) : Set G) := hp ▸ zpow_mem hn a
  have hqN : q ∈ normalizer ((𝔖.S : Subgroup G) : Set G) := hq ▸ zpow_mem hn b
  have hp2 : IsPGroup 2 (zpowers p) := by
    have hdvd : orderOf p ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  obtain ⟨c, hc, hcS⟩ :=
    exists_mem_conj_mem_of_isSylowOf (G3cF.isSylowOf_S 𝔖 le_normalizer) hpN hp2
  have hpS : p ∈ (𝔖.S : Subgroup G) := (mem_normalizer_iff.1 hc p).2 hcS
  have hpx : p * x = x * p := mem_centralizer_iff.1 (mem_inf.1 hx).2 p hpS
  refine ⟨q, hqN, hodd, x, hx, fun h => hnx ?_⟩
  rw [← hab]
  calc p * q * x * (p * q)⁻¹ = p * (q * x * q⁻¹) * p⁻¹ := by group
    _ = x := by rw [h, hpx, mul_inv_cancel_right]

theorem exists_invariant_complement (h₁ : IsKleinFour 𝔖.S₁) {z u : G} (hzS₂ : z ∈ 𝔖.S₂)
    (hzord : orderOf z = 2) (hZ₂ : 𝔖.S₂ ⊓ centralizer (𝔖.S₂ : Set G) = zpowers z)
    (huN : u ∈ normalizer ((𝔖.S : Subgroup G) : Set G)) (hodd : Odd (orderOf u)) {x : G}
    (hx : x ∈ (𝔖.S : Subgroup G) ⊓ centralizer (𝔖.S : Set G)) (hux : u * x * u⁻¹ ≠ x) :
    ∃ W : Subgroup G, W ≤ (𝔖.S : Subgroup G) ⊓ centralizer (𝔖.S : Set G) ∧ Nat.card W = 4 ∧
      z ∉ W ∧ u ∈ normalizer (W : Set G) ∧ u ∉ centralizer (W : Set G) ∧
      W ⊓ zpowers z = ⊥ ∧ W ⊔ zpowers z = (𝔖.S : Subgroup G) ⊓ centralizer (𝔖.S : Set G) := by
  set Z : Subgroup G := (𝔖.S : Subgroup G) ⊓ centralizer (𝔖.S : Set G) with hZdef
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hzord; exact absurd hzord (by norm_num)
  have hZsq := Sec3Setting.center_S_sq_eq_one 𝔖 h₁ hzS₂ hzord hZ₂
  have hZ8 : Nat.card Z = 8 := Sec3Setting.center_S_card 𝔖 h₁ hzS₂ hzord hZ₂
  have hP : CFSG.Open.IsElemAbelian 2 Z := CFSG.CGT.Foote81L6.TStruct.isElemAbelian_two_iff.2 hZsq
  have huZ : ∀ y ∈ Z, u * y * u⁻¹ ∈ Z := by
    intro y hy
    refine mem_inf.2 ⟨(mem_normalizer_iff.1 huN y).1 (mem_inf.1 hy).1, ?_⟩
    exact (mem_normalizer_iff.1 (G4b.mem_normalizer_centralizer huN) y).1 (mem_inf.1 hy).2
  obtain ⟨Cs, D, hCP, hDP, hCiff, hDinv, hCD, hDfix, hdec⟩ :=
    CFSG.RankThree.GF2n.Tim77.sec414_elemAbelian_decomp hP hodd huZ
  have hzZ : z ∈ Z := mem_inf.2 ⟨𝔖.decomp.le_right hzS₂,
    Sec3Setting.central_of_mem_center_S₂ 𝔖 hzS₂ hZ₂⟩
  have hzC : z ∈ Cs := (hCiff z hzZ).1 (Sec3Setting.normalizer_fixes_z 𝔖 h₁ hzS₂ hzord hz1 hZ₂ huN)
  have hxC : x ∉ Cs := fun h => hux ((hCiff x hx).2 h)
  have hCDb : Cs ⊓ D = ⊥ := eq_bot_iff.2 fun g hg => (mem_bot).2 (hCD g (mem_inf.1 hg).1
    (mem_inf.1 hg).2)
  have hZeq : Cs ⊔ D = Z := by
    refine le_antisymm (sup_le hCP hDP) fun y hy => ?_
    obtain ⟨c, hc, d, hd, rfl, -⟩ := hdec y hy
    exact mul_mem (mem_sup_left hc) (mem_sup_right hd)
  have hcommZ : ∀ a ∈ Cs, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
    mem_centralizer_iff.1 (mem_inf.1 (hDP hb)).2 a (mem_inf.1 (hCP ha)).1
  have hcard : Nat.card Cs * Nat.card D = 8 := by
    rw [← hZ8, ← hZeq, card_sup_of_le_normalizer (le_normalizer_of_comm hcommZ) hCDb]
  have hC2 : Nat.card Cs = 2 := by
    have hdvd : Nat.card Cs ∣ 8 := ⟨_, hcard.symm⟩
    have hC1 : Nat.card Cs ≠ 1 := fun h => hz1 (by
      have h' := hzC
      rw [card_eq_one.1 h] at h'
      exact (mem_bot).1 h')
    have hC8 : Nat.card Cs ≠ 8 := fun h => hxC (by
      have hle : Cs ≤ Z := hCP
      rw [eq_of_le_of_card_ge hle (by rw [h, hZ8])]
      exact hx)
    have hC4 : Nat.card Cs ≠ 4 := by
      intro h4
      have hD2 : Nat.card D = 2 := by rw [h4] at hcard; omega
      have hDne : D ≠ ⊥ := fun h => by rw [h, card_bot] at hD2; omega
      obtain ⟨⟨d, hd⟩, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hDne
      have hd1' : d ≠ 1 := fun h => hd1 (Subtype.ext h)
      have hdd : d * d = 1 := hZsq d (hDP hd)
      have hzp : zpowers d = D := eq_of_le_of_card_ge (zpowers_le.2 hd)
        (by rw [hD2, Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hdd) hd1'])
      have hud : u * d * u⁻¹ ∈ zpowers d := hzp ▸ hDinv d hd
      rcases CFSG.CGT.Foote81L6.TStruct.eq_one_or_eq_of_mem_zpowers hdd hud with h | h
      · exact hd1' (by
          calc d = u⁻¹ * (u * d * u⁻¹) * u := by group
            _ = 1 := by rw [h]; group)
      · exact hd1' (hDfix d hd h)
    obtain ⟨m, hm, hm'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (show Nat.card Cs ∣ 2 ^ 3 by norm_num; exact hdvd)
    have hm4 : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 := by omega
    rcases hm4 with rfl | rfl | rfl | rfl
    · rw [pow_zero] at hm'
      exact absurd hm' hC1
    · rw [pow_one] at hm'
      exact hm'
    · exact absurd (hm'.trans (by norm_num)) hC4
    · exact absurd (hm'.trans (by norm_num)) hC8
  have hCz : Cs = zpowers z := (eq_of_le_of_card_ge (zpowers_le.2 hzC)
    (by rw [hC2, Nat.card_zpowers, hzord])).symm
  have hD4 : Nat.card D = 4 := by rw [hC2] at hcard; omega
  have hDne : D ≠ ⊥ := fun h => by rw [h, card_bot] at hD4; omega
  refine ⟨D, hDP, hD4, fun h => hz1 (hCD z hzC h), ?_, ?_, ?_, ?_⟩
  ·
    have hmap : D.map (MulAut.conj u).toMonoidHom ≤ D := by
      rintro _ ⟨d, hd, rfl⟩
      exact hDinv d hd
    rw [G4b.mem_normalizer_iff_map_conj_eq']
    exact eq_of_le_of_card_ge hmap (by rw [card_map_of_injective (MulAut.conj u).injective])
  ·
    intro hC
    obtain ⟨⟨d, hd⟩, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hDne
    apply hd1
    apply Subtype.ext
    apply hDfix d hd
    have h := mem_centralizer_iff.1 hC d hd
    rw [← h, mul_inv_cancel_right]
  · rw [← hCz, inf_comm, hCDb]
  · rw [← hCz, sup_comm, hZeq]

end G3bFourOdd

namespace Sec3Setting

variable {G : Type} [Group G] [Finite G]

theorem lemma34OddInput_of (𝔖 : Sec3Setting G) (h₁ : IsKleinFour 𝔖.S₁)
    (h₂ : ∀ x ∈ 𝔖.S₂, ∀ y ∈ 𝔖.S₂, orderOf x = 2 → orderOf y = 2 → IsConj x y) :
    Lemma34OddInput 𝔖 := by
  obtain ⟨z, hzS₂, hzord, hZ₂⟩ := exists_central_involution_S₂ 𝔖
  obtain ⟨u, huN, hodd, x, hx, hux⟩ :=
    G3bFourOdd.exists_odd_mem_normalizer_not_mem_centralizer_center 𝔖 h₁ h₂
  obtain ⟨W, hWZ, hW4, hzW, huNW, huCW, hWinf, hWsup⟩ :=
    G3bFourOdd.exists_invariant_complement 𝔖 h₁ hzS₂ hzord hZ₂ huN hodd hx hux
  have huC : u ∉ centralizer (𝔖.S : Set G) := fun h => hux (by
    rw [← mem_centralizer_iff.1 h x (mem_inf.1 hx).1, mul_inv_cancel_right])
  exact ⟨z, u, W, hzS₂, hzord, hZ₂, huN, hodd, huC, hWZ, hW4, hzW, huNW, huCW, hWinf, hWsup⟩

end Sec3Setting

end CFSG.GH72
