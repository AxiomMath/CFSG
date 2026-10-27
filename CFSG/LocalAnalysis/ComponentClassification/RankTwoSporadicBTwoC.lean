module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicBClasses
public import CFSG.Monster.B.CTIB.DistThreeProductFinal
public import CFSG.Monster.B.CTIB.Rank2158Final
public import CFSG.Monster.B.CTIB.HOuter
public import CFSG.Monster.B.TwoA.Amalgam.Exact3510
public import CFSG.Monster.B.TwoA.Amalgam.OrderFour
public import CFSG.Monster.B.TwoA.Amalgam.DistThreeCentFinal
public import CFSG.Monster.B.GSide.TwoBNative
public import CFSG.Monster.B.GSide.CompletionFusion
public import CFSG.Monster.B.GSide.TwoDNativeOrderFinal
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate1020
public import Certificates.Certificate1022
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import Certificates.Certificate3011
public import Certificates.Certificate3012
public import Certificates.Certificate3014
public import Certificates.Certificate3015
public import Certificates.Certificate3016
public import Certificates.Certificate3017
public import Certificates.Certificate3018
public import Certificates.Certificate3019
public import Certificates.Certificate3020
public import Certificates.Certificate3021
public import Certificates.Certificate3022
public import Certificates.Certificate3023
public import Certificates.Certificate3024
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3027
public import Certificates.Certificate3028
public import Certificates.Certificate3029
public import Certificates.Certificate3030
public import Certificates.Certificate3031
public import Certificates.Certificate3032
public import Certificates.Certificate3033
public import Certificates.Certificate3034
public import Certificates.Certificate3035
public import Certificates.Certificate3036
public import Certificates.Certificate3041
public import Certificates.Certificate3042
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3054
public import Certificates.Certificate3055
public import Certificates.Certificate3056
public import Certificates.Certificate3057
public import Certificates.Certificate3058
public import Certificates.Certificate3059
public import Certificates.Certificate3060
public import Certificates.Certificate3061
public import Certificates.Certificate3062
public import Certificates.Certificate3063
public import Certificates.Certificate3065
public import Certificates.Certificate3066
public import Certificates.Certificate3067
public import Certificates.Certificate3068
public import Certificates.Certificate3069
public import Certificates.Certificate3072
public import Certificates.Certificate3073
public import Certificates.Certificate3074
public import Certificates.Certificate3075
public import Certificates.Certificate3076
public import Certificates.Certificate3077
public import Certificates.Certificate3078
public import Certificates.Certificate3079
public import Certificates.Certificate3080
public import Certificates.Certificate3081
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate3098
public import Certificates.Certificate3099
public import Certificates.Certificate3100
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3110
public import Certificates.Certificate3111
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3118
public import Certificates.Certificate3121
public import Certificates.Certificate3122
public import Certificates.Certificate3124
public import Certificates.Certificate3125
public import Certificates.Certificate3126
public import Certificates.Certificate3127
public import Certificates.Certificate3175
public import Certificates.Certificate3176
public import Certificates.Certificate6007
public import Certificates.Certificate6023
public import Certificates.Certificate6024
public import Certificates.Certificate8955
public import Certificates.Certificate10032
public import Certificates.Certificate10033
public import Certificates.Certificate10034
public import Certificates.Certificate10035
public import Certificates.Certificate10069
public import Certificates.Certificate10070
public import Certificates.Certificate16001
public import Certificates.Certificate16003
public import Certificates.Certificate16010
public import Certificates.Certificate16015
public import Certificates.Certificate16016
public import Certificates.Certificate16021
public import Certificates.Certificate16022
public import Certificates.Certificate16023
public import Certificates.Certificate16028
public import Certificates.Certificate16029
public import Certificates.Certificate16033
public import Certificates.Certificate16035
public import Certificates.Certificate16036
public import Certificates.Certificate16040
public import Certificates.Certificate16042
public import Certificates.Certificate16951
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ComponentClassification.RankTwoSporadic.B

open Subgroup
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

theorem inv_conj_eq_of_conj_eq {h a b : G} (e : h * a * h⁻¹ = b) : h⁻¹ * b * h = a := by
  rw [← e]
  group

theorem commutator_conj_eq_of_fix_or_swap {g k p q : G}
    (hg : (g * p * g⁻¹ = p ∧ g * q * g⁻¹ = q) ∨ (g * p * g⁻¹ = q ∧ g * q * g⁻¹ = p))
    (hk : (k * p * k⁻¹ = p ∧ k * q * k⁻¹ = q) ∨ (k * p * k⁻¹ = q ∧ k * q * k⁻¹ = p)) :
    ⁅g, k⁆ * p * ⁅g, k⁆⁻¹ = p := by
  have e : ⁅g, k⁆ * p * ⁅g, k⁆⁻¹ = g * (k * (g⁻¹ * (k⁻¹ * p * k) * g) * k⁻¹) * g⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e]
  rcases hg with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;> rcases hk with ⟨k1, k2⟩ | ⟨k1, k2⟩
  · rw [inv_conj_eq_of_conj_eq k1, inv_conj_eq_of_conj_eq g1, k1, g1]
  · rw [inv_conj_eq_of_conj_eq k2, inv_conj_eq_of_conj_eq g2, k2, g1]
  · rw [inv_conj_eq_of_conj_eq k1, inv_conj_eq_of_conj_eq g2, k2, g2]
  · rw [inv_conj_eq_of_conj_eq k2, inv_conj_eq_of_conj_eq g1, k1, g2]

theorem le_centralizer_of_fix_or_swap {P : Subgroup G} (hP : ⁅P, P⁆ = P) {p q : G}
    (h : ∀ g ∈ P, (g * p * g⁻¹ = p ∧ g * q * g⁻¹ = q) ∨ (g * p * g⁻¹ = q ∧ g * q * g⁻¹ = p)) :
    P ≤ centralizer {p} := by
  rw [← hP, commutator_le]
  intro g hg k hk
  rw [mem_centralizer_singleton_iff]
  have e := commutator_conj_eq_of_fix_or_swap (h g hg) (h k hk)
  calc ⁅g, k⁆ * p = ⁅g, k⁆ * p * ⁅g, k⁆⁻¹ * ⁅g, k⁆ := by group
    _ = p * ⁅g, k⁆ := by rw [e]

theorem commutator_eq_self_of_isSimpleGroup_of_dvd {X : Subgroup G} [IsSimpleGroup X] {p : ℕ}
    [hp : Fact p.Prime] (hdvd : p ∣ Nat.card X) (hne : Nat.card X ≠ p) (h0 : Nat.card X ≠ 0) :
    ⁅X, X⁆ = X := by
  have : Finite X := Nat.finite_of_card_ne_zero h0
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
  · exfalso
    have hc : ∀ a b : X, a * b = b * a := fun a b => by
      have hab : ⁅a, b⁆ ∈ commutator X := commutator_mem_commutator (mem_top _) (mem_top _)
      rwa [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hab
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hn : (zpowers g).Normal := ⟨fun n hn x => by
      rw [hc x n, mul_inv_cancel_right]
      exact hn⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (zpowers g) with h1 | h1
    · have hg1 : g = 1 := by
        have hmem : g ∈ zpowers g := mem_zpowers g
        rwa [h1, mem_bot] at hmem
      rw [hg1, orderOf_one] at hg
      exact hp.out.one_lt.ne hg
    · exact hne (by rw [← hg, ← Nat.card_zpowers, h1, card_top])
  · have hm := congrArg (map X.subtype) h
    rwa [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at hm

theorem eq_one_of_forall_commute {X : Subgroup G} [IsSimpleGroup X] (hP : ⁅X, X⁆ = X)
    (hne : X ≠ ⊥) {k : G} (hk : k ∈ X) (hc : ∀ g ∈ X, g * k = k * g) : k = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
  · have hz : (⟨k, hk⟩ : X) ∈ center X := mem_center_iff.2 fun g => Subtype.ext (hc g g.2)
    rw [h, mem_bot] at hz
    exact congrArg Subtype.val hz
  · exfalso
    apply hne
    rw [← hP, commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [mem_centralizer_iff]
    intro b hb
    have hz : (⟨a, ha⟩ : X) ∈ center X := h ▸ mem_top _
    exact congrArg Subtype.val ((mem_center_iff.1 hz) ⟨b, hb⟩)

theorem le_centralizer_left_of_le {H : Subgroup G} {a b : G}
    (h : H ≤ centralizer ({a, b} : Set G)) : H ≤ centralizer {a} := fun _ hg =>
  mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 (h hg)) a (Set.mem_insert _ _)).symm

theorem le_centralizer_right_of_le {H : Subgroup G} {a b : G}
    (h : H ≤ centralizer ({a, b} : Set G)) : H ≤ centralizer {b} := fun _ hg =>
  mem_centralizer_singleton_iff.2
    ((mem_centralizer_iff.1 (h hg)) b (Set.mem_insert_of_mem _ rfl)).symm

theorem le_centralizer_pair {H : Subgroup G} {a b : G} (ha : H ≤ centralizer {a})
    (hb : H ≤ centralizer {b}) : H ≤ centralizer ({a, b} : Set G) := fun _ hg =>
  mem_centralizer_iff.2 fun z hz => by
    rcases hz with rfl | rfl
    · exact (mem_centralizer_singleton_iff.1 (ha hg)).symm
    · exact (mem_centralizer_singleton_iff.1 (hb hg)).symm

theorem le_centralizer_mul_pow {H : Subgroup G} {a b : G} (ha : H ≤ centralizer {a})
    (hb : H ≤ centralizer {b}) (n : ℕ) : H ≤ centralizer {(a * b) ^ n} := fun _ hg =>
  mem_centralizer_singleton_iff.2 ((Commute.mul_right (mem_centralizer_singleton_iff.1 (ha hg))
    (mem_centralizer_singleton_iff.1 (hb hg))).pow_right n).eq

theorem eq_of_card_le_four {α : Type*} [Finite α] (h : Nat.card α ≤ 4) {a b c d : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (x : α) : x = a ∨ x = b ∨ x = c ∨ x = d := by
  by_contra hx
  simp only [not_or] at hx
  obtain ⟨hxa, hxb, hxc, hxd⟩ := hx
  have hinj : Function.Injective ![a, b, c, d, x] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
      first
      | exact absurd hij ‹_›
      | exact absurd hij.symm ‹_›
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hle
  omega

theorem eq_of_mem_inf_centralizer {R F : Subgroup G} (hFR : F ≤ R)
    (hRcard : Nat.card R = 4 * Nat.card F) (hF0 : Nat.card F ≠ 0)
    (hcen : ∀ k ∈ F, (∀ g ∈ F, g * k = k * g) → k = 1) {a b z : G}
    (ha : a ∈ R ⊓ centralizer (F : Set G)) (hb : b ∈ R ⊓ centralizer (F : Set G))
    (hz : z ∈ R ⊓ centralizer (F : Set G)) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b)
    (hb2 : b * b = 1) : z = 1 ∨ z = a ∨ z = b ∨ z = a * b := by
  set K := R ⊓ centralizer (F : Set G)
  have hR0 : Nat.card R ≠ 0 := by rw [hRcard]; omega
  have : Finite R := Nat.finite_of_card_ne_zero hR0
  have : Finite K := Finite.of_injective _ (inclusion_injective (inf_le_left : K ≤ R))
  let f : K → R ⧸ F.subgroupOf R := fun k => ((⟨k, k.2.1⟩ : R) : R ⧸ F.subgroupOf R)
  have hf : Function.Injective f := by
    intro k₁ k₂ h12
    have hmem := QuotientGroup.eq.1 h12
    rw [mem_subgroupOf] at hmem
    have hmem' : (k₁ : G)⁻¹ * k₂ ∈ F := by simpa using hmem
    have hc : (k₁ : G)⁻¹ * k₂ ∈ centralizer (F : Set G) :=
      mul_mem (inv_mem k₁.2.2) k₂.2.2
    have h1 := hcen _ hmem' ((mem_centralizer_iff).1 hc)
    exact Subtype.ext (by rw [← mul_inv_cancel_left (k₁ : G) k₂, h1, mul_one])
  have hq : Nat.card (R ⧸ F.subgroupOf R) = 4 := by
    have h := card_eq_card_quotient_mul_card_subgroup (F.subgroupOf R)
    rw [Nat.card_congr (subgroupOfEquivOfLe hFR).toEquiv, hRcard] at h
    have hpos : 0 < Nat.card F := Nat.pos_of_ne_zero hF0
    exact (Nat.eq_of_mul_eq_mul_right hpos h).symm
  have hK : Nat.card K ≤ 4 := (Nat.card_le_card_of_injective f hf).trans hq.le
  have hab1 : a * b ≠ 1 := fun h => hab (by
    calc a = a * b * b := by rw [mul_assoc, hb2, mul_one]
      _ = b := by rw [h, one_mul])
  have hne : ∀ {s t : G} (hs : s ∈ K) (ht : t ∈ K), s ≠ t → (⟨s, hs⟩ : K) ≠ ⟨t, ht⟩ :=
    fun _ _ h h' => h (congrArg Subtype.val h')
  have hres := eq_of_card_le_four hK (a := ⟨1, K.one_mem⟩) (b := ⟨a, ha⟩) (c := ⟨b, hb⟩)
    (d := ⟨a * b, K.mul_mem ha hb⟩) (hne _ _ (Ne.symm ha1)) (hne _ _ (Ne.symm hb1))
    (hne _ _ (Ne.symm hab1)) (hne _ _ hab) (hne _ _ fun h => hb1 (by
      calc b = a⁻¹ * (a * b) := by group
        _ = 1 := by rw [← h, inv_mul_cancel]))
    (hne _ _ fun h => ha1 (by
      calc a = a * b * b⁻¹ := by group
        _ = 1 := by rw [← h, mul_inv_cancel])) ⟨z, hz⟩
  rcases hres with h | h | h | h <;> have h' := congrArg Subtype.val h
  · exact Or.inl h'
  · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr (Or.inl h'))
  · exact Or.inr (Or.inr (Or.inr h'))

theorem classFact_of_mulEquiv {W₁ W₂ : Type*} [Group W₁] [Group W₂] (e : W₁ ≃* W₂)
    {r₁ : W₁ → ℕ} {r₂ : W₂ → ℕ} (hr : ∀ a, r₂ (e a) = r₁ a) {x : W₁}
    (h : ClassFact r₂ (e x)) : ClassFact r₁ x := by
  obtain ⟨P, hP, hPx, hb⟩ := h
  refine ⟨P.map e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rw [← map_commutator, hP]
  · rintro _ ⟨p, hp, rfl⟩
    rw [mem_centralizer_singleton_iff]
    apply e.injective
    have hpx := mem_centralizer_singleton_iff.1 (hPx hp)
    simpa only [MulEquiv.coe_toMonoidHom, map_mul, MulEquiv.apply_symm_apply] using hpx
  · intro y hy hyx hy2 hy1 hyx'
    have hy' : e y ∈ centralizer (P : Set W₂) := by
      rw [mem_centralizer_iff] at hy ⊢
      intro p hp
      have hc := congrArg e (hy (e.symm p) ⟨p, hp, rfl⟩)
      simpa only [map_mul, MulEquiv.apply_symm_apply] using hc
    have hlt := hb (e y) hy' (by rw [← map_mul, ← map_mul, hyx]) (by rw [← map_pow, hy2, map_one])
      (fun h1 => hy1 (e.injective (by rw [h1, map_one]))) (fun h1 => hyx' (e.injective h1))
    rwa [hr, hr] at hlt

end Generic

open CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
  CFSG.Monster.B.CTIB CFSG.Monster.B.GSide

theorem false_of_le_centralizer_isConj_xhatS
    {P : Subgroup Shat} (h17 : 17 ∣ Nat.card P) {z : Shat} (hz : IsConj z xhatS)
    (hP : P ≤ centralizer {z}) : False := by
  obtain ⟨φ⟩ := centralizer_equiv_of_isConj hz
  have h1 := card_dvd_of_le hP
  rw [Nat.card_congr φ.toEquiv, natCard_centralizer_xhatS] at h1
  exact absurd (h17.trans h1) (by norm_num)

theorem clabelS_eq_or_dist_eq_three
    {P : Subgroup Shat} (h17 : 17 ∣ Nat.card P) {a u : CVert}
    (ha : P ≤ centralizer {clabelS a}) (hu : P ≤ centralizer {clabelS u}) :
    clabelS u = clabelS a ∨ cgraph.dist a u = 3 := by
  have hamb := ambientRootOrbitsHyp
  have hL := labelsInput_of_ambient hamb
  have hinj := clabel_injective_of_inputs hL (outerInput_of_ambient hamb)
    (pathInput_of_ambient hamb) (typeThreeBoundInput_of_ambient hamb)
  rcases commute_or_three_or_four (diameter_three_rank_five_of_ambient hamb).1 hL a u with
    hc | ⟨h3, -⟩ | ⟨h4, -⟩
  · by_cases he : clabelS a = clabelS u
    · exact Or.inl he.symm
    by_cases hx : IsConj (clabelS a * clabelS u) xhatS
    · exact (false_of_le_centralizer_isConj_xhatS h17 hx
        (by simpa only [pow_one] using le_centralizer_mul_pow ha hu 1)).elim
    · exact Or.inr (dist_eq_three_of_commute hamb he hc hx)
  · exfalso
    have hcard := (native_order_three_common_neighbors_exact_3510.1 a u h3).2.2.2.2.2
    have hle : P ≤ vStab a ⊓ vStab u := by
      rw [← centralizer_pair_eq_inf hinj a u]
      exact le_centralizer_pair ha hu
    have hd := card_dvd_of_le hle
    rw [hcard] at hd
    exact absurd (h17.trans hd) (by norm_num)
  · exfalso
    obtain ⟨s, hp, hqs⟩ := (native_coset_graph_order_four_common_neighbors.1 a u h4).2.2.1
    have hsq := sq_clabel_mul_of_mem_cPi h4 hp hqs
    have e : (clabelS a * clabelS u) ^ 2 = s⁻¹ * xhatS * s := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv, coe_clabelS]
      exact hsq
    have hc : IsConj ((clabelS a * clabelS u) ^ 2) xhatS := by
      rw [e]
      exact isConj_iff.2 ⟨s, by group⟩
    exact false_of_le_centralizer_isConj_xhatS h17 hc (le_centralizer_mul_pow ha hu 2)

theorem clabelS_eq_of_le_centralizer
    {v w : CVert} (hvw : cgraph.dist v w = 3) {F : Subgroup Shat}
    (hFR : F ≤ centralizer ({clabelS v, clabelS w} : Set Shat))
    (hRcard : Nat.card (centralizer ({clabelS v, clabelS w} : Set Shat)) = 4 * Nat.card F)
    (h17 : 17 ∣ Nat.card F) (hF0 : Nat.card F ≠ 0)
    (hcen : ∀ k ∈ F, (∀ g ∈ F, g * k = k * g) → k = 1) {u : CVert}
    (hu : F ≤ centralizer {clabelS u}) : clabelS u = clabelS v ∨ clabelS u = clabelS w := by
  have hamb := ambientRootOrbitsHyp
  have hL := labelsInput_of_ambient hamb
  have hFv := le_centralizer_left_of_le hFR
  have hFw := le_centralizer_right_of_le hFR
  rcases clabelS_eq_or_dist_eq_three h17 hFv hu with h | h
  · exact Or.inl h
  rcases clabelS_eq_or_dist_eq_three h17 hFw hu with h' | h'
  · exact Or.inr h'
  exfalso
  have hcu := (hL v u h).2.2.2
  have hcu' := (hL w u h').2.2.2
  have hcvw := (hL v w hvw).2.2.2
  have hmemC : ∀ {t : Shat}, F ≤ centralizer {t} → t ∈ centralizer (F : Set Shat) :=
    fun hF => mem_centralizer_iff.2 fun g hg => mem_centralizer_singleton_iff.1 (hF hg)
  have hmemR : ∀ {t : Shat}, Commute t (clabelS v) → Commute t (clabelS w) →
      t ∈ centralizer ({clabelS v, clabelS w} : Set Shat) := fun h1 h2 =>
    mem_centralizer_iff.2 fun z hz => by
      rcases hz with rfl | rfl
      · exact h1.eq.symm
      · exact h2.eq.symm
  rcases eq_of_mem_inf_centralizer hFR hRcard hF0 hcen
      (a := clabelS v) (b := clabelS w) (z := clabelS u)
      ⟨hmemR (Commute.refl _) hcvw.symm, hmemC hFv⟩ ⟨hmemR hcvw (Commute.refl _), hmemC hFw⟩
      ⟨hmemR hcu hcu', hmemC hu⟩ (clabelS_ne_one v) (clabelS_ne_one w)
      (hL v w hvw).2.2.1.symm (clabelS_mul_clabelS w) with hz | hz | hz | hz
  · exact clabelS_ne_one u hz
  · exact (hL v u h).2.2.1 hz
  · exact (hL w u h').2.2.1 hz
  · have h1 : rankS (clabelS u) = 1860 := rank_clabelS u
    have h2 : rankS (clabelS v * clabelS w) = 2158 := rank_clabelS_mul_of_dist_three hvw
    rw [hz] at h1
    omega

theorem classFact_rankS_twoC
    {v w : CVert} (hvw : cgraph.dist v w = 3) : ClassFact rankS (clabelS v * clabelS w) := by
  have hamb := ambientRootOrbitsHyp
  have hL := labelsInput_of_ambient hamb
  have hO := outerInput_of_ambient hamb
  have hPa := pathInput_of_ambient hamb
  have hT := typeThreeBoundInput_of_ambient hamb
  obtain ⟨-, hRv, hRC, -, -, -, -, -, hFcard, -, -, -, hFs, -⟩ :=
    distance_three_product_full_centralizer_final hvw rfl rfl rfl
  obtain ⟨-, -, -, -, -, hRcard', -⟩ :=
    native_distance_three_pair_is_full_local_centralizer_final hvw
  set R := centralizer ({clabelS v, clabelS w} : Set Shat) with hR
  set F := ⁅R, R⁆ with hF
  have hRcard : Nat.card R = 4 * Nat.card F := by rw [hRv, hRcard', hFcard]
  have h17 : 17 ∣ Nat.card F := by
    rw [hFcard]
    norm_num
  have hFR : F ≤ R := commutator_self_le R
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  have := hFs
  have hPF : ⁅F, F⁆ = F := commutator_eq_self_of_isSimpleGroup_of_dvd (p := 17) h17
    (by rw [hFcard]; norm_num) (by rw [hFcard]; norm_num)
  have hF0 : Nat.card F ≠ 0 := by
    rw [hFcard]
    norm_num
  have hFne : F ≠ ⊥ := fun h => by
    rw [h, card_bot] at hFcard
    norm_num at hFcard
  have hcen : ∀ k ∈ F, (∀ g ∈ F, g * k = k * g) → k = 1 := fun k hk hc =>
    eq_one_of_forall_commute hPF hFne hk hc
  have hFv : F ≤ centralizer {clabelS v} := le_centralizer_left_of_le hFR
  have hFw : F ≤ centralizer {clabelS w} := le_centralizer_right_of_le hFR
  have hcvw := (hL v w hvw).2.2.2
  have hvw1 : clabelS v * clabelS w ≠ 1 := fun h => (hL v w hvw).2.2.1
    ((inv_eq_of_mul_eq_one_right (clabelS_mul_clabelS w)).symm.trans
      (inv_eq_of_mul_eq_one_left h))
  refine ⟨F, hPF, hFR.trans hRC, fun y hy hyx hy2 hy1 hyx' => ?_⟩
  have hrx : rankS (clabelS v * clabelS w) = 2158 := rank_clabelS_mul_of_dist_three hvw
  rw [hrx]
  have hyo : orderOf y = 2 := orderOf_eq_prime hy2 hy1
  have hPy : F ≤ centralizer {y} := fun g hg =>
    mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 hy) g hg)
  rcases rankS_mem_of_orderOf hyo with h | h | h | h
  · omega
  · omega
  · exfalso
    have hxo : orderOf (clabelS v * clabelS w) = 2 :=
      orderOf_eq_prime (sq_clabelS_mul_of_commute hcvw.symm) hvw1
    obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_of_rankS_eq hxo hyo (hrx.trans h.symm))
    obtain ⟨p, hp⟩ := exists_clabelS_eq_of_isConj (isConj_iff.2 ⟨c, rfl⟩ :
      IsConj (clabelS v) (c * clabelS v * c⁻¹))
    obtain ⟨q, hq⟩ := exists_clabelS_eq_of_isConj (isConj_iff.2 ⟨c, rfl⟩ :
      IsConj (clabelS w) (c * clabelS w * c⁻¹))
    have hy' : y = clabelS p * clabelS q := by
      rw [hp, hq, ← hc]
      group
    have hpq : cgraph.dist p q = 3 := by
      refine dist_eq_three_of_commute hamb ?_ ?_ ?_
      · rw [hp, hq]
        intro h'
        exact (hL v w hvw).2.2.1 (mul_left_cancel (mul_right_cancel h')).symm
      · rw [hp, hq]
        show c * clabelS v * c⁻¹ * (c * clabelS w * c⁻¹) =
          c * clabelS w * c⁻¹ * (c * clabelS v * c⁻¹)
        calc c * clabelS v * c⁻¹ * (c * clabelS w * c⁻¹) = c * (clabelS v * clabelS w) * c⁻¹ := by
              group
          _ = c * (clabelS w * clabelS v) * c⁻¹ := by rw [hcvw.eq]
          _ = c * clabelS w * c⁻¹ * (c * clabelS v * c⁻¹) := by group
      · rw [← hy']
        intro hconj
        have e1 := rankS_conj hconj
        rw [h, ← sEquiv_xs, rankS_sEquiv_xs] at e1
        norm_num at e1
    rw [hy'] at hPy hyx'
    have hfs : ∀ g ∈ F, (g * clabelS p * g⁻¹ = clabelS p ∧ g * clabelS q * g⁻¹ = clabelS q) ∨
        (g * clabelS p * g⁻¹ = clabelS q ∧ g * clabelS q * g⁻¹ = clabelS p) := fun g hg =>
      (mem_centralizer_mul_iff hL hO hPa hT hpq g).1 (hPy hg)
    have hFp := le_centralizer_of_fix_or_swap hPF hfs
    have hFq := le_centralizer_of_fix_or_swap hPF fun g hg =>
      (hfs g hg).imp (fun h => ⟨h.2, h.1⟩) fun h => ⟨h.2, h.1⟩
    have hne := (hL p q hpq).2.2.1
    rcases clabelS_eq_of_le_centralizer hvw hFR hRcard h17 hF0 hcen hFp with hp' | hp' <;>
      rcases clabelS_eq_of_le_centralizer hvw hFR hRcard h17 hF0 hcen hFq with hq' | hq'
    · exact hne (hq'.trans hp'.symm)
    · exact hyx' (by rw [hp', hq'])
    · exact hyx' (by rw [hp', hq', hcvw.eq])
    · exact hne (hq'.trans hp'.symm)
  · exfalso
    have hc := natCard_centralizer_of_rankS_eq_2168 centralizer_t2DS_le_normalizer y hyo h
    have hd := h17.trans (card_dvd_of_le hPy)
    rw [hc] at hd
    exact absurd hd (by norm_num)

theorem rankS_sEquiv_iotaEquiv
    (X : NativeSporadic.B) : rankS (sEquiv (iotaEquiv X)) = rankB X := by
  unfold rankS rankB
  rw [MulEquiv.symm_apply_apply, ← rank_iotaEquiv_symm, MulEquiv.symm_apply_apply]

theorem twoC_classFact
    : ClassFact rankB (classRep 5) := by
  have hamb := ambientRootOrbitsHyp
  obtain ⟨w, hw⟩ := (diameter_three_rank_five_of_ambient hamb).2.1 cv0
  obtain ⟨X, hXe⟩ : ∃ X : NativeSporadic.B, sEquiv (iotaEquiv X) = clabelS cv0 * clabelS w :=
    ⟨iotaEquiv.symm (sEquiv.symm _), by rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]⟩
  have hS : ClassFact (fun s => rankS (sEquiv s)) (iotaEquiv X) :=
    classFact_of_mulEquiv sEquiv (r₁ := fun s => rankS (sEquiv s)) (fun _ => rfl)
      (by rw [hXe]; exact classFact_rankS_twoC hw)
  have hX : ClassFact rankB X :=
    @classFact_of_mulEquiv NativeSporadic.B Sbp inferInstance inferInstance iotaEquiv rankB
      (fun s => rankS (sEquiv s)) (fun a => rankS_sEquiv_iotaEquiv a) X hS
  have hXr : rankB X = 2158 := by
    rw [← rankS_sEquiv_iotaEquiv, hXe]
    exact rank_clabelS_mul_of_dist_three hw
  have hX2 : X ^ 2 = 1 := by
    have hc := ((labelsInput_of_ambient hamb) cv0 w hw).2.2.2
    apply iotaEquiv.injective
    apply sEquiv.injective
    rw [map_pow, map_pow, hXe, map_one, map_one, sq_clabelS_mul_of_commute hc.symm]
  have hX1 : X ≠ 1 := fun h => by
    rw [h] at hXr
    simp [rankB] at hXr
  have hc5 : IsConj X (classRep 5) := by
    obtain ⟨i, hi, hc, hr⟩ := isConj_classRep hX2 hX1
    obtain ⟨-, h1, h0, -, h3⟩ := classes_B
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · omega
    · omega
    · exact hc
    · omega
  obtain ⟨g, hg⟩ := isConj_iff.1 hc5
  rw [← hg]
  exact @classFact_conj NativeSporadic.B inferInstance rankB rankB_conj X hX g

end CFSG.ComponentClassification.RankTwoSporadic.B
