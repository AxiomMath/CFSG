module

public import CFSG.Geometry.GeneralizedQuadrangles.Moufang.NoSpansTwoAux

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons CFSG.Quasithin CFSG.Quasithin.Stroth
open scoped Pointwise

variable {V : Type} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
  {H : Type} [Group H] [MulAction H V] [FaithfulSMul H V] [GraphAction H Γ]

structure NoSpansTwoBaseData
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2))
    {s t : ℕ} (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) (hst : s ≤ t)
    (hM : MoufangCondition H Γ 4) {p : V} (hp : c p = 0)
    (h1 : ∀ x, Γ.dist p x = 4 → (spanSet Γ p x).ncard = 2)
    (h2 : ∀ L M, Γ.Adj p L → Γ.dist L M = 4 → (spanSet Γ L M).ncard = 2) where
  L0 : V
  hL0 : Γ.Adj p L0
  L1 : V
  hL1 : Γ.Adj p L1
  hL10 : L1 ≠ L0
  L2 : V
  hL2 : Γ.Adj p L2
  hL20 : L2 ≠ L0
  hL21 : L2 ≠ L1
  hcL0 : c L0 = 1
  hcL1 : c L1 = 1
  hcL2 : c L2 = 1
  hL10' : L0 ≠ L1
  hL20' : L0 ≠ L2
  hL21' : L1 ≠ L2
  ht2 : 2 ≤ t
  hs2 : 2 ≤ s
  hOpp : (Finset.univ.filter fun y => Γ.dist p y = 4).card = s ^ 2 * t
  hpos : 0 < s ^ 2 * t
  y : V
  hyF : y ∈ Finset.univ.filter fun y => Γ.dist p y = 4
  hy4 : Γ.dist p y = 4
  hcy : c y = 0
  hyL0 : Γ.dist y L0 = 3
  hyL1 : Γ.dist y L1 = 3
  z0 : V
  z1 : V
  hz0L0 : Γ.Adj L0 z0
  hz1L1 : Γ.Adj L1 z1
  hyz0 : Γ.dist y z0 = 2
  hyz1 : Γ.dist y z1 = 2
  hcz0 : c z0 = 0
  hcz1 : c z1 = 0
  hz0p : z0 ≠ p
  hz1p : z1 ≠ p
  M0 : V
  M1 : V
  hyM0 : Γ.Adj y M0
  hz0M0 : Γ.Adj z0 M0
  hyM1 : Γ.Adj y M1
  hz1M1 : Γ.Adj z1 M1
  hcM0 : c M0 = 1
  hcM1 : c M1 = 1
  hM0ne : M0 ≠ L0
  hM1ne : M1 ≠ L1
  hzp0 : Γ.dist p z0 = 2
  hzp1 : Γ.dist p z1 = 2
  hpM0 : ¬ Γ.Adj p M0
  hpM1 : ¬ Γ.Adj p M1
  hdistpM0 : Γ.dist p M0 = 3
  hdistpM1 : Γ.dist p M1 = 3
  v : ZMod 8 → V
  hv : IsPolygonApartment Γ 4 v
  hv0 : v 0 = p
  h1v : ∀ x, Γ.dist (v 0) x = 4 → (spanSet Γ (v 0) x).ncard = 2
  E : Subgroup H
  hE0 : Γ.Adj (v 0) (v 1)
  hv4 : Γ.dist (v 0) (v 4) = 4
  hEcard : Nat.card ↥E = s * t * s
  hfree : ∀ (g : ↥E) {x : V}, Γ.dist p x = 4 → (g : H) • x = x → g = 1
  htrans : ∀ x x' : V, Γ.dist p x = 4 → Γ.dist p x' = 4 → ∃ g : ↥E, (g : H) • x = x'
  S0 : Subgroup H
  S1 : Subgroup H
  S0s : Subgroup H
  S1s : Subgroup H
  w2 : V
  hw2L2 : Γ.Adj L2 w2
  hw2p : w2 ≠ p
  M2 : V
  hw2M2 : Γ.Adj w2 M2
  hM2L2 : M2 ≠ L2
  hexists_smul_L0 : ∀ u u' : V, Γ.Adj L0 u → Γ.Adj L0 u' → u ≠ p → u' ≠ p → ∃ g ∈ E, g • u = u'
  horbit0 : (MulAction.orbit ↥E z0 : Set V) = Γ.neighborSet L0 \ {p}
  hL0p_card : (Γ.neighborSet L0 \ {p}).ncard = s
  horbit0card : Nat.card ↥(MulAction.orbit ↥E z0) = s
  hS0s_card : Nat.card ↥S0s = s * t
  Uloc : Subgroup H
  hUloc_le : Uloc ≤ E
  hUloc_card : Nat.card ↥Uloc = t
  hUloc_trans : ∀ K K' : V, Γ.Adj z0 K → K ≠ L0 → Γ.Adj z0 K' → K' ≠ L0 → ∃ g ∈ Uloc, g • K = K'
  U0 : Subgroup H
  hU0leE : U0 ≤ E
  hU0card : Nat.card ↥U0 = s
  hU0leS0 : U0 ≤ S0
  hmaps : ∀ g : ↥S0, (g : H) • y ∈ Γ.neighborSet M0 \ {z0}
  hS0le : Nat.card ↥S0 ≤ s
  hS0_eq_U0 : S0 = U0
  hS0s_fix : ∀ θ : H, θ ∈ S0s → ∀ u : V, Γ.Adj L0 u → θ • u = u
  hE_eq : E = elationGroup H Γ v
  hS0_eq : S0 = E ⊓ MulAction.stabilizer H M0
  hS1_eq : S1 = E ⊓ MulAction.stabilizer H M1
  hS0s_eq : S0s = E ⊓ MulAction.stabilizer H z0
  hS1s_eq : S1s = E ⊓ MulAction.stabilizer H z1
  hUloc_eq : Uloc = rootGroup H Γ L0 p L2
  hU0_eq : U0 = rootGroup H Γ p L0 z0

public noncomputable def noSpansTwoBase
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) (hst : s ≤ t)
    (hM : MoufangCondition H Γ 4) {p : V} (hp : c p = 0)
    (h1 : ∀ x, Γ.dist p x = 4 → (spanSet Γ p x).ncard = 2)
    (h2 : ∀ L M, Γ.Adj p L → Γ.dist L M = 4 → (spanSet Γ L M).ncard = 2) :
    NoSpansTwoBaseData hP hT c hdeg hst hM hp h1 h2 := by
  classical
  have ht2 : 2 ≤ t := by
    have h3 := hT p
    rw [hdeg p, if_pos hp] at h3
    omega
  have hs2 : 2 ≤ s := two_le_s hP hT c hdeg
  have hL0_exists : ∃ L : V, Γ.Adj p L := by
    have h3 : 3 ≤ (Γ.neighborFinset p).card := by
      rw [card_neighborFinset_eq_degree]
      simpa [hdeg p, if_pos hp] using hT p
    obtain ⟨L, hL⟩ := Finset.card_pos.mp (by omega : 0 < (Γ.neighborFinset p).card)
    exact ⟨L, by simpa using hL⟩
  let L0 : V := Classical.choose hL0_exists
  have hL0 : Γ.Adj p L0 := Classical.choose_spec hL0_exists
  have hL1_exists := exists_adj_ne_two hT p L0 L0
  let L1 : V := Classical.choose hL1_exists
  have hL1_spec := Classical.choose_spec hL1_exists
  have hL1 : Γ.Adj p L1 := hL1_spec.1
  have hL10 : L1 ≠ L0 := hL1_spec.2.1
  have hL2_exists := exists_adj_ne_two hT p L0 L1
  let L2 : V := Classical.choose hL2_exists
  have hL2_spec := Classical.choose_spec hL2_exists
  have hL2 : Γ.Adj p L2 := hL2_spec.1
  have hL20 : L2 ≠ L0 := hL2_spec.2.1
  have hL21 : L2 ≠ L1 := hL2_spec.2.2
  have hcL0 : c L0 = 1 := color_eq_one_of_adj_of_color_eq_zero hp hL0
  have hcL1 : c L1 = 1 := color_eq_one_of_adj_of_color_eq_zero hp hL1
  have hcL2 : c L2 = 1 := color_eq_one_of_adj_of_color_eq_zero hp hL2
  have hL10' : L0 ≠ L1 := fun h => hL10 h.symm
  have hL20' : L0 ≠ L2 := fun h => hL20 h.symm
  have hL21' : L1 ≠ L2 := fun h => hL21 h.symm
  have hOpp : (Finset.univ.filter fun y => Γ.dist p y = 4).card = s ^ 2 * t :=
    card_opposite hP hT c hdeg hp
  have hpos : 0 < s ^ 2 * t := Nat.mul_pos (pow_pos (by omega) 2) (by omega)
  have hy_exists : ∃ y, y ∈ Finset.univ.filter (fun y => Γ.dist p y = 4) :=
    Finset.card_pos.mp (by rw [hOpp]; exact hpos)
  let y : V := Classical.choose hy_exists
  have hyF : y ∈ Finset.univ.filter (fun y => Γ.dist p y = 4) := Classical.choose_spec hy_exists
  have hy4 : Γ.dist p y = 4 := by simpa using hyF
  have hcy : c y = 0 := by
    have heven : Even (Γ.dist p y) := by rw [hy4]; norm_num
    have h : c p = c y := (hP.eq_iff_even_dist c p y).2 heven
    rw [hp] at h
    exact h.symm
  have hyL0 : Γ.dist y L0 = 3 := dist_eq_three_of_adj_of_dist_eq_four hP hy4 hL0
  have hyL1 : Γ.dist y L1 = 3 := dist_eq_three_of_adj_of_dist_eq_four hP hy4 hL1
  let z0 : V := proj hP hyL0
  let z1 : V := proj hP hyL1
  have hz0L0 : Γ.Adj L0 z0 := proj_adj hP hyL0
  have hz1L1 : Γ.Adj L1 z1 := proj_adj hP hyL1
  have hyz0 : Γ.dist y z0 = 2 := proj_dist hP hyL0
  have hyz1 : Γ.dist y z1 = 2 := proj_dist hP hyL1
  have hcz0 : c z0 = 0 := color_eq_zero_of_dist_eq_two hP hcy hyz0
  have hcz1 : c z1 = 0 := color_eq_zero_of_dist_eq_two hP hcy hyz1
  have hz0p : z0 ≠ p := by
    intro h
    rw [h, SimpleGraph.dist_comm] at hyz0
    omega
  have hz1p : z1 ≠ p := by
    intro h
    rw [h, SimpleGraph.dist_comm] at hyz1
    omega
  let M0 : V := commonNeighbor hP hyz0
  let M1 : V := commonNeighbor hP hyz1
  have hyM0 : Γ.Adj y M0 := commonNeighbor_adj_left hP hyz0
  have hz0M0 : Γ.Adj z0 M0 := commonNeighbor_adj_right hP hyz0
  have hyM1 : Γ.Adj y M1 := commonNeighbor_adj_left hP hyz1
  have hz1M1 : Γ.Adj z1 M1 := commonNeighbor_adj_right hP hyz1
  have hcM0 : c M0 = 1 := color_eq_one_of_adj_of_color_eq_zero hcy hyM0
  have hcM1 : c M1 = 1 := color_eq_one_of_adj_of_color_eq_zero hcy hyM1
  have hM0ne : M0 ≠ L0 := by
    intro h
    have h1 : Γ.Adj y L0 := by rw [← h]; exact hyM0
    have h2 : Γ.dist y L0 = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h1
    omega
  have hM1ne : M1 ≠ L1 := by
    intro h
    have h1 : Γ.Adj y L1 := by rw [← h]; exact hyM1
    have h2 : Γ.dist y L1 = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h1
    omega
  have hzp0 : Γ.dist p z0 = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hL0 hz0L0 (Ne.symm hz0p)
  have hzp1 : Γ.dist p z1 = 2 :=
    dist_eq_two_of_adj_of_adj_of_ne hP hL1 hz1L1 (Ne.symm hz1p)
  have hpM0 : ¬ Γ.Adj p M0 := by
    intro h
    have hL : L0 = M0 := (existsUnique_commonNeighbor hP hzp0).unique
      ⟨hL0, hz0L0.symm⟩ ⟨h, hz0M0⟩
    exact hM0ne hL.symm
  have hpM1 : ¬ Γ.Adj p M1 := by
    intro h
    have hL : L1 = M1 := (existsUnique_commonNeighbor hP hzp1).unique
      ⟨hL1, hz1L1.symm⟩ ⟨h, hz1M1⟩
    exact hM1ne hL.symm
  have hdistpM0 : Γ.dist p M0 = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c hpM0 (by rw [hp, hcM0]; decide)
  have hdistpM1 : Γ.dist p M1 = 3 :=
    dist_eq_three_of_not_adj_of_color_ne hP c hpM1 (by rw [hp, hcM1]; decide)
  have hv_exists := exists_apartment_at_point hP hT hL0
  let v : ZMod 8 → V := Classical.choose hv_exists
  have hv_spec := Classical.choose_spec hv_exists
  have hv : IsPolygonApartment Γ 4 v := hv_spec.1
  have hv0 : v 0 = p := hv_spec.2
  have h1v : ∀ x, Γ.dist (v 0) x = 4 → (spanSet Γ (v 0) x).ncard = 2 := by
    intro x hx
    rw [hv0] at hx
    rw [hv0]
    exact h1 x hx
  let E : Subgroup H := elationGroup H Γ v
  have hE_eq : E = elationGroup H Γ v := rfl
  haveI hEfin : Fintype ↥E :=
    Fintype.ofInjective (fun e : ↥E => fun y : V => (e : H) • y) (by
      intro e f hef
      apply Subtype.ext
      exact eq_of_smul_eq_smul (m₁ := (e : H)) (m₂ := (f : H)) (fun y => congrFun hef y))
  have hE0 : Γ.Adj (v 0) (v 1) := by
    have h := hv.2 0
    have e : ((0 : ZMod 8) + 1) = 1 := by decide
    simpa [e] using h
  have hv4 : Γ.dist (v 0) (v 4) = 4 := by
    have h := hP.isGeodesic_of_noBack (by norm_num : 4 ≤ 4) (aptPath_noBack (by norm_num) hv 0)
    have a0 : apt (n := 4) v 0 = v 0 := by
      show v ((0 : ℤ) : ZMod 8) = v 0
      exact congrArg v (by decide)
    have a4 : apt (n := 4) v 4 = v 4 := by
      show v ((4 : ℤ) : ZMod 8) = v 4
      exact congrArg v (by decide)
    simpa [GPath.IsGeodesic, a0, a4] using h
  have hEcard : Nat.card ↥E = s * t * s := by
    have hcard := card_elationGroup (H := H) hP hT hM v hv
    have hc1 : c (v 1) = 1 := by
      have h := hv.2 0
      have e : ((0 : ZMod 8) + 1) = 1 := by decide
      have hadj : Γ.Adj (v 0) (v 1) := by simpa [e] using h
      rw [hv0] at hadj
      exact color_eq_one_of_adj_of_color_eq_zero hp hadj
    have hc2 : c (v 2) = 0 := by
      have h := hv.2 1
      have e : ((1 : ZMod 8) + 1) = 2 := by decide
      have hadj : Γ.Adj (v 1) (v 2) := by simpa [e] using h
      exact color_eq_zero_of_adj_of_color_eq_one hc1 hadj
    have hc3 : c (v 3) = 1 := by
      have h := hv.2 2
      have e : ((2 : ZMod 8) + 1) = 3 := by decide
      have hadj : Γ.Adj (v 2) (v 3) := by simpa [e] using h
      exact color_eq_one_of_adj_of_color_eq_zero hc2 hadj
    have hd1 : Γ.degree (v 1) = s + 1 := by rw [hdeg (v 1), if_neg (by rw [hc1]; decide)]
    have hd2 : Γ.degree (v 2) = t + 1 := by rw [hdeg (v 2), if_pos hc2]
    have hd3 : Γ.degree (v 3) = s + 1 := by rw [hdeg (v 3), if_neg (by rw [hc3]; decide)]
    rw [hcard, hd1, hd2, hd3]
    simp only [Nat.add_sub_cancel]
  have hfree : ∀ (g : ↥E) {x : V}, Γ.dist p x = 4 → (g : H) • x = x → g = 1 := by
    intro g x hx hgx
    obtain ⟨g0, hg0, huniq⟩ := existsUnique_elationGroup hP hT hM v hv (w := v 4)
      (by simpa [hv0] using hv4)
    obtain ⟨hx0, hhx0E, hhx0⟩ := exists_mem_elationGroup_smul_eq hP hT hM v hv (by
      rw [hv0]; exact hx)
    let h0 : ↥E := ⟨hx0, hhx0E⟩
    have hconj : ((h0⁻¹ * g * h0 : ↥E) : H) • v 4 = v 4 := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [mul_smul, mul_smul, hhx0]
      have : (h0 : H) = hx0 := rfl
      rw [this]
      have hxinv : (hx0⁻¹ : H) • x = v 4 := by
        have h := congrArg (fun z => (hx0⁻¹ : H) • z) hhx0
        simpa using h.symm
      rw [hgx, hxinv]
    have hone : h0⁻¹ * g * h0 = 1 :=
      (huniq (h0⁻¹ * g * h0) hconj).trans (huniq 1 (by simp)).symm
    calc
      g = h0 * (h0⁻¹ * g * h0) * h0⁻¹ := by group
      _ = 1 := by rw [hone]; simp
  have htrans : ∀ x x' : V, Γ.dist p x = 4 → Γ.dist p x' = 4 →
      ∃ g : ↥E, (g : H) • x = x' := by
    intro x x' hx hx'
    obtain ⟨gx, hgxE, hgx⟩ := exists_mem_elationGroup_smul_eq hP hT hM v hv (by rw [hv0]; exact hx)
    obtain ⟨gx', hgx'E, hgx'⟩ :=
      exists_mem_elationGroup_smul_eq hP hT hM v hv (by rw [hv0]; exact hx')
    refine ⟨⟨gx' * gx⁻¹, E.mul_mem hgx'E (E.inv_mem hgxE)⟩, ?_⟩
    show (gx' * gx⁻¹ : H) • x = x'
    rw [mul_smul]
    have hxinv : (gx⁻¹ : H) • x = v 4 := by
      have h := congrArg (fun z => (gx⁻¹ : H) • z) hgx
      simpa using h.symm
    rw [hxinv, hgx']
  let S0 : Subgroup H := E ⊓ MulAction.stabilizer H M0
  let S1 : Subgroup H := E ⊓ MulAction.stabilizer H M1
  let S0s : Subgroup H := E ⊓ MulAction.stabilizer H z0
  let S1s : Subgroup H := E ⊓ MulAction.stabilizer H z1
  have hS0_eq : S0 = E ⊓ MulAction.stabilizer H M0 := rfl
  have hS1_eq : S1 = E ⊓ MulAction.stabilizer H M1 := rfl
  have hS0s_eq : S0s = E ⊓ MulAction.stabilizer H z0 := rfl
  have hS1s_eq : S1s = E ⊓ MulAction.stabilizer H z1 := rfl
  have hw2_exists : ∃ w : V, Γ.Adj L2 w ∧ w ≠ p := by
    obtain ⟨w, hw, hw1, -⟩ := exists_adj_ne_two hT L2 p p
    exact ⟨w, hw, hw1⟩
  let w2 : V := Classical.choose hw2_exists
  have hw2_spec := Classical.choose_spec hw2_exists
  have hw2L2 : Γ.Adj L2 w2 := hw2_spec.1
  have hw2p : w2 ≠ p := hw2_spec.2
  have hM2_exists : ∃ N : V, Γ.Adj w2 N ∧ N ≠ L2 := by
    obtain ⟨N, hN, hN1, -⟩ := exists_adj_ne_two hT w2 L2 L2
    exact ⟨N, hN, hN1⟩
  let M2 : V := Classical.choose hM2_exists
  have hM2_spec := Classical.choose_spec hM2_exists
  have hw2M2 : Γ.Adj w2 M2 := hM2_spec.1
  have hM2L2 : M2 ≠ L2 := hM2_spec.2
  have hexists_smul_L0 : ∀ u u' : V, Γ.Adj L0 u → Γ.Adj L0 u' → u ≠ p → u' ≠ p →
      ∃ g ∈ E, g • u = u' := by
    intro u u' hu hu' hup hu'p
    let rA : GPath Γ 4 := GPath.cons L0
      (GPath.cons p (GPath.cons L2 (GPath.ofAdj hw2M2) hw2L2) hL2) hL0.symm
    have hrA0 : rA 0 = L0 := rfl
    have hrA1 : rA 1 = p := rfl
    have hrA2 : rA 2 = L2 := rfl
    have hrA3 : rA 3 = w2 := rfl
    have hrA4 : rA 4 = M2 := rfl
    have hrAnb : rA.NoBack := by
      intro i hi
      have hi2 : i ≤ 2 := by omega
      interval_cases i
      · rw [hrA0, hrA2]; exact hL20'
      · rw [hrA1, hrA3]; exact hw2p.symm
      · rw [hrA2, hrA4]; exact hM2L2.symm
    have hrev4 : rA.rev 4 = L0 := by rw [GPath.rev_apply _ le_rfl]; omega
    have hrev3 : rA.rev 3 = p := by
      rw [GPath.rev_apply _ (by omega)]; rw [show 4 - 3 = 1 by omega, hrA1]
    have hrev1 : rA.rev 1 = w2 := by
      rw [GPath.rev_apply _ (by omega)]; rw [show 4 - 1 = 3 by omega, hrA3]
    have hrev2 : rA.rev 2 = L2 := by
      rw [GPath.rev_apply _ (by omega)]; rw [show 4 - 2 = 2 by omega, hrA2]
    have hrevnb : rA.rev.NoBack := hrAnb.rev
    obtain ⟨g, hgfix, hgu⟩ := hM (rA.rev) hrevnb u u'
      (by rw [hrev4]; exact hu) (by rw [hrev4]; exact hu')
      (by rw [hrev3]; exact hup) (by rw [hrev3]; exact hu'p)
    have hgU : g ∈ rootGroup H Γ w2 L2 p := by
      rw [mem_rootGroup]
      refine ⟨?_, ?_, ?_⟩
      · rw [mem_fixingSubgroup_iff]; intro x hx
        exact hgfix 1 (by omega) (by omega) x (by rw [hrev1]; exact hx)
      · rw [mem_fixingSubgroup_iff]; intro x hx
        exact hgfix 2 (by omega) (by omega) x (by rw [hrev2]; exact hx)
      · rw [mem_fixingSubgroup_iff]; intro x hx
        exact hgfix 3 (by omega) (by omega) x (by rw [hrev3]; exact hx)
    have hle : rootGroup H Γ w2 L2 p ≤ E := by
      have h := rootGroup_le_elationGroup hP hT c hdeg hst hM v hv
        (by rw [hv0]; exact hp) h1v rA.rev hrevnb (by rw [hv0, hrev3]; simp)
      rwa [hrev1, hrev2, hrev3] at h
    exact ⟨g, hle hgU, hgu⟩
  have horbit0 : (MulAction.orbit ↥E z0 : Set V) = Γ.neighborSet L0 \ {p} := by
    ext u
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, hg⟩
      have hgE : (g : H) ∈ E := g.2
      have hfixp : (g : H) • p = p := by
        have h := elationGroup_le_whorlGroup v hv hgE
        rw [hv0] at h
        exact whorlGroup_fix_self hP hT h
      have hfixL : (g : H) • L0 = L0 := by
        have h := elationGroup_le_whorlGroup v hv hgE
        rw [hv0] at h
        rw [mem_whorlGroup, mem_fixingSubgroup_iff] at h
        exact h L0 hL0
      have hdist : Γ.dist p ((g : H) • z0) = Γ.dist p z0 := by
        calc Γ.dist p ((g : H) • z0) = Γ.dist ((g : H) • p) ((g : H) • z0) := by rw [hfixp]
          _ = Γ.dist p z0 := GPath.dist_smul hP.connected (g : H) p z0
      have hadj : Γ.Adj L0 ((g : H) • z0) := by
        have h := (GraphAction.adj_smul (g : H) z0 L0).mpr hz0L0.symm
        rw [hfixL] at h
        exact h.symm
      have hne : (g : H) • z0 ≠ p := by
        intro hpz
        have : Γ.dist p ((g : H) • z0) = 0 := by rw [hpz, SimpleGraph.dist_self]
        rw [hdist, hzp0] at this
        omega
      rw [← hg]
      exact ⟨hadj, hne⟩
    · rintro ⟨huL, hup⟩
      obtain ⟨g, hgE, hgu⟩ := hexists_smul_L0 u z0 huL hz0L0 hup hz0p
      refine ⟨⟨g⁻¹, E.inv_mem hgE⟩, ?_⟩
      have hgu' : (g⁻¹ : H) • z0 = u := by
        have h := congrArg (fun z => (g⁻¹ : H) • z) hgu
        simpa using h.symm
      exact hgu'
  have hL0p_card : (Γ.neighborSet L0 \ {p}).ncard = s :=
    ncard_points_of_line_erase hdeg hcL0 hL0.symm
  have horbit0card_fintype : Fintype.card ↥(MulAction.orbit ↥E z0) = s := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, horbit0, hL0p_card]
  have horbit0card : Nat.card ↥(MulAction.orbit ↥E z0) = s := by
    rw [Nat.card_eq_fintype_card]
    exact horbit0card_fintype
  have hS0s_card : Nat.card ↥S0s = s * t := by
    have hstab : MulAction.stabilizer ↥E z0 = S0s.subgroupOf E := by
      ext g
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
    have hstab_card : Nat.card ↥(MulAction.stabilizer ↥E z0) = Nat.card ↥S0s := by
      rw [hstab, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    have horb_nat : Nat.card ↥(MulAction.orbit ↥E z0) = s := horbit0card
    haveI : Fintype ↥(MulAction.stabilizer ↥E z0) := Fintype.ofFinite _
    have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥E) (b := z0)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card] at h
    rw [horb_nat, hstab_card, hEcard] at h
    have hs0 : 0 < s := by omega
    refine Nat.mul_left_cancel (n := s) (m := Nat.card ↥S0s) (k := s * t) hs0 ?_
    calc s * Nat.card ↥S0s = s * t * s := h
      _ = s * (s * t) := by ring
  let Uloc : Subgroup H := rootGroup H Γ L0 p L2
  have hUloc_eq : Uloc = rootGroup H Γ L0 p L2 := rfl
  have hUloc_le : Uloc ≤ E := by
    let s3 : GPath Γ 4 := GPath.cons z0
      (GPath.cons L0 (GPath.cons p (GPath.ofAdj hw2L2) hL2) hL0.symm) hz0L0.symm
    have hs30 : s3 0 = z0 := rfl
    have hs31 : s3 1 = L0 := rfl
    have hs32 : s3 2 = p := rfl
    have hs33 : s3 3 = L2 := rfl
    have hs34 : s3 4 = w2 := rfl
    have hs3nb : s3.NoBack := by
      intro i hi
      have hi2 : i ≤ 2 := by omega
      interval_cases i
      · rw [hs30, hs32]; exact hz0p
      · rw [hs31, hs33]; exact hL20'
      · rw [hs32, hs34]; exact hw2p.symm
    have h := rootGroup_le_elationGroup hP hT c hdeg hst hM v hv
      (by rw [hv0]; exact hp) h1v s3 hs3nb (by rw [hv0, hs32]; simp)
    rwa [hs31, hs32, hs33] at h
  have hUloc_card : Nat.card ↥Uloc = t := by
    let s3 : GPath Γ 4 := GPath.cons z0
      (GPath.cons L0 (GPath.cons p (GPath.ofAdj hw2L2) hL2) hL0.symm) hz0L0.symm
    have hs30 : s3 0 = z0 := rfl
    have hs31 : s3 1 = L0 := rfl
    have hs32 : s3 2 = p := rfl
    have hs33 : s3 3 = L2 := rfl
    have hs34 : s3 4 = w2 := rfl
    have hs3nb : s3.NoBack := by
      intro i hi
      have hi2 : i ≤ 2 := by omega
      interval_cases i
      · rw [hs30, hs32]; exact hz0p
      · rw [hs31, hs33]; exact hL20'
      · rw [hs32, hs34]; exact hw2p.symm
    have h := card_rootGroup hP hT hM s3 hs3nb
    rw [hs31, hs32, hs33] at h
    have hd : Γ.degree (s3 4) = t + 1 := by
      rw [hs34, hdeg w2]
      exact if_pos (color_eq_zero_of_adj_of_color_eq_one hcL2 hw2L2)
    have hd' : Γ.degree (s3 4) - 1 = t := by rw [hd]; omega
    rw [hd'] at h
    exact h
  have hUloc_trans : ∀ K K' : V, Γ.Adj z0 K → K ≠ L0 → Γ.Adj z0 K' → K' ≠ L0 →
      ∃ g ∈ Uloc, g • K = K' := by
    intro K K' hK hKL hK' hK'L
    let s3 : GPath Γ 4 := GPath.cons z0
      (GPath.cons L0 (GPath.cons p (GPath.ofAdj hw2L2) hL2) hL0.symm) hz0L0.symm
    have hs30 : s3 0 = z0 := rfl
    have hs31 : s3 1 = L0 := rfl
    have hs32 : s3 2 = p := rfl
    have hs33 : s3 3 = L2 := rfl
    have hs34 : s3 4 = w2 := rfl
    have hs3nb : s3.NoBack := by
      intro i hi
      have hi2 : i ≤ 2 := by omega
      interval_cases i
      · rw [hs30, hs32]; exact hz0p
      · rw [hs31, hs33]; exact hL20'
      · rw [hs32, hs34]; exact hw2p.symm
    have hrev4 : s3.rev 4 = z0 := by rw [GPath.rev_apply _ le_rfl]; omega
    have hrev3 : s3.rev 3 = L0 := by
      rw [GPath.rev_apply _ (by omega)]; rw [show 4 - 3 = 1 by omega, hs31]
    have hrev1 : s3.rev 1 = L2 := by
      rw [GPath.rev_apply _ (by omega)]; rw [show 4 - 1 = 3 by omega, hs33]
    have hrev2 : s3.rev 2 = p := by
      rw [GPath.rev_apply _ (by omega)]; rw [show 4 - 2 = 2 by omega, hs32]
    have hrevnb : s3.rev.NoBack := hs3nb.rev
    obtain ⟨g, hgfix, hgK⟩ := hM (s3.rev) hrevnb K K'
      (by rw [hrev4]; exact hK) (by rw [hrev4]; exact hK')
      (by rw [hrev3]; exact hKL) (by rw [hrev3]; exact hK'L)
    have hgU : g ∈ Uloc := by
      rw [mem_rootGroup]
      refine ⟨?_, ?_, ?_⟩
      · rw [mem_fixingSubgroup_iff]; intro x hx
        exact hgfix 3 (by omega) (by omega) x (by rw [hrev3]; exact hx)
      · rw [mem_fixingSubgroup_iff]; intro x hx
        exact hgfix 2 (by omega) (by omega) x (by rw [hrev2]; exact hx)
      · rw [mem_fixingSubgroup_iff]; intro x hx
        exact hgfix 1 (by omega) (by omega) x (by rw [hrev1]; exact hx)
    exact ⟨g, hgU, hgK⟩
  let U0 : Subgroup H := rootGroup H Γ p L0 z0
  have hU0_eq : U0 = rootGroup H Γ p L0 z0 := rfl
  have hU0leE : U0 ≤ E := by
    let qU : GPath Γ 4 := GPath.cons L1
      (GPath.cons p (GPath.cons L0 (GPath.ofAdj hz0M0) hz0L0) hL0) hL1.symm
    have hq1 : qU 1 = p := rfl
    have hq2 : qU 2 = L0 := rfl
    have hq3 : qU 3 = z0 := rfl
    have hq4 : qU 4 = M0 := rfl
    have hq : qU.NoBack := by
      intro i hi
      have hi2 : i ≤ 2 := by omega
      interval_cases i
      · rw [show qU 0 = L1 from rfl, hq2]; exact hL10'.symm
      · rw [hq1, hq3]; exact hz0p.symm
      · rw [hq2, hq4]; exact hM0ne.symm
    have h := rootGroup_le_elationGroup hP hT c hdeg hst hM v hv (by rw [hv0]; exact hp) h1v
      qU hq (by rw [hv0, hq1]; simp)
    rwa [hq1, hq2, hq3] at h
  have hU0card : Nat.card ↥U0 = s := by
    let qU : GPath Γ 4 := GPath.cons L1
      (GPath.cons p (GPath.cons L0 (GPath.ofAdj hz0M0) hz0L0) hL0) hL1.symm
    have hq1 : qU 1 = p := rfl
    have hq2 : qU 2 = L0 := rfl
    have hq3 : qU 3 = z0 := rfl
    have hq4 : qU 4 = M0 := rfl
    have hq : qU.NoBack := by
      intro i hi
      have hi2 : i ≤ 2 := by omega
      interval_cases i
      · rw [show qU 0 = L1 from rfl, hq2]; exact hL10'.symm
      · rw [hq1, hq3]; exact hz0p.symm
      · rw [hq2, hq4]; exact hM0ne.symm
    have h := card_rootGroup hP hT hM qU hq
    rw [hq1, hq2, hq3] at h
    have hd : Γ.degree (qU 4) = s + 1 := by
      rw [hq4, hdeg M0, if_neg (by rw [hcM0]; decide)]
    have hd' : Γ.degree (qU 4) - 1 = s := by rw [hd]; omega
    rw [hd'] at h
    exact h
  have hU0leS0 : U0 ≤ S0 := by
    intro u hu
    refine Subgroup.mem_inf.mpr ⟨hU0leE hu, ?_⟩
    refine MulAction.mem_stabilizer_iff.mpr ?_
    exact (mem_fixingSubgroup_iff H).mp ((mem_rootGroup H).mp hu).2.2 M0 hz0M0
  have hmaps : ∀ g : ↥S0, (g : H) • y ∈ Γ.neighborSet M0 \ {z0} := by
    intro g
    have hgE : (g : H) ∈ E := (Subgroup.mem_inf.mp g.2).1
    have hgM : (g : H) • M0 = M0 := (MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp g.2).2)
    have hfixp : (g : H) • p = p := by
      have h := elationGroup_le_whorlGroup v hv hgE
      rw [hv0] at h
      exact whorlGroup_fix_self hP hT h
    have hadj : Γ.Adj M0 ((g : H) • y) := by
      have h := (GraphAction.adj_smul (g : H) y M0).mpr hyM0
      rw [hgM] at h
      exact h.symm
    refine ⟨by simpa using hadj, ?_⟩
    intro hzy
    have hdist : Γ.dist p ((g : H) • y) = 4 := by
      have h := GPath.dist_smul hP.connected (g : H) p y
      rw [hfixp] at h
      rw [h]
      exact hy4
    rw [hzy, hzp0] at hdist
    omega
  haveI : Fintype ↥S0 :=
    Fintype.ofInjective (fun g : ↥S0 => (⟨(g : H), (Subgroup.mem_inf.mp g.2).1⟩ : ↥E))
      (by
        intro a b hab
        apply Subtype.ext
        exact congrArg (fun z : ↥E => (z : H)) hab)
  have hS0le : Nat.card ↥S0 ≤ s := by
    let f : ↥S0 → ↥(Γ.neighborSet M0 \ {z0}) := fun g => ⟨(g : H) • y, hmaps g⟩
    have hinj : Function.Injective f := by
      intro g g' hgg
      have heq : (g : H) • y = (g' : H) • y := congrArg Subtype.val hgg
      have hgE : (g : H) ∈ E := (Subgroup.mem_inf.mp g.2).1
      have hgE' : (g' : H) ∈ E := (Subgroup.mem_inf.mp g'.2).1
      let e : ↥E := ⟨(g' : H)⁻¹ * (g : H), E.mul_mem (E.inv_mem hgE') hgE⟩
      have hefix : (e : H) • y = y := by
        show ((g' : H)⁻¹ * (g : H)) • y = y
        rw [mul_smul, heq]
        simp
      have he1 : e = 1 := hfree e hy4 hefix
      have hHH : (g' : H)⁻¹ * (g : H) = 1 := by
        have := congrArg Subtype.val he1
        simpa [e] using this
      have hEq : (g : H) = (g' : H) := by
        calc (g : H) = (g' : H) * ((g' : H)⁻¹ * (g : H)) := by group
          _ = (g' : H) := by rw [hHH, mul_one]
      exact Subtype.ext hEq
    have hcard := Nat.card_le_card_of_injective f hinj
    rw [Nat.card_coe_set_eq, ncard_points_of_line_erase hdeg hcM0 hz0M0.symm] at hcard
    exact hcard
  have hS0_eq_U0 : S0 = U0 := by
    have h := Subgroup.eq_of_le_of_card_ge hU0leS0 (by rw [hU0card]; exact hS0le)
    exact h.symm
  have hS0s_fix : ∀ θ : H, θ ∈ S0s → ∀ u : V, Γ.Adj L0 u → θ • u = u := by
    intro θ hθ u hu
    have hθE : θ ∈ E := (Subgroup.mem_inf.mp hθ).1
    have hθz : θ • z0 = z0 := (MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hθ).2)
    by_cases hfixM : θ • M0 = M0
    · have hθS0 : θ ∈ S0 := Subgroup.mem_inf.mpr ⟨hθE, MulAction.mem_stabilizer_iff.mpr hfixM⟩
      rw [hS0_eq_U0] at hθS0
      exact (mem_fixingSubgroup_iff H).mp ((mem_rootGroup H).mp hθS0).2.1 u hu
    · have hKL0 : θ • M0 ≠ L0 := by
        intro h
        have hθL : θ • L0 = L0 := by
          have h' := elationGroup_le_whorlGroup v hv hθE
          rw [hv0] at h'
          rw [mem_whorlGroup, mem_fixingSubgroup_iff] at h'
          exact h' L0 hL0
        have hML : M0 = L0 := by
          calc M0 = θ⁻¹ • (θ • M0) := by simp
            _ = θ⁻¹ • L0 := by rw [h]
            _ = θ⁻¹ • (θ • L0) := by rw [hθL]
            _ = L0 := by simp
        exact hM0ne hML
      have hKadj : Γ.Adj z0 (θ • M0) := by
        have h := (GraphAction.adj_smul θ M0 z0).mpr hz0M0.symm
        rw [hθz] at h
        exact h.symm
      obtain ⟨φ, hφU, hφK⟩ := hUloc_trans (θ • M0) M0 hKadj hKL0 hz0M0 hM0ne
      have hφfix : ∀ v : V, Γ.Adj L0 v → φ • v = v := by
        intro v hv
        exact (mem_fixingSubgroup_iff H).mp ((mem_rootGroup H).mp hφU).1 v hv
      have hφθS0 : φ * θ ∈ S0 := by
        refine Subgroup.mem_inf.mpr ⟨E.mul_mem (hUloc_le hφU) hθE, ?_⟩
        refine MulAction.mem_stabilizer_iff.mpr ?_
        show (φ * θ) • M0 = M0
        rw [mul_smul, hφK]
      rw [hS0_eq_U0] at hφθS0
      have hφθfix : (φ * θ) • u = u :=
        (mem_fixingSubgroup_iff H).mp ((mem_rootGroup H).mp hφθS0).2.1 u hu
      have : θ • u = φ⁻¹ • u := by
        have h := hφθfix
        rw [mul_smul] at h
        exact eq_inv_smul_iff.mpr h
      rw [this]
      have hφu : φ • u = u := hφfix u hu
      calc φ⁻¹ • u = φ⁻¹ • (φ • u) := by rw [hφu]
        _ = u := by simp
  exact ⟨L0, hL0, L1, hL1, hL10, L2, hL2, hL20, hL21, hcL0, hcL1, hcL2, hL10', hL20', hL21',
    ht2, hs2, hOpp, hpos, y, hyF, hy4, hcy, hyL0, hyL1, z0, z1, hz0L0, hz1L1, hyz0, hyz1, hcz0,
    hcz1, hz0p, hz1p, M0, M1, hyM0, hz0M0, hyM1, hz1M1, hcM0, hcM1, hM0ne, hM1ne, hzp0, hzp1,
    hpM0, hpM1, hdistpM0, hdistpM1, v, hv, hv0, h1v, E, hE0, hv4, hEcard, hfree, htrans, S0,
    S1, S0s, S1s, w2, hw2L2, hw2p, M2, hw2M2, hM2L2, hexists_smul_L0, horbit0, hL0p_card,
    horbit0card, hS0s_card, Uloc, hUloc_le, hUloc_card, hUloc_trans, U0, hU0leE, hU0card,
    hU0leS0, hmaps, hS0le, hS0_eq_U0, hS0s_fix, hE_eq, hS0_eq, hS1_eq, hS0s_eq, hS1s_eq,
    hUloc_eq, hU0_eq ⟩

end CFSG.Geometry.GeneralizedQuadrangles
