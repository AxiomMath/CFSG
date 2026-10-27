module

public import CFSG.Geometry.GeneralizedQuadrangles.Moufang.NoSpansTwoCore

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons CFSG.Quasithin CFSG.Quasithin.Stroth
open scoped Pointwise

variable {V : Type} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
  {H : Type} [Group H] [MulAction H V] [FaithfulSMul H V] [GraphAction H Γ]

structure NoSpansTwoMidData
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
  hexists_smul_L1 : ∀ u u' : V, Γ.Adj L1 u → Γ.Adj L1 u' → u ≠ p → u' ≠ p → ∃ g ∈ E, g • u = u'
  horbit1 : (MulAction.orbit ↥E z1 : Set V) = Γ.neighborSet L1 \ {p}
  hL1p_card : (Γ.neighborSet L1 \ {p}).ncard = s
  horbit1card : Nat.card ↥(MulAction.orbit ↥E z1) = s
  hS1s_card : Nat.card ↥S1s = s * t
  Vloc : Subgroup H
  hVloc_le : Vloc ≤ E
  hVloc_card : Nat.card ↥Vloc = t
  hVloc_trans : ∀ K K' : V, Γ.Adj z1 K → K ≠ L1 → Γ.Adj z1 K' → K' ≠ L1 → ∃ g ∈ Vloc, g • K = K'
  U1 : Subgroup H
  hU1leE : U1 ≤ E
  hU1card : Nat.card ↥U1 = s
  hU1leS1 : U1 ≤ S1
  hmaps1 : ∀ g : ↥S1, (g : H) • y ∈ Γ.neighborSet M1 \ {z1}
  hS1le : Nat.card ↥S1 ≤ s
  hS1_eq_U1 : S1 = U1
  hS1s_fix : ∀ θ : H, θ ∈ S1s → ∀ u : V, Γ.Adj L1 u → θ • u = u
  hE_fixL0 : ∀ e : H, e ∈ E → e • L0 = L0
  hE_fixL1 : ∀ e : H, e ∈ E → e • L1 = L1
  hpoint_fix : ∀ e : H, e ∈ E → e • p = p
  hS0s_normal : ∀ e : H, e ∈ E → ∀ y : H, y ∈ S0s ↔ e * y * e⁻¹ ∈ S0s
  hS1s_normal : ∀ e : H, e ∈ E → ∀ y : H, y ∈ S1s ↔ e * y * e⁻¹ ∈ S1s
  hVloc_eq : Vloc = rootGroup H Γ L1 p L2
  hU1_eq : U1 = rootGroup H Γ p L1 z1

public noncomputable def noSpansTwoMid
    (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ) (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) (hst : s ≤ t)
    (hM : MoufangCondition H Γ 4) {p : V} (hp : c p = 0)
    (h1 : ∀ x, Γ.dist p x = 4 → (spanSet Γ p x).ncard = 2)
    (h2 : ∀ L M, Γ.Adj p L → Γ.dist L M = 4 → (spanSet Γ L M).ncard = 2)
    (D : NoSpansTwoBaseData hP hT c hdeg hst hM hp h1 h2) :
    NoSpansTwoMidData hP hT c hdeg hst hM hp h1 h2 := by
  classical
  let D0 := D
  obtain ⟨L0, hL0, L1, hL1, hL10, L2, hL2, hL20, hL21, hcL0, hcL1, hcL2, hL10', hL20', hL21',
    ht2, hs2, hOpp, hpos, y, hyF, hy4, hcy, hyL0, hyL1, z0, z1, hz0L0, hz1L1, hyz0, hyz1, hcz0,
    hcz1, hz0p, hz1p, M0, M1, hyM0, hz0M0, hyM1, hz1M1, hcM0, hcM1, hM0ne, hM1ne, hzp0, hzp1,
    hpM0, hpM1, hdistpM0, hdistpM1, v, hv, hv0, h1v, E, hE0, hv4, hEcard, hfree, htrans, S0,
    S1, S0s, S1s, w2, hw2L2, hw2p, M2, hw2M2, hM2L2, hexists_smul_L0, horbit0, hL0p_card,
    horbit0card, hS0s_card, Uloc, hUloc_le, hUloc_card, hUloc_trans, U0, hU0leE, hU0card,
    hU0leS0, hmaps, hS0le, hS0_eq_U0, hS0s_fix, hE_eq, hS0_eq, hS1_eq, hS0s_eq, hS1s_eq,
    hUloc_eq, hU0_eq⟩ := D0
  subst hE_eq
  let E : Subgroup H := elationGroup H Γ v
  subst hS0_eq
  subst hS1_eq
  subst hS0s_eq
  subst hS1s_eq
  let S0 : Subgroup H := E ⊓ MulAction.stabilizer H M0
  let S1 : Subgroup H := E ⊓ MulAction.stabilizer H M1
  let S0s : Subgroup H := E ⊓ MulAction.stabilizer H z0
  let S1s : Subgroup H := E ⊓ MulAction.stabilizer H z1
  subst hUloc_eq
  let Uloc : Subgroup H := rootGroup H Γ L0 p L2
  subst hU0_eq
  let U0 : Subgroup H := rootGroup H Γ p L0 z0

  haveI hEfin : Fintype ↥E :=
    Fintype.ofInjective (fun e : ↥E => fun x : V => (e : H) • x)
      (by
        intro e f hef
        apply Subtype.ext
        exact eq_of_smul_eq_smul (m₁ := (e : H)) (m₂ := (f : H))
          (fun x => congrFun hef x))
  have hexists_smul_L1 : ∀ u u' : V, Γ.Adj L1 u → Γ.Adj L1 u' → u ≠ p → u' ≠ p →
      ∃ g ∈ E, g • u = u' := by
    intro u u' hu hu' hup hu'p
    let rB : GPath Γ 4 := GPath.cons L1
      (GPath.cons p (GPath.cons L2 (GPath.ofAdj hw2M2) hw2L2) hL2) hL1.symm
    have hrB0 : rB 0 = L1 := rfl
    have hrB1 : rB 1 = p := rfl
    have hrB2 : rB 2 = L2 := rfl
    have hrB3 : rB 3 = w2 := rfl
    have hrB4 : rB 4 = M2 := rfl
    have hrBnb : rB.NoBack := by
      intro i hi
      have hi2 : i ≤ 2 := by omega
      interval_cases i
      · rw [hrB0, hrB2]; exact hL21'
      · rw [hrB1, hrB3]; exact hw2p.symm
      · rw [hrB2, hrB4]; exact hM2L2.symm
    have hrev4 : rB.rev 4 = L1 := by rw [GPath.rev_apply _ le_rfl]; omega
    have hrev3 : rB.rev 3 = p := by
      rw [GPath.rev_apply _ (by omega)]; rw [show 4 - 3 = 1 by omega, hrB1]
    have hrev1 : rB.rev 1 = w2 := by
      rw [GPath.rev_apply _ (by omega)]; rw [show 4 - 1 = 3 by omega, hrB3]
    have hrev2 : rB.rev 2 = L2 := by
      rw [GPath.rev_apply _ (by omega)]; rw [show 4 - 2 = 2 by omega, hrB2]
    have hrevnb : rB.rev.NoBack := hrBnb.rev
    obtain ⟨g, hgfix, hgu⟩ := hM (rB.rev) hrevnb u u'
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
        (by rw [hv0]; exact hp) h1v rB.rev hrevnb (by rw [hv0, hrev3]; simp)
      rwa [hrev1, hrev2, hrev3] at h
    exact ⟨g, hle hgU, hgu⟩
  have horbit1 : (MulAction.orbit ↥E z1 : Set V) = Γ.neighborSet L1 \ {p} := by
    ext u
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, hg⟩
      have hgE : (g : H) ∈ E := g.2
      have hfixp : (g : H) • p = p := by
        have h := elationGroup_le_whorlGroup v hv hgE
        rw [hv0] at h
        exact whorlGroup_fix_self hP hT h
      have hfixL : (g : H) • L1 = L1 := by
        have h := elationGroup_le_whorlGroup v hv hgE
        rw [hv0] at h
        rw [mem_whorlGroup, mem_fixingSubgroup_iff] at h
        exact h L1 hL1
      have hdist : Γ.dist p ((g : H) • z1) = Γ.dist p z1 := by
        calc Γ.dist p ((g : H) • z1) = Γ.dist ((g : H) • p) ((g : H) • z1) := by rw [hfixp]
          _ = Γ.dist p z1 := GPath.dist_smul hP.connected (g : H) p z1
      have hadj : Γ.Adj L1 ((g : H) • z1) := by
        have h := (GraphAction.adj_smul (g : H) z1 L1).mpr hz1L1.symm
        rw [hfixL] at h
        exact h.symm
      have hne : (g : H) • z1 ≠ p := by
        intro hpz
        have : Γ.dist p ((g : H) • z1) = 0 := by rw [hpz, SimpleGraph.dist_self]
        rw [hdist, hzp1] at this
        omega
      rw [← hg]
      exact ⟨hadj, hne⟩
    · rintro ⟨huL, hup⟩
      obtain ⟨g, hgE, hgu⟩ := hexists_smul_L1 u z1 huL hz1L1 hup hz1p
      refine ⟨⟨g⁻¹, E.inv_mem hgE⟩, ?_⟩
      have hgu' : (g⁻¹ : H) • z1 = u := by
        have h := congrArg (fun z => (g⁻¹ : H) • z) hgu
        simpa using h.symm
      exact hgu'
  have hL1p_card : (Γ.neighborSet L1 \ {p}).ncard = s :=
    ncard_points_of_line_erase hdeg hcL1 hL1.symm
  have horbit1card_fintype : Fintype.card ↥(MulAction.orbit ↥E z1) = s := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, horbit1, hL1p_card]
  have horbit1card : Nat.card ↥(MulAction.orbit ↥E z1) = s := by
    rw [Nat.card_eq_fintype_card]
    exact horbit1card_fintype
  have hS1s_card : Nat.card ↥S1s = s * t := by
    have hstab : MulAction.stabilizer ↥E z1 = S1s.subgroupOf E := by
      ext g
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
    have hstab_card : Nat.card ↥(MulAction.stabilizer ↥E z1) = Nat.card ↥S1s := by
      rw [hstab, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    have horb_nat : Nat.card ↥(MulAction.orbit ↥E z1) = s := horbit1card
    haveI : Fintype ↥(MulAction.stabilizer ↥E z1) := Fintype.ofFinite _
    have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥E) (b := z1)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card] at h
    rw [horb_nat, hstab_card, hEcard] at h
    have hs0 : 0 < s := by omega
    refine Nat.mul_left_cancel (n := s) (m := Nat.card ↥S1s) (k := s * t) hs0 ?_
    calc s * Nat.card ↥S1s = s * t * s := h
      _ = s * (s * t) := by ring

  let Vloc : Subgroup H := rootGroup H Γ L1 p L2
  have hVloc_eq : Vloc = rootGroup H Γ L1 p L2 := rfl
  have hVloc_le : Vloc ≤ E := by
    let sB : GPath Γ 4 := GPath.cons z1
      (GPath.cons L1 (GPath.cons p (GPath.ofAdj hw2L2) hL2) hL1.symm) hz1L1.symm
    have hsB0 : sB 0 = z1 := rfl
    have hsB1 : sB 1 = L1 := rfl
    have hsB2 : sB 2 = p := rfl
    have hsB3 : sB 3 = L2 := rfl
    have hsB4 : sB 4 = w2 := rfl
    have hsBnb : sB.NoBack := by
      intro i hi
      have hi2 : i ≤ 2 := by omega
      interval_cases i
      · rw [hsB0, hsB2]; exact hz1p
      · rw [hsB1, hsB3]; exact hL21'
      · rw [hsB2, hsB4]; exact hw2p.symm
    have h := rootGroup_le_elationGroup hP hT c hdeg hst hM v hv
      (by rw [hv0]; exact hp) h1v sB hsBnb (by rw [hv0, hsB2]; simp)
    rwa [hsB1, hsB2, hsB3] at h
  have hVloc_card : Nat.card ↥Vloc = t := by
    let sB : GPath Γ 4 := GPath.cons z1
      (GPath.cons L1 (GPath.cons p (GPath.ofAdj hw2L2) hL2) hL1.symm) hz1L1.symm
    have hsB0 : sB 0 = z1 := rfl
    have hsB1 : sB 1 = L1 := rfl
    have hsB2 : sB 2 = p := rfl
    have hsB3 : sB 3 = L2 := rfl
    have hsB4 : sB 4 = w2 := rfl
    have hsBnb : sB.NoBack := by
      intro i hi
      have hi2 : i ≤ 2 := by omega
      interval_cases i
      · rw [hsB0, hsB2]; exact hz1p
      · rw [hsB1, hsB3]; exact hL21'
      · rw [hsB2, hsB4]; exact hw2p.symm
    have h := card_rootGroup hP hT hM sB hsBnb
    rw [hsB1, hsB2, hsB3] at h
    have hd : Γ.degree (sB 4) = t + 1 := by
      rw [hsB4, hdeg w2]
      exact if_pos (color_eq_zero_of_adj_of_color_eq_one hcL2 hw2L2)
    have hd' : Γ.degree (sB 4) - 1 = t := by rw [hd]; omega
    rw [hd'] at h
    exact h
  have hVloc_trans : ∀ K K' : V, Γ.Adj z1 K → K ≠ L1 → Γ.Adj z1 K' → K' ≠ L1 →
      ∃ g ∈ Vloc, g • K = K' := by
    intro K K' hK hKL hK' hK'L
    let sB : GPath Γ 4 := GPath.cons z1
      (GPath.cons L1 (GPath.cons p (GPath.ofAdj hw2L2) hL2) hL1.symm) hz1L1.symm
    have hsB0 : sB 0 = z1 := rfl
    have hsB1 : sB 1 = L1 := rfl
    have hsB2 : sB 2 = p := rfl
    have hsB3 : sB 3 = L2 := rfl
    have hsB4 : sB 4 = w2 := rfl
    have hsBnb : sB.NoBack := by
      intro i hi
      have hi2 : i ≤ 2 := by omega
      interval_cases i
      · rw [hsB0, hsB2]; exact hz1p
      · rw [hsB1, hsB3]; exact hL21'
      · rw [hsB2, hsB4]; exact hw2p.symm
    have hrev4 : sB.rev 4 = z1 := by rw [GPath.rev_apply _ le_rfl]; omega
    have hrev3 : sB.rev 3 = L1 := by
      rw [GPath.rev_apply _ (by omega)]; rw [show 4 - 3 = 1 by omega, hsB1]
    have hrev1 : sB.rev 1 = L2 := by
      rw [GPath.rev_apply _ (by omega)]; rw [show 4 - 1 = 3 by omega, hsB3]
    have hrev2 : sB.rev 2 = p := by
      rw [GPath.rev_apply _ (by omega)]; rw [show 4 - 2 = 2 by omega, hsB2]
    have hrevnb : sB.rev.NoBack := hsBnb.rev
    obtain ⟨g, hgfix, hgK⟩ := hM (sB.rev) hrevnb K K'
      (by rw [hrev4]; exact hK) (by rw [hrev4]; exact hK')
      (by rw [hrev3]; exact hKL) (by rw [hrev3]; exact hK'L)
    have hgU : g ∈ Vloc := by
      rw [mem_rootGroup]
      refine ⟨?_, ?_, ?_⟩
      · rw [mem_fixingSubgroup_iff]; intro x hx
        exact hgfix 3 (by omega) (by omega) x (by rw [hrev3]; exact hx)
      · rw [mem_fixingSubgroup_iff]; intro x hx
        exact hgfix 2 (by omega) (by omega) x (by rw [hrev2]; exact hx)
      · rw [mem_fixingSubgroup_iff]; intro x hx
        exact hgfix 1 (by omega) (by omega) x (by rw [hrev1]; exact hx)
    exact ⟨g, hgU, hgK⟩
  let U1 : Subgroup H := rootGroup H Γ p L1 z1
  have hU1_eq : U1 = rootGroup H Γ p L1 z1 := rfl
  have hU1leE : U1 ≤ E := by
    let qW : GPath Γ 4 := GPath.cons L0
      (GPath.cons p (GPath.cons L1 (GPath.ofAdj hz1M1) hz1L1) hL1) hL0.symm
    have hq1 : qW 1 = p := rfl
    have hq2 : qW 2 = L1 := rfl
    have hq3 : qW 3 = z1 := rfl
    have hq4 : qW 4 = M1 := rfl
    have hq : qW.NoBack := by
      intro i hi
      have hi2 : i ≤ 2 := by omega
      interval_cases i
      · rw [show qW 0 = L0 from rfl, hq2]; exact hL10'
      · rw [hq1, hq3]; exact hz1p.symm
      · rw [hq2, hq4]; exact hM1ne.symm
    have h := rootGroup_le_elationGroup hP hT c hdeg hst hM v hv
      (by rw [hv0]; exact hp) h1v qW hq (by rw [hv0, hq1]; simp)
    rwa [hq1, hq2, hq3] at h
  have hU1card : Nat.card ↥U1 = s := by
    let qW : GPath Γ 4 := GPath.cons L0
      (GPath.cons p (GPath.cons L1 (GPath.ofAdj hz1M1) hz1L1) hL1) hL0.symm
    have hq1 : qW 1 = p := rfl
    have hq2 : qW 2 = L1 := rfl
    have hq3 : qW 3 = z1 := rfl
    have hq4 : qW 4 = M1 := rfl
    have hq : qW.NoBack := by
      intro i hi
      have hi2 : i ≤ 2 := by omega
      interval_cases i
      · rw [show qW 0 = L0 from rfl, hq2]; exact hL10'
      · rw [hq1, hq3]; exact hz1p.symm
      · rw [hq2, hq4]; exact hM1ne.symm
    have h := card_rootGroup hP hT hM qW hq
    rw [hq1, hq2, hq3] at h
    have hd : Γ.degree (qW 4) = s + 1 := by
      rw [hq4, hdeg M1, if_neg (by rw [hcM1]; decide)]
    have hd' : Γ.degree (qW 4) - 1 = s := by rw [hd]; omega
    rw [hd'] at h
    exact h
  have hU1leS1 : U1 ≤ S1 := by
    intro u hu
    refine Subgroup.mem_inf.mpr ⟨hU1leE hu, ?_⟩
    refine MulAction.mem_stabilizer_iff.mpr ?_
    exact (mem_fixingSubgroup_iff H).mp ((mem_rootGroup H).mp hu).2.2 M1 hz1M1
  have hmaps1 : ∀ g : ↥S1, (g : H) • y ∈ Γ.neighborSet M1 \ {z1} := by
    intro g
    have hgE : (g : H) ∈ E := (Subgroup.mem_inf.mp g.2).1
    have hgM : (g : H) • M1 = M1 := (MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp g.2).2)
    have hfixp : (g : H) • p = p := by
      have h := elationGroup_le_whorlGroup v hv hgE
      rw [hv0] at h
      exact whorlGroup_fix_self hP hT h
    have hadj : Γ.Adj M1 ((g : H) • y) := by
      have h := (GraphAction.adj_smul (g : H) y M1).mpr hyM1
      rw [hgM] at h
      exact h.symm
    refine ⟨by simpa using hadj, ?_⟩
    intro hzy
    have hdist : Γ.dist p ((g : H) • y) = 4 := by
      have h := GPath.dist_smul hP.connected (g : H) p y
      rw [hfixp] at h
      rw [h]
      exact hy4
    rw [hzy, hzp1] at hdist
    omega
  haveI : Fintype ↥S1 :=
    Fintype.ofInjective (fun g : ↥S1 => (⟨(g : H), (Subgroup.mem_inf.mp g.2).1⟩ : ↥E))
      (by
        intro a b hab
        apply Subtype.ext
        exact congrArg (fun z : ↥E => (z : H)) hab)
  have hS1le : Nat.card ↥S1 ≤ s := by
    let f : ↥S1 → ↥(Γ.neighborSet M1 \ {z1}) := fun g => ⟨(g : H) • y, hmaps1 g⟩
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
    rw [Nat.card_coe_set_eq, ncard_points_of_line_erase hdeg hcM1 hz1M1.symm] at hcard
    exact hcard
  have hS1_eq_U1 : S1 = U1 := by
    have h := Subgroup.eq_of_le_of_card_ge hU1leS1 (by rw [hU1card]; exact hS1le)
    exact h.symm
  have hS1s_fix : ∀ θ : H, θ ∈ S1s → ∀ u : V, Γ.Adj L1 u → θ • u = u := by
    intro θ hθ u hu
    have hθE : θ ∈ E := (Subgroup.mem_inf.mp hθ).1
    have hθz : θ • z1 = z1 := (MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hθ).2)
    by_cases hfixM : θ • M1 = M1
    · have hθS1 : θ ∈ S1 := Subgroup.mem_inf.mpr ⟨hθE, MulAction.mem_stabilizer_iff.mpr hfixM⟩
      rw [hS1_eq_U1] at hθS1
      exact (mem_fixingSubgroup_iff H).mp ((mem_rootGroup H).mp hθS1).2.1 u hu
    · have hKL1 : θ • M1 ≠ L1 := by
        intro h
        have hθL : θ • L1 = L1 := by
          have h' := elationGroup_le_whorlGroup v hv hθE
          rw [hv0] at h'
          rw [mem_whorlGroup, mem_fixingSubgroup_iff] at h'
          exact h' L1 hL1
        have hML : M1 = L1 := by
          calc M1 = θ⁻¹ • (θ • M1) := by simp
            _ = θ⁻¹ • L1 := by rw [h]
            _ = θ⁻¹ • (θ • L1) := by rw [hθL]
            _ = L1 := by simp
        exact hM1ne hML
      have hKadj : Γ.Adj z1 (θ • M1) := by
        have h := (GraphAction.adj_smul θ M1 z1).mpr hz1M1.symm
        rw [hθz] at h
        exact h.symm
      obtain ⟨φ, hφV, hφK⟩ := hVloc_trans (θ • M1) M1 hKadj hKL1 hz1M1 hM1ne
      have hφfix : ∀ v : V, Γ.Adj L1 v → φ • v = v := by
        intro v hv
        exact (mem_fixingSubgroup_iff H).mp ((mem_rootGroup H).mp hφV).1 v hv
      have hφθS1 : φ * θ ∈ S1 := by
        refine Subgroup.mem_inf.mpr ⟨E.mul_mem (hVloc_le hφV) hθE, ?_⟩
        refine MulAction.mem_stabilizer_iff.mpr ?_
        show (φ * θ) • M1 = M1
        rw [mul_smul, hφK]
      rw [hS1_eq_U1] at hφθS1
      have hφθfix : (φ * θ) • u = u :=
        (mem_fixingSubgroup_iff H).mp ((mem_rootGroup H).mp hφθS1).2.1 u hu
      have : θ • u = φ⁻¹ • u := by
        have h := hφθfix
        rw [mul_smul] at h
        exact eq_inv_smul_iff.mpr h
      rw [this]
      have hφu : φ • u = u := hφfix u hu
      calc φ⁻¹ • u = φ⁻¹ • (φ • u) := by rw [hφu]
        _ = u := by simp

  have hE_fixL0 : ∀ e : H, e ∈ E → e • L0 = L0 := by
    intro e he
    have h := elationGroup_le_whorlGroup v hv he
    rw [hv0] at h
    rw [mem_whorlGroup, mem_fixingSubgroup_iff] at h
    exact h L0 hL0
  have hE_fixL1 : ∀ e : H, e ∈ E → e • L1 = L1 := by
    intro e he
    have h := elationGroup_le_whorlGroup v hv he
    rw [hv0] at h
    rw [mem_whorlGroup, mem_fixingSubgroup_iff] at h
    exact h L1 hL1
  have hpoint_fix : ∀ e : H, e ∈ E → e • p = p := by
    intro e he
    have h := elationGroup_le_whorlGroup v hv he
    rw [hv0] at h
    exact whorlGroup_fix_self hP hT h
  have hS0s_normal : ∀ e : H, e ∈ E → ∀ y : H, y ∈ S0s ↔ e * y * e⁻¹ ∈ S0s := by
    intro e he y
    have heL0 : e • L0 = L0 := hE_fixL0 e he
    have he'L0 : e⁻¹ • L0 = L0 := hE_fixL0 e⁻¹ (E.inv_mem he)
    constructor
    · intro hy
      have hyE : y ∈ E := (Subgroup.mem_inf.mp hy).1
      have hyfix : ∀ u : V, Γ.Adj L0 u → y • u = u := hS0s_fix y hy
      refine Subgroup.mem_inf.mpr ⟨E.mul_mem (E.mul_mem he hyE) (E.inv_mem he), ?_⟩
      refine MulAction.mem_stabilizer_iff.mpr ?_
      show (e * y * e⁻¹) • z0 = z0
      have hzL0 : Γ.Adj L0 (e⁻¹ • z0) := by
        have h := (GraphAction.adj_smul e⁻¹ L0 z0).mpr hz0L0
        rw [he'L0] at h
        exact h
      have hfix := hyfix (e⁻¹ • z0) hzL0
      calc (e * y * e⁻¹) • z0 = e • (y • (e⁻¹ • z0)) := by simp [mul_smul]
        _ = e • (e⁻¹ • z0) := by rw [hfix]
        _ = z0 := by simp
    · intro hy
      have hyE : y ∈ E := by
        have hEY : e * y * e⁻¹ ∈ E := (Subgroup.mem_inf.mp hy).1
        have hyEq : y = e⁻¹ * (e * y * e⁻¹) * e := by group
        rw [hyEq]
        exact E.mul_mem (E.mul_mem (E.inv_mem he) hEY) he
      have hconjfix : ∀ u : V, Γ.Adj L0 u → (e * y * e⁻¹) • u = u :=
        hS0s_fix (e * y * e⁻¹) hy
      have hzL0 : Γ.Adj L0 (e • z0) := by
        have h := (GraphAction.adj_smul e L0 z0).mpr hz0L0
        rw [heL0] at h
        exact h
      have h := hconjfix (e • z0) hzL0
      have h' : e • (y • z0) = e • z0 := by
        calc e • (y • z0) = (e * y) • z0 := by simp [mul_smul]
          _ = ((e * y * e⁻¹) * e) • z0 := by group
          _ = (e * y * e⁻¹) • (e • z0) := by simp [mul_smul]
          _ = e • z0 := h
      have h2 := congrArg (fun w => e⁻¹ • w) h'
      refine Subgroup.mem_inf.mpr ⟨hyE, ?_⟩
      refine MulAction.mem_stabilizer_iff.mpr ?_
      show y • z0 = z0
      simpa using h2
  have hS1s_normal : ∀ e : H, e ∈ E → ∀ y : H, y ∈ S1s ↔ e * y * e⁻¹ ∈ S1s := by
    intro e he y
    have heL1 : e • L1 = L1 := hE_fixL1 e he
    have he'L1 : e⁻¹ • L1 = L1 := hE_fixL1 e⁻¹ (E.inv_mem he)
    constructor
    · intro hy
      have hyE : y ∈ E := (Subgroup.mem_inf.mp hy).1
      have hyfix : ∀ u : V, Γ.Adj L1 u → y • u = u := hS1s_fix y hy
      refine Subgroup.mem_inf.mpr ⟨E.mul_mem (E.mul_mem he hyE) (E.inv_mem he), ?_⟩
      refine MulAction.mem_stabilizer_iff.mpr ?_
      show (e * y * e⁻¹) • z1 = z1
      have hzL1 : Γ.Adj L1 (e⁻¹ • z1) := by
        have h := (GraphAction.adj_smul e⁻¹ L1 z1).mpr hz1L1
        rw [he'L1] at h
        exact h
      have hfix := hyfix (e⁻¹ • z1) hzL1
      calc (e * y * e⁻¹) • z1 = e • (y • (e⁻¹ • z1)) := by simp [mul_smul]
        _ = e • (e⁻¹ • z1) := by rw [hfix]
        _ = z1 := by simp
    · intro hy
      have hyE : y ∈ E := by
        have hEY : e * y * e⁻¹ ∈ E := (Subgroup.mem_inf.mp hy).1
        have hyEq : y = e⁻¹ * (e * y * e⁻¹) * e := by group
        rw [hyEq]
        exact E.mul_mem (E.mul_mem (E.inv_mem he) hEY) he
      have hconjfix : ∀ u : V, Γ.Adj L1 u → (e * y * e⁻¹) • u = u :=
        hS1s_fix (e * y * e⁻¹) hy
      have hzL1 : Γ.Adj L1 (e • z1) := by
        have h := (GraphAction.adj_smul e L1 z1).mpr hz1L1
        rw [heL1] at h
        exact h
      have h := hconjfix (e • z1) hzL1
      have h' : e • (y • z1) = e • z1 := by
        calc e • (y • z1) = (e * y) • z1 := by simp [mul_smul]
          _ = ((e * y * e⁻¹) * e) • z1 := by group
          _ = (e * y * e⁻¹) • (e • z1) := by simp [mul_smul]
          _ = e • z1 := h
      have h2 := congrArg (fun w => e⁻¹ • w) h'
      refine Subgroup.mem_inf.mpr ⟨hyE, ?_⟩
      refine MulAction.mem_stabilizer_iff.mpr ?_
      show y • z1 = z1
      simpa using h2
  exact ⟨L0, hL0, L1, hL1, hL10, L2, hL2, hL20, hL21, hcL0, hcL1, hcL2, hL10', hL20', hL21',
    ht2, hs2, hOpp, hpos, y, hyF, hy4, hcy, hyL0, hyL1, z0, z1, hz0L0, hz1L1, hyz0, hyz1, hcz0,
    hcz1, hz0p, hz1p, M0, M1, hyM0, hz0M0, hyM1, hz1M1, hcM0, hcM1, hM0ne, hM1ne, hzp0, hzp1,
    hpM0, hpM1, hdistpM0, hdistpM1, v, hv, hv0, h1v, E, hE0, hv4, hEcard, hfree, htrans, S0,
    S1, S0s, S1s, w2, hw2L2, hw2p, M2, hw2M2, hM2L2, hexists_smul_L0, horbit0, hL0p_card,
    horbit0card, hS0s_card, Uloc, hUloc_le, hUloc_card, hUloc_trans, U0, hU0leE, hU0card,
    hU0leS0, hmaps, hS0le, hS0_eq_U0, hS0s_fix, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, hexists_smul_L1, horbit1,
    hL1p_card, horbit1card, hS1s_card, Vloc, hVloc_le, hVloc_card, hVloc_trans, U1, hU1leE,
    hU1card, hU1leS1, hmaps1, hS1le, hS1_eq_U1, hS1s_fix, hE_fixL0, hE_fixL1, hpoint_fix,
    hS0s_normal, hS1s_normal, hVloc_eq, hU1_eq ⟩

end CFSG.Geometry.GeneralizedQuadrangles
