module

public import CFSG.Geometry.GeneralizedQuadrangles.Moufang.NoSpansTwoCore2
public import CFSG.Geometry.GeneralizedQuadrangles.Moufang.NoSpansTwoSpan
public import CFSG.Geometry.GeneralizedQuadrangles.Moufang.NoSpansTwoAux2

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons CFSG.Quasithin CFSG.Quasithin.Stroth
open scoped Pointwise

variable {V : Type} {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]
  {H : Type} [Group H] [MulAction H V] [FaithfulSMul H V] [GraphAction H Γ]


private theorem card_sup_mul_card_inf {G : Type*} [Group G] (H N : Subgroup G)
    (h : ∀ b ∈ H, ∀ n ∈ N, b * n * b⁻¹ ∈ N) :
    Nat.card (H ⊔ N : Subgroup G) * Nat.card (H ⊓ N : Subgroup G) =
      Nat.card H * Nat.card N := by
  have hLE : H ≤ Subgroup.normalizer (N : Set G) := fun b hb => by
    rw [Subgroup.mem_normalizer_iff]; intro n; constructor
    · intro hn; exact h b hb n hn
    · intro hn
      have := h b⁻¹ (inv_mem hb) _ hn
      simpa [mul_assoc] using this
  have h1 : N.relIndex (H ⊔ N) = N.relIndex H := by
    letI := Subgroup.normal_subgroupOf_of_le_normalizer hLE
    letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hLE
    unfold Subgroup.relIndex Subgroup.index
    exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hLE).toEquiv.symm
  have e1 := Subgroup.relIndex_mul_card (H := N) (K := H ⊔ N)
  have e2 := Subgroup.relIndex_mul_card (H := N) (K := H)
  rw [inf_of_le_left (le_sup_right : N ≤ H ⊔ N)] at e1
  rw [h1] at e1
  rw [inf_comm]
  rw [← e1, ← e2]
  ring

private theorem set_mul_ncard_of_inf_eq_bot {G : Type*} [Group G] {A B : Subgroup G}
    (hAB : A ⊓ B = ⊥) :
    ((A : Set G) * (B : Set G)).ncard = Nat.card A * Nat.card B := by
  let f : ↥A × ↥B → G := fun p => (p.1 : G) * (p.2 : G)
  have hinj : Function.Injective f := by
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ heq
    have heq' : (a₁ : G) * b₁ = a₂ * b₂ := heq
    have hmem : (a₂ : G)⁻¹ * a₁ ∈ A ⊓ B := by
      refine ⟨A.mul_mem (A.inv_mem a₂.2) a₁.2, ?_⟩
      have e : (a₂ : G)⁻¹ * a₁ = b₂ * (b₁ : G)⁻¹ := by
        calc (a₂ : G)⁻¹ * a₁ = (a₂ : G)⁻¹ * (a₁ * b₁) * (b₁ : G)⁻¹ := by group
          _ = (a₂ : G)⁻¹ * (a₂ * b₂) * (b₁ : G)⁻¹ := by rw [heq']
          _ = b₂ * (b₁ : G)⁻¹ := by group
      rw [e]
      exact B.mul_mem b₂.2 (B.inv_mem b₁.2)
    rw [hAB, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    have hb : (b₁ : G) = b₂ := by
      have h : (a₁ : G) * b₁ = a₁ * b₂ := by rw [heq', hmem]
      exact mul_left_cancel h
    exact Prod.ext (Subtype.ext hmem.symm) (Subtype.ext hb)
  have himg : f '' Set.univ = (A : Set G) * (B : Set G) := by
    ext x
    constructor
    · rintro ⟨p, -, rfl⟩
      exact Set.mul_mem_mul p.1.2 p.2.2
    · intro hx
      rcases hx with ⟨a, ha, b, hb, rfl⟩
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Set.mem_univ _, rfl⟩
  have h := Set.ncard_image_of_injective (Set.univ : Set (↥A × ↥B)) hinj
  rw [himg, Set.ncard_univ, Nat.card_prod] at h
  exact h

theorem false_of_spans_two (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1) (hst : s ≤ t)
    (hM : MoufangCondition H Γ 4) {p : V} (hp : c p = 0)
    (h1 : ∀ x, Γ.dist p x = 4 → (spanSet Γ p x).ncard = 2)
    (h2 : ∀ L M, Γ.Adj p L → Γ.dist L M = 4 → (spanSet Γ L M).ncard = 2) : False := by
  classical
  let D := noSpansTwoBase hP hT c hdeg hst hM hp h1 h2
  obtain ⟨L0, hL0, L1, hL1, hL10, L2, hL2, hL20, hL21, hcL0, hcL1, hcL2, hL10', hL20', hL21',
    ht2, hs2, hOpp, hpos, y, hyF, hy4, hcy, hyL0, hyL1, z0, z1, hz0L0, hz1L1, hyz0, hyz1, hcz0,
    hcz1, hz0p, hz1p, M0, M1, hyM0, hz0M0, hyM1, hz1M1, hcM0, hcM1, hM0ne, hM1ne, hzp0, hzp1,
    hpM0, hpM1, hdistpM0, hdistpM1, v, hv, hv0, h1v, E, hE0, hv4, hEcard, hfree, htrans, S0,
    S1, S0s, S1s, w2, hw2L2, hw2p, M2, hw2M2, hM2L2, hexists_smul_L0, horbit0, hL0p_card,
    horbit0card, hS0s_card, Uloc, hUloc_le, hUloc_card, hUloc_trans, U0, hU0leE, hU0card,
    hU0leS0, hmaps, hS0le, hS0_eq_U0, hS0s_fix, hE_eq, hS0_eq, hS1_eq, hS0s_eq, hS1s_eq,
    hUloc_eq, hU0_eq⟩ := D
  subst hE_eq
  classical
  let M := noSpansTwoMid hP hT c hdeg hst hM hp h1 h2 (noSpansTwoBase hP hT c hdeg hst hM hp h1 h2)
  obtain ⟨L0, hL0, L1, hL1, hL10, L2, hL2, hL20, hL21, hcL0, hcL1, hcL2, hL10', hL20', hL21',
    ht2, hs2, hOpp, hpos, y, hyF, hy4, hcy, hyL0, hyL1, z0, z1, hz0L0, hz1L1, hyz0, hyz1, hcz0,
    hcz1, hz0p, hz1p, M0, M1, hyM0, hz0M0, hyM1, hz1M1, hcM0, hcM1, hM0ne, hM1ne, hzp0, hzp1,
    hpM0, hpM1, hdistpM0, hdistpM1, v, hv, hv0, h1v, E, hE0, hv4, hEcard, hfree, htrans, S0,
    S1, S0s, S1s, w2, hw2L2, hw2p, M2, hw2M2, hM2L2, hexists_smul_L0, horbit0, hL0p_card,
    horbit0card, hS0s_card, Uloc, hUloc_le, hUloc_card, hUloc_trans, U0, hU0leE, hU0card,
    hU0leS0, hmaps, hS0le, hS0_eq_U0, hS0s_fix, hE_eq, hS0_eq, hS1_eq, hS0s_eq, hS1s_eq,
    hUloc_eq, hU0_eq, hexists_smul_L1, horbit1, hL1p_card, horbit1card, hS1s_card, Vloc,
    hVloc_le, hVloc_card, hVloc_trans, U1, hU1leE, hU1card, hU1leS1, hmaps1, hS1le, hS1_eq_U1,
    hS1s_fix, hE_fixL0, hE_fixL1, hpoint_fix, hS0s_normal, hS1s_normal, hVloc_eq, hU1_eq⟩ := M
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
  subst hVloc_eq
  let Vloc : Subgroup H := rootGroup H Γ L1 p L2
  subst hU1_eq
  let U1 : Subgroup H := rootGroup H Γ p L1 z1


  haveI hEfin : Fintype ↥E :=
    Fintype.ofInjective (fun e : ↥E => fun x : V => (e : H) • x)
      (by
        intro e f hef
        apply Subtype.ext
        exact eq_of_smul_eq_smul (m₁ := (e : H)) (m₂ := (f : H))
          (fun x => congrFun hef x))

  let D : Subgroup H := S0s ⊓ S1s
  let U01 : Subgroup H := rootGroup H Γ L0 p L1
  have hU01_le_E : U01 ≤ E := by
    let qD : GPath Γ 4 := GPath.cons z0
      (GPath.cons L0 (GPath.cons p (GPath.ofAdj hz1L1) hL1) hL0.symm) hz0L0.symm
    have hq1 : qD 1 = L0 := rfl
    have hq2 : qD 2 = p := rfl
    have hq3 : qD 3 = L1 := rfl
    have hq4 : qD 4 = z1 := rfl
    have hqnb : qD.NoBack := by
      intro i hi
      have hi2 : i ≤ 2 := by omega
      interval_cases i
      · rw [show qD 0 = z0 from rfl, hq2]; exact hz0p
      · rw [hq1, hq3]; exact hL10'
      · rw [hq2, hq4]; exact hz1p.symm
    have h := rootGroup_le_elationGroup hP hT c hdeg hst hM v hv
      (by rw [hv0]; exact hp) h1v qD hqnb (by rw [hv0, hq2]; simp)
    rwa [hq1, hq2, hq3] at h

  have hU01_card : Nat.card ↥U01 = t := by
    let qD : GPath Γ 4 := GPath.cons z0
      (GPath.cons L0 (GPath.cons p (GPath.ofAdj hz1L1) hL1) hL0.symm) hz0L0.symm
    have hq1 : qD 1 = L0 := rfl
    have hq2 : qD 2 = p := rfl
    have hq3 : qD 3 = L1 := rfl
    have hq4 : qD 4 = z1 := rfl
    have hqnb : qD.NoBack := by
      intro i hi
      have hi2 : i ≤ 2 := by omega
      interval_cases i
      · rw [show qD 0 = z0 from rfl, hq2]; exact hz0p
      · rw [hq1, hq3]; exact hL10'
      · rw [hq2, hq4]; exact hz1p.symm
    have h := card_rootGroup hP hT hM qD hqnb
    rw [hq1, hq2, hq3] at h
    have hd : Γ.degree (qD 4) = t + 1 := by
      rw [hq4, hdeg z1, if_pos hcz1]
    have hd' : Γ.degree (qD 4) - 1 = t := by rw [hd]; omega
    rw [hd'] at h
    exact h
  have hD_le_U01 : D ≤ U01 := by
    intro θ hθ
    have hθ0 : θ ∈ S0s := (Subgroup.mem_inf.mp hθ).1
    have hθ1 : θ ∈ S1s := (Subgroup.mem_inf.mp hθ).2
    have hθE : θ ∈ E := (Subgroup.mem_inf.mp hθ0).1
    rw [mem_rootGroup]
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_fixingSubgroup_iff]; exact hS0s_fix θ hθ0
    · rw [mem_fixingSubgroup_iff]
      intro u hu
      have h := elationGroup_le_whorlGroup v hv hθE
      rw [hv0] at h
      exact (mem_fixingSubgroup_iff H).mp h u hu
    · rw [mem_fixingSubgroup_iff]; exact hS1s_fix θ hθ1
  have hU01_le_D : U01 ≤ D := by
    intro θ hθ
    have hθE : θ ∈ E := hU01_le_E hθ
    have hfixL0 : ∀ u : V, Γ.Adj L0 u → θ • u = u :=
      (mem_fixingSubgroup_iff H).mp ((mem_rootGroup H).mp hθ).1
    have hfixL1 : ∀ u : V, Γ.Adj L1 u → θ • u = u :=
      (mem_fixingSubgroup_iff H).mp ((mem_rootGroup H).mp hθ).2.2
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · refine Subgroup.mem_inf.mpr ⟨hθE, MulAction.mem_stabilizer_iff.mpr ?_⟩
      show θ • z0 = z0
      exact hfixL0 z0 hz0L0
    · refine Subgroup.mem_inf.mpr ⟨hθE, MulAction.mem_stabilizer_iff.mpr ?_⟩
      show θ • z1 = z1
      exact hfixL1 z1 hz1L1
  have hD_eq : D = U01 := le_antisymm hD_le_U01 hU01_le_D
  have hD_card : Nat.card ↥D = t := by rw [hD_eq, hU01_card]
  have hS0_le_S0s : S0 ≤ S0s := by
    intro θ hθ
    have hθE : θ ∈ E := (Subgroup.mem_inf.mp hθ).1
    have hθM : θ • M0 = M0 := (MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hθ).2)
    refine Subgroup.mem_inf.mpr ⟨hθE, MulAction.mem_stabilizer_iff.mpr ?_⟩
    show θ • z0 = z0
    have hfixp : θ • p = p := hpoint_fix θ hθE
    have hz0M0' : Γ.Adj M0 (θ • z0) := by
      have h := (GraphAction.adj_smul θ z0 M0).mpr hz0M0
      rw [hθM] at h
      exact h.symm
    have hdist : Γ.dist p (θ • z0) = 2 := by
      calc Γ.dist p (θ • z0) = Γ.dist (θ • p) (θ • z0) := by rw [hfixp]
        _ = Γ.dist p z0 := GPath.dist_smul hP.connected θ p z0
        _ = 2 := hzp0
    have h := eq_of_mem_line_of_dist_eq_three hP hdistpM0 hz0M0.symm hz0M0' hzp0 hdist
    exact h.symm
  have hS1_le_S1s : S1 ≤ S1s := by
    intro θ hθ
    have hθE : θ ∈ E := (Subgroup.mem_inf.mp hθ).1
    have hθM : θ • M1 = M1 := (MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hθ).2)
    refine Subgroup.mem_inf.mpr ⟨hθE, MulAction.mem_stabilizer_iff.mpr ?_⟩
    show θ • z1 = z1
    have hfixp : θ • p = p := hpoint_fix θ hθE
    have hz1M1' : Γ.Adj M1 (θ • z1) := by
      have h := (GraphAction.adj_smul θ z1 M1).mpr hz1M1
      rw [hθM] at h
      exact h.symm
    have hdist : Γ.dist p (θ • z1) = 2 := by
      calc Γ.dist p (θ • z1) = Γ.dist (θ • p) (θ • z1) := by rw [hfixp]
        _ = Γ.dist p z1 := GPath.dist_smul hP.connected θ p z1
        _ = 2 := hzp1
    have h := eq_of_mem_line_of_dist_eq_three hP hdistpM1 hz1M1.symm hz1M1' hzp1 hdist
    exact h.symm
  have hz01 : z0 ≠ z1 := by
    intro h
    have hz0L1 : Γ.Adj L1 z0 := by rw [h]; exact hz1L1
    have hdist : Γ.dist L0 L1 = 2 :=
      dist_eq_two_of_adj_of_adj_of_ne hP hL0.symm hL1 hL10'
    have hz0p' : z0 = p := (existsUnique_commonNeighbor hP hdist).unique
      ⟨hz0L0, hz0L1⟩ ⟨hL0.symm, hL1.symm⟩
    exact hz0p hz0p'
  have hz01_4 : Γ.dist z0 z1 = 4 :=
    dist_eq_four_of_mem_trace hP hy4 ⟨hzp0, hyz0⟩ ⟨hzp1, hyz1⟩ hz01
  have hS0_inter_D : S0 ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro θ hθ
    have hθS0 : θ ∈ S0 := (Subgroup.mem_inf.mp hθ).1
    have hθD : θ ∈ D := (Subgroup.mem_inf.mp hθ).2
    have hθU01 : θ ∈ U01 := hD_le_U01 hθD
    have hθz1 : θ • z1 = z1 :=
      (mem_fixingSubgroup_iff H).mp ((mem_rootGroup H).mp hθU01).2.2 z1 hz1L1
    have hθS0' : θ ∈ rootGroup H Γ z0 L0 p := by
      have h : rootGroup H Γ z0 L0 p = S0 := by
        rw [rootGroup_comm z0 L0 p]
        exact hS0_eq_U0.symm
      rw [h]; exact hθS0
    let qR : GPath Γ 4 := GPath.cons M0
      (GPath.cons z0 (GPath.cons L0 (GPath.ofAdj hL2) hL0.symm) hz0L0.symm) hz0M0.symm
    have hq1 : qR 1 = z0 := rfl
    have hq2 : qR 2 = L0 := rfl
    have hq3 : qR 3 = p := rfl
    have hqnb : qR.NoBack := by
      intro i hi
      have hi2 : i ≤ 2 := by omega
      interval_cases i
      · rw [show qR 0 = M0 from rfl, hq2]; exact hM0ne
      · rw [hq1, hq3]; exact hz0p
      · rw [hq2, show qR 4 = L2 from rfl]; exact hL20'
    have hmem : θ ∈ rootGroup H Γ (qR 1) (qR 2) (qR 3) := by
      rwa [hq1, hq2, hq3]
    have heq : θ = 1 := eq_one_of_mem_rootGroup_of_fix_opposite_end hP hT qR hqnb hmem
      (by rw [hq1]; exact hz01_4) hθz1
    exact Subgroup.mem_bot.mpr heq
  have hS1_inter_D : S1 ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro θ hθ
    have hθS1 : θ ∈ S1 := (Subgroup.mem_inf.mp hθ).1
    have hθD : θ ∈ D := (Subgroup.mem_inf.mp hθ).2
    have hθU01 : θ ∈ U01 := hD_le_U01 hθD
    have hθz0 : θ • z0 = z0 :=
      (mem_fixingSubgroup_iff H).mp ((mem_rootGroup H).mp hθU01).1 z0 hz0L0
    have hθS1' : θ ∈ rootGroup H Γ z1 L1 p := by
      have h : rootGroup H Γ z1 L1 p = S1 := by
        rw [rootGroup_comm z1 L1 p]
        exact hS1_eq_U1.symm
      rw [h]; exact hθS1
    let qR : GPath Γ 4 := GPath.cons M1
      (GPath.cons z1 (GPath.cons L1 (GPath.ofAdj hL2) hL1.symm) hz1L1.symm) hz1M1.symm
    have hq1 : qR 1 = z1 := rfl
    have hq2 : qR 2 = L1 := rfl
    have hq3 : qR 3 = p := rfl
    have hqnb : qR.NoBack := by
      intro i hi
      have hi2 : i ≤ 2 := by omega
      interval_cases i
      · rw [show qR 0 = M1 from rfl, hq2]; exact hM1ne
      · rw [hq1, hq3]; exact hz1p
      · rw [hq2, show qR 4 = L2 from rfl]; exact hL21'
    have hmem : θ ∈ rootGroup H Γ (qR 1) (qR 2) (qR 3) := by
      rwa [hq1, hq2, hq3]
    have heq : θ = 1 := eq_one_of_mem_rootGroup_of_fix_opposite_end hP hT qR hqnb hmem
      (by rw [hq1, SimpleGraph.dist_comm]; exact hz01_4) hθz0
    exact Subgroup.mem_bot.mpr heq

  haveI hS0sFin : Fintype ↥S0s :=
    Fintype.ofInjective (fun g : ↥S0s => (⟨(g : H), (Subgroup.mem_inf.mp g.2).1⟩ : ↥E))
      (by intro a b hab; apply Subtype.ext; exact congrArg (fun z : ↥E => (z : H)) hab)
  haveI hS1sFin : Fintype ↥S1s :=
    Fintype.ofInjective (fun g : ↥S1s => (⟨(g : H), (Subgroup.mem_inf.mp g.2).1⟩ : ↥E))
      (by intro a b hab; apply Subtype.ext; exact congrArg (fun z : ↥E => (z : H)) hab)
  have hS0s_le_E : S0s ≤ E := fun x hx => (Subgroup.mem_inf.mp hx).1
  have hS1s_le_E : S1s ≤ E := fun x hx => (Subgroup.mem_inf.mp hx).1
  have hS0_le_E : S0 ≤ E := fun x hx => hS0s_le_E (hS0_le_S0s hx)
  have hS1_le_E : S1 ≤ E := fun x hx => hS1s_le_E (hS1_le_S1s hx)
  have hS0_card : Nat.card ↥S0 = s := by
    change Nat.card ↥(E ⊓ MulAction.stabilizer H M0) = s
    rw [hS0_eq_U0, hU0card]
  have hS1_card : Nat.card ↥S1 = s := by
    change Nat.card ↥(E ⊓ MulAction.stabilizer H M1) = s
    rw [hS1_eq_U1, hU1card]
  have hS0_normal : ∀ e : H, e ∈ S0s → ∀ y : H, y ∈ S0 ↔ e * y * e⁻¹ ∈ S0 := by
    intro e he y
    have heE : e ∈ E := (Subgroup.mem_inf.mp he).1
    have hdp : e • p = p := hpoint_fix e heE
    have hdL : e • L0 = L0 := hE_fixL0 e heE
    have hdz : e • z0 = z0 := (MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp he).2)
    have hmap_of : ∀ d : H, d • p = p → d • L0 = L0 → d • z0 = z0 →
        S0.map (MulAut.conj d).toMonoidHom = S0 := by
      intro d h1 h2 h3
      change (E ⊓ MulAction.stabilizer H M0).map (MulAut.conj d).toMonoidHom =
        (E ⊓ MulAction.stabilizer H M0)
      rw [hS0_eq_U0]
      have h := rootGroup_map_conj (H := H) (Γ := Γ) d p L0 z0
      rw [h1, h2, h3] at h
      exact h
    constructor
    · intro hy
      have hmem : (MulAut.conj e) y ∈ S0.map (MulAut.conj e).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
      rw [hmap_of e hdp hdL hdz] at hmem
      rw [MulAut.conj_apply] at hmem
      exact hmem
    · intro hy
      have he' : e⁻¹ ∈ S0s := S0s.inv_mem he
      have hdp' : e⁻¹ • p = p := hpoint_fix e⁻¹ (E.inv_mem heE)
      have hdL' : e⁻¹ • L0 = L0 := hE_fixL0 e⁻¹ (E.inv_mem heE)
      have hdz' : e⁻¹ • z0 = z0 :=
        (MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp he').2)
      have hmem : (MulAut.conj e⁻¹) (e * y * e⁻¹) ∈
          S0.map (MulAut.conj e⁻¹).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨_, hy, rfl⟩
      rw [hmap_of e⁻¹ hdp' hdL' hdz'] at hmem
      rw [MulAut.conj_apply] at hmem
      have hEq : e⁻¹ * (e * y * e⁻¹) * (e⁻¹)⁻¹ = y := by group
      rwa [hEq] at hmem
  have hS1_normal : ∀ e : H, e ∈ S1s → ∀ y : H, y ∈ S1 ↔ e * y * e⁻¹ ∈ S1 := by
    intro e he y
    have heE : e ∈ E := (Subgroup.mem_inf.mp he).1
    have hdp : e • p = p := hpoint_fix e heE
    have hdL : e • L1 = L1 := hE_fixL1 e heE
    have hdz : e • z1 = z1 := (MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp he).2)
    have hmap_of : ∀ d : H, d • p = p → d • L1 = L1 → d • z1 = z1 →
        S1.map (MulAut.conj d).toMonoidHom = S1 := by
      intro d h1 h2 h3
      change (E ⊓ MulAction.stabilizer H M1).map (MulAut.conj d).toMonoidHom =
        (E ⊓ MulAction.stabilizer H M1)
      rw [hS1_eq_U1]
      have h := rootGroup_map_conj (H := H) (Γ := Γ) d p L1 z1
      rw [h1, h2, h3] at h
      exact h
    constructor
    · intro hy
      have hmem : (MulAut.conj e) y ∈ S1.map (MulAut.conj e).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
      rw [hmap_of e hdp hdL hdz] at hmem
      rw [MulAut.conj_apply] at hmem
      exact hmem
    · intro hy
      have he' : e⁻¹ ∈ S1s := S1s.inv_mem he
      have hdp' : e⁻¹ • p = p := hpoint_fix e⁻¹ (E.inv_mem heE)
      have hdL' : e⁻¹ • L1 = L1 := hE_fixL1 e⁻¹ (E.inv_mem heE)
      have hdz' : e⁻¹ • z1 = z1 :=
        (MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp he').2)
      have hmem : (MulAut.conj e⁻¹) (e * y * e⁻¹) ∈
          S1.map (MulAut.conj e⁻¹).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨_, hy, rfl⟩
      rw [hmap_of e⁻¹ hdp' hdL' hdz'] at hmem
      rw [MulAut.conj_apply] at hmem
      have hEq : e⁻¹ * (e * y * e⁻¹) * (e⁻¹)⁻¹ = y := by group
      rwa [hEq] at hmem
  have hD_normal : ∀ e : H, e ∈ E → ∀ y : H, y ∈ D ↔ e * y * e⁻¹ ∈ D := by
    intro e he y
    have h0 := hS0s_normal e he y
    have h1 := hS1s_normal e he y
    constructor
    · intro hy
      have hy' : y ∈ S0s ∧ y ∈ S1s := hy
      exact ⟨h0.mp hy'.1, h1.mp hy'.2⟩
    · intro hy
      have hy' : e * y * e⁻¹ ∈ S0s ∧ e * y * e⁻¹ ∈ S1s := hy
      exact ⟨h0.mpr hy'.1, h1.mpr hy'.2⟩
  have hS0_inter_S1s : S0 ⊓ S1s = ⊥ := by
    rw [eq_bot_iff]
    intro θ hθ
    have hθS0 : θ ∈ S0 := (Subgroup.mem_inf.mp hθ).1
    have hθS1s : θ ∈ S1s := (Subgroup.mem_inf.mp hθ).2
    have hθD : θ ∈ D := Subgroup.mem_inf.mpr ⟨hS0_le_S0s hθS0, hθS1s⟩
    have hθ' : θ ∈ S0 ⊓ D := Subgroup.mem_inf.mpr ⟨hθS0, hθD⟩
    rw [hS0_inter_D] at hθ'
    exact hθ'
  have hS0D_card : Nat.card ↥(S0 ⊔ D) = s * t := by
    have h := card_sup_mul_card_inf S0 D
      (fun b hb n hn => (hD_normal b (hS0s_le_E (hS0_le_S0s hb)) n).mp hn)
    rw [hS0_inter_D] at h
    have hbot : Nat.card ↥((⊥ : Subgroup H)) = 1 := by simp
    rw [hbot, mul_one, hS0_card, hD_card] at h
    exact h
  have hS0s_eq : S0s = S0 ⊔ D := by
    have h1 : S0 ⊔ D ≤ S0s := sup_le hS0_le_S0s (fun x hx => (Subgroup.mem_inf.mp hx).1)
    exact (Subgroup.eq_of_le_of_card_ge h1 (by rw [hS0D_card, hS0s_card])).symm
  have hS1D_card : Nat.card ↥(S1 ⊔ D) = s * t := by
    have h := card_sup_mul_card_inf S1 D
      (fun b hb n hn => (hD_normal b (hS1s_le_E (hS1_le_S1s hb)) n).mp hn)
    rw [hS1_inter_D] at h
    have hbot : Nat.card ↥((⊥ : Subgroup H)) = 1 := by simp
    rw [hbot, mul_one, hS1_card, hD_card] at h
    exact h
  have hS1s_eq : S1s = S1 ⊔ D := by
    have h1 : S1 ⊔ D ≤ S1s := sup_le hS1_le_S1s (fun x hx => (Subgroup.mem_inf.mp hx).2)
    exact (Subgroup.eq_of_le_of_card_ge h1 (by rw [hS1D_card, hS1s_card])).symm
  have hS0S1s_card : Nat.card ↥(S0 ⊔ S1s) = s * (s * t) := by
    have h := card_sup_mul_card_inf S0 S1s
      (fun b hb n hn => (hS1s_normal b (hS0s_le_E (hS0_le_S0s hb)) n).mp hn)
    rw [hS0_inter_S1s] at h
    have hbot : Nat.card ↥((⊥ : Subgroup H)) = 1 := by simp
    rw [hbot, mul_one, hS0_card, hS1s_card] at h
    exact h
  have hS0S1s_le_E : S0 ⊔ S1s ≤ E :=
    sup_le (fun x hx => (Subgroup.mem_inf.mp hx).1) (fun x hx => (Subgroup.mem_inf.mp hx).1)
  have hE_eq : E = S0 ⊔ S1s := by
    refine (Subgroup.eq_of_le_of_card_ge hS0S1s_le_E ?_).symm
    rw [hS0S1s_card, hEcard]
    exact le_of_eq (by ring)
  have hE_eq_sup : E = S0 ⊔ S1 ⊔ D := by
    rw [hE_eq, hS1s_eq, sup_assoc]
  have hD_le_normS0 : D ≤ Subgroup.normalizer (S0 : Set H) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro s
    exact hS0_normal d ((Subgroup.mem_inf.mp hd).1) s
  have hS0_le_normD : S0 ≤ Subgroup.normalizer (D : Set H) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro d
    exact hD_normal s (hS0s_le_E (hS0_le_S0s hs)) d
  have hcomm_S0 : ∀ d : H, d ∈ D → ∀ s : H, s ∈ S0 → d * s = s * d := by
    intro d hd s hs
    have hdS0s : d ∈ S0s := (Subgroup.mem_inf.mp hd).1
    have hsS0s : s ∈ S0s := hS0_le_S0s hs
    have hcS0 : d * s * d⁻¹ * s⁻¹ ∈ S0 :=
      S0.mul_mem ((hS0_normal d hdS0s s).mp hs) (S0.inv_mem hs)
    have hcD : d * s * d⁻¹ * s⁻¹ ∈ D := by
      have h1 : s * d⁻¹ * s⁻¹ ∈ D := (hD_normal s (hS0s_le_E hsS0s) d⁻¹).mp (D.inv_mem hd)
      have h2 : d * s * d⁻¹ * s⁻¹ = d * (s * d⁻¹ * s⁻¹) := by group
      rw [h2]
      exact D.mul_mem hd h1
    have hc1 : d * s * d⁻¹ * s⁻¹ = 1 := by
      have hmem : d * s * d⁻¹ * s⁻¹ ∈ S0 ⊓ D := Subgroup.mem_inf.mpr ⟨hcS0, hcD⟩
      rw [hS0_inter_D] at hmem
      exact Subgroup.mem_bot.mp hmem
    calc d * s = (d * s * d⁻¹) * d := by group
      _ = s * d := by
        have h : d * s * d⁻¹ = s := by
          have h' := congrArg (fun x => x * s) hc1
          simpa [mul_assoc] using h'
        rw [h]
  have hD_le_normS1 : D ≤ Subgroup.normalizer (S1 : Set H) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro s
    exact hS1_normal d ((Subgroup.mem_inf.mp hd).2) s
  have hS1_le_normD : S1 ≤ Subgroup.normalizer (D : Set H) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro d
    exact hD_normal s (hS1s_le_E (hS1_le_S1s hs)) d
  have hcomm_S1 : ∀ d : H, d ∈ D → ∀ s : H, s ∈ S1 → d * s = s * d := by
    intro d hd s hs
    have hdS1s : d ∈ S1s := (Subgroup.mem_inf.mp hd).2
    have hsS1s : s ∈ S1s := hS1_le_S1s hs
    have hcS1 : d * s * d⁻¹ * s⁻¹ ∈ S1 :=
      S1.mul_mem ((hS1_normal d hdS1s s).mp hs) (S1.inv_mem hs)
    have hcD : d * s * d⁻¹ * s⁻¹ ∈ D := by
      have h1 : s * d⁻¹ * s⁻¹ ∈ D := (hD_normal s (hS1s_le_E hsS1s) d⁻¹).mp (D.inv_mem hd)
      have h2 : d * s * d⁻¹ * s⁻¹ = d * (s * d⁻¹ * s⁻¹) := by group
      rw [h2]
      exact D.mul_mem hd h1
    have hc1 : d * s * d⁻¹ * s⁻¹ = 1 := by
      have hmem : d * s * d⁻¹ * s⁻¹ ∈ S1 ⊓ D := Subgroup.mem_inf.mpr ⟨hcS1, hcD⟩
      rw [hS1_inter_D] at hmem
      exact Subgroup.mem_bot.mp hmem
    calc d * s = (d * s * d⁻¹) * d := by group
      _ = s * d := by
        have h : d * s * d⁻¹ = s := by
          have h' := congrArg (fun x => x * s) hc1
          simpa [mul_assoc] using h'
        rw [h]

  have hM01 : M0 ≠ M1 := by
    intro hh
    have hz1 : Γ.Adj M0 z1 := by rw [hh]; exact hz1M1.symm
    have h2' : Γ.dist z0 z1 = 2 := dist_eq_two_of_adj_of_adj_of_ne hP hz0M0 hz1 hz01
    omega
  have hM1L0 : M1 ≠ L0 := by
    intro hh
    have h : Γ.Adj y L0 := by rw [← hh]; exact hyM1
    have h1' : Γ.dist y L0 = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h
    omega
  have hM0L1 : M0 ≠ L1 := by
    intro hh
    have h : Γ.Adj y L1 := by rw [← hh]; exact hyM0
    have h1' : Γ.dist y L1 = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr h
    omega
  have hL1M0_4 : Γ.dist L1 M0 = 4 := by
    let pth : GPath Γ 4 := GPath.cons L1
      (GPath.cons p (GPath.cons L0 (GPath.ofAdj hz0M0) hz0L0) hL0) hL1.symm
    have hp0 : pth 0 = L1 := rfl
    have hp4 : pth 4 = M0 := rfl
    have hnb : pth.NoBack := by
      intro i hi
      have hi2 : i ≤ 2 := by omega
      interval_cases i
      · rw [show pth 0 = L1 from rfl, show pth 2 = L0 from rfl]; exact hL10'.symm
      · rw [show pth 1 = p from rfl, show pth 3 = z0 from rfl]; exact hz0p.symm
      · rw [show pth 2 = L0 from rfl, show pth 4 = M0 from rfl]; exact hM0ne.symm
    have hgeo := hP.isGeodesic_of_noBack (by norm_num : 4 ≤ 4) hnb
    simpa [GPath.IsGeodesic, hp0, hp4] using hgeo
  have hKD : ∀ h : H, h ∈ S0 ⊔ S1 → h ∈ D → h = 1 := by
    intro h hhK hhD
    by_contra hne
    have hhE : h ∈ E := (sup_le hS0_le_E hS1_le_E) hhK
    have hcentD : ∀ d : H, d ∈ D → h * d = d * h := by
      have hle : S0 ⊔ S1 ≤ Subgroup.centralizer (D : Set H) := by
        refine sup_le ?_ ?_
        · intro s hs
          rw [Subgroup.mem_centralizer_iff]
          intro d hd
          exact hcomm_S0 d hd s hs
        · intro s hs
          rw [Subgroup.mem_centralizer_iff]
          intro d hd
          exact hcomm_S1 d hd s hs
      have hmem : ∀ d ∈ D, d * h = h * d := by
        have := hle hhK
        rwa [Subgroup.mem_centralizer_iff] at this
      intro d hd
      exact (hmem d hd).symm
    have hcentE : ∀ x : H, x ∈ E → h * x = x * h := by
      have hle : S0 ⊔ S1 ⊔ D ≤ Subgroup.centralizer ({h} : Set H) := by
        refine sup_le (sup_le ?_ ?_) ?_
        · intro s hs
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          rw [hy]
          exact hcomm_S0 h hhD s hs
        · intro s hs
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          rw [hy]
          exact hcomm_S1 h hhD s hs
        · intro d hd
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          rw [hy]
          exact hcentD d hd
      intro x hx
      have hx' : x ∈ S0 ⊔ S1 ⊔ D := by rw [← hE_eq_sup]; exact hx
      have hmem := hle hx'
      rw [Subgroup.mem_centralizer_iff] at hmem
      exact hmem h (Set.mem_singleton h)
    have hfix_proj : ∀ (L : V) (hL : Γ.Adj p L) (hyL : Γ.dist y L = 3),
        h • proj hP hyL = proj hP hyL := by
      intro L hL hyL
      have hzLadj : Γ.Adj L (proj hP hyL) := proj_adj hP hyL
      have hyzL : Γ.dist y (proj hP hyL) = 2 := proj_dist hP hyL
      have hzLp : proj hP hyL ≠ p := by
        intro hh
        rw [hh, SimpleGraph.dist_comm] at hyzL
        omega
      have hyML : Γ.Adj y (commonNeighbor hP hyzL) := commonNeighbor_adj_left hP hyzL
      have hzML : Γ.Adj (proj hP hyL) (commonNeighbor hP hyzL) :=
        commonNeighbor_adj_right hP hyzL
      have hnorm : ∀ s : H, s ∈ elationGroup H Γ v →
          s • commonNeighbor hP hyzL = commonNeighbor hP hyzL →
          h * s * h⁻¹ ∈ elationGroup H Γ v ∧
            (h * s * h⁻¹) • commonNeighbor hP hyzL = commonNeighbor hP hyzL := by
        intro s hs hfix
        have hc : h * s = s * h := hcentE s hs
        have hconj : h * s * h⁻¹ = s := by rw [hc]; group
        rw [hconj]
        exact ⟨hs, hfix⟩
      exact normalizer_stabilizer_fixes hP hT c hdeg hst hM hp h1 h2 v hv hv0 hy4 hL
        hzLadj hzLp hyzL hyML hzML hEcard hfree hhE hnorm
    have hfix_trace : ∀ w : V, w ∈ traceSet Γ p y → h • w = w := by
      intro w hw
      have hwp : Γ.dist p w = 2 := hw.1
      have hwy : Γ.dist y w = 2 := hw.2
      let L : V := commonNeighbor hP hwp
      have hpL : Γ.Adj p L := commonNeighbor_adj_left hP hwp
      have hLw : Γ.Adj L w := (commonNeighbor_adj_right hP hwp).symm
      have hyL : Γ.dist y L = 3 := dist_eq_three_of_adj_of_dist_eq_four hP hy4 hpL
      have hzw : proj hP hyL = w := (eq_proj hP hyL hLw hwy).symm
      have h' := hfix_proj L hpL hyL
      rwa [hzw] at h'
    have hhy_span : h • y ∈ spanSet Γ p y := by
      intro w hw
      have hwfix : h • w = w := hfix_trace w hw
      have hdist : Γ.dist (h • y) w = Γ.dist y w := by
        calc Γ.dist (h • y) w = Γ.dist (h • y) (h • w) := by rw [hwfix]
          _ = Γ.dist y w := GPath.dist_smul hP.connected h y w
      rw [hdist, hw.2]
    have hy_ne_p : y ≠ p := by
      intro hh
      rw [hh] at hy4
      simp at hy4
    have hhy_ne_y : h • y ≠ y := by
      intro hhy
      have h1' : (⟨h, hhE⟩ : ↥E) = 1 := hfree ⟨h, hhE⟩ hy4 hhy
      exact hne (congrArg Subtype.val h1')
    have hhy_ne_p : h • y ≠ p := by
      intro hhy
      have h1' : y = h⁻¹ • p := by
        calc y = h⁻¹ • (h • y) := by simp
          _ = h⁻¹ • p := by rw [hhy]
      have h2' : h⁻¹ • p = p := hpoint_fix h⁻¹ (E.inv_mem hhE)
      rw [h2'] at h1'
      exact hy_ne_p h1'
    have hthree : 3 ≤ (spanSet Γ p y).ncard := by
      have hsub : ({p, y, h • y} : Set V) ⊆ spanSet Γ p y := by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl
        · exact left_mem_spanSet hy4
        · exact right_mem_spanSet hy4
        · exact hhy_span
      have hcard : ({p, y, h • y} : Set V).ncard = 3 := by
        rw [Set.ncard_eq_three]
        exact ⟨p, y, h • y, hy_ne_p.symm, hhy_ne_p.symm, hhy_ne_y.symm, rfl⟩
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      rwa [hcard] at hle
    have hpspan := h1 y hy4
    omega
  have hKD_bot : (S0 ⊔ S1) ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    intro h hh
    exact Subgroup.mem_bot.mpr (hKD h (Subgroup.mem_inf.mp hh).1 (Subgroup.mem_inf.mp hh).2)
  have hK_card : Nat.card ↥(S0 ⊔ S1) = s * s := by
    have h := card_sup_mul_card_inf (S0 ⊔ S1) D
      (fun b hb n hn => (hD_normal b ((sup_le hS0_le_E hS1_le_E) hb) n).mp hn)
    rw [hKD_bot] at h
    have hbot : Nat.card ↥((⊥ : Subgroup H)) = 1 := by simp
    have hsupE : (S0 ⊔ S1) ⊔ D = E := hE_eq_sup.symm
    rw [hbot, mul_one, hsupE, hEcard, hD_card] at h
    have htpos : 0 < t := by omega
    have h' : s * s * t = Nat.card ↥(S0 ⊔ S1) * t := by
      rw [← h]; ring
    exact (Nat.eq_of_mul_eq_mul_right htpos h').symm
  have hS0_inter_S1 : S0 ⊓ S1 = ⊥ := by
    rw [eq_bot_iff]
    intro θ hθ
    have h1' : θ ∈ S0 := (Subgroup.mem_inf.mp hθ).1
    have h2' : θ ∈ S1 := (Subgroup.mem_inf.mp hθ).2
    have hD : θ ∈ D := Subgroup.mem_inf.mpr ⟨hS0_le_S0s h1', hS1_le_S1s h2'⟩
    have h' : θ ∈ S0 ⊓ D := Subgroup.mem_inf.mpr ⟨h1', hD⟩
    rw [hS0_inter_D] at h'
    exact h'
  have hS0S1_prod_card : ((S0 : Set H) * (S1 : Set H)).ncard = s * s := by
    rw [set_mul_ncard_of_inf_eq_bot hS0_inter_S1, hS0_card, hS1_card]
  have hS1S0_prod_card : ((S1 : Set H) * (S0 : Set H)).ncard = s * s := by
    rw [set_mul_ncard_of_inf_eq_bot (by rw [inf_comm]; exact hS0_inter_S1), hS1_card, hS0_card]
  have hS0S1_subset : ((S0 : Set H) * (S1 : Set H)) ⊆ (S0 ⊔ S1 : Subgroup H) := by
    intro x hx
    rcases hx with ⟨a, ha, b, hb, rfl⟩
    exact (S0 ⊔ S1).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
  have hS1S0_subset : ((S1 : Set H) * (S0 : Set H)) ⊆ (S0 ⊔ S1 : Subgroup H) := by
    intro x hx
    rcases hx with ⟨a, ha, b, hb, rfl⟩
    exact (S0 ⊔ S1).mul_mem (Subgroup.mem_sup_right ha) (Subgroup.mem_sup_left hb)
  haveI hSup01Fin : Fintype ↥(S0 ⊔ S1) :=
    Fintype.ofInjective
      (fun g : ↥(S0 ⊔ S1) => (⟨(g : H), (sup_le hS0_le_E hS1_le_E) g.2⟩ : ↥E))
      (by intro a b hab; apply Subtype.ext; exact congrArg (fun z : ↥E => (z : H)) hab)
  have hS0S1_eq : ((S0 : Set H) * (S1 : Set H)) = (S0 ⊔ S1 : Subgroup H) := by
    refine Set.eq_of_subset_of_ncard_le hS0S1_subset ?_ (Set.toFinite _)
    rw [hS0S1_prod_card]
    show Nat.card ↥(S0 ⊔ S1) ≤ s * s
    rw [hK_card]
  have hS1S0_eq : ((S1 : Set H) * (S0 : Set H)) = (S0 ⊔ S1 : Subgroup H) := by
    refine Set.eq_of_subset_of_ncard_le hS1S0_subset ?_ (Set.toFinite _)
    rw [hS1S0_prod_card]
    show Nat.card ↥(S0 ⊔ S1) ≤ s * s
    rw [hK_card]
  have hprod_comm : ((S1 : Set H) * (S0 : Set H)) = ((S0 : Set H) * (S1 : Set H)) :=
    hS1S0_eq.trans hS0S1_eq.symm
  exact noSpansTwoSpanContradiction hP c hdeg hs2 h2 hL0 hL1 hL10' hcL1 hz0L0 hz0M0 hM0ne
    hz1L1 hz1M1 hM1ne hyM0 hyM1 hM01 hM1L0 hM0L1 hL1M0_4 E hE_fixL0 hE_fixL1
    hS0_inter_S1 hS0_card hS1_card hprod_comm

end CFSG.Geometry.GeneralizedQuadrangles
