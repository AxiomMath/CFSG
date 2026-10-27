module

public import CFSG.GH74.QTGen4.DSGen4.LeafWrappers

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

private theorem dsj1_le_normalizer_of_conj_mem {G : Type} [Group G] {H X : Subgroup G}
    (h : ∀ g ∈ H, ∀ x ∈ X, g * x * g⁻¹ ∈ X) : H ≤ Subgroup.normalizer (X : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h g hg x hx, fun hx => ?_⟩
  have := h g⁻¹ (H.inv_mem hg) (g * x * g⁻¹) hx
  simpa [mul_assoc] using this

private theorem dsj1_mem_centerOf_iff {G : Type} [Group G] {X : Subgroup G} {x : G} :
    x ∈ centerOf X ↔ x ∈ X ∧ ∀ y ∈ X, y * x = x * y := by
  simp only [centerOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe]

private theorem dsj1_le_normalizer_centerOf {G : Type} [Group G] {H X : Subgroup G}
    (h : H ≤ Subgroup.normalizer (X : Set G)) :
    H ≤ Subgroup.normalizer ((centerOf X : Subgroup G) : Set G) := by
  refine dsj1_le_normalizer_of_conj_mem fun g hg x hx => ?_
  obtain ⟨hxX, hxc⟩ := dsj1_mem_centerOf_iff.mp hx
  refine dsj1_mem_centerOf_iff.mpr
    ⟨(Subgroup.mem_normalizer_iff.mp (h hg) x).mp hxX, fun y hy => ?_⟩
  have hy' : g⁻¹ * y * g ∈ X := by
    have := (Subgroup.mem_normalizer_iff.mp (h (H.inv_mem hg)) y).mp hy
    simpa using this
  calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [hxc _ hy']
    _ = g * x * g⁻¹ * y := by group

private theorem dsj1_le_centralizer_of_card_two {G : Type} [Group G] {H N : Subgroup G}
    (hN : Nat.card N = 2) (hH : H ≤ Subgroup.normalizer (N : Set G)) :
    N ≤ Subgroup.centralizer (H : Set G) := by
  obtain ⟨⟨w, hw⟩, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥N)).mp hN
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hc : h * z * h⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hH hh) z).mp hz
  by_cases hz1 : z = 1
  · subst hz1
    simp
  · have hzw : (⟨z, hz⟩ : ↥N) = ⟨w, hw⟩ :=
      huniq _ (fun e => hz1 (congrArg Subtype.val e))
    have hcN : (⟨h * z * h⁻¹, hc⟩ : ↥N) ≠ 1 := by
      intro e
      apply hz1
      have e' : h * z * h⁻¹ = 1 := congrArg Subtype.val e
      calc z = h⁻¹ * (h * z * h⁻¹) * h := by group
        _ = 1 := by rw [e']; group
    have hcw : (⟨h * z * h⁻¹, hc⟩ : ↥N) = ⟨w, hw⟩ := huniq _ hcN
    have h1 : h * z * h⁻¹ = w := congrArg Subtype.val hcw
    have h2 : z = w := congrArg Subtype.val hzw
    calc h * z = (h * z * h⁻¹) * h := by group
      _ = z * h := by rw [h1, h2]

private theorem dsj1_le_of_sup_dsFrattini_eq {G : Type} [Group G] [Finite G] {Q M : Subgroup G}
    (hM : M ≤ Q) (h : M ⊔ dsFrattini Q = Q) : Q ≤ M := by
  have hA : M.subgroupOf Q ⊔ frattini ↥Q = ⊤ := by
    apply Subgroup.map_injective (f := Q.subtype) Q.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hM,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact h
  have hAtop : M.subgroupOf Q = ⊤ := frattini_nongenerating hA
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥Q) ∈ M.subgroupOf Q := by
    rw [hAtop]
    exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp hmem

theorem leafDSBJQ1 [DSLeaf LeafDSBJV1] [DSLeaf LeafDSBJZ2] [DSLeaf LeafDSBA5Vertex]
    [DSLeaf LeafFrattiniChief] [DSLeaf LeafM6] [DSLeaf LeafM8a] [DSLeaf LeafM8b]
    [DSLeaf LeafSylowS] : LeafDSBJQ1 := by
  intro G _ _ L1 L2 S h cJ
  obtain ⟨hZc, hA, hNS, hcomm, hVQ⟩ := dsbjv1 h cJ
  have hQL1 : dsQ L1 L2 S ≤ L1 := (dsba5_vertex h).2.2
  have hA5 : A5Par L1 (L1 ⊔ bigB L1 L2 S) := A5Par.of_hyp111R Finite4.gen4 h.hyp h.ns1
  have hF : A5Chief (L1 ⊔ bigB L1 L2 S) L1 (dsQ L1 L2 S) (dsFrattini (dsQ L1 L2 S)) :=
    frattini_chief hA5
  have hNV : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer ((dsV1 L1 L2 S : Subgroup G) : Set G) :=
    hA.norm_E
  have hNZ : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer ((dsZ S : Subgroup G) : Set G) :=
    hA.norm_K
  have hZV : dsZ S ≤ dsV1 L1 L2 S := hA.sec.1
  have hVN : dsV1 L1 L2 S ≤ Subgroup.normalizer ((dsZ S : Subgroup G) : Set G) :=
    hA.E_le.trans hNZ
  have hΦQ : dsFrattini (dsQ L1 L2 S) ≤ dsQ L1 L2 S := Subgroup.map_subtype_le _
  have hQP : dsQ L1 L2 S ≤ L1 ⊔ bigB L1 L2 S := Subgroup.map_subtype_le _
  have hZne : dsZ S ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hZc
    omega
  have hVne : ⁅dsV1 L1 L2 S, dsV1 L1 L2 S⁆ ≠ ⊥ := by
    rw [hcomm]
    exact hZne
  have hZcen : dsZ S ≤ Subgroup.centralizer (dsV1 L1 L2 S : Set G) :=
    dsj1_le_centralizer_of_card_two hZc hVN
  have hcV : centerOf (dsV1 L1 L2 S) ≤ dsV1 L1 L2 S := fun x hx =>
    (dsj1_mem_centerOf_iff.mp hx).1
  have hcZ : centerOf (dsV1 L1 L2 S) ≤ dsZ S := by
    have hZc' : dsZ S ≤ centerOf (dsV1 L1 L2 S) := fun z hz =>
      dsj1_mem_centerOf_iff.mpr
        ⟨hZV hz, fun y hy => Subgroup.mem_centralizer_iff.mp (hZcen hz) y hy⟩
    have hsup : L1 ⊔ bigB L1 L2 S ≤
        Subgroup.normalizer ((centerOf (dsV1 L1 L2 S) ⊔ dsZ S : Subgroup G) : Set G) :=
      F1.le_normalizer_sup (dsj1_le_normalizer_centerOf hNV) hNZ
    rcases hA.irred (centerOf (dsV1 L1 L2 S) ⊔ dsZ S) le_sup_right (sup_le hcV hZV) hsup with
      hX | hX
    · exact le_trans le_sup_left hX.le
    · exfalso
      have hceq : centerOf (dsV1 L1 L2 S) = dsV1 L1 L2 S :=
        (sup_eq_left.mpr hZc').symm.trans hX
      have hVc : dsV1 L1 L2 S ≤ Subgroup.centralizer (dsV1 L1 L2 S : Set G) := fun x hx => by
        have hx' : x ∈ centerOf (dsV1 L1 L2 S) := by
          rw [hceq]
          exact hx
        exact Subgroup.mem_centralizer_iff.mpr (dsj1_mem_centerOf_iff.mp hx').2
      exact hZne (hcomm.symm.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hVc))
  have hVcard : Nat.card (dsV1 L1 L2 S) = 32 := by
    have h1 := Subgroup.relIndex_mul_card (H := dsZ S) (K := dsV1 L1 L2 S)
    rw [inf_eq_left.mpr hZV, hA.card, hZc] at h1
    omega
  have hn : Nat.card {x : ↥(dsV1 L1 L2 S) | x ^ 2 = 1} = 12 := m6 hA hNS hZc hVne
  have hQdec : ∀ q ∈ dsQ L1 L2 S,
      q ∈ (dsQ L1 L2 S ⊓ Subgroup.centralizer (dsV1 L1 L2 S : Set G)) ⊔ dsV1 L1 L2 S := by
    intro q hq
    obtain ⟨v, hv, hc⟩ :=
      m8a hA.sec hZc hcomm hcZ q (hNV (hQP hq)) (fun x hx => hA.core q hq x hx)
    have hcC : q * v⁻¹ ∈ dsQ L1 L2 S ⊓ Subgroup.centralizer (dsV1 L1 L2 S : Set G) :=
      Subgroup.mem_inf.mpr ⟨(dsQ L1 L2 S).mul_mem hq ((dsQ L1 L2 S).inv_mem (hVQ hv)), hc⟩
    have e : q = q * v⁻¹ * v := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left hcC) (Subgroup.mem_sup_right hv)
  have hPX : L1 ⊔ bigB L1 L2 S ≤
      Subgroup.normalizer ((dsV1 L1 L2 S ⊔ dsFrattini (dsQ L1 L2 S) : Subgroup G) : Set G) :=
    F1.le_normalizer_sup hNV hF.norm_K
  have hQV : dsQ L1 L2 S = dsV1 L1 L2 S := by
    rcases hF.irred (dsV1 L1 L2 S ⊔ dsFrattini (dsQ L1 L2 S)) le_sup_right
        (sup_le hVQ hΦQ) hPX with hX | hX
    · exfalso
      have hVΦ : dsV1 L1 L2 S ≤ dsFrattini (dsQ L1 L2 S) := le_trans le_sup_left hX.le
      have hCΦ : (dsQ L1 L2 S ⊓ Subgroup.centralizer (dsV1 L1 L2 S : Set G)) ⊔
          dsFrattini (dsQ L1 L2 S) = dsQ L1 L2 S := by
        apply le_antisymm
        · exact sup_le inf_le_left hΦQ
        · intro q hq
          exact sup_le_sup_left hVΦ _ (hQdec q hq)
      have hQC := dsj1_le_of_sup_dsFrattini_eq inf_le_left hCΦ
      have hVc : dsV1 L1 L2 S ≤ Subgroup.centralizer (dsV1 L1 L2 S : Set G) := fun v hv =>
        (Subgroup.mem_inf.mp (hQC (hVQ hv))).2
      exact hZne (hcomm.symm.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hVc))
    · exact (le_antisymm hVQ (dsj1_le_of_sup_dsFrattini_eq hVQ hX)).symm
  have hO2 : pCoreOf 2 L1 = dsQ L1 L2 S :=
    (F1.inf_pCoreOf_parabolic_eq h.hyp).symm.trans (inf_eq_left.mpr hQL1)
  refine ⟨hQV, hO2, ?_⟩
  rw [hO2, hQV]
  exact m8b hA.sec hZc hcomm hcZ hVcard hn

end CFSG.GH74.QTGen4.DSGen4
