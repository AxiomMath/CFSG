module

public import CFSG.GH74.Generic.S1.LayerPair
public import CFSG.GH74.Generic.S1.TYCore
public import CFSG.GH74.Generic.S1.TLarge
public import CFSG.GH74.Generic.S1.TPairFacts

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 Subgroup CFSG.GH74.Generic CFSG.LocalCores CFSG.Assembly.LowTwoRank
open scoped commutatorElement

structure SymPairData {G : Type} [Group G] (X : Fin 5 → G) (c : G) : Prop where
  hc4 : X 4 ∈ centralizer ({c} : Set G)
  hc1 : X 1 ∈ centralizer ({c} : Set G)
  j1 : CFSG.GH74.GLS.IsPCompIn 2 (centralizer ({X 4} : Set G) ⊓ centralizer ({c} : Set G)) (symJ X 1)
  j3_4 : CFSG.GH74.GLS.IsPCompIn 2 (centralizer ({X 4} : Set G) ⊓ centralizer ({c} : Set G)) (symJ X 3)
  j0 : CFSG.GH74.GLS.IsPCompIn 2 (centralizer ({X 1} : Set G) ⊓ centralizer ({c} : Set G)) (symJ X 0)
  j3_1 : CFSG.GH74.GLS.IsPCompIn 2 (centralizer ({X 1} : Set G) ⊓ centralizer ({c} : Set G)) (symJ X 3)
  xy4 : ∃ y ∈ symJ X 1, X 4 = y * c
  xy1 : ∃ y ∈ symJ X 0, X 1 = y * c
  j1_norm : ∀ d ∈ centralizer ({X 4} : Set G) ⊓ centralizer ({c} : Set G), ∀ u ∈ symJ X 1,
    d * u * d⁻¹ ∈ symJ X 1

section Generic

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] {S : Subgroup (GL (Fin 4) F)}

variable (ops : BlockOps F S) (hpf : PairFacts ops)
  (hblkq : ∀ a b : Fin 4, a ≠ b → IsQuasisimple ↥(ops.blk a b))
  (X : Fin 5 → G) (D : ∀ e, LayerData (X e) S)
  (hw : ∀ e j, X (e.succAbove j) ∈ centralizer ({X e} : Set G))
  (hact : ∀ e j, ActsAsReflOn (D e).iso (barOf (hw e j)) (reflDiag F j))

include hpf hblkq hact

theorem symPairs_isPCompIn {c : G} (hcJ : c ∈ symJ X 3) (hc2 : c * c = 1) (hc1 : c ≠ 1)
    (hcc : ∀ a ∈ symJ X 3, a * c = c * a) :
    (CFSG.GH74.GLS.IsPCompIn 2 (centralizer ({X 4} : Set G) ⊓ centralizer ({c} : Set G)) (symJ X 1) ∧
      CFSG.GH74.GLS.IsPCompIn 2 (centralizer ({X 4} : Set G) ⊓ centralizer ({c} : Set G))
        (symJ X 3)) ∧
    (CFSG.GH74.GLS.IsPCompIn 2 (centralizer ({X 1} : Set G) ⊓ centralizer ({c} : Set G)) (symJ X 0) ∧
      CFSG.GH74.GLS.IsPCompIn 2 (centralizer ({X 1} : Set G) ⊓ centralizer ({c} : Set G))
        (symJ X 3)) := by
  have hJ3 := symJ_three ops X D hw hact
  have h4a : symJ X 1 = (ops.blk 0 1).map (D 4).ι := symJ_one ops X D hw hact
  have h4b : symJ X 3 = (ops.blk 2 3).map (D 4).ι := hJ3
  have h1a : symJ X 0 = (ops.blk 3 0).map (D 1).ι :=
    pairRes_eq_map' ops X D hw hact 1 (a := 3) (b := 0) (c := 1) (d := 2) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h1b : symJ X 3 = (ops.blk 1 2).map (D 1).ι :=
    pairRes_eq_map' ops X D hw hact 1 (a := 1) (b := 2) (c := 3) (d := 0) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  constructor
  ·
    have hcJ' := hcJ
    rw [h4b] at hcJ'
    obtain ⟨z0, hz0, rfl⟩ := hcJ'
    have hz0sq : z0 * z0 = 1 := (D 4).ι_injective (by rw [map_mul, map_one]; exact hc2)
    have hz01 : z0 ≠ 1 := fun h => hc1 (by rw [h, map_one])
    have hcent : ∀ g ∈ ops.blk 2 3, g * z0 = z0 * g := fun g hg =>
      (D 4).ι_injective (by
        rw [map_mul, map_mul]
        exact hcc _ (by rw [h4b]; exact ⟨g, hg, rfl⟩))
    have := layerPair_isPCompIn ops hpf hblkq (D 4) (a := 0) (b := 1) (c := 2) (d := 3)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hz0 hz0sq hz01 hcent
    rw [h4a, h4b]
    exact this
  ·
    have hcJ' := hcJ
    rw [h1b] at hcJ'
    obtain ⟨z0, hz0, rfl⟩ := hcJ'
    have hz0sq : z0 * z0 = 1 := (D 1).ι_injective (by rw [map_mul, map_one]; exact hc2)
    have hz01 : z0 ≠ 1 := fun h => hc1 (by rw [h, map_one])
    have hcent : ∀ g ∈ ops.blk 1 2, g * z0 = z0 * g := fun g hg =>
      (D 1).ι_injective (by
        rw [map_mul, map_mul]
        exact hcc _ (by rw [h1b]; exact ⟨g, hg, rfl⟩))
    have := layerPair_isPCompIn ops hpf hblkq (D 1) (a := 3) (b := 0) (c := 1) (d := 2)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hz0 hz0sq hz01 hcent
    rw [h1a, h1b]
    exact this


theorem symPairs_j1_norm {c : G} (hcJ : c ∈ symJ X 3) (hc2 : c * c = 1) (hc1 : c ≠ 1)
    (hcc : ∀ a ∈ symJ X 3, a * c = c * a) :
    ∀ d ∈ centralizer ({X 4} : Set G) ⊓ centralizer ({c} : Set G), ∀ u ∈ symJ X 1,
      d * u * d⁻¹ ∈ symJ X 1 := by
  have hJ3 := symJ_three ops X D hw hact
  have h4a : symJ X 1 = (ops.blk 0 1).map (D 4).ι := symJ_one ops X D hw hact
  have h4b : symJ X 3 = (ops.blk 2 3).map (D 4).ι := hJ3
  have hcJ' := hcJ
  rw [h4b] at hcJ'
  obtain ⟨z0, hz0, rfl⟩ := hcJ'
  have hz0sq : z0 * z0 = 1 := (D 4).ι_injective (by rw [map_mul, map_one]; exact hc2)
  have hz01 : z0 ≠ 1 := fun h => hc1 (by rw [h, map_one])
  have hcent : ∀ g ∈ ops.blk 2 3, g * z0 = z0 * g := fun g hg =>
    (D 4).ι_injective (by
      rw [map_mul, map_mul]
      exact hcc _ (by rw [h4b]; exact ⟨g, hg, rfl⟩))
  have hnorm := layerPair_normal ops hpf hblkq (D 4) (a := 0) (b := 1) (c := 2) (d := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hz0 hz0sq hz01 hcent
  intro d hd u hu
  rw [h4a] at hu ⊢
  have h1 := (hnorm d hd).1
  have : d * u * d⁻¹ ∈ ((ops.blk 0 1).map (D 4).ι).map (MulAut.conj d).toMonoidHom :=
    ⟨u, hu, by simp [MulAut.conj_apply]⟩
  rwa [h1] at this

omit hpf hblkq hact in
theorem symX_mem_centralizer_of_mem_symJ_three {c : G} (e : Fin 5) {s : ↥S}
    (hs : (D e).ι s = c) : X e ∈ centralizer ({c} : Set G) := by
  rw [mem_centralizer_singleton_iff, ← hs]
  exact ((D e).ι_comm_self s).symm

theorem symPairs_data (hX2 : ∀ e, orderOf (X e) = 2) (hxK : ∀ e, xbar (X e) ∈ (D e).K) {c : G}
    (hcJ : c ∈ symJ X 3) (hc2 : c * c = 1) (hc1 : c ≠ 1)
    (hcc : ∀ a ∈ symJ X 3, a * c = c * a) : SymPairData X c := by
  obtain ⟨⟨h41, h43⟩, ⟨h10, h13⟩⟩ := symPairs_isPCompIn ops hpf hblkq X D hw hact hcJ hc2 hc1 hcc
  have hJ3 := symJ_three ops X D hw hact
  have hcJ' := hcJ
  rw [hJ3] at hcJ'
  obtain ⟨z0, hz0m, hz0⟩ := hcJ'
  have h1b : symJ X 3 = (ops.blk 1 2).map (D 1).ι :=
    pairRes_eq_map' ops X D hw hact 1 (a := 1) (b := 2) (c := 3) (d := 0) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h1a : symJ X 0 = (ops.blk 3 0).map (D 1).ι :=
    pairRes_eq_map' ops X D hw hact 1 (a := 3) (b := 0) (c := 1) (d := 2) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hcJ1 := hcJ
  rw [h1b] at hcJ1
  obtain ⟨z1, hz1m, hz1⟩ := hcJ1
  have hz0sq : z0 * z0 = 1 := (D 4).ι_injective (by rw [map_mul, map_one, hz0]; exact hc2)
  have hz01 : z0 ≠ 1 := fun h => hc1 (by rw [← hz0, h, map_one])
  have hz1sq : z1 * z1 = 1 := (D 1).ι_injective (by rw [map_mul, map_one, hz1]; exact hc2)
  have hz11 : z1 ≠ 1 := fun h => hc1 (by rw [← hz1, h, map_one])
  refine ⟨symX_mem_centralizer_of_mem_symJ_three X D 4 hz0,
    symX_mem_centralizer_of_mem_symJ_three X D 1 hz1, h41, h43, h10, h13, ?_, ?_,
    symPairs_j1_norm ops hpf hblkq X D hw hact hcJ hc2 hc1 hcc⟩
  ·
    obtain ⟨s, hsc, hs2, hs1, hsx⟩ := exists_center_involution_of_layer (hX2 4) (D 4) (hxK 4)
    have hsz : s * z0 ∈ ops.blk 0 1 :=
      hpf.neg_mul 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        s hsc hs2 hs1 z0 hz0m hz0sq hz01
    refine ⟨(D 4).ι (s * z0), ?_, ?_⟩
    · rw [symJ_one ops X D hw hact]
      exact ⟨s * z0, hsz, rfl⟩
    · rw [map_mul, hsx, hz0, mul_assoc, hc2, mul_one]
  ·
    obtain ⟨s, hsc, hs2, hs1, hsx⟩ := exists_center_involution_of_layer (hX2 1) (D 1) (hxK 1)
    have hsz : s * z1 ∈ ops.blk 3 0 :=
      hpf.neg_mul 3 0 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        s hsc hs2 hs1 z1 hz1m hz1sq hz11
    refine ⟨(D 1).ι (s * z1), ?_, ?_⟩
    · rw [h1a]
      exact ⟨s * z1, hsz, rfl⟩
    · rw [map_mul, hsx, hz1, mul_assoc, hc2, mul_one]



end Generic

section FromData

variable {G : Type} [Group G] [Finite G]

theorem SymPairData.barSub_le_layer {X : Fin 5 → G} {c : G} (hX2 : ∀ e, orderOf (X e) = 2)
    (h : SymPairData X c) :
    S45.barSub c (symJ X 0) ≤ layer (CentralizerBar c) ∧
      S45.barSub c (symJ X 1) ≤ layer (CentralizerBar c) ∧
      S45.barSub c (symJ X 3) ≤ layer (CentralizerBar c) :=
  ⟨barSub_le_layer_of_isPCompIn (hX2 1) h.hc1 h.j0, barSub_le_layer_of_isPCompIn (hX2 4) h.hc4 h.j1,
    barSub_le_layer_of_isPCompIn (hX2 4) h.hc4 h.j3_4⟩

end FromData


section Frame

variable {G : Type} [Group G] [Finite G]

theorem linBlk_quasisimple {F : Type} [Field F] [Finite F] (hF : Nat.card F % 4 = 3)
    (h4 : 3 < Nat.card F) : ∀ a b : Fin 4, a ≠ b → IsQuasisimple ↥((linBlockOps hF h4).blk a b) := by
  intro a b hab
  obtain ⟨c, d, hac, had, hbc, hbd, hcd⟩ := exists_two_more a b hab
  obtain ⟨W, hW⟩ := lin_std hF h4 a b c hab hac hbc
  exact (lin_pair_UV_quasisimple h4 hW).1

theorem uniBlk_quasisimple {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2)
    (hq : q % 4 = 1) : ∀ a b : Fin 4, a ≠ b → IsQuasisimple ↥((uniBlockOps hF hq).blk a b) := by
  obtain ⟨p, f, h, rfl, hp2⟩ := FrameUni.exists_unitaryFieldData hF hq
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP F p := h.charP
  have hq5 : 5 ≤ p ^ f := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    rw [hF] at h1
    have hq1 : 1 < p ^ f := by
      by_contra hle
      have hle' : p ^ f ≤ 1 := by omega
      interval_cases hpf : p ^ f <;> simp at h1
    omega
  intro a b hab
  obtain ⟨c, d, hac, had, hbc, hbd, hcd⟩ := exists_two_more a b hab
  obtain ⟨W, hW⟩ := uni_std hF hq rfl a b c hab hac hbc
  exact (uni_pair_UV_quasisimple hF hq5 hW).1

theorem sym_pairData (hExact : S1LiftExactProp) {x : G} {K : Subgroup (CentralizerBar x)}
    (hset : S1Setup G x K) (hfront : S1Front G x K) (hbigK : S1LargeModel K) {u : Fin 4 → G}
    {hu : ∀ i, u i ∈ centralizer ({x} : Set G)} (hf : S1Frame x K u hu) (hsym : S1SymFrame x u)
    {c : G} (hcJ : c ∈ symJ (symX x u) 3) (hc2 : orderOf c = 2)
    (hcc : ∀ a ∈ symJ (symX x u) 3, a * c = c * a) : SymPairData (symX x u) c := by
  obtain ⟨hXconj, -, hXc, -, -⟩ := symX_facts hset.shape.2 hset.inv hf
  have hX2 : ∀ e, orderOf (symX x u e) = 2 := fun e =>
    (IsConj.orderOf_eq (hXconj e)).symm.trans hset.inv
  have hw : ∀ e j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G) := fun e j =>
    mem_centralizer_singleton_iff.2 (hXc _ _)
  have hc2' : c * c = 1 := by rw [← sq, ← hc2]; exact pow_orderOf_eq_one c
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hc2
    exact absurd hc2 (by norm_num)
  rcases id hsym with ⟨F, _, _, hF, hlin⟩ | ⟨q, F, _, _, hF, hq, huni⟩
  · have h4 : 3 < Nat.card F := three_lt_card_of_largeModel hbigK hF (sym_model_four hfront hlin)
    have hloc : ∀ e : Fin 5, ∃ (K' : Subgroup (CentralizerBar (symX x u e)))
        (hw' : ∀ j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G)),
          S1Setup G (symX x u e) K' ∧ S1Front G (symX x u e) K' ∧
          ∃ e' : ↥K' ≃* ↥(StatedSL 4 F), ∀ j, ActsAsReflOn e' (barOf (hw' j)) (reflDiag F j) := by
      intro e
      obtain ⟨K', hw', hset', hfront', -, e', he'⟩ := hlin e
      exact ⟨K', hw', hset', hfront', e', he'⟩
    choose D hDK hDact using sym_layerData hExact x u hw hloc
    have hxK : ∀ e, xbar (symX x u e) ∈ (D e).K := by
      intro e
      obtain ⟨K', -, hset', hfront', -⟩ := hloc e
      rw [hDK e, hfront'.layer_eq]
      exact hset'.shape.2
    exact symPairs_data (linBlockOps hF h4) (linPairFacts hF h4) (linBlk_quasisimple hF h4)
      (symX x u) D hw hDact hX2 hxK hcJ hc2' hc1 hcc
  · have hloc : ∀ e : Fin 5, ∃ (K' : Subgroup (CentralizerBar (symX x u e)))
        (hw' : ∀ j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G)),
          S1Setup G (symX x u e) K' ∧ S1Front G (symX x u e) K' ∧
          ∃ e' : ↥K' ≃* ↥(StatedSU 4 q F), ∀ j, ActsAsReflOn e' (barOf (hw' j)) (reflDiag F j) := by
      intro e
      obtain ⟨K', hw', hset', hfront', -, e', he'⟩ := huni e
      exact ⟨K', hw', hset', hfront', e', he'⟩
    choose D hDK hDact using sym_layerData hExact x u hw hloc
    have hxK : ∀ e, xbar (symX x u e) ∈ (D e).K := by
      intro e
      obtain ⟨K', -, hset', hfront', -⟩ := hloc e
      rw [hDK e, hfront'.layer_eq]
      exact hset'.shape.2
    exact symPairs_data (uniBlockOps hF hq) (uniPairFacts hF hq) (uniBlk_quasisimple hF hq)
      (symX x u) D hw hDact hX2 hxK hcJ hc2' hc1 hcc

theorem sym_barSub_le_layer (hExact : S1LiftExactProp) {x : G} {K : Subgroup (CentralizerBar x)}
    (hset : S1Setup G x K) (hfront : S1Front G x K) (hbigK : S1LargeModel K) {u : Fin 4 → G}
    {hu : ∀ i, u i ∈ centralizer ({x} : Set G)} (hf : S1Frame x K u hu) (hsym : S1SymFrame x u)
    {c : G} (hcJ : c ∈ symJ (symX x u) 3) (hc2 : orderOf c = 2)
    (hcc : ∀ a ∈ symJ (symX x u) 3, a * c = c * a) :
    S45.barSub c (symJ (symX x u) 0) ≤ layer (CentralizerBar c) ∧
      S45.barSub c (symJ (symX x u) 1) ≤ layer (CentralizerBar c) ∧
      S45.barSub c (symJ (symX x u) 3) ≤ layer (CentralizerBar c) := by
  obtain ⟨hXconj, -, -, -, -⟩ := symX_facts hset.shape.2 hset.inv hf
  have hX2 : ∀ e, orderOf (symX x u e) = 2 := fun e =>
    (IsConj.orderOf_eq (hXconj e)).symm.trans hset.inv
  exact (sym_pairData hExact hset hfront hbigK hf hsym hcJ hc2 hcc).barSub_le_layer hX2

end Frame

end CFSG.GH74.Generic.S1
