module

public import CFSG.GH74.Generic.S1.TPairFacts
public import CFSG.GH74.Generic.S1.TDualUni
public import CFSG.GH74.Generic.S1.TYClause

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan CFSG.LocalCores
open scoped MatrixGroups commutatorElement

@[expose] def S1LeafAHigh : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    S1Front G x K → S1LargeModel K → ∀ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)),
      S1Frame x K u hu → S1SymFrame x u →
        ∀ c ∈ symJ (symX x u) 3, orderOf c = 2 → (∀ a ∈ symJ (symX x u) 3, a * c = c * a) →
          layer ↥(centralizer ({c} : Set G)) =
            ((symJ (symX x u) 0 ⊔ symJ (symX x u) 1) ⊔ symJ (symX x u) 3).subgroupOf
              (centralizer ({c} : Set G))

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem no_central_involution_subgroupOf {L S : Subgroup G} (hLS : L ≤ S)
    (hLc : ∀ z ∈ L, (∀ w ∈ L, z * w = w * z) → Odd (orderOf z)) :
    ∀ z ∈ L.subgroupOf S, (∀ b ∈ L.subgroupOf S, z * b = b * z) → ¬ (z * z = 1 ∧ z ≠ 1) := by
  intro z hz hzc ⟨hz2, hz1⟩
  have hzL : (z : G) ∈ L := mem_subgroupOf.1 hz
  have hodd : Odd (orderOf (z : G)) := by
    refine hLc z hzL fun w hw => ?_
    have := hzc ⟨w, hLS hw⟩ (mem_subgroupOf.2 hw)
    exact congrArg Subtype.val this
  have hz2' : (z : G) * (z : G) = 1 := congrArg Subtype.val hz2
  have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : orderOf (z : G) = 2 := orderOf_eq_prime (by rw [sq]; exact hz2') hz1'
  rw [h2] at hodd
  exact absurd hodd (by decide)

omit [Finite G] in
theorem normalizer_of_subgroupOf_normal {L S : Subgroup G} (hLS : L ≤ S)
    (hnorm : (L.subgroupOf S).Normal) : S ≤ normalizer (L : Set G) := by
  intro n hn
  rw [mem_normalizer_iff]
  intro g
  have hn' : n⁻¹ ∈ S := S.inv_mem hn
  constructor
  · intro hg
    have hgS : g ∈ S := hLS hg
    have := hnorm.conj_mem ⟨g, hgS⟩ (mem_subgroupOf.2 hg) ⟨n, hn⟩
    exact mem_subgroupOf.1 this
  · intro hg
    have hgS : n * g * n⁻¹ ∈ S := hLS hg
    have := hnorm.conj_mem ⟨n * g * n⁻¹, hgS⟩ (mem_subgroupOf.2 hg) ⟨n⁻¹, hn'⟩
    have h2 := mem_subgroupOf.1 this
    simpa [mul_assoc] using h2

omit [Finite G] in
theorem sup_comm_three {J : Fin 4 → Subgroup G}
    (hcomm : ∀ i j : Fin 4, (i : ℕ) + 1 < j → ∀ a ∈ J i, ∀ b ∈ J j, a * b = b * a) :
    ∀ a ∈ J 0 ⊔ J 1, ∀ b ∈ J 3, a * b = b * a := by
  intro a ha b hb
  have h : J 0 ⊔ J 1 ≤ centralizer (J 3 : Set G) :=
    sup_le (fun a ha => mem_centralizer_iff.2 fun b hb => (hcomm 0 3 (by decide) a ha b hb).symm)
      (fun a ha => mem_centralizer_iff.2 fun b hb => (hcomm 1 3 (by decide) a ha b hb).symm)
  exact ((mem_centralizer_iff.1 (h ha)) b hb).symm

theorem sym_a4_lin (hExact : S1LiftExactProp) {x : G} {K : Subgroup (CentralizerBar x)}
    (hset : S1Setup G x K) {u : Fin 4 → G} {hu : ∀ i, u i ∈ centralizer ({x} : Set G)}
    (hf : S1Frame x K u hu) {F : Type} [Field F] [Finite F] (hF : Nat.card F % 4 = 3)
    (h4 : 3 < Nat.card F) (hlin : S1SymFrameLin x u F) :
    WeakCTA4 F (symJ (symX x u)) ∧ ∃ q8 : QuaternionGroup 2 →* G, Function.Injective q8 ∧
      ∀ g, q8 g ∈ symJ (symX x u) 1 := by
  obtain ⟨-, -, hXc, -, -⟩ := symX_facts hset.shape.2 hset.inv hf
  have hw : ∀ e j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G) := fun e j =>
    mem_centralizer_singleton_iff.2 (hXc _ _)
  have hloc : ∀ e : Fin 5, ∃ (K' : Subgroup (CentralizerBar (symX x u e)))
      (hw' : ∀ j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G)),
        S1Setup G (symX x u e) K' ∧ S1Front G (symX x u e) K' ∧
        ∃ e' : ↥K' ≃* ↥(StatedSL 4 F), ∀ j, ActsAsReflOn e' (barOf (hw' j)) (reflDiag F j) := by
    intro e
    obtain ⟨K', hw', hset', hfront', -, e', he'⟩ := hlin e
    exact ⟨K', hw', hset', hfront', e', he'⟩
  choose D hDK hDact using sym_layerData hExact x u hw hloc
  have hstd := fun a b c hab hac hbc => lin_std hF h4 a b c hab hac hbc
  have hchain := lin_chain hF h4
  have hcen := lin_blk_center hF h4
  obtain ⟨hcomm, hpair, -, -⟩ :=
    symSystem (linBlockOps hF h4) (symX x u) D hw hDact (linKind F) hstd hchain hcen
  refine ⟨⟨hcomm, hpair⟩, ?_⟩
  obtain ⟨q8, hq8, hq8blk⟩ := exists_q8_blkLin hF (c := 0) (d := 1) (by decide)
  refine ⟨(D 4).ι.comp q8, (D 4).ι_injective.comp hq8, fun g => ?_⟩
  rw [symJ_one (linBlockOps hF h4) (symX x u) D hw hDact]
  exact ⟨q8 g, hq8blk g, rfl⟩

theorem sym_a4_uni (hExact : S1LiftExactProp) {x : G} {K : Subgroup (CentralizerBar x)}
    (hset : S1Setup G x K) {u : Fin 4 → G} {hu : ∀ i, u i ∈ centralizer ({x} : Set G)}
    (hf : S1Frame x K u hu) {q : ℕ} {F : Type} [Field F] [Finite F] (hF : Nat.card F = q ^ 2)
    (hq : q % 4 = 1) (huni : S1SymFrameUni x u q F) (p f : ℕ) [Fact p.Prime] [CharP F p]
    (hp2 : p ≠ 2) (hqpf : q = p ^ f) :
    WeakPhanA4 F p f (symJ (symX x u)) ∧ ∃ q8 : QuaternionGroup 2 →* G, Function.Injective q8 ∧
      ∀ g, q8 g ∈ symJ (symX x u) 1 := by
  subst hqpf
  obtain ⟨-, -, hXc, -, -⟩ := symX_facts hset.shape.2 hset.inv hf
  have hw : ∀ e j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G) := fun e j =>
    mem_centralizer_singleton_iff.2 (hXc _ _)
  have hloc : ∀ e : Fin 5, ∃ (K' : Subgroup (CentralizerBar (symX x u e)))
      (hw' : ∀ j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G)),
        S1Setup G (symX x u e) K' ∧ S1Front G (symX x u e) K' ∧
        ∃ e' : ↥K' ≃* ↥(StatedSU 4 (p ^ f) F), ∀ j,
          ActsAsReflOn e' (barOf (hw' j)) (reflDiag F j) := by
    intro e
    obtain ⟨K', hw', hset', hfront', -, e', he'⟩ := huni e
    exact ⟨K', hw', hset', hfront', e', he'⟩
  choose D hDK hDact using sym_layerData hExact x u hw hloc
  have hstd := fun a b c hab hac hbc => uni_std hF hq rfl a b c hab hac hbc
  have hchain := uni_chain hF hq rfl
  have hcen := uni_blk_center hF hq
  obtain ⟨hcomm, hpair, -, -⟩ :=
    symSystem (uniBlockOps hF hq) (symX x u) D hw hDact (uniKind F p f) hstd hchain hcen
  refine ⟨⟨hcomm, hpair⟩, ?_⟩
  obtain ⟨q8, hq8, hq8blk⟩ := exists_q8_uniBlk hF hp2 (c := 0) (d := 1) (by decide)
  refine ⟨(D 4).ι.comp q8, (D 4).ι_injective.comp hq8, fun g => ?_⟩
  rw [symJ_one (uniBlockOps hF hq) (symX x u) D hw hDact]
  exact ⟨q8 g, hq8blk g, rfl⟩

theorem sym_a4_q3 {x : G} {K : Subgroup (CentralizerBar x)} (hset : S1Setup G x K)
    {u : Fin 4 → G} {hu : ∀ i, u i ∈ centralizer ({x} : Set G)} (hf : S1Frame x K u hu)
    {F : Type} [Field F] [Finite F] (hF3 : Nat.card F = 3) (hlin : S1SymFrameLin x u F)
    (hodd : S1FrameOddFree x u) :
    WeakCTA4 F (symJ3 (symX x u)) ∧ ∃ q8 : QuaternionGroup 2 →* G, Function.Injective q8 ∧
      ∀ g, q8 g ∈ symJ3 (symX x u) 1 := by
  obtain ⟨-, -, hXc, -, -⟩ := symX_facts hset.shape.2 hset.inv hf
  have hw : ∀ e j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G) := fun e j =>
    mem_centralizer_singleton_iff.2 (hXc _ _)
  have hloc : ∀ e : Fin 5, ∃ (K' : Subgroup (CentralizerBar (symX x u e)))
      (hw' : ∀ j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G)),
        S1Setup G (symX x u e) K' ∧ S1Front G (symX x u e) K' ∧
        ∃ e' : ↥K' ≃* ↥(StatedSL 4 F), ∀ j, ActsAsReflOn e' (barOf (hw' j)) (reflDiag F j) := by
    intro e
    obtain ⟨K', hw', hset', hfront', -, e', he'⟩ := hlin e
    exact ⟨K', hw', hset', hfront', e', he'⟩
  choose D hDK hDact using sym_layerData3 x u hF3 hodd hw hloc
  obtain ⟨hcomm, hpair, -, -⟩ :=
    symSystem3 (linBlockOps3 hF3) (symX x u) D hw hDact (linKind F)
      (fun a b c hab hac hbc => blkLin_standardPair a b c hab hac hbc) blkLin_chain
      (lin_blk_center3 hF3)
  refine ⟨⟨hcomm, hpair⟩, ?_⟩
  obtain ⟨q8, hq8, hq8blk⟩ := exists_q8_blkLin (by rw [hF3]) (c := 0) (d := 1) (by decide)
  refine ⟨(D 4).toLayerData.ι.comp q8, (D 4).toLayerData.ι_injective.comp hq8, fun g => ?_⟩
  rw [symJ3_one (linBlockOps3 hF3) (symX x u) D hw hDact]
  exact ⟨q8 g, hq8blk g, rfl⟩

theorem layer_normal_contains (X : Type) [Group X] :
    (layer X).Normal ∧ ∀ M : Subgroup X, IsComponent M → M ≤ layer X := by
  have : (layer X).Characteristic := layer_characteristic
  exact ⟨inferInstance, fun _ hM => le_sSup hM⟩

section Gen4Permutation

variable {S : Type} [Group S] [Finite S]

theorem normal_of_component_gen4 (hS : Gen4 S) {B : Subgroup S} (hBc : IsComponent B)
    (hBodd : ∀ z ∈ B, (∀ b ∈ B, z * b = b * z) → ¬ (z * z = 1 ∧ z ≠ 1))
    (q8 : QuaternionGroup 2 →* S) (hq8 : Function.Injective q8) (hq8B : ∀ g, q8 g ∈ B)
    {c : S} (hcc : c ∈ Subgroup.center S) (hc2 : c * c = 1) (hc1 : c ≠ 1) : B.Normal := by
  classical
  refine ⟨fun n hn h => ?_⟩
  set M : Subgroup S := B.map (MulAut.conj h).toMonoidHom with hMdef
  have hMc : IsComponent M := isComponent_map_mulEquiv (MulAut.conj h) hBc
  have hnM : h * n * h⁻¹ ∈ M := ⟨n, hn, by simp [MulAut.conj_apply]⟩
  by_cases hMB : M = B
  · rw [← hMB]
    exact hnM
  exfalso
  have hcomm_MB : ⁅M, B⁆ = ⊥ := (distinct_components_commute hMc hBc).resolve_left hMB
  have hMB' : ∀ m ∈ M, ∀ b ∈ B, m * b = b * m := by
    intro m hm b hb
    have h1 := (commutator_eq_bot_iff_le_centralizer).1 hcomm_MB hm
    exact ((mem_centralizer_iff.1 h1) b hb).symm
  let q8' : QuaternionGroup 2 →* S := (MulAut.conj h).toMonoidHom.comp q8
  have hq8' : Function.Injective q8' := (MulAut.conj h).injective.comp hq8
  have hq8'M : ∀ g, q8' g ∈ M := fun g => ⟨q8 g, hq8B g, rfl⟩
  have hcm : ∀ a b : QuaternionGroup 2, Commute (q8 a) (q8' b) := fun a b =>
    (hMB' _ (hq8'M b) _ (hq8B a)).symm
  let φ : QuaternionGroup 2 × QuaternionGroup 2 →* S := MonoidHom.noncommCoprod q8 q8' hcm
  have hφ : ∀ a b, φ (a, b) = q8 a * q8' b := fun a b => by simp [φ]
  have hzz : q8 (QuaternionGroup.a 2) * q8 (QuaternionGroup.a 2) = 1 := by
    have h1 : (QuaternionGroup.a 2 : QuaternionGroup 2) * QuaternionGroup.a 2 = 1 := by decide
    rw [← map_mul, h1, map_one]
  have hz1 : q8 (QuaternionGroup.a 2) ≠ 1 := fun h1 => by
    have := hq8 (h1.trans (map_one q8).symm)
    exact absurd this (by decide)
  have hz : ∀ a : QuaternionGroup 2, (∀ b ∈ B, q8 a * b = b * q8 a) → a = 1 := by
    intro a ha
    have hac : ∀ a' : QuaternionGroup 2, a * a' = a' * a := fun a' =>
      hq8 (by rw [map_mul, map_mul]; exact ha _ (hq8B a'))
    rcases CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices.quaternion_center a hac with h1 | h1
    · exact h1
    · exfalso
      subst h1
      exact hBodd _ (hq8B _) ha ⟨hzz, hz1⟩
  have hker : ∀ g, φ g = 1 → g = 1 ∨ g = (QuaternionGroup.a 2, QuaternionGroup.a 2) := by
    rintro ⟨a, b⟩ hg
    rw [hφ] at hg
    have h1 : q8 a = (q8' b)⁻¹ := eq_inv_of_mul_eq_one_left hg
    have hm : q8 a ∈ M := by
      rw [h1]
      exact inv_mem (hq8'M b)
    have ha : a = 1 := hz a fun b' hb' => hMB' _ hm b' hb'
    subst ha
    left
    rw [map_one, one_mul] at hg
    have : b = 1 := hq8' (hg.trans (map_one q8').symm)
    rw [this]
    rfl
  have hT : IsPGroup 2 ↥(Subgroup.zpowers c) := by
    have hord : orderOf c = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [sq]; exact hc2) hc1
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord]
    norm_num
  have hTc : Subgroup.zpowers c ≤ Subgroup.center S := (Subgroup.zpowers_le).2 hcc
  have hcomm_T : ∀ (a : QuaternionGroup 2 × QuaternionGroup 2) (t : S), t ∈ Subgroup.zpowers c →
      φ a * t = t * φ a := fun a t ht => (Subgroup.mem_center_iff.1 (hTc ht) (φ a))
  obtain ⟨g, hgc, hgz⟩ := q8q8_commuting_two_subgroup_le' hS φ hker (Subgroup.zpowers c) hT hcomm_T c
    (Subgroup.mem_zpowers c)
  obtain ⟨g1, g2⟩ := g
  have hg1 : g1 = 1 ∨ g1 = QuaternionGroup.a 2 :=
    CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices.quaternion_center g1 (fun x => by
      have := congrArg Prod.fst (hgz (x, 1))
      simpa using this)
  have hg2 : g2 = 1 ∨ g2 = QuaternionGroup.a 2 :=
    CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices.quaternion_center g2 (fun x => by
      have := congrArg Prod.snd (hgz (1, x))
      simpa using this)
  rw [hφ] at hgc
  have hcB : c ∈ B → False := fun hcB =>
    hBodd c hcB (fun b hb => (Subgroup.mem_center_iff.1 hcc b).symm) ⟨hc2, hc1⟩
  rcases hg1 with rfl | rfl <;> rcases hg2 with rfl | rfl
  ·
    rw [map_one, map_one, one_mul] at hgc
    exact hc1 hgc.symm
  ·
    rw [map_one, one_mul] at hgc
    have h1 : h⁻¹ * c * h = q8 (QuaternionGroup.a 2) := by
      rw [← hgc]
      simp [q8', MulAut.conj_apply]
      try group
    have h2 : h⁻¹ * c * h = c := by
      have := Subgroup.mem_center_iff.1 hcc h⁻¹
      calc h⁻¹ * c * h = c * h⁻¹ * h := by rw [this]
        _ = c := by group
    exact hcB (by rw [← h2, h1]; exact hq8B _)
  ·
    rw [map_one, mul_one] at hgc
    exact hcB (by rw [← hgc]; exact hq8B _)
  ·
    have hzB : ∀ b ∈ B, q8 (QuaternionGroup.a 2) * b = b * q8 (QuaternionGroup.a 2) := by
      intro b hb
      set A := q8 (QuaternionGroup.a 2) with hA
      set B' := q8' (QuaternionGroup.a 2) with hB'
      have h3 : b * (A * B') = (A * B') * b := by
        rw [hgc]
        exact Subgroup.mem_center_iff.1 hcc b
      have h2 : B' * b = b * B' := hMB' _ (hq8'M _) b hb
      have h4 : (b * A) * B' = (A * b) * B' := by
        calc (b * A) * B' = b * (A * B') := by group
          _ = (A * B') * b := h3
          _ = A * (B' * b) := by group
          _ = A * (b * B') := by rw [h2]
          _ = (A * b) * B' := by group
      exact (mul_right_cancel h4).symm
    exact hBodd _ (hq8B _) hzB ⟨hzz, hz1⟩

end Gen4Permutation

theorem normalizer_of_component_gen4 (hG : Gen4 G) {L : Subgroup G} (hLq : IsQuasisimple L)
    (hLc : ∀ z ∈ L, (∀ w ∈ L, z * w = w * z) → Odd (orderOf z))
    (q8 : QuaternionGroup 2 →* G) (hq8 : Function.Injective q8) (hq8L : ∀ g, q8 g ∈ L)
    {c : G} (hcL : ∀ a ∈ L, a * c = c * a) (hc2 : orderOf c = 2)
    (hsub : (L.subgroupOf (centralizer ({c} : Set G))).IsSubnormal) :
    centralizer ({c} : Set G) ≤ normalizer (L : Set G) := by
  classical
  set S : Subgroup G := centralizer ({c} : Set G) with hS
  have hLS : L ≤ S := fun a ha => mem_centralizer_singleton_iff.2 (hcL a ha)
  have hcz : c * c = 1 := by rw [← sq, ← hc2]; exact pow_orderOf_eq_one c
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hc2
    exact absurd hc2 (by norm_num)
  have hBc : IsComponent (L.subgroupOf S) :=
    ⟨isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hLS).symm hLq, hsub⟩
  let q8S : QuaternionGroup 2 →* ↥S :=
    q8.codRestrict S fun g => mem_centralizer_singleton_iff.2 (hcL _ (hq8L g))
  have hq8S : Function.Injective q8S := fun a b h => hq8 (congrArg Subtype.val h)
  have hq8SB : ∀ g, q8S g ∈ L.subgroupOf S := fun g => mem_subgroupOf.2 (hq8L g)
  have hcS : (⟨c, mem_centralizer_singleton_iff.2 rfl⟩ : ↥S) ∈ Subgroup.center ↥S := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_singleton_iff.1 g.2)
  have hnorm : (L.subgroupOf S).Normal :=
    normal_of_component_gen4 (Gen4.subgroup S hG) hBc (no_central_involution_subgroupOf hLS hLc) q8S
      hq8S hq8SB hcS (Subtype.ext hcz) (fun h => hc1 (congrArg Subtype.val h))
  exact normalizer_of_subgroupOf_normal hLS hnorm

@[expose] def S1LeafCompHigh : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    S1Front G x K → S1LargeModel K → ∀ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)),
      S1Frame x K u hu → S1SymFrame x u →
        ∀ c ∈ symJ (symX x u) 3, orderOf c = 2 → (∀ a ∈ symJ (symX x u) 3, a * c = c * a) →
          ((symJ (symX x u) 0 ⊔ symJ (symX x u) 1).subgroupOf (centralizer ({c} : Set G))).IsSubnormal

@[expose] def S1LeafComp3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (x : G) (K : Subgroup (CentralizerBar x)), S1Setup G x K →
    S1Front G x K → ∀ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)),
      S1Frame x K u hu → ∀ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 3 →
        S1SymFrameLin x u F → S1FrameOddFree x u →
          ∀ c ∈ symJ3 (symX x u) 3, orderOf c = 2 → (∀ a ∈ symJ3 (symX x u) 3, a * c = c * a) →
            ((symJ3 (symX x u) 0 ⊔ symJ3 (symX x u) 1).subgroupOf (centralizer ({c} : Set G))).IsSubnormal

theorem s1CompNormal_of_leafComp (hExact : S1LiftExactProp) (hA : S1LeafCompHigh) : S1CompNormal := by
  intro G _ _ x K hset hfront hbigK u hu hf hsym c hcJ hc2 hcc
  have hsub := hA G x K hset hfront hbigK u hu hf hsym c hcJ hc2 hcc
  rcases id hsym with ⟨F, _, _, hF, hlin⟩ | ⟨q, F, _, _, hF, hq, huni⟩
  · have h4 : 3 < Nat.card F := three_lt_card_of_largeModel hbigK hF (sym_model_four hfront hlin)
    have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card (Nat.odd_iff.2 (by omega))
    obtain ⟨⟨hcomm, hpair⟩, q8, hq8, hq8J⟩ := sym_a4_lin hExact hset hf hF h4 hlin
    obtain ⟨W01, hW01⟩ := hpair 0 1 rfl
    obtain ⟨hWe, -⟩ := lin_pair_fusion h2 hW01
    obtain ⟨hWq, hWc⟩ := lin_pair_W_facts hW01
    subst hWe
    exact normalizer_of_component_gen4 hset.gen4 hWq hWc q8 hq8 (fun g => Subgroup.mem_sup_right (hq8J g))
      (fun a ha => sup_comm_three hcomm a ha c hcJ) hc2 hsub
  · obtain ⟨p, f, hud, hqpf, hp2⟩ := FrameUni.exists_unitaryFieldData hF hq
    have : Fact p.Prime := ⟨hud.prime⟩
    have : CharP F p := hud.charP
    subst hqpf
    have hodd : Odd (p ^ f) := Nat.odd_iff.2 (by omega)
    obtain ⟨⟨hcomm, hpair⟩, q8, hq8, hq8J⟩ := sym_a4_uni hExact hset hf hF hq huni p f hp2 rfl
    obtain ⟨W01, hW01⟩ := hpair 0 1 rfl
    obtain ⟨hWe, -⟩ := uni_pair_fusion hF hodd hW01
    obtain ⟨hWq, hWc⟩ := uni_pair_W_facts hF hodd hW01
    subst hWe
    exact normalizer_of_component_gen4 hset.gen4 hWq hWc q8 hq8 (fun g => Subgroup.mem_sup_right (hq8J g))
      (fun a ha => sup_comm_three hcomm a ha c hcJ) hc2 hsub

theorem s1CompNormal3_of_leafComp (hA : S1LeafComp3) : S1CompNormal3 := by
  intro G _ _ x K hset hfront u hu hf F hFld hFin hF3 hlin hodd c hcJ hc2 hcc
  have hsub := hA G x K hset hfront u hu hf F hFld hFin hF3 hlin hodd c hcJ hc2 hcc
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card (by rw [hF3]; exact ⟨1, rfl⟩)
  obtain ⟨⟨hcomm, hpair⟩, q8, hq8, hq8J⟩ := sym_a4_q3 hset hf hF3 hlin hodd
  obtain ⟨W01, hW01⟩ := hpair 0 1 rfl
  obtain ⟨hWe, -⟩ := lin_pair_fusion h2 hW01
  obtain ⟨hWq, hWc⟩ := lin_pair_W_facts hW01
  subst hWe
  exact normalizer_of_component_gen4 hset.gen4 hWq hWc q8 hq8 (fun g => Subgroup.mem_sup_right (hq8J g))
    (fun a ha => sup_comm_three hcomm a ha c hcJ) hc2 hsub

theorem symJ_comm_high (hExact : S1LiftExactProp) {x : G} {K : Subgroup (CentralizerBar x)}
    (hset : S1Setup G x K) (hfront : S1Front G x K) (hbigK : S1LargeModel K) {u : Fin 4 → G}
    {hu : ∀ i, u i ∈ centralizer ({x} : Set G)} (hf : S1Frame x K u hu) (hsym : S1SymFrame x u) :
    ∀ i j : Fin 4, (i : ℕ) + 1 < j → ∀ a ∈ symJ (symX x u) i, ∀ b ∈ symJ (symX x u) j,
      a * b = b * a := by
  rcases id hsym with ⟨F, _, _, hF, hlin⟩ | ⟨q, F, _, _, hF, hq, huni⟩
  · have h4 : 3 < Nat.card F := three_lt_card_of_largeModel hbigK hF (sym_model_four hfront hlin)
    exact (sym_a4_lin hExact hset hf hF h4 hlin).1.1
  · obtain ⟨p, f, hud, hqpf, hp2⟩ := FrameUni.exists_unitaryFieldData hF hq
    have : Fact p.Prime := ⟨hud.prime⟩
    have : CharP F p := hud.charP
    exact (sym_a4_uni hExact hset hf hF hq huni p f hp2 hqpf).1.1

end CFSG.GH74.Generic.S1
