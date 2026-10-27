module

public import CFSG.GH74.Generic.S1.SymPairs
public import CFSG.GH74.Generic.S1.TLeafA

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 Subgroup CFSG.GH74.Generic CFSG.LocalCores CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section NoCommute

variable {G : Type} [Group G] [Finite G]

theorem false_of_commutator_mem_odd {Cc O B0 B1 : Subgroup G}
    (hOn : ∀ g ∈ Cc, ∀ o ∈ O, g * o * g⁻¹ ∈ O) (hOodd : Odd (Nat.card O))
    (hB0 : B0 ≤ Cc) (hB1 : B1 ≤ Cc) (hq0 : IsQuasisimple ↥B0) (hq1 : IsQuasisimple ↥B1)
    (hqL : IsQuasisimple ↥(B0 ⊔ B1))
    (hcomm : ∀ b0 ∈ B0, ∀ b1 ∈ B1, b0 * b1 * b0⁻¹ * b1⁻¹ ∈ O) : False := by
  set L : Subgroup G := B0 ⊔ B1 with hL
  have hB0L : B0 ≤ L := le_sup_left
  have hB1L : B1 ≤ L := le_sup_right
  have hLC : L ≤ Cc := sup_le hB0 hB1
  have hN : (O.subgroupOf L).Normal :=
    ⟨fun n hn g => mem_subgroupOf.2 (hOn g.1 (hLC g.2) n.1 (mem_subgroupOf.1 hn))⟩
  have hOsolv : Group.IsSolvable ↥O := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hOodd
  have hsolv : Group.IsSolvable ↥(O.subgroupOf L) := by
    let φ : ↥(O.subgroupOf L) →* ↥O :=
      ((L.subtype).comp (O.subgroupOf L).subtype).codRestrict O (fun x => x.2)
    have hφ : Function.Injective φ := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥O => (z : G)) hab
    exact Group.isSolvable_of_isSolvable_injective hφ
  have hperf : ⁅B0, B0⁆ = B0 := Subgroup.isPerfect_iff.1 hq0.1
  rcases quasisimple_normal_subgroups hqL hN with htop | hcen
  ·
    have : Group.IsSolvable ↥(⊤ : Subgroup ↥L) := by rw [← htop]; exact hsolv
    have hLs : Group.IsSolvable ↥L :=
      Group.isSolvable_of_surjective (f := (Subgroup.topEquiv : (⊤ : Subgroup ↥L) ≃* ↥L).toMonoidHom)
        Subgroup.topEquiv.surjective
    have : Nontrivial ↥L := isQuasisimple_nontrivial hqL
    have : Group.IsPerfect ↥L := hqL.1
    exact Group.IsPerfect.not_isSolvable ↥L hLs
  ·
    set Z : Subgroup G := (center ↥L).map L.subtype with hZ
    have hcz : ∀ b0 ∈ B0, ∀ b1 ∈ B1, ⁅b0, b1⁆ ∈ Z := by
      intro b0 hb0 b1 hb1
      have h1 : ⁅b0, b1⁆ ∈ L := by
        rw [commutatorElement_def]
        exact L.mul_mem (L.mul_mem (L.mul_mem (hB0L hb0) (hB1L hb1)) (L.inv_mem (hB0L hb0)))
          (L.inv_mem (hB1L hb1))
      have h2 : (⟨⁅b0, b1⁆, h1⟩ : ↥L) ∈ O.subgroupOf L := mem_subgroupOf.2 (hcomm b0 hb0 b1 hb1)
      exact ⟨⟨⁅b0, b1⁆, h1⟩, hcen h2, rfl⟩
    have hBZ : ⁅B0, B1⁆ ≤ Z := Subgroup.commutator_le.2 hcz
    have hZL : ∀ z ∈ Z, ∀ l ∈ L, l * z = z * l := by
      rintro _ ⟨z, hz, rfl⟩ l hl
      have := Subgroup.mem_center_iff.1 hz ⟨l, hl⟩
      exact congrArg Subtype.val this
    have hZB : ∀ H : Subgroup G, H ≤ L → ⁅Z, H⁆ = ⊥ := by
      intro H hH
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro z hz
      rw [mem_centralizer_iff]
      intro h hh
      exact hZL z hz h (hH hh)
    have h1 : ⁅⁅B0, B1⁆, B0⁆ = ⊥ :=
      eq_bot_iff.2 ((Subgroup.commutator_mono hBZ le_rfl).trans (hZB B0 hB0L).le)
    have h2 : ⁅⁅B1, B0⁆, B0⁆ = ⊥ := by
      rw [Subgroup.commutator_comm B1 B0]
      exact h1
    have h3 : ⁅⁅B0, B0⁆, B1⁆ = ⊥ :=
      Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := B0) (H₂ := B0) (H₃ := B1) h1 h2
    rw [hperf] at h3
    have hB01 : ∀ b0 ∈ B0, ∀ b1 ∈ B1, b0 * b1 = b1 * b0 := by
      intro b0 hb0 b1 hb1
      have : b0 ∈ centralizer (B1 : Set G) := by
        have := (Subgroup.commutator_eq_bot_iff_le_centralizer).1 h3 hb0
        exact this
      exact ((mem_centralizer_iff.1 this) b1 hb1).symm
    have hB0n : (B0.subgroupOf L).Normal := by
      refine (normal_subgroupOf_iff_le_normalizer hB0L).2 (sup_le le_normalizer ?_)
      intro b1 hb1
      have : b1 ∈ centralizer (B0 : Set G) := mem_centralizer_iff.2 fun b0 hb0 => (hB01 b0 hb0 b1 hb1)
      exact Subgroup.centralizer_le_normalizer _ this
    rcases quasisimple_normal_subgroups hqL hB0n with h0 | h0
    ·
      refine quasisimple_not_commutative hq1 fun a b => ?_
      have hb : (b : G) ∈ B0 := by
        have : (⟨b.1, hB1L b.2⟩ : ↥L) ∈ B0.subgroupOf L := by rw [h0]; trivial
        exact this
      exact Subtype.ext (hB01 _ hb _ a.2).symm
    · refine quasisimple_not_commutative hq0 fun a b => ?_
      have := Subgroup.mem_center_iff.1 (h0 (show (⟨a.1, hB0L a.2⟩ : ↥L) ∈ B0.subgroupOf L from a.2))
        ⟨b.1, hB0L b.2⟩
      exact Subtype.ext (congrArg Subtype.val this).symm


section Pumpup

open CFSG.GH74.GLS.TwoThin

theorem exists_component_of_pumpup {c s : G} (hs : orderOf s = 2)
    (hsc : s ∈ centralizer ({c} : Set G)) {B : Subgroup G}
    (hB : CFSG.GH74.GLS.IsPCompIn 2 (centralizer ({s} : Set G) ⊓ centralizer ({c} : Set G)) B)
    {y : G} (hyB : y ∈ B) (hsy : s = y * c) :
    ∃ M : Subgroup (CentralizerBar c), IsComponent M ∧ S45.barSub c B ≤ M := by
  have hs' := orderOf_mk_centralizer hsc hs
  have hΛC := le_centralizer_mk hB.1 hsc
  have hΛ := isTwoComponent_centralizer_mk hB hsc
  obtain ⟨-, -, M, hM, hcases, -⟩ := pumpupY_structure hs' hΛC hΛ
  have hBC : B ≤ centralizer ({c} : Set G) := fun b hb => (Subgroup.mem_inf.1 (hB.1 hb)).2
  have hlay : S45.barSub c B ≤ layer (CentralizerBar c) := barSub_le_layer_of_isPCompIn hs hsc hB
  have hyc : y ∈ centralizer ({c} : Set G) := hBC hyB
  have hcc : c ∈ centralizer ({c} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hsub : (⟨s, hsc⟩ : ↥(centralizer ({c} : Set G))) = ⟨y, hyc⟩ * ⟨c, hcc⟩ :=
    Subtype.ext hsy
  have hyM : barMk ↥(centralizer ({c} : Set G)) ⟨y, hyc⟩ ∈ normalizer (M : Set (CentralizerBar c)) :=
    layer_le_normalizer hM (hlay (S45.proj_mem_barSub hyc hyB))
  have hcM : barMk ↥(centralizer ({c} : Set G)) ⟨c, hcc⟩ ∈ normalizer (M : Set (CentralizerBar c)) := by
    refine Subgroup.centralizer_le_normalizer (M : Set (CentralizerBar c)) ?_
    rw [mem_centralizer_iff]
    intro m _
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective m
    show (barMk ↥(centralizer ({c} : Set G)) k) * barMk ↥(centralizer ({c} : Set G)) ⟨c, hcc⟩ =
      barMk ↥(centralizer ({c} : Set G)) ⟨c, hcc⟩ * barMk ↥(centralizer ({c} : Set G)) k
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 k.2)
  have hnorm : barMk ↥(centralizer ({c} : Set G)) ⟨s, hsc⟩ ∈ normalizer (M : Set (CentralizerBar c)) := by
    rw [hsub, map_mul]
    exact (normalizer (M : Set (CentralizerBar c))).mul_mem hyM hcM
  rcases hcases with ⟨-, hle⟩ | ⟨hne, -⟩
  · exact ⟨M, hM, hle⟩
  · exfalso
    refine hne (Subgroup.ext fun v => ?_)
    rw [mem_conjSub_iff', inv_inv]
    exact (mem_normalizer_iff.1 hnorm v).symm


omit [Finite G] in
theorem barSub_sup {c : G} {A B : Subgroup G} (hA : A ≤ centralizer ({c} : Set G))
    (hB : B ≤ centralizer ({c} : Set G)) :
    S45.barSub c (A ⊔ B) = S45.barSub c A ⊔ S45.barSub c B := by
  unfold S45.barSub
  rw [subgroupOf_sup hA hB, Subgroup.map_sup]

theorem exists_component_of_two_pumpups {c s0 s1 : G} (hs0 : orderOf s0 = 2) (hs1 : orderOf s1 = 2)
    (hs0c : s0 ∈ centralizer ({c} : Set G)) (hs1c : s1 ∈ centralizer ({c} : Set G))
    {B0 B1 : Subgroup G}
    (hB0 : CFSG.GH74.GLS.IsPCompIn 2 (centralizer ({s0} : Set G) ⊓ centralizer ({c} : Set G)) B0)
    (hB1 : CFSG.GH74.GLS.IsPCompIn 2 (centralizer ({s1} : Set G) ⊓ centralizer ({c} : Set G)) B1)
    {y0 y1 : G} (hy0 : y0 ∈ B0) (hy1 : y1 ∈ B1) (hsy0 : s0 = y0 * c) (hsy1 : s1 = y1 * c)
    (hq0 : IsQuasisimple ↥B0) (hq1 : IsQuasisimple ↥B1) (hqL : IsQuasisimple ↥(B0 ⊔ B1)) :
    ∃ M : Subgroup (CentralizerBar c), IsComponent M ∧ S45.barSub c (B0 ⊔ B1) ≤ M := by
  obtain ⟨M0, hM0, h0⟩ := exists_component_of_pumpup hs0 hs0c hB0 hy0 hsy0
  obtain ⟨M1, hM1, h1⟩ := exists_component_of_pumpup hs1 hs1c hB1 hy1 hsy1
  have hB0C : B0 ≤ centralizer ({c} : Set G) := fun b hb => (Subgroup.mem_inf.1 (hB0.1 hb)).2
  have hB1C : B1 ≤ centralizer ({c} : Set G) := fun b hb => (Subgroup.mem_inf.1 (hB1.1 hb)).2
  rcases distinct_components_commute hM0 hM1 with heq | hcomm
  · subst heq
    exact ⟨M0, hM0, by rw [barSub_sup hB0C hB1C]; exact sup_le h0 h1⟩
  · exfalso
    refine false_of_commutator_mem_odd (Cc := centralizer ({c} : Set G))
      (O := CFSG.GH74.GLS.pPrimeCoreOf 2 (centralizer ({c} : Set G)))
      (fun g hg o ho => CFSG.GH74.GLS.TwoThin.pPrimeCoreOf_normalized _ hg ho)
      (CFSG.GH74.GLS.TwoThin.card_pPrimeCoreOf_odd _) hB0C hB1C hq0 hq1 hqL ?_
    intro b0 hb0 b1 hb1
    have hb0c := hB0C hb0
    have hb1c := hB1C hb1
    have hp0 : proj c ⟨b0, hb0c⟩ ∈ M0 := h0 (S45.proj_mem_barSub hb0c hb0)
    have hp1 : proj c ⟨b1, hb1c⟩ ∈ M1 := h1 (S45.proj_mem_barSub hb1c hb1)
    have hcm : proj c ⟨b0, hb0c⟩ * proj c ⟨b1, hb1c⟩ =
        proj c ⟨b1, hb1c⟩ * proj c ⟨b0, hb0c⟩ := by
      have h2 : ⁅proj c ⟨b0, hb0c⟩, proj c ⟨b1, hb1c⟩⁆ = 1 := by
        have := Subgroup.commutator_mem_commutator hp0 hp1
        rw [hcomm, Subgroup.mem_bot] at this
        exact this
      exact commutatorElement_eq_one_iff_mul_comm.1 h2
    have hmem : (⟨b0 * b1 * b0⁻¹ * b1⁻¹, by
        exact (centralizer ({c} : Set G)).mul_mem
          ((centralizer ({c} : Set G)).mul_mem
            ((centralizer ({c} : Set G)).mul_mem hb0c hb1c)
            ((centralizer ({c} : Set G)).inv_mem hb0c))
          ((centralizer ({c} : Set G)).inv_mem hb1c)⟩ : ↥(centralizer ({c} : Set G))) ∈
        pPrimeCore 2 ↥(centralizer ({c} : Set G)) := by
      rw [← QuotientGroup.eq_one_iff]
      have hprod : proj c ⟨b0 * b1 * b0⁻¹ * b1⁻¹, (centralizer ({c} : Set G)).mul_mem
          ((centralizer ({c} : Set G)).mul_mem
            ((centralizer ({c} : Set G)).mul_mem hb0c hb1c)
            ((centralizer ({c} : Set G)).inv_mem hb0c))
          ((centralizer ({c} : Set G)).inv_mem hb1c)⟩ =
          proj c ⟨b0, hb0c⟩ * proj c ⟨b1, hb1c⟩ * (proj c ⟨b0, hb0c⟩)⁻¹ * (proj c ⟨b1, hb1c⟩)⁻¹ := by
        rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
        rfl
      have h3 : proj c ⟨b0, hb0c⟩ * proj c ⟨b1, hb1c⟩ * (proj c ⟨b0, hb0c⟩)⁻¹ *
          (proj c ⟨b1, hb1c⟩)⁻¹ = 1 := by
        rw [hcm]
        group
      exact hprod.trans h3
    exact ⟨_, hmem, rfl⟩

end Pumpup

end NoCommute


section Frame

variable {G : Type} [Group G] [Finite G]

theorem sym_quasisimple (hExact : S1LiftExactProp) {x : G} {K : Subgroup (CentralizerBar x)}
    (hset : S1Setup G x K) (hfront : S1Front G x K) (hbigK : S1LargeModel K) {u : Fin 4 → G}
    {hu : ∀ i, u i ∈ centralizer ({x} : Set G)} (hf : S1Frame x K u hu) (hsym : S1SymFrame x u) :
    IsQuasisimple ↥(symJ (symX x u) 0) ∧ IsQuasisimple ↥(symJ (symX x u) 1) ∧
      IsQuasisimple ↥(symJ (symX x u) 0 ⊔ symJ (symX x u) 1) ∧
      ∀ z ∈ symJ (symX x u) 0 ⊔ symJ (symX x u) 1,
        (∀ w ∈ symJ (symX x u) 0 ⊔ symJ (symX x u) 1, z * w = w * z) → Odd (orderOf z) := by
  rcases id hsym with ⟨F, _, _, hF, hlin⟩ | ⟨q, F, _, _, hF, hq, huni⟩
  · have h4 : 3 < Nat.card F := three_lt_card_of_largeModel hbigK hF (sym_model_four hfront hlin)
    have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card (Nat.odd_iff.2 (by omega))
    obtain ⟨⟨hcomm, hpair⟩, q8, hq8, hq8J⟩ := sym_a4_lin hExact hset hf hF h4 hlin
    obtain ⟨W01, hW01⟩ := hpair 0 1 rfl
    obtain ⟨hWe, -⟩ := lin_pair_fusion h2 hW01
    obtain ⟨hWq, hWc⟩ := lin_pair_W_facts hW01
    obtain ⟨hq0, hq1⟩ := lin_pair_UV_quasisimple h4 hW01
    subst hWe
    exact ⟨hq0, hq1, hWq, hWc⟩
  · obtain ⟨p, f, hud, hqpf, hp2⟩ := FrameUni.exists_unitaryFieldData hF hq
    have : Fact p.Prime := ⟨hud.prime⟩
    have : CharP F p := hud.charP
    subst hqpf
    have hodd : Odd (p ^ f) := Nat.odd_iff.2 (by omega)
    have hq5 : 5 ≤ p ^ f := by
      have h1 : 1 < Nat.card F := Finite.one_lt_card
      rw [hF] at h1
      have hq1 : 1 < p ^ f := by
        by_contra hle
        have hle' : p ^ f ≤ 1 := by omega
        interval_cases hpf : p ^ f <;> simp at h1
      omega
    obtain ⟨⟨hcomm, hpair⟩, q8, hq8, hq8J⟩ := sym_a4_uni hExact hset hf hF hq huni p f hp2 rfl
    obtain ⟨W01, hW01⟩ := hpair 0 1 rfl
    obtain ⟨hWe, -⟩ := uni_pair_fusion hF hodd hW01
    obtain ⟨hWq, hWc⟩ := uni_pair_W_facts hF hodd hW01
    obtain ⟨hq0, hq1⟩ := uni_pair_UV_quasisimple hF hq5 hW01
    subst hWe
    exact ⟨hq0, hq1, hWq, hWc⟩

theorem sym_component_of_L (hExact : S1LiftExactProp) {x : G} {K : Subgroup (CentralizerBar x)}
    (hset : S1Setup G x K) (hfront : S1Front G x K) (hbigK : S1LargeModel K) {u : Fin 4 → G}
    {hu : ∀ i, u i ∈ centralizer ({x} : Set G)} (hf : S1Frame x K u hu) (hsym : S1SymFrame x u)
    {c : G} (hcJ : c ∈ symJ (symX x u) 3) (hc2 : orderOf c = 2)
    (hcc : ∀ a ∈ symJ (symX x u) 3, a * c = c * a) :
    ∃ M : Subgroup (CentralizerBar c), IsComponent M ∧
      S45.barSub c (symJ (symX x u) 0 ⊔ symJ (symX x u) 1) ≤ M := by
  obtain ⟨hXconj, -, -, -, -⟩ := symX_facts hset.shape.2 hset.inv hf
  have hX2 : ∀ e, orderOf (symX x u e) = 2 := fun e =>
    (IsConj.orderOf_eq (hXconj e)).symm.trans hset.inv
  have hdata := sym_pairData hExact hset hfront hbigK hf hsym hcJ hc2 hcc
  obtain ⟨hq0, hq1, hqL, -⟩ := sym_quasisimple hExact hset hfront hbigK hf hsym
  obtain ⟨y1, hy1, hxy1⟩ := hdata.xy4
  obtain ⟨y0, hy0, hxy0⟩ := hdata.xy1
  exact exists_component_of_two_pumpups (hX2 1) (hX2 4) hdata.hc1 hdata.hc4 hdata.j0 hdata.j1 hy0 hy1
    hxy0 hxy1 hq0 hq1 hqL

end Frame

end CFSG.GH74.Generic.S1
