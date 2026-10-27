module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1520OneE
import CFSG.LocalAnalysis.ComponentInitial.EmptyLayerCharTwo
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1520OneC
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1520OneG
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.QuasithinUnique CFSG.Open Subgroup

theorem not_dvd_index_of_commutator_mem {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hnp : ∀ N : Subgroup X, N.Normal → N.index ≠ p) {N : Subgroup X} [N.Normal]
    (hN : ∀ x y : X, x * y * x⁻¹ * y⁻¹ ∈ N) : ¬ p ∣ N.index := by
  intro hdvd
  haveI : IsMulCommutative (X ⧸ N) := ⟨⟨fun a b => by
    refine QuotientGroup.induction_on a fun x => QuotientGroup.induction_on b fun y => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have := hN y⁻¹ x⁻¹
    simpa [mul_assoc] using this⟩⟩
  have hd : p ∣ Nat.card (X ⧸ N) := by
    rw [← Subgroup.index_eq_card]
    exact hdvd
  obtain ⟨H, hH, hHn⟩ := Group.IsNilpotent.exists_normal_index_eq_of_dvd_card hd
  refine hnp (H.comap (QuotientGroup.mk' N)) (hHn.comap _) ?_
  rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N)]
  exact hH

theorem pRank_le_of_inner_action {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hnp : ∀ N : Subgroup X, N.Normal → N.index ≠ p) {Y S N : Subgroup X} [N.Normal]
    (hN : ∀ x y : X, x * y * x⁻¹ * y⁻¹ ∈ N)
    (hNS : ∀ y ∈ N, ∃ s ∈ S, ∀ z ∈ S, y * z * y⁻¹ = s * z * s⁻¹)
    (hSY : S ≤ Y) (hC : ∀ c ∈ Y, (∀ z ∈ S, c * z * c⁻¹ = z) → c ∈ S) :
    Open.pRank p Y ≤ Open.pRank p S := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hidx := not_dvd_index_of_commutator_mem hnp hN
  obtain ⟨E, hEY, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt Y
  have hEp : IsPGroup p E := fun g => ⟨1, Subtype.ext (by simpa [pow_one] using hE.2 g g.2)⟩
  have hEN : E ≤ N := le_of_isPGroup_of_not_dvd_index hEp hidx
  have hES : E ≤ S := by
    intro y hy
    obtain ⟨s, hs, hsz⟩ := hNS y (hEN hy)
    have hc : s⁻¹ * y ∈ S := by
      refine hC _ (Y.mul_mem (Y.inv_mem (hSY hs)) (hEY hy)) fun z hz => ?_
      calc s⁻¹ * y * z * (s⁻¹ * y)⁻¹ = s⁻¹ * (y * z * y⁻¹) * s := by group
        _ = z := by rw [hsz z hz]; group
    have : y = s * (s⁻¹ * y) := by group
    rw [this]
    exact S.mul_mem hs hc
  exact CFSG.SectionRank.le_pRank hp.one_lt hES hE hcard

theorem exists_normal_inner_action_of_cyclic {X : Type*} [Group X] {S : Subgroup X} [S.Normal]
    [IsCyclic ↥S] :
    ∃ N : Subgroup X, N.Normal ∧ (∀ x y : X, x * y * x⁻¹ * y⁻¹ ∈ N) ∧
      ∀ y ∈ N, ∃ s ∈ S, ∀ z ∈ S, y * z * y⁻¹ = s * z * s⁻¹ := by
  have hc : ∀ a b : MulAut ↥S, a * b = b * a := by
    intro a b
    obtain ⟨m, hm⟩ := MonoidHom.map_cyclic (a : ↥S →* ↥S)
    obtain ⟨n, hn⟩ := MonoidHom.map_cyclic (b : ↥S →* ↥S)
    refine MulEquiv.ext fun g => ?_
    have e1 : a (b g) = g ^ (m * n) := by
      rw [show b g = g ^ n from hn g, map_zpow, show a g = g ^ m from hm g, ← zpow_mul]
    have e2 : b (a g) = g ^ (n * m) := by
      rw [show a g = g ^ m from hm g, map_zpow, show b g = g ^ n from hn g, ← zpow_mul]
    show a (b g) = b (a g)
    rw [e1, e2, mul_comm]
  refine ⟨(MulAut.conjNormal : X →* MulAut ↥S).ker, inferInstance, fun x y => ?_,
    fun y hy => ⟨1, S.one_mem, fun z hz => ?_⟩⟩
  · simp only [MonoidHom.mem_ker, map_mul, map_inv]
    rw [hc (MulAut.conjNormal x) (MulAut.conjNormal y)]
    group
  · have h := congrArg (fun φ : MulAut ↥S => (φ ⟨z, hz⟩ : X)) (MonoidHom.mem_ker.1 hy)
    simpa using h

theorem exists_normal_inner_action_of_simple
    (hSz : CFSG.RankThree.PartTwo.KFacts.KPSz) {X : Type} [Group X] [Finite X]
    (hK : CFSG.IsKGroup X) {S : Subgroup X} [S.Normal] [IsSimpleGroup ↥S]
    (hnab : ∃ a b : ↥S, a * b ≠ b * a) (h3 : ¬ 3 ∣ Nat.card S) :
    ∃ N : Subgroup X, N.Normal ∧ (∀ x y : X, x * y * x⁻¹ * y⁻¹ ∈ N) ∧
      ∀ y ∈ N, ∃ s ∈ S, ∀ z ∈ S, y * z * y⁻¹ = s * z * s⁻¹ := by
  have hcat : CFSG.Assembly.InCatalog ↥S :=
    hK.inCatalog_of_surjective S (MonoidHom.id ↥S) Function.surjective_id
  have hcomm :=
    CFSG.RankThree.PartTwo.KFacts.commutator_le_inner_of_not_three_dvd hSz hnab hcat h3
  haveI hnorm : (MulAut.conj : ↥S →* MulAut ↥S).range.Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal ↥S
  refine ⟨((MulAut.conj : ↥S →* MulAut ↥S).range).comap (MulAut.conjNormal : X →* MulAut ↥S),
    hnorm.comap _, fun x y => ?_, fun y hy => ?_⟩
  · rw [Subgroup.mem_comap]
    simp only [map_mul, map_inv]
    exact hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  · obtain ⟨s, hs⟩ := MonoidHom.mem_range.1 (Subgroup.mem_comap.1 hy)
    refine ⟨s, s.2, fun z hz => ?_⟩
    have h := congrArg (fun φ : MulAut ↥S => (φ ⟨z, hz⟩ : X)) hs
    simpa using h.symm

theorem exists_component_dvd_three_of_two_le_pRank
    (hSz : CFSG.RankThree.PartTwo.KFacts.KPSz) {X : Type} [Group X] [Finite X]
    (hK : CFSG.IsKGroup X) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hnp : ∀ N : Subgroup X, N.Normal → N.index ≠ p) {Y : Subgroup X} [Y.Normal]
    (hO : CFSG.pPrimeCore p ↥Y = ⊥) (hrk : 2 ≤ Open.pRank p Y)
    (hF : ¬ 3 ∣ Nat.card (CFSG.generalizedFitting ↥Y) →
      Open.pRank p (CFSG.generalizedFitting ↥Y) ≤ 1) :
    ∃ K : Subgroup ↥Y, CFSG.IsComponent K ∧ 3 ∣ Nat.card K ∧ p ∣ Nat.card K := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hKp : ∀ K : Subgroup ↥Y, CFSG.IsComponent K → p ∣ Nat.card K := fun K hKc =>
    CFSG.RankThree.PartOne.Sec1511.p_dvd_card_component hO hKc
  by_contra hcon
  have hK3 : ∀ K : Subgroup ↥Y, CFSG.IsComponent K → ¬ 3 ∣ Nat.card K := fun K hKc h3 =>
    hcon ⟨K, hKc, h3, hKp K hKc⟩
  have hF3 := not_dvd_card_generalizedFitting hp Nat.prime_three hp3 hO hK3
  have hr1 := hF hF3
  haveI hchar : (CFSG.generalizedFitting ↥Y).Characteristic :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := ↥Y)).1
  set S : Subgroup X := (CFSG.generalizedFitting ↥Y).map Y.subtype with hSdef
  haveI hSn : S.Normal := inferInstance
  have hSY : S ≤ Y := map_subtype_le _
  have hC : ∀ c ∈ Y, (∀ z ∈ S, c * z * c⁻¹ = z) → c ∈ S := by
    intro c hc hcz
    have hcen : (⟨c, hc⟩ : ↥Y) ∈ Subgroup.centralizer (CFSG.generalizedFitting ↥Y : Set ↥Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      apply Subtype.ext
      have h := hcz (f : X) ⟨f, hf, rfl⟩
      simp only [Subgroup.coe_mul]
      calc (f : X) * c = c * f * c⁻¹ * c := by rw [h]
        _ = c * f := by group
    exact ⟨⟨c, hc⟩, CFSG.centralizer_generalizedFitting_le ↥Y hcen, rfl⟩
  have hrkS : Open.pRank p Y ≤ Open.pRank p S := by
    rcases generalizedFitting_cases_of_pRank_le_one hp hp2 hO hr1 with
      ⟨hFeq, hcyc⟩ | ⟨-, K, hKc, hFK, hZ⟩
    ·
      haveI : IsCyclic ↥(CFSG.generalizedFitting ↥Y) := by
        rw [hFeq]
        exact hcyc
      haveI : IsCyclic ↥S :=
        isCyclic_of_surjective ((CFSG.generalizedFitting ↥Y).equivMapOfInjective Y.subtype
          Y.subtype_injective).toMonoidHom (MulEquiv.surjective _)
      obtain ⟨N, hNn, hN, hNS⟩ := exists_normal_inner_action_of_cyclic (S := S)
      haveI := hNn
      exact pRank_le_of_inner_action hp hnp hN hNS hSY hC
    ·
      let e1 : ↥K ⧸ Subgroup.center ↥K ≃* ↥K :=
        (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
      let eS : ↥K ≃* ↥S :=
        (MulEquiv.subgroupCongr hFK).symm.trans
          ((CFSG.generalizedFitting ↥Y).equivMapOfInjective Y.subtype Y.subtype_injective)
      haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hKc.1.2.1
      haveI : IsSimpleGroup ↥K := e1.symm.isSimpleGroup
      haveI : IsSimpleGroup ↥S := eS.symm.isSimpleGroup
      have hnab : ∃ a b : ↥S, a * b ≠ b * a := by
        obtain ⟨a, b, hab⟩ := hKc.1.2.2
        refine ⟨eS (e1 a), eS (e1 b), fun h => hab ?_⟩
        apply e1.injective
        apply eS.injective
        rw [map_mul, map_mul, map_mul, map_mul]
        exact h
      have h3S : ¬ 3 ∣ Nat.card S := by
        rw [← Nat.card_congr eS.toEquiv]
        exact hK3 K hKc
      obtain ⟨N, hNn, hN, hNS⟩ := exists_normal_inner_action_of_simple hSz hK hnab h3S
      haveI := hNn
      exact pRank_le_of_inner_action hp hnp hN hNS hSY hC
  have h1 : Open.pRank p S = Open.pRank p (CFSG.generalizedFitting ↥Y) :=
    pRank_map_eq_of_coprime_kernel Y.subtype _ (by
      rw [Y.ker_subtype, inf_bot_eq, Subgroup.card_bot]
      exact hp.not_dvd_one)
  omega

theorem pPrimeCore_eq_subgroupOf_of_normal {M : Type*} [Group M] [Finite M] {p : ℕ}
    [Fact p.Prime] (H : Subgroup M) [H.Normal] :
    CFSG.pPrimeCore p ↥H = (CFSG.pPrimeCore p M).subgroupOf H := by
  apply le_antisymm
  · haveI : ((CFSG.pPrimeCore p ↥H).map H.subtype).Normal := inferInstance
    have hcop : Nat.Coprime p (Nat.card ((CFSG.pPrimeCore p ↥H).map H.subtype)) := by
      rw [Subgroup.card_map_of_injective H.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    exact Subgroup.map_le_iff_le_comap.1 (le_sSup ⟨inferInstance, hcop⟩)
  · have hcop : Nat.Coprime p (Nat.card ((CFSG.pPrimeCore p M).subgroupOf H)) := by
      have h1 : ((CFSG.pPrimeCore p M).subgroupOf H).map H.subtype ≤ CFSG.pPrimeCore p M :=
        Subgroup.map_le_iff_le_comap.2 le_rfl
      have h2 := Subgroup.card_dvd_of_le h1
      rw [Subgroup.card_map_of_injective H.subtype_injective] at h2
      exact Nat.Coprime.coprime_dvd_right h2 CFSG.pPrimeCore_coprime_card
    exact le_sSup ⟨inferInstance, hcop⟩

theorem exists_pComponent_map_eq {H Y : Type} [Group H] [Finite H] [Group Y] {p : ℕ}
    (f : H →* Y) (hf : Function.Surjective f) (hker : f.ker = CFSG.pPrimeCore p H)
    {K : Subgroup Y} (hK : CFSG.IsComponent K) :
    ∃ L : Subgroup H, CFSG.IsPComponent p L ∧ Nat.card K ∣ Nat.card L := by
  let e : H ⧸ CFSG.pPrimeCore p H ≃* Y :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  obtain ⟨L, hL, hLmap⟩ := CFSG.LocalAnalysis.ComponentInitial.exists_isPComponent_of_isComponent p
    (CFSG.LocalCores.isComponent_map_mulEquiv e.symm hK)
  refine ⟨L, hL, ?_⟩
  have hfe : f = e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pPrimeCore p H)) := by
    ext x
    simp only [e, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      QuotientGroup.mk'_apply, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  have hLK : L.map f = K := by
    rw [hfe, ← Subgroup.map_map, hLmap]
    exact CFSG.LocalCores.map_map_symm e.symm K
  have hdvd := Subgroup.card_map_dvd (H := L) f
  rwa [hLK] at hdvd

theorem pPrimeCore_eq_bot_of_normal {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hX : CFSG.pPrimeCore p X = ⊥) (Y : Subgroup X) [Y.Normal] : CFSG.pPrimeCore p ↥Y = ⊥ := by
  haveI : ((CFSG.pPrimeCore p ↥Y).map Y.subtype).Normal := inferInstance
  have hcop : Nat.Coprime p (Nat.card ((CFSG.pPrimeCore p ↥Y).map Y.subtype)) := by
    rw [Subgroup.card_map_of_injective Y.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hbot := (CFSG.pPrimeCore_eq_bot_iff (p := p) (G := X)).1 hX _ inferInstance hcop
  exact (Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective).1 hbot

theorem pRank_generalizedFitting_le_one
    (hSz : CFSG.RankThree.PartTwo.KFacts.KPSz) {M : Type} [Group M] [Finite M]
    (hK : CFSG.IsKGroup M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hM : CharTwo (⊤ : Subgroup M)) {T : Subgroup M} (hT : IsSylowTwoOf T ⊤)
    (hN : ∀ T₀ : Subgroup M, T₀ ≠ ⊥ → T₀ ≤ T → (T₀.subgroupOf T).Characteristic →
      Open.pRank p (normalizer (T₀ : Set M)) ≤ 1)
    (Y : Subgroup (M ⧸ CFSG.pPrimeCore p M)) [Y.Normal]
    (h3 : ¬ 3 ∣ Nat.card (CFSG.generalizedFitting ↥Y)) :
    Open.pRank p (CFSG.generalizedFitting ↥Y) ≤ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : (CFSG.generalizedFitting ↥Y).Characteristic :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := ↥Y)).1
  have hsurj : Function.Surjective (QuotientGroup.mk' (CFSG.pPrimeCore p M)) :=
    QuotientGroup.mk'_surjective _
  let F' : Subgroup (M ⧸ CFSG.pPrimeCore p M) := (CFSG.generalizedFitting ↥Y).map Y.subtype
  haveI : F'.Normal := inferInstance
  let A : Subgroup M := F'.comap (QuotientGroup.mk' (CFSG.pPrimeCore p M))
  haveI hAn : A.Normal := Subgroup.Normal.comap inferInstance _
  have hWA : CFSG.pPrimeCore p M ≤ A := fun w hw => by
    show QuotientGroup.mk' (CFSG.pPrimeCore p M) w ∈ F'
    rw [show QuotientGroup.mk' (CFSG.pPrimeCore p M) w = 1 from (QuotientGroup.eq_one_iff w).2 hw]
    exact F'.one_mem
  have hAmap : A.map (QuotientGroup.mk' (CFSG.pPrimeCore p M)) = F' :=
    Subgroup.map_comap_eq_self_of_surjective hsurj F'
  have hidx : (CFSG.pPrimeCore p M).relIndex A = Nat.card F' := by
    calc (CFSG.pPrimeCore p M).relIndex A
        = ((⊥ : Subgroup (M ⧸ CFSG.pPrimeCore p M)).comap
            (QuotientGroup.mk' (CFSG.pPrimeCore p M))).relIndex A := by
          rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
      _ = Nat.card (A.map (QuotientGroup.mk' (CFSG.pPrimeCore p M))) := by
          rw [Subgroup.relIndex_comap, Subgroup.relIndex_bot_left]
      _ = Nat.card F' := by rw [hAmap]
  have h3A : ¬ 3 ∣ (CFSG.pPrimeCore p M).relIndex A := by
    rw [hidx, Subgroup.card_map_of_injective Y.subtype_injective]
    exact h3
  have h6 := pRank_quotient_pPrimeCore_le_one hSz hK hp hp2 hM hT hN hWA h3A
  have h7 : Open.pRank p F' = Open.pRank p (CFSG.generalizedFitting ↥Y) :=
    pRank_map_eq_of_coprime_kernel Y.subtype _ (by
      rw [Y.ker_subtype, inf_bot_eq, Subgroup.card_bot]
      exact hp.not_dvd_one)
  rw [← h7, ← hAmap]
  exact h6

theorem exists_pComponent_dvd_three_of_two_le_pRank
    (hSz : CFSG.RankThree.PartTwo.KFacts.KPSz) {M : Type}
    [Group M] [Finite M] (hK : CFSG.IsKGroup M) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hM : CharTwo (⊤ : Subgroup M)) {T : Subgroup M} (hT : IsSylowTwoOf T ⊤)
    (hN : ∀ T₀ : Subgroup M, T₀ ≠ ⊥ → T₀ ≤ T → (T₀.subgroupOf T).Characteristic →
      Open.pRank p (normalizer (T₀ : Set M)) ≤ 1)
    (hnp : ∀ N : Subgroup M, N.Normal → N.index ≠ p) {H : Subgroup M} [H.Normal]
    (hrk : 2 ≤ Open.pRank p H) :
    ∃ I : Subgroup M, I ≤ H ∧ CFSG.IsPComponent p (I.subgroupOf H) ∧ 3 ∣ Nat.card I ∧
      p ∣ Nat.card I := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hsurj : Function.Surjective (QuotientGroup.mk' (CFSG.pPrimeCore p M)) :=
    QuotientGroup.mk'_surjective _
  haveI hYn : (H.map (QuotientGroup.mk' (CFSG.pPrimeCore p M))).Normal :=
    Subgroup.Normal.map inferInstance _ hsurj
  have hkerH : ¬ p ∣ Nat.card ↥(H ⊓ (QuotientGroup.mk' (CFSG.pPrimeCore p M)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact fun h => (Nat.Prime.coprime_iff_not_dvd hp).1
      (CFSG.pPrimeCore_coprime_card (p := p) (G := M)) (h.trans (card_dvd_of_le inf_le_right))
  have hrkY : 2 ≤ Open.pRank p (H.map (QuotientGroup.mk' (CFSG.pPrimeCore p M))) := by
    rw [pRank_map_eq_of_coprime_kernel _ H hkerH]
    exact hrk
  have hnpX : ∀ N : Subgroup (M ⧸ CFSG.pPrimeCore p M), N.Normal → N.index ≠ p :=
    fun N hNn => by
      rw [← Subgroup.index_comap_of_surjective N hsurj]
      exact hnp _ (hNn.comap _)
  have hO := pPrimeCore_eq_bot_of_normal (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot p)
    (H.map (QuotientGroup.mk' (CFSG.pPrimeCore p M)))
  obtain ⟨K, hKc, h3K, hpK⟩ := exists_component_dvd_three_of_two_le_pRank hSz (hK.quotient _) hp
    hp5 hnpX hO hrkY (pRank_generalizedFitting_le_one hSz hK hp hp2 hM hT hN _)
  have hkerΦ : ((QuotientGroup.mk' (CFSG.pPrimeCore p M)).subgroupMap H).ker =
      CFSG.pPrimeCore p ↥H := by
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk', pPrimeCore_eq_subgroupOf_of_normal H]
  obtain ⟨L, hL, hdvd⟩ := exists_pComponent_map_eq
    ((QuotientGroup.mk' (CFSG.pPrimeCore p M)).subgroupMap H)
    ((QuotientGroup.mk' (CFSG.pPrimeCore p M)).subgroupMap_surjective H) hkerΦ hKc
  refine ⟨L.map H.subtype, Subgroup.map_subtype_le L, ?_, ?_, ?_⟩
  · have h : (L.map H.subtype).subgroupOf H = L :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective L
    rwa [h]
  · rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact h3K.trans hdvd
  · rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact hpK.trans hdvd

end CFSG.LocalAnalysis.RankThreeUC.S15
