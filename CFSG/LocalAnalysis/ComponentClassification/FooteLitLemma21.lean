module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma22
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHypG

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

theorem conjClosure_eq_iSup {G : Type*} [Group G] (Y E : Subgroup G) :
    conjClosure Y E = ⨆ e ∈ E, conjugate Y e := by
  unfold conjClosure
  simp only [Subgroup.closure_iUnion, Subgroup.closure_eq, SetLike.mem_coe]

variable {H : Type} [Group H] [Finite H]

theorem le_pLayer_of_isPComponent_centralizer_singleton {a : H} (ha : orderOf a = 2)
    {K : Subgroup H} (hKa : K ≤ centralizer ({a} : Set H))
    (hK : IsPComponent 2 (K.subgroupOf (centralizer ({a} : Set H)))) : K ≤ pLayer H 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  have hbal := ClassicalInvolution.l2PrimeBalance H (zpowers a) hp
  rw [FooteLit.centralizer_zpowers_eq] at hbal
  have hKE : K.subgroupOf (centralizer ({a} : Set H)) ≤ pLayer ↥(centralizer ({a} : Set H)) 2 :=
    le_sSup hK
  intro k hk
  exact hbal ⟨⟨k, hKa hk⟩, hKE (show (⟨k, hKa hk⟩ : centralizer ({a} : Set H)) ∈
    K.subgroupOf (centralizer ({a} : Set H)) from hk), rfl⟩

theorem pLayer_le_normalizer_of_isPComponent {X : Subgroup H} (hX : IsPComponent 2 X) :
    pLayer H 2 ≤ normalizer (X : Set H) := by
  apply sSup_le
  intro M hM
  by_cases hMX : X = M
  · rw [← hMX]
    exact le_normalizer
  · exact ((CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two X M hX
      hM).2 hMX).1

theorem conjClosure_eq_sup_conjugate {a : H} (ha : orderOf a = 2) {K M : Subgroup H}
    (hKa : K ≤ centralizer ({a} : Set H))
    (hK : IsPComponent 2 (K.subgroupOf (centralizer ({a} : Set H)))) (hM : IsPComponent 2 M)
    (hKM : K ≤ M ⊔ conjugate M a) :
    conjClosure K (pLayer H 2) = M ⊔ conjugate M a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E := pLayer H 2 with hE
  set J := M ⊔ conjugate M a with hJ
  have haa : a * a = 1 := by rw [← sq, ← ha, pow_orderOf_eq_one]
  have hMa : IsPComponent 2 (conjugate M a) := isPComponent_conjugate hM a
  have hEJ : E ≤ normalizer (J : Set H) := fun e he =>
    mem_normalizer_sup (pLayer_le_normalizer_of_isPComponent hM he)
      (pLayer_le_normalizer_of_isPComponent hMa he)
  have hME : M ≤ E := le_sSup hM
  have hMaE : conjugate M a ≤ E := le_sSup hMa
  have hJE : J ≤ E := sup_le hME hMaE
  set S := conjClosure K E with hS
  have hSi : S = ⨆ e ∈ E, conjugate K e := conjClosure_eq_iSup K E
  have hSJ : S ≤ J := by
    rw [hSi]
    refine iSup₂_le fun e he => ?_
    calc conjugate K e ≤ conjugate J e := map_mono hKM
      _ = J := conjugate_eq_of_mem_normalizer (hEJ he)
  have hKS : K ≤ S := by
    rw [hSi]
    exact le_iSup₂_of_le 1 (one_mem E) (by rw [conjugate_one])
  have hES : E ≤ normalizer (S : Set H) := fun e he => by
    rw [hSi]; exact mem_normalizer_iSup_conjugate_of_mem he
  have haE : a ∈ normalizer (E : Set H) := by
    rw [normalizer_eq_top]; exact mem_top a
  have haK : a ∈ normalizer (K : Set H) :=
    mem_normalizer_of_conjugate_eq (conjugate_eq_self_of_le_centralizer hKa)
  have haS : a ∈ normalizer (S : Set H) := by
    rw [hSi]; exact mem_normalizer_iSup_conjugate_of_normalizer haE haK
  have hKperf : ⁅K, K⁆ = K := GSThmB.commutator_eq_self_of_isPComponent hKa hK
  have hSperf : ⁅S, S⁆ = S := by
    refine le_antisymm (commutator_le_self _) ?_
    rw [hSi]
    refine iSup₂_le fun e he => ?_
    have h1 : conjugate K e = ⁅conjugate K e, conjugate K e⁆ := by
      rw [conjugate, ← map_commutator, hKperf]
    rw [h1]
    exact commutator_mono (le_iSup₂_of_le e he le_rfl) (le_iSup₂_of_le e he le_rfl)
  set π := QuotientGroup.mk' (pPrimeCore 2 H) with hπ
  obtain ⟨A, hA, -, hAeq, -⟩ := id hM
  obtain ⟨B, hB, -, hBeq, -⟩ := id hMa
  have hSM : S ≤ normalizer (M : Set H) :=
    hSJ.trans (hJE.trans (pLayer_le_normalizer_of_isPComponent hM))
  have hSMa : S ≤ normalizer ((conjugate M a : Subgroup H) : Set H) :=
    hSJ.trans (hJE.trans (pLayer_le_normalizer_of_isPComponent hMa))
  have hMS : M ≤ normalizer (S : Set H) := hME.trans hES
  have hMaS : conjugate M a ≤ normalizer (S : Set H) := hMaE.trans hES
  have hπA : S.map π ≤ normalizer (A : Set (H ⧸ pPrimeCore 2 H)) := by
    rw [← hAeq]; exact (map_mono hSM).trans (le_normalizer_map π)
  have hπB : S.map π ≤ normalizer (B : Set (H ⧸ pPrimeCore 2 H)) := by
    rw [← hBeq]; exact (map_mono hSMa).trans (le_normalizer_map π)
  have hMJ : M ≤ S → J ≤ S := fun h => sup_le h (by
    rw [← conjugate_eq_of_mem_normalizer haS]; exact map_mono h)
  have hMaJ : conjugate M a ≤ S → J ≤ S := fun h => hMJ (by
    rw [← conjugate_conjugate_self_of_mul_self (X := M) haa, ← conjugate_eq_of_mem_normalizer haS]
    exact map_mono h)
  refine le_antisymm hSJ ?_
  rcases commutator_eq_self_or_eq_bot hA hπA with hAS | hAS
  · exact hMJ (le_of_commutator_map_eq hM hSM hMS (by rw [hAeq]; exact hAS))
  rcases commutator_eq_self_or_eq_bot hB hπB with hBS | hBS
  · exact hMaJ (le_of_commutator_map_eq hMa hSMa hMaS (by rw [hBeq]; exact hBS))
  exfalso
  have hcA : A ≤ centralizer ((S.map π : Subgroup _) : Set (H ⧸ pPrimeCore 2 H)) :=
    (commutator_eq_bot_iff_le_centralizer).mp hAS
  have hcB : B ≤ centralizer ((S.map π : Subgroup _) : Set (H ⧸ pPrimeCore 2 H)) :=
    (commutator_eq_bot_iff_le_centralizer).mp hBS
  have hSAB : S.map π ≤ A ⊔ B := by
    rw [← hAeq, ← hBeq, ← Subgroup.map_sup]; exact map_mono hSJ
  have hcomm : ∀ x ∈ S.map π, ∀ y ∈ S.map π, x * y = y * x := fun x hx y hy =>
    (mem_centralizer_iff.mp ((sup_le hcA hcB) (hSAB hy)) x hx)
  have hπperf : ⁅S.map π, S.map π⁆ = S.map π := by rw [← map_commutator, hSperf]
  have hbot := eq_bot_of_perfect_of_comm hπperf hcomm
  have hSO : S ≤ pPrimeCore 2 H := by
    intro s hs
    have h1 : π s ∈ S.map π := mem_map_of_mem π hs
    rw [hbot, mem_bot] at h1
    exact (QuotientGroup.eq_one_iff s).mp h1
  exact not_le_of_isPComponent_of_coprime hKa hK (pPrimeCore_coprime_card (p := 2) (G := H))
    (hKS.trans hSO)

omit [Finite H] in
theorem mk_mem_center_iff {Y : Type*} [Group Y] (N : Subgroup Y) [N.Normal] (y : Y) :
    (QuotientGroup.mk y : Y ⧸ N) ∈ center (Y ⧸ N) ↔ ∀ x : Y, (x * y)⁻¹ * (y * x) ∈ N := by
  rw [mem_center_iff]
  constructor
  · intro h x
    have h1 := h (QuotientGroup.mk x)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
    exact h1
  · intro h q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    exact h x

omit [Finite H] in
theorem mem_fusionZStar_iff_forall {Y : Type*} [Group Y] (y : Y) :
    y ∈ Open.fusionZStar Y ↔ ∀ x : Y, (x * y)⁻¹ * (y * x) ∈ pPrimeCore 2 Y := by
  rw [mem_fusionZStar_iff, mk_mem_center_iff, GSThmB.fusionOddCore_eq_pPrimeCore]

omit [Finite H] in
theorem commutatorElement_mul_mem_center_left {Q : Type*} [Group Q] {g h z : Q}
    (hz : z ∈ center Q) : ⁅g * z, h⁆ = ⁅g, h⁆ := by
  have hz' : z * h = h * z := (mem_center_iff.mp hz h).symm
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc g * z * h * (z⁻¹ * g⁻¹) * h⁻¹ = g * (z * h) * z⁻¹ * g⁻¹ * h⁻¹ := by group
    _ = g * (h * z) * z⁻¹ * g⁻¹ * h⁻¹ := by rw [hz']
    _ = g * h * g⁻¹ * h⁻¹ := by group

omit [Finite H] in
theorem commutatorElement_mul_mem_center_right {Q : Type*} [Group Q] {g h z : Q}
    (hz : z ∈ center Q) : ⁅g, h * z⁆ = ⁅g, h⁆ := by
  calc ⁅g, h * z⁆ = ⁅h * z, g⁆⁻¹ := (commutatorElement_inv _ _).symm
    _ = ⁅h, g⁆⁻¹ := by rw [commutatorElement_mul_mem_center_left hz]
    _ = ⁅g, h⁆ := commutatorElement_inv _ _

theorem sup_oddCoreIn_eq_of_fusionZStar_equiv {K M : Subgroup H} (hKM : K ≤ M)
    (hMperf : ⁅M, M⁆ = M) (e : K ⧸ Open.fusionZStar K ≃* M ⧸ Open.fusionZStar M) :
    K ⊔ oddCoreIn M = M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ι : K →* M := Subgroup.inclusion hKM with hι
  set ψ : K →* M ⧸ Open.fusionZStar M := (QuotientGroup.mk' _).comp ι with hψ
  have hKO : K ⊓ oddCoreIn M ≤ oddCoreIn K :=
    le_oddCoreIn inf_le_left (fun k hk => mem_normalizer_inf' (le_normalizer hk)
      (mem_normalizer_oddCoreIn (le_normalizer (hKM hk))))
      (Odd.of_dvd_nat (odd_card_oddCoreIn M) (card_dvd_of_le inf_le_right))
  have hker : ψ.ker ≤ Open.fusionZStar K := by
    intro k hk
    have hkZ : ι k ∈ Open.fusionZStar M := (QuotientGroup.eq_one_iff _).mp hk
    rw [mem_fusionZStar_iff_forall] at hkZ ⊢
    intro k'
    have h1 := hkZ (ι k')
    rw [mem_pPrimeCore_iff_mem_oddCoreIn] at h1 ⊢
    apply hKO
    refine mem_inf.mpr ⟨((k' * k)⁻¹ * (k * k')).2, ?_⟩
    simpa [hι] using h1
  have hrange : ψ.range = ⊤ := by
    apply Subgroup.eq_top_of_le_card
    rw [← Subgroup.index_ker, ← Nat.card_congr e.toEquiv]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite))
      (Subgroup.index_dvd_of_le hker)
  have hsurj : ∀ m : M, ∃ k : K, (ι k)⁻¹ * m ∈ Open.fusionZStar M := by
    intro m
    obtain ⟨k, hk⟩ := (MonoidHom.mem_range).mp (hrange ▸ mem_top (QuotientGroup.mk m :
      M ⧸ Open.fusionZStar M))
    exact ⟨k, QuotientGroup.eq.mp hk⟩
  set π₂ := QuotientGroup.mk' (pPrimeCore 2 M) with hπ₂
  set Kbar := (K.subgroupOf M).map π₂ with hKbar
  have hZc : ∀ z : M, z ∈ Open.fusionZStar M → π₂ z ∈ center (M ⧸ pPrimeCore 2 M) := by
    intro z hz
    rw [mem_fusionZStar_iff_forall] at hz
    exact (mk_mem_center_iff _ z).mpr hz
  have hMp : ⁅(⊤ : Subgroup M), (⊤ : Subgroup M)⁆ = (⊤ : Subgroup M) := by
    apply map_injective M.subtype_injective
    rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    exact hMperf
  have hQperf : ⁅(⊤ : Subgroup (M ⧸ pPrimeCore 2 M)), (⊤ : Subgroup (M ⧸ pPrimeCore 2 M))⁆ =
      (⊤ : Subgroup (M ⧸ pPrimeCore 2 M)) := by
    rw [← map_top_of_surjective π₂ (QuotientGroup.mk'_surjective _), ← map_commutator, hMp]
  have hmemK : ∀ k : K, π₂ (ι k) ∈ Kbar := fun k =>
    mem_map_of_mem π₂ (show ι k ∈ K.subgroupOf M from k.2)
  have hKtop : Kbar = ⊤ := by
    rw [eq_top_iff, ← hQperf, commutator_le]
    intro q₁ _ q₂ _
    obtain ⟨m₁, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 M) q₁
    obtain ⟨m₂, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 M) q₂
    obtain ⟨k₁, hk₁⟩ := hsurj m₁
    obtain ⟨k₂, hk₂⟩ := hsurj m₂
    have e₁ : π₂ m₁ = π₂ (ι k₁) * π₂ ((ι k₁)⁻¹ * m₁) := by rw [← map_mul, mul_inv_cancel_left]
    have e₂ : π₂ m₂ = π₂ (ι k₂) * π₂ ((ι k₂)⁻¹ * m₂) := by rw [← map_mul, mul_inv_cancel_left]
    rw [e₁, e₂, commutatorElement_mul_mem_center_right (hZc _ hk₂),
      commutatorElement_mul_mem_center_left (hZc _ hk₁), commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem (hmemK k₁) (hmemK k₂)) (inv_mem (hmemK k₁)))
      (inv_mem (hmemK k₂))
  have htop : K.subgroupOf M ⊔ pPrimeCore 2 M = ⊤ := by
    have h := congrArg (Subgroup.comap π₂) hKtop
    rwa [hKbar, comap_map_eq, QuotientGroup.ker_mk', comap_top] at h
  have h2 := congrArg (Subgroup.map M.subtype) htop
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hKM, ← MonoidHom.range_eq_map,
    range_subtype] at h2
  exact h2

theorem oddResidualIn_eq_self_of_isPComponent_top {M : Subgroup H} (hM : IsPComponent 2 M) :
    oddResidualIn M = M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hres, -⟩ :=
    (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 M).mp hM
  refine le_antisymm (oddResidualIn_le M) ?_
  intro x hx
  have hxtop : (⟨x, hx⟩ : M) ∈ CatalogueBPrimeJoin.primeResidual 2 M := hres ▸ mem_top _
  have hle : (CatalogueBPrimeJoin.primeResidual 2 M).map M.subtype ≤ oddResidualIn M := by
    rw [map_le_iff_le_comap]
    refine sSup_le fun P hP => ?_
    intro y hy
    obtain ⟨i, hi⟩ := hP ⟨y, hy⟩
    have hyi : (y : H) ^ 2 ^ i = 1 := by
      have := congrArg (fun z : P => ((z : M) : H)) hi
      simpa using this
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hyi)
    exact mem_oddResidualIn y.2 ⟨j, hj⟩
  exact hle ⟨⟨x, hx⟩, hxtop, rfl⟩

theorem foote_lemma_2_1_iv {a : H} (ha : orderOf a = 2) {K : Subgroup H}
    (hKa : K ≤ centralizer ({a} : Set H))
    (hK : IsPComponent 2 (K.subgroupOf (centralizer ({a} : Set H)))) :
    ∃ L : Subgroup H, IsPComponent 2 L ∧ K ≤ L ⊔ conjugate L a ∧
      conjClosure K (pLayer H 2) = L ⊔ conjugate L a ∧
      ((conjugate L a = L ∧ L = oddResidualIn (K ⊔ pPrimeCore 2 H) ∧
          Nonempty (K ⧸ pPrimeCore 2 K ≃* L ⧸ pPrimeCore 2 L)) ∨
        (conjugate L a = L ∧ K ⊔ oddCoreIn L < L ∧
          IsEmpty (K ⧸ Open.fusionZStar K ≃* L ⧸ Open.fusionZStar L)) ∨
        (conjugate L a ≠ L ∧
          K = twoLayerIn ((L ⊔ conjugate L a) ⊓ centralizer ({a} : Set H)) ∧
          (pPrimeCore 2 K).index ≤ (pPrimeCore 2 L).index)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKE := le_pLayer_of_isPComponent_centralizer_singleton ha hKa hK
  obtain ⟨M, hM, hKM, hKpc⟩ := two_layer_fixed_component_orbit_location ha hKa hK hKE
  refine ⟨M, hM, hKM, conjClosure_eq_sup_conjugate ha hKa hK hM hKM, ?_⟩
  have hKC : K ≤ (M ⊔ conjugate M a) ⊓ centralizer ({a} : Set H) := le_inf hKM hKa
  obtain ⟨hle, hswap, heq⟩ := UnbalancedGS.involution_orbit_fixed_component_quotient_comparison
    ha M hM _ rfl _ rfl K hKC hKpc
  by_cases hMa : M = conjugate M a
  · have hKM' : K ≤ M := by
      have h := hKM
      rwa [← hMa, sup_idem] at h
    have hMperf : ⁅M, M⁆ = M := by
      have : Group.IsPerfect M := CatalogueBAlternating.pComponent_perfect hM
      exact Subgroup.commutator_eq_self
    obtain ⟨-, -, hMsub, -, -⟩ := id hM
    by_cases hidx : (pPrimeCore 2 K).index = (pPrimeCore 2 M).index
    · left
      have hcov : K ⊔ (pPrimeCore 2 M).map M.subtype = M := (heq hidx).2 hMa
      refine ⟨hMa.symm, le_antisymm ?_ ?_, ?_⟩
      · have hOM : (pPrimeCore 2 M).map M.subtype ≤ pPrimeCore 2 H :=
          Walter.map_pPrimeCore_le_of_isSubnormal hMsub
        calc M = oddResidualIn M := (oddResidualIn_eq_self_of_isPComponent_top hM).symm
          _ ≤ oddResidualIn (K ⊔ pPrimeCore 2 H) :=
            oddResidualIn_mono ((le_of_eq hcov.symm).trans (sup_le_sup_left hOM K))
      · refine (closure_le _).mpr fun g hg => ?_
        have hOodd : Odd (Nat.card (pPrimeCore 2 H)) :=
          Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := H))
        have hle' : K ⊔ pPrimeCore 2 H ≤ pPrimeCore 2 H ⊔ M :=
          sup_le (le_sup_of_le_right hKM') le_sup_left
        exact mem_of_two_element_of_mem_sup (UnbalancedLayer.pPrimeCore_le_normalizer hM)
          (by rw [oddResidualIn_eq_bot_of_odd hOodd]; exact bot_le) (hle' hg.1) hg.2
      · obtain ⟨-, e, -⟩ := restriction_quotient_mulEquiv hKM' hcov
        exact ⟨e⟩
    · right; left
      have hlt : K ⊔ oddCoreIn M < M := by
        refine lt_of_le_of_ne (sup_le hKM' (map_subtype_le _)) fun h => hidx ?_
        obtain ⟨-, e, -⟩ := restriction_quotient_mulEquiv hKM' h
        exact Nat.card_congr e.toEquiv
      exact ⟨hMa.symm, hlt, ⟨fun e => hlt.ne (sup_oddCoreIn_eq_of_fusionZStar_equiv hKM' hMperf e)⟩⟩
  · right; right
    exact ⟨Ne.symm hMa, (hswap hMa).symm, hle⟩

end CFSG.ComponentClassification.FooteLit
