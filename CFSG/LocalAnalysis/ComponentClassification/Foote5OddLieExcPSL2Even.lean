module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcPSL2Fam
public import CFSG.LieType.Ree.LargeReeInvolutionComponentFree
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalOddTwo
public import CFSG.Sporadic.Schreier.TitsComponent

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem center_eq_bot_of_isQuasisimple_of_isSimpleGroup {X : Type*} [Group X]
    (hq : IsQuasisimple X) (hs : IsSimpleGroup X) : center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective (center X) a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective (center X) b
    apply hab
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, h]
    exact mem_top _

theorem eq_one_of_mem_center_of_center_quot_eq_bot {G : Type*} [Group G] [Finite G]
    {J : Subgroup G} (hZJ : center (↥J ⧸ pPrimeCore 2 ↥J) = ⊥) {j : J}
    (hjc : (j : G) ∈ center G) {k : ℕ} (hk : (j : G) ^ 2 ^ k = 1) : j = 1 := by
  have hjcJ : j ∈ center ↥J := mem_center_iff.mpr fun y =>
    Subtype.ext ((mem_center_iff.mp hjc) _)
  have hjO : j ∈ pPrimeCore 2 ↥J := by
    have hcen : (QuotientGroup.mk' (pPrimeCore 2 ↥J) j) ∈ center (↥J ⧸ pPrimeCore 2 ↥J) := by
      refine mem_center_iff.mpr fun w => ?_
      obtain ⟨w', rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥J) w
      rw [← map_mul, ← map_mul, (mem_center_iff.mp hjcJ w')]
    rw [hZJ] at hcen
    exact (QuotientGroup.eq_one_iff j).1 (mem_bot.mp hcen)
  have hodd : Odd (orderOf j) := by
    have h1 : orderOf (⟨j, hjO⟩ : pPrimeCore 2 ↥J) ∣ Nat.card (pPrimeCore 2 ↥J) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat (Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2)
      (G := ↥J))) h1
  have hdvd : orderOf j ∣ 2 ^ k := by
    have h1 := orderOf_dvd_of_pow_eq_one hk
    rwa [Subgroup.orderOf_coe] at h1
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hi0 : i = 0 := by
    rcases Nat.eq_zero_or_pos i with h | h
    · exact h
    · rw [hi] at hodd
      exact absurd (Nat.even_pow.mpr ⟨even_two, h.ne'⟩) (Nat.not_even_iff_odd.mpr hodd)
  rw [hi0, pow_zero] at hi
  exact orderOf_eq_one_iff.mp hi

theorem exists_pComponent_centralizer_mk_of_center_eq_bot {M : Type} [Group M] [Finite M]
    (hZ2 : IsPGroup 2 (center M)) {x : M} {J : Subgroup ↥(centralizer ({x} : Set M))}
    (hJ : IsPComponent 2 J) (hZJ : center (↥J ⧸ pPrimeCore 2 ↥J) = ⊥) :
    ∃ L : Subgroup ↥(centralizer ({QuotientGroup.mk' (center M) x} : Set (M ⧸ center M))),
      IsPComponent 2 L ∧ Nonempty (↥J ≃* ↥L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (center M) with hπ
  set s : M ⧸ center M := π x with hs
  have hmem : ∀ c : ↥(centralizer ({x} : Set M)), π c ∈ centralizer ({s} : Set (M ⧸ center M)) := by
    intro c
    have hcx : (c : M) * x = x * c := mem_centralizer_singleton_iff.mp c.2
    rw [mem_centralizer_singleton_iff, hs, ← map_mul, ← map_mul, hcx]
  let φ : ↥(centralizer ({x} : Set M)) →* ↥(centralizer ({s} : Set (M ⧸ center M))) :=
    (π.comp (centralizer ({x} : Set M)).subtype).codRestrict _ hmem
  have hφ : ∀ c, ((φ c : ↥(centralizer ({s} : Set (M ⧸ center M)))) : M ⧸ center M) = π c :=
    fun _ => rfl
  have hnorm : φ.range.Normal := by
    refine ⟨?_⟩
    rintro _ ⟨c, rfl⟩ y
    obtain ⟨m, hm⟩ := QuotientGroup.mk'_surjective (center M) (y : M ⧸ center M)
    have hy : s * (y : M ⧸ center M) * s⁻¹ = y := by
      rw [← mem_centralizer_singleton_iff.mp y.2, mul_inv_cancel_right]
    have hz : x * m * x⁻¹ * m⁻¹ ∈ center M := by
      rw [← QuotientGroup.eq_one_iff]
      change π (x * m * x⁻¹ * m⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hm, ← hs, hy, mul_inv_cancel]
    refine ⟨⟨m * c * m⁻¹, conj_mem_centralizer_of_comm_mem_center hz c.2⟩, ?_⟩
    apply Subtype.ext
    rw [hφ]
    change π (m * c * m⁻¹) = (y : M ⧸ center M) * π c * (y : M ⧸ center M)⁻¹
    rw [map_mul, map_mul, map_inv, hm]
  obtain ⟨hJsn, hJres, hJqq⟩ :=
    (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 J).1 hJ
  have hinj : Function.Injective (φ.domRestrict J) := by
    refine (injective_iff_map_eq_one _).mpr fun j hj => ?_
    have hjZ : ((j : ↥(centralizer ({x} : Set M))) : M) ∈ center M := by
      have h1 := congrArg Subtype.val hj
      exact (QuotientGroup.eq_one_iff _).1 h1
    have hjc : (j : ↥(centralizer ({x} : Set M))) ∈ center ↥(centralizer ({x} : Set M)) :=
      mem_center_iff.mpr fun y => Subtype.ext ((mem_center_iff.mp hjZ) _)
    obtain ⟨k, hk⟩ := hZ2 ⟨_, hjZ⟩
    refine eq_one_of_mem_center_of_center_quot_eq_bot hZJ hjc (k := k) ?_
    apply Subtype.ext
    have h1 := congrArg Subtype.val hk
    rw [Subgroup.coe_pow] at h1
    rw [Subgroup.coe_pow]
    exact h1
  let eJ : ↥J ≃* ↥(J.map φ) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (MonoidHom.domRestrict_range J φ))
  have hsn : (J.map φ).IsSubnormal := by
    have h1 : (J.map φ.rangeRestrict).IsSubnormal := hJsn.map φ.rangeRestrict_surjective
    have h2 := h1.trans' hnorm.isSubnormal
    rwa [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict] at h2
  refine ⟨J.map φ, ?_, ⟨eJ⟩⟩
  refine (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 _).2
    ⟨hsn, primeResidual_eq_top_of_mulEquiv eJ hJres, ?_⟩
  exact LocalCores.isQuasisimple_of_mulEquiv
    (QuotientGroup.congr _ _ eJ (pPrimeCore_map_iso 2 eJ)) hJqq

@[expose] def InvolutionCentralizersNoTwoComponent (S : Type*) [Group S] : Prop :=
  ∀ s : S, orderOf s = 2 → ∀ L : Subgroup ↥(centralizer ({s} : Set S)), ¬ IsPComponent 2 L

theorem InvolutionCentralizersNoTwoComponent.of_mulEquiv {S T : Type*} [Group S] [Group T]
    (e : S ≃* T) (h : InvolutionCentralizersNoTwoComponent T) :
    InvolutionCentralizersNoTwoComponent S := by
  intro t ht B hB
  let φ : centralizer ({t} : Set S) ≃* centralizer ({e t} : Set T) :=
    ((centralizer ({t} : Set S)).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (UnbalancingLocal.map_centralizer_singleton_mulEquiv e t))
  exact h (e t) (by rw [MulEquiv.orderOf_eq]; exact ht) _
    (LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 φ hB)

theorem not_isPComponent_two_of_isCharacteristicP {C : Type*} [Group C] [Finite C]
    (hC : IsCharacteristicP 2 C) (L : Subgroup C) : ¬ IsPComponent 2 L := by
  intro hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : pPrimeCore 2 C = ⊥ := pPrimeCore_eq_bot_of_isCharacteristicP C 2 hC
  obtain ⟨hs, -, hq⟩ :=
    (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 L).1 hL
  have hcore : pPrimeCore 2 L = ⊥ := by
    have h1 := UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hs
    rw [hO, inf_bot_eq] at h1
    exact (map_eq_bot_iff_of_injective _ L.subtype_injective).mp h1
  have e : L ⧸ pPrimeCore 2 L ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  exact LieType.Chevalley.RootWeightDatum.not_isComponent_of_isCharacteristicP hC L
    ⟨(LocalAnalysis.ComponentInitial.isQuasisimple_congr e).1 hq, hs⟩

theorem not_isPComponent_two_of_isSolvable {C : Type*} [Group C] [Finite C]
    [Group.IsSolvable C] (L : Subgroup C) : ¬ IsPComponent 2 L := by
  intro hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hq⟩ :=
    (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 L).1 hL
  exact Sporadic.Schreier.Tits.not_isQuasisimple_of_solvable _ hq

theorem isCharacteristicP_two_of_hasTwoCore {C : Type*} [Group C]
    (h : Sporadic.Schreier.Tits.HasTwoCore C) : IsCharacteristicP 2 C := by
  obtain ⟨J, hJn, hJ2, hJC⟩ := h
  have hle : J ≤ pCore 2 C := le_sSup ⟨hJn, hJ2⟩
  exact (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hle)).trans (hJC.trans hle)

theorem hasTwoCore_centralizer_of_conj_kernel {G : Type*} [Group G] {Γ : Subgroup G}
    {t r x : G} (ht : t ∈ Γ) (hx : x ∈ Γ) (hr : x * t * x⁻¹ = r) {N : Subgroup G}
    (hNC : N ≤ Γ ⊓ centralizer {r}) (hN2 : IsPGroup 2 N)
    (hnorm : ∀ g ∈ Γ ⊓ centralizer {r}, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hcen : ∀ g ∈ Γ ⊓ centralizer {r}, (∀ n ∈ N, g * n = n * g) → g ∈ N) :
    Sporadic.Schreier.Tits.HasTwoCore ↥(centralizer ({⟨t, ht⟩} : Set Γ)) := by
  set C := centralizer ({⟨t, ht⟩} : Set Γ) with hCdef
  let f : C →* G := (MulAut.conj x).toMonoidHom.comp (Γ.subtype.comp C.subtype)
  have hf : Function.Injective f :=
    (MulAut.conj x).injective.comp (Γ.subtype_injective.comp C.subtype_injective)
  set Q : Subgroup C := N.comap f with hQ
  have hmemQ : ∀ c : C, c ∈ Q ↔ x * ((c : Γ) : G) * x⁻¹ ∈ N := fun c => Iff.rfl
  have hconjC : ∀ c : C, x * ((c : Γ) : G) * x⁻¹ ∈ Γ ⊓ centralizer {r} := fun c => by
    have hct : ((c : Γ) : G) * t = t * ((c : Γ) : G) :=
      congrArg Subtype.val (mem_centralizer_singleton_iff.1 c.2)
    refine mem_inf.2 ⟨mul_mem (mul_mem hx (c : Γ).2) (inv_mem hx),
      mem_centralizer_singleton_iff.2 ?_⟩
    rw [← hr]
    calc x * ((c : Γ) : G) * x⁻¹ * (x * t * x⁻¹) = x * (((c : Γ) : G) * t) * x⁻¹ := by group
      _ = x * (t * ((c : Γ) : G)) * x⁻¹ := by rw [hct]
      _ = x * t * x⁻¹ * (x * ((c : Γ) : G) * x⁻¹) := by group
  refine ⟨Q, ⟨fun q hq c => ?_⟩, hN2.comap_of_injective f hf, fun c hc => ?_⟩
  ·
    rw [hmemQ] at hq ⊢
    have h := hnorm _ (hconjC c) _ hq
    have e : x * (((c * q * c⁻¹ : C) : Γ) : G) * x⁻¹ = x * ((c : Γ) : G) * x⁻¹ *
        (x * ((q : Γ) : G) * x⁻¹) * (x * ((c : Γ) : G) * x⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact h
  ·
    rw [hmemQ]
    refine hcen _ (hconjC c) fun n hn => ?_
    obtain ⟨hnΓ, hnr⟩ := mem_inf.1 (hNC hn)
    have hnr' : n * r = r * n := mem_centralizer_singleton_iff.1 hnr
    have hyΓ : x⁻¹ * n * x ∈ Γ := mul_mem (mul_mem (inv_mem hx) hnΓ) hx
    have hyC : (⟨x⁻¹ * n * x, hyΓ⟩ : Γ) ∈ C := by
      rw [hCdef, mem_centralizer_singleton_iff]
      apply Subtype.ext
      change x⁻¹ * n * x * t = t * (x⁻¹ * n * x)
      rw [← hr] at hnr'
      calc x⁻¹ * n * x * t = x⁻¹ * (n * (x * t * x⁻¹)) * x := by group
        _ = x⁻¹ * (x * t * x⁻¹ * n) * x := by rw [hnr']
        _ = t * (x⁻¹ * n * x) := by group
    have hyQ : (⟨⟨x⁻¹ * n * x, hyΓ⟩, hyC⟩ : C) ∈ Q := by
      rw [hmemQ]
      change x * (x⁻¹ * n * x) * x⁻¹ ∈ N
      rw [show x * (x⁻¹ * n * x) * x⁻¹ = n by group]
      exact hn
    have h : x⁻¹ * n * x * ((c : Γ) : G) = ((c : Γ) : G) * (x⁻¹ * n * x) :=
      congrArg (fun z : C => ((z : Γ) : G)) (mem_centralizer_iff.1 hc _ hyQ)
    calc x * ((c : Γ) : G) * x⁻¹ * n = x * (((c : Γ) : G) * (x⁻¹ * n * x)) * x⁻¹ := by group
      _ = x * (x⁻¹ * n * x * ((c : Γ) : G)) * x⁻¹ := by rw [h]
      _ = n * (x * ((c : Γ) : G) * x⁻¹) := by group

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
theorem isCharacteristicP_two_centralizer_rootWeightDatum
    {K : Type} [Field K] [Finite K] [CharP K 2] (D : RootWeightDatum K) {c : D.group}
    (hc2 : c ^ 2 = 1) (hc : c ≠ 1) :
    IsCharacteristicP 2 ↥(centralizer ({c} : Set D.group)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := zpowers c with hQ
  have hQp : IsPGroup 2 Q := by
    intro x
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 x.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← hn, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      show ((2 : ℕ) : ℤ) = 2 from rfl, zpow_two, ← sq, hc2, one_zpow, Subgroup.coe_one]
  have hQ1 : Q ≠ ⊥ := fun h => hc (by
    have : c ∈ Q := Subgroup.mem_zpowers c
    rw [h, Subgroup.mem_bot] at this
    exact this)
  have hcent : centralizer (Q : Set D.group) = centralizer ({c} : Set D.group) := by
    rw [hQ, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  obtain ⟨hchar, -⟩ := D.defining_characteristic_root_local_groups_component_free 2 Q hQp hQ1
    (centralizer (Q : Set D.group)) (Or.inr rfl)
  rw [hcent] at hchar
  exact hchar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
theorem involutionCentralizersNoTwoComponent_adjointGroup
    {τ : Tag} {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ f) :
    InvolutionCentralizersNoTwoComponent (adjointGroup τ K) := by
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have := finite_modGL (τ := τ) (K := K)
  intro c hc L
  have hc2 : c ^ 2 = 1 := by rw [← hc, pow_orderOf_eq_one]
  have hc1 : c ≠ 1 := fun h => by
    rw [h, orderOf_one] at hc
    exact absurd hc (by norm_num)
  exact not_isPComponent_two_of_isCharacteristicP
    (isCharacteristicP_two_centralizer_rootWeightDatum (RootWeightDatum.ordinary τ) hc2 hc1) L

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
theorem involutionCentralizersNoTwoComponent_graphFixedRootGroup
    (t : TwistTag) {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ t.order) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    InvolutionCentralizersNoTwoComponent (graphFixedRootGroup t K σ.toRingHom) := by
  obtain ⟨σ', hσ', hord, -⟩ := finite_graph_field_parameter_fields t Nat.prime_two hf K hK
  have hσσ' : σ = σ' := RingEquiv.ext fun c => by rw [hσ, hσ']
  have hσo : σ ^ t.order = 1 := by
    rw [hσσ', ← hord]
    exact pow_orderOf_eq_one σ'
  have hm := t.order_pos
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)))
      (show Nat.card K = 2 ^ (f * t.order) by rw [hK, ← pow_mul])
  have := finite_modGL (τ := t.tag) (K := K)
  intro c hc L
  have hc2 : c ^ 2 = 1 := by rw [← hc, pow_orderOf_eq_one]
  have hc1 : c ≠ 1 := fun h => by
    rw [h, orderOf_one] at hc
    exact absurd hc (by norm_num)
  exact not_isPComponent_two_of_isCharacteristicP
    (isCharacteristicP_two_centralizer_rootWeightDatum (RootWeightDatum.fixed t σ hσo) hc2
      hc1) L

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
theorem involutionCentralizersNoTwoComponent_chevalley
    {S : Type} [Group S] {t : StatedLieTag} (ht : t ∈ chevalleyExceptionalTags) {f : ℕ}
    (h : ChevalleyExceptionalModel S t 2 f) : InvolutionCentralizersNoTwoComponent S := by
  have hf : 1 ≤ f := h.1.2.1
  simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2 h.2
    exact .of_mulEquiv e (involutionCentralizersNoTwoComponent_adjointGroup hf hK)
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 h.2
    exact .of_mulEquiv e (involutionCentralizersNoTwoComponent_adjointGroup hf hK)
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 h.2
    exact .of_mulEquiv e (involutionCentralizersNoTwoComponent_adjointGroup hf hK)
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E7 h.2
    exact .of_mulEquiv e (involutionCentralizersNoTwoComponent_adjointGroup hf hK)
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E8 h.2
    exact .of_mulEquiv e (involutionCentralizersNoTwoComponent_adjointGroup hf hK)
  · obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
      exists_mulEquiv_graphFixedRootGroup_card TwistTag.E6 Nat.prime_two hf h.2
    exact .of_mulEquiv e (involutionCentralizersNoTwoComponent_graphFixedRootGroup _ hf hK σ hσ)
  · obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
      exists_mulEquiv_graphFixedRootGroup_card TwistTag.D4 Nat.prime_two hf h.2
    exact .of_mulEquiv e (involutionCentralizersNoTwoComponent_graphFixedRootGroup _ hf hK σ hσ)

theorem involutionCentralizersNoTwoComponent_suzuki {S : Type}
    [Group S] [Finite S] {p f : ℕ} (h : SuzukiModel S p f) :
    InvolutionCentralizersNoTwoComponent S := by
  obtain ⟨-, a, -, K, _, _, hf, hK, ⟨e⟩⟩ := h
  have : Finite (suzukiGroup a K) := Finite.of_equiv _ e.toEquiv
  refine .of_mulEquiv e fun t ht L => ?_
  have := Sporadic.Schreier.Tits.suzuki_involution_centralizer_solvable (by rw [hK, hf]) t ht
  exact not_isPComponent_two_of_isSolvable L

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag in
theorem involutionCentralizersNoTwoComponent_twistedF4
    {S : Type} [Group S] {p f : ℕ} (h : ReeTitsModel S .twistedF4 p f) :
    InvolutionCentralizersNoTwoComponent S := by
  obtain ⟨-, -, -, hp2, -, hiso⟩ := large_Ree_model_Schreier _ p f h
  subst hp2
  obtain ⟨hadm, a, hfa, K, _, _, hK, hw⟩ := h
  have : CharP K F4.prime :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have hf3 : 3 ≤ f := hadm.2.2.2.2.2
  have ha : 1 ≤ a := by omega
  obtain ⟨e⟩ := hiso a K hfa hK hw
  have := finite_modGL (τ := F4.tag) (K := K)
  refine .of_mulEquiv e fun t ht L => ?_
  have ht2 : orderOf (t : ModGL F4.tag K) = 2 := by rw [Subgroup.orderOf_coe, ht]
  have htt : (t : ModGL F4.tag K) ^ 2 = 1 := by rw [← ht2, pow_orderOf_eq_one]
  have ht1 : (t : ModGL F4.tag K) ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  obtain ⟨r, x, hx, hxt, N, hNC, hN2, hn, hc⟩ :=
    LargeReeInvolution.exists_kernel ha hK' t.2 htt ht1
  exact not_isPComponent_two_of_isCharacteristicP (isCharacteristicP_two_of_hasTwoCore
    (hasTwoCore_centralizer_of_conj_kernel t.2 hx hxt hNC hN2 hn hc)) L

open CFSG.Sporadic.Schreier.Tits in
theorem involutionCentralizersNoTwoComponent_tits
    {S : Type} [Group S] {p f : ℕ} (h : ReeTitsModel S .Tits p f) :
    InvolutionCentralizersNoTwoComponent S := by
  obtain ⟨e⟩ := titsModelEquiv _ p f h
  refine .of_mulEquiv e fun x hx L => ?_
  have hz : HasTwoCore (Subgroup.centralizer {titsZD}) :=
    hasTwoCore_centralizer_of_map_eq titsD_centralizer_z hasTwoCore_titsH
  have ht : HasTwoCore (Subgroup.centralizer {titsTD}) :=
    hasTwoCore_centralizer_of_map_eq titsD_centralizer_t.1.symm hasTwoCore_titsCt
  rcases titsD_involution_conj x hx with h | h
  · exact not_isPComponent_two_of_isCharacteristicP
      (isCharacteristicP_two_of_hasTwoCore (hasTwoCore_centralizer_of_conj h hz)) L
  · exact not_isPComponent_two_of_isCharacteristicP
      (isCharacteristicP_two_of_hasTwoCore (hasTwoCore_centralizer_of_conj h ht)) L

theorem involutionCentralizersNoTwoComponent_even
    {S : Type} [Group S] [Finite S]
    (h : (∃ (t : StatedLieTag) (f : ℕ), t ∈ chevalleyExceptionalTags ∧
        ChevalleyExceptionalModel S t 2 f) ∨
      (∃ (p f : ℕ), ReeTitsModel S .twistedF4 p f ∨ ReeTitsModel S .Tits p f) ∨
      ∃ p f : ℕ, SuzukiModel S p f) :
    InvolutionCentralizersNoTwoComponent S := by
  rcases h with ⟨t, f, ht, hm⟩ | ⟨p, f, hm | hm⟩ | ⟨p, f, hm⟩
  · exact involutionCentralizersNoTwoComponent_chevalley ht hm
  · exact involutionCentralizersNoTwoComponent_twistedF4 hm
  · exact involutionCentralizersNoTwoComponent_tits hm
  · exact involutionCentralizersNoTwoComponent_suzuki hm

theorem false_of_involutionCentralizersNoTwoComponent {M : Type} [Group M] [Finite M]
    (hZ2 : IsPGroup 2 (center M)) (hS : InvolutionCentralizersNoTwoComponent (M ⧸ center M))
    {x : M} (hx : x * x = 1) (hxZ : x ∉ center M) {J : Subgroup ↥(centralizer ({x} : Set M))}
    (hJ : IsPComponent 2 J) (hZJ : center (↥J ⧸ pPrimeCore 2 ↥J) = ⊥) : False := by
  obtain ⟨L, hL, -⟩ := exists_pComponent_centralizer_mk_of_center_eq_bot hZ2 hJ hZJ
  have hs1 : QuotientGroup.mk' (center M) x ≠ 1 := fun h =>
    hxZ ((QuotientGroup.eq_one_iff x).1 h)
  have hs2 : orderOf (QuotientGroup.mk' (center M) x) = 2 :=
    orderOf_eq_prime (by rw [sq, ← map_mul, hx, map_one]) hs1
  exact hS _ hs2 L hL

theorem false_of_even_exceptional
    {M : Type} [Group M] [Finite M] (hZ2 : IsPGroup 2 (center M))
    (hS : (∃ (t : StatedLieTag) (f : ℕ), t ∈ chevalleyExceptionalTags ∧
        ChevalleyExceptionalModel (M ⧸ center M) t 2 f) ∨
      (∃ (p f : ℕ), ReeTitsModel (M ⧸ center M) .twistedF4 p f ∨
        ReeTitsModel (M ⧸ center M) .Tits p f) ∨
      ∃ p f : ℕ, SuzukiModel (M ⧸ center M) p f)
    {x : M} (hx : x * x = 1) (hxZ : x ∉ center M) {J : Subgroup ↥(centralizer ({x} : Set M))}
    (hJ : IsPComponent 2 J) {p f : ℕ} (hJm : LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 p f) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJs : IsSimpleGroup (↥J ⧸ pPrimeCore 2 ↥J) := FooteLit.isSimpleGroup_of_lieModel_psl_two hJm
  obtain ⟨-, -, hJqq⟩ :=
    (CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 J).1 hJ
  exact false_of_involutionCentralizersNoTwoComponent hZ2
    (involutionCentralizersNoTwoComponent_even hS) hx hxZ hJ
    (center_eq_bot_of_isQuasisimple_of_isSimpleGroup hJqq hJs)

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
