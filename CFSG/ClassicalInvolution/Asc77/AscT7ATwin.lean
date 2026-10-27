module

public import CFSG.ClassicalInvolution.Asc77.AscT7ASetup
public import CFSG.ClassicalInvolution.Asc77.AscE184Quot

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

namespace T7A

omit [Finite G] in
theorem card_sup_mul_card_inf {A C : Subgroup G} (hC : C ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (C ⊔ A : Subgroup G) * Nat.card (A ⊓ C : Subgroup G) =
      Nat.card A * Nat.card C := by
  let := Subgroup.normal_subgroupOf_of_le_normalizer hC
  let := Subgroup.normal_subgroupOf_sup_of_le_normalizer hC
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient C A hC
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf C)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf (C ⊔ A))
  have h3 : Nat.card (A.subgroupOf (C ⊔ A)) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have h4 : Nat.card (A.subgroupOf C) = Nat.card (A ⊓ C : Subgroup G) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [h2, h3, h1, h4, Nat.card_congr e.toEquiv]
  ring

omit [Finite G] in
theorem le_normalizer_of_commutes {A B : Subgroup G} (h : Commutes A B) :
    B ≤ Subgroup.normalizer (A : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : y * x * y⁻¹ = x := by
      have := h x hx y hy
      calc y * x * y⁻¹ = (x * y) * y⁻¹ := by rw [this]
        _ = x := by group
    rw [this]
    exact hx
  · intro hx
    have h2 := h _ hx y⁻¹ (B.inv_mem hy)
    have : x = y * x * y⁻¹ := by
      calc x = y⁻¹ * (y * x * y⁻¹) * y := by group
        _ = (y * x * y⁻¹) * y⁻¹ * y := by rw [← h2]
        _ = y * x * y⁻¹ := by group
    rw [this]
    exact hx

theorem isSylow2In_sup_of_twin (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω) {K K' R R' : Subgroup G}
    {z : G} (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hne : K' ≠ K) (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) (hR : IsSylow2In R K) (hR' : IsSylow2In R' K')
    (hc : Commutes R R') : IsSylow2In (R ⊔ R') (K ⊔ K') := by
  have hKN : K' ≤ Subgroup.normalizer (K : Set G) := hΩ.le_normalizer_of_twin hK' hK hne hz' hz
  have hprod := card_sup_mul_card_inf hKN
  rw [sup_comm] at hprod
  have hRset : R ∈ RSet Ω := mem_RSet_of_isSylow2In hK hR
  have hR'set : R' ∈ RSet Ω := mem_RSet_of_isSylow2In hK' hR'
  have h8 : 8 ≤ Nat.card R := hΩ.eight_le_of_mem_RSet hp hRset
  have h8' : 8 ≤ Nat.card R' := hΩ.eight_le_of_mem_RSet hp hR'set
  have hzR : z ∈ R := mem_of_isUniqueInvolution_of_isPGroup hz hR.1 hR.2.1 (by omega)
  have hzR' : z ∈ R' := mem_of_isUniqueInvolution_of_isPGroup hz' hR'.1 hR'.2.1 (by omega)
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have hN0 : Nat.card ↥(K ⊓ K') ≠ 0 := Nat.card_pos.ne'
  have hinfK : (Nat.card ↥(K ⊓ K')).factorization 2 = 1 := by
    have hdvd : 2 ∣ Nat.card ↥(K ⊓ K') := by
      have := Subgroup.orderOf_dvd_natCard (K ⊓ K') (x := z) ⟨hz.mem, hz'.mem⟩
      rwa [hz2] at this
    have h1 : 1 ≤ (Nat.card ↥(K ⊓ K')).factorization 2 :=
      (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hN0).mp hdvd
    have h2 : padicValNat 2 (Nat.card ↥(K ⊓ K')) ≤ 1 :=
      (hΩ.omega4 K hK K' hK' hne.symm).1
    rw [Nat.factorization_def _ Nat.prime_two] at h1 ⊢
    omega
  have hinfR : Nat.card ↥(R ⊓ R') = 2 := by
    refine le_antisymm ?_ ?_
    · exact hΩ.card_le_two_of_le_inf hK hK' hne.symm (hR.2.1.to_le inf_le_left)
        (inf_le_left.trans hR.1) (inf_le_right.trans hR'.1)
    · have h1 : Subgroup.zpowers z ≤ R ⊓ R' := Subgroup.zpowers_le.mpr ⟨hzR, hzR'⟩
      have := Subgroup.card_le_of_le h1
      rwa [Nat.card_zpowers, hz2] at this
  have hRN : R' ≤ Subgroup.normalizer (R : Set G) := le_normalizer_of_commutes hc
  have hprodR := card_sup_mul_card_inf hRN
  rw [hinfR] at hprodR
  have ha := natCard_eq_pow_of_isSylow2In hR
  have hb := natCard_eq_pow_of_isSylow2In hR'
  have hQ0 : Nat.card ↥(K ⊔ K') ≠ 0 := Nat.card_pos.ne'
  have hK0 : Nat.card ↥K ≠ 0 := Nat.card_pos.ne'
  have hK'0 : Nat.card ↥K' ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card ↥(K ⊔ K')).factorization 2 + 1 =
      (Nat.card ↥K).factorization 2 + (Nat.card ↥K').factorization 2 := by
    have := congrArg (fun n => n.factorization 2) hprod
    simp only [Nat.factorization_mul hQ0 hN0, Nat.factorization_mul hK0 hK'0, Finsupp.add_apply,
      hinfK] at this
    exact this
  have hRR : Nat.card ↥(R ⊔ R') = 2 ^ (Nat.card ↥(K ⊔ K')).factorization 2 := by
    have h1 : Nat.card ↥(R' ⊔ R) = Nat.card ↥(R ⊔ R') := by rw [sup_comm]
    rw [h1, ha, hb] at hprodR
    have h2 : 2 ^ ((Nat.card ↥(K ⊔ K')).factorization 2 + 1) =
        2 ^ (Nat.card ↥K).factorization 2 * 2 ^ (Nat.card ↥K').factorization 2 := by
      rw [hfac, pow_add]
    rw [pow_succ] at h2
    have := hprodR.trans h2.symm
    have h3 : 0 < 2 := by norm_num
    exact Nat.eq_of_mul_eq_mul_right h3 (by linarith)
  have hP2 : IsPGroup 2 ↥(R ⊔ R') := hR.2.1.to_sup_of_normal_right' hR'.2.1
    (le_normalizer_of_commutes hc.symm)
  refine ⟨sup_le_sup hR.1 hR'.1, hP2, fun V hVQ hV2 hle => ?_⟩
  obtain ⟨n, hn⟩ := hV2.exists_card_eq
  have hdvd : Nat.card ↥V ∣ Nat.card ↥(K ⊔ K') := Subgroup.card_dvd_of_le hVQ
  rw [hn] at hdvd
  have hnle : n ≤ (Nat.card ↥(K ⊔ K')).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hQ0).mp hdvd
  have hcard : Nat.card ↥V ≤ Nat.card ↥(R ⊔ R') := by
    rw [hn, hRR]
    exact Nat.pow_le_pow_right (by norm_num) hnle
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

omit [Finite G] in
theorem conjSub_sup_eq (g : G) (A B : Subgroup G) :
    conjSub g (A ⊔ B) = conjSub g A ⊔ conjSub g B := by
  unfold conjSub
  exact Subgroup.map_sup _ _ _

theorem exists_conj_sylow_pair (hp : p ≠ 2) (hΩ : HypOmegaMod p f Ω)
    {K K' R R' R₀ R₀' : Subgroup G} {z : G} (hK : K ∈ Ω) (hK' : K' ∈ Ω) (hne : K' ≠ K)
    (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z) (hR : IsSylow2In R K)
    (hR' : IsSylow2In R' K') (hc : Commutes R R') (hR₀ : IsSylow2In R₀ K)
    (hR₀' : IsSylow2In R₀' K') (hc₀ : Commutes R₀ R₀') :
    ∃ g ∈ K ⊔ K', conjSub g R₀ = R ∧ conjSub g R₀' = R' := by
  have hQ := isSylow2In_sup_of_twin hp hΩ hK hK' hne hz hz' hR hR' hc
  have hQ₀ := isSylow2In_sup_of_twin hp hΩ hK hK' hne hz hz' hR₀ hR₀' hc₀
  obtain ⟨g, hgQ, hg⟩ := exists_conjSub_eq_of_isSylow2In hQ₀ hQ
  have hKN : K' ≤ Subgroup.normalizer (K : Set G) := hΩ.le_normalizer_of_twin hK' hK hne hz' hz
  have hK'N : K ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_twin hK hK' hne.symm hz hz'
  have hgK : conjSub g K = K :=
    mem_normalizer_iff_conjSub_eq.mp ((sup_le Subgroup.le_normalizer hKN) hgQ)
  have hgK' : conjSub g K' = K' :=
    mem_normalizer_iff_conjSub_eq.mp ((sup_le hK'N Subgroup.le_normalizer) hgQ)
  have hP2 : IsPGroup 2 ↥(R ⊔ R') := hQ.2.1
  refine ⟨g, hgQ, ?_, ?_⟩
  · have h1 : IsSylow2In (conjSub g R₀) K := by
      have := hR₀.conj g
      rwa [hgK] at this
    have h1le : conjSub g R₀ ≤ R ⊔ R' := by
      rw [← hg, conjSub_sup_eq]
      exact le_sup_left
    have hT2 : IsPGroup 2 ↥((R ⊔ R') ⊓ K) := hP2.to_le inf_le_left
    have hTR : (R ⊔ R') ⊓ K = R := hR.eq_of_le hT2 inf_le_right (le_inf le_sup_left hR.1)
    have h2 : conjSub g R₀ ≤ R := by
      rw [← hTR]
      exact le_inf h1le h1.1
    exact Subgroup.eq_of_le_of_card_ge h2 (h1.natCard_eq hR).ge
  · have h1 : IsSylow2In (conjSub g R₀') K' := by
      have := hR₀'.conj g
      rwa [hgK'] at this
    have h1le : conjSub g R₀' ≤ R ⊔ R' := by
      rw [← hg, conjSub_sup_eq]
      exact le_sup_right
    have hT2 : IsPGroup 2 ↥((R ⊔ R') ⊓ K') := hP2.to_le inf_le_left
    have hTR : (R ⊔ R') ⊓ K' = R' := hR'.eq_of_le hT2 inf_le_right (le_inf le_sup_right hR'.1)
    have h2 : conjSub g R₀' ≤ R' := by
      rw [← hTR]
      exact le_inf h1le h1.1
    exact Subgroup.eq_of_le_of_card_ge h2 (h1.natCard_eq hR').ge

end T7A

theorem exists_twinFrameData_of_sylows (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K K' J R₁ R₂ : Subgroup G} {z t : G} (hK : K ∈ Ω) (hz : IsUniqueInvolution K z)
    (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) (hJ : J ∈ omegaOfSet Ω (twinSet Ω K))
    (ht : IsUniqueInvolution J t) (hR₁ : IsSylow2In R₁ K) (hR₂ : IsSylow2In R₂ K')
    (hc : Commutes R₁ R₂) :
    ∃ g ∈ K ⊔ K', ∃ W : Subgroup G, conjSub g J ∈ omegaOfSet Ω (twinSet Ω K) ∧
      IsUniqueInvolution (conjSub g J) (g * t * g⁻¹) ∧ W ∈ WSet Ω ∧ z ∈ W ∧ g * t * g⁻¹ ∈ W ∧
      ∀ x ∈ R₁, ∀ y ∈ R₂, orderOf x = 4 → orderOf y = 4 →
        TwinFrameData Ω K K' z (x * y) (conjSub g J) (g * t * g⁻¹) := by
  have hK'Ω : K' ∈ Ω := hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  have hJΩ : J ∈ Ω := hJ.1
  obtain ⟨S₀, R₀, R₀', T₀, hR₀, hR₀', hT₀, hR₀S, hR₀'S, hT₀S, hc₀, hRT₀, hR'T₀⟩ :=
    exists_twinSylow hp hq hΩ hK hz hK' hne hJ
  obtain ⟨g, hgQ, hgR, hgR'⟩ := T7A.exists_conj_sylow_pair hp hΩ hK hK'Ω hne hz hzK' hR₁ hR₂ hc
    hR₀ hR₀' hc₀
  have hKN : K' ≤ Subgroup.normalizer (K : Set G) := hΩ.le_normalizer_of_twin hK'Ω hK hne hzK' hz
  have hgK : conjSub g K = K :=
    mem_normalizer_iff_conjSub_eq.mp ((sup_le Subgroup.le_normalizer hKN) hgQ)
  have hgiK : conjSub g⁻¹ K = K :=
    mem_normalizer_iff_conjSub_eq.mp (Subgroup.inv_mem _ ((sup_le Subgroup.le_normalizer hKN) hgQ))
  have hJΩ' : conjSub g J ∈ Ω := hΩ.conjInvariant g J hJΩ
  have ht' : IsUniqueInvolution (conjSub g J) (g * t * g⁻¹) := ht.conj g
  have hJ' : conjSub g J ∈ omegaOfSet Ω (twinSet Ω K) := by
    refine ⟨hJΩ', fun L hL => ?_⟩
    have hL' : conjSub g⁻¹ L ∈ twinSet Ω K := by
      have := twinSet_conj hΩ.conjInvariant hL g⁻¹
      rwa [hgiK] at this
    have := omegaNbr_conj hΩ.conjInvariant (hJ.2 _ hL') g
    rwa [conjSub_conjSub_inv] at this
  have hTsyl : IsSylow2In (conjSub g T₀) (conjSub g J) := hT₀.conj g
  have hT8 : 8 ≤ Nat.card ↥(conjSub g T₀) :=
    hΩ.eight_le_of_mem_RSet hp (mem_RSet_of_isSylow2In hJΩ' hTsyl)
  have htT : g * t * g⁻¹ ∈ conjSub g T₀ :=
    mem_of_isUniqueInvolution_of_isPGroup ht' hTsyl.1 hTsyl.2.1 (by omega)
  have hcRT : Commutes R₁ (conjSub g T₀) := by
    have := hRT₀.conjSub g
    rwa [hgR] at this
  have hcR'T : Commutes R₂ (conjSub g T₀) := by
    have := hR'T₀.conjSub g
    rwa [hgR'] at this
  obtain ⟨S₁, hS₁⟩ : ∃ S₁ : Sylow 2 G, conjSub g (S₀ : Subgroup G) ≤ (S₁ : Subgroup G) :=
    (isPGroup_conjSub g S₀.isPGroup').exists_le_sylow
  have hS₀ : ∀ {A : Subgroup G}, A ≤ (S₀ : Subgroup G) → conjSub g A ≤ (S₁ : Subgroup G) :=
    fun hA => (conjSub_mono hA).trans hS₁
  have hR₁S : R₁ ≤ (S₁ : Subgroup G) := by rw [← hgR]; exact hS₀ hR₀S
  have hTS : conjSub g T₀ ≤ (S₁ : Subgroup G) := hS₀ hT₀S
  obtain ⟨η, hη, hηinv⟩ := exists_invariant_mem_etaSet hp hq hΩ S₁
  have hWmem : (⨆ U ∈ η, U) ∈ WSet Ω := ⟨η, ⟨S₁, hη, hηinv⟩, rfl⟩
  have hzW := exists_mem_eta_of_sylow hp hΩ hη hK hz hR₁ hR₁S
  have htW := exists_mem_eta_of_sylow hp hΩ hη hJΩ' ht' hTsyl hTS
  refine ⟨g, hgQ, ⨆ U ∈ η, U, hJ', ht', hWmem, hzW, htW, ?_⟩
  intro x hx y hy hx4 hy4
  have hxK : x ∈ K := hR₁.1 hx
  have hyK' : y ∈ K' := hR₂.1 hy
  have hsqx : x * x = z := T7A.sq_eq_of_orderOf_four hz hxK hx4
  have hsqy : y * y = z := T7A.sq_eq_of_orderOf_four hzK' hyK' hy4
  have hcxy : x * y = y * x := hc x hx y hy
  have hxK' : x ∉ K' := fun h => T7A.not_mem_inf_of_orderOf_four hΩ hK hK'Ω hne hx4 hxK h
  have hyK : y ∉ K := fun h => T7A.not_mem_inf_of_orderOf_four hΩ hK hK'Ω hne hy4 h hyK'
  have hu2 : (x * y) * (x * y) = 1 := by
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hcxy]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hsqx, hsqy, hz.sq]
  have hu1 : x * y ≠ 1 := by
    intro h
    apply hxK'
    have : x = y⁻¹ := by rw [eq_inv_iff_mul_eq_one]; exact h
    rw [this]
    exact K'.inv_mem hyK'
  have huz : x * y ≠ z := by
    intro h
    apply hxK'
    have : x = z * y⁻¹ := by rw [← h]; group
    rw [this]
    exact K'.mul_mem hzK'.mem (K'.inv_mem hyK')
  have htu : (g * t * g⁻¹) * (x * y) = (x * y) * (g * t * g⁻¹) := by
    have h1 : x * (g * t * g⁻¹) = (g * t * g⁻¹) * x := hcRT x hx _ htT
    have h2 : y * (g * t * g⁻¹) = (g * t * g⁻¹) * y := hcR'T y hy _ htT
    calc (g * t * g⁻¹) * (x * y) = ((g * t * g⁻¹) * x) * y := by group
      _ = (x * (g * t * g⁻¹)) * y := by rw [h1]
      _ = x * ((g * t * g⁻¹) * y) := by group
      _ = x * (y * (g * t * g⁻¹)) := by rw [h2]
      _ = (x * y) * (g * t * g⁻¹) := by group
  exact
    { mem := hK
      hz := hz
      hK' := hK'
      hne := hne
      hu := Subgroup.mul_mem _ (Subgroup.mem_sup_left hxK) (Subgroup.mem_sup_right hyK')
      hu2 := hu2
      hu1 := hu1
      huz := huz
      hJ := hJ'
      ht := ht'
      htu := htu }

end CFSG.ClassicalInvolution.Asc77
