module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigDich
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigFunctor

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

variable {G : Type} [Group G] [Finite G] {N : Subgroup G}

theorem normalizer_le_normalizer_twoLayerIn (X : Subgroup G) :
    normalizer (X : Set G) ≤ normalizer (twoLayerIn X : Set G) := fun g hg => by
  have hg' : X.map (MulAut.conj g).toMonoidHom = X := mem_normalizer_iff_map_conj_eq.mp hg
  refine mem_normalizer_iff_map_conj_eq.mpr ?_
  have h := map_twoLayerIn (MulAut.conj g) X
  rw [hg'] at h
  exact h

omit [Finite G] in
theorem le_normalizer_sup {A B X : Subgroup G} (hA : X ≤ normalizer (A : Set G))
    (hB : X ≤ normalizer (B : Set G)) : X ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) :=
  fun g hg => by
    rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      mem_normalizer_iff_map_conj_eq.mp (hA hg), mem_normalizer_iff_map_conj_eq.mp (hB hg)]

theorem mem_sup_inf_centralizer {M O : Subgroup G} {a : G} (ha2 : orderOf a = 2)
    (haM : a ∈ normalizer (M : Set G)) (haO : a ∈ normalizer (O : Set G))
    (hOM : O ≤ normalizer (M : Set G)) (hO : Odd (Nat.card O)) {x : G} (hx : x ∈ M ⊔ O)
    (hxa : x ∈ centralizer ({a} : Set G)) :
    x ∈ (M ⊓ centralizer ({a} : Set G)) ⊔ (O ⊓ centralizer ({a} : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm, o, ho, rfl⟩ := exists_mul_of_mem_sup_normalizer hOM hx
  have hxa' : a * (m * o) = m * o * a := (mem_centralizer_singleton_iff.mp hxa).symm
  set S : Set G := {y | y ∈ M ∧ m⁻¹ * y ∈ O} with hS
  have hmam : m⁻¹ * (a * m * a⁻¹) ∈ O := by
    have e : m⁻¹ * (a * m * a⁻¹) = o * (a * o⁻¹ * a⁻¹) := by
      have h1 : a * m * a⁻¹ = m * o * (a * o⁻¹ * a⁻¹) := by
        calc a * m * a⁻¹ = a * (m * o) * o⁻¹ * a⁻¹ := by group
          _ = m * o * a * o⁻¹ * a⁻¹ := by rw [hxa']
          _ = m * o * (a * o⁻¹ * a⁻¹) := by group
      rw [h1]
      group
    rw [e]
    exact mul_mem ho ((mem_normalizer_iff.mp haO _).mp (inv_mem ho))
  have hinvS : ∀ y ∈ S, a * y * a⁻¹ ∈ S := by
    rintro y ⟨hyM, hyO⟩
    refine ⟨(mem_normalizer_iff.mp haM y).mp hyM, ?_⟩
    have e : m⁻¹ * (a * y * a⁻¹) = m⁻¹ * (a * m * a⁻¹) * (a * (m⁻¹ * y) * a⁻¹) := by group
    rw [e]
    exact mul_mem hmam ((mem_normalizer_iff.mp haO _).mp hyO)
  set A := zpowers a with hA
  have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha2, pow_one])
  set α : A →* MulAut G := MulAut.conj.comp A.subtype with hα
  have hαS : ∀ g : A, ∀ y ∈ S, α g y ∈ S := by
    rintro ⟨g, hg⟩ y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    show a ^ k * y * (a ^ k)⁻¹ ∈ S
    rw [← zpow_mod_orderOf, ha2]
    have hk : k % (2 : ℕ) = 0 ∨ k % (2 : ℕ) = 1 := by omega
    rcases hk with hk | hk
    · rw [hk, zpow_zero, one_mul, inv_one, mul_one]
      exact hy
    · rw [hk, zpow_one]
      exact hinvS y hy
  have hcard : Nat.card S = Nat.card (O ⊓ M : Subgroup G) := Nat.card_congr
    { toFun := fun y => ⟨m⁻¹ * y.1, Subgroup.mem_inf.mpr ⟨y.2.2, M.mul_mem (M.inv_mem hm) y.2.1⟩⟩
      invFun := fun z => ⟨m * z.1, M.mul_mem hm (Subgroup.mem_inf.mp z.2).2,
        by simpa using (Subgroup.mem_inf.mp z.2).1⟩
      left_inv := fun y => Subtype.ext (by simp)
      right_inv := fun z => Subtype.ext (by simp) }
  have hSodd : ¬ 2 ∣ Nat.card S := by
    rw [hcard]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
        (Nat.coprime_two_left.mpr hO))
  obtain ⟨c, ⟨hcM, hcO⟩, hfix⟩ :=
    CFSG.Semidihedral.Principal.CoprimeFixedPoint.exists_fixed_of_invariant 2 hA2 α S hαS hSodd
  have hca : c ∈ centralizer ({a} : Set G) := by
    have h := hfix ⟨a, mem_zpowers a⟩
    have h' : a * c * a⁻¹ = c := h
    rw [mem_centralizer_singleton_iff]
    calc c * a = a * c * a⁻¹ * a := by rw [h']
      _ = a * c := by group
  have hw : c⁻¹ * (m * o) ∈ O := by
    have e : c⁻¹ * (m * o) = (m⁻¹ * c)⁻¹ * o := by group
    rw [e]
    exact mul_mem (inv_mem hcO) ho
  have hwa : c⁻¹ * (m * o) ∈ centralizer ({a} : Set G) := mul_mem (inv_mem hca) hxa
  have e : m * o = c * (c⁻¹ * (m * o)) := by group
  rw [e]
  exact mul_mem (mem_sup_left ⟨hcM, hca⟩) (mem_sup_right ⟨hw, hwa⟩)

theorem ncard_pumpSet_eq_one (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {K K' : Subgroup G} (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') {t : G} (htK' : t ∈ K')
    (ht2 : orderOf t = 2) : (pumpSet K (centralizer ({t} : Set G))).ncard = 1 := by
  have htQ : t ∈ coreActionKernel K := mem_coreActionKernel_of_ne hK' hK hne.symm htK'
  obtain ⟨M, hM⟩ := pumpSet_nonempty hK htQ ht2
  have hle : (pumpSet K (centralizer ({t} : Set G))).ncard ≤ 1 := by
    by_contra h
    exact false_of_two_le_ncard_pumpSet hq (kStarKProper_of_simpleAmbient hG) hR1 hG
      (fun N' hN' => not_le_solomonKStarOf_top_of_simple hG hN') hN hK' hK hne.symm htK' ht2
      (by omega)
  have hpos := (Set.ncard_pos (Set.toFinite _)).mpr ⟨M, hM⟩
  omega

theorem mem_coreActionKernel_pump (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {K K' : Subgroup G} (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') {e : G} (heK' : e ∈ K')
    (he2 : orderOf e = 2) {a : G} (haQ : a ∈ coreActionKernel K) (hae : a * e = e * a)
    {M : Subgroup G} (hM : M ∈ pumpSet K (centralizer ({e} : Set G))) :
    a ∈ coreActionKernel M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h32 := lemma32FullFor_simple_of_twoPart hq hR1
  set Ce := centralizer ({e} : Set G) with hCe
  set Ke := twoLayerIn (K ⊓ Ce) with hKe
  have haCe : a ∈ Ce := mem_centralizer_singleton_iff.mpr hae
  have h1 := ncard_pumpSet_eq_one hq hR1 hG hN hK hK' hne heK' he2
  obtain ⟨M', hM'⟩ := Set.ncard_eq_one.mp h1
  have hMM' : M = M' := by
    have := hM
    rw [hM'] at this
    exact this
  have haM : a ∈ normalizer (M : Set G) := by
    have hMa := map_conj_mem_pumpSet (le_normalizer haCe) haQ.1 hM
    rw [hM'] at hMa
    have hMa' : M.map (MulAut.conj a).toMonoidHom = M := by rw [hMa, hMM']
    exact mem_normalizer_iff_map_conj_eq.mpr hMa'
  obtain ⟨M₀, hM₀, hsup⟩ := exists_pump_sup_eq hq hR1 hG hN hK hK' hne heK' he2
  have hM₀M : M₀ = M := by
    have := hM₀
    rw [hM'] at this
    rw [this, hMM']
  rw [hM₀M] at hsup
  have hMle : M ≤ oddCoreIn (twoLayerIn Ce) ⊔ Ke := by
    rw [sup_comm, hsup]
    exact le_sup_left
  have heQ : e ∈ coreActionKernel K := mem_coreActionKernel_of_ne hK' hK hne.symm heK'
  obtain ⟨hKe2, -, -, -, -⟩ := pump_facts hK heQ he2
  have hKeK : Ke ≤ K := hKe2.1.trans inf_le_left
  have hLe : Ce ≤ normalizer (twoLayerIn Ce : Set G) := le_normalizer_twoLayerIn Ce
  have hKeL : Ke ≤ twoLayerIn Ce := by
    obtain ⟨-, -, -, h212, -⟩ := pump_facts hK heQ he2
    exact h212.trans (solomonKStarOf_le_twoLayerIn Ce)
  have hOLn : twoLayerIn Ce ≤ normalizer (oddCoreIn (twoLayerIn Ce) : Set G) :=
    le_normalizer_oddCoreIn (twoLayerIn Ce)
  have haOL : a ∈ normalizer (oddCoreIn (twoLayerIn Ce) : Set G) :=
    mem_normalizer_oddCoreIn (hLe haCe)
  have haKe : a ∈ normalizer (Ke : Set G) := by
    have hKC : a ∈ normalizer ((K ⊓ Ce : Subgroup G) : Set G) := by
      rw [mem_normalizer_iff]
      intro y
      rw [mem_inf, mem_inf, mem_normalizer_iff.mp haQ.1 y,
        mem_normalizer_iff.mp (le_normalizer haCe) y]
    exact normalizer_le_normalizer_twoLayerIn _ hKC
  refine ⟨haM, fun m hm => ?_⟩
  obtain ⟨o, ho, k, hk, rfl⟩ := exists_mul_of_mem_sup_normalizer (hKeL.trans hOLn) (hMle hm)
  have e1 : (o * k)⁻¹ * a⁻¹ * (o * k) * a =
      (k⁻¹ * (o⁻¹ * (a⁻¹ * o * a)) * k) * (k⁻¹ * a⁻¹ * k * a) := by group
  have hX : k⁻¹ * (o⁻¹ * (a⁻¹ * o * a)) * k ∈ oddCoreIn Ce := by
    refine oddCoreIn_twoLayerIn_le Ce ?_
    have h1 : a⁻¹ * o * a ∈ oddCoreIn (twoLayerIn Ce) := by
      have := (mem_normalizer_iff.mp (inv_mem haOL) o).mp ho
      simpa [mul_assoc] using this
    have h2 : o⁻¹ * (a⁻¹ * o * a) ∈ oddCoreIn (twoLayerIn Ce) := mul_mem (inv_mem ho) h1
    have := (mem_normalizer_iff.mp (inv_mem (hOLn (hKeL hk))) _).mp h2
    simpa [mul_assoc] using this
  have hY : k⁻¹ * a⁻¹ * k * a ∈ oddCoreIn Ce := by
    have hKO : k⁻¹ * a⁻¹ * k * a ∈ oddCoreIn K := haQ.2 k (hKeK hk)
    have hKe' : k⁻¹ * a⁻¹ * k * a ∈ Ke := by
      have h1 : a⁻¹ * k * a ∈ Ke := by
        have := (mem_normalizer_iff.mp (inv_mem haKe) k).mp hk
        simpa [mul_assoc] using this
      have := mul_mem (inv_mem hk) h1
      simpa [mul_assoc] using this
    have hOK : oddCoreIn K ⊓ Ke ≤ oddCoreIn Ke :=
      inf_le_oddCoreIn (coprime_card_oddCoreIn K) (hKeK.trans (le_normalizer_oddCoreIn K))
    exact oddCoreIn_pump_le h32 hG hN hK hK' hne heK' he2 (hOK ⟨hKO, hKe'⟩)
  have hMem : (o * k)⁻¹ * a⁻¹ * (o * k) * a ∈ M := by
    have h1 : a⁻¹ * (o * k) * a ∈ M := by
      have := (mem_normalizer_iff.mp (inv_mem haM) (o * k)).mp hm
      simpa [mul_assoc] using this
    have := mul_mem (inv_mem hm) h1
    simpa [mul_assoc] using this
  have hOM : oddCoreIn Ce ⊓ M ≤ oddCoreIn M :=
    inf_le_oddCoreIn (coprime_card_oddCoreIn Ce) (hM.1.1.1.trans (le_normalizer_oddCoreIn Ce))
  refine hOM ⟨?_, hMem⟩
  rw [e1]
  exact mul_mem hX hY

theorem exists_pumpSet_subset_pair (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {K K' : Subgroup G} (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') {a : G} (haQ : a ∈ coreActionKernel K)
    (ha2 : orderOf a = 2) {e : G} (heK' : e ∈ K') (he2 : orderOf e = 2) (hae : a * e = e * a) :
    ∃ B : Subgroup G, IsTwoComponentIn B (centralizer ({a} : Set G)) ∧
      ∀ M ∈ pumpSet K (centralizer ({a} : Set G)), M = B ∨ M = conjugate B e := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ca := centralizer ({a} : Set G) with hCa
  set Ce := centralizer ({e} : Set G) with hCe
  set Y := twoLayerIn (K ⊓ Ca) with hYdef
  obtain ⟨hY2, -, -, h212, -⟩ := pump_facts hK haQ ha2
  have hYL : Y ≤ twoLayerIn Ca := h212.trans (solomonKStarOf_le_twoLayerIn Ca)
  have heQ : e ∈ coreActionKernel K := mem_coreActionKernel_of_ne hK' hK hne.symm heK'
  have heCa : e ∈ Ca := mem_centralizer_singleton_iff.mpr hae.symm
  have haCe : a ∈ Ce := mem_centralizer_singleton_iff.mpr hae
  obtain ⟨Me, hMe, hPsup⟩ := exists_pump_sup_eq hq hR1 hG hN hK hK' hne heK' he2
  have haMe := mem_coreActionKernel_pump hq hR1 hG hN hK hK' hne heK' he2 haQ hae hMe
  have hza2 : IsPGroup 2 (zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha2, pow_one])
  have hcov := inf_centralizer_sup_oddCoreIn_eq hza2 (zpowers_le.mpr haMe)
  rw [centralizer_zpowers_eq] at hcov
  have hMeq : IsQuasisimple (↥Me ⧸ pPrimeCore 2 ↥Me) :=
    isQuasisimple_quotient_of_isPComponent hMe.1.1.1 hMe.1.1.2
  obtain ⟨hJ2, hJL, hJsup, -⟩ := cover_facts hMeq inf_le_left hcov
  set J := oddResidualIn (Me ⊓ Ca) with hJdef
  have hY'CC : Me ⊓ Ca ≤ Ca ⊓ Ce := le_inf inf_le_right (inf_le_left.trans hMe.1.1.1)
  have hsub : ((Me ⊓ Ca).subgroupOf (Ca ⊓ Ce)).IsSubnormal := by
    obtain ⟨-, -, hsn, -, -⟩ := hMe.1.1.2
    have h := hsn.comap (Subgroup.inclusion (inf_le_right : Ca ⊓ Ce ≤ Ce))
    convert h using 1
    ext x
    simp only [mem_subgroupOf, mem_comap, mem_inf, Subgroup.coe_inclusion]
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, (mem_inf.mp x.2).1⟩⟩
  have hJCC : IsPComponent 2 (J.subgroupOf (Ca ⊓ Ce)) :=
    GrSLit.isPComponent_subgroupOf_of_isSubnormal hJ2.1 hY'CC hsub hJ2.2
  obtain ⟨B, hBCa, hBpc, hJB, -⟩ :=
    foote_lemma_2_1_iv_subgroup heCa he2 (hJ2.1.trans hY'CC) hJCC
  have hB : IsTwoComponentIn B Ca := ⟨hBCa, hBpc⟩
  have hBe : IsTwoComponentIn (conjugate B e) Ca :=
    isTwoComponentIn_map_conj hB (le_normalizer (inv_mem heCa))
  refine ⟨B, hB, ?_⟩
  have hYQe : e ∈ coreActionKernel Y := by
    have heY : e ∈ normalizer (Y : Set G) := by
      have hKC : e ∈ normalizer ((K ⊓ Ca : Subgroup G) : Set G) := by
        rw [mem_normalizer_iff]
        intro y
        rw [mem_inf, mem_inf, mem_normalizer_iff.mp heQ.1 y,
          mem_normalizer_iff.mp (le_normalizer heCa) y]
      exact normalizer_le_normalizer_twoLayerIn _ hKC
    refine ⟨heY, fun y hy => ?_⟩
    have hKO : y⁻¹ * e⁻¹ * y * e ∈ oddCoreIn K := heQ.2 y (hY2.1 hy).1
    have hYm : y⁻¹ * e⁻¹ * y * e ∈ Y := by
      have h1 : e⁻¹ * y * e ∈ Y := by
        have := (mem_normalizer_iff.mp (inv_mem heY) y).mp hy
        simpa [mul_assoc] using this
      have := mul_mem (inv_mem hy) h1
      simpa [mul_assoc] using this
    exact inf_le_oddCoreIn (coprime_card_oddCoreIn K)
      ((hY2.1.trans inf_le_left).trans (le_normalizer_oddCoreIn K)) ⟨hKO, hYm⟩
  have hze2 : IsPGroup 2 (zpowers e) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, he2, pow_one])
  have hcovY := inf_centralizer_sup_oddCoreIn_eq hze2 (zpowers_le.mpr hYQe)
  rw [centralizer_zpowers_eq] at hcovY
  have hYq : IsQuasisimple (↥Y ⧸ pPrimeCore 2 ↥Y) :=
    isQuasisimple_quotient_of_isPComponent hY2.1 hY2.2
  obtain ⟨-, -, hYTsup, -⟩ := cover_facts hYq inf_le_left hcovY
  set Ω := oddCoreIn Ce ⊓ Ca with hΩ
  have hΩodd : Odd (Nat.card Ω) := Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right
    (Subgroup.card_dvd_of_le inf_le_left) (coprime_card_oddCoreIn Ce))
  have hOCeMe : oddCoreIn Ce ≤ normalizer (Me : Set G) :=
    UnbalancedCorr.pPrimeCore_le_normalizer_of_isPComponent hMe.1.1.1 hMe.1.1.2
  have hΩJ : Ω ≤ normalizer (J : Set G) := by
    have hΩY' : Ω ≤ normalizer ((Me ⊓ Ca : Subgroup G) : Set G) := fun g hg => by
      rw [mem_normalizer_iff]
      intro y
      rw [mem_inf, mem_inf, mem_normalizer_iff.mp (hOCeMe hg.1) y,
        mem_normalizer_iff.mp (le_normalizer hg.2) y]
    rw [← hJL]
    exact hΩY'.trans (normalizer_le_normalizer_twoLayerIn _)
  have hY'le : Me ⊓ Ca ≤ J ⊔ Ω := by
    intro y hy
    have hyM : y ∈ oddCoreIn Me ⊔ J := by rw [sup_comm, hJsup]; exact hy.1
    obtain ⟨o, ho, j, hj, rfl⟩ := exists_mul_of_mem_sup_normalizer
      ((hJ2.1.trans inf_le_left).trans (le_normalizer_oddCoreIn Me)) hyM
    have hjCa : j ∈ Ca := (hJ2.1 hj).2
    have hoCa : o ∈ Ca := by
      have e1 : o = o * j * j⁻¹ := by group
      rw [e1]
      exact mul_mem hy.2 (inv_mem hjCa)
    have hoCe : o ∈ oddCoreIn Ce := oddCoreIn_le_of_isTwoComponentIn hMe.1.1 ho
    exact mul_mem (mem_sup_right ⟨hoCe, hoCa⟩) (mem_sup_left hj)
  have hYTJ : oddResidualIn (Y ⊓ Ce) ≤ J := by
    rw [oddResidualIn, closure_le]
    rintro x ⟨hxY, k, hk⟩
    have hxK : x ∈ K ⊓ Ce := ⟨(hY2.1 hxY.1).1, hxY.2⟩
    have hxKe : x ∈ twoLayerIn (K ⊓ Ce) := mem_pump_of_two hK heQ he2 hxK hk
    have hxMO : x ∈ Me ⊔ oddCoreIn Ce := by
      have h1 : twoLayerIn (K ⊓ Ce) ≤ Me ⊔ oddCoreIn (twoLayerIn Ce) := by
        rw [← hPsup]
        exact le_sup_left
      exact (h1.trans (sup_le_sup_left (oddCoreIn_twoLayerIn_le Ce) _)) hxKe
    have hxCa : x ∈ Ca := (hY2.1 hxY.1).2
    have hx2 := mem_sup_inf_centralizer ha2 haMe.1
      (mem_normalizer_oddCoreIn (le_normalizer haCe)) hOCeMe
      (Nat.coprime_two_left.mp (coprime_card_oddCoreIn Ce)) hxMO hxCa
    have hxJΩ : x ∈ J ⊔ Ω := (sup_le hY'le le_sup_right) hx2
    exact mem_of_mem_sup_of_coprime_index hΩJ (Nat.Coprime.coprime_dvd_right
      (Subgroup.index_dvd_card _) (Nat.coprime_two_left.mpr hΩodd)) hxJΩ hk
  have hLB : twoLayerIn Ca ≤ normalizer ((B ⊔ conjugate B e : Subgroup G) : Set G) :=
    le_normalizer_sup (twoLayerIn_le_normalizer hB.1 hB.2) (twoLayerIn_le_normalizer hBe.1 hBe.2)
  have hYB : Y ≤ B ⊔ conjugate B e :=
    le_of_perfect_of_le_sup (UnbalancedCorr.commutator_eq_of_isPComponent hY2.1 hY2.2)
      (hYL.trans hLB) (((map_subtype_le _).trans hYL).trans hLB)
      (Nat.coprime_two_left.mp (coprime_card_oddCoreIn Y))
      (hYTsup.symm.le.trans (sup_le_sup_right (hYTJ.trans hJB) _))
  have hS : conjClosure Y (twoLayerIn Ca) ≤ B ⊔ conjugate B e := Sol78.conjClosure_le hYB hLB
  intro M hM
  exact eq_or_eq_of_le_sup hM.1.1 hB hBe
    ((le_conjClosure_of_not_le_coreActionKernel hM.1.1 hYL hM.2).trans hS)

theorem ncard_pumpSet_le_one (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {K K' : Subgroup G} (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') {a : G} (haQ : a ∈ coreActionKernel K)
    (ha2 : orderOf a = 2) {E : Subgroup G} (hE : IsKleinFour E) (hEK' : E ≤ K')
    (hEa : E ≤ centralizer ({a} : Set G)) :
    (pumpSet K (centralizer ({a} : Set G))).ncard ≤ 1 := by
  classical
  by_contra hlt
  push Not at hlt
  obtain ⟨M₁, M₂, hM₁, hM₂, h12⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp hlt
  have hswap : ∀ e ∈ E, e ≠ 1 → conjugate M₁ e = M₂ := by
    intro e he he1
    have he2 : orderOf e = 2 := orderOf_eq_two_of_isKleinFour hE he he1
    have hae : a * e = e * a := (mem_centralizer_singleton_iff.mp (hEa he)).symm
    obtain ⟨B, -, hPB⟩ :=
      exists_pumpSet_subset_pair hq hR1 hG hN hK hK' hne haQ ha2 (hEK' he) he2 hae
    have hee : e * e = 1 := by rw [← pow_two, sq_eq_one_of_orderOf_eq_two he2]
    rcases hPB M₁ hM₁ with h1 | h1 <;> rcases hPB M₂ hM₂ with h2 | h2
    · exact (h12 (h1.trans h2.symm)).elim
    · rw [h1, h2]
    · rw [h1, h2, conjugate_conjugate_mul, hee, conjugate_one']
    · exact (h12 (h1.trans h2.symm)).elim
  have := Fintype.ofFinite ↥E
  have h4 : Fintype.card ↥E = 4 := by rw [← Nat.card_eq_fintype_card]; exact hE.card_four
  obtain ⟨u, -, hu⟩ := Finset.exists_mem_ne (s := Finset.univ)
    (by rw [Finset.card_univ]; omega) (1 : ↥E)
  obtain ⟨v, hv, hvu⟩ := Finset.exists_mem_ne (s := Finset.univ.erase (1 : ↥E))
    (by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]; omega) u
  have hv1 : v ≠ 1 := Finset.ne_of_mem_erase hv
  have hu1' : (u : G) ≠ 1 := fun h => hu (Subtype.ext h)
  have hv1' : (v : G) ≠ 1 := fun h => hv1 (Subtype.ext h)
  have huv1 : (u : G) * v ≠ 1 := by
    intro h
    apply hvu
    have hu2 : (u : G) * u = 1 := by
      rw [← pow_two]; exact sq_eq_one_of_isKleinFour hE u.2
    apply Subtype.ext
    calc (v : G) = (u : G) * u * v := by rw [hu2, one_mul]
      _ = u * (u * v) := by group
      _ = u := by rw [h, mul_one]
  have hv2 : (v : G) * v = 1 := by rw [← pow_two]; exact sq_eq_one_of_isKleinFour hE v.2
  have h1 := hswap _ (mul_mem u.2 v.2) huv1
  rw [← conjugate_conjugate_mul, hswap _ u.2 hu1'] at h1
  have h2 : conjugate M₂ v = M₁ := by
    rw [← hswap _ v.2 hv1', conjugate_conjugate_mul, hv2, conjugate_one']
  rw [h2] at h1
  exact h12 h1

theorem conjClosure_le_of_isKleinFour (hq : QuasisimpleTwoPartInput)
    (hR1 : Lemma32ConditionTwoInputFor simpleAmbient) (hG : SimpleAmbient G)
    (hN : IsSolomonChoice N) {K K' : Subgroup G} (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hne : K ≠ K') {a : G} (haQ : a ∈ coreActionKernel K)
    (ha2 : orderOf a = 2) {E : Subgroup G} (hE : IsKleinFour E) (hEK' : E ≤ K')
    (hEa : E ≤ centralizer ({a} : Set G)) :
    conjClosure (twoLayerIn (K ⊓ centralizer ({a} : Set G)))
        (twoLayerIn (centralizer ({a} : Set G))) ≤
      oddCoreIn (twoLayerIn (centralizer ({a} : Set G))) ⊔
        twoLayerIn (K ⊓ centralizer ({a} : Set G)) := by
  obtain ⟨M, hM⟩ := pumpSet_nonempty hK haQ ha2
  have h1 : (pumpSet K (centralizer ({a} : Set G))).ncard = 1 := by
    have hle := ncard_pumpSet_le_one hq hR1 hG hN hK hK' hne haQ ha2 hE hEK' hEa
    have hpos := (Set.ncard_pos (Set.toFinite _)).mpr ⟨M, hM⟩
    omega
  obtain ⟨M', hM'⟩ := Set.ncard_eq_one.mp h1
  exact conjClosure_le_of_pumpSet_eq hK haQ ha2 hM'

end CFSG.ComponentClassification.Sol76.Sig
