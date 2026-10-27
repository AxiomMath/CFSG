module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inner56
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inputs56
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Choice56

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inf_centralizer_mul_central_eq {S : Subgroup G} {t v : G}
    (hZS : ∀ s ∈ S, s * t = t * s) :
    S ⊓ centralizer ({v * t} : Set G) = S ⊓ centralizer ({v} : Set G) := by
  ext s
  simp only [mem_inf, mem_centralizer_singleton_iff]
  refine ⟨fun ⟨hs, h⟩ => ⟨hs, ?_⟩, fun ⟨hs, h⟩ => ⟨hs, ?_⟩⟩
  · have hst : s * t = t * s := hZS s hs
    have h' : s * v * t = v * s * t := by
      calc s * v * t = s * (v * t) := by group
        _ = v * t * s := h
        _ = v * (t * s) := by group
        _ = v * (s * t) := by rw [hst]
        _ = v * s * t := by group
    exact mul_right_cancel h'
  · have hst : s * t = t * s := hZS s hs
    calc s * (v * t) = s * v * t := by group
      _ = v * s * t := by rw [h]
      _ = v * (s * t) := by group
      _ = v * (t * s) := by rw [hst]
      _ = v * t * s := by group

omit [Finite G] in
theorem orderOf_mul_central_eq_two {t v : G} (hv : orderOf v = 2) (ht2 : t * t = 1)
    (hvt : v * t = t * v) (hne : v ≠ t) : orderOf (v * t) = 2 := by
  have h1 : v * v = 1 := by rw [← pow_two, ← hv, pow_orderOf_eq_one]
  refine orderOf_eq_prime ?_ ?_
  · calc (v * t) ^ 2 = v * (t * v) * t := by rw [pow_two]; group
      _ = v * v * (t * t) := by rw [← hvt]; group
      _ = 1 := by rw [h1, ht2, one_mul]
  · intro h
    apply hne
    rw [mul_eq_one_iff_eq_inv.mp h, inv_eq_of_mul_eq_one_right ht2]

theorem exists_unbalanced_lt_of_unbalanced
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact)
    (hL2 : L2UnbalancingSylowFact) (hUnit : L34UnbalancingUnitaryStep)
    (hUC : L34UnitaryCentralizerFact) (hFour : L34CommutatorFourGroupFact)
    (hOut : L34OuterInvolutionCentralizerFact) {L : Subgroup G} {t : G} {S T : Subgroup G}
    (hset : L34Sec5Setting G L t S T) (hSG : IsSylowTwoIn S ⊤) {u : G} (huS : u ∈ S)
    (hu2 : orderOf u = 2) (hidx : Nat.card S ≤ 4 * Nat.card ↥(S ⊓ centralizer ({u} : Set G)))
    (hUu : ¬ oddIn L ⊓ centralizer ({u} : Set G) ≤ oddIn (centralizer ({u} : Set G))) :
    ∃ u' ∈ S, orderOf u' = 2 ∧
      Nat.card ↥(S ⊓ centralizer ({u} : Set G)) < Nat.card ↥(S ⊓ centralizer ({u'} : Set G)) ∧
      ¬ oddIn L ⊓ centralizer ({u'} : Set G) ≤ oddIn (centralizer ({u'} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hset' := hset
  obtain ⟨hbase, hfam, -, hSyl, htS, -, -⟩ := hset'
  obtain ⟨⟨-, -, -, -, -, hto, -, -⟩, htypeL, -, -, -⟩ := hfam
  have htypes := hbase.2.2.2.2.2.2.2
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  have htK : t ∈ coreActionKernel L := mem_coreActionKernel_of_commute fun l hl =>
    (mem_centralizer_singleton_iff.mp (hLt hl)).symm
  have hperf : ⁅L, L⁆ = L := GSThmB.commutator_eq_self_of_isPComponent hLt hLpt
  have hut : t * u = u * t := (hZS u huS).symm
  have hXt : oddIn L ≤ oddIn (centralizer ({t} : Set G)) :=
    GSLit.map_pPrimeCore_le_of_isPComponent hLt hLpt
  have hYD : oddIn L ⊓ centralizer ({u} : Set G) ≤
      oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({u} : Set G) := inf_le_inf_right _ hXt
  obtain ⟨K₁, hK₁u, hK₁p, hK₁n⟩ := exists_isPComponent_not_le hSol hto hu2 hut hYD hUu
  have hT := gsUnbalancingTriple_of_not_le hSol hto hu2 hut hK₁u hK₁p hYD hK₁n
  have htype1 := htypes u t K₁ hT
  set C := centralizer ({u} : Set G) with hC
  have hS2 : IsPGroup 2 S := IsSylowTwoIn.isPGroup hSG
  have hSC2 : IsPGroup 2 ↥((S ⊓ C).subgroupOf C) :=
    (hS2.to_le inf_le_left).of_equiv (subgroupOfEquivOfLe inf_le_right).symm
  obtain ⟨R₀, hR₀⟩ := hSC2.exists_le_sylow
  set R₁ : Subgroup G := (R₀ : Subgroup ↥C).map C.subtype with hR₁
  have hR₁syl : IsSylowTwoIn R₁ C :=
    ⟨map_subtype_le _, R₀, (comap_map_eq_self_of_injective C.subtype_injective _).symm⟩
  have hSR₁ : S ⊓ C ≤ R₁ := fun x hx =>
    ⟨⟨x, (mem_inf.mp hx).2⟩, hR₀ (show (⟨x, (mem_inf.mp hx).2⟩ : C) ∈ (S ⊓ C).subgroupOf C
      from hx), rfl⟩
  obtain ⟨hK₁sub, -, -⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K₁ C hK₁u).mp hK₁p
  have hR₁K := isSylowTwoIn_inf_of_isSubnormal hR₁syl hK₁u hK₁sub
  have hRBt : S ⊓ C ⊓ K₁ ≤ centralizer ({t} : Set G) := fun y hy =>
    mem_centralizer_singleton_iff.mpr (hZS y (mem_inf.mp (mem_inf.mp hy).1).1)
  have hRB2 : IsPGroup 2 ↥(S ⊓ C ⊓ K₁) := hS2.to_le (inf_le_left.trans inf_le_left)
  have h64 : IsL34Type (K₁ ⧸ Open.fusionZStar K₁) → 64 ∣ Nat.card K₁ := by
    intro h
    have h1 := GSThmB.card_of_lieModel_L34 h
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Open.fusionZStar K₁)
    rw [h1] at h2
    rw [h2]
    exact Dvd.dvd.mul_right (by norm_num) _
  by_cases hEq : R₁ = S ⊓ C
  ·
    exfalso
    rw [hEq] at hR₁K
    rcases htype1 with h5 | h7 | h34
    · exact hL2 G u t K₁ _ hT (Or.inl h5) hR₁K hRBt
    · exact hL2 G u t K₁ _ hT (Or.inr h7) hR₁K hRBt
    · have h8 := card_le_eight_of_unitary hUnit hUC hT h34 inf_le_right hRBt hRB2
      have h64' := sixtyFour_le_card_of_isSylowTwoIn hR₁K (h64 h34)
      omega
  have hlt : Nat.card ↥(S ⊓ C) < Nat.card R₁ := by
    by_contra hle
    exact hEq (eq_of_le_of_card_ge hSR₁ (not_lt.mp hle)).symm
  have hR₁2 : IsPGroup 2 R₁ := IsSylowTwoIn.isPGroup hR₁syl
  obtain ⟨g, -, hg⟩ := exists_conjugate_le_of_isSylowTwoIn hSG le_top hR₁2
  set w := g⁻¹ * u * g with hw
  have huR₁ : u ∈ R₁ := hSR₁ (mem_inf.mpr ⟨huS, mem_centralizer_singleton_iff.mpr rfl⟩)
  have hwS : w ∈ S := hg (conj_mem_conjugate huR₁ g)
  have hRw : conjugate R₁ g ≤ centralizer ({w} : Set G) := by
    rw [← conjugate_centralizer_singleton]
    exact map_mono hR₁syl.1
  have hcw : Nat.card R₁ ≤ Nat.card ↥(S ⊓ centralizer ({w} : Set G)) := by
    have h1 : Nat.card (conjugate R₁ g) = Nat.card R₁ :=
      card_map_of_injective (MulAut.conj g⁻¹).injective
    rw [← h1]
    exact card_le_of_le (le_inf hg hRw)
  have hw2 : orderOf w = 2 := by
    rw [hw, show g⁻¹ * u * g = MulAut.conj g⁻¹ u by simp, MulEquiv.orderOf_eq, hu2]
  have hww : w * w = 1 := by rw [← pow_two, ← hw2, pow_orderOf_eq_one]
  have hltw : Nat.card ↥(S ⊓ C) < Nat.card ↥(S ⊓ centralizer ({w} : Set G)) :=
    hlt.trans_le hcw
  by_cases hwK : w ∈ coreActionKernel L
  ·
    exfalso
    have hwQ : w ∈ S ⊓ coreActionKernel L := mem_inf.mpr ⟨hwS, hwK⟩
    obtain ⟨hK₁g, hK₁gp⟩ := GSThmB.Six.isPComponent_conjugate hK₁u hK₁p g
    rw [conjugate_centralizer_singleton] at hK₁g hK₁gp
    obtain ⟨-, -, -, -, h34g⟩ := isPComponent_eq_of_setting hS hU hheld hSol hGW hMax hL34 hset
      hwQ hw2 hK₁g hK₁gp (types_conjugate g htype1)
    have h34 := isL34Type_of_conjugate g h34g
    have h8 := card_le_eight_of_unitary hUnit hUC hT h34 inf_le_right hRBt hRB2
    have h64' := sixtyFour_le_card_of_isSylowTwoIn hR₁K (h64 h34)
    have hidx' : (S ⊓ C).relIndex R₁ ≤ 4 := by
      have h1 := relIndex_mul_card_of_le hSR₁
      have h2 : Nat.card R₁ ≤ Nat.card S := card_le_of_isSylowTwoIn_top hSG hR₁2
      have h3 : 0 < Nat.card ↥(S ⊓ C) := Nat.card_pos
      by_contra hgt
      push Not at hgt
      have : 5 * Nat.card ↥(S ⊓ C) ≤ Nat.card R₁ := by
        rw [← h1]
        exact Nat.mul_le_mul_right _ hgt
      omega
    have hRK : Nat.card ↥(R₁ ⊓ K₁) ≤ 4 * Nat.card ↥(S ⊓ C ⊓ K₁) := by
      have h1 := relIndex_mul_card_of_le (inf_le_inf_right K₁ hSR₁)
      have h2 := relIndex_inf_le_of_le (K := K₁) hSR₁
      rw [← h1]
      exact Nat.mul_le_mul_right _ (h2.trans hidx')
    omega
  by_cases hwW : w ∈ withKernel L
  ·
    have hidx2 : Nat.card S ≤ 2 * Nat.card ↥(S ⊓ centralizer ({w} : Set G)) := by
      have h1 := relIndex_mul_card_of_le (inf_le_left : S ⊓ centralizer ({w} : Set G) ≤ S)
      obtain ⟨n, hn⟩ := hS2.exists_card_eq
      have hk3 : (S ⊓ centralizer ({w} : Set G)).relIndex S ≠ 3 := by
        intro hk
        have h3 : 3 ∣ 2 ^ n := ⟨Nat.card ↥(S ⊓ centralizer ({w} : Set G)), by
          rw [← hn, ← h1, hk]⟩
        exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
      have hk4 : (S ⊓ centralizer ({w} : Set G)).relIndex S < 4 := by
        by_contra hk
        push Not at hk
        have : 4 * Nat.card ↥(S ⊓ centralizer ({w} : Set G)) ≤ Nat.card S := by
          rw [← h1]
          exact Nat.mul_le_mul_right _ hk
        omega
      rw [← h1]
      exact Nat.mul_le_mul_right _ (by omega)
    obtain ⟨w₁, hw₁, hUw₁⟩ := exists_unbalanced_of_mem_withKernel
      (l34Lemma53_of_inputs hS hU hheld hSol hGW) hFour hSol hset hLt hLpt hZS hwS hw2 hwK hwW
      hidx2
    rcases (show w₁ = w ∨ w₁ = w * t by simpa using hw₁) with h | h
    · rw [h] at hUw₁
      exact ⟨w, hwS, hw2, hltw, hUw₁⟩
    · rw [h] at hUw₁
      refine ⟨w * t, mul_mem hwS htS, orderOf_mul_central_eq_two hw2 ht2 (hZS w hwS)
        fun h' => hwK (h' ▸ htK), ?_, hUw₁⟩
      rw [inf_centralizer_mul_central_eq hZS]
      exact hltw
  ·
    exfalso
    have hS₀ : IsSylowTwoIn (S ⊓ L) L := isSylowTwoIn_inf_of_isSubnormal hSyl le_normalizer
      (Subgroup.Normal.isSubnormal Subgroup.normal_in_normalizer)
    have h4 := hOut G L S (S ⊓ L) w hperf htypeL hS₀ inf_le_left hS2 hSyl.1 hwS hww hwW
    omega

theorem l34Lemma56_of_facts
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact)
    (hL2 : L2UnbalancingSylowFact) (hUnit : L34UnbalancingUnitaryStep)
    (hUC : L34UnitaryCentralizerFact) (hRank : L34CenterRankFact)
    (hFour : L34CommutatorFourGroupFact) (hOut : L34OuterInvolutionCentralizerFact) :
    L34Lemma56 := by
  intro G _ _ L t S T hset hSG
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hset' := hset
  obtain ⟨-, hfam, -, hSyl, htS, -, -⟩ := hset'
  obtain ⟨⟨-, -, -, -, -, hto, -, -⟩, htype, -, -, -⟩ := hfam
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  have htK : t ∈ coreActionKernel L := mem_coreActionKernel_of_commute fun l hl =>
    (mem_centralizer_singleton_iff.mp (hLt hl)).symm
  have hperf : ⁅L, L⁆ = L := GSThmB.commutator_eq_self_of_isPComponent hLt hLpt
  have key : ∀ n : ℕ, ∀ u ∈ S, Nat.card S - Nat.card ↥(S ⊓ centralizer ({u} : Set G)) < n →
      orderOf u = 2 → Nat.card S ≤ 4 * Nat.card ↥(S ⊓ centralizer ({u} : Set G)) →
      ¬ (¬ oddIn L ⊓ centralizer ({u} : Set G) ≤ oddIn (centralizer ({u} : Set G))) := by
    intro n
    induction n with
    | zero => exact fun u _ h => absurd h (Nat.not_lt_zero _)
    | succ n ih =>
      intro u huS hlt hu2 hidx hUu
      obtain ⟨u', hu'S, hu'2, hlt', hUu'⟩ := exists_unbalanced_lt_of_unbalanced hS hU hheld hSol
        hGW hMax hL34 hL2 hUnit hUC hFour hOut hset hSG huS hu2 hidx hUu
      have hle : Nat.card ↥(S ⊓ centralizer ({u'} : Set G)) ≤ Nat.card S :=
        card_le_of_le inf_le_left
      exact ih u' hu'S (by omega) hu'2 (by omega) hUu'
  obtain ⟨u₀, hu₀SL, hu₀K, hu₀2, hcen⟩ := exists_lemma56_involution hFour hperf htype hSyl
  have hu₀S : u₀ ∈ S := (mem_inf.mp hu₀SL).1
  have hu₀L : u₀ ∈ L := (mem_inf.mp hu₀SL).2
  have hidx := card_le_four_mul_card_centralizer hRank hperf htype hSyl hu₀S hu₀L hu₀2 hcen
  have hu₀o : orderOf u₀ = 2 :=
    orderOf_eq_prime (by rw [pow_two, hu₀2]) fun h => hu₀K (h ▸ one_mem _)
  obtain ⟨-, u, hu, hUu⟩ := l34Lemma53_of_inputs hS hU hheld hSol hGW G L t S T hset u₀ hu₀S
    hu₀o hu₀K (mem_sup_left hu₀L)
  rcases (show u = u₀ ∨ u = u₀ * t by simpa using hu) with h | h
  · rw [h] at hUu
    exact key _ u₀ hu₀S (Nat.lt_succ_self _) hu₀o hidx hUu
  · rw [h] at hUu
    rw [← inf_centralizer_mul_central_eq (v := u₀) hZS] at hidx
    exact key _ (u₀ * t) (mul_mem hu₀S htS) (Nat.lt_succ_self _)
      (orderOf_mul_central_eq_two hu₀o ht2 (hZS u₀ hu₀S) fun h' => hu₀K (h' ▸ htK)) hidx hUu

end CFSG.ComponentClassification.GrSLit.GrS5
