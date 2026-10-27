module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdAutomizer
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdCentralSylow
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdShear
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdFullConj
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdCover
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionRank
public import CFSG.LocalAnalysis.OddStandard.GlueL34
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicONan
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundationFinal
public import CFSG.LocalAnalysis.ComponentClassification.Foote5Asc25Main

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup
open CFSG.Blueprint.NativeSporadic (IsSporadic)

variable {G : Type} [Group G] [Finite G]

theorem false_of_conj_eq_mul_of_card_four {J : Subgroup G} (hst : IsStandardSubgroup J)
    (hZ : Odd (Nat.card (center ↥J))) (hcen : center (↥J ⧸ center ↥J) = ⊥)
    (hOut : ∀ α β : MulAut (↥J ⧸ center ↥J),
      α ∉ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range →
      β ∉ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range →
      α * β ∈ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range)
    (hfix : ∀ (T : Sylow 2 (↥J ⧸ center ↥J)) (α : MulAut (↥J ⧸ center ↥J)),
      (∀ x ∈ (T : Subgroup (↥J ⧸ center ↥J)), α x = x) →
        α ∈ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range)
    (hZT : ∀ T : Sylow 2 (↥J ⧸ center ↥J), Nat.card (center (T : Subgroup (↥J ⧸ center ↥J))) = 2)
    (hcls : ∀ a b : ↥J, orderOf a = 2 → orderOf b = 2 → ∃ j : ↥J, b = j⁻¹ * a * j)
    (hpow : ∀ a : ↥J, orderOf a = 2 → ∃ y : ↥J, y ^ 8 = a)
    (hcyc : ∀ P : Subgroup G, P ≤ centralizer (J : Set G) → IsPGroup 2 P → IsCyclic P)
    (hC4 : ∀ P : Subgroup G, P ≤ centralizer (J : Set G) → IsPGroup 2 P → Nat.card P ≤ 4)
    {R : Subgroup G} (hRC : R ≤ centralizer (J : Set G)) (hR : IsPGroup 2 R)
    (hR4 : Nat.card R = 4) {t₀ u h : G} (ht₀R : t₀ ∈ R) (ht₀ : orderOf t₀ = 2) (huJ : u ∈ J)
    (hu : orderOf u = 2) (hh : h⁻¹ * t₀ * h = u * t₀) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht₀C : t₀ ∈ centralizer (J : Set G) := hRC ht₀R
  have hnotJ : ∀ g : G, g⁻¹ * t₀ * g ∉ J :=
    conj_not_mem_of_forall_pow_eight hst hOut hZ hpow hC4 ht₀ ht₀C
  have hRcyc : IsCyclic ↥R := hcyc R hRC hR
  have hRt : R ≤ centralizer ({t₀} : Set G) := by
    intro r hr
    rw [mem_centralizer_singleton_iff]
    have h := (IsCyclic.commGroup (α := ↥R)).mul_comm ⟨r, hr⟩ ⟨t₀, ht₀R⟩
    exact congrArg Subtype.val h
  have hR' : IsPGroup 2 (R.subgroupOf (centralizer ({t₀} : Set G))) := by
    rw [← Subgroup.comap_subtype]
    exact hR.comap_subtype
  obtain ⟨P₀, hP₀⟩ := hR'.exists_le_sylow
  set S' : Subgroup G := (P₀ : Subgroup ↥(centralizer ({t₀} : Set G))).map
    (centralizer ({t₀} : Set G)).subtype with hS'def
  have hS' : IsSylowTwoIn S' (centralizer ({t₀} : Set G)) := by
    refine ⟨map_subtype_le _, P₀, ?_⟩
    rw [hS'def, ← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective
      (centralizer ({t₀} : Set G)).subtype_injective]
  have hRS : R ≤ S' := by
    intro r hr
    exact Subgroup.mem_map.mpr ⟨⟨r, hRt hr⟩, hP₀ (Subgroup.mem_subgroupOf.mpr hr), rfl⟩
  have hS'p : IsPGroup 2 S' := P₀.isPGroup'.map _
  have hSC : Nat.card ↥(S' ⊓ centralizer (J : Set G)) = 4 := by
    refine le_antisymm (hC4 _ inf_le_right (hS'p.to_le inf_le_left)) ?_
    rw [← hR4]
    exact Subgroup.card_le_of_le (le_inf hRS hRC)
  obtain ⟨z, hzS, hzc, hz⟩ := exists_mem_inf_center_of_card_center_sylow hst hZ hZT ht₀ ht₀C hS'
  have hZ' := fun w hwS hwc hw =>
    eq_or_eq_or_eq_of_mem_center_of_sylow_fix hst hZ hcen hfix hZT hcyc ht₀ ht₀C hS' hzS hzc hz
      (w := w) hwS hwc hw
  obtain ⟨j, hj⟩ := hcls ⟨u, huJ⟩ ⟨z, hzS.2⟩ (by rw [Subgroup.orderOf_mk]; exact hu)
    (by rw [Subgroup.orderOf_mk]; exact hz)
  have hjt : (j : G) * t₀ = t₀ * j := mem_centralizer_iff.mp ht₀C j j.2
  have hfus : (h * j)⁻¹ * t₀ * (h * j) = z * t₀ := by
    have hz' : z = (j : G)⁻¹ * u * j := by
      have := congrArg Subtype.val hj
      simpa using this
    calc (h * j)⁻¹ * t₀ * (h * j) = (j : G)⁻¹ * (h⁻¹ * t₀ * h) * j := by group
      _ = (j : G)⁻¹ * u * j * ((j : G)⁻¹ * t₀ * j) := by rw [hh]; group
      _ = z * t₀ := by
        rw [← hz', show (j : G)⁻¹ * t₀ * j = t₀ by
          rw [mul_assoc, ← hjt, ← mul_assoc, inv_mul_cancel, one_mul]]
  have hnot : ∀ g : G, g⁻¹ * t₀ * g ≠ z := fun g hg => hnotJ g (hg ▸ hzS.2)
  have hzt : z ≠ t₀ := fun h' => hnotJ 1 (by rw [inv_one, one_mul, mul_one, ← h']; exact hzS.2)
  have ht₀S : t₀ ∈ S' := hRS ht₀R
  have ht₀c : ∀ s ∈ S', s * t₀ = t₀ * s := fun s hs =>
    (mem_centralizer_singleton_iff.mp (hS'.1 hs))
  by_cases hSyl : ∃ P : Sylow 2 G, (P : Subgroup G) = S'
  · obtain ⟨P, hP⟩ := hSyl
    exact false_of_sylow_of_conj_eq_mul P (hP ▸ ht₀S) (fun s hs => ht₀c s (hP ▸ hs))
      (hP ▸ hzS.1) (fun s hs => hzc s (hP ▸ hs)) ht₀ hz hzt
      (fun w hw hwc hw2 => hZ' w (hP ▸ hw) (fun s hs => hwc s (hP.symm ▸ hs)) hw2) hnot hfus
  · obtain ⟨P, hSP⟩ := hS'p.exists_le_sylow
    have hlt : S' < (P : Subgroup G) := lt_of_le_of_ne hSP fun h' => hSyl ⟨P, h'.symm⟩
    obtain ⟨x, -, hxN, hxt, -⟩ := exists_shear_of_lt ht₀ hS' P.isPGroup' hlt hzS.1 hzc hz hzt
      hZ' hnot
    exact false_of_shear_of_card_four hst hZ hcen hfix hZT hcyc ht₀ ht₀C hS' hSC hzS hz hxN hxt

theorem card_sylow_centralizer_eq_two_of_onan
    (hAS : RankTwoSporadic.SporadicCaseOdd .ONan)
    (hCIT : StandardRecognition.ClassicalInvolutionTheoremModels)
    (h25 : EvenSporadicStandard.Finkelstein77.Asc76Lemma25)
    [IsSimpleGroup G] (hnonab : ∃ g h : G, g * h ≠ h * g)
    (hK : Assembly.KProper Blueprint.Catalog G) (hU : ¬ OutcomeLocal.UOutcome G)
    {J : Subgroup G} (hst : IsStandardSubgroup J)
    (hF : IsSporadic (↥J ⧸ center ↥J) .ONan) (hZ : Odd (Nat.card (center ↥J)))
    (S : Sylow 2 ↥(centralizer (J : Set G))) : Nat.card S = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd := CFSG.IsStandardSubgroup.assembly hst
  have hS : OddStandard.StandardSetting G J :=
    ⟨inferInstance, hnonab, hK, CFSG.IsStandardSubgroup.standardComponentIsStandard hst⟩
  have h7 : 7 ∣ Nat.card G := by
    have hdvd := OddStandard.GlueL34.card_quotient_center_dvd J
    obtain ⟨e⟩ := hF
    have hcard : Nat.card (↥J ⧸ center ↥J) = 460815505920 :=
      (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.ON.card_ON
    rw [hcard] at hdvd
    exact (by norm_num : 7 ∣ 460815505920).trans hdvd
  rcases StandardRecognition.standard_centralizer_rank_split hstd S with
    hrank | ⟨hcyc, -⟩ | ⟨n, hn, hSq, -⟩
  ·
    exact False.elim (hAS G J (OddStandard.GlueL34.rankTwoHyp hS hrank)
      (OddStandard.GlueL34.oddCore_eq_bot hS) hF)
  ·
    by_contra hne
    have h4 : 4 ≤ Nat.card S :=
      EvenSporadicStandard.Finkelstein77.four_le_card_sylow_of_ne_two S hstd.2.1 hne
    have hcycP : ∀ P : Subgroup G, P ≤ centralizer (J : Set G) → IsPGroup 2 P → IsCyclic P :=
      fun P hPC hP =>
        (LocalAnalysis.ComponentInitial.Finkelstein1977.isCyclic_and_card_le_of_le S hcyc hPC
          hP).1
    by_cases hall : ∀ g : G, g ∉ normalizer (J : Set G) → ∀ P : Subgroup G,
        P ≤ (centralizer (J : Set G)).map (MulAut.conj g).toMonoidHom ⊓ normalizer (J : Set G) →
          IsPGroup 2 P → Nat.card P ≤ 2
    ·
      obtain ⟨y, hy⟩ :=
        EvenSporadicStandard.Finkelstein77.exists_orderOf_four_of_cyclic_sylow S hcyc h4
      have hy4 : orderOf (y : G) = 4 := by rw [Subgroup.orderOf_coe, hy]
      have hW := EvenSporadicStandard.Finkelstein77.weaklyClosed_zpowers hstd S hcyc hall y.2 hy4
      have h2 :=
        EvenSporadicStandard.Finkelstein77.sectionalTwoRankLE_of_lemma25 h25 hnonab hy4 hW
      have hbound := ((h2.subgroup J).quotient (center J)).twoRank_le
      obtain ⟨E, hE, hEcard⟩ := hasElemAbelianEight_onan hF
      have h3 :=
        EvenSporadicStandard.Finkelstein77.three_le_twoRank_of_elemAbelian_eight E hE hEcard
      omega
    ·
      push Not at hall
      obtain ⟨g, hg, P, hP, hP2, hPcard⟩ := hall
      have hP4 : 4 ≤ Nat.card P := by
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP2
        rw [hk] at hPcard ⊢
        have hk2 : 2 ≤ k := by
          by_contra h
          have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      have hcen : center (↥J ⧸ center ↥J) = ⊥ :=
        EvenSporadicStandard.Solomon78.center_eq_bot_of_isSporadic_on hF
      have hOut : ∀ α β : MulAut (↥J ⧸ center ↥J),
          α ∉ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range →
          β ∉ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range →
          α * β ∈ (MulAut.conj : (↥J ⧸ center ↥J) →* MulAut (↥J ⧸ center ↥J)).range :=
        fun _ _ hα hβ => mul_mem_range_conj_onan hF hα hβ
      have hpow : ∀ a : ↥J, orderOf a = 2 → ∃ y : ↥J, y ^ 8 = a :=
        fun _ ha => exists_pow_eight_eq_of_orderOf_eq_two_onan hF hZ ha
      obtain ⟨g', hg', R, T, hRC, hR, hRcard, hTg, hTN, hT, hTcard, hRT⟩ :=
        LocalAnalysis.ComponentInitial.Finkelstein1977.exists_full_conj_centralized hstd S hcyc hg
          (hP.trans inf_le_left) (hP.trans inf_le_right) hP2 hP4
      obtain ⟨hle4, u, t₀, s, huJ, hu, ht₀R, ht₀, -, -, hsu, h, hh⟩ :=
        card_le_four_of_full_conj hst hZ hcen hOut
          (fun _ ha _ hWa hWn hW => eq_bot_of_odd_of_normalized_centralizer_onan hF ha hWa hWn hW)
          (fun _ ha => card_centralizer_commutator_centralizer_onan hF ha)
          (fun _ ha _ hα => mem_range_conj_of_forall_mem_commutator_centralizer_onan hF ha hα)
          S hcyc h4 hg' hRC hR hRcard hTg hTN hT hTcard hRT
      have hC4 : ∀ P : Subgroup G, P ≤ centralizer (J : Set G) → IsPGroup 2 P → Nat.card P ≤ 4 :=
        fun P hPC hP =>
          (LocalAnalysis.ComponentInitial.Finkelstein1977.isCyclic_and_card_le_of_le S hcyc hPC
            hP).2.trans hle4
      rcases hsu with hsu | hsu
      ·
        exact conj_not_mem_of_forall_pow_eight hst hOut hZ hpow hC4 ht₀ (hRC ht₀R) h
          (by rw [hh, hsu]; exact huJ)
      ·
        exact false_of_conj_eq_mul_of_card_four hst hZ hcen hOut
          (fun T _ hα => mem_range_conj_of_forall_mem_sylow_onan hF T hα)
          (fun T => card_center_sylow_onan hF T)
          (fun _ _ ha hb => exists_conj_of_orderOf_eq_two_onan hF hZ ha hb) hpow hcycP hC4 hRC hR
          (hRcard.trans (le_antisymm hle4 h4)) ht₀R ht₀ huJ hu (hh.trans hsu)
  ·
    rcases StandardRecognition.quaternion_standard_recognition hCIT hS.nonab hstd
      S hn hSq with hlie | hM11 | hM12
    · exact False.elim (hU (CFSG.ComponentClassification.GSLit.uOutcome_of_oddLieType hlie))
    · obtain ⟨e⟩ : Nonempty (G ≃* Blueprint.NativeSporadic.M11) := hM11
      have hG : Nat.card G = 7920 :=
        (Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.card_M11
      rw [hG] at h7
      omega
    · obtain ⟨e⟩ : Nonempty (G ≃* Blueprint.NativeSporadic.M12) := hM12
      have hG : Nat.card G = 95040 :=
        (Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.card_M12
      rw [hG] at h7
      omega

theorem card_sylow_centralizer_eq_two_of_onan_of_classicalInvolution
    (hCIT : StandardRecognition.ClassicalInvolutionTheoremModels)
    [IsSimpleGroup G] (hnonab : ∃ g h : G, g * h ≠ h * g)
    (hK : Assembly.KProper Blueprint.Catalog G) (hU : ¬ OutcomeLocal.UOutcome G)
    {J : Subgroup G} (hst : IsStandardSubgroup J)
    (hF : IsSporadic (↥J ⧸ center ↥J) .ONan) (hZ : Odd (Nat.card (center ↥J)))
    (S : Sylow 2 ↥(centralizer (J : Set G))) : Nat.card S = 2 :=
  card_sylow_centralizer_eq_two_of_onan
    (RankTwoSporadic.ONan.sporadicCaseOdd_ONan RankTwoFoundation.lemma32
      RankTwoFoundation.lemma33Three)
    hCIT Foote5.Asc25.asc76Lemma25 hnonab hK hU hst hF hZ S

end CFSG.ComponentClassification.GrSLit.L34Sec5S

end
