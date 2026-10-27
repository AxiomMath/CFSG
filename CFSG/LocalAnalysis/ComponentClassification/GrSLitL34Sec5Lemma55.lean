module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma551

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem le_oddIn_of_normalized {L T N : Subgroup G} (hTL : T ≤ L)
    (hTset : (T : Set G) * (oddIn L : Set G) = L) (hNL : N ≤ L) (hNodd : Odd (Nat.card N))
    (hTN : T ≤ normalizer (N : Set G)) : N ≤ oddIn L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥L) with hπ
  set N' : Subgroup ↥L := N.subgroupOf L with hN'
  have hdec : ∀ l : ↥L, ∃ y ∈ T, ∃ hyL : y ∈ L, π l = π ⟨y, hyL⟩ := by
    intro l
    have hl : (l : G) ∈ (T : Set G) * (oddIn L : Set G) := by rw [hTset]; exact l.2
    obtain ⟨y, hy, o, ho, hyo⟩ := hl
    refine ⟨y, hy, hTL hy, ?_⟩
    obtain ⟨o', ho', rfl⟩ := ho
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hyo' : y * (o' : G) = l := hyo
    have e : l⁻¹ * (⟨y, hTL hy⟩ : ↥L) = o'⁻¹ := by
      apply Subtype.ext
      simp only [coe_mul, coe_inv]
      rw [← hyo']
      group
    rw [e]
    exact inv_mem ho'
  have hNn : (N'.map π).Normal := by
    constructor
    rintro _ ⟨n, hn, rfl⟩ g
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥L) g
    obtain ⟨y, hy, hyL, hly⟩ := hdec l
    rw [show (QuotientGroup.mk' (pPrimeCore 2 ↥L)) l = π l from rfl, hly, ← map_mul, ← map_inv,
      ← map_mul]
    refine ⟨⟨y, hyL⟩ * n * ⟨y, hyL⟩⁻¹, ?_, rfl⟩
    rw [SetLike.mem_coe] at hn
    rw [SetLike.mem_coe, hN', mem_subgroupOf] at *
    simpa using (mem_normalizer_iff.mp (hTN hy) _).mp hn
  have hcop : Nat.Coprime 2 (Nat.card (N'.map π)) := by
    have h1 : Nat.card N' = Nat.card N := Nat.card_congr (subgroupOfEquivOfLe hNL).toEquiv
    exact Nat.coprime_two_left.mpr ((h1 ▸ hNodd).of_dvd_nat (card_map_dvd N' π))
  have hbot : N'.map π = ⊥ := by
    have h1 : N'.map π ≤ pPrimeCore 2 (↥L ⧸ pPrimeCore 2 ↥L) := le_sSup ⟨hNn, hcop⟩
    rwa [CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot, le_bot_iff] at h1
  intro x hx
  have h1 : π ⟨x, hNL hx⟩ ∈ N'.map π := ⟨⟨x, hNL hx⟩, hx, rfl⟩
  rw [hbot, mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact ⟨⟨x, hNL hx⟩, h1, rfl⟩

theorem mem_oddIn_of_mem_zStarIn {K : Subgroup G} {x : G} (hx : x ∈ zStarIn K)
    (hodd : Odd (orderOf x)) : x ∈ oddIn K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x', hx', rfl⟩ := hx
  rw [SetLike.mem_coe, Sol78.fusionZStar_eq_comap, mem_comap] at hx'
  obtain ⟨n, hn⟩ := UnbalancedGS.SwappedCentralProduct.pow_two_pow_eq_one_of_mem_center
    (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥K) 2) hx'
  set y := QuotientGroup.mk' (pPrimeCore 2 ↥K) x' with hy
  have h1 : orderOf y ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have h2 : orderOf y ∣ orderOf x' := orderOf_map_dvd _ _
  have h3 : orderOf x' = orderOf (x' : G) := (Subgroup.orderOf_coe x').symm
  have h4 : orderOf y = 1 := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    rcases m with _ | m
    · simpa using hm
    · exfalso
      rw [hm, h3] at h2
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr
        ((dvd_pow_self 2 (Nat.succ_ne_zero m)).trans h2))
  rw [orderOf_eq_one_iff, hy, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h4
  exact ⟨x', h4, rfl⟩

theorem inf_le_zStarIn_of_ne {C K₁ K₂ : Subgroup G} (hK₁C : K₁ ≤ C) (hK₂C : K₂ ≤ C)
    (hK₁ : IsPComponent 2 (K₁.subgroupOf C)) (hK₂ : IsPComponent 2 (K₂.subgroupOf C))
    (hne : K₁ ≠ K₂) : K₁ ⊓ K₂ ≤ zStarIn K₁ := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := mem_inf.mp hx
  have hcomm := commute_mod_of_ne hK₂C hK₁C hK₂ hK₁ (Ne.symm hne)
  refine ⟨⟨x, hx1⟩, GSThmB.OddQuot.mem_fusionZStar_iff.mpr fun m => ?_, rfl⟩
  have h1 : x * m * x⁻¹ * (m : G)⁻¹ ∈ oddIn C ⊓ K₁ :=
    mem_inf.mpr ⟨hcomm x hx2 m m.2, mul_mem (mul_mem (mul_mem hx1 m.2) (inv_mem hx1))
      (inv_mem m.2)⟩
  obtain ⟨y, hy, hyeq⟩ := inf_oddIn_le_oddIn hK₁C h1
  have e : ⁅(⟨x, hx1⟩ : ↥K₁), m⁆ = y := by
    apply Subtype.ext
    rw [show ((y : ↥K₁) : G) = x * m * x⁻¹ * (m : G)⁻¹ from hyeq, commutatorElement_def]
    simp
  rw [e]
  exact hy

theorem mem_normalizer_map_pLayer {H : Subgroup G} {h : G} (hh : h ∈ H) :
    h ∈ normalizer (((pLayer ↥H 2).map H.subtype : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (pLayer ↥H 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
  have hn : (pLayer ↥H 2).Normal := inferInstance
  rw [mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨h, hh⟩ * p * ⟨h, hh⟩⁻¹, hn.conj_mem p hp _, by simp⟩
  · rintro ⟨p, hp, hpe⟩
    refine ⟨⟨h, hh⟩⁻¹ * p * ⟨h, hh⟩, ?_, ?_⟩
    · have := hn.conj_mem p hp ⟨h, hh⟩⁻¹
      simpa using this
    · simp only [coe_subtype, coe_mul, coe_inv] at hpe ⊢
      rw [hpe]
      group

omit [Finite G] in
theorem omegaOne_le (H : Subgroup G) : omegaOne H ≤ H :=
  closure_le _ |>.mpr fun _ hh => hh.1

omit [Finite G] in
theorem omegaOne_omegaOne (H : Subgroup G) : omegaOne (omegaOne H) = omegaOne H :=
  le_antisymm (omegaOne_le _) (closure_le _ |>.mpr fun _ hh => subset_closure
    ⟨subset_closure hh, hh.2⟩)

theorem wGroup_zpowers_eq_bot_of_setting (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) {z : G}
    (hzQ : z ∈ S ⊓ coreActionKernel L) (hz : orderOf z = 2) :
    wGroup (zpowers z ⊔ zpowers t) = ⊥ := by
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  obtain ⟨hbase, hfam, -, -, -, -, -⟩ := hset
  obtain ⟨hsimple, hnonab, hK, -, -, hloc, -, -⟩ := hbase
  obtain ⟨⟨-, -, -, -, -, hto, -, -⟩, htypeL, -, -, hW8'⟩ := hfam
  have : IsSimpleGroup G := hsimple
  have hGWb := gwTwoBalanced_of_locallyTwoBalanced hSol hloc
  obtain ⟨hzS, hzK⟩ := mem_inf.mp hzQ
  have htz : t * z = z * t := (hZS z hzS).symm
  have hz1 : z ≠ 1 := by rintro rfl; simp at hz
  have ht1 : t ≠ 1 := by rintro rfl; simp at hto
  have hz2 : z * z = 1 := by rw [← pow_two, ← hz, pow_orderOf_eq_one]
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  have hzZ : z ∉ center G := not_mem_center_of_ne_one hnonab hz1
  obtain ⟨hTtz, -, -, hTset, -, ⟨φ⟩⟩ := gsFixedLayer_facts hS hK hto hz htz hzZ hLt hLpt hzK
  obtain ⟨hTL, -⟩ := gsFixedLayer_sup_oddIn hTset
  obtain ⟨eT⟩ := nonempty_fusionZStar_equiv_of_quotient_equiv φ
  have htypeT : IsL34Type (gsFixedLayer L z ⧸ Open.fusionZStar (gsFixedLayer L z)) :=
    LieType.CurtisTits.lieModel_of_mulEquiv eT.symm htypeL
  obtain ⟨W, hWT, hW, hW4, hWC⟩ := exists_four_inf_centralizer htypeT
  have hWL : W ≤ L := hWT.trans hTL
  have hWz : ∀ w ∈ W, z * w = w * z := fun w hw =>
    (mem_centralizer_singleton_iff.mp ((hWT.trans (hTtz.trans inf_le_right)) hw)).symm
  have htL : t ∈ centralizer (L : Set G) := mem_centralizer_iff.mpr fun l hl =>
    mem_centralizer_singleton_iff.mp (hLt hl)
  have htW : t ∉ W := by
    intro h
    have : t ∈ W ⊓ centralizer (gsFixedLayer L z : Set G) :=
      mem_inf.mpr ⟨h, centralizer_le hTL htL⟩
    rw [hWC] at this
    exact ht1 (mem_bot.mp this)
  have htWc : ∀ w ∈ W, t * w = w * t := fun w hw => ((mem_centralizer_iff.mp htL) w (hWL hw)).symm
  obtain ⟨hE₁, hE₁c⟩ := elemTwo_zpowers_sup ht2 hW htWc htW
  have hE₁L : zpowers t ⊔ W ≤ L ⊔ zpowers t := sup_le le_sup_right (hWL.trans le_sup_left)
  have hWE₁ : wGroup (zpowers t ⊔ W) = ⊥ := hW8' _ ⟨hE₁, by rw [hE₁c, hW4]⟩ (Or.inl hE₁L)
  by_cases hzE : z ∈ zpowers t ⊔ W
  · apply le_bot_iff.mp
    rw [← hWE₁]
    exact wGroup_mono (sup_le (zpowers_le.mpr hzE) le_sup_left)
  · have hzE₁ : ∀ y ∈ zpowers t ⊔ W, z * y = y * z := by
      intro y hy
      have hle : zpowers t ⊔ W ≤ centralizer ({z} : Set G) := sup_le
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr htz))
        fun w hw => mem_centralizer_singleton_iff.mpr (hWz w hw).symm
      exact (mem_centralizer_singleton_iff.mp (hle hy)).symm
    obtain ⟨hA, hAc⟩ := elemTwo_zpowers_sup hz2 hE₁ hzE₁ hzE
    have hA16 : 16 ≤ Nat.card ↥(zpowers z ⊔ (zpowers t ⊔ W)) := by rw [hAc, hE₁c, hW4]
    have hE₁8 : 8 ≤ Nat.card ↥(zpowers t ⊔ W) := by rw [hE₁c, hW4]
    have hconn : AbelianConnected 3 (zpowers t ⊔ W) (zpowers z ⊔ (zpowers t ⊔ W)) :=
      ⟨rank3 hE₁ hE₁8, Relation.ReflTransGen.single ⟨rank3 hA (by omega),
        fun a ha b hb => hA.1 a (mem_sup_right ha) b hb⟩⟩
    have hself : AbelianConnected 3 (zpowers z ⊔ (zpowers t ⊔ W))
        (zpowers z ⊔ (zpowers t ⊔ W)) := ⟨rank3 hA (by omega), Relation.ReflTransGen.refl⟩
    obtain ⟨hGW1, -⟩ := hGW G hGWb _ hA.1 hA.2 hA16
    obtain ⟨-, hWeq, -⟩ := hGW1 _ _ hself hconn
    rw [hWE₁] at hWeq
    apply le_bot_iff.mp
    rw [hWeq]
    exact wGroup_mono (sup_le le_sup_left (zpowers_le.mpr
      (mem_sup_right (mem_sup_left (mem_zpowers t)))))

theorem conj_eq_inv_of_setting (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) {z : G}
    (hzQ : z ∈ S ⊓ coreActionKernel L) (hz : orderOf z = 2) (hzt : z ≠ t) :
    ∀ y ∈ oddIn L, z * y * z⁻¹ = y⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hset' := hset
  have hWzt := wGroup_zpowers_eq_bot_of_setting hS hU hheld hSol hGW hset hzQ hz
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  obtain ⟨hbase, hfam, -, -, htS, -, -⟩ := hset
  obtain ⟨hsimple, hnonab, hK, -, -, -, -, hUtypes⟩ := hbase
  obtain ⟨⟨-, -, -, -, -, hto, -, -⟩, -, -, -, -⟩ := hfam
  have : IsSimpleGroup G := hsimple
  obtain ⟨hzS, hzK⟩ := mem_inf.mp hzQ
  have htz : t * z = z * t := (hZS z hzS).symm
  have hz1 : z ≠ 1 := by rintro rfl; simp at hz
  have hz2 : z * z = 1 := by rw [← pow_two, ← hz, pow_orderOf_eq_one]
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  have hzN : z ∈ normalizer (L : Set G) := (mem_coreActionKernel.mp hzK).1
  have htL : t ∈ centralizer (L : Set G) := mem_centralizer_iff.mpr fun l hl =>
    mem_centralizer_singleton_iff.mp (hLt hl)
  have htK : t ∈ coreActionKernel L := mem_coreActionKernel_of_commute fun l hl =>
    ((mem_centralizer_iff.mp htL) l hl).symm
  have hXt : oddIn L ≤ oddIn (centralizer ({t} : Set G)) :=
    GSLit.map_pPrimeCore_le_of_isPComponent hLt hLpt
  set Y := oddIn L ⊓ centralizer ({z} : Set G) with hYdef
  by_cases hY : Y = ⊥
  · exact conj_eq_inv_of_inf_centralizer_eq_bot (normalizer_le_normalizer_oddIn L hzN) hz2 hY
  exfalso
  have hYt : ∀ x ∈ Y, x * t = t * x := fun x hx =>
    (mem_centralizer_iff.mp htL) x (map_subtype_le _ (mem_inf.mp hx).1)
  have hYzt : Y ≤ centralizer ({z * t} : Set G) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    have h1 := mem_centralizer_singleton_iff.mp (mem_inf.mp hx).2
    calc x * (z * t) = (x * z) * t := by group
      _ = z * x * t := by rw [h1]
      _ = z * (x * t) := by group
      _ = z * (t * x) := by rw [hYt x hx]
      _ = z * t * x := by group
  have hex : ∃ z₁ ∈ ({z, z * t} : Set G), ¬ Y ≤ oddIn (centralizer ({z₁} : Set G)) := by
    by_contra hall
    push Not at hall
    have h₁ := hall z (Set.mem_insert z _)
    have h₂ := hall (z * t) (Set.mem_insert_of_mem z rfl)
    apply hY
    apply le_bot_iff.mp
    rw [← hWzt]
    have hzt' : z ∉ zpowers t := by
      intro h
      rcases eq_one_or_eq_of_mem_zpowers' ht2 h with h1 | h1
      · exact hz1 h1
      · exact hzt h1
    obtain ⟨hB, hBc⟩ := elemTwo_zpowers_sup hz2 (isElemTwo_zpowers ht2) (fun y hy => by
      obtain ⟨l, rfl⟩ := mem_zpowers_iff.mp hy
      exact (Commute.zpow_right (show Commute z t from htz.symm) l).eq) hzt'
    refine le_trans ?_ (le_iSup _ (zpowers z ⊔ zpowers t))
    refine le_trans ?_ (le_iSup _ le_rfl)
    refine le_trans ?_ (le_iSup _ (by rw [hBc, Nat.card_zpowers, hto]))
    refine le_trans ?_ (le_iSup (fun _ : ∀ b ∈ zpowers z ⊔ zpowers t, b * b = 1 => _) hB.2)
    intro x hx
    simp only [mem_iInf]
    intro b hb hb1
    rcases mem_four_of_mem_sup hz2 ht2 htz.symm hb with h | h | h | h
    · exact absurd h hb1
    · rw [h]
      exact h₁ hx
    · rw [h]
      exact hXt (mem_inf.mp hx).1
    · rw [h]
      exact h₂ hx
  obtain ⟨z₁, hz₁, hYn⟩ := hex
  have hz₁Q : z₁ ∈ S ⊓ coreActionKernel L := by
    rcases hz₁ with rfl | rfl
    · exact hzQ
    · exact mem_inf.mpr ⟨mul_mem hzS htS, mul_mem hzK htK⟩
  have hYz₁ : Y ≤ centralizer ({z₁} : Set G) := by
    rcases hz₁ with rfl | rfl
    · exact inf_le_right
    · exact hYzt
  have hz₁t : z₁ * t = t * z₁ := by
    rcases hz₁ with rfl | rfl
    · exact htz.symm
    · calc z * t * t = z := by rw [mul_assoc, ht2, mul_one]
        _ = t * (z * t) := by rw [← mul_assoc, htz, mul_assoc, ht2, mul_one]
  have hz₁o : orderOf z₁ = 2 := by
    rcases hz₁ with rfl | rfl
    · exact hz
    · refine orderOf_eq_prime ?_ ?_
      · rw [pow_two]
        calc z * t * (z * t) = z * (t * z) * t := by group
          _ = z * (z * t) * t := by rw [htz]
          _ = (z * z) * (t * t) := by group
          _ = 1 := by rw [hz2, ht2, one_mul]
      · intro h
        apply hzt
        have := eq_inv_of_mul_eq_one_left h
        rw [this, inv_eq_of_mul_eq_one_right ht2]
  have hz₁1 : z₁ ≠ 1 := by rintro rfl; simp at hz₁o
  have hz₁Z : z₁ ∉ center G := not_mem_center_of_ne_one hnonab hz₁1
  have hYD : Y ≤ oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({z₁} : Set G) :=
    le_inf (inf_le_left.trans hXt) hYz₁
  obtain ⟨M₁, hM₁z, hM₁p, hM₁Y⟩ := exists_isPComponent_not_le hSol hto hz₁o hz₁t.symm hYD hYn
  have hU₁ := gsUnbalancingTriple_of_not_le hSol hto hz₁o hz₁t.symm hM₁z hM₁p hYD hM₁Y
  have htype : (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      Blueprint.LieModel (M₁ ⧸ pPrimeCore 2 M₁) .PSL 2 p f) ∨
      IsL34Type (M₁ ⧸ Open.fusionZStar M₁) := by
    rcases hUtypes z₁ t M₁ hU₁ with h | h | h
    · exact Or.inl ⟨5, 1, by norm_num, by norm_num, le_rfl, h⟩
    · exact Or.inl ⟨7, 1, by norm_num, by norm_num, le_rfl, h⟩
    · exact Or.inr h
  obtain ⟨hTM, hTO, hMn, -, -⟩ := isPComponent_eq_of_setting hS hU hheld hSol hGW hMax hL34
    hset' hz₁Q hz₁o hM₁z hM₁p htype
  apply hM₁Y
  obtain ⟨-, -, -, -, hO₁, -⟩ := gsFixedLayer_facts hS hK hto hz₁o hz₁t.symm hz₁Z hLt hLpt
    (mem_inf.mp hz₁Q).2
  set T₁ := gsFixedLayer L z₁ with hT₁
  have hTL₁ : T₁ ≤ L := (gsFixedLayer_le_inf L z₁).trans inf_le_left
  have hT₁N : T₁ ≤ normalizer (oddIn M₁ : Set G) := fun x hx =>
    normalizer_le_normalizer_oddIn M₁ (le_normalizer (hTM hx))
  have hT₁set : (T₁ : Set G) * (oddIn M₁ : Set G) = M₁ := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right T₁ (oddIn M₁) hT₁N, hTO]
  have hOT₁ : oddIn T₁ ≤ oddIn M₁ := by
    refine le_oddIn_of_normalized hTM hT₁set ((map_subtype_le _).trans hTM) ?_
      fun x hx => normalizer_le_normalizer_oddIn T₁ (le_normalizer hx)
    rw [oddIn, card_map_of_injective (subtype_injective _)]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  rw [commutator_le]
  intro m hm y hy
  have hyL : y ∈ L := map_subtype_le _ (mem_inf.mp hy).1
  have hyX : y ∈ oddIn L := (mem_inf.mp hy).1
  have hyT : y ∈ normalizer (T₁ : Set G) :=
    mem_normalizer_map_pLayer (H := L ⊓ centralizer ({z₁} : Set G)) (mem_inf.mpr ⟨hyL, hYz₁ hy⟩)
  have hyO : y ∈ normalizer (oddIn M₁ : Set G) := normalizer_le_normalizer_oddIn M₁
    (mem_normalizer_of_conjugate_eq (hMn y (hYz₁ hy)))
  have hm' : m ∈ (T₁ : Set G) * (oddIn M₁ : Set G) := by rw [hT₁set]; exact hm
  obtain ⟨τ, hτ, o, ho, rfl⟩ := hm'
  have hτy : τ * y * τ⁻¹ * y⁻¹ ∈ oddIn M₁ := by
    apply hOT₁
    rw [hO₁]
    refine mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : y * τ⁻¹ * y⁻¹ ∈ T₁ := (mem_normalizer_iff.mp hyT _).mp (inv_mem hτ)
      rw [show τ * y * τ⁻¹ * y⁻¹ = τ * (y * τ⁻¹ * y⁻¹) by group]
      exact mul_mem hτ h1
    · have h1 : τ * y * τ⁻¹ ∈ oddIn L := (mem_normalizer_iff.mp
        (normalizer_le_normalizer_oddIn L (le_normalizer (hTL₁ hτ))) y).mp hyX
      exact mul_mem h1 (inv_mem hyX)
  have hoy : o * y * o⁻¹ * y⁻¹ ∈ oddIn M₁ := by
    have h1 : y * o⁻¹ * y⁻¹ ∈ oddIn M₁ := (mem_normalizer_iff.mp hyO _).mp (inv_mem ho)
    rw [show o * y * o⁻¹ * y⁻¹ = o * (y * o⁻¹ * y⁻¹) by group]
    exact mul_mem ho h1
  have e : ⁅τ * o, y⁆ = τ * (o * y * o⁻¹ * y⁻¹) * τ⁻¹ * (τ * y * τ⁻¹ * y⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact mul_mem ((mem_normalizer_iff.mp (hT₁N hτ) _).mp hoy) hτy

omit [Finite G] in
theorem mem_of_mul_self_mem_of_odd {H : Subgroup G} {x : G} (hodd : Odd (orderOf x))
    (hx : x * x ∈ H) : x ∈ H := by
  obtain ⟨m, hm⟩ := hodd
  have e : x = (x * x) ^ (m + 1) := by
    rw [← pow_two, ← pow_mul, show 2 * (m + 1) = 2 * m + 1 + 1 by ring, pow_succ, ← hm,
      pow_orderOf_eq_one, one_mul]
  rw [e]
  exact pow_mem hx _

theorem commute_of_mem_unbalancingSet (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    {L : Subgroup G} {t : G} {S T : Subgroup G} (hset : L34Sec5Setting G L t S T) {w u : G}
    (hwQ : w ∈ S ⊓ coreActionKernel L) (hu : u ∈ S ⊓ L ⊔ zpowers t) : w * u = u * w := by
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  obtain ⟨-, -, -, hSyl, htS, -, -⟩ := hset
  obtain ⟨hwS, hwK⟩ := mem_inf.mp hwQ
  have hSp : IsPGroup 2 S := IsSylowTwoIn.isPGroup hSyl
  have hoddL : Odd (Nat.card (oddIn L)) := by
    rw [oddIn, card_map_of_injective (subtype_injective _)]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  rw [sup_comm] at hu
  obtain ⟨i, l, hl, rfl⟩ := mem_zpowers_sup (fun y hy => (hZS y (mem_inf.mp hy).1).symm) hu
  obtain ⟨hlS, hlL⟩ := mem_inf.mp hl
  have hc : w * l * w⁻¹ * l⁻¹ = 1 := by
    have h1 : w * l * w⁻¹ * l⁻¹ ∈ oddIn L := conj_mem_oddIn_of_mem_coreActionKernel hwK l hlL
    have h2 : w * l * w⁻¹ * l⁻¹ ∈ S :=
      mul_mem (mul_mem (mul_mem hwS hlS) (inv_mem hwS)) (inv_mem hlS)
    have h3 := eq_bot_of_le_two_group_of_le_odd hSp hoddL (zpowers_le.mpr h2)
      (zpowers_le.mpr h1)
    exact zpowers_eq_bot.mp h3
  have hwl : w * l = l * w := by
    have := congrArg (· * l * w) hc
    simpa [mul_assoc] using this
  have hwt : w * t ^ i = t ^ i * w := (Commute.zpow_right (show Commute w t from hZS w hwS) i).eq
  calc w * (t ^ i * l) = t ^ i * (w * l) := by rw [← mul_assoc, hwt, mul_assoc]
    _ = t ^ i * l * w := by rw [hwl, mul_assoc]

end CFSG.ComponentClassification.GrSLit.GrS5
