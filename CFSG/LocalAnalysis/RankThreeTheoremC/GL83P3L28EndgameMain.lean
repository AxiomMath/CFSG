module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28EndgameBase
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28EndgameAut
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Reduced3
import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantConjugacy
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3KFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3KFactsL28

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28End

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.AGLEmbedding (CatalogSimpleSections exists_mem_sylow_inf_component)

variable {Y : Type} [Group Y] [Finite Y]

theorem mem_normalizer_of_pow_mem' {H : Subgroup Y} {y : Y} {n : ℕ} (hy : y ^ 3 ^ n = 1) {m : ℕ}
    (hm : Nat.Coprime m 3) (hym : y ^ m ∈ normalizer (H : Set Y)) :
    y ∈ normalizer (H : Set Y) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : y = 1 := by simpa using hy
    rw [this]
    exact one_mem _
  · have hcop : Nat.Coprime m (3 ^ n) := Nat.Coprime.pow_right n hm
    obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop
      (Nat.one_lt_pow hn.ne' (by norm_num))
    have h1 : y = (y ^ m) ^ k := by
      rw [← pow_mul, pow_eq_pow_mod (m * k) hy, hk, pow_one]
    rw [h1]
    exact pow_mem hym k

theorem three_dvd_center {K : Subgroup Y} {z : Y} (hzK : z ∈ K) (hzc : ∀ k ∈ K, k * z = z * k)
    (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) : 3 ∣ Nat.card (center K) := by
  have hz : (⟨z, hzK⟩ : K) ∈ center K :=
    Subgroup.mem_center_iff.mpr (fun k => Subtype.ext (hzc k k.2))
  have hord : orderOf (⟨⟨z, hzK⟩, hz⟩ : center K) = 3 := by
    have h1 := Subgroup.orderOf_coe (⟨⟨z, hzK⟩, hz⟩ : center K)
    have h2 := Subgroup.orderOf_coe (⟨z, hzK⟩ : K)
    rw [← h1, ← h2]
    exact orderOf_eq_prime hz3 hz1
  rw [← hord]
  exact _root_.orderOf_dvd_natCard _

namespace EndData

variable {F U M₁ N R : Subgroup Y} {x : Y}

theorem center_not_dvd (hd : EndData F U M₁ N R x) (hCen : KFactCentralOmega) {K : Subgroup Y}
    (hK : IsComponentOf K ⊤) : ¬ 3 ∣ Nat.card (center K) := by
  intro h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : CFSG.Open.IsQuasisimple K := hK.2.2
  haveI hs : IsSimpleGroup (K ⧸ center K) := hq.2
  have hcat : IsCatalogGroup (K ⧸ center K) := by
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hq
    exact hd.catalog.surjective_image K (QuotientGroup.mk' (center K))
      (QuotientGroup.mk'_surjective _) ⟨a, b, hab⟩
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup K) < 4 := by
    obtain ⟨E, -, hE, hcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3
      Nat.prime_three (⊤ : Subgroup K)
    have hE' := CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hE K.subtype
    have h1 := hd.card_elem_le hE'
    rw [Subgroup.card_map_of_injective K.subtype_injective, hcard] at h1
    by_contra hge
    push Not at hge
    have h2 : 3 ^ 4 ≤ 3 ^ CFSG.Open.pRank 3 (⊤ : Subgroup K) :=
      Nat.pow_le_pow_right (by norm_num) hge
    omega
  obtain ⟨S⟩ := (Sylow.nonempty : Nonempty (Sylow 3 K))
  have hS' : IsPGroup 3 ((S : Subgroup K).map K.subtype) := S.isPGroup'.map K.subtype
  obtain ⟨k, -, hk⟩ := GL83P3L28Aux.exists_mem_conj_le_sylow hd.sylow le_top hS'
  have key : ∀ c : K, c ∈ (S : Subgroup K) → c ^ 3 = 1 → k⁻¹ * (c : Y) * k ∈ U := by
    intro c hc hc3
    refine hd.toFData.omega _ (hk c ⟨c, hc, rfl⟩) ?_
    have hc3' : (c : Y) ^ 3 = 1 := by simpa using congrArg Subtype.val hc3
    calc (k⁻¹ * (c : Y) * k) ^ 3 = k⁻¹ * (c : Y) ^ 3 * k := by
          have := conj_pow (a := k⁻¹) (b := (c : Y)) (i := 3)
          simpa using this
      _ = 1 := by rw [hc3']; group
  refine hCen K hq hcat h3 hrank S (fun a ha b hb ha3 hb3 => ?_)
  have h2 : k⁻¹ * ((a : Y) * b) * k = k⁻¹ * ((b : Y) * a) * k := by
    have h1 := hd.toFData.U_comm (key a ha ha3) (key b hb hb3)
    calc k⁻¹ * ((a : Y) * b) * k = (k⁻¹ * (a : Y) * k) * (k⁻¹ * (b : Y) * k) := by group
      _ = (k⁻¹ * (b : Y) * k) * (k⁻¹ * (a : Y) * k) := h1
      _ = k⁻¹ * ((b : Y) * a) * k := by group
  exact Subtype.ext (by simpa using h2)

theorem le_normalizer_comp (hd : EndData F U M₁ N R x)
    (hcore : primeComplementCore (G := Y) 3 = ⊥) {K : Subgroup Y} (hK : IsComponentOf K ⊤) :
    F ≤ normalizer (K : Set Y) := by
  classical
  intro f hf
  by_contra hfK
  obtain ⟨n, hn⟩ := hd.sylow.isPGroup ⟨f, hf⟩
  have hfn : f ^ 3 ^ n = 1 := congrArg Subtype.val hn
  set g : ℕ → Subgroup Y := fun i => K.map (MulAut.conj (f ^ i)).toMonoidHom with hg
  have hgK : ∀ i, IsComponentOf (g i) ⊤ := fun i =>
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj (f ^ i)) K).mpr hK
  have hinj : Set.InjOn g (Finset.range 3 : Set ℕ) := by
    have key : ∀ i j : ℕ, i < j → j < 3 → g i ≠ g j := by
      intro i j hij hj hgij
      apply hfK
      refine mem_normalizer_of_pow_mem' hfn (m := j - i) ?_ ?_
      · exact (Nat.coprime_of_lt_prime (by omega) (by omega) Nat.prime_three).symm
      · rw [mem_normalizer_iff_map_conj_eq]
        have h1 : g j = (g (j - i)).map (MulAut.conj (f ^ i)).toMonoidHom := by
          simp only [hg]
          rw [← CFSG.RankThreeEvenClassification.Helpers.subgroup_map_conj_mul, ← pow_add,
            Nat.add_sub_cancel' hij.le]
        rw [h1] at hgij
        exact (map_injective (MulAut.conj (f ^ i)).injective hgij).symm
    intro i hi j hj hgij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rcases lt_trichotomy i j with h | h | h
    · exact absurd hgij (key i j h hj)
    · exact h
    · exact absurd hgij.symm (key j i h hi)
  have hcard := card_le_pRank_of_isComponentOf Nat.prime_three (by norm_num) hcore
    ((Finset.range 3).image g) (fun K' hK' => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hK'
      exact hgK i)
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at hcard
  have := hd.pRank_le_two
  omega

theorem exists_central_comp (hd : EndData F U M₁ N R x)
    (hcore : primeComplementCore (G := Y) 3 = ⊥) {K : Subgroup Y} (hK : IsComponentOf K ⊤) :
    ∃ z ∈ K ⊓ U, z ≠ 1 ∧ z ^ 3 = 1 ∧ ∀ f ∈ F, f * z = z * f := by
  obtain ⟨S, hS⟩ := hd.exists_sylow
  obtain ⟨t, htS, hto, -⟩ := exists_mem_sylow_inf_component Nat.prime_three (by norm_num) hcore S hK
  have hNF := hd.le_normalizer_comp hcore hK
  rw [hS] at htS
  have hne : F ⊓ K ≠ ⊥ := by
    intro h
    have ht1 : t = 1 := by simpa [h] using htS
    rw [ht1, orderOf_one] at hto
    omega
  obtain ⟨z, hz, hz1, hz3, hzc⟩ := FData.exists_central (A := F ⊓ K) hd.sylow.isPGroup inf_le_left
    (fun f hf a ha => ⟨F.mul_mem (F.mul_mem hf ha.1) (F.inv_mem hf),
      ((mem_normalizer_iff.mp (hNF hf)) a).mp ha.2⟩) hne
  exact ⟨z, ⟨hz.2, hd.toFData.omega z hz.1 hz3⟩, hz1, hz3, hzc⟩

theorem comp_unique (hd : EndData F U M₁ N R x) (hcore : primeComplementCore (G := Y) 3 = ⊥)
    (hCen : KFactCentralOmega) {K₁ K₂ : Subgroup Y} (h₁ : IsComponentOf K₁ ⊤)
    (h₂ : IsComponentOf K₂ ⊤) : K₁ = K₂ := by
  by_contra hne
  obtain ⟨z₁, hz₁, hz₁1, -, hz₁c⟩ := hd.exists_central_comp hcore h₁
  obtain ⟨z₂, hz₂, hz₂1, hz₂3, hz₂c⟩ := hd.exists_central_comp hcore h₂
  have h12 : K₂ ≤ centralizer (K₁ : Set Y) := le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne K₁ K₂ h₁ h₂ hne))
  refine hd.toFData.false_of_central hz₁.2 hz₂.2 hz₁1 ?_ hz₁c hz₂c
  intro hmem
  have hz₂K₁ : z₂ ∈ K₁ := (zpowers_le.mpr hz₁.1) hmem
  exact hd.center_not_dvd hCen h₁ (three_dvd_center hz₂K₁
    (fun k hk => (mem_centralizer_iff.mp (h12 hz₂.1) k hk)) hz₂1 hz₂3)

theorem pCore_eq_bot (hd : EndData F U M₁ N R x) (hcore : primeComplementCore (G := Y) 3 = ⊥)
    (hCen : KFactCentralOmega) {K : Subgroup Y} (hK : IsComponentOf K ⊤) :
    CFSG.pCore 3 Y = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hO
  obtain ⟨S, hS⟩ := hd.exists_sylow
  have hOF : CFSG.pCore 3 Y ≤ F := by
    have := CFSG.pCore_isPGroup.le_sylow_of_normal S
    rwa [hS] at this
  obtain ⟨z', hz', hz'1, hz'3, hz'c⟩ := FData.exists_central hd.sylow.isPGroup hOF
    (fun f _ a ha => (CFSG.pCore_normal (p := 3) (G := Y)).conj_mem a ha f) hO
  obtain ⟨z, hz, hz1, hz3, hzc⟩ := hd.exists_central_comp hcore hK
  have hFit : CFSG.fittingSubgroup Y = CFSG.pCore 3 Y := CFSG.Fitting_eq_pcore Y 3 hcore
  have hOC : CFSG.pCore 3 Y ≤ centralizer (CFSG.layer Y : Set Y) := by
    rw [← hFit]
    exact commutator_eq_bot_iff_le_centralizer.mp CFSG.LocalCores.fitting_layer_commute
  have hKL : K ≤ CFSG.layer Y :=
    CFSG.LocalCores.component_le_layer ((CFSG.isComponent_iff_open K).mpr hK)
  have hz'K : z' ∈ centralizer (K : Set Y) := centralizer_le hKL (hOC hz')
  refine hd.toFData.false_of_central (hd.toFData.omega z' (hOF hz') hz'3) hz.2 hz'1 ?_ hz'c hzc
  intro hmem
  have hzC : z ∈ centralizer (K : Set Y) := (zpowers_le.mpr hz'K) hmem
  exact hd.center_not_dvd hCen hK (three_dvd_center hz.1
    (fun k hk => (mem_centralizer_iff.mp hzC k hk)) hz1 hz3)

theorem R_eq_bot (hd : EndData F U M₁ N R x) (hcore : primeComplementCore (G := Y) 3 = ⊥)
    (hCen : KFactCentralOmega) (hM27 : KFactSylowM27) (hGen : KFactFieldGeneration) :
    R = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hcomp : ∃ K : Subgroup Y, IsComponentOf K ⊤
  swap
  · push Not at hcomp
    exact le_bot_iff.mp (hd.R_le.trans (hd.eq_bot_of_noComponent hcore hcomp).le)
  obtain ⟨K, hK⟩ := hcomp
  have hu : ∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K := fun L hL =>
    hd.comp_unique hcore hCen hL hK
  have hKn : K.Normal := ⟨fun n hn g => by
    have hmap : K.map (MulAut.conj g).toMonoidHom = K :=
      hu _ ((CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) K).mpr hK)
    rw [← hmap]
    exact ⟨n, hn, by simp [MulAut.conj_apply]⟩⟩
  haveI := hKn
  have hlay : CFSG.layer Y = K := by
    refine le_antisymm (sSup_le fun L hL => ?_) (le_sSup ((CFSG.isComponent_iff_open K).mpr hK))
    exact (hu L ((CFSG.isComponent_iff_open L).mp hL)).le
  have hO := hd.pCore_eq_bot hcore hCen hK
  have hCK : centralizer (K : Set Y) = ⊥ := by
    have := centralizer_layer_eq_bot_of_pCore_eq_bot hcore hO
    rwa [hlay] at this
  have hZ : center K = ⊥ := center_eq_bot_of_centralizer_layer_eq_bot (by rw [hlay]; exact hCK) hK
  obtain ⟨hs, hnonab⟩ := isSimpleGroup_of_isComponentOf_of_center_eq_bot hK hZ
  have hcat : IsCatalogGroup K := hd.catalog.simple_subgroup K hs hnonab
  obtain ⟨t₀, ht₀F, ht₀U⟩ := hd.toFData.exists_not_mem
  obtain ⟨-, hcyc, hcard9⟩ := hM27 Y K hKn hs hnonab hcat hCK F hd.sylow hd.toFData.card_F
    hd.toFData.nonab ⟨t₀, ht₀F, hd.toFData.pow_ne_one ht₀F ht₀U⟩
  have hSyl : IsSylowOf 3 (F ⊓ K) K :=
    hd.sylow.inf_of_le_normalizer le_top (by rw [normalizer_eq_top K])
  have h3K : 3 ∣ Nat.card K := by
    have := Subgroup.card_dvd_of_le (inf_le_right : F ⊓ K ≤ K)
    rw [hcard9] at this
    exact (dvd_pow_self 3 (by norm_num)).trans this
  by_cases hL28 : IsRankThreeL28 K
  · have h3 : 3 ∣ Nat.card ↥(F ⊓ K) := by
      rw [hcard9]
      exact dvd_pow_self 3 (by norm_num)
    obtain ⟨g', hg'⟩ := exists_prime_orderOf_dvd_card' (G := ↥(F ⊓ K)) 3 h3
    have hgo : orderOf (g' : Y) = 3 := by rw [Subgroup.orderOf_coe]; exact hg'
    have hg3 : (g' : Y) ^ 3 = 1 := hgo ▸ pow_orderOf_eq_one _
    have hg1 : (g' : Y) ≠ 1 := fun h => by rw [h, orderOf_one] at hgo; omega
    have hgU : (g' : Y) ∈ U := hd.toFData.omega _ g'.2.1 hg3
    exact l28_no_invariant_two_group hL28 hCK g'.2.2 hg3 hg1 hd.R_two (hd.R_norm hgU)
  · set T' : Subgroup K := (F ⊓ K).subgroupOf K with hT'
    have hT : IsSylowOf 3 T' ⊤ := by
      rw [← isSylowOf_map_subtype_iff K, hT', subgroupOf_map_subtype, ← MonoidHom.range_eq_map,
        range_subtype, inf_assoc, inf_idem]
      exact hSyl
    have hTe : T' ≃* ↥(F ⊓ K) := subgroupOfEquivOfLe inf_le_right
    have hTcyc : IsCyclic T' := (hTe.isCyclic).mpr hcyc
    have hTcard : Nat.card T' = 3 ^ 2 := by rw [Nat.card_congr hTe.toEquiv]; exact hcard9
    obtain ⟨t₁, ht₁, ht₁U⟩ : ∃ t ∈ F ⊓ K, t ∉ U := by
      by_contra hall
      push Not at hall
      obtain ⟨g, hg⟩ := hcyc.exists_generator
      have hord := orderOf_eq_card_of_forall_mem_zpowers hg
      have h3 : g ^ 3 = 1 :=
        Subtype.ext (by simpa using hd.toFData.U_elem.2 _ (hall g.1 g.2))
      have := orderOf_dvd_of_pow_eq_one h3
      rw [hord, hcard9] at this
      norm_num at this
    obtain ⟨u, huU, hux⟩ := hd.toFData.exists_u
    have hu1 : u ≠ 1 := fun h => hux (h ▸ one_mem _)
    have hu3 : u ^ 3 = 1 := hd.toFData.U_elem.2 u huU
    have huF : u ∈ F := hd.toFData.U_le huU
    let α : MulAut K := MulAut.conjNormal u
    have hα3 : α ^ 3 = 1 := by
      rw [show α = MulAut.conjNormal u from rfl, ← map_pow, hu3, map_one]
    have hα1 : α ≠ 1 := by
      intro h
      apply hu1
      have : u ∈ centralizer (K : Set Y) := by
        rw [mem_centralizer_iff]
        intro k hk
        have h1 := congrArg (fun φ : MulAut K => ((φ ⟨k, hk⟩ : K) : Y)) h
        simp only [α, MulAut.conjNormal_apply, MulAut.one_apply] at h1
        calc k * u = (u * k * u⁻¹) * u := by rw [h1]
          _ = u * k := by group
      rwa [hCK, mem_bot] at this
    have hαo : orderOf α = 3 := orderOf_eq_prime hα3 hα1
    have hαT : T'.map α.toMonoidHom = T' := by
      ext y
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨t, ht, rfl⟩
        rw [hT', mem_subgroupOf] at ht ⊢
        refine ⟨?_, (α t).2⟩
        have := F.mul_mem (F.mul_mem huF ht.1) (F.inv_mem huF)
        simpa [α, MulAut.conjNormal_apply] using this
      · intro hy
        refine ⟨(MulAut.conjNormal u⁻¹ : MulAut K) y, ?_, ?_⟩
        · rw [hT', mem_subgroupOf] at hy ⊢
          refine ⟨?_, (MulAut.conjNormal u⁻¹ y).2⟩
          simpa [MulAut.conjNormal_apply] using
            F.mul_mem (F.mul_mem (F.inv_mem huF) hy.1) huF
        · apply Subtype.ext
          simp only [α, MulEquiv.coe_toMonoidHom, MulAut.conjNormal_apply]
          group
    have hex : ∃ t ∈ T', α t ≠ t := by
      refine ⟨⟨t₁, ht₁.2⟩, ?_, ?_⟩
      · rw [hT', mem_subgroupOf]
        exact ht₁
      · intro hαt
        have h1 := congrArg Subtype.val hαt
        simp only [α, MulAut.conjNormal_apply] at h1
        apply hd.toFData.not_comm huU hux ht₁.1 ht₁U
        calc u * t₁ = (u * t₁ * u⁻¹) * u := by group
          _ = t₁ * u := by rw [h1]
    have hgen := hGen K hs hnonab hcat hL28 T' hT hTcyc hTcard α hαo hαT hex
    have hKM : K ≤ M₁ := by
      intro k hk
      have hk' : (⟨k, hk⟩ : K) ∈ T' ⊔ α.toMonoidHom.eqLocus (MonoidHom.id K) := by
        rw [hgen]
        exact mem_top _
      have hkmap : k ∈ (T' ⊔ α.toMonoidHom.eqLocus (MonoidHom.id K)).map K.subtype :=
        ⟨_, hk', rfl⟩
      rw [Subgroup.map_sup] at hkmap
      have hle : T'.map K.subtype ⊔
          (α.toMonoidHom.eqLocus (MonoidHom.id K)).map K.subtype ≤ M₁ := by
        refine sup_le ?_ ?_
        · rintro _ ⟨t, ht, rfl⟩
          have ht' : (t : Y) ∈ F ⊓ K := mem_subgroupOf.mp (SetLike.mem_coe.mp ht)
          exact hd.F_le ht'.1
        · rintro _ ⟨e, he, rfl⟩
          have he' : α e = e := he
          have h1 := congrArg Subtype.val he'
          simp only [α, MulAut.conjNormal_apply] at h1
          refine hd.cover u huU hux ?_
          rw [mem_centralizer_singleton_iff]
          calc (e : Y) * u = (u * e * u⁻¹) * u := by rw [h1]
            _ = u * e := by group
      exact hle hkmap
    exact le_bot_iff.mp (hd.R_le.trans (hd.eq_bot_of_cover hs h3K hKM hCK).le)

end EndData

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28End
