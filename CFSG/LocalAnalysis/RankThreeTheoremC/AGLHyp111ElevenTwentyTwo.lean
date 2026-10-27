module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111ElevenTwentySix
public import CFSG.LocalAnalysis.RankThreeTheoremC.PGroupRankTwoCharSubgroupOf
public import CFSG.GroupTheory.PRankCoprimeQuotient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

section Generic

variable {X : Type} [Group X] [Finite X]

theorem le_of_le_sup_of_not_dvd {p : ℕ} [hp : Fact p.Prime] {S T C : Subgroup X} [C.Normal]
    (hT : IsPGroup p T) (hTN : T ≤ Subgroup.normalizer (S : Set X)) (hC : ¬ p ∣ Nat.card C) (h : T ≤ S ⊔ C) :
    T ≤ S := by
  set U := T ⊔ S with hUdef
  have hUN : U ≤ Subgroup.normalizer (S : Set X) := sup_le hTN Subgroup.le_normalizer
  have hSU : S ≤ U := le_sup_right
  have hTU : T ≤ U := le_sup_left
  haveI : (S.subgroupOf U).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUN
  have htop : T.subgroupOf U ⊔ S.subgroupOf U = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hTU hSU, Subgroup.subgroupOf_self]
  have hidx : (S.subgroupOf U).index = (S.subgroupOf U).relIndex (T.subgroupOf U) := by
    rw [← Subgroup.relIndex_sup_right, htop, Subgroup.relIndex_top_right]
  have hdvdT : (S.subgroupOf U).index ∣ Nat.card T := by
    rw [hidx, Subgroup.relIndex]
    have := Subgroup.index_dvd_card ((S.subgroupOf U).subgroupOf (T.subgroupOf U))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTU).toEquiv] at this
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT
  rw [hn] at hdvdT
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).mp hdvdT
  have hcU : Nat.card S * (S.subgroupOf U).index = Nat.card U := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSU).toEquiv]
    exact Subgroup.card_mul_index _
  have hUSC : Nat.card U ∣ Nat.card (S ⊔ C : Subgroup X) :=
    Subgroup.card_dvd_of_le (sup_le h le_sup_left)
  have hSC : Nat.card (S ⊔ C : Subgroup X) ∣ Nat.card C * Nat.card S := by
    rw [← Subgroup.relIndex_mul_card (H := C) (K := S ⊔ C),
      inf_eq_left.mpr (le_sup_right : C ≤ S ⊔ C), Subgroup.relIndex_sup_right, mul_comm]
    exact Nat.mul_dvd_mul_left _ (Subgroup.relIndex_dvd_card C S)
  have hm : (S.subgroupOf U).index ∣ Nat.card C := by
    have h1 := hcU ▸ hUSC.trans hSC
    rw [mul_comm (Nat.card C)] at h1
    exact Nat.dvd_of_mul_dvd_mul_left Nat.card_pos h1
  have hj0 : j = 0 := by
    by_contra hj0
    exact hC ((dvd_pow_self p hj0).trans (hj ▸ hm))
  rw [hj0, pow_zero] at hj
  have hU : U ≤ S := by
    have h1 : S.relIndex U = 1 := hj
    exact Subgroup.relIndex_eq_one.mp h1
  exact hTU.trans hU

theorem center_eq_bot_of_isLinThreeFour {K : Type} [Group K] (h : IsLinThreeFour K) :
    Subgroup.center K = ⊥ := by
  have := isSimpleGroup_of_isLinThreeFour' h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with hb | ht
  · exact hb
  · exfalso
    let : CommGroup K := { ‹Group K› with
      mul_comm := fun a b => (Subgroup.mem_center_iff.1 (ht ▸ Subgroup.mem_top a) b).symm }
    have hp := IsSimpleGroup.prime_card (α := K)
    rw [card_of_isLinThreeFour h] at hp
    exact absurd hp (by norm_num)

theorem not_dvd_card_centralizer {K E : Subgroup X} (hK : IsLinThreeFour K) (hEK : E ≤ K)
    (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 9) (hrk : Open.pRank 3 (⊤ : Subgroup X) ≤ 2) :
    ¬ 3 ∣ Nat.card (Subgroup.centralizer (K : Set X)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h3
  obtain ⟨⟨c, hcC⟩, hc⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer (K : Set X)) 3 h3
  rw [Subgroup.orderOf_mk] at hc
  have hcE : c ∉ E := by
    intro hcE
    have hcZ : (⟨c, hEK hcE⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro k
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hcC k k.2)
    rw [center_eq_bot_of_isLinThreeFour hK, Subgroup.mem_bot] at hcZ
    have : c = 1 := congrArg Subtype.val hcZ
    rw [this, orderOf_one] at hc
    norm_num at hc
  obtain ⟨hF, hFc⟩ := isElemAbelian_sup_zpowers hE hcE hc fun a ha =>
    Subgroup.mem_centralizer_iff.1 hcC a (hEK ha)
  have := CFSG.SectionRank.le_pRank (k := 3) (by norm_num) le_top hF (by rw [hFc, hEc]; norm_num)
  omega

@[expose] def KFactL34A6Normalizer : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K S T : Subgroup X), K.Normal → IsLinThreeFour K →
    Subgroup.centralizer (K : Set X) = ⊥ → S ≤ K → S ≠ K → 360 ∣ Nat.card S →
    IsPGroup 3 T → T ≤ Subgroup.normalizer (S : Set X) → T ≤ S

theorem le_of_kFactL34A6Normalizer (hKF : KFactL34A6Normalizer) {K S T : Subgroup X} [K.Normal]
    (hK : IsLinThreeFour K) (hrk : Open.pRank 3 (⊤ : Subgroup X) ≤ 2) (hSK : S ≤ K)
    (hSne : S ≠ K) (h360 : 360 ∣ Nat.card S) (hS2 : 2 ≤ Open.pRank 3 S) (hT : IsPGroup 3 T)
    (hTN : T ≤ Subgroup.normalizer (S : Set X)) : T ≤ S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hES, hE, hEc⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank hS2
  set C := Subgroup.centralizer (K : Set X) with hCdef
  haveI : C.Normal := by rw [hCdef]; infer_instance
  have hC := not_dvd_card_centralizer hK (hES.trans hSK) hE (by rw [hEc]; norm_num) hrk
  set φ := QuotientGroup.mk' C with hφ
  have hker : φ.ker = C := QuotientGroup.ker_mk' C
  have hKC : ∀ x ∈ K, x ∈ C → x = 1 := by
    intro x hxK hxC
    have hZ : (⟨x, hxK⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro k
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxC k k.2)
    rw [center_eq_bot_of_isLinThreeFour hK, Subgroup.mem_bot] at hZ
    exact congrArg Subtype.val hZ
  have hinj : ∀ {L : Subgroup X}, L ≤ K → Function.Injective (φ.comp L.subtype) := by
    intro L hLK
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker] at hx
    exact (Subgroup.mem_bot).2 (Subtype.ext (hKC _ (hLK x.2) hx))
  have hrange : ∀ L : Subgroup X, (φ.comp L.subtype).range = L.map φ := fun L => by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcard : ∀ {L : Subgroup X}, L ≤ K → Nat.card (L.map φ) = Nat.card L := fun hLK => by
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective (hinj hLK)).toEquiv]
  have hK' : IsLinThreeFour (K.map φ) := by
    obtain ⟨d, hd, ⟨f⟩⟩ := hK
    exact ⟨d, hd, ⟨((MonoidHom.ofInjective (hinj le_rfl)).trans
      (MulEquiv.subgroupCongr (hrange K))).symm.trans f⟩⟩
  haveI : (K.map φ).Normal := Subgroup.Normal.map ‹_› φ (QuotientGroup.mk'_surjective C)
  have hcen : Subgroup.centralizer ((K.map φ : Subgroup (X ⧸ C)) : Set (X ⧸ C)) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective C y
    rw [Subgroup.mem_bot, ← MonoidHom.mem_ker, hker]
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : φ k ∈ K.map φ := ⟨k, hk, rfl⟩
    have h1 : φ k * φ x = φ x * φ k := Subgroup.mem_centralizer_iff.1 hy _ hk'
    have hcomm : k * x * k⁻¹ * x⁻¹ ∈ C := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, h1]
      group
    have hcK : k * x * k⁻¹ * x⁻¹ ∈ K := by
      have : x * k⁻¹ * x⁻¹ ∈ K := ‹K.Normal›.conj_mem _ (K.inv_mem hk) x
      have h2 := K.mul_mem hk this
      simpa [mul_assoc] using h2
    have h3 := hKC _ hcK hcomm
    have : k * x = x * k := by
      have h4 : k * x * k⁻¹ * x⁻¹ * (x * k) = x * k := by rw [h3, one_mul]
      simpa [mul_assoc] using h4
    exact this
  have hS'K : S.map φ ≤ K.map φ := Subgroup.map_mono hSK
  have hS'ne : S.map φ ≠ K.map φ := by
    intro heq
    apply hSne
    refine Subgroup.eq_of_le_of_card_ge hSK ?_
    rw [← hcard hSK, ← hcard le_rfl, heq]
  have h360' : 360 ∣ Nat.card (S.map φ) := by rw [hcard hSK]; exact h360
  have hT' : IsPGroup 3 (T.map φ) := hT.map φ
  have hTN' : T.map φ ≤ Subgroup.normalizer ((S.map φ : Subgroup (X ⧸ C)) : Set (X ⧸ C)) :=
    (Subgroup.map_mono hTN).trans (Subgroup.le_normalizer_map φ)
  have hle := hKF (X ⧸ C) (K.map φ) (S.map φ) (T.map φ) inferInstance hK' hcen hS'K hS'ne h360'
    hT' hTN'
  have hTSC : T ≤ S ⊔ C := by
    rw [← hker, ← Subgroup.comap_map_eq]
    exact Subgroup.map_le_iff_le_comap.mp hle
  exact le_of_le_sup_of_not_dvd hT hTN hC hTSC

end Generic

section Image

variable {G : Type} [Group G] [Finite G]

theorem image_facts_of_isAltTwoP {H N W : Subgroup G} (hWH : W ≤ H) (hWN : W ≤ N)
    {K₁ : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    {K₂ : Subgroup (N ⧸ primeComplementCore (G := N) 3)}
    (h₁ : (W.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) = K₁)
    (h₂ : (W.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) 3)) ≤ K₂)
    (hK₁ : IsAltTwoP 3 K₁) (hK₂ : IsLinThreeFour K₂) :
    360 ∣ Nat.card ((W.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) 3))) ∧
    (W.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) 3)) ≠ K₂ ∧
    2 ≤ Open.pRank 3 ((W.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) 3))) ∧
    ∀ T : Subgroup G, T ≤ W → IsPGroup 3 T → Nat.card T ∣ 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set S := (W.subgroupOf N).map (QuotientGroup.mk' (primeComplementCore (G := N) 3)) with hSdef
  set φ₁ : W →* H ⧸ primeComplementCore (G := H) 3 :=
    (QuotientGroup.mk' (primeComplementCore (G := H) 3)).comp (Subgroup.inclusion hWH)
  set φ₂ : W →* N ⧸ primeComplementCore (G := N) 3 :=
    (QuotientGroup.mk' (primeComplementCore (G := N) 3)).comp (Subgroup.inclusion hWN)
  have hr₁ : φ₁.range = K₁ := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range, h₁]
  have hr₂ : φ₂.range = S := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hker₁ : Nat.Coprime 3 (Nat.card φ₁.ker) := by
    have hle : φ₁.ker.map (Subgroup.inclusion hWH) ≤ primeComplementCore (G := H) 3 := by
      rintro _ ⟨x, hx, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mp hx
    have hc : Nat.card (φ₁.ker.map (Subgroup.inclusion hWH)) = Nat.card φ₁.ker :=
      Subgroup.card_map_of_injective (Subgroup.inclusion_injective hWH)
    rw [← hc]
    exact (primeComplementCore_coprime 3).coprime_dvd_right (Subgroup.card_dvd_of_le hle)
  have hker₂ : Nat.Coprime 3 (Nat.card φ₂.ker) := by
    have hle : φ₂.ker.map (Subgroup.inclusion hWN) ≤ primeComplementCore (G := N) 3 := by
      rintro _ ⟨x, hx, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mp hx
    have hc : Nat.card (φ₂.ker.map (Subgroup.inclusion hWN)) = Nat.card φ₂.ker :=
      Subgroup.card_map_of_injective (Subgroup.inclusion_injective hWN)
    rw [← hc]
    exact (primeComplementCore_coprime 3).coprime_dvd_right (Subgroup.card_dvd_of_le hle)
  obtain ⟨e⟩ := hK₁
  haveI : IsSimpleGroup (alternatingGroup (Fin (2 * 3))) :=
    alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup K₁ := e.isSimpleGroup
  set φ₁' : W →* K₁ := φ₁.codRestrict K₁ fun w => hr₁ ▸ MonoidHom.mem_range.mpr ⟨w, rfl⟩
  have hsurj : Function.Surjective φ₁' := by
    rintro ⟨y, hy⟩
    rw [← hr₁] at hy
    obtain ⟨w, rfl⟩ := hy
    exact ⟨w, rfl⟩
  have hker' : φ₁'.ker = φ₁.ker := MonoidHom.ker_codRestrict _ _ _
  have hle : φ₂.ker ≤ φ₁.ker := by
    have hn : (φ₂.ker.map φ₁').Normal := (MonoidHom.normal_ker φ₂).map φ₁' hsurj
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (φ₂.ker.map φ₁') with h | h
    · rw [← hker']
      exact (Subgroup.map_eq_bot_iff _).mp h
    · exfalso
      have hd : Nat.card (φ₂.ker.map φ₁') ∣ Nat.card φ₂.ker := Subgroup.card_map_dvd _ _
      rw [h, Subgroup.card_top, card_of_isAltTwoP_three ⟨e⟩] at hd
      have := Nat.Coprime.eq_one_of_dvd hker₂ ((by norm_num : 3 ∣ 360).trans hd)
      norm_num at this
  have hcard₁ : Nat.card φ₁.range = 360 := by rw [hr₁]; exact card_of_isAltTwoP_three ⟨e⟩
  have hk₁ := Subgroup.card_ker_mul_card_range φ₁
  have hk₂ := Subgroup.card_ker_mul_card_range φ₂
  rw [hcard₁] at hk₁
  rw [hr₂] at hk₂
  obtain ⟨r, hr⟩ := Subgroup.card_dvd_of_le hle
  have hpos : 0 < Nat.card φ₂.ker := Nat.card_pos
  have hS : Nat.card S = 360 * r := by
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [hk₂, ← hk₁, hr]
    ring
  refine ⟨⟨r, hS⟩, ?_, ?_, ?_⟩
  ·
    intro hSK
    haveI := isSimpleGroup_of_isLinThreeFour' hK₂
    have hr₂' : φ₂.range = K₂ := hr₂.trans hSK
    set φ₂' : W →* K₂ := φ₂.codRestrict K₂ fun w => hr₂' ▸ MonoidHom.mem_range.mpr ⟨w, rfl⟩
    have hsurj₂ : Function.Surjective φ₂' := by
      rintro ⟨y, hy⟩
      rw [← hr₂'] at hy
      obtain ⟨w, rfl⟩ := hy
      exact ⟨w, rfl⟩
    have hker₂' : φ₂'.ker = φ₂.ker := MonoidHom.ker_codRestrict _ _ _
    have hn : (φ₁.ker.map φ₂').Normal := (MonoidHom.normal_ker φ₁).map φ₂' hsurj₂
    have hK₂c := card_of_isLinThreeFour hK₂
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (φ₁.ker.map φ₂') with h | h
    · have hle' : φ₁.ker ≤ φ₂.ker := by rw [← hker₂']; exact (Subgroup.map_eq_bot_iff _).mp h
      have hc : Nat.card φ₁.ker = Nat.card φ₂.ker :=
        le_antisymm (Subgroup.card_le_of_le hle') (Subgroup.card_le_of_le hle)
      have : Nat.card S = 360 := by
        refine Nat.eq_of_mul_eq_mul_left hpos ?_
        rw [hk₂, ← hc, hk₁]
      rw [hSK, hK₂c] at this
      norm_num at this
    · have hd : Nat.card (φ₁.ker.map φ₂') ∣ Nat.card φ₁.ker := Subgroup.card_map_dvd _ _
      rw [h, Subgroup.card_top, hK₂c] at hd
      have := Nat.Coprime.eq_one_of_dvd hker₁ ((by norm_num : 3 ∣ 20160).trans hd)
      norm_num at this
  ·
    have hW₂ : CFSG.pRank 3 (W ⧸ φ₂.ker) = CFSG.pRank 3 W :=
      CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_three _
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hker₂)
    have hW₁ : CFSG.pRank 3 (W ⧸ φ₁.ker) = CFSG.pRank 3 W :=
      CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_three _
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hker₁)
    have e₁ : W ⧸ φ₁.ker ≃* K₁ :=
      (QuotientGroup.quotientKerEquivRange φ₁).trans (MulEquiv.subgroupCongr hr₁)
    have e₂ : W ⧸ φ₂.ker ≃* S :=
      (QuotientGroup.quotientKerEquivRange φ₂).trans (MulEquiv.subgroupCongr hr₂)
    have h2 := two_le_pRank_of_isAltTwoP ⟨e⟩
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank, ← CFSG.pRank_congr_of_mulEquiv e₁, hW₁] at h2
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank, ← CFSG.pRank_congr_of_mulEquiv e₂, hW₂]
    exact h2
  ·
    intro T hTW hT
    set T' := T.subgroupOf W
    have hT'c : Nat.card T' = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTW).toEquiv
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT
    have hinf : T' ⊓ φ₁.ker = ⊥ := by
      have h1 : Nat.card ↥(T' ⊓ φ₁.ker) ∣ 3 ^ n := hn ▸ hT'c ▸ Subgroup.card_dvd_of_le inf_le_left
      have h2 : Nat.card ↥(T' ⊓ φ₁.ker) ∣ Nat.card φ₁.ker := Subgroup.card_dvd_of_le inf_le_right
      have h3 : Nat.Coprime (3 ^ n) (Nat.card φ₁.ker) := Nat.Coprime.pow_left n hker₁
      exact Subgroup.card_eq_one.mp (Nat.Coprime.eq_one_of_dvd (h3.coprime_dvd_left h1) h2)
    have hinj : Function.Injective (φ₁.comp T'.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker] at hx
      have : (x : W) ∈ T' ⊓ φ₁.ker := ⟨x.2, hx⟩
      rw [hinf, Subgroup.mem_bot] at this
      exact (Subgroup.mem_bot).2 (Subtype.ext this)
    have hrng : (φ₁.comp T'.subtype).range ≤ φ₁.range := by
      rintro _ ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    have hd : Nat.card T ∣ 360 := by
      rw [← hT'c, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, ← hcard₁]
      exact Subgroup.card_dvd_of_le hrng
    rw [hn] at hd ⊢
    have hc : Nat.Coprime (3 ^ n) 40 := Nat.Coprime.pow_left n (by norm_num)
    exact hc.dvd_of_dvd_mul_right (by simpa using hd)

end Image

section Main

open CFSG.PreuniquenessRankFour.Helpers CFSG.AGLEmbeddingD2

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_hyp111Pre_iff {p : ℕ} {H : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {x : G} :
    x ∈ hyp111Pre p H K ↔
      ∃ hx : x ∈ H, QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨x, hx⟩ ∈ K := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hk⟩
    exact ⟨⟨x, hx⟩, hk, rfl⟩

omit [Finite G] in
theorem conj_mem_hyp111Pre {p : ℕ} {H : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} [K.Normal] {b x : G} (hb : b ∈ H)
    (hx : x ∈ hyp111Pre p H K) : b * x * b⁻¹ ∈ hyp111Pre p H K := by
  obtain ⟨hxH, hk⟩ := mem_hyp111Pre_iff.mp hx
  refine mem_hyp111Pre_iff.mpr ⟨H.mul_mem (H.mul_mem hb hxH) (H.inv_mem hb), ?_⟩
  have := ‹K.Normal›.conj_mem _ hk (QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨b, hb⟩)
  convert this using 1
  simp only [← map_mul, ← map_inv]
  rfl

omit [Finite G] in
theorem le_hyp111Pre_of_map_le {p : ℕ} {H W : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hWH : W ≤ H)
    (h : (W.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤ K) :
    W ≤ hyp111Pre p H K := fun x hx =>
  mem_hyp111Pre_iff.mpr ⟨hWH hx, h ⟨⟨x, hWH hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩⟩

omit [Finite G] in
theorem map_hyp111Pre_le {p : ℕ} {H W : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hW : W ≤ hyp111Pre p H K) :
    (W.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤ K := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨_, hk⟩ := mem_hyp111Pre_iff.mp (hW (Subgroup.mem_subgroupOf.mp hy))
  exact hk

omit [Finite G] in
theorem hyp111Pre_le {p : ℕ} {H : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} : hyp111Pre p H K ≤ H :=
  fun _ hx => (mem_hyp111Pre_iff.mp hx).1

omit [Finite G] in
theorem subgroupOf_le_normalizer {N B W : Subgroup G}
    (h : B ≤ Subgroup.normalizer (W : Set G)) :
    B.subgroupOf N ≤ Subgroup.normalizer ((W.subgroupOf N : Subgroup N) : Set N) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  simpa using (Subgroup.mem_normalizer_iff.mp (h (Subgroup.mem_subgroupOf.mp hb)) (x : G))

theorem three_le_pRank_of_sylow {p : ℕ} [hp : Fact p.Prime] {H₀ Q₀ : Subgroup G}
    (S : Sylow p H₀) (hS : (S : Subgroup H₀).map H₀.subtype = Q₀)
    (h : 3 ≤ Open.pRank p H₀) : 3 ≤ Open.pRank p Q₀ := by
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h
  obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank h
  obtain ⟨S', hS'⟩ := (IsPGroup.of_card (n := 3) hEc).exists_le_sylow
  have h1 : 3 ≤ Open.pRank p (S' : Subgroup H₀) :=
    CFSG.SectionRank.le_pRank hp.out.one_lt hS' hE hEc
  rw [sylow_pRank_eq p hp.out S' S] at h1
  rw [← hS]
  exact h1.trans (CFSG.SectionRank.pRank_le_map hp.out.one_lt H₀.subtype H₀.subtype_injective _)

theorem pRank_le_two_of_l34 (hS : Setting G) {P : Sylow 3 G} {M H R : Subgroup G}
    (he : D1Escape 3 P M H R) (hcex : ¬ ElevenTwentyConcl M) {B H₀ : Subgroup G}
    (hB : IsAGLQ 3 M B) (hH₀ : GLBIsMaxTwoLocal H₀) (hH₀M : ¬ H₀ ≤ M) (hBH₀ : B ≤ H₀)
    (hK₀ : ∃ L : Subgroup (H₀ ⧸ primeComplementCore (G := H₀) 3), IsComponentOf L ⊤ ∧
      ¬ L ≤ d1X0 3 M H₀) (hL34 : IsLinThreeFour (d1KBar 3 M H₀)) :
    Open.pRank 3 H₀ ≤ 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra h3
  push Not at h3
  obtain ⟨Q₀, -, hQ₀H, hQ₀, S, hS₀⟩ := exists_sylowBase he hB hBH₀
  have hQ3 := three_le_pRank_of_sylow S hS₀ (by omega)
  have hHM3 : 3 ≤ Open.pRank 3 (H₀ ⊓ M) :=
    hQ3.trans (CFSG.SectionRank.pRank_mono (by norm_num) (le_inf hQ₀H hQ₀.1))
  refine hcex ⟨H₀, hH₀, fun h => hH₀M h.le, le_antisymm ?_ hHM3, _,
    isComponentOf_d1KBar_of_isLinThreeFour hK₀ hL34, hL34⟩
  exact (CFSG.SectionRank.pRank_mono (by norm_num) inf_le_left).trans
    (pRank_le_three_of_twoLocal hS hH₀.1)

theorem base_of_l34Step (hKF : KFactL34A6Normalizer) (hS : Setting G)
    (h9 : AGL81NineCompetitorQ G) (h917 : AGL81NineSeventeenOne G)
    {P : Sylow 3 G} {M H R : Subgroup G} (he : D1Escape 3 P M H R)
    (hA6 : IsAltTwoP 3 (d1KBar 3 M H)) (hcex : ¬ ElevenTwentyConcl M) {B H₀ : Subgroup G}
    (hB : IsAGLQ 3 M B) (hBH : B ≤ H) (hH₀ : GLBIsMaxTwoLocal H₀) (hH₀M : ¬ H₀ ≤ M)
    (hBH₀ : B ≤ H₀) (hcov : AGLCovers 3 H H₀ (d1KBar 3 M H))
    (hL34 : IsLinThreeFour (d1KBar 3 M H₀)) :
    B ≤ hyp111Pre 3 H (d1KBar 3 M H) ∧ B ≤ hyp111Pre 3 H₀ (d1KBar 3 M H₀) ∧
      IsElemAbelian 3 B ∧ Nat.card B = 9 ∧ rankThreeGamma 1 3 B ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hg := aglGlobal_of_setting hS
  have hμ := muAt_of_escape he
  have hK := exists_component_of_d1KBar_ne_bot (d1KBar_ne_bot_of_isAltTwoP hA6)
  have hK₀ := exists_component_of_d1KBar_ne_bot (M := M) (N := H₀) (p := 3) fun hb => by
    have h := card_of_isLinThreeFour hL34
    rw [hb, Subgroup.card_bot] at h
    norm_num at h
  haveI : (d1KBar 3 M H).Normal :=
    (h9 hg 3 P M H hμ he.maxTwoLocal_H he.not_le hK B H hB hBH he.maxTwoLocal_H he.not_le hBH
      (aglCovers_self H _)).1.nineThree.normal
  haveI : (d1KBar 3 M H₀).Normal :=
    (h9 hg 3 P M H₀ hμ hH₀ hH₀M hK₀ B H₀ hB hBH₀ hH₀ hH₀M hBH₀
      (aglCovers_self H₀ _)).1.nineThree.normal
  obtain ⟨W, hW, hWK, hWN⟩ := h917 hg 3 P M H hμ he.maxTwoLocal_H he.not_le hK
    (two_le_pRank_of_isAltTwoP hA6) B H₀ hB hBH hH₀ hH₀M hBH₀ hcov
  have hWH : W ≤ H := hW.trans inf_le_left
  have hWH₀ : W ≤ H₀ := hW.trans inf_le_right
  have hWKh : W ≤ hyp111Pre 3 H (d1KBar 3 M H) := le_hyp111Pre_of_map_le hWH hWK.le
  have hWKh₀ : W ≤ hyp111Pre 3 H₀ (d1KBar 3 M H₀) := le_hyp111Pre_of_map_le hWH₀ hWN
  set Ws : Subgroup G := ⨆ b : B, W.map (MulAut.conj (b : G)).toMonoidHom with hWs
  have hconj : ∀ {X : Subgroup G}, (∀ b ∈ B, ∀ x ∈ X, b * x * b⁻¹ ∈ X) → W ≤ X → Ws ≤ X := by
    intro X hX hWX
    refine iSup_le fun b => ?_
    rintro _ ⟨w, hw, rfl⟩
    exact hX b b.2 w (hWX hw)
  have hWsKh : Ws ≤ hyp111Pre 3 H (d1KBar 3 M H) :=
    hconj (fun b hb x hx => conj_mem_hyp111Pre (hBH hb) hx) hWKh
  have hWsKh₀ : Ws ≤ hyp111Pre 3 H₀ (d1KBar 3 M H₀) :=
    hconj (fun b hb x hx => conj_mem_hyp111Pre (hBH₀ hb) hx) hWKh₀
  have hWsH : Ws ≤ H := hWsKh.trans hyp111Pre_le
  have hWsH₀ : Ws ≤ H₀ := hWsKh₀.trans hyp111Pre_le
  have hWWs : W ≤ Ws := by
    intro w hw
    refine Subgroup.mem_iSup_of_mem (⟨1, B.one_mem⟩ : B) ⟨w, hw, ?_⟩
    simp
  have key : ∀ b ∈ B, ∀ x ∈ Ws, b * x * b⁻¹ ∈ Ws := by
    intro b hb x hx
    refine Subgroup.iSup_induction (fun c : B => W.map (MulAut.conj (c : G)).toMonoidHom)
      (C := fun x => b * x * b⁻¹ ∈ Ws) hx ?_ ?_ ?_
    · rintro c _ ⟨w, hw, rfl⟩
      refine Subgroup.mem_iSup_of_mem (⟨b * c, B.mul_mem hb c.2⟩ : B) ⟨w, hw, ?_⟩
      simp [mul_assoc]
    · simp
    · intro x y hx hy
      have := Ws.mul_mem hx hy
      simpa [mul_assoc] using this
  have hBN : B ≤ Subgroup.normalizer (Ws : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key b hb x, fun hx => ?_⟩
    have := key b⁻¹ (B.inv_mem hb) _ hx
    simpa [mul_assoc] using this
  have h₁ : (Ws.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) =
      d1KBar 3 M H := by
    refine le_antisymm (map_hyp111Pre_le hWsKh) ?_
    rw [← hWK]
    exact Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
      (hWWs (Subgroup.mem_subgroupOf.mp hx))
  have h₂ : (Ws.subgroupOf H₀).map (QuotientGroup.mk' (primeComplementCore (G := H₀) 3)) ≤
      d1KBar 3 M H₀ := map_hyp111Pre_le hWsKh₀
  obtain ⟨h360, hne, hS2, hT9⟩ := image_facts_of_isAltTwoP hWsH hWsH₀ h₁ h₂ hA6 hL34
  have hcop : ¬ 3 ∣ Nat.card (primeComplementCore (G := H₀) 3) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (primeComplementCore_coprime 3)
  have hrkbar : Open.pRank 3 (⊤ : Subgroup (H₀ ⧸ primeComplementCore (G := H₀) 3)) ≤ 2 := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top,
      CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_three _ hcop,
      CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact pRank_le_two_of_l34 hS he hcex hB hH₀ hH₀M hBH₀ hK₀ hL34
  have hBp : IsPGroup 3 (B.subgroupOf H₀) := hB.2.1.comap_subtype
  have hBN₀ := subgroupOf_le_normalizer (N := H₀) hBN
  have hTS := le_of_kFactL34A6Normalizer hKF hL34 hrkbar h₂ hne h360 hS2
    (hBp.map (QuotientGroup.mk' (primeComplementCore (G := H₀) 3)))
    ((Subgroup.map_mono hBN₀).trans (Subgroup.le_normalizer_map _))
  have hBsup : B.subgroupOf H₀ ≤ Ws.subgroupOf H₀ ⊔ primeComplementCore (G := H₀) 3 := by
    rw [← QuotientGroup.ker_mk' (primeComplementCore (G := H₀) 3), ← Subgroup.comap_map_eq]
    exact Subgroup.map_le_iff_le_comap.mp hTS
  have hBWs' := le_of_le_sup_of_not_dvd hBp hBN₀ hcop hBsup
  have hBWs : B ≤ Ws := fun x hx =>
    hBWs' (show (⟨x, hBH₀ hx⟩ : H₀) ∈ B.subgroupOf H₀ from hx)
  have hB9 := hT9 B hBWs hB.2.1
  refine ⟨hBWs.trans hWsKh, hBWs.trans hWsKh₀, ?_⟩
  rcases hB.2.2 with h3 | ⟨E, hEB, hE, hEc, hΓ⟩
  · exfalso
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at h3
    obtain ⟨E, hEB, -, hEc⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank h3
    have := (Subgroup.card_dvd_of_le hEB).trans hB9
    rw [hEc] at this
    norm_num at this
  · have hEq : E = B := Subgroup.eq_of_le_of_card_ge hEB (by
      rw [hEc]; exact Nat.le_of_dvd (by norm_num) hB9)
    subst hEq
    exact ⟨hE, hEc, hΓ⟩

theorem exists_base_of_ascentStep (hKF : KFactL34A6Normalizer) (hS : Setting G)
    (h9 : AGL81NineCompetitorQ G) (h917 : AGL81NineSeventeenOne G)
    {P : Sylow 3 G} {M H R : Subgroup G} (he : D1Escape 3 P M H R)
    (hA6 : IsAltTwoP 3 (d1KBar 3 M H)) (hcex : ¬ ElevenTwentyConcl M) {H₀ : Subgroup G}
    (hst : AGLAscentStep 3 M H H₀) (hL34 : IsLinThreeFour (d1KBar 3 M H₀)) :
    ∃ A : Subgroup G, IsAGLQ 3 M A ∧ A ≤ H ⊓ H₀ ∧ A ≤ hyp111Pre 3 H (d1KBar 3 M H) ∧
      A ≤ hyp111Pre 3 H₀ (d1KBar 3 M H₀) ∧ IsElemAbelian 3 A ∧ Nat.card A = 9 ∧
      rankThreeGamma 1 3 A ≤ M := by
  obtain ⟨B, hB, hBH, hH₀, hH₀M, hBH₀, hcov, -, -⟩ := hst
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    base_of_l34Step hKF hS h9 h917 he hA6 hcex hB hBH hH₀ hH₀M hBH₀ hcov hL34
  exact ⟨B, hB, le_inf hBH hBH₀, h1, h2, h3, h4, h5⟩

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
