module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviBorel
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg

variable {K Y : Type*} [Group K] [Group Y] [Finite K] [Finite Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem isElemAbelian_of_le_normalizer_borel (h : BorelQuotient D n H π M) (hM : M ∣ 3)
    (hr : Nonempty (Fin D.rank))
    (T : Sylow 2 Y) (V : Subgroup Y)
    (hV : V ≤ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) (hV3 : IsPGroup 3 V) :
    IsElemAbelian 3 V := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π', hπ', hker, hT⟩ := h.exists_conj_eq T
  have hQ : BorelQuotient D n H π' M :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  set N : Subgroup Y := Subgroup.normalizer ((T : Subgroup Y) : Set Y) with hN
  have hTN : (T : Subgroup Y) ≤ N := fun t ht => Subgroup.le_normalizer ht
  set T₀ : Subgroup K := ⨆ k, H k with hT₀
  have hT03 : ∀ t ∈ T₀, t ^ 3 = 1 := fun t ht => by
    obtain ⟨k, hk⟩ := hM
    rw [hk, pow_mul, hQ.pow_eq_one_of_mem_iSup ht, one_pow]
  have hT0mem : ∀ t ∈ T₀, π' t ∈ N := fun t ht => by
    rw [hNπ]; exact ⟨t, iSup_le_borel ht, rfl⟩
  have hdec : ∀ v ∈ N, ∃ t ∈ T₀, ∃ s ∈ (T : Subgroup Y), v = π' t * s := by
    intro v hv
    rw [hNπ] at hv
    obtain ⟨b, hb, rfl⟩ := hv
    obtain ⟨i₀⟩ := hr
    obtain ⟨t, ht, u, hu, w, hw, rfl⟩ := exists_eq_mul_mul_of_mem_borel hQ.ct hQ.extras i₀ hb
    refine ⟨t, ht, π' (u * w), ?_, by simp only [map_mul, mul_assoc]⟩
    rw [hT]
    exact ⟨u * w, mul_mem (posUnipotentExcept_le_posUnipotent i₀ hu)
      (rootGroup_le_posUnipotent ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i₀)
        (ht_single_pos i₀) hw), rfl⟩
  set Tn : Subgroup N := (T : Subgroup Y).subgroupOf N with hTn
  haveI hTnn : Tn.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hTN).2 le_rfl
  let ψ : ↥T₀ →* N ⧸ Tn :=
    (QuotientGroup.mk' Tn).comp ((π'.comp T₀.subtype).codRestrict N fun t => hT0mem t.1 t.2)
  have hψ : ∀ t : ↥T₀, ψ t = QuotientGroup.mk ⟨π' t, hT0mem t.1 t.2⟩ := fun t => rfl
  have hsurj : Function.Surjective ψ := by
    intro x
    obtain ⟨⟨v, hv⟩, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨t, ht, s, hs, rfl⟩ := hdec v hv
    refine ⟨⟨t, ht⟩, ?_⟩
    rw [hψ]
    refine (QuotientGroup.eq).2 ?_
    rw [hTn, Subgroup.mem_subgroupOf]
    simpa using hs
  have hcomm : ∀ x y : N ⧸ Tn, x * y = y * x := by
    intro x y
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨b, rfl⟩ := hsurj y
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (commute_of_mem_sup_tori hQ.extras a.2 b.2).eq
  have hexp : ∀ x : N ⧸ Tn, x ^ 3 = 1 := by
    intro x
    obtain ⟨a, rfl⟩ := hsurj x
    rw [← map_pow]
    have : a ^ 3 = 1 := Subtype.ext (hT03 a.1 a.2)
    rw [this, map_one]
  have hmeet : ∀ x ∈ V, x ∈ (T : Subgroup Y) → x = 1 := by
    intro x hxV hxT
    obtain ⟨k, hk⟩ := hV3 ⟨x, hxV⟩
    obtain ⟨m, hm⟩ := (T.isPGroup' (G := Y)) ⟨x, hxT⟩
    have h3 : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    have h2 : orderOf x ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hm)
    have := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow k m (by norm_num : Nat.Coprime 3 2)) h3 h2
    exact orderOf_eq_one_iff.mp this
  have hVN : ∀ v ∈ V, v ∈ N := fun v hv => hV hv
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun v hv => ?_⟩
  · obtain ⟨v, hv⟩ := a
    obtain ⟨w, hw⟩ := b
    have hc := hcomm (QuotientGroup.mk ⟨v, hVN v hv⟩) (QuotientGroup.mk ⟨w, hVN w hw⟩)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hTn,
      Subgroup.mem_subgroupOf] at hc
    have hmem : (v * w)⁻¹ * (w * v) ∈ V :=
      V.mul_mem (V.inv_mem (V.mul_mem hv hw)) (V.mul_mem hw hv)
    have h1 := hmeet _ hmem (by simpa using hc)
    exact Subtype.ext (inv_mul_eq_one.mp h1)
  · have h3 := hexp (QuotientGroup.mk ⟨v, hVN v hv⟩)
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hTn, Subgroup.mem_subgroupOf] at h3
    exact hmeet _ (V.pow_mem hv 3) (by simpa using h3)

theorem eq_bot_of_le_normalizer_borel (h : BorelQuotient D n H π M) (hH : ∀ k, H k = ⊥)
    (hr : Nonempty (Fin D.rank)) (T : Sylow 2 Y) (V : Subgroup Y)
    (hV : V ≤ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) (hV3 : IsPGroup 3 V) :
    V = ⊥ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π', hπ', hker, hT⟩ := h.exists_conj_eq T
  have hQ : BorelQuotient D n H π' M :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  rw [Subgroup.eq_bot_iff_forall]
  intro v hv
  have hvN := hV hv
  rw [hNπ] at hvN
  obtain ⟨b, hb, rfl⟩ := hvN
  obtain ⟨i₀⟩ := hr
  obtain ⟨t, ht, u, hu, w, hw, rfl⟩ := exists_eq_mul_mul_of_mem_borel hQ.ct hQ.extras i₀ hb
  have ht1 : t = 1 := by
    have : t ∈ (⊥ : Subgroup K) := by
      have h0 : (⨆ k, H k) = ⊥ := by simp [hH]
      rwa [h0] at ht
    exact this
  have hs : π' (t * u * w) ∈ (T : Subgroup Y) := by
    rw [hT, ht1, one_mul]
    exact ⟨u * w, mul_mem (posUnipotentExcept_le_posUnipotent i₀ hu)
      (rootGroup_le_posUnipotent ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i₀)
        (ht_single_pos i₀) hw), by simp [map_mul]⟩
  obtain ⟨k, hk⟩ := hV3 ⟨π' (t * u * w), hv⟩
  obtain ⟨m, hm⟩ := (T.isPGroup' (G := Y)) ⟨π' (t * u * w), hs⟩
  have h3 : orderOf (π' (t * u * w)) ∣ 3 ^ k :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h2 : orderOf (π' (t * u * w)) ∣ 2 ^ m :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hm)
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow k m (by norm_num : Nat.Coprime 3 2)) h3 h2)

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
