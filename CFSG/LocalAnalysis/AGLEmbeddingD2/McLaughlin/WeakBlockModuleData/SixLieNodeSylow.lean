module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviBorel
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg

variable {K Y : Type*} [Group K] [Group Y] [Finite K] [Finite Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem card_dvd_of_le_normalizer_borel (h : BorelQuotient D n H π M)
    (hr : Nonempty (Fin D.rank)) (T : Sylow 2 Y) (V : Subgroup Y)
    (hV : V ≤ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) (hV3 : IsPGroup 3 V) :
    Nat.card V ∣ Nat.card (⨆ k, H k : Subgroup K) := by
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
  have hmeet : ∀ x ∈ V, x ∈ (T : Subgroup Y) → x = 1 := by
    intro x hxV hxT
    obtain ⟨k, hk⟩ := hV3 ⟨x, hxV⟩
    obtain ⟨m, hm⟩ := (T.isPGroup' (G := Y)) ⟨x, hxT⟩
    have h3 : orderOf x ∣ 3 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    have h2 : orderOf x ∣ 2 ^ m :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hm)
    have := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow k m (by norm_num : Nat.Coprime 3 2)) h3 h2
    exact orderOf_eq_one_iff.mp this
  let φ : ↥V →* N ⧸ Tn := (QuotientGroup.mk' Tn).comp (Subgroup.inclusion hV)
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : (QuotientGroup.mk' Tn) (Subgroup.inclusion hV x) = 1 := hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hTn, Subgroup.mem_subgroupOf] at hx'
    exact Subtype.ext (hmeet x.1 x.2 hx')
  exact (Subgroup.card_dvd_of_injective φ hφ).trans (Subgroup.card_dvd_of_surjective hsurj)

theorem comm_mem_of_le_normalizer_borel (h : BorelQuotient D n H π M)
    (hr : Nonempty (Fin D.rank)) (T : Sylow 2 Y) {y z : Y}
    (hy : y ∈ Subgroup.normalizer ((T : Subgroup Y) : Set Y))
    (hz : z ∈ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) :
    z⁻¹ * y⁻¹ * z * y ∈ (T : Subgroup Y) := by
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
  have hc := hcomm (QuotientGroup.mk ⟨y, hy⟩) (QuotientGroup.mk ⟨z, hz⟩)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hTn,
    Subgroup.mem_subgroupOf] at hc
  simpa [mul_assoc] using hc

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
