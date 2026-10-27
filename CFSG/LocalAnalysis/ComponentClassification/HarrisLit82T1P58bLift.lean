module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bProps
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C4Props

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank

namespace P58b

theorem isSLTwoOver_of_equiv {q : ℕ} {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : IsSLTwoOver q A) : IsSLTwoOver q B := by
  obtain ⟨F, i₁, i₂, hF, ⟨eF⟩⟩ := h
  exact ⟨F, i₁, i₂, hF, ⟨e.symm.trans eF⟩⟩

variable {K : Type} [Group K] [Finite K]

theorem orderOf_mk_eq_two {z : K} (hz : orderOf z = 2) :
    orderOf (QuotientGroup.mk' (pPrimeCore 2 K) z) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
    rw [← map_pow, hz2, map_one]
  · intro h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 : orderOf z ∣ Nat.card ↥(pPrimeCore 2 K) := by
      rw [← Subgroup.orderOf_mk z h1]
      exact orderOf_dvd_natCard _
    rw [hz] at h2
    exact (Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card) h2

theorem nonempty_coreQuot_map (L : Subgroup K) :
    Nonempty (↥L ⧸ pPrimeCore 2 ↥L ≃*
      ↥(L.map (QuotientGroup.mk' (pPrimeCore 2 K))) ⧸
        pPrimeCore 2 ↥(L.map (QuotientGroup.mk' (pPrimeCore 2 K)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : Function.Surjective ((QuotientGroup.mk' (pPrimeCore 2 K)).subgroupMap L) :=
    MonoidHom.subgroupMap_surjective _ L
  have hodd : ¬ 2 ∣ Nat.card ((QuotientGroup.mk' (pPrimeCore 2 K)).subgroupMap L).ker := by
    intro h2
    have hle : ((QuotientGroup.mk' (pPrimeCore 2 K)).subgroupMap L).ker.map L.subtype ≤
        pPrimeCore 2 K := by
      rintro _ ⟨l, hl, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val (MonoidHom.mem_ker.mp hl))
    have h3 : Nat.card ((QuotientGroup.mk' (pPrimeCore 2 K)).subgroupMap L).ker ∣
        Nat.card ↥(pPrimeCore 2 K) := by
      rw [← Subgroup.card_map_of_injective L.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    exact (Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card) (h2.trans h3)
  obtain ⟨hcomap, -⟩ := prime_complement_kernel_core_preimage _ hf hodd
  have hg : Function.Surjective ((QuotientGroup.mk' (pPrimeCore 2
      ↥(L.map (QuotientGroup.mk' (pPrimeCore 2 K))))).comp
        ((QuotientGroup.mk' (pPrimeCore 2 K)).subgroupMap L)) :=
    (QuotientGroup.mk'_surjective _).comp hf
  have hgker : ((QuotientGroup.mk' (pPrimeCore 2
      ↥(L.map (QuotientGroup.mk' (pPrimeCore 2 K))))).comp
        ((QuotientGroup.mk' (pPrimeCore 2 K)).subgroupMap L)).ker = pPrimeCore 2 ↥L := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hcomap]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hgker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hg)⟩

theorem isTwoComponentIn_map_mk {z : K} (hz : z * z = 1) {L : Subgroup K}
    (hL : IsTwoComponentIn L (centralizer {z})) :
    IsTwoComponentIn (L.map (QuotientGroup.mk' (pPrimeCore 2 K)))
      (centralizer {QuotientGroup.mk' (pPrimeCore 2 K) z}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hLC, hsub, hperf, hq⟩ := hL
  have hOodd : Odd (Nat.card (pPrimeCore 2 K)) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  rw [← UnbalancedLayer.map_centralizer_eq hOodd hz]
  have heq : (L.subgroupOf (centralizer {z})).map
      ((QuotientGroup.mk' (pPrimeCore 2 K)).subgroupMap (centralizer {z})) =
      (L.map (QuotientGroup.mk' (pPrimeCore 2 K))).subgroupOf
        ((centralizer {z}).map (QuotientGroup.mk' (pPrimeCore 2 K))) := by
    ext y
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact mem_subgroupOf.mpr ⟨c, mem_subgroupOf.mp hc, rfl⟩
    · intro hy
      obtain ⟨l, hl, hly⟩ := mem_map.mp (mem_subgroupOf.mp hy)
      exact ⟨⟨l, hLC hl⟩, mem_subgroupOf.mpr hl, Subtype.ext hly⟩
  obtain ⟨e⟩ := nonempty_coreQuot_map L
  exact ⟨map_mono hLC, heq ▸ hsub.map (MonoidHom.subgroupMap_surjective _ _),
    Group.IsPerfect.map _, LocalCores.isQuasisimple_of_mulEquiv e hq⟩

end P58b

open P58b in
theorem harris82Lemma58b_of_cover (h : Harris82Lemma58bCover) : Harris82Lemma58b := by
  intro K _ _ hK p hp hp2 hChev z₁ z₂ hz₁ hz₁Z hz₂ hz₂Z L₁ L₂ hL₁ hL₂ hz₁L₁ hz₂L₂ k hk hSL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX : IsQuasisimple (K ⧸ pPrimeCore 2 K) := hK.2
  have hChevX : IsSimpleChevalleyOver p
      ((K ⧸ pPrimeCore 2 K) ⧸ center (K ⧸ pPrimeCore 2 K)) := by
    obtain ⟨τ, n, f, hm⟩ := hChev
    exact ⟨τ, n, f, LieType.CurtisTits.lieModel_of_mulEquiv
      (Sol78.coreQuotientCenterEquiv K).symm hm⟩
  have hz2 : z₂ * z₂ = 1 := by rw [← pow_two, ← hz₂, pow_orderOf_eq_one]
  obtain ⟨e₁⟩ := nonempty_coreQuot_map L₁
  obtain ⟨e₂⟩ := nonempty_coreQuot_map L₂
  have hcZ : QuotientGroup.mk' (pPrimeCore 2 K) z₁ ∈ center (K ⧸ pPrimeCore 2 K) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ g
    rw [← map_mul, ← map_mul, mem_center_iff.mp hz₁Z y]
  have hcfg : Lemma58bConfig (K ⧸ pPrimeCore 2 K) p k (QuotientGroup.mk' _ z₁)
      (QuotientGroup.mk' _ z₂) (L₁.map (QuotientGroup.mk' (pPrimeCore 2 K))) :=
    ⟨orderOf_mk_eq_two hz₁, hcZ, orderOf_mk_eq_two hz₂, hz₂Z, isTwoComponentIn_map_mk hz2 hL₁,
      mem_map_of_mem _ hz₁L₁, hk, isSLTwoOver_of_equiv e₁ hSL⟩
  obtain ⟨hA, hB⟩ := h _ hX (pPrimeCore_quotient_pPrimeCore_eq_bot 2) p hp hp2 hChevX k _ _ _ _
    hcfg (isTwoComponentIn_map_mk hz2 hL₂) (mem_map_of_mem _ hz₂L₂)
  refine ⟨fun hτ => hA ?_, fun hSL₂ => hB (isSLTwoOver_of_equiv e₂ hSL₂)⟩
  obtain ⟨τ, n, hm⟩ := hτ
  exact ⟨τ, n, LieType.CurtisTits.lieModel_of_mulEquiv (Sol78.fusionZStarQuotOfCore e₂) hm⟩

end CFSG.ComponentClassification.HarrisLit.T1
