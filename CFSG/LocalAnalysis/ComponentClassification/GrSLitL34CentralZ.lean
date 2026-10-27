module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Central
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Basic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHypG
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSylow
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Fixed

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
  CFSG.ComponentClassification.GSLit
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped Pointwise

namespace L34Central

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_eq_mul_odd {T : Subgroup G} {b y o : G} (hb : b * b = 1) (hy : y ∈ T)
    (hyb : y * b = b * y) (hbo : b = y * o) (ho : Odd (orderOf o)) : b ∈ T := by
  have hyo : Commute y o := by
    have e : o = y⁻¹ * b := by rw [hbo]; group
    show y * o = o * y
    rw [e, mul_assoc y⁻¹, ← hyb]
    group
  obtain ⟨m, hm⟩ := ho
  have h1 : b ^ orderOf o = y ^ orderOf o := by
    rw [hbo, hyo.mul_pow, pow_orderOf_eq_one, mul_one]
  have h2 : b ^ orderOf o = b := by
    rw [hm, pow_succ, pow_mul, pow_two, hb, one_pow, one_mul]
  rw [← h2, h1]
  exact pow_mem hy _

theorem le_normalizer_inf_zStarIn {S J : Subgroup G} (hSJ : S ≤ normalizer (J : Set G)) :
    S ≤ normalizer ((S ⊓ zStarIn J : Subgroup G) : Set G) := by
  intro s hs
  refine mem_normalizer_of_map_le ?_
  rintro _ ⟨h, hh, rfl⟩
  obtain ⟨hhS, hhZ⟩ := mem_inf.mp hh
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  refine mem_inf.mpr ⟨mul_mem (mul_mem hs hhS) (inv_mem hs), ?_⟩
  have h1 : zStarIn J = J ⊓ coreActionKernel J := GSThmB.map_fusionZStar_eq J
  rw [h1] at hhZ ⊢
  exact mem_inf.mpr ⟨(mem_normalizer_iff.mp (hSJ hs) h).mp (mem_inf.mp hhZ).1,
    UnbalancedLayer.conj_mem_coreActionKernel (hSJ hs) (mem_inf.mp hhZ).2⟩

theorem exists_setting_of_central_step
    (hS : SchreierFor Blueprint.Catalog) (hMax : MaximalTwoComponentInput) {a x b : G}
    {J S : Subgroup G} (hset : L34Sec4Setting G a x J S)
    (hmaxS : ∀ (a' x' : G) (J' S' : Subgroup G), L34Sec4Setting G a' x' J' S' →
      Nat.card S' ≤ Nat.card S)
    (hb : orderOf b = 2) (hbS : b ∈ S) (hbc : ∀ s ∈ S, s * b = b * s)
    (hbK : b ∈ coreActionKernel J) :
    ∃ M : Subgroup G, L34Sec4Setting G b x M S ∧ (b ∈ J → b ∈ M) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hset' : L34Sec4Setting G a x J S := hset
  obtain ⟨hbase, hT, h34, hmaxJ, hSyl, haS, hxS⟩ := hset'
  obtain ⟨hsimple, hnonab, hK, -, -, -, -, htypes⟩ := id hbase
  have : IsSimpleGroup G := hsimple
  obtain ⟨ha, -, -, hJa, hJ, -, -⟩ := gsUnbalancingTriple_iff.mp hT
  obtain ⟨hbN, hJb'⟩ := mem_coreActionKernel.mp hbK
  have hab : a * b = b * a := hbc a haS
  have hxb : x * b = b * x := hbc x hxS
  have hbZ : b ∉ center G := GSLit.not_mem_center_of_orderOf_eq_two hnonab hb
  obtain ⟨M, hW, hUM, hidx, hcorr⟩ := exists_gsWeakCorr_of_target hS hK hT hb hbZ hab hxb hbN hJb'
  obtain ⟨-, -, -, -, -, hMb, hM, -, -, -⟩ := id hW
  obtain ⟨hsF, hnF, hoF⟩ := GrS5.fstar_facts hbase
  have hcorr' : GSCorr a J b M →
      GSWeakMaximalComponent M ∧ IsL34Type (M ⧸ Open.fusionZStar M) := by
    intro hC
    have hR : GSWeakReach J M := GSWeakReach.of_gsReach (GSReach.of_gsCorr hC)
    obtain ⟨e⟩ := hmaxJ.2 M hR
    exact ⟨hmaxJ.of_weakReach hR,
      LieType.CurtisTits.lieModel_of_mulEquiv e h34⟩
  have hMa : conjugate M a = M := by
    by_contra hne
    have hne' : M ≠ conjugate M a := fun h => hne h.symm
    obtain ⟨hmaxM, htypeM⟩ := hcorr' (hcorr (Or.inl hne'))
    have h3 := GrS5.three_le_pRank_of_l34 htypeM
    obtain ⟨-, h2⟩ := hMax G hsF hnF hoF hK M hmaxM (by omega)
      (Sol78.not_psp4_of_l34 htypeM) (Or.inl ⟨htypeM, hbase⟩) b hb
      hMb
    apply h2 h3 a
    obtain ⟨hMab, hMap⟩ := UGSChain.conjugate_isPComponent_centralizer hab hMb hM
    exact GrS5.commutator_le_inf_oddIn hMb hMab hM hMap hne'
  obtain ⟨hJM, hJMp, ⟨φ⟩⟩ := gsFixedLayer_isPComponent_of_gsWeakCorr hS hK hW hbZ
  rw [hMa, sup_idem] at hJM hJMp
  have h34₀ : IsL34Type (gsFixedLayer J b ⧸ Open.fusionZStar (gsFixedLayer J b)) :=
    LieType.CurtisTits.lieModel_of_mulEquiv (Sol78.fusionZStarQuotOfCore φ).symm h34
  have hidx₀ : (pPrimeCore 2 ↥(gsFixedLayer J b)).index = (pPrimeCore 2 ↥J).index := by
    rw [index_eq_card, index_eq_card]
    exact Nat.card_congr φ.toEquiv
  have hidxeq : (pPrimeCore 2 ↥J).index = (pPrimeCore 2 ↥M).index := by
    have hJ0 := le_index_of_l34 h34
    rcases htypes b x M hUM with h5 | h7 | h34M
    · exfalso
      have h60 : (pPrimeCore 2 ↥M).index = 60 := by
        rw [index_eq_card, GSThmB.card_of_lieModel_psl_two (by norm_num) h5]
        decide
      omega
    · exfalso
      have h168 : (pPrimeCore 2 ↥M).index = 168 := by
        rw [index_eq_card, GSThmB.card_of_lieModel_psl_two (by norm_num) h7]
        decide
      omega
    · by_contra hne
      have hlt : (pPrimeCore 2 ↥(gsFixedLayer J b)).index < (pPrimeCore 2 ↥M).index := by
        rw [hidx₀]
        exact lt_of_le_of_ne hidx hne
      have hρ := l34FixedInput G a b M (gsFixedLayer J b) ha hb hab hMb hM hMa hJM hJMp hlt h34M
      have hJc := GSThmB.card_of_lieModel_L34 h34₀
      rcases hρ with h5 | h7
      · rw [GSThmB.card_of_lieModel_psl_two (by norm_num) h5] at hJc
        exact absurd hJc (by decide)
      · rw [GSThmB.card_of_lieModel_psl_two (by norm_num) h7] at hJc
        exact absurd hJc (by decide)
  obtain ⟨hmaxM, htypeM⟩ := hcorr' (hcorr (Or.inr hidxeq))
  have hJM' : gsFixedLayer J b ≤ M := hJM.trans inf_le_left
  have hJ₀s : ∀ s ∈ S, conjugate (gsFixedLayer J b) s = gsFixedLayer J b := by
    intro s hs
    have h1 : (MulAut.conj s⁻¹) b = b := by
      rw [MulAut.conj_apply, inv_inv, mul_assoc, ← hbc s hs, ← mul_assoc, inv_mul_cancel,
        one_mul]
    have h2 := GSLit.map_gsFixedLayer (MulAut.conj s⁻¹) J b
    rw [h1] at h2
    change (gsFixedLayer J b).map (MulAut.conj s⁻¹).toMonoidHom = gsFixedLayer J b
    rw [h2]
    congr 1
    exact conjugate_eq_of_mem_normalizer (hSyl.1 hs)
  have hSM : S ≤ normalizer (M : Set G) := by
    intro s hs
    have hsb : s * b = b * s := hbc s hs
    obtain ⟨hMsb, hMsp⟩ := UGSChain.conjugate_isPComponent_centralizer hsb hMb hM
    by_cases hMs : M = conjugate M s
    · have h1 : conjugate M s = M := hMs.symm
      have h2 : s⁻¹ ∈ normalizer (M : Set G) := mem_normalizer_iff_map_conj_eq.mpr h1
      simpa using inv_mem h2
    · exfalso
      have hc := GrS5.commutator_le_inf_oddIn hMb hMsb hM hMsp hMs
      have hJs : gsFixedLayer J b ≤ conjugate M s := by
        rw [← hJ₀s s hs]
        exact map_mono hJM'
      have hJO : gsFixedLayer J b ≤ (pPrimeCore 2 ↥M).map M.subtype := by
        rw [← GSThmB.commutator_eq_self_of_isPComponent hJM hJMp]
        exact (commutator_mono hJM' hJs).trans (hc.trans inf_le_left)
      have hodd : Odd (Nat.card ↥((pPrimeCore 2 ↥M).map M.subtype)) := by
        rw [card_map_of_injective M.subtype_injective]
        exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
      exact (Nat.not_even_iff_odd.mpr (hodd.of_dvd_nat (card_dvd_of_le hJO)))
        (even_iff_two_dvd.mpr (two_dvd_card_of_l34 h34₀))
  obtain ⟨S', hS', hSS'⟩ := exists_isSylowTwoIn_le hSM hSyl.isPGroup
  have hsetM : L34Sec4Setting G b x M S' :=
    ⟨hbase, hUM, htypeM, hmaxM, hS', hSS' hbS, hSS' hxS⟩
  have hSeq : S = S' := eq_of_le_of_card_ge hSS' (hmaxS b x M S' hsetM)
  rw [← hSeq] at hS'
  refine ⟨M, ⟨hbase, hUM, htypeM, hmaxM, hS', hbS, hxS⟩, fun hbJ => hJM' ?_⟩
  obtain ⟨-, -, -, hTset, -, -⟩ := GrS5.gsFixedLayer_facts hS hK ha hb hab hbZ hJa hJ hbK
  have hb' : b ∈ (gsFixedLayer J b : Set G) * (oddIn J : Set G) := by rw [hTset]; exact hbJ
  obtain ⟨y, hy, o, ho, hyo⟩ := hb'
  have hyb : y * b = b * y :=
    mem_centralizer_singleton_iff.mp (mem_inf.mp (gsFixedLayer_le_inf J b hy)).2
  have hoo : Odd (orderOf o) :=
    (odd_card_map_pPrimeCore J).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ ho)
  exact mem_of_eq_mul_odd (by rw [← pow_two, ← hb, pow_orderOf_eq_one]) hy hyb hyo.symm hoo

theorem exists_setting_zStar_step
    (hS : SchreierFor Blueprint.Catalog) (hMax : MaximalTwoComponentInput) {a x : G}
    {J S : Subgroup G} (hset : L34Sec4Setting G a x J S)
    (hmaxS : ∀ (a' x' : G) (J' S' : Subgroup G), L34Sec4Setting G a' x' J' S' →
      Nat.card S' ≤ Nat.card S)
    (hZ : S ⊓ zStarIn J ≠ ⊥) :
    ∃ (b : G) (M : Subgroup G), L34Sec4Setting G b x M S ∧ (∀ s ∈ S, s * b = b * s) ∧
      b ∈ S ⊓ zStarIn M := by
  have hset' : L34Sec4Setting G a x J S := hset
  obtain ⟨-, -, -, -, hSyl, -, -⟩ := hset'
  obtain ⟨b, hbH, hb, hbc⟩ := exists_central_involution hSyl.isPGroup inf_le_left
    (le_normalizer_inf_zStarIn hSyl.1) hZ
  obtain ⟨hbS, hbZ⟩ := mem_inf.mp hbH
  have hbJK : b ∈ J ⊓ coreActionKernel J := by
    rw [← GSThmB.map_fusionZStar_eq J]
    exact hbZ
  obtain ⟨M, hsetM, hbM⟩ := exists_setting_of_central_step hS hMax hset hmaxS hb hbS hbc
    (mem_inf.mp hbJK).2
  have hsetM' : L34Sec4Setting G b x M S := hsetM
  obtain ⟨-, hUM, -, -, -, -, -⟩ := hsetM'
  obtain ⟨-, -, -, hMb, -, -, -⟩ := gsUnbalancingTriple_iff.mp hUM
  exact ⟨b, M, hsetM, hbc, mem_inf.mpr ⟨hbS,
    GrS4.mem_zStarIn_of_le_centralizer (hbM (mem_inf.mp hbJK).1) hMb⟩⟩

end L34Central

end CFSG.ComponentClassification.GrSLit
