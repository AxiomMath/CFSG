module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma410Setup
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma414Small

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools GSThmB

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem Foote410Config.isPGroup_sup {M : Subgroup G} {g : G} {E Q : Subgroup G} {t : G}
    (hc : Foote410Config M g E Q t) : IsPGroup 2 ↥(E ⊔ Q) := by
  have hEp : IsPGroup 2 E := IsPGroup.of_card (n := 3) (by rw [hc.hE8]; norm_num)
  have hQp : IsPGroup 2 Q := IsPGroup.of_card (n := 3) (by rw [hc.hQ8]; norm_num)
  refine hEp.to_sup_of_normal_left' hQp fun q hq => mem_normalizer_iff.mpr fun e => ?_
  constructor
  · intro he
    rw [show q * e * q⁻¹ = e by rw [← hc.hEQ e he q hq]; group]
    exact he
  · intro he
    have h1 := hc.hEQ _ he q hq
    have h2 : e = q * e * q⁻¹ := by
      calc e = q⁻¹ * (q * e * q⁻¹ * q) := by group
        _ = q⁻¹ * (q * (q * e * q⁻¹)) := by rw [h1]
        _ = q * e * q⁻¹ := by group
    rw [h2]
    exact he

theorem Foote410Config.exists_sylow
    (h : FooteSec4 G L) (h47 : FooteThm47Statement) (hST : GSThmB.SuzukiTausskyInput)
    (hAsc : Foote5.AschbacherCentralCoreInput) (h2An : GSThmB.Solomon2AnInput) {M : Subgroup G}
    (hM : IsFooteM L M) {g : G} {E Q : Subgroup G} {t : G} (hc : Foote410Config M g E Q t) :
    ∃ T : Subgroup G, IsSylowOf 2 T (coreActionKernel M ⊓ centralizer ({t} : Set G)) ∧ Q ≤ T ∧
      E ≤ normalizer (T : Set G) ∧ IsSylowOf 2 (T ⊓ footeK L t) (footeK L t) ∧
      E ≤ normalizer ((T ⊓ footeK L t : Subgroup G) : Set G) ∧
      Q ≤ normalizer ((T ⊓ footeK L t : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ht2, htC, hCt⟩ := hc.ht
  obtain ⟨hBN, -, hBs, -⟩ := foote_lemma_4_9_core h h47 hST hM ht2 htC hCt
  obtain ⟨hKB, -⟩ := foote_lemma_4_9 h h47 hST hAsc h2An hM ht2 htC hCt
  obtain ⟨R₀, hR₀, hR₀C⟩ := exists_isSylowOf_footeK_le h h47 hST hAsc h2An hM hc.ht
  set K := footeK L t with hK
  set C := coreActionKernel M with hC
  set D := C ⊓ centralizer ({t} : Set G) with hD
  have hKs : K ≤ centralizer ({t} : Set G) := hKB.trans hBs
  have hEt : E ≤ centralizer ({t} : Set G) := fun e he =>
    mem_centralizer_singleton_iff.mpr (hc.hEQ e he t hc.htQ)
  have hQt : Q ≤ centralizer ({t} : Set G) := fun q hq =>
    mem_centralizer_singleton_iff.mpr (commute_of_sq_eq_one hc.hQ2 hq hc.htQ)
  have hQD : Q ≤ D := le_inf hc.hQC hQt
  have hEQD : E ⊔ Q ≤ normalizer (D : Set G) := sup_le
    (fun e he => mem_normalizer_inf' (normalizer_le_normalizer_coreActionKernel M (hc.hEN he))
      (le_normalizer (hEt he)))
    (hQD.trans le_normalizer)
  obtain ⟨T, hT, hQT, hTN⟩ := exists_isSylowOf_ge_le_normalizer hEQD hQD
    (by rw [sup_assoc, sup_idem]; exact hc.isPGroup_sup)
  have hKCD : K ⊓ C ≤ D := fun x hx =>
    mem_inf.mpr ⟨(mem_inf.mp hx).2, hKs (mem_inf.mp hx).1⟩
  have hDKC : D ≤ normalizer ((K ⊓ C : Subgroup G) : Set G) := fun d hd =>
    mem_normalizer_inf' (mem_normalizer_footeK (hBN (mem_inf.mp hd).2))
      (le_normalizer (mem_inf.mp hd).1)
  have hTKC := hT.inf_of_le_normalizer hKCD hDKC
  have hTC : T ≤ C := hT.le.trans inf_le_left
  have hTKC' : T ⊓ (K ⊓ C) = T ⊓ K := by
    ext x
    simp only [mem_inf]
    exact ⟨fun hx => ⟨hx.1, hx.2.1⟩, fun hx => ⟨hx.1, hx.2, hTC hx.1⟩⟩
  rw [hTKC'] at hTKC
  have hR₀KC : IsSylowOf 2 R₀ (K ⊓ C) := hR₀.of_le (le_inf hR₀.le hR₀C) inf_le_left
  have hRK : IsSylowOf 2 (T ⊓ K) K := by
    apply isSylowOf_of_card (hTKC.le.trans inf_le_left)
    rw [hTKC.card_eq, ← hR₀KC.card_eq, hR₀.card_eq]
  have hKN : ∀ x ∈ centralizer ({t} : Set G), x ∈ normalizer (K : Set G) := fun x hx =>
    mem_normalizer_footeK (hBN hx)
  refine ⟨T, hT, hQT, fun e he => hTN (mem_sup_left he), hRK, fun e he => ?_, fun q hq => ?_⟩
  · exact mem_normalizer_inf' (hTN (mem_sup_left he)) (hKN e (hEt he))
  · exact mem_normalizer_inf' (hTN (mem_sup_right hq)) (hKN q (hQt hq))

theorem Foote410Config.not_mem_footeK
    (h : FooteSec4 G L) (h47 : FooteThm47Statement) (hST : GSThmB.SuzukiTausskyInput)
    (hAsc : Foote5.AschbacherCentralCoreInput) (h2An : GSThmB.Solomon2AnInput) {M : Subgroup G}
    (hM : IsFooteM L M) {g : G} {E Q : Subgroup G} {t : G} (hc : Foote410Config M g E Q t) :
    t ∉ footeK L t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro htK
  obtain ⟨ht2, htC, hCt⟩ := hc.ht
  obtain ⟨-, -, -, -, htype, -⟩ := foote_lemma_4_9 h h47 hST hAsc h2An hM ht2 htC hCt
  have hcov : IsCoverOverTwo (footeK L t ⧸ pPrimeCore 2 (footeK L t)) (Open.Sz 1) := by
    rcases htype with ⟨-, h1⟩ | ⟨h1, -⟩
    · exact absurd htK h1
    · exact h1
  obtain ⟨T, hT, hQT, hET, hRK, -, -⟩ := hc.exists_sylow h h47 hST hAsc h2An hM
  obtain ⟨A, hAR, hA16, hA2, hAinv⟩ := exists_omega_of_isCoverOverTwo_sz_quotient hRK hcov
  have hTC : T ≤ coreActionKernel M := hT.le.trans inf_le_left
  have hTs : T ≤ centralizer ({t} : Set G) := hT.le.trans inf_le_right
  have htt : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  have hTA : ∀ x ∈ T, x ^ 2 = 1 → x ∈ A := by
    intro x hxT hx2
    by_cases hx1 : x = 1
    · rw [hx1]
      exact one_mem A
    have hxo : orderOf x = 2 := orderOf_eq_prime hx2 hx1
    have hxs : x * t = t * x := mem_centralizer_singleton_iff.mp (hTs hxT)
    rcases mem_or_mul_mem_footeK h h47 hST hAsc h2An hM hc.ht (hTC hxT) hxs hxo with hxK | hxK
    · exact hAinv x (mem_inf.mpr ⟨hxT, hxK⟩) hx2
    · have h1 : x ∈ footeK L t := by
        have h2 := mul_mem hxK (inv_mem htK)
        rwa [mul_inv_cancel_right] at h2
      exact hAinv x (mem_inf.mpr ⟨hxT, h1⟩) hx2
  have hAo : IsOmegaOneOf A T := ⟨hAR.trans inf_le_left, hA2, hTA⟩
  have hEA : A ≤ centralizer (E : Set G) := by
    intro a ha
    rw [mem_centralizer_iff]
    intro e he
    have h1 := conj_eq_of_footeInCC_of_mem_footeK h h47 hST hAsc h2An hM hc.ht htK hT hAo
      (hc.hE2 e he) (mem_centralizer_singleton_iff.mpr (hc.hEQ e he t hc.htQ))
      (hET he) a ha
    calc e * a = e * a * e⁻¹ * e := by group
      _ = a * e := by rw [h1]
  obtain ⟨W, hW, hWE⟩ := exists_isKleinFour_le hc.hE2 (by rw [hc.hE8]; norm_num)
  have hAN : A ≤ normalizer (conjugate M g : Set G) := fun a ha =>
    foote_cor_4_8_iv h h47 hST (isFooteM_conjugate h hM g) hc.hEC hW hWE
      (centralizer_le_normalizer _ (hEA ha))
  have hAp : IsPGroup 2 A := hT.isPGroup.to_le (hAR.trans inf_le_left)
  have hQA : Q ≤ A := fun q hq => hTA q (hQT hq) (hc.hQ2 q hq)
  have hAQ := hc.hQSyl.eq_of_le hQA (le_inf ((hAR.trans inf_le_left).trans hTC) hAN) hAp
  have h8 := hc.hQ8
  rw [← hAQ, hA16] at h8
  omega

theorem Foote410Config.card_inf_footeK
    (h : FooteSec4 G L) (h47 : FooteThm47Statement) (hST : GSThmB.SuzukiTausskyInput)
    (hAsc : Foote5.AschbacherCentralCoreInput) (h2An : GSThmB.Solomon2AnInput) {M : Subgroup G}
    (hM : IsFooteM L M) {g : G} {E Q : Subgroup G} {t : G} (hc : Foote410Config M g E Q t)
    (htK : t ∉ footeK L t) : Nat.card ↥(Q ⊓ footeK L t) = 4 := by
  set K := footeK L t with hK
  set V := Q ⊓ K with hV
  have hVQ : V ≤ Q := inf_le_left
  have hx : ∀ x ∈ Q, x ∈ K ∨ x * t ∈ K := by
    intro x hxQ
    by_cases hx1 : x = 1
    · left
      rw [hx1]
      exact one_mem K
    · exact mem_or_mul_mem_footeK h h47 hST hAsc h2An hM hc.ht (hc.hQC hxQ)
        (commute_of_sq_eq_one hc.hQ2 hxQ hc.htQ) (orderOf_eq_prime (hc.hQ2 x hxQ) hx1)
  have hidx : (V.subgroupOf Q).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨t, hc.htQ⟩, fun b => ?_⟩
    rw [mem_subgroupOf, mem_subgroupOf, Subgroup.coe_mul]
    by_cases hb : (b : G) ∈ K
    · right
      refine ⟨mem_inf.mpr ⟨b.2, hb⟩, fun h1 => htK ?_⟩
      have h2 := mul_mem (inv_mem hb) (mem_inf.mp h1).2
      rwa [inv_mul_cancel_left] at h2
    · left
      exact ⟨mem_inf.mpr ⟨mul_mem b.2 hc.htQ, (hx b b.2).resolve_left hb⟩,
        fun h1 => hb (mem_inf.mp h1).2⟩
  have h1 := (V.subgroupOf Q).card_mul_index
  rw [hidx, Nat.card_congr (subgroupOfEquivOfLe hVQ).toEquiv, hc.hQ8] at h1
  omega

end CFSG.ComponentClassification.FooteLit
