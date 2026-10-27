module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCor48
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm46Cent

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

@[expose] noncomputable def footeB (L : Subgroup G) (t : G) : Subgroup G :=
  centralizer ({t} : Set G) ⊓ coreActionKernel (footeF L t)

omit [Finite G] in
theorem centralizer_le_coreActionKernel' (J : Subgroup G) :
    centralizer (J : Set G) ≤ coreActionKernel J := by
  intro g hg
  refine mem_coreActionKernel.mpr ⟨centralizer_le_normalizer _ hg, fun j hj => ?_⟩
  have h1 : j * g = g * j := mem_centralizer_iff.mp hg j hj
  have h2 : j⁻¹ * g⁻¹ * j * g = 1 := by
    calc j⁻¹ * g⁻¹ * j * g = j⁻¹ * g⁻¹ * (j * g) := by group
      _ = j⁻¹ * g⁻¹ * (g * j) := by rw [h1]
      _ = 1 := by group
  rw [h2]
  exact one_mem _

theorem foote_lemma_4_9_core (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) {M : Subgroup G} (hM : IsFooteM L M) {t : G}
    (ht : orderOf t = 2) (htC : t ∈ coreActionKernel M)
    (hCt : ¬ centralizer ({t} : Set G) ≤ normalizer (M : Set G)) :
    centralizer ({t} : Set G) ≤ normalizer (footeB L t : Set G) ∧ t ∈ footeB L t ∧
      footeB L t ≤ centralizer ({t} : Set G) ∧ ¬ footeB L t ≤ normalizer (M : Set G) ∧
      ∃ Q : Subgroup G, IsSylowOf 2 Q (footeB L t) ∧ Q ≤ coreActionKernel M ∧
        (∃ F : Subgroup G, F ≤ Q ∧ (∀ x ∈ F, x ^ 2 = 1) ∧ Nat.card F = 8) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := footeF L t with hBdef
  obtain ⟨-, -, hBmax, hBF⟩ := foote_lemma_4_5_i h hM ht htC
  have hBN : centralizer ({t} : Set G) ≤ normalizer (B : Set G) :=
    le_normalizer_of_mem_footeFamilyOf h.huniq hBmax.1 hBF
  have hBt : B ≤ centralizer ({t} : Set G) := hBmax.1.2.1
  have hNB : centralizer ({t} : Set G) ≤ normalizer (footeB L t : Set G) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    have h1 := mem_normalizer_iff.mp (le_normalizer hg) x
    have h2 := mem_normalizer_iff.mp (normalizer_le_normalizer_coreActionKernel B (hBN hg)) x
    simp only [footeB, mem_inf]
    exact and_congr h1 h2
  have htB : t ∈ footeB L t := by
    refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr rfl, ?_⟩
    apply centralizer_le_coreActionKernel'
    exact mem_centralizer_iff.mpr fun b hb => mem_centralizer_singleton_iff.mp (hBt hb)
  obtain ⟨F, hF, hF2, hF8⟩ := exists_card_eight_of_le_pRank (h47 G L h M hM t ht htC)
  obtain ⟨hBM, -⟩ := footeF_le_of_card_eight h hM ht htC hF2 hF8 hF
  have hCB : coreActionKernel M ⊓ centralizer ({t} : Set G) ≤ coreActionKernel B := fun x hx =>
    mem_coreActionKernel_of_le hBM (hBN (mem_inf.mp hx).2) (mem_inf.mp hx).1
  obtain ⟨Q, hQ⟩ := exists_isSylowOf 2 (coreActionKernel M ⊓ centralizer ({t} : Set G))
  have heq : coreActionKernel M ⊓ coreActionKernel B ⊓ centralizer ({t} : Set G) =
      coreActionKernel M ⊓ centralizer ({t} : Set G) := by
    apply le_antisymm
    · exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
    · exact le_inf (le_inf inf_le_left hCB) inf_le_right
  obtain ⟨-, hiv2, -, -⟩ := foote_lemma_4_5_iv h hM ht htC hF2 hF8 hF
  have hQB : IsSylowOf 2 Q (footeB L t) := by
    have h1 := hiv2 Q (heq ▸ hQ)
    rwa [inf_comm] at h1
  have hQC : Q ≤ coreActionKernel M := hQ.le.trans inf_le_left
  have hFp : IsPGroup 2 F := IsPGroup.of_card (n := 3) (by rw [hF8]; norm_num)
  obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf hQ hF hFp
  have hFQ : ∃ F' : Subgroup G, F' ≤ Q ∧ (∀ x ∈ F', x ^ 2 = 1) ∧ Nat.card F' = 8 :=
    ⟨conjugate F k, conjugate_le_of_forall hk, sq_eq_one_of_mem_conjugate hF2 k,
      by rw [card_conjugate_eq_card, hF8]⟩
  have hBnot : ¬ footeB L t ≤ normalizer (M : Set G) := by
    intro hle
    apply hCt
    obtain ⟨F', hF'Q, hF'2, hF'8⟩ := hFQ
    obtain ⟨W, hW, hWF'⟩ := exists_isKleinFour_le hF'2 (by omega)
    have hNQ : normalizer (Q : Set G) ≤ normalizer (M : Set G) :=
      foote_cor_4_8_iv h h47 hST hM hQC hW (hWF'.trans hF'Q)
    intro g hg
    obtain ⟨m, hm, hgm⟩ := exists_mul_mem_normalizer_of_isSylowOf hQB (hNB hg)
    rw [show g = g * m * m⁻¹ by group]
    exact mul_mem (hNQ hgm) (inv_mem (hle hm))
  exact ⟨hNB, htB, inf_le_left, hBnot, Q, hQB, hQC, hFQ⟩

theorem foote_lemma_4_9_gamma
    (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) {M : Subgroup G} (hM : IsFooteM L M) {t : G}
    (ht : orderOf t = 2) (htC : t ∈ coreActionKernel M)
    (hCt : ¬ centralizer ({t} : Set G) ≤ normalizer (M : Set G)) :
    ∃ S : Sylow 2 ↥(footeB L t),
      Open.properTwoGenCoreGamma (S : Subgroup ↥(footeB L t)) 2 ≠ ⊤ ∧
        3 ≤ CFSG.pRank 2 ↥(footeB L t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hBnot, Q, hQB, hQC, F, hFQ, hF2, hF8⟩ :=
    foote_lemma_4_9_core h h47 hST hM ht htC hCt
  set B := footeB L t with hBdef
  have hQB' := hQB
  obtain ⟨S, hS⟩ := hQB'
  have hcore : Open.properTwoGenCoreGamma (S : Subgroup B) 2 ≠ ⊤ := by
    intro htop
    apply hBnot
    have hle : Open.properTwoGenCoreGamma (S : Subgroup B) 2 ≤
        (normalizer (M : Set G)).subgroupOf B := by
      refine iSup₂_le fun X hXS => iSup_le fun hX2 => ?_
      obtain ⟨E, hEX, hE, hEcard⟩ := SectionRank.exists_pRank one_lt_two X
      have hE4 : 4 ≤ Nat.card E := by
        rw [hEcard]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ Open.pRank 2 X := Nat.pow_le_pow_right (by norm_num) hX2
      obtain ⟨V, hV, hVE⟩ := exists_isKleinFour_le hE.2 hE4
      have hXQ : X.map B.subtype ≤ Q := hS ▸ map_mono hXS
      have hVG : IsKleinFour (V.map B.subtype) := by
        refine isKleinFour_of_card_eq_four ?_ ?_
        · rw [card_map_of_injective B.subtype_injective, hV.card_four]
        · rintro _ ⟨v, hv, rfl⟩
          rw [← map_pow, sq_eq_one_of_isKleinFour hV hv, map_one]
      have hNX := foote_cor_4_8_iv h h47 hST hM (hXQ.trans hQC) hVG
        (map_mono (hVE.trans hEX))
      intro b hb
      exact hNX (Subgroup.le_normalizer_map B.subtype ⟨b, hb, rfl⟩)
    intro x hx
    have h1 : (⟨x, hx⟩ : B) ∈ (normalizer (M : Set G)).subgroupOf B := hle (htop ▸ mem_top _)
    exact h1
  have hrank : 3 ≤ CFSG.pRank 2 B := by
    rw [SectionRank.pRank_eq_open_pRank_top]
    have hFB : F ≤ B := hFQ.trans hQB.le
    have hel : Open.IsElemAbelian 2 (F.subgroupOf B) := by
      refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun a ha => Subtype.ext ?_⟩
      · exact commute_of_sq_eq_one hF2 a.2 b.2
      · rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact hF2 _ ha
    have hcard : Nat.card (F.subgroupOf B) = 2 ^ 3 := by
      rw [← Nat.card_congr (subgroupOfEquivOfLe hFB).symm.toEquiv, hF8]
      norm_num
    exact SectionRank.le_pRank one_lt_two le_top hel hcard
  exact ⟨S, hcore, hrank⟩

end CFSG.ComponentClassification.FooteLit
