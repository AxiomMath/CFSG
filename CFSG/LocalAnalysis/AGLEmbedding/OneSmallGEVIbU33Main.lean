module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbU33Block
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaOrder
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeUnique
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalCount
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneChar
import CFSG.LocalAnalysis.AGLEmbedding.SurvivorBarM
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltSplit

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem D1PhaseThree.false_of_u33_three_ib (h : D1PhaseThree p P M H R) (hp3 : p = 3)
    (hc : D1IbCubeThreeData p P M H R Rbar K z)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hSch : KFactCatalogSchreier) (hShape : KFactSmallSylowShape) (hOrb3 : KFactSmallOrbitsCube)
    (hK : CitedBlockToralThreeIb) (hKA : CitedBlockThreeAutCenterIb)
    (hperf : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ barM M (H ⊓ M) → ⁅V, V⁆ = V →
      ¬ 3 ^ 2 ∣ Nat.card V)
    (hcent : ∀ W : Subgroup (H ⧸ primeComplementCore (G := H) p), W ≤ d1X0 p M H →
      ⁅W, W⁆ = W → W ≤ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)))
    (hcov : ∃ V : Subgroup G, V ≤ H ⊓ M ∧ ⁅V, V⁆ = V ∧ z ∈ V ∧
      ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → V ≤ Subgroup.normalizer (L : Set G))
    (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hsyl : ∃ S : Sylow 3 ↥(M ⊓ Subgroup.centralizer ({z} : Set G)),
      (S : Subgroup _).map (M ⊓ Subgroup.centralizer ({z} : Set G)).subtype = R)
    (hfusZ : ∀ r ∈ R, r ∉ d1LiftX p H R K → (∀ s ∈ R, r * s = s * r) → r ∈ fusionSet R z)
    (hinv : ∀ t ∈ d1LiftX p H R K, t ≠ 1 → ∃ n ∈ M, n * z * n⁻¹ = z ∧ n * t * n⁻¹ = t⁻¹)
    (hPz : ∀ y ∈ (P : Subgroup G), y * z = z * y → y ∈ R)
    (hP6 : 3 ^ 6 ≤ Nat.card (P : Subgroup G))
    (hmove : ∃ x ∈ (P : Subgroup G), x ∈ Subgroup.normalizer (R : Set G) ∧ x ∉ R ∧
      x * z * x⁻¹ ∉ Subgroup.zpowers z) : False := by
  subst hp3
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set S := pCoreOf 2 H with hS
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set T := d1LiftX 3 H R K with hT
  have hRM : R ≤ M := h.le_M
  have hRp : IsPGroup 3 R := h.isPGroup
  have hTR : T ≤ R := d1LiftX_le 3 H R K
  have hzR : z ∈ R := hc.elt.1
  have hzM : z ∈ M := hRM hzR
  set zb := mk ⟨z, hzM⟩ with hzb
  have hzo : orderOf z = 3 := hc.elt.2.1
  have hz3 : z ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
  have hz : IsPGroup 3 (Subgroup.zpowers z) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hz3)
  have hzb3 : zb ^ 3 = 1 := by
    rw [hzb, ← map_pow]
    have : (⟨z, hzM⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
    rw [this, map_one]
  have hzT : z ∉ T := hc.card_d1LiftX.2
  have hPL : ∀ L : Subgroup G, IsWeakSBlock M S L → IbPerfectSections 3 (blockPL M S L) := by
    intro L hL W hW hWp
    refine hperf W (hW.trans (barM_mono ?_)) hWp
    rw [h.normalizer_twoCore_H]
    exact inf_le_inf_left H hL.le
  obtain ⟨L₁, hL₁, hzL₁'⟩ :=
    h.exists_block_u33_three_ib rfl hc h84 hD2 hSch hShape hOrb3 hcov hCz hsyl hfusZ hinv
  have hzL₁ : zb ∈ barM M L₁ := hzL₁'
  have hzC₁ := h.not_mem_centralizer_block hp hp2 hzM hz hCz hL₁
  set A := barM M L₁ with hA
  have hall : ∀ L' : Subgroup G, IsWeakSBlock M S L' → barM M L' = A := fun L' hL' =>
    h.barM_eq_of_mem_component hp hp2 hzM hz hCz hL₁.component hzL₁ hL'
  have hNA : ∀ g : G, g ∈ H → ∀ hgM : g ∈ M,
      mk ⟨g, hgM⟩ ∈ Subgroup.normalizer (A : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro g hgH hgM
    have hL' := hL₁.map_conj hgM (localGroup_le_normalizer_pCoreOf 2 H hgH)
    have he := hall _ hL'
    rw [barM_map_conj hgM L₁] at he
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr he
  have hTL₁ : ∀ t ∈ T, t ∈ Subgroup.normalizer (L₁ : Set G) := by
    intro t ht
    have htH : t ∈ H := hc.data.cfg.ext.le_H (hTR ht)
    have htM : t ∈ M := hRM (hTR ht)
    have hL' := hL₁.map_conj htM (localGroup_le_normalizer_pCoreOf 2 H htH)
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (hL'.toIsTwoPrimeComponent.eq_of_barM_eq hL₁.toIsTwoPrimeComponent (hall _ hL'))
  obtain ⟨t, htZ, ht1, htM, htA⟩ :=
    h.exists_center_mem_block_u33 rfl hc hcent hL₁ hzL₁ hall hmove
  have htT : t ∈ T := htZ.1
  have htR : t ∈ R := hTR htT
  have ht3 : t ^ 3 = 1 := hc.exp t htR
  have hto : orderOf t = 3 := by
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one ht3) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) ht1
    · exact h1
  set E := Subgroup.zpowers t ⊔ Subgroup.zpowers z with hE
  have hER : E ≤ R := sup_le (Subgroup.zpowers_le.mpr htR) (Subgroup.zpowers_le.mpr hzR)
  have hEp : IsPGroup 3 E := hRp.to_le hER
  have hinf : Subgroup.zpowers t ⊓ Subgroup.zpowers z = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun y hy => ?_
    by_contra hy1
    have hzy := mem_zpowers_of_mem_zpowers_of_prime hp hzo hy.2 hy1
    exact hzT ((Subgroup.zpowers_le.mpr ((Subgroup.zpowers_le.mpr htT) hy.1)) hzy)
  have hE9 : 3 ^ 2 ∣ Nat.card E := by
    have h1 := mul_card_le_of_inf_eq_bot (le_sup_left : Subgroup.zpowers t ≤ E) le_sup_right hinf
    rw [Nat.card_zpowers, Nat.card_zpowers, hto, hzo] at h1
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hEp
    rw [hk] at h1 ⊢
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have : 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact Nat.pow_dvd_pow 3 hk2
  set Ã : Subgroup G := (A.comap mk).map M.subtype with hÃ
  have hÃA : barM M Ã = A := by
    have h1 : Ã.subgroupOf M = A.comap mk :=
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
    change (Ã.subgroupOf M).map mk = A
    rw [h1, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  have hEÃ : E ≤ Ã := by
    refine sup_le (Subgroup.zpowers_le.mpr ⟨⟨t, htM⟩, htA, rfl⟩)
      (Subgroup.zpowers_le.mpr ⟨⟨z, hzM⟩, hzL₁, rfl⟩)
  have hA9 : 3 ^ 2 ∣ Nat.card A := by
    have h1 : Nat.card (barM M E) = Nat.card E := card_barM_of_isPGroup hp hp2 (hER.trans hRM) hEp
    rw [← hÃA]
    exact (h1 ▸ hE9).trans (Subgroup.card_dvd_of_le (barM_mono hEÃ))
  have hPA : barM M (P : Subgroup G) ≤ Subgroup.normalizer (A : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨⟨g, hgM⟩, -, rfl⟩
    have hL₃c := hL₁.toIsTwoPrimeComponent.map_conj hgM
    by_cases hwk : L₁.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (S : Set G)
    · exfalso
      have hL₃H : L₁.map (MulAut.conj g).toMonoidHom ≤ H := by
        have := hwk
        rwa [h.normalizer_twoCore_H] at this
      have hle : barM M (L₁.map (MulAut.conj g).toMonoidHom) ≤ barM M (H ⊓ M) :=
        barM_mono (le_inf hL₃H hL₃c.le)
      obtain ⟨hp', -, -⟩ := h.barM_cover (V := L₁.map (MulAut.conj g).toMonoidHom)
        (le_inf hL₃H hL₃c.le) hL₃c.perfect (L := L₁.map (MulAut.conj g).toMonoidHom)
        Subgroup.le_normalizer
      refine hperf _ hle hp' ?_
      rw [barM_map_conj hgM L₁, Subgroup.card_map_of_injective (MulAut.conj _).injective]
      exact hA9
    · have he := hall _ ⟨hL₃c, hwk⟩
      rw [barM_map_conj hgM L₁] at he
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr he
  have hinvX : ∀ X : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      Subgroup.normalizer (A : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
        Subgroup.normalizer (X : Set (↥M ⧸ CFSG.pCore 2 ↥M)) →
      IsInvR 3 H R K z (rPart M R X) := by
    intro X hX n hn hnz _ b hb
    have hnM : n ∈ M := h.toD1Escape.normalizer_le hn
    have hnC : n ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc n * z = n * z * n⁻¹ * n := by group
        _ = z * n := by rw [hnz]
    have hnN := hX (hNA n (hCz hnC) hnM)
    have hbR : b ∈ R := hb.1
    have hnbR : n * b * n⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hn b).mp hbR
    rw [mem_rPart hRM hbR] at hb
    rw [mem_rPart hRM hnbR]
    have h1 : (⟨n * b * n⁻¹, hRM hnbR⟩ : ↥M) = ⟨n, hnM⟩ * ⟨b, hRM hbR⟩ * ⟨n, hnM⟩⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hnN _).mp hb
  have hRCinv := hinvX _ (normalizer_le_normalizer_centralizer _)
  have hzRL : z ∈ rPart M R A := (mem_rPart hRM hzR).mpr hzL₁
  obtain ⟨V, hVHM, hVp, hzV, hVN⟩ := hcov
  obtain ⟨hVp', hVL', hVSL⟩ := h.barM_cover hVHM hVp (hVN L₁ hL₁)
  have hVz : ∃ V' : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), ⁅V', V'⁆ = V' ∧
      V' ≤ Subgroup.normalizer (A : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      V' ≤ Subgroup.normalizer (barM M (S ⊓ L₁) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧ zb ∈ V' :=
    ⟨barM M V, hVp', hVL', hVSL, ⟨⟨z, hzM⟩, Subgroup.mem_subgroupOf.mpr hzV, rfl⟩⟩
  have hfix := fun l hl hl' => h.fixed_le_barM_normalizer_inf hp hp2 hzM hz hCz (L := L₁) l hl hl'
  have hTRA : ¬ T ≤ rPart M R A := by
    intro hTL
    have hRA : barM M R ≤ A := by
      rintro _ ⟨⟨y, hyM⟩, hyR, rfl⟩
      have hyR' := Subgroup.mem_subgroupOf.mp hyR
      have hyRL : y ∈ rPart M R A := by
        obtain ⟨t', ht', i, rfl⟩ := hc.dec y hyR'
        exact (rPart M R A).mul_mem (hTL ht') ((rPart M R A).pow_mem hzRL i)
      exact (mem_rPart hRM hyR').mp hyRL
    obtain ⟨E₃, hE₃R, hE₃el, hE₃card⟩ :=
      CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3 hp R
    rw [hc.data.pRank_R] at hE₃card
    refine hK G M S L₁ h.isKGroup.1 h.asc81bHyp hL₁ (h.nineThree h93 hL₁)
      (h.nineThree_not_one h85 hD2 hL₁).1 (h.not_isSylowTwoOf_inf h85 hD2 hL₁) (hPL L₁ hL₁) zb
      hzL₁ hzb3 hzC₁ hVz hfix (barM M E₃) ((barM_mono hE₃R).trans hRA) ?_
      (isElemAbelian_barM hE₃el) ?_
    · rintro _ ⟨⟨e, heM⟩, he, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, hzb, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hc.commute_z (hE₃R (Subgroup.mem_subgroupOf.mp he)))
    · rw [card_barM_of_isPGroup hp hp2 (hE₃R.trans hRM) (IsPGroup.of_card (n := 3) hE₃card),
        hE₃card]
  obtain ⟨hAut, hCen⟩ := hKA G M S L₁ h.isKGroup.1 h.asc81bHyp (h.twoCore_M_le h.twoCore_inf)
    hL₁ (h.nineThree h93 hL₁) (h.nineThree_not_one h85 hD2 hL₁).1
    (h.not_isSylowTwoOf_inf h85 hD2 hL₁) (hPL L₁ hL₁) zb hzL₁ hzb3 hzC₁ hVz hfix
  have hzRC : z ∉ rPart M R (Subgroup.centralizer (A : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :=
    fun hz' => hzC₁ ((mem_rPart hRM hzR).mp hz')
  rcases hc.lattice hShape hOrb3 inf_le_left hRCinv with hTC | ⟨hdecC, hbotC, hneC⟩
  ·
    have hTbar : barM M T ≤ Subgroup.centralizer (A : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
      rintro _ ⟨⟨y, hyM⟩, hyT, rfl⟩
      exact (mem_rPart hRM (hTR (Subgroup.mem_subgroupOf.mp hyT))).mp
        (hTC (Subgroup.mem_subgroupOf.mp hyT))
    have hTS : T ≤ Subgroup.normalizer (S : Set G) := fun y hy =>
      localGroup_le_normalizer_pCoreOf 2 H (hc.data.cfg.ext.le_H (hTR hy))
    have hbot := hCen T (hTR.trans hRM) (hRp.to_le hTR) hTL₁ hTS hTbar
    have htcomm : t ∈ ⁅T, T⁆ := hc.centerOf_le_commutator_self hShape htZ
    have hmk : mk ⟨t, htM⟩ ∈ ⁅barM M T, barM M T⁆ := by
      rw [← barM_commutator (hTR.trans hRM)]
      exact ⟨⟨t, htM⟩, Subgroup.mem_subgroupOf.mpr htcomm, rfl⟩
    have htC : mk ⟨t, htM⟩ ∈ Subgroup.centralizer (A : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
      hTbar ⟨⟨t, htM⟩, Subgroup.mem_subgroupOf.mpr htT, rfl⟩
    have hmem : mk ⟨t, htM⟩ ∈ ⁅barM M T, barM M T⁆ ⊓
        (A ⊓ Subgroup.centralizer (A : Set (↥M ⧸ CFSG.pCore 2 ↥M))) := ⟨hmk, htA, htC⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact ht1 (eq_one_of_mem_pCoreOf_two hp hp2 hRp htR (coe_mem_pCoreOf_two_of_mk_eq_one _ hmem))
  ·
    set RC := rPart M R (Subgroup.centralizer (A : Set (↥M ⧸ CFSG.pCore 2 ↥M))) with hRCdef
    have hRC3 : Nat.card RC ≤ 3 := by
      by_cases hD : RC ⊓ T = ⊥
      · have hle := hbotC hD
        have hbot' : RC = ⊥ := by
          refine (Subgroup.eq_bot_iff_forall _).mpr fun b hb => ?_
          by_contra hb1
          exact hzRC ((Subgroup.zpowers_le.mpr hb)
            (mem_zpowers_of_mem_zpowers_of_prime hp hzo (hle hb) hb1))
        rw [hbot', Subgroup.card_bot]
        norm_num
      · have hZle := hneC hD
        have hle : RC ≤ centerOf T := by
          intro b hb
          obtain ⟨c, hcZ, i, rfl⟩ := hdecC b hb
          have hzi : z ^ i ∈ RC := by
            have := RC.mul_mem (RC.inv_mem (hZle hcZ)) hb
            simpa using this
          by_cases hzi1 : z ^ i = 1
          · rw [hzi1, mul_one]
            exact hcZ
          · exact absurd ((Subgroup.zpowers_le.mpr hzi) (mem_zpowers_of_mem_zpowers_of_prime hp hzo
              (Subgroup.npow_mem_zpowers z i) hzi1)) hzRC
        calc Nat.card RC ≤ Nat.card (centerOf T) := Subgroup.card_le_of_le hle
          _ = 3 := hc.card_Z hShape
    have hidx := hAut (barM M (P : Subgroup G)) hPA ((P.isPGroup'.comap_subtype (K := M)).map _)
    have hbound := card_le_mul_card_rPart h.sylow_le P.isPGroup' hRM hRp (h.le_P hzR) hPz
      (C := Subgroup.centralizer (A : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
      (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hy _ hzL₁).symm) hidx
    have hRC3' : Nat.card (rPart M R
        (Subgroup.centralizer (A : Set (↥M ⧸ CFSG.pCore 2 ↥M)))) ≤ 3 := hRC3
    have h729 : (3 : ℕ) ^ 6 = 729 := by norm_num
    rw [h729] at hP6
    omega

end CFSG.AGLEmbedding
