module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614ICommon
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614IIndex
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614IL32Sylow
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Plane
import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Setup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614I

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M : Subgroup G} {x z : G}
  {H S K : Subgroup G}

theorem plane_of_hyp (hyp : Hyp P M x z H S) : SmallRankPlane 3 (P : Subgroup G) x z :=
  SmallRankPlane.of_situation hyp.setting hyp.situation hyp.point hyp.central

theorem P_le_M (hyp : Hyp P M x z H S) : (P : Subgroup G) ≤ M :=
  (sylow_le_of_isCoreMaxLocal hyp.setting hyp.situation.mem_sigmaA
    hyp.situation.isCoreMaxLocal).1

theorem pRank_P (hyp : Hyp P M x z H S) : CFSG.Open.pRank 3 (P : Subgroup G) = 3 :=
  (sylow_le_of_isCoreMaxLocal hyp.setting hyp.situation.mem_sigmaA
    hyp.situation.isCoreMaxLocal).2

theorem B_le_P (hyp : Hyp P M x z H S) : zpowers x ⊔ zpowers z ≤ (P : Subgroup G) :=
  (plane_of_hyp hyp).isIsolatedPlane.1

theorem isPGroup_B (hyp : Hyp P M x z H S) : IsPGroup 3 ↥(zpowers x ⊔ zpowers z) :=
  IsPGroup.of_card (n := 2) (plane_of_hyp hyp).card_eq

theorem S_le_glbPrimeCore (hyp : Hyp P M x z H S) (hα : HasPrimeConstraint (G := M) 3) :
    S ≤ GLBPrimeCore 3 M := by
  have hpl := plane_of_hyp hyp
  have hS3 : Nat.Coprime 3 (Nat.card S) := by
    obtain ⟨k, hk⟩ := (isPGroup_S hyp).exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  exact CFSG.AGLEmbedding.signalizer_le_glbPrimeCore_of_contains Nat.prime_three (by norm_num)
    hα (isPGroup_B hyp) ((B_le_P hyp).trans (P_le_M hyp))
    (fun y _ hyB hord => hpl.mem_of_mem_centralizer y hyB (by
      rw [← hord]
      exact pow_orderOf_eq_one y)) (S_le_M hyp) hS3 (B_le_normalizer_S hyp)

omit [Finite G] in
theorem center_map_of_fix {Q : Subgroup G} {φ : G →* G} (hφ : Function.Injective φ)
    (hzφ : φ z = z) (hcen : ∀ w ∈ Q, w ∈ centralizer (Q : Set G) → w ^ 3 = 1 → w ∈ zpowers z) :
    ∀ w ∈ Q.map φ, w ∈ centralizer ((Q.map φ : Subgroup G) : Set G) → w ^ 3 = 1 →
      w ∈ zpowers z := by
  rintro _ ⟨p, hp, rfl⟩ hwc hw3
  have hpc : p ∈ centralizer (Q : Set G) := by
    rw [mem_centralizer_iff]
    intro q hq
    apply hφ
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.mp hwc (φ q) ⟨q, hq, rfl⟩
  have hp3 : p ^ 3 = 1 := by
    apply hφ
    rw [map_pow, map_one]
    exact hw3
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hcen p hp hpc hp3)
  exact mem_zpowers_iff.mpr ⟨k, by rw [← hk, map_zpow, hzφ]⟩

omit [Finite G] in
theorem centralizes_map_of_fix {Q : Subgroup G} {φ : G →* G} (hzφ : φ z = z)
    (hzc : z ∈ centralizer (Q : Set G)) : z ∈ centralizer ((Q.map φ : Subgroup G) : Set G) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨a, ha, rfl⟩
  have h := mem_centralizer_iff.mp hzc a ha
  calc φ a * z = φ a * φ z := by rw [hzφ]
    _ = φ (a * z) := (map_mul φ a z).symm
    _ = φ (z * a) := by rw [h]
    _ = z * φ a := by rw [map_mul, hzφ]

theorem exists_T_Y (hyp : Hyp P M x z H S) (hα : HasPrimeConstraint (G := M) 3) {t : G}
    (htM : t ∈ M) (htB : t ∈ normalizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G))
    (htS : t ∈ normalizer (S : Set G)) {n : ℕ} (htn : t ^ 2 ^ n = 1) :
    ∃ T Y : Subgroup G, fusionIsSylowIn 2 T (GLBPrimeCore 3 M) ∧ S ≤ T ∧
      zpowers x ⊔ zpowers z ≤ normalizer (T : Set G) ∧ t ∈ normalizer (T : Set G) ∧
      IsPGroup 3 Y ∧ Y ≤ M ∧ zpowers x ⊔ zpowers z ≤ Y ∧ Y ≤ normalizer (T : Set G) ∧
      z ∈ centralizer (Y : Set G) ∧
      (∀ w ∈ Y, w ∈ centralizer (Y : Set G) → w ^ 3 = 1 → w ∈ zpowers z) ∧
      CFSG.Open.pRank 3 Y = 3 ∧ 27 ≤ Nat.card Y := by
  set B : Subgroup G := zpowers x ⊔ zpowers z
  set D : Subgroup G := GLBPrimeCore 3 M
  have hpl := plane_of_hyp hyp
  have hB3 := isPGroup_B hyp
  have hPM := P_le_M hyp
  have hBP := B_le_P hyp
  have hD3 : ¬ 3 ∣ Nat.card D := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
    (CFSG.AGLEmbedding.glbPrimeCore_coprime 3 M)
  have hBD : B ≤ normalizer (D : Set G) :=
    (hBP.trans hPM).trans (CFSG.AGLEmbedding.le_normalizer_glbPrimeCore 3 M)
  have hPD : (P : Subgroup G) ≤ normalizer (D : Set G) :=
    hPM.trans (CFSG.AGLEmbedding.le_normalizer_glbPrimeCore 3 M)
  have htD : t ∈ normalizer (D : Set G) := CFSG.AGLEmbedding.le_normalizer_glbPrimeCore 3 M htM
  obtain ⟨T, hTsyl, hST, hBT, htT⟩ := exists_sylow_two_invariant_containing hB3 hD3 hBD htD htB
    htn (S_le_glbPrimeCore hyp hα) (isPGroup_S hyp) (B_le_normalizer_S hyp) htS
  have hbot2 : IsPGroup 2 (⊥ : Subgroup G) := IsPGroup.of_card (n := 0) (by simp)
  have hPbot : (P : Subgroup G) ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  obtain ⟨T', hT'syl, -, hPT'⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two P.isPGroup' hD3 hPD bot_le hbot2 hPbot
  obtain ⟨c, hc, hTc⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows
    Nat.prime_three Nat.prime_two hB3 hD3 hBD hT'syl hTsyl (hBP.trans hPT') hBT
  have hcM : c ∈ M := CFSG.AGLEmbedding.glbPrimeCore_le 3 M (mem_inf.mp hc).1
  have hcB : c ∈ centralizer (B : Set G) := (mem_inf.mp hc).2
  have hcz : z * c = c * z := mem_centralizer_iff.mp hcB z (mem_sup_right (mem_zpowers z))
  have hzφ : (MulAut.conj c).toMonoidHom z = z := by
    change c * z * c⁻¹ = z
    rw [← hcz, mul_inv_cancel_right]
  set Y : Subgroup G := (P : Subgroup G).map (MulAut.conj c).toMonoidHom
  have hYT : Y ≤ normalizer (T : Set G) := by
    rw [hTc, ← Subgroup.map_equiv_normalizer_eq]
    exact map_mono hPT'
  have hBY : B ≤ Y := by
    intro β hβ
    have hβc : β * c = c * β := mem_centralizer_iff.mp hcB β hβ
    refine ⟨β, hBP hβ, ?_⟩
    change c * β * c⁻¹ = β
    rw [← hβc, mul_inv_cancel_right]
  have hYM : Y ≤ M := by
    rintro _ ⟨a, ha, rfl⟩
    exact M.mul_mem (M.mul_mem hcM (hPM ha)) (M.inv_mem hcM)
  have hY3 : CFSG.Open.pRank 3 Y = 3 := by
    rw [pRank_map_automorphism 3 Nat.prime_three.one_lt]
    exact pRank_P hyp
  have hY27 : 27 ≤ Nat.card Y := by
    obtain ⟨E, hEY, -, hEc⟩ := pRank_attained 3 Y (by omega)
    rw [hY3] at hEc
    exact (show 27 = 3 ^ 3 by norm_num) ▸ hEc ▸ Subgroup.card_le_of_le hEY
  exact ⟨T, Y, hTsyl, hST, hBT, htT, P.isPGroup'.map _, hYM, hBY, hYT,
    centralizes_map_of_fix hzφ hyp.central.centralizes,
    center_map_of_fix (MulAut.conj c).injective hzφ hpl.center, hY3, hY27⟩

theorem x_not_mem_zpowers_z (hyp : Hyp P M x z H S) : x ∉ zpowers z := by
  intro hx
  have hle : zpowers x ⊔ zpowers z ≤ zpowers z := sup_le (zpowers_le.2 hx) le_rfl
  have h1 := card_le_of_le hle
  rw [(plane_of_hyp hyp).card_eq, Nat.card_zpowers,
    orderOf_eq_prime (hp := ⟨Nat.prime_three⟩) hyp.central.pow_eq_one hyp.central.ne_one] at h1
  omega

theorem false_of_elemAbelian_le_normalizer (hyp : Hyp P M x z H S)
    (hα : HasPrimeConstraint (G := M) 3) {E : Subgroup G}
    (hEB : E ≤ normalizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G))
    (hE : IsElemAbelian 3 E) (hE27 : Nat.card E = 27) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set B : Subgroup G := zpowers x ⊔ zpowers z
  have hpl := plane_of_hyp hyp
  have hsetup : Setup65A G P M x z :=
    ⟨hyp.setting, hyp.u0, hyp.situation, hα, hyp.point, hyp.central⟩
  have hxB : x ∈ B := mem_sup_left (mem_zpowers x)
  have hCx : CFSG.Open.pRank 3 (centralizer ({x} : Set G)) ≤ 2 :=
    pRank_centralizer_le_two_of_mem_plane hsetup hxB (x_not_mem_zpowers_z hyp)
  have hx3 : x ^ 3 = 1 := hyp.point.pow_eq_one
  have hx1 : x ≠ 1 := hyp.point.ne_one
  have hA : ∀ e ∈ E, e * x * e⁻¹ ∈ (B : Set G) \ {1} := fun e he =>
    ⟨(mem_normalizer_iff.1 (hEB he) x).1 hxB, fun h1 => hx1 (conj_eq_one_iff.1 h1)⟩
  have hcardA : Nat.card ↥((B : Set G) \ {1}) = 8 := by
    rw [Nat.card_coe_set_eq, Set.ncard_diff_singleton_of_mem (one_mem B), ← Nat.card_coe_set_eq]
    change Nat.card ↥B - 1 = 8
    rw [hpl.card_eq]
    norm_num
  have hr8 := (relIndex_centralizer_le_card_of_conj_mem E x _ hA).trans hcardA.le
  have hmul := relIndex_mul_card (centralizer ({x} : Set G)) E
  rw [hE27] at hmul
  have hr27 : (centralizer ({x} : Set G)).relIndex E ∣ 27 := Dvd.intro _ hmul
  have hr3 : (centralizer ({x} : Set G)).relIndex E ≤ 3 := by
    have h27 : (27 : ℕ) = 3 ^ 3 := by norm_num
    rw [h27] at hr27
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hr27
    rw [hj'] at hr8 ⊢
    interval_cases j
    · norm_num
    · norm_num
    · norm_num at hr8
    · norm_num at hr8
  have hC9 : 9 ≤ Nat.card ↥(centralizer ({x} : Set G) ⊓ E) := by
    by_contra hlt
    push Not at hlt
    have : (centralizer ({x} : Set G)).relIndex E * Nat.card ↥(centralizer ({x} : Set G) ⊓ E) <
        3 * 9 := Nat.mul_lt_mul_of_le_of_lt hr3 hlt (by norm_num)
    omega
  set E' := centralizer ({x} : Set G) ⊓ E
  have hE' : IsElemAbelian 3 E' := ⟨⟨⟨fun a b => Subtype.ext (by
      have := hE.1.is_comm.comm ⟨a, (mem_inf.1 a.2).2⟩ ⟨b, (mem_inf.1 b.2).2⟩
      simpa using congrArg Subtype.val this)⟩⟩, fun a ha => hE.2 a (mem_inf.1 ha).2⟩
  have hxE' : zpowers x ≤ centralizer (E' : Set G) := by
    rw [zpowers_le, mem_centralizer_iff]
    intro e he
    exact mem_centralizer_singleton_iff.1 (mem_inf.1 he).1
  have hF : IsElemAbelian 3 (E' ⊔ zpowers x) := by
    have i1 : CFSG.IsElementaryAbelian 3 E' :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E').2 hE'
    have i2 : CFSG.IsElementaryAbelian 3 (zpowers x) :=
      CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hx3
    exact (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).1
      (CFSG.IsElementaryAbelian.sup_of_le_centralizer hxE')
  have hFC : E' ⊔ zpowers x ≤ centralizer ({x} : Set G) :=
    sup_le inf_le_left (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
  have hF27 : 3 ^ 3 ≤ Nat.card ↥(E' ⊔ zpowers x) := by
    by_cases hxE : x ∈ E'
    ·
      have hEE : E ≤ E' := by
        intro e he
        refine mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_, he⟩
        have := hE.1.is_comm.comm ⟨e, he⟩ ⟨x, (mem_inf.1 hxE).2⟩
        simpa using congrArg Subtype.val this
      have := card_le_of_le (hEE.trans (le_sup_left : E' ≤ E' ⊔ zpowers x))
      rw [hE27] at this
      norm_num
      exact this
    · rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three E' hx3 hxE
        (fun e he => mem_centralizer_singleton_iff.1 (mem_inf.1 he).1)]
      norm_num
      omega
  have := CFSG.LocalAnalysis.RankFourTheoremC.le_pRank_of_isElemAbelian Nat.prime_three hFC hF hF27
  omega

theorem normalizer_le_normalizer_B (hyp : Hyp P M x z H S) {Q₀ : Subgroup G}
    (hBQ : zpowers x ⊔ zpowers z ≤ Q₀)
    (hQ : ∀ q ∈ Q₀, q ^ 3 = 1 → q ∈ zpowers x ⊔ zpowers z) :
    normalizer (Q₀ : Set G) ≤ normalizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) := by
  have hpl := plane_of_hyp hyp
  have key : ∀ g ∈ normalizer (Q₀ : Set G), ∀ β ∈ zpowers x ⊔ zpowers z,
      g * β * g⁻¹ ∈ zpowers x ⊔ zpowers z := by
    intro g hg β hβ
    refine hQ _ ((mem_normalizer_iff.1 hg β).1 (hBQ hβ)) ?_
    rw [conj_pow, hpl.isElemAbelian.2 β hβ]
    group
  intro g hg
  rw [mem_normalizer_iff]
  intro β
  refine ⟨key g hg β, fun hβ => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hβ
  simpa [mul_assoc] using this

theorem exists_three_of_le_normalizer (hyp : Hyp P M x z H S)
    (hα : HasPrimeConstraint (G := M) 3) {Y Q₀ : Subgroup G} (hY3 : CFSG.Open.pRank 3 Y = 3)
    (hBQ : zpowers x ⊔ zpowers z ≤ Q₀) (hYQ : Y ≤ normalizer (Q₀ : Set G)) :
    ∃ q ∈ Q₀, q ^ 3 = 1 ∧ q ∉ zpowers x ⊔ zpowers z := by
  by_contra hcon
  push Not at hcon
  have hYB := hYQ.trans (normalizer_le_normalizer_B hyp hBQ hcon)
  obtain ⟨E, hEY, hE, hEc⟩ := pRank_attained 3 Y (by omega)
  rw [hY3] at hEc
  exact false_of_elemAbelian_le_normalizer hyp hα (hEY.trans hYB) hE (by rw [hEc]; norm_num)

theorem exists_three_normalizer (hyp : Hyp P M x z H S) (hα : HasPrimeConstraint (G := M) 3)
    {Y : Subgroup G} (hY : IsPGroup 3 Y) (hY3 : CFSG.Open.pRank 3 Y = 3)
    (hBY : zpowers x ⊔ zpowers z ≤ Y) :
    ∃ q ∈ Y ⊓ normalizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G), q ^ 3 = 1 ∧
      q ∉ zpowers x ⊔ zpowers z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q₀ := Y ⊓ normalizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G)
  by_contra hcon
  push Not at hcon
  have hBQ : zpowers x ⊔ zpowers z ≤ Q₀ := le_inf hBY le_normalizer
  have hNQ := normalizer_le_normalizer_B hyp hBQ hcon
  have hQY : Q₀ = Y := by
    by_contra hne
    obtain ⟨y, hyY, hyN, hyQ⟩ :=
      exists_mem_normalizer_not_mem_of_lt hY (lt_of_le_of_ne inf_le_left hne)
    exact hyQ ⟨hyY, hNQ hyN⟩
  obtain ⟨E, hEY, hE, hEc⟩ := pRank_attained 3 Y (by omega)
  rw [hY3] at hEc
  exact false_of_elemAbelian_le_normalizer hyp hα (hEY.trans (hQY ▸ inf_le_right)) hE
    (by rw [hEc]; norm_num)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614I
