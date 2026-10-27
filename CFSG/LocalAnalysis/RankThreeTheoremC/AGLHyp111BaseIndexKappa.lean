module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111OneSmallKappa
import CFSG.Goldschmidt.Steps.Sec82e
import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111FactorAtBase
import CFSG.LocalAnalysis.RankThreeTheoremC.D1BlockPushUp
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericFrobenius
import CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6CentralizingBase

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_maxPSubgroup_of_normalizer_le {p : ℕ} [Fact p.Prime] {Q N M : Subgroup G}
    (hQ : IsPGroup p Q) (hQN : Q ≤ N) (hQM : Q ≤ M)
    (hNorm : ∀ U : Subgroup G, Q ≤ U → U ≤ M → IsPGroup p U →
      Subgroup.normalizer (U : Set G) ≤ M) :
    ∃ T : Subgroup G, Q ≤ T ∧ T ≤ N ∧ T ≤ M ∧ IsPGroup p T ∧
      ∀ V : Subgroup G, V ≤ N → IsPGroup p V → T ≤ V → V = T := by
  classical
  set s : Set (Subgroup G) := {U | Q ≤ U ∧ U ≤ N ∧ U ≤ M ∧ IsPGroup p U} with hs
  obtain ⟨T, ⟨hQT, hTN, hTM, hT⟩, hmax⟩ :=
    Set.exists_max_image s (fun U : Subgroup G => Nat.card U) (Set.toFinite s)
      ⟨Q, le_rfl, hQN, hQM, hQ⟩
  refine ⟨T, hQT, hTN, hTM, hT, fun V hVN hV hTV => ?_⟩
  by_contra hVT
  have hlt : T.subgroupOf V ≠ ⊤ := by
    intro htop
    exact hVT (le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hTV)
  have : Group.IsNilpotent V := hV.isNilpotent
  obtain ⟨x, hxN, hxT⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (T.subgroupOf V) (lt_top_iff_ne_top.mpr hlt))
  have hmapT : (T.subgroupOf V).map V.subtype = T := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTV]
  have hxN' : (x : G) ∈ Subgroup.normalizer (T : Set G) := by
    have := Subgroup.le_normalizer_map V.subtype ⟨x, hxN, rfl⟩
    rwa [hmapT] at this
  set W := V ⊓ Subgroup.normalizer (T : Set G) with hW
  have hWs : W ∈ s := ⟨hQT.trans (le_inf hTV Subgroup.le_normalizer), inf_le_left.trans hVN,
    inf_le_right.trans (hNorm T hQT hTM hT), hV.to_le inf_le_left⟩
  have hTW : T ≤ W := le_inf hTV Subgroup.le_normalizer
  have hWT : W = T :=
    (Subgroup.eq_of_le_of_card_ge hTW (hmax W hWs)).symm
  have hxW : (x : G) ∈ W := ⟨x.2, hxN'⟩
  rw [hWT] at hxW
  exact hxT hxW

theorem exists_conj_le {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M U : Subgroup G}
    (hPM : (P : Subgroup G) ≤ M) (hU : IsPGroup p U) (hUM : U ≤ M) :
    ∃ m ∈ M, U ≤ (P : Subgroup G).map (MulAut.conj m).toMonoidHom := by
  classical
  obtain ⟨S, hS⟩ := (hU.comap_subtype (K := M)).exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M (P.subtype hPM) S
  refine ⟨m, m.2, fun t ht => ?_⟩
  have h1 : (⟨t, hUM ht⟩ : M) ∈ (S : Subgroup M) := hS (Subgroup.mem_subgroupOf.mpr ht)
  rw [← hm, Sylow.coe_subgroup_smul, Sylow.coe_subtype,
    Subgroup.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨y, hy, hyt⟩ := h1
  refine ⟨y, Subgroup.mem_subgroupOf.mp hy, ?_⟩
  have := congrArg Subtype.val hyt
  simpa [MulAut.smul_def, MulAut.conj_apply] using this

def omegaOneCenter (p : ℕ) (U : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ U ∧ (∀ u ∈ U, u * x = x * u) ∧ x ^ p = 1}
  one_mem' := ⟨U.one_mem, fun u _ => by simp, one_pow p⟩
  mul_mem' := by
    rintro x y ⟨hx, hxc, hxp⟩ ⟨hy, hyc, hyp⟩
    refine ⟨U.mul_mem hx hy, fun u hu => ?_, ?_⟩
    · rw [← mul_assoc, hxc u hu, mul_assoc, hyc u hu, mul_assoc]
    · rw [(Commute.mul_pow (hyc x hx) p), hxp, hyp, one_mul]
  inv_mem' := by
    rintro x ⟨hx, hxc, hxp⟩
    refine ⟨U.inv_mem hx, fun u hu => ?_, by rw [inv_pow, hxp, inv_one]⟩
    have := hxc u hu
    calc u * x⁻¹ = x⁻¹ * (x * u) * x⁻¹ := by group
      _ = x⁻¹ * (u * x) * x⁻¹ := by rw [this]
      _ = x⁻¹ * u := by group

theorem normalizer_le_normalizer_omegaOneCenter (p : ℕ) (U : Subgroup G) :
    Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (omegaOneCenter p U : Set G) := by
  intro g hg
  apply Subgroup.mem_normalizer_fintype
  rintro x ⟨hx, hxc, hxp⟩
  have hgU := Subgroup.mem_normalizer_iff.mp hg
  refine ⟨(hgU x).mp hx, fun u hu => ?_, by rw [conj_pow, hxp]; group⟩
  have hu' : g⁻¹ * u * g ∈ U := by
    have := (hgU (g⁻¹ * u * g)).mpr (by simpa [mul_assoc] using hu)
    exact this
  have h := hxc _ hu'
  calc u * (g * x * g⁻¹) = g * ((g⁻¹ * u * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * u * g)) * g⁻¹ := by rw [h]
    _ = g * x * g⁻¹ * u := by group

theorem normalizer_le_of_isAGLQ {p : ℕ} {P : Sylow p G} {M H R U : Subgroup G}
    (hext : D1Extremal p P M H R) (hU : IsAGLQ p M U) :
    Subgroup.normalizer (U : Set G) ≤ M := by
  classical
  have hp := hext.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hUM, hUp, hU3⟩ := hU
  have rank3 : 3 ≤ Open.pRank p U → Subgroup.normalizer (U : Set G) ≤ M := by
    intro h3
    obtain ⟨m, hm, hUP⟩ := exists_conj_le hext.sylow_le hUp hUM
    exact (normalizer_le_weakCore p hUP (by omega)
      (h3.trans (CFSG.SectionRank.pRank_mono hp.one_lt le_sup_left))).trans
      (weakCore_conj_le hp hext.weakCore_le hm)
  by_cases h3 : 3 ≤ Open.pRank p U
  · exact rank3 h3
  rcases hU3 with h | ⟨E, hEU, hEab, hEc, hΓ⟩
  · exact absurd (by rwa [CFSG.SectionRank.pRank_coe_eq_openPRank] at h) h3
  set F := omegaOneCenter p U with hF
  have hFE : F ≤ E := by
    rintro x ⟨hx, hxc, hxp⟩
    by_contra hxE
    obtain ⟨hab, hcard⟩ := CFSG.Goldschmidt.Sec82.isElemAbelian_sup_zpowers hp hEc hEab.2 hxp hxE
      (fun e he => hxc e (hEU he))
    exact h3 (le_csSup (pRank_bddAbove p hp U)
      ⟨_, sup_le hEU ((Subgroup.zpowers_le).mpr hx), hab, hcard⟩)
  have : Nontrivial U := by
    have h1 : 1 < Nat.card U := by
      have := Subgroup.card_le_of_le hEU
      have hp2 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
      omega
    exact Finite.one_lt_card_iff_nontrivial.mp h1
  have := hUp.center_nontrivial
  obtain ⟨n, hn, hcn⟩ := (hUp.to_subgroup (Subgroup.center U)).nontrivial_iff_card.mp inferInstance
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p (G := Subgroup.center U)
    (by rw [hcn]; exact dvd_pow_self p hn.ne')
  set x : G := ((z : U) : G) with hx
  have hxF : x ∈ F := by
    refine ⟨(z : U).2, fun u hu => ?_, ?_⟩
    · have := Subgroup.mem_center_iff.mp z.2 ⟨u, hu⟩
      exact congrArg Subtype.val this
    · have : z ^ p = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
      have := congrArg (fun w : Subgroup.center U => ((w : U) : G)) this
      simpa [hx] using this
  have hx1 : x ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext (Subtype.ext (by simpa [hx] using h))
    rw [this, orderOf_one] at hz
    exact hp.one_lt.ne hz
  have hF1 : 1 ≤ Open.pRank p F := by
    have hxp : x ^ p = 1 := hxF.2.2
    refine le_csSup (pRank_bddAbove p hp F) ⟨Subgroup.zpowers x, (Subgroup.zpowers_le).mpr hxF,
      ⟨inferInstance, fun y hy => ?_⟩, ?_⟩
    · obtain ⟨k, rfl⟩ := hy
      simp only
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
    · rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1, pow_one]
  exact (normalizer_le_normalizer_omegaOneCenter p U).trans
    ((le_sSup ⟨F, hFE, hF1, rfl⟩ : Subgroup.normalizer (F : Set G) ≤ GLBCore p 1 E).trans hΓ)

theorem isAGLQ_of_le {p : ℕ} [Fact p.Prime] {M B U : Subgroup G} (hB : IsAGLQ p M B)
    (hBU : B ≤ U) (hUM : U ≤ M) (hU : IsPGroup p U) : IsAGLQ p M U := by
  obtain ⟨-, -, h | ⟨E, hEB, hE⟩⟩ := hB
  · refine ⟨hUM, hU, Or.inl ?_⟩
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at h ⊢
    exact h.trans (CFSG.SectionRank.pRank_mono (Fact.out : p.Prime).one_lt hBU)
  · exact ⟨hUM, hU, Or.inr ⟨E, hEB.trans hBU, hE⟩⟩

theorem card_le_of_ne_of_index {p : ℕ} [hp : Fact p.Prime] {Q T R : Subgroup G}
    (hT : IsPGroup p T) (hQT : Q ≤ T) (hne : T ≠ Q) (hidx : Nat.card R = p * Nat.card Q) :
    Nat.card R ≤ Nat.card T := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (hT.to_le hQT)
  have hlt : Nat.card Q < Nat.card T := by
    rcases (Subgroup.card_le_of_le hQT).lt_or_eq with h | h
    · exact h
    · exact absurd (Subgroup.eq_of_le_of_card_ge hQT h.symm.le).symm hne
  rw [hn, ha] at hlt
  have han : a < n := (Nat.pow_lt_pow_iff_right hp.out.one_lt).mp hlt
  rw [hidx, ha, hn, ← pow_succ']
  exact Nat.pow_le_pow_right hp.out.pos han

theorem exists_d1Extremal_of_maxPSubgroup {p : ℕ} {P : Sylow p G} {M H R N T : Subgroup G}
    (hext : D1Extremal p P M H R) (hN : GLBIsMaxTwoLocal N) (hNM : ¬ N ≤ M) (hTN : T ≤ N)
    (hTM : T ≤ M) (hT : IsPGroup p T)
    (hmax : ∀ V : Subgroup G, V ≤ N → IsPGroup p V → T ≤ V → V = T)
    (hcard : Nat.card R ≤ Nat.card T) (h3 : 3 ≤ Open.pRank p T)
    (hrk : Open.pRank p R ≤ Open.pRank p T) :
    ∃ P' : Sylow p G, D1Extremal p P' M N T := by
  classical
  have hp := hext.prime
  have : Fact p.Prime := ⟨hp⟩
  have hPM : (P : Subgroup G) ≤ M := hext.sylow_le
  obtain ⟨S, hS⟩ := (hT.comap_subtype (K := M)).exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M (P.subtype hPM) S
  set P' : Sylow p G := (m : G) • P with hP'
  have hP'coe : (P' : Subgroup G) = (P : Subgroup G).map (MulAut.conj (m : G)).toMonoidHom := by
    ext x
    rw [hP', Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    rfl
  have hP'M : (P' : Subgroup G) ≤ M := by
    rw [hP'coe]
    rintro _ ⟨y, hy, rfl⟩
    exact M.mul_mem (M.mul_mem m.2 (hPM hy)) (M.inv_mem m.2)
  have hTP' : T ≤ P' := by
    intro t ht
    have h1 : (⟨t, hTM ht⟩ : M) ∈ (S : Subgroup M) := hS (Subgroup.mem_subgroupOf.mpr ht)
    rw [← hm, Sylow.coe_subgroup_smul, Sylow.coe_subtype,
      Subgroup.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨y, hy, hyt⟩ := h1
    rw [hP'coe]
    refine ⟨y, Subgroup.mem_subgroupOf.mp hy, ?_⟩
    have := congrArg Subtype.val hyt
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  have hW : GLBWeakCore p (P' : Subgroup G) ≤ M := by
    rw [hP'coe]; exact weakCore_conj_le hp hext.weakCore_le m.2
  let T₀ : Sylow p N :=
    { toSubgroup := T.subgroupOf N
      isPGroup' := hT.comap_subtype
      is_maximal' := by
        intro Q hQ hle
        have hV := hmax (Q.map N.subtype) (Subgroup.map_subtype_le _) (hQ.map _) (by
          intro t ht
          exact ⟨⟨t, hTN ht⟩, hle (Subgroup.mem_subgroupOf.mpr ht), rfl⟩)
        rw [← hV]
        exact (Subgroup.comap_map_eq_self_of_injective N.subtype_injective Q).symm }
  have hT₀ : (T₀ : Subgroup N).map N.subtype = T := by
    show (T.subgroupOf N).map N.subtype = T
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTN]
  exact ⟨P',
    { prime := hp
      ne_two := hext.ne_two
      sylow_le := hP'M
      weakCore_le := hW
      maxTwoLocal_M := hext.maxTwoLocal_M
      maxTwoLocal_H := hN
      le_H := hTN
      le_P := hTP'
      isSylow := ⟨T₀, hT₀⟩
      three_le_pRank := h3
      not_le := hNM
      extremal := fun H' hH' hH'M h3' X hX hXp =>
        (hext.extremal H' hH' hH'M h3' X hX hXp).trans hcard
      extremal3 := fun H' hH' hH'M h3' X hX hXp hXT => by
        have h1 := hext.extremal H' hH' hH'M h3' X hX hXp
        have hXR : Nat.card X = Nat.card R := le_antisymm h1 (hXT ▸ hcard)
        exact (hext.extremal3 H' hH' hH'M h3' X hX hXp hXR).trans hrk }⟩

theorem false_of_extremal_kappa_stepP {p : ℕ} {M : Subgroup G}
    (step : ∀ (P : Sylow p G) (H R : Subgroup G), D1Extremal p P M H R →
      (∀ (P' : Sylow p G) (N R' : Subgroup G), D1Extremal p P' M N R' →
        d1Kappa p M H < d1Kappa p M N → False) → False) :
    ∀ (P : Sylow p G) (H R : Subgroup G), D1Extremal p P M H R → False := by
  intro P H R hHR
  refine false_of_kappa_step (α := Sylow p G × Subgroup G × Subgroup G)
    (fun a => D1Extremal p a.1 M a.2.1 a.2.2) (fun a => d1Kappa p M a.2.1) (Nat.card G)
    (fun a _ => d1Kappa_le_card p M a.2.1) (fun a ha hih => ?_) (P, H, R) hHR
  exact step a.1 a.2.1 a.2.2 ha fun P' N R' hN hlt => hih (P', N, R') hN hlt

theorem kappa_le_or_of_base {p : ℕ} {P : Sylow p G} {M H R H₀ : Subgroup G}
    (hih : ∀ (P' : Sylow p G) (N R' : Subgroup G), D1Extremal p P' M N R' →
      d1Kappa p M H₀ < d1Kappa p M N → False)
    (hk : d1Kappa p M H₀ ≤ d1Kappa p M H) (hext : D1Extremal p P M H R) {B : Subgroup G}
    (hBR : B ≤ R) (hidx : Nat.card R = p * Nat.card B)
    (hNorm : ∀ U : Subgroup G, B ≤ U → U ≤ M → IsPGroup p U →
      Subgroup.normalizer (U : Set G) ≤ M)
    (hR3 : Open.pRank p R ≤ 3) {N : Subgroup G} (hN : GLBIsMaxTwoLocal N) (hNM : ¬ N ≤ M)
    (hBN : B ≤ N) :
    ∃ T : Subgroup G, B ≤ T ∧ T ≤ N ∧ T ≤ M ∧ IsPGroup p T ∧
      (∀ V : Subgroup G, V ≤ N → IsPGroup p V → T ≤ V → V = T) ∧
      (T = B ∨ Open.pRank p T ≤ 2 ∨ d1Kappa p M N ≤ d1Kappa p M H) := by
  have : Fact p.Prime := ⟨hext.prime⟩
  have hB : IsPGroup p B := hext.isPGroup.to_le hBR
  obtain ⟨T, hBT, hTN, hTM, hT, hmax⟩ :=
    exists_maxPSubgroup_of_normalizer_le hB hBN (hBR.trans hext.le_M) hNorm
  refine ⟨T, hBT, hTN, hTM, hT, hmax, ?_⟩
  by_cases hTB : T = B
  · exact Or.inl hTB
  by_cases h2 : Open.pRank p T ≤ 2
  · exact Or.inr (Or.inl h2)
  push Not at h2
  obtain ⟨P', hP'⟩ := exists_d1Extremal_of_maxPSubgroup hext hN hNM hTN hTM hT hmax
    (card_le_of_ne_of_index hT hBT hTB hidx) h2 (hR3.trans h2)
  refine Or.inr (Or.inr ?_)
  by_contra hlt
  exact hih P' N T hP' (lt_of_le_of_lt hk (not_le.mp hlt))

theorem factorAt_base_of_ih {p : ℕ} {P : Sylow p G} {M H R H₀ : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hih : ∀ (P' : Sylow p G) (N R' : Subgroup G), D1Extremal p P' M N R' →
      d1Kappa p M H₀ < d1Kappa p M N → False)
    (hk : d1Kappa p M H₀ ≤ d1Kappa p M H) (hext : D1Extremal p P M H R) {B : Subgroup G}
    (hBR : B ≤ R) (hidx : Nat.card R = p * Nat.card B)
    (hNorm : ∀ U : Subgroup G, B ≤ U → U ≤ M → IsPGroup p U →
      Subgroup.normalizer (U : Set G) ≤ M)
    (hR3 : Open.pRank p R ≤ 3) (h917 : Hyp917R p M H B K)
    (hrank2 : ∀ N T : Subgroup G, GLBIsMaxTwoLocal N → ¬ N ≤ M → B ≤ N → AGLCovers p H N K →
      B ≤ T → T ≤ N → T ≤ M → IsPGroup p T →
      (∀ V : Subgroup G, V ≤ N → IsPGroup p V → T ≤ V → V = T) → (T = B ∨ Open.pRank p T ≤ 2) →
      ∀ x ∈ N, ∃ m ∈ N ⊓ M, ∃ y ∈ H ⊓ N, x = m * y) :
    AGLCompetitorFactorAt p M H K B := by
  intro N hN hNM hBN hcov
  obtain ⟨T, hBT, hTN, hTM, hT, hmax, hor⟩ :=
    kappa_le_or_of_base hih hk hext hBR hidx hNorm hR3 hN hNM hBN
  rcases hor with h | h | h
  · exact hrank2 N T hN hNM hBN hcov hBT hTN hTM hT hmax (Or.inl h)
  · exact hrank2 N T hN hNM hBN hcov hBT hTN hTM hT hmax (Or.inr h)
  · exact (h917 N hN hNM hBN hcov).resolve_right (not_lt.mpr h)


theorem kappa_le_or_of_isAGLQ {p : ℕ} {P : Sylow p G} {M H R H₀ : Subgroup G}
    (hih : ∀ (P' : Sylow p G) (N R' : Subgroup G), D1Extremal p P' M N R' →
      d1Kappa p M H₀ < d1Kappa p M N → False)
    (hk : d1Kappa p M H₀ ≤ d1Kappa p M H) (hext : D1Extremal p P M H R) {B : Subgroup G}
    (hBQ : IsAGLQ p M B) (hBR : B ≤ R) (hidx : Nat.card R = p * Nat.card B)
    (hR3 : Open.pRank p R ≤ 3) {N : Subgroup G} (hN : GLBIsMaxTwoLocal N) (hNM : ¬ N ≤ M)
    (hBN : B ≤ N) :
    ∃ T : Subgroup G, B ≤ T ∧ T ≤ N ∧ T ≤ M ∧ IsPGroup p T ∧
      (∀ V : Subgroup G, V ≤ N → IsPGroup p V → T ≤ V → V = T) ∧
      (T = B ∨ Open.pRank p T ≤ 2 ∨ d1Kappa p M N ≤ d1Kappa p M H) := by
  have : Fact p.Prime := ⟨hext.prime⟩
  exact kappa_le_or_of_base hih hk hext hBR hidx
    (fun U hBU hUM hU => normalizer_le_of_isAGLQ hext (isAGLQ_of_le hBQ hBU hUM hU)) hR3 hN hNM hBN

@[expose] def AGLRankTwoFactorAt (p : ℕ) (M H B : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) : Prop :=
  ∀ N T : Subgroup G, GLBIsMaxTwoLocal N → ¬ N ≤ M → B ≤ N → AGLCovers p H N K →
    B ≤ T → T ≤ N → T ≤ M → IsPGroup p T →
    (∀ V : Subgroup G, V ≤ N → IsPGroup p V → T ≤ V → V = T) → (T = B ∨ Open.pRank p T ≤ 2) →
    ∀ x ∈ N, ∃ m ∈ N ⊓ M, ∃ y ∈ H ⊓ N, x = m * y

theorem false_of_centralizing_base_of_factorAtB {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1PhaseThree p P M H R) (hCGT : AschbacherLocalCGTBlock) (hD2 : NoXBlockFor G)
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hKX : ¬ K ≤ d1X0 p M H)
    (hOM : (primeComplementCore (G := H) p).map H.subtype ≤ M)
    (hHfac : ∀ x ∈ H, ∃ m ∈ H ⊓ M, ∃ k : H,
      QuotientGroup.mk' (primeComplementCore (G := H) p) k ∈ K ∧ x = m * k)
    {B : Subgroup G} (hfacB : AGLCompetitorFactorAt p M H K B) (hXM : d1PlusCore p H K ≤ M)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hLn : (L.subgroupOf M).Normal)
    (hBp : IsPGroup p B) (hBH : B ≤ H) (hBM : B ≤ M)
    (hb3 : ∀ S : Subgroup G, IsPGroup 2 S → S ≤ H → B ≤ Subgroup.normalizer (S : Set G) →
      S ≤ d1PlusCore p H K)
    (hBL : ∀ b ∈ B, ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 M) : False := by
  have hM : IsTwoLocal M := h.maxTwoLocal_M.1
  have hOH : pCoreOf 2 M ≤ pCoreOf 2 H := h.toD1Escape.twoCore_M_le h.twoCore_inf
  have hHM : pCoreOf 2 H ≤ M := h.toD1Escape.twoCore_le
  have hBS : B ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    hBH.trans (localGroup_le_normalizer_pCoreOf 2 H)
  obtain ⟨RB, hSRB, hRB⟩ := TwoRest3A6.exists_isMaxInvariantTwoIn_ge
    (hb3 _ (RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H)
      (RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H) hBS)
    (RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H) hBS
  have hRBX : RB ≤ d1PlusCore p H K := hRB.1
  have hRB1 : RB ≠ ⊥ := fun h1 =>
    pCoreOf_two_ne_bot h.maxTwoLocal_H.1 (le_bot_iff.mp (h1 ▸ hSRB))
  have habs := absorbsAt_of_factorAt hM h.maxTwoLocal_H hOH hHM hOM hHfac hfacB
  obtain ⟨hCGS, hRBmax⟩ := star_of_absorbsAt_of_le_normalizer h.prime h.ne_two hBp hBH hKX habs
    hb3 hRB hRB1 hRB.2.2.1
  have hRBM : RB ≤ M := hRBX.trans hXM
  have hMn : M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.le).mp hLn
  have hRBL : RB ≤ Subgroup.normalizer (L : Set G) := hRBM.trans hMn
  have hORB : pCoreOf 2 M ≤ RB :=
    TwoRest3A6.le_of_isMaxInvariantTwo hRBmax
      (RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
      (hRBM.trans (localGroup_le_normalizer_pCoreOf 2 M))
      (hBM.trans (localGroup_le_normalizer_pCoreOf 2 M))
  have hsyl := TwoRest3A6.not_two_dvd_index_inf_of_isMaxInvariantTwo hRBmax hORB hRBL hBL
  have hloc : ∀ C : Subgroup G, C ≤ RB → C ≠ ⊥ → (C.subgroupOf RB).Characteristic →
      Subgroup.normalizer (C : Set G) ≤ H := fun C hC hC1 hCc =>
    le_trans (by
      unfold CFSG.Quasithin.CGS
      exact le_iSup_of_le C <| le_iSup_of_le hC <| le_iSup_of_le hC1 <|
        le_iSup (fun _ : (C.subgroupOf RB).Characteristic => Subgroup.normalizer (C : Set G)) hCc)
      hCGS
  have hLH : L ≤ H := le_of_normal_block_of_local h.glob hCGT hD2 h.maxTwoLocal_M h.not_le hL.le
    hLn hRBM hRBmax.1 hORB hRBL hsyl hloc
  exact hL.not_le_normalizer (hLH.trans (localGroup_le_normalizer_pCoreOf 2 H))

theorem false_of_centralizing_base_of_ih {p : ℕ} {P : Sylow p G} {M H R H₀ : Subgroup G}
    (h : D1PhaseThree p P M H R) (hext : D1Extremal p P M H R)
    (hih : ∀ (P' : Sylow p G) (N R' : Subgroup G), D1Extremal p P' M N R' →
      d1Kappa p M H₀ < d1Kappa p M N → False)
    (hk : d1Kappa p M H₀ ≤ d1Kappa p M H) (hCGT : AschbacherLocalCGTBlock)
    (hD2 : NoXBlockFor G)
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hKX : ¬ K ≤ d1X0 p M H)
    (hOM : (primeComplementCore (G := H) p).map H.subtype ≤ M)
    (hHfac : ∀ x ∈ H, ∃ m ∈ H ⊓ M, ∃ k : H,
      QuotientGroup.mk' (primeComplementCore (G := H) p) k ∈ K ∧ x = m * k)
    (hXM : d1PlusCore p H K ≤ M)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hLn : (L.subgroupOf M).Normal)
    {B : Subgroup G} (hBQ : IsAGLQ p M B) (hBR : B ≤ R) (hidx : Nat.card R = p * Nat.card B)
    (hR3 : Open.pRank p R ≤ 3) (h917 : Hyp917R p M H B K) (h2 : AGLRankTwoFactorAt p M H B K)
    (hb3 : ∀ S : Subgroup G, IsPGroup 2 S → S ≤ H → B ≤ Subgroup.normalizer (S : Set G) →
      S ≤ d1PlusCore p H K)
    (hBL : ∀ b ∈ B, ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 M) : False := by
  have : Fact p.Prime := ⟨hext.prime⟩
  have hfacB : AGLCompetitorFactorAt p M H K B :=
    factorAt_base_of_ih hih hk hext hBR hidx
      (fun U hBU hUM hU => normalizer_le_of_isAGLQ hext (isAGLQ_of_le hBQ hBU hUM hU)) hR3 h917 h2
  exact false_of_centralizing_base_of_factorAtB h hCGT hD2 hKX hOM hHfac hfacB hXM hL hLn
    hBQ.2.1 (hBR.trans hext.le_H) hBQ.1 hb3 hBL

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
