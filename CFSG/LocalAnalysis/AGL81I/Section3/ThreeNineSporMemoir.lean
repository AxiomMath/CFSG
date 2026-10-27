module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporBigOvergroup

import CFSG.GH74.GLS.Balance.Bender.Aux2
import CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.IndependentFactorRank

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporBig

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.ABGLocalTools
open CFSG.PreuniquenessRankFour CFSG.RankThreeCoreUniqueness
open CFSG.RankThreeEvenClassification
open scoped Pointwise

variable {L : Type} [Group L] [Finite L] {p d : ℕ} {Y : Subgroup L}

private theorem eb_le_y_of_data {Eb : Subgroup L} {p : ℕ} (hEb : IsElemAbelian p Eb)
    (hcent : ∀ e ∈ Eb, e ≠ 1 → Subgroup.centralizer ({e} : Set L) ≤ Y) : Eb ≤ Y := by
  intro e he
  by_cases he1 : e = 1
  · simpa [he1] using Y.one_mem
  · exact hcent e he he1 (Subgroup.mem_centralizer_singleton_iff.mpr rfl)

private theorem pRank_top_le_three_of_data (h : SporOvergroupData L p d Y) :
    CFSG.Open.pRank p (⊤ : Subgroup ↥Y) ≤ 3 := by
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) Y]
  exact (CFSG.SectionRank.pRank_mono h.prime.one_lt (le_top : Y ≤ ⊤)).trans h.rank_le

private theorem glaPPrimeCore_inf_centralizer_eq_bot_of_data (h : SporOvergroupData L p d Y)
    (hO : OPrimeCoreTrivialAt p L) {Eb : Subgroup L} (hEb : IsElemAbelian p Eb)
    (hcent : ∀ e ∈ Eb, e ≠ 1 → Subgroup.centralizer ({e} : Set L) ≤ Y) :
    ∀ e ∈ Eb, e ≠ 1 → GLAPPrimeCoreOf p Y ⊓ Subgroup.centralizer ({e} : Set L) = ⊥ := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  intro e he he1
  have hEbY : Eb ≤ Y := eb_le_y_of_data hEb hcent
  have hVleY : GLAPPrimeCoreOf p Y ≤ Y := GLAPPrimeCoreOf_le Y
  have hVnormal : (GLAPPrimeCoreOf p Y).subgroupOf Y |>.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact GLAPPrimeCoreOf_conj_mem (g : L) g.2 x hx
  have hYnormV : Y ≤ Subgroup.normalizer (GLAPPrimeCoreOf p Y : Set L) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVleY).mp hVnormal
  have hCY : Subgroup.centralizer ({(e : L)} : Set L) ≤ Y :=
    hcent (e : L) he (he1)
  have hord : orderOf (e : L) = p :=
    orderOf_eq_prime (hEb.2 (e : L) he) (he1)
  have hcop : Nat.Coprime p
      (Nat.card ↥(GLAPPrimeCoreOf p Y ⊓
        Subgroup.centralizer ({(e : L)} : Set L))) :=
    (coprime_card_GLAPPrimeCoreOf h.prime Y).coprime_dvd_right
      (Subgroup.card_dvd_of_le inf_le_left)
  have hSC : ∀ g ∈ Subgroup.centralizer ({(e : L)} : Set L),
      ∀ x ∈ GLAPPrimeCoreOf p Y ⊓ Subgroup.centralizer ({(e : L)} : Set L),
        g * x * g⁻¹ ∈ GLAPPrimeCoreOf p Y ⊓
          Subgroup.centralizer ({(e : L)} : Set L) := by
    intro g hg x hx
    refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hYnormV (hCY hg)) x).mp hx.1
    · exact (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hg) x).mp hx.2
  have hle := le_GLAPPrimeCoreOf_of_normal inf_le_right hSC hcop
  have hbot : GLAPPrimeCoreOf p (Subgroup.centralizer ({(e : L)} : Set L)) = ⊥ :=
    hO (e : L) hord
  rw [eq_bot_iff]
  intro x hx
  exact Subgroup.mem_bot.mp (hbot ▸ hle hx)

theorem gLAPPrimeCoreOf_eq_bot_of_data (h : SporOvergroupData L p d Y)
    (hO : OPrimeCoreTrivialAt p L) : GLAPPrimeCoreOf p Y = ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨Eb, hEb, hcard, hcent, hnorm⟩ := h.barE
  have hEbY : Eb ≤ Y := eb_le_y_of_data hEb hcent
  have hVleY : GLAPPrimeCoreOf p Y ≤ Y := GLAPPrimeCoreOf_le Y
  have hVnormal : (GLAPPrimeCoreOf p Y).subgroupOf Y |>.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact GLAPPrimeCoreOf_conj_mem (g : L) g.2 x hx
  have hYnormV : Y ≤ Subgroup.normalizer (GLAPPrimeCoreOf p Y : Set L) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVleY).mp hVnormal
  have hEbNormV : Eb ≤ Subgroup.normalizer (GLAPPrimeCoreOf p Y : Set L) :=
    hEbY.trans hYnormV
  have hgen := Helpers.coprime_centralizer_generation_of_plane
    p h.prime Eb (GLAPPrimeCoreOf p Y) (fun e => by
      have := hEb.2 (e : L) e.2
      exact Subtype.ext this) hcard
    (fun hdvd =>
      (h.prime.coprime_iff_not_dvd.mp (coprime_card_GLAPPrimeCoreOf h.prime Y)) hdvd)
    hEbNormV
  rw [hgen]
  refine iSup₂_eq_bot.mpr ?_
  intro e he
  exact glaPPrimeCore_inf_centralizer_eq_bot_of_data h hO hEb hcent (e : L) e.2
    (fun h => he (Subtype.ext h))

theorem exists_sylow_le_of_data (h : SporOvergroupData L p d Y) :
    ∃ Q : Sylow p L, (Q : Subgroup L) ≤ Y := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨Eb, hEb, -, -, hnorm⟩ := h.barE
  obtain ⟨Q, hEbQ⟩ := (CFSG.Open.IsElemAbelian.isPGroup hEb).exists_le_sylow
  exact ⟨Q, Subgroup.le_normalizer.trans (hnorm Q Q.isPGroup' hEbQ)⟩

theorem card_dvd_card_mulAut_of_centralizer_inf_eq_bot {J : Subgroup L} (hJY : J ≤ Y)
    (hJn : (J.subgroupOf Y).Normal) (hC : Subgroup.centralizer (J : Set L) ⊓ Y = ⊥) :
    Nat.card Y ∣ Nat.card (MulAut ↥J) := by
  have hYnormJ : Y ≤ Subgroup.normalizer (J : Set L) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJY).mp hJn
  let eJ : ↥(J.subgroupOf Y) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJY
  let rho : ↥Y →* MulAut ↥(J.subgroupOf Y) := MulAut.conjNormal
  let phi : ↥Y →* MulAut ↥J := (MulAut.congr eJ).toMonoidHom.comp rho
  have hphi_inj : Function.Injective phi := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro y hy
    rw [MonoidHom.mem_ker] at hy
    have hcongr1 : (MulAut.congr eJ) (rho y) = 1 := by
      have hphi : phi y = (MulAut.congr eJ) (rho y) := rfl
      rw [hphi] at hy
      exact hy
    have h1 : (MulAut.congr eJ) (rho y) = (MulAut.congr eJ) 1 := by
      rw [hcongr1, map_one]
    have hrho1 : rho y = 1 := (MulAut.congr eJ).injective h1
    have hfix : ∀ j : ↥J, (y : L) * (j : L) * (y : L)⁻¹ = (j : L) := by
      intro j
      let j' : ↥(J.subgroupOf Y) := ⟨⟨(j : L), hJY j.2⟩, j.2⟩
      have h := congrArg (fun f : MulAut ↥(J.subgroupOf Y) => f j') hrho1
      simp only [rho, MulAut.conjNormal_apply, MulAut.one_apply] at h
      have h2 := congrArg Subtype.val h
      have h2' : ((y : Y) * (j' : Y) * (y : Y)⁻¹ : Y) = (j' : Y) := h2
      simpa [j'] using congrArg (fun z : Y => (z : L)) h2'
    have hycent : (y : L) ∈ Subgroup.centralizer (J : Set L) := by
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have h := hfix ⟨j, hj⟩
      have hcomm : (y : L) * (j : L) = (j : L) * (y : L) := by
        calc (y : L) * (j : L) = ((y : L) * (j : L) * (y : L)⁻¹) * (y : L) := by group
          _ = (j : L) * (y : L) := by rw [h]
      exact hcomm.symm
    have hybot : (y : L) ∈ Subgroup.centralizer (J : Set L) ⊓ Y := ⟨hycent, y.2⟩
    rw [hC] at hybot
    exact Subtype.ext (Subgroup.mem_bot.mp hybot)
  have hcardrange : Nat.card ↥Y = Nat.card ↥phi.range :=
    Nat.card_congr (MonoidHom.ofInjective hphi_inj).toEquiv
  rw [hcardrange]
  exact Subgroup.card_subgroup_dvd_card phi.range

theorem pow_factorization_dvd_card_of_data (h : SporOvergroupData L p d Y) :
    p ^ (Nat.card L).factorization p ∣ Nat.card Y ∧
      d ^ (Nat.card L).factorization d ∣ Nat.card Y := by
  obtain ⟨-, -, -, hpc, -, hdc, -⟩ := coreOfData h
  exact ⟨hpc, hdc⟩

private theorem inf_sylow_normal_ne_bot {p : ℕ} [Fact p.Prime]
    {Y : Type} [Group Y] [Finite Y] {Q M : Subgroup Y}
    (hQ : IsSylowOf p Q ⊤) (hQM : Q ≤ Subgroup.normalizer (M : Set Y))
    (hMp : p ∣ Nat.card ↥M) : Q ⊓ M ≠ ⊥ := by
  have hQidx : ¬ p ∣ Q.index := by
    simpa [Subgroup.relIndex_top_right] using (isSylowOf_iff.mp hQ).2.2
  have hQsup : IsSylowOf p Q (M ⊔ Q) := by
    rw [isSylowOf_iff]
    refine ⟨le_sup_right, hQ.isPGroup, ?_⟩
    exact fun hdvd => hQidx (hdvd.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))
  have hsupNorm : M ⊔ Q ≤ Subgroup.normalizer (M : Set Y) :=
    sup_le Subgroup.le_normalizer hQM
  have hMsyl : IsSylowOf p (Q ⊓ M) M := hQsup.inf_of_le_normalizer le_sup_left hsupNorm
  have hcard : Nat.card ↥(Q ⊓ M) = p ^ (Nat.card ↥M).factorization p := hMsyl.card_eq
  have hfac : 0 < (Nat.card ↥M).factorization p :=
    (Fact.out : p.Prime).factorization_pos_of_dvd Nat.card_pos.ne' hMp
  have hdvd : p ∣ Nat.card ↥(Q ⊓ M) := by
    rw [hcard]
    exact dvd_pow_self p hfac.ne'
  intro hbot
  rw [hbot, Subgroup.card_bot] at hdvd
  exact (Fact.out : p.Prime).not_dvd_one hdvd

private theorem center_sylow_le_of_le_normalizer {p : ℕ} [Fact p.Prime]
    {Y : Type} [Group Y] [Finite Y] {Q M : Subgroup Y}
    (hQ : IsSylowOf p Q ⊤) (hQM : Q ≤ Subgroup.normalizer (M : Set Y))
    (hMp : p ∣ Nat.card ↥M) (hZcard : Nat.card ↥(Subgroup.center ↥Q) = p) :
    (Subgroup.center ↥Q).map Q.subtype ≤ M := by
  have hne : Q ⊓ M ≠ ⊥ := inf_sylow_normal_ne_bot hQ hQM hMp
  have hQnorm : Q ≤ Subgroup.normalizer (Q ⊓ M : Set Y) :=
    (le_inf Subgroup.le_normalizer hQM).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := Q) (K := M))
  have hIntNormal : ((Q ⊓ M).subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hQnorm
  have hneSub : ((Q ⊓ M).subgroupOf Q) ≠ ⊥ := by
    intro hbot
    apply hne
    have hmap := congrArg (Subgroup.map Q.subtype) hbot
    rwa [Subgroup.map_subgroupOf_eq_of_le inf_le_left, Subgroup.map_bot] at hmap
  have hZmeet : ((Q ⊓ M).subgroupOf Q) ⊓ Subgroup.center ↥Q ≠ ⊥ := by
    haveI : ((Q ⊓ M).subgroupOf Q).Normal := hIntNormal
    exact CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter.inf_center_ne_bot
      hQ.isPGroup ((Q ⊓ M).subgroupOf Q) hneSub
  have hcardMeet : Nat.card ↥(((Q ⊓ M).subgroupOf Q) ⊓ Subgroup.center ↥Q) = p := by
    have hdvdZ : Nat.card ↥(((Q ⊓ M).subgroupOf Q) ⊓ Subgroup.center ↥Q) ∣ p := by
      have := Subgroup.card_dvd_of_le (inf_le_right :
        ((Q ⊓ M).subgroupOf Q) ⊓ Subgroup.center ↥Q ≤ Subgroup.center ↥Q)
      rwa [hZcard] at this
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvdZ with h1 | hp
    · exact absurd (Subgroup.card_eq_one.mp h1) hZmeet
    · exact hp
  have hinterEq : ((Q ⊓ M).subgroupOf Q) ⊓ Subgroup.center ↥Q = Subgroup.center ↥Q :=
    Subgroup.eq_of_le_of_card_ge
      (H := ((Q ⊓ M).subgroupOf Q) ⊓ Subgroup.center ↥Q)
      (K := Subgroup.center ↥Q) inf_le_right (by rw [hcardMeet, hZcard])
  have hcenterLe : Subgroup.center ↥Q ≤ ((Q ⊓ M).subgroupOf Q) := hinterEq ▸ inf_le_left
  have hmap := Subgroup.map_mono (f := Q.subtype) hcenterLe
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left] at hmap
  exact hmap.trans inf_le_right

private theorem sylow_center_data {L : Type} [Group L] [Finite L] {p d : ℕ} {Y : Subgroup L}
    (h : SporOvergroupData L p d Y)
    (hZ : ∀ Q : Sylow p L, Nat.card (Subgroup.center ↥(Q : Subgroup L)) = p) :
    ∃ QY : Sylow p Y,
      CFSG.ABGLocalTools.IsSylowOf p (QY : Subgroup Y) ⊤ ∧
        Nat.card (Subgroup.center ↥(QY : Subgroup Y)) = p := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨Eb, hEb, -, -, hnorm⟩ := h.barE
  obtain ⟨Q, hEbQ⟩ := (CFSG.Open.IsElemAbelian.isPGroup hEb).exists_le_sylow
  have hQleY : (Q : Subgroup L) ≤ Y :=
    Subgroup.le_normalizer.trans (hnorm Q Q.isPGroup' hEbQ)
  have hQY_syl : CFSG.ABGLocalTools.IsSylowOf p (Q : Subgroup L) Y := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hQleY, Q.isPGroup', ?_⟩
    exact fun hdvd => Q.not_dvd_index
      (hdvd.trans (Subgroup.relIndex_dvd_index_of_le hQleY))
  obtain ⟨QY, hQY⟩ := hQY_syl.exists_sylow_eq_subgroupOf
  have hQYtop : CFSG.ABGLocalTools.IsSylowOf p (QY : Subgroup Y) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, QY.isPGroup', by rw [Subgroup.relIndex_top_right]; exact QY.not_dvd_index⟩
  have e : ↥(QY : Subgroup Y) ≃* ↥(Q : Subgroup L) :=
    (MulEquiv.subgroupCongr hQY).trans (Subgroup.subgroupOfEquivOfLe hQleY)
  have hZcard : Nat.card (Subgroup.center ↥(QY : Subgroup Y)) = p := by
    have hmap := Subgroup.map_center_eq e
    have hcard := congrArg (fun H : Subgroup ↥(Q : Subgroup L) => Nat.card ↥H) hmap
    rw [Subgroup.card_map_of_injective e.injective] at hcard
    exact hcard.trans (hZ Q)
  exact ⟨QY, hQYtop, hZcard⟩

private theorem y_ne_bot_of_data (h : SporOvergroupData L p d Y) : Y ≠ ⊥ := by
  obtain ⟨Eb, hEb, hcardEb, hcent, hnormEb⟩ := h.barE
  have hEbY : Eb ≤ Y := eb_le_y_of_data hEb hcent
  intro hYbot
  have hEbEq : Eb = ⊥ := le_bot_iff.mp (hYbot ▸ hEbY)
  have hcard1 : Nat.card Eb = 1 := by rw [hEbEq, Subgroup.card_bot]
  have hlarge : 1 < Nat.card Eb := by
    rw [hcardEb]
    exact Nat.one_lt_pow (by norm_num) h.prime.one_lt
  omega

private theorem exists_minimal_normal_of_data (hYne : Y ≠ ⊥) :
    ∃ N : Subgroup ↥Y, Minimal (fun M : Subgroup ↥Y => M.Normal ∧ M ≠ ⊥) N := by
  haveI : Nontrivial ↥Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hYne
  obtain ⟨N, -, hNmin⟩ := Finite.exists_le_minimal
    (p := fun M : Subgroup ↥Y => M.Normal ∧ M ≠ ⊥) (a := ⊤)
    ⟨inferInstance, top_ne_bot⟩
  exact ⟨N, hNmin⟩

private theorem not_isPGroup_of_normal_of_data
    (hOp : ∀ R : Subgroup L, IsPGroup p R → R ≤ Y → (R.subgroupOf Y).Normal → R = ⊥)
    {N : Subgroup ↥Y} (hN : N.Normal) (hNne : N ≠ ⊥) : ¬ IsPGroup p ↥N := by
  intro hNp
  have hRleY : N.map Y.subtype ≤ Y := Subgroup.map_subtype_le N
  have hRp : IsPGroup p ↥(N.map Y.subtype) := hNp.map Y.subtype
  have hRn : ((N.map Y.subtype).subgroupOf Y).Normal := by
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective Y.subtype_injective]
    exact hN
  exact hNne ((Subgroup.map_eq_bot_iff_of_injective N Y.subtype_injective).mp
    (hOp (N.map Y.subtype) hRp hRleY hRn))

private theorem p_dvd_card_of_normal_of_data (h : SporOvergroupData L p d Y)
    (hO : GLAPPrimeCoreOf p Y = ⊥)
    {N : Subgroup ↥Y} (hN : N.Normal) (hNne : N ≠ ⊥) : p ∣ Nat.card ↥N := by
  by_contra hpdvd
  have hcop : Nat.Coprime p (Nat.card ↥(N.map Y.subtype)) := by
    rw [Subgroup.card_map_of_injective Y.subtype_injective]
    exact h.prime.coprime_iff_not_dvd.mpr hpdvd
  have hSN : ∀ g ∈ Y, ∀ x ∈ N.map Y.subtype, g * x * g⁻¹ ∈ N.map Y.subtype := by
    intro g hg x hx
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨(⟨g, hg⟩ : ↥Y) * n * (⟨g, hg⟩ : ↥Y)⁻¹, ?_, ?_⟩
    · exact hN.conj_mem n hn ⟨g, hg⟩
    · rfl
  have hle := le_GLAPPrimeCoreOf_of_normal (Subgroup.map_subtype_le N) hSN hcop
  rw [hO] at hle
  exact hNne ((Subgroup.map_eq_bot_iff_of_injective N Y.subtype_injective).mp
    (le_bot_iff.mp hle))

private theorem minimal_normal_center_eq_bot_of_data [Fact p.Prime]
    (h : SporOvergroupData L p d Y)
    (hO : GLAPPrimeCoreOf p Y = ⊥)
    (hOp : ∀ R : Subgroup L, IsPGroup p R → R ≤ Y → (R.subgroupOf Y).Normal → R = ⊥)
    {N : Subgroup ↥Y}
    (hNmin : Minimal (fun M : Subgroup ↥Y => M.Normal ∧ M ≠ ⊥) N) :
    Subgroup.center ↥N = ⊥ := by
  haveI : N.Normal := hNmin.1.1
  have hNne : N ≠ ⊥ := hNmin.1.2
  have hNmin' : ∀ M : Subgroup ↥Y, M.Normal → M ≤ N → M = ⊥ ∨ M = N := by
    intro M hMn hMN
    by_cases hMbot : M = ⊥
    · exact Or.inl hMbot
    · exact Or.inr (hNmin.eq_of_le ⟨hMn, hMbot⟩ hMN)
  rcases CFSG.GH74.GLS.Balance.BenderExt.minimal_normal_trichotomy (p := p) (N := N)
      hNne hNmin' with hfirst | hsecond | hthird
  · exact (not_isPGroup_of_normal_of_data hOp hNmin.1.1 hNne hfirst.1).elim
  · exact False.elim (hsecond (p_dvd_card_of_normal_of_data h hO hNmin.1.1 hNne))
  · exact hthird.1

private theorem sylow_le_normalizer_of_normal {Q M : Subgroup ↥Y} (hM : M.Normal) :
    Q ≤ Subgroup.normalizer (M : Set ↥Y) := by
  haveI : M.Normal := hM
  have hMnormTop : (⊤ : Subgroup ↥Y) ≤ Subgroup.normalizer (M : Set ↥Y) := by
    rw [Subgroup.normalizer_eq_top]
  exact le_top.trans hMnormTop

private theorem center_sylow_map_card {Q : Subgroup ↥Y}
    (hZcard : Nat.card ↥(Subgroup.center ↥Q) = p) :
    Nat.card ↥((Subgroup.center ↥Q).map Q.subtype) = p := by
  rw [Subgroup.card_map_of_injective Q.subtype_injective, hZcard]

private theorem center_sylow_map_ne_bot [Fact p.Prime] {Q : Subgroup ↥Y}
    (hZcard : Nat.card ↥(Subgroup.center ↥Q) = p) :
    (Subgroup.center ↥Q).map Q.subtype ≠ ⊥ := by
  intro hbot
  have hcard : Nat.card ↥((Subgroup.center ↥Q).map Q.subtype) = 1 := by
    rw [hbot, Subgroup.card_bot]
  have hpc := center_sylow_map_card hZcard
  rw [hcard] at hpc
  exact (Fact.out : p.Prime).ne_one hpc.symm

private theorem minimal_normal_unique_of_data [Fact p.Prime]
    (h : SporOvergroupData L p d Y)
    (hO : GLAPPrimeCoreOf p Y = ⊥)
    (hOp : ∀ R : Subgroup L, IsPGroup p R → R ≤ Y → (R.subgroupOf Y).Normal → R = ⊥)
    {Q : Subgroup ↥Y} (hQ : IsSylowOf p Q ⊤)
    (hZcard : Nat.card ↥(Subgroup.center ↥Q) = p)
    {N M : Subgroup ↥Y}
    (hNmin : Minimal (fun K : Subgroup ↥Y => K.Normal ∧ K ≠ ⊥) N)
    (hMmin : Minimal (fun K : Subgroup ↥Y => K.Normal ∧ K ≠ ⊥) M) : M = N := by
  have hNne : N ≠ ⊥ := hNmin.1.2
  have hMne : M ≠ ⊥ := hMmin.1.2
  have hNp : p ∣ Nat.card ↥N :=
    p_dvd_card_of_normal_of_data h hO hNmin.1.1 hNne
  have hMp : p ∣ Nat.card ↥M :=
    p_dvd_card_of_normal_of_data h hO hMmin.1.1 hMne
  let Z : Subgroup ↥Y := (Subgroup.center ↥Q).map Q.subtype
  have hZN : Z ≤ N :=
    center_sylow_le_of_le_normalizer hQ (sylow_le_normalizer_of_normal hNmin.1.1) hNp hZcard
  have hZM : Z ≤ M :=
    center_sylow_le_of_le_normalizer hQ (sylow_le_normalizer_of_normal hMmin.1.1) hMp hZcard
  have hZne : Z ≠ ⊥ := center_sylow_map_ne_bot hZcard
  by_contra hMN
  have hdisj : M ⊓ N = ⊥ :=
    CFSG.LocalCores.inf_eq_bot_of_minimal_normal
      ⟨hMmin.1.1, hMmin.1.2, fun K hKn hKM =>
        (em (K = ⊥)).imp id fun hKne => hMmin.eq_of_le ⟨hKn, hKne⟩ hKM⟩
      ⟨hNmin.1.1, hNmin.1.2, fun K hKn hKN =>
        (em (K = ⊥)).imp id fun hKne => hNmin.eq_of_le ⟨hKn, hKne⟩ hKN⟩ hMN
  exact hZne (le_bot_iff.mp (hdisj ▸ le_inf hZM hZN))

private theorem centralizer_eq_bot_of_minimal_normal [Fact p.Prime]
    (h : SporOvergroupData L p d Y)
    (hO : GLAPPrimeCoreOf p Y = ⊥)
    (hOp : ∀ R : Subgroup L, IsPGroup p R → R ≤ Y → (R.subgroupOf Y).Normal → R = ⊥)
    {Q : Subgroup ↥Y} (hQ : IsSylowOf p Q ⊤)
    (hZcard : Nat.card ↥(Subgroup.center ↥Q) = p)
    {N : Subgroup ↥Y}
    (hNmin : Minimal (fun K : Subgroup ↥Y => K.Normal ∧ K ≠ ⊥) N) :
    Subgroup.centralizer (N : Set ↥Y) = ⊥ := by
  haveI : N.Normal := hNmin.1.1
  have hcenterN : Subgroup.center ↥N = ⊥ :=
    minimal_normal_center_eq_bot_of_data h hO hOp hNmin
  have hCnormal : (Subgroup.centralizer (N : Set ↥Y)).Normal := Subgroup.normal_centralizer
  by_contra hCne
  obtain ⟨M, hMn, hMleC, hMne, hMmin0⟩ :=
    CFSG.exists_minimal_normal_le (Subgroup.centralizer (N : Set ↥Y)) hCnormal hCne
  have hMmin : Minimal (fun K : Subgroup ↥Y => K.Normal ∧ K ≠ ⊥) M := by
    refine ⟨⟨hMn, hMne⟩, ?_⟩
    intro K hK hKM
    exact (hMmin0 K hK.1 hKM hK.2).ge
  have hMeqN : M = N :=
    minimal_normal_unique_of_data h hO hOp hQ hZcard hNmin hMmin
  have hNleC : N ≤ Subgroup.centralizer (N : Set ↥Y) := hMeqN ▸ hMleC
  have hNcomm : IsMulCommutative ↥N :=
    (Subgroup.le_centralizer_iff_isMulCommutative (K := N)).mp hNleC
  have hcenterTop : Subgroup.center ↥N = ⊤ := Subgroup.center_eq_top_iff.mpr hNcomm
  rw [hcenterN] at hcenterTop
  haveI : Nontrivial ↥N := (Subgroup.nontrivial_iff_ne_bot N).mpr hNmin.1.2
  exact top_ne_bot hcenterTop.symm

private theorem exists_simple_factor_component_of_data [Fact p.Prime] {N : Subgroup ↥Y}
    (hNmin : Minimal (fun K : Subgroup ↥Y => K.Normal ∧ K ≠ ⊥) N)
    (hcenterN : Subgroup.center ↥N = ⊥) (hNp : p ∣ Nat.card ↥N) :
    ∃ T₀ : Subgroup ↥Y, T₀ ≤ N ∧ (T₀.subgroupOf N).Normal ∧ IsSimpleGroup ↥T₀ ∧
      (∃ a b : ↥T₀, a * b ≠ b * a) ∧ p ∣ Nat.card ↥T₀ ∧ CFSG.IsComponent T₀ := by
  haveI : N.Normal := hNmin.1.1
  obtain ⟨T, hTmin, hTsimple, hTnonab, hTpdvd⟩ :=
    Helpers.minimal_normal_subgroup_contains_normal_simple_with_nonab_of_centerless N hNmin
  have hTnonab' : ∃ a b : ↥T, a * b ≠ b * a := hTnonab hcenterN
  have hTp : p ∣ Nat.card ↥T := hTpdvd p (Fact.out : p.Prime) hNp
  let T₀ : Subgroup ↥Y := T.map N.subtype
  have hT₀leN : T₀ ≤ N := Subgroup.map_subtype_le T
  have hT₀normalN : (T₀.subgroupOf N).Normal := by
    have hTeq : T₀.subgroupOf N = T := by
      dsimp only [T₀]
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
    rw [hTeq]
    exact hTmin.1.1
  have hT₀simple : IsSimpleGroup ↥T₀ := by
    haveI : IsSimpleGroup ↥T := hTsimple
    exact (Subgroup.equivMapOfInjective T N.subtype N.subtype_injective).symm.isSimpleGroup
  have hT₀nonab : ∃ a b : ↥T₀, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hTnonab'
    let e : ↥T ≃* ↥T₀ := Subgroup.equivMapOfInjective T N.subtype N.subtype_injective
    exact ⟨e a, e b, fun h => hab (e.injective (by simpa using h))⟩
  have hT₀p : p ∣ Nat.card ↥T₀ := by
    rw [show Nat.card ↥T₀ = Nat.card ↥T from
      Subgroup.card_map_of_injective N.subtype_injective]
    exact hTp
  have hT₀ne : T₀ ≠ ⊥ := by
    haveI : IsSimpleGroup ↥T₀ := hT₀simple
    exact (Subgroup.nontrivial_iff_ne_bot T₀).mp inferInstance
  have hT₀component : CFSG.IsComponent T₀ := by
    refine ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hT₀nonab).1, ?_⟩
    exact Subgroup.IsSubnormal.step T₀ N hT₀leN hNmin.1.1.isSubnormal hT₀normalN
  exact ⟨T₀, hT₀leN, hT₀normalN, hT₀simple, hT₀nonab, hT₀p, hT₀component⟩

private abbrev conjActImage (Q : Subgroup ↥Y) : Subgroup (ConjAct ↥Y) :=
  Q.map (ConjAct.toConjAct : ↥Y ≃* ConjAct ↥Y).toMonoidHom

private theorem orbit_iso {T₀ : Subgroup ↥Y}
    (A : ↥(MulAction.orbit (ConjAct ↥Y) T₀)) :
    Nonempty (↥T₀ ≃* ↥A.1) := by
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp A.2
  exact ⟨(Subgroup.equivSMul g T₀).trans (MulEquiv.subgroupCongr hg)⟩

private theorem orbit_component {T₀ : Subgroup ↥Y} (hT₀ : CFSG.IsComponent T₀)
    (A : ↥(MulAction.orbit (ConjAct ↥Y) T₀)) : CFSG.IsComponent A.1 := by
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp A.2
  rw [← hg]
  have hsmul : g • T₀ = T₀.map (MulAut.conj (ConjAct.ofConjAct g)).toMonoidHom := by
    rw [Subgroup.pointwise_smul_def]
    congr 1
  rw [hsmul]
  exact CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (ConjAct.ofConjAct g)) hT₀

private theorem orbit_centerless {T₀ : Subgroup ↥Y} (hT₀simple : IsSimpleGroup ↥T₀)
    (hT₀nonab : ∃ a b : ↥T₀, a * b ≠ b * a)
    (A : ↥(MulAction.orbit (ConjAct ↥Y) T₀)) :
    Subgroup.center ↥A.1 = ⊥ := by
  obtain ⟨e⟩ := orbit_iso A
  have hmap := Subgroup.map_center_eq e
  haveI : IsSimpleGroup ↥T₀ := hT₀simple
  have hcenterT₀ : Subgroup.center ↥T₀ = ⊥ :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hT₀nonab).2
  rw [hcenterT₀, Subgroup.map_bot] at hmap
  exact hmap.symm

private theorem orbit_pdvd {T₀ : Subgroup ↥Y} (hT₀p : p ∣ Nat.card ↥T₀)
    (A : ↥(MulAction.orbit (ConjAct ↥Y) T₀)) : p ∣ Nat.card ↥A.1 := by
  obtain ⟨e⟩ := orbit_iso A
  rw [← Nat.card_congr e.toEquiv]
  exact hT₀p

private theorem orbit_comm {T₀ : Subgroup ↥Y}
    (hcomponent : ∀ A : ↥(MulAction.orbit (ConjAct ↥Y) T₀), CFSG.IsComponent A.1) :
    Pairwise fun A B : ↥(MulAction.orbit (ConjAct ↥Y) T₀) =>
      A.1 ≤ Subgroup.centralizer (B.1 : Set ↥Y) := by
  intro A B hAB
  have hne : A.1 ≠ B.1 := fun h => hAB (Subtype.ext h)
  rcases CFSG.LocalCores.distinct_components_commute (hcomponent A) (hcomponent B) with h | h
  · exact absurd h hne
  · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h

private theorem orbit_card_le_three [Fact p.Prime] {T₀ : Subgroup ↥Y}
    (hYrank : CFSG.Open.pRank p (⊤ : Subgroup ↥Y) ≤ 3)
    (hcomm : Pairwise fun A B : ↥(MulAction.orbit (ConjAct ↥Y) T₀) =>
      A.1 ≤ Subgroup.centralizer (B.1 : Set ↥Y))
    (hcenter : ∀ A : ↥(MulAction.orbit (ConjAct ↥Y) T₀),
      Subgroup.center ↥A.1 = ⊥)
    (hpdvd : ∀ A : ↥(MulAction.orbit (ConjAct ↥Y) T₀), p ∣ Nat.card ↥A.1) :
    Nat.card ↥(MulAction.orbit (ConjAct ↥Y) T₀) ≤ 3 := by
  letI : Fintype ↥Y := Fintype.ofFinite _
  letI : Fintype (ConjAct ↥Y) := Fintype.ofEquiv ↥Y ConjAct.ofConjAct.symm.toEquiv
  haveI : Finite ↥(MulAction.orbit (ConjAct ↥Y) T₀) := by
    rw [MulAction.orbit]
    exact (Set.finite_range (fun g : ConjAct ↥Y => g • T₀)).to_subtype
  letI : Fintype ↥(MulAction.orbit (ConjAct ↥Y) T₀) := Fintype.ofFinite _
  have hbound := Helpers.commuting_centerless_prime_divisible_factors_card_le_rank
    p (Fact.out : p.Prime) (fun A : ↥(MulAction.orbit (ConjAct ↥Y) T₀) => A.1)
    hcomm hcenter hpdvd
  simpa [Nat.card_eq_fintype_card] using hbound.trans hYrank

private theorem orbit_subsingleton [Fact p.Prime] {T₀ Q : Subgroup ↥Y}
    (hcard3 : Nat.card ↥(MulAction.orbit (ConjAct ↥Y) T₀) ≤ 3)
    (hQ : IsPGroup p ↥Q) (hp5 : 5 ≤ p)
    (A : ↥(MulAction.orbit (ConjAct ↥Y) T₀)) :
    Subsingleton ↥(MulAction.orbit ↥(conjActImage Q) A.1) := by
  have hQc : IsPGroup p ↥(conjActImage Q) :=
    IsPGroup.map hQ (ConjAct.toConjAct : ↥Y ≃* ConjAct ↥Y).toMonoidHom
  have hsubset : MulAction.orbit ↥(conjActImage Q) A.1 ⊆
      MulAction.orbit (ConjAct ↥Y) T₀ := by
    intro Bh hBh
    obtain ⟨q, hq⟩ := MulAction.mem_orbit_iff.mp hBh
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp A.2
    exact MulAction.mem_orbit_iff.mpr ⟨(q : ConjAct ↥Y) * g, by
      rw [mul_smul, hg]
      exact hq⟩
  have hleIndex : Nat.card ↥(MulAction.orbit ↥(conjActImage Q) A.1) ≤
      Nat.card ↥(MulAction.orbit (ConjAct ↥Y) T₀) := by
    refine Nat.card_le_card_of_injective
      (fun Bh : ↥(MulAction.orbit ↥(conjActImage Q) A.1) =>
        (⟨Bh.1, hsubset Bh.2⟩ : ↥(MulAction.orbit (ConjAct ↥Y) T₀))) ?_
    intro Bh Ch hBC
    exact Subtype.ext (congrArg (fun x => x.1) hBC)
  obtain ⟨n, hn⟩ := hQc.card_orbit A.1
  have hpn : p ^ n ≤ 3 := by
    rw [← hn]
    exact hleIndex.trans hcard3
  have hn0 : n = 0 := by
    by_contra hnne
    have hp_le : p ≤ p ^ n := Nat.le_pow (Nat.pos_of_ne_zero hnne)
    omega
  have hcard_orbit : Nat.card ↥(MulAction.orbit ↥(conjActImage Q) A.1) = 1 := by
    calc
      Nat.card ↥(MulAction.orbit ↥(conjActImage Q) A.1) = p ^ n := hn
      _ = p ^ 0 := by rw [hn0]
      _ = 1 := pow_zero p
  exact (Nat.card_eq_one_iff_unique.mp hcard_orbit).1

private theorem sylow_smul_factor [Fact p.Prime] {T₀ Q : Subgroup ↥Y}
    (hcard3 : Nat.card ↥(MulAction.orbit (ConjAct ↥Y) T₀) ≤ 3)
    (hQ : IsPGroup p ↥Q) (hp5 : 5 ≤ p)
    (A : ↥(MulAction.orbit (ConjAct ↥Y) T₀)) (q : ↥Q) :
    A.1.map (MulAut.conj (q : ↥Y)).toMonoidHom = A.1 := by
  let qc : ↥(conjActImage Q) :=
    ⟨ConjAct.toConjAct (q : ↥Y), Subgroup.mem_map_of_mem _ q.2⟩
  have hsub : Subsingleton ↥(MulAction.orbit ↥(conjActImage Q) A.1) :=
    orbit_subsingleton hcard3 hQ hp5 A
  have heq := Subsingleton.elim
    (⟨qc • A.1, ⟨qc, rfl⟩⟩ : ↥(MulAction.orbit ↥(conjActImage Q) A.1))
    ⟨A.1, MulAction.mem_orbit_self A.1⟩
  have hq : qc • A.1 = A.1 := congrArg Subtype.val heq
  have hq' : (ConjAct.toConjAct (q : ↥Y)) • A.1 = A.1 := by
    simpa [qc, Subgroup.smul_def] using hq
  have hmap : (ConjAct.toConjAct (q : ↥Y)) • A.1 =
      A.1.map (MulAut.conj (q : ↥Y)).toMonoidHom := by
    rw [Subgroup.pointwise_smul_def]
    congr 1
  rwa [hmap] at hq'

private theorem sylow_fixes_factor [Fact p.Prime] {T₀ Q : Subgroup ↥Y}
    (hcard3 : Nat.card ↥(MulAction.orbit (ConjAct ↥Y) T₀) ≤ 3)
    (hQ : IsPGroup p ↥Q) (hp5 : 5 ≤ p)
    (A : ↥(MulAction.orbit (ConjAct ↥Y) T₀)) :
    Q ≤ Subgroup.normalizer (A.1 : Set ↥Y) := by
  intro q hq
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact sylow_smul_factor hcard3 hQ hp5 A ⟨q, hq⟩

private theorem false_of_two_factors [Fact p.Prime] {T₀ Q : Subgroup ↥Y}
    (hcomponent : ∀ A : ↥(MulAction.orbit (ConjAct ↥Y) T₀), CFSG.IsComponent A.1)
    (hcenter : ∀ A : ↥(MulAction.orbit (ConjAct ↥Y) T₀),
      Subgroup.center ↥A.1 = ⊥)
    (hpdvd : ∀ A : ↥(MulAction.orbit (ConjAct ↥Y) T₀), p ∣ Nat.card ↥A.1)
    (hcard3 : Nat.card ↥(MulAction.orbit (ConjAct ↥Y) T₀) ≤ 3)
    (hQtop : CFSG.ABGLocalTools.IsSylowOf p Q ⊤)
    (hZcard : Nat.card ↥(Subgroup.center ↥Q) = p) (hp5 : 5 ≤ p)
    {A B : ↥(MulAction.orbit (ConjAct ↥Y) T₀)} (hAB : A ≠ B) : False := by
  have hZA : (Subgroup.center ↥Q).map Q.subtype ≤ A.1 :=
    center_sylow_le_of_le_normalizer hQtop
      (sylow_fixes_factor hcard3 hQtop.isPGroup hp5 A) (hpdvd A) hZcard
  have hZB : (Subgroup.center ↥Q).map Q.subtype ≤ B.1 :=
    center_sylow_le_of_le_normalizer hQtop
      (sylow_fixes_factor hcard3 hQtop.isPGroup hp5 B) (hpdvd B) hZcard
  have hdisj : A.1 ⊓ B.1 = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxcenter : (⟨x, hx.1⟩ : ↥A.1) ∈ Subgroup.center ↥A.1 := by
      rw [Subgroup.mem_center_iff]
      intro a
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp
        (orbit_comm hcomponent hAB a.2) x hx.2).symm
    rw [hcenter A] at hxcenter
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hxcenter)
  exact center_sylow_map_ne_bot hZcard
    (le_bot_iff.mp (hdisj ▸ le_inf hZA hZB))

private theorem eq_of_subsingleton_orbit {T₀ N : Subgroup ↥Y}
    (hcard1 : Nat.card ↥(MulAction.orbit (ConjAct ↥Y) T₀) = 1)
    (hNmin : Minimal (fun K : Subgroup ↥Y => K.Normal ∧ K ≠ ⊥) N)
    (hT₀leN : T₀ ≤ N) (hT₀simple : IsSimpleGroup ↥T₀) : N = T₀ := by
  have hsub : Subsingleton ↥(MulAction.orbit (ConjAct ↥Y) T₀) :=
    (Nat.card_eq_one_iff_unique.mp hcard1).1
  have hT₀normal : T₀.Normal := by
    apply Subgroup.Normal.of_conjugate_fixed
    intro g
    have heq : (⟨ConjAct.toConjAct g • T₀,
        ⟨ConjAct.toConjAct g, rfl⟩⟩ : ↥(MulAction.orbit (ConjAct ↥Y) T₀)) =
        ⟨T₀, MulAction.mem_orbit_self T₀⟩ := hsub.elim _ _
    have hg : ConjAct.toConjAct g • T₀ = T₀ := congrArg Subtype.val heq
    have hsmul : ConjAct.toConjAct g • T₀ = MulAut.conj g • T₀ := by
      rw [Subgroup.pointwise_smul_def, Subgroup.pointwise_smul_def]
      congr 1
    rwa [hsmul] at hg
  have hT₀ne : T₀ ≠ ⊥ := by
    haveI : IsSimpleGroup ↥T₀ := hT₀simple
    exact (Subgroup.nontrivial_iff_ne_bot T₀).mp inferInstance
  exact le_antisymm (hNmin.2 ⟨hT₀normal, hT₀ne⟩ hT₀leN) hT₀leN

private theorem exists_simple_normal_of_eq {N T₀ : Subgroup ↥Y} (hNT : N = T₀)
    (hT₀normal : T₀.Normal) (hT₀simple : IsSimpleGroup ↥T₀)
    (hT₀nonab : ∃ a b : ↥T₀, a * b ≠ b * a)
    (hCbot : Subgroup.centralizer (N : Set ↥Y) = ⊥) :
    ∃ J : Subgroup L, J ≤ Y ∧ (J.subgroupOf Y).Normal ∧ IsSimpleGroup ↥J ∧
      (∃ a b : ↥J, a * b ≠ b * a) ∧ Subgroup.centralizer (J : Set L) ⊓ Y = ⊥ := by
  let J : Subgroup L := T₀.map Y.subtype
  have hJleY : J ≤ Y := Subgroup.map_subtype_le T₀
  have hJsub : J.subgroupOf Y = T₀ := by
    dsimp only [J]
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective Y.subtype_injective]
  have hJnormal : (J.subgroupOf Y).Normal := by
    rw [hJsub]
    exact hT₀normal
  let eJ : ↥T₀ ≃* ↥J := Subgroup.equivMapOfInjective T₀ Y.subtype Y.subtype_injective
  have hJsimple : IsSimpleGroup ↥J := by
    haveI : IsSimpleGroup ↥T₀ := hT₀simple
    exact eJ.symm.isSimpleGroup
  have hJnonab : ∃ a b : ↥J, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hT₀nonab
    exact ⟨eJ a, eJ b, fun h => hab (eJ.injective (by simpa using h))⟩
  have hJcent : Subgroup.centralizer (J : Set L) ⊓ Y = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hycentJ : y ∈ Subgroup.centralizer (J : Set L) := hy.1
    have hyY : y ∈ Y := hy.2
    have hycentN : (⟨y, hyY⟩ : ↥Y) ∈ Subgroup.centralizer (N : Set ↥Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have hmemJ : (n : L) ∈ J := by
        dsimp only [J]
        rw [← hNT]
        exact Subgroup.mem_map_of_mem Y.subtype hn
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hycentJ (n : L) hmemJ)
    rw [hCbot] at hycentN
    exact congr_arg Subtype.val (Subgroup.mem_bot.mp hycentN)
  exact ⟨J, hJleY, hJnormal, hJsimple, hJnonab, hJcent⟩

private structure SimpleNormalData (L : Type) [Group L] [Finite L] (p d : ℕ) (Y : Subgroup L)
    where
  Q : Subgroup ↥Y
  hQtop : CFSG.ABGLocalTools.IsSylowOf p Q ⊤
  hZcard : Nat.card ↥(Subgroup.center ↥Q) = p
  N : Subgroup ↥Y
  hNmin : Minimal (fun M : Subgroup ↥Y => M.Normal ∧ M ≠ ⊥) N
  T₀ : Subgroup ↥Y
  hT₀leN : T₀ ≤ N
  hT₀simple : IsSimpleGroup ↥T₀
  hT₀nonab : ∃ a b : ↥T₀, a * b ≠ b * a
  hCbot : Subgroup.centralizer (N : Set ↥Y) = ⊥
  hcomponent : ∀ A : ↥(MulAction.orbit (ConjAct ↥Y) T₀), CFSG.IsComponent A.1
  hcenter : ∀ A : ↥(MulAction.orbit (ConjAct ↥Y) T₀), Subgroup.center ↥A.1 = ⊥
  hpdvd : ∀ A : ↥(MulAction.orbit (ConjAct ↥Y) T₀), p ∣ Nat.card ↥A.1
  hcomm : Pairwise fun A B : ↥(MulAction.orbit (ConjAct ↥Y) T₀) =>
    A.1 ≤ Subgroup.centralizer (B.1 : Set ↥Y)
  hcard3 : Nat.card ↥(MulAction.orbit (ConjAct ↥Y) T₀) ≤ 3

private theorem simple_normal_data_of_data [Fact p.Prime]
    (h : SporOvergroupData L p d Y) (hO : GLAPPrimeCoreOf p Y = ⊥)
    (hOp : ∀ R : Subgroup L, IsPGroup p R → R ≤ Y → (R.subgroupOf Y).Normal → R = ⊥)
    (hZ : ∀ Q : Sylow p L, Nat.card (Subgroup.center ↥(Q : Subgroup L)) = p) :
    Nonempty (SimpleNormalData L p d Y) := by
  classical
  obtain ⟨QY, hQYtop, hZcard⟩ := sylow_center_data h hZ
  have hYne : Y ≠ ⊥ := y_ne_bot_of_data h
  obtain ⟨N, hNmin⟩ := exists_minimal_normal_of_data (Y := Y) hYne
  have hcenterN : Subgroup.center ↥N = ⊥ :=
    minimal_normal_center_eq_bot_of_data h hO hOp hNmin
  have hNp : p ∣ Nat.card ↥N :=
    p_dvd_card_of_normal_of_data h hO hNmin.1.1 hNmin.1.2
  have hCbot : Subgroup.centralizer (N : Set ↥Y) = ⊥ :=
    centralizer_eq_bot_of_minimal_normal h hO hOp hQYtop hZcard hNmin
  obtain ⟨T₀, hT₀leN, -, hT₀simple, hT₀nonab, hT₀p, hT₀component⟩ :=
    exists_simple_factor_component_of_data hNmin hcenterN hNp
  have hcomponent : ∀ A : ↥(MulAction.orbit (ConjAct ↥Y) T₀), CFSG.IsComponent A.1 :=
    orbit_component hT₀component
  have hcenter : ∀ A : ↥(MulAction.orbit (ConjAct ↥Y) T₀),
      Subgroup.center ↥A.1 = ⊥ :=
    orbit_centerless hT₀simple hT₀nonab
  have hpdvd : ∀ A : ↥(MulAction.orbit (ConjAct ↥Y) T₀), p ∣ Nat.card ↥A.1 :=
    orbit_pdvd hT₀p
  have hcomm : Pairwise fun A B : ↥(MulAction.orbit (ConjAct ↥Y) T₀) =>
      A.1 ≤ Subgroup.centralizer (B.1 : Set ↥Y) :=
    orbit_comm hcomponent
  have hcard3 : Nat.card ↥(MulAction.orbit (ConjAct ↥Y) T₀) ≤ 3 :=
    orbit_card_le_three (pRank_top_le_three_of_data h) hcomm hcenter hpdvd
  exact ⟨
    { Q := QY
      hQtop := hQYtop
      hZcard := hZcard
      N := N
      hNmin := hNmin
      T₀ := T₀
      hT₀leN := hT₀leN
      hT₀simple := hT₀simple
      hT₀nonab := hT₀nonab
      hCbot := hCbot
      hcomponent := hcomponent
      hcenter := hcenter
      hpdvd := hpdvd
      hcomm := hcomm
      hcard3 := hcard3 }⟩

theorem exists_simple_normal_of_data (h : SporOvergroupData L p d Y) (hp5 : 5 ≤ p)
    (hO : GLAPPrimeCoreOf p Y = ⊥)
    (hOp : ∀ R : Subgroup L, IsPGroup p R → R ≤ Y → (R.subgroupOf Y).Normal → R = ⊥)
    (hZ : ∀ Q : Sylow p L, Nat.card (Subgroup.center ↥(Q : Subgroup L)) = p) :
    ∃ J : Subgroup L, J ≤ Y ∧ (J.subgroupOf Y).Normal ∧ IsSimpleGroup ↥J ∧
      (∃ a b : ↥J, a * b ≠ b * a) ∧ Subgroup.centralizer (J : Set L) ⊓ Y = ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨D⟩ := simple_normal_data_of_data h hO hOp hZ
  let Index : Set (Subgroup ↥Y) := MulAction.orbit (ConjAct ↥Y) D.T₀
  haveI : Finite ↥Index := by
    letI : Fintype ↥Y := Fintype.ofFinite _
    letI : Fintype (ConjAct ↥Y) := Fintype.ofEquiv ↥Y ConjAct.ofConjAct.symm.toEquiv
    rw [show Index = Set.range (fun g : ConjAct ↥Y => g • D.T₀) from rfl]
    exact (Set.finite_range (fun g : ConjAct ↥Y => g • D.T₀)).to_subtype
  haveI : Nonempty ↥Index := ⟨⟨D.T₀, MulAction.mem_orbit_self D.T₀⟩⟩
  letI : Fintype ↥Index := Fintype.ofFinite _
  by_cases hcard1 : Nat.card ↥Index = 1
  · have hNT : D.N = D.T₀ :=
      eq_of_subsingleton_orbit hcard1 D.hNmin D.hT₀leN D.hT₀simple
    exact exists_simple_normal_of_eq hNT (hNT ▸ D.hNmin.1.1) D.hT₀simple D.hT₀nonab D.hCbot
  · exfalso
    have h2 : 1 < Nat.card ↥Index := by
      have hpos : 0 < Nat.card ↥Index := Nat.card_pos
      omega
    have h2' : 1 < (Finset.univ : Finset ↥Index).card := by simpa using h2
    obtain ⟨A, -, B, -, hAB⟩ := Finset.one_lt_card.mp h2'
    exact false_of_two_factors D.hcomponent D.hcenter D.hpdvd D.hcard3 D.hQtop
      D.hZcard hp5 hAB

end CFSG.LocalAnalysis.AGL81I.Section3.SporBig
