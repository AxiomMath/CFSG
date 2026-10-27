module

public import CFSG.LocalAnalysis.GLTheoremA.S4S.Common
public import CFSG.LocalAnalysis.GLTheoremA.S4.L49b
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Assembly
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_minimal_invariant_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B T : Subgroup G}
    (hB : IsElemAbelian p B) (hT : IsPGroup 2 T) (hBT : B ≤ Subgroup.normalizer (T : Set G))
    (hne : (⁅T, B⁆ : Subgroup G) ≠ ⊥) :
    ∃ T' : Subgroup G, T' ≤ T ∧ B ≤ Subgroup.normalizer (T' : Set G) ∧
      (⁅T', B⁆ : Subgroup G) = T' ∧ T' ≠ ⊥ ∧
      Nat.card B ≤ p * Nat.card (B ⊓ Subgroup.centralizer (T' : Set G) : Subgroup G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hex : ∃ n : ℕ, ∃ U : Subgroup G, U ≤ T ∧ B ≤ Subgroup.normalizer (U : Set G) ∧
      (⁅U, B⁆ : Subgroup G) ≠ ⊥ ∧ Nat.card U = n := ⟨_, T, le_rfl, hBT, hne, rfl⟩
  obtain ⟨T', hT'T, hBT', hT'ne, hT'card⟩ := Nat.find_spec hex
  have hmin : ∀ U : Subgroup G, U ≤ T → B ≤ Subgroup.normalizer (U : Set G) →
      (⁅U, B⁆ : Subgroup G) ≠ ⊥ → Nat.card T' ≤ Nat.card U := by
    intro U hUT hBU hUne
    rw [hT'card]
    exact Nat.find_min' hex ⟨U, hUT, hBU, hUne, rfl⟩
  have hT'2 : IsPGroup 2 T' := hT.to_le hT'T
  have hBp : IsPGroup p B := isPGroup_of_isElemAbelian hB
  have hcop : Nat.Coprime (Nat.card B) (Nat.card T') := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hBp.exists_card_eq
    obtain ⟨m, hm⟩ := hT'2.exists_card_eq
    rw [hk, hm]
    exact Nat.Coprime.pow k m ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hsolv : Group.IsSolvable T' := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Group.IsNilpotent T' := hT'2.isNilpotent
    infer_instance
  have hdouble : (⁅⁅T', B⁆, B⁆ : Subgroup G) = ⁅T', B⁆ :=
    GL83.commutator_double_eq_self B T' hBT' hcop hsolv
  have hTB : (⁅T', B⁆ : Subgroup G) ≤ T' := commutator_le_left_of_normalizes hBT'
  have hBTB : B ≤ Subgroup.normalizer ((⁅T', B⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator hBT' Subgroup.le_normalizer
  have h2 : (⁅T', B⁆ : Subgroup G) = T' := by
    have hc := hmin ⁅T', B⁆ (hTB.trans hT'T) hBTB (by rw [hdouble]; exact hT'ne)
    exact Subgroup.eq_of_le_of_card_ge hTB hc
  have hT'1 : T' ≠ ⊥ := by
    intro h
    apply hT'ne
    rw [h]
    exact Subgroup.commutator_bot_left B
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian hp hB
  have hpB : p ≤ Nat.card B := by
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, Subgroup.card_eq_one] at hk
      apply hT'ne
      rw [hk]
      exact Subgroup.commutator_bot_right T'
    rw [hk]
    exact Nat.le_self_pow hk0 p
  have hcopT : Nat.Coprime p (Nat.card T') := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨m, hm⟩ := hT'2.exists_card_eq
    rw [hm]
    exact Nat.Coprime.pow_right m ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_hyperplanes hp hB hpB hBT'
    hcopT
  have hH : ∃ H ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes p B,
      T' ≤ Subgroup.centralizer (H : Set G) := by
    by_contra hcon
    push_neg at hcon
    apply hT'ne
    have hUC : ∀ H ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes p B,
        T' ⊓ Subgroup.centralizer (H : Set G) ≤ Subgroup.centralizer (B : Set G) := by
      intro H hH
      have hlt : T' ⊓ Subgroup.centralizer (H : Set G) < T' :=
        lt_of_le_of_ne inf_le_left fun h => hcon H hH (h ▸ inf_le_right)
      have hBH : B ≤ Subgroup.centralizer (H : Set G) := by
        intro g hg
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        exact isElemAbelian_commute hB (hH.1 hh) hg
      have hBU : B ≤ Subgroup.normalizer ((T' ⊓ Subgroup.centralizer (H : Set G) : Subgroup G) : Set G) :=
        le_normalizer_inf hBT' (hBH.trans Subgroup.le_normalizer)
      by_contra hnc
      have hne' : (⁅T' ⊓ Subgroup.centralizer (H : Set G), B⁆ : Subgroup G) ≠ ⊥ := fun h =>
        hnc (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h)
      have hc := hmin _ (inf_le_left.trans hT'T) hBU hne'
      exact absurd (Subgroup.card_lt_of_lt hlt) (not_lt.2 hc)
    have hle : T' ≤ Subgroup.centralizer (B : Set G) := by
      rw [← hgen]
      exact iSup₂_le fun H hH => hUC H hH
    have hcB : (⁅T', B⁆ : Subgroup G) = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hle
    exact hcB
  obtain ⟨H, hHyp, hHC⟩ := hH
  refine ⟨T', hT'T, hBT', h2, hT'1, ?_⟩
  have hHle : H ≤ B ⊓ Subgroup.centralizer (T' : Set G) :=
    le_inf hHyp.1 (Subgroup.le_centralizer_iff.2 hHC)
  calc Nat.card B = p * Nat.card H := hHyp.2
    _ ≤ p * Nat.card (B ⊓ Subgroup.centralizer (T' : Set G) : Subgroup G) :=
      Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hHle)

theorem autBar_le_innerAut_of_inducesInner {p : ℕ} {B J : Subgroup G}
    (hBJ : B ≤ Subgroup.normalizer (J : Set G)) (h : ∀ c ∈ B, InducesInnerMod p J c) :
    autBar p B J ≤ innerAut (barOf p J) := by
  rintro _ ⟨γ, hγ, rfl⟩
  have hcB : (γ : G) ∈ B := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hγ)).1
  obtain ⟨l, hl, hl'⟩ := h _ hcB
  refine ⟨QuotientGroup.mk ⟨l, hl⟩, ?_⟩
  ext z
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
  rw [barAut_mk, MulAut.conj_apply]
  have hy₁coe : ((J.normalizerMonoidHom γ y : ↥J) : G) = (γ : G) * y * (γ : G)⁻¹ :=
    Subgroup.normalizerMonoidHom_apply_apply_coe J γ y
  have key := hl' ((J.normalizerMonoidHom γ y : ↥J) : G) (J.normalizerMonoidHom γ y).2
  rw [hy₁coe] at key
  have hO := (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p J hl) _).1 key
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  refine (Subgroup.mem_map_iff_mem J.subtype_injective).1 ?_
  have h2 := Subgroup.inv_mem _ hO
  have e : J.subtype ((⟨l, hl⟩ * y * ⟨l, hl⟩⁻¹ : ↥J)⁻¹ * J.normalizerMonoidHom γ y) =
      (l * ((l⁻¹ * ((γ : G) * y * (γ : G)⁻¹) * l)⁻¹ *
        ((γ : G)⁻¹ * ((γ : G) * y * (γ : G)⁻¹) * (γ : G))) * l⁻¹)⁻¹ := by
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hy₁coe]
    group
  rw [e]
  exact h2

theorem balanced_of_level_le_two {p : ℕ} (hpp : p.Prime) (hp2 : p ≠ 2) (hS3 : Stage3 G p)
    (h1912 : I1912At) {B : Subgroup G} {b : G} {J : Subgroup G} (hB : GLAIsBmax p B) (hbB : b ∈ B)
    (hb1 : b ≠ 1) (hJc : GLAPComponent p (Subgroup.centralizer ({b} : Set G)) J)
    (hBJ : B ≤ Subgroup.normalizer (J : Set G)) (hlev : fullCoverLevel p (PQuot p J) ≤ 2) :
    IsCompTwoPrimaryWeaklyLocallyBalanced p 1 B J := by
  obtain ⟨-, -, -, -, hc5⟩ := hS3
  have hBel : IsElemAbelian p B := hB.1
  have hquasi : CFSG.Open.IsQuasisimple (barOf p J) := isQuasisimple_pQuot_of_glaPComponent hpp hJc
  have hdvd : p ∣ Nat.card (barOf p J) := dvd_card_pQuot_of_component hpp hJc
  rcases h1912 p hpp hp2 (barOf p J) hquasi hdvd
      (k1Cover_or_k2Cover_of_fullCoverLevel_le_two hlev) (autBar p B J)
      (CFSG.HardMathSupport.Timmesfeld.Balance.Alt.isElemAbelian_autBar hBel J) with h | ⟨h3, hcat, hnot⟩
  · exact h
  · subst h3
    obtain ⟨-, hinner⟩ := hc5 rfl B b J hB hbB hb1 hJc hcat
    exact absurd (autBar_le_innerAut_of_inducesInner hBJ hinner) hnot

theorem claimA {m : ℕ} (hctx : ThmACtx G m) {p : ℕ} (hp : p ∈ Mu G m) (hS3 : Stage3 G p)
    (hS4o : Stage4Order G p) (h1912 : I1912At) (h1933 : I1933At G p) (hd : dLevel G p ≤ 2)
    {B : Subgroup G} {b x : G} {T : Subgroup G} (hB : GLAIsBmax p B) (hbB : b ∈ B) (hb1 : b ≠ 1)
    (hbe : IsEssential p B b) (hxB : x ∈ B) (hx1 : x ≠ 1) (hT2 : IsPGroup 2 T)
    (hTB : B ≤ Subgroup.normalizer (T : Set G))
    (hTx : T ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)))
    (hTb : T ≤ Subgroup.centralizer ({b} : Set G)) (hBT : (⁅B, T⁆ : Subgroup G) = T) :
    T ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G)) := by
  have hpp : p.Prime := hp.1.1
  have hp2 : p ≠ 2 := hp.1.2.1
  obtain ⟨-, -, -, -, -, -, -, h412⟩ := hS4o
  have hBel : IsElemAbelian p B := hB.1
  have hxcard : Nat.card (Subgroup.zpowers x) = p ^ 1 := by
    rw [pow_one]
    exact card_zpowers_eq_of_pow hpp (hBel.2 x hxB) hx1
  have hEk : IsEkIn p 1 B (Subgroup.zpowers x) :=
    ⟨Subgroup.zpowers_le.2 hxB, isElemAbelian_zpowers_of_mem hBel hxB, hxcard⟩
  have hJ : ∀ J : Subgroup G, GLAPComponent p (Subgroup.centralizer ({b} : Set G)) J →
      B ≤ Subgroup.normalizer (J : Set G) ∧ IsCompTwoPrimaryWeaklyLocallyBalanced p 1 B J := by
    intro J hJc
    have hSt : IsSTriple p B b J := ⟨hB, hbe, hJc⟩
    have hBJ : B ≤ Subgroup.normalizer (J : Set G) := h412 (hd.trans (by norm_num)) B b J hSt
    refine ⟨hBJ, ?_⟩
    have hlev : fullCoverLevel p (PQuot p J) ≤ 2 := by
      have h1 := tripleLevel_le_dLevel hSt
      have h2 : tripleLevel p B J ≤ 2 := h1.trans hd
      unfold tripleLevel at h2
      by_cases hG : IsGStar p B J
      · rw [if_pos hG] at h2
        omega
      · rw [if_neg hG] at h2
        omega
    exact balanced_of_level_le_two hpp hp2 hS3 h1912 hB hbB hb1 hJc hBJ hlev
  have hΔ : GLADelta p (Subgroup.zpowers x) = GLAPPrimeCoreOf p (Subgroup.centralizer ({x} : Set G)) :=
    gLADelta_zpowers hpp (hBel.2 x hxB) hx1
  have key := h1933 hpp hp2 hctx.1.simple hctx.1.nonabelian hctx.1.kProper B (Subgroup.zpowers x) 1 b
    hBel le_rfl hEk hbB hb1 hJ T hT2 hTB (by rw [hΔ]; exact le_inf hTx hTb)
  rw [Subgroup.commutator_comm, hBT] at key
  exact key

theorem lemma414 {m : ℕ} (hctx : ThmACtx G m) {p : ℕ} (hp : p ∈ Mu G m) (hS3 : Stage3 G p)
    (hS4o : Stage4Order G p) (h1912 : I1912At) (h1933 : I1933At G p) : Lemma414At G p := by
  intro hd B x T hB hxB hx1 hTx hT2 hBT
  by_contra hne
  have hpp : p.Prime := hp.1.1
  have hp2 : p ≠ 2 := hp.1.2.1
  have hΔ : GLADeltaZero G p := hp.2.2
  have hBel : IsElemAbelian p B := hB.1
  obtain ⟨T', hT'T, hBT', hT'B, hT'1, hrank⟩ :=
    exists_minimal_invariant_two hpp hp2 hBel hT2 hBT hne
  obtain ⟨A, hAB, hAcard, hAess⟩ := hS3.2.1 B hB
  have hm4 : 4 ≤ GLATwoLocalRank p G := by
    rw [hp.2.1]
    exact hctx.1.four_le
  have hBcard : Nat.card B = p ^ GLATwoLocalRank p G := hB.2.1
  set C' : Subgroup G := B ⊓ Subgroup.centralizer (T' : Set G) with hC'
  have hBA : B ≤ Subgroup.centralizer (A : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact isElemAbelian_commute hBel (hAB ha) hg
  have hCB : C' ≤ Subgroup.normalizer (A : Set G) :=
    (inf_le_left.trans hBA).trans (Subgroup.centralizer_le_normalizer _)
  have hprod := card_sup_mul_card_inf_of_le_normalizer hCB
  have hsupB : Nat.card (A ⊔ C' : Subgroup G) ≤ Nat.card B :=
    Subgroup.card_le_of_le (sup_le hAB inf_le_left)
  have hapos : 0 < Nat.card A := Nat.card_pos
  have h1 : Nat.card A ≤ Nat.card C' := by
    have h1' : p * Nat.card A ≤ p * Nat.card C' :=
      calc p * Nat.card A = Nat.card B := by rw [← hAcard, mul_comm]
        _ ≤ p * Nat.card C' := hrank
    exact Nat.le_of_mul_le_mul_left h1' hpp.pos
  have h2 : Nat.card A * Nat.card A ≤ Nat.card A * (p * Nat.card (A ⊓ C' : Subgroup G)) := by
    calc Nat.card A * Nat.card A ≤ Nat.card A * Nat.card C' := Nat.mul_le_mul_left _ h1
      _ = Nat.card (A ⊔ C' : Subgroup G) * Nat.card (A ⊓ C' : Subgroup G) := hprod.symm
      _ ≤ Nat.card B * Nat.card (A ⊓ C' : Subgroup G) := Nat.mul_le_mul_right _ hsupB
      _ = Nat.card A * (p * Nat.card (A ⊓ C' : Subgroup G)) := by rw [← hAcard]; ring
  have h3 : Nat.card A ≤ p * Nat.card (A ⊓ C' : Subgroup G) := Nat.le_of_mul_le_mul_left h2 hapos
  have h4 : p ^ 2 ≤ Nat.card (A ⊓ C' : Subgroup G) := by
    have hN : p ^ 4 ≤ Nat.card B := by
      rw [hBcard]
      exact Nat.pow_le_pow_right hpp.pos hm4
    have h5 : p ^ 2 * p ^ 2 ≤ p ^ 2 * Nat.card (A ⊓ C' : Subgroup G) := by
      calc p ^ 2 * p ^ 2 = p ^ 4 := by ring
        _ ≤ Nat.card B := hN
        _ = Nat.card A * p := hAcard.symm
        _ ≤ (p * Nat.card (A ⊓ C' : Subgroup G)) * p := Nat.mul_le_mul_right _ h3
        _ = p ^ 2 * Nat.card (A ⊓ C' : Subgroup G) := by ring
    exact Nat.le_of_mul_le_mul_left h5 (pow_pos hpp.pos 2)
  have hAC' : (A ⊓ C' : Subgroup G) = A ⊓ Subgroup.centralizer (T' : Set G) := by
    ext g
    simp only [hC', Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hAB h.1, h.2⟩⟩
  have hApgrp : IsPGroup p (A ⊓ C' : Subgroup G) :=
    (GLAIsBmax.isPGroup hB).to_le (inf_le_left.trans hAB)
  obtain ⟨D, hDle, hDc⟩ := exists_le_card_eq_pow hpp hApgrp h4
  have hDA : D ≤ A := hDle.trans inf_le_left
  have hDT : D ≤ Subgroup.centralizer (T' : Set G) := hDle.trans (inf_le_right.trans inf_le_right)
  have hDel : IsElemAbelian p D := isElemAbelian_mono hBel (hDA.trans hAB)
  have hT'Δ : T' ≤ GLADelta p D := by
    refine le_iInf fun b => le_iInf fun hbD => le_iInf fun hb1 => ?_
    have hbA : b ∈ A := hDA hbD
    have hbB : b ∈ B := hAB hbA
    have hTb : T' ≤ Subgroup.centralizer ({b} : Set G) := by
      intro t ht
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 (hDT hbD) t ht
    exact claimA hctx hp hS3 hS4o h1912 h1933 hd hB hbB hb1 (hAess b hbA hb1) hxB hx1
      (hT2.to_le hT'T) hBT' (hT'T.trans hTx) hTb (by rw [Subgroup.commutator_comm]; exact hT'B)
  exact delta_zero_contra hpp hp2 hΔ hB (hDA.trans hAB) hDel hDc (hT2.to_le hT'T) hT'Δ hBT'
    (by rw [hT'B]; exact hT'1)

end CFSG.LocalAnalysis.GLTheoremA
