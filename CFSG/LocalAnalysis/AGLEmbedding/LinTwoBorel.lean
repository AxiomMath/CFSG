module

import CFSG.LocalAnalysis.AGLEmbedding.LinTwoAutRank
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoBorelAux
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoBorelSolvable
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoReduced
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoTorus
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoUnipotentCentralizer
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCatalog
public import CFSG.LocalAnalysis.AGLEmbedding.RankLemmas
public import CFSG.LocalAnalysis.AGLEmbedding.ReducedQuotient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

section Borel

variable {Y : Type} [Group Y] [Finite Y]

theorem le_sylow_inf_of_le_normalizer {p : ℕ} [Fact p.Prime] (K : Subgroup Y) [K.Normal]
    (Rb : Sylow p Y) {V : Subgroup Y} (hV : IsPGroup p V) (hVK : V ≤ K)
    (hVN : V ≤ Subgroup.normalizer (((Rb : Subgroup Y) ⊓ K : Subgroup Y) : Set Y)) :
    V ≤ (Rb : Subgroup Y) ⊓ K := by
  obtain ⟨T, hT⟩ := exists_sylow_map_subtype_eq_inf K Rb
  have hmemT : ∀ k : K, k ∈ (T : Subgroup K) ↔ (k : Y) ∈ (Rb : Subgroup Y) ⊓ K := fun k => by
    rw [← hT]
    exact (Subgroup.mem_map_iff_mem K.subtype_injective).symm
  have h := (hV.comap_subtype (K := K)).inf_normalizer_sylow T
  intro v hv
  have hv' : (⟨v, hVK hv⟩ : K) ∈
      V.comap K.subtype ⊓ Subgroup.normalizer ((T : Subgroup K) : Set K) := by
    refine ⟨hv, Subgroup.mem_normalizer_iff.mpr fun k => ?_⟩
    rw [hmemT, hmemT]
    exact Subgroup.mem_normalizer_iff.mp (hVN hv) k
  exact (hmemT _).mp (h.le hv').2

theorem le_normalizer_sylow_inf {p : ℕ} [Fact p.Prime] (K : Subgroup Y) [K.Normal]
    (Rb : Sylow p Y) {Y₀ : Subgroup Y} (hUY₀ : (Rb : Subgroup Y) ⊓ K ≤ Y₀)
    (hY₀K : Y₀ ⊓ K ≤ Subgroup.normalizer (((Rb : Subgroup Y) ⊓ K : Subgroup Y) : Set Y)) :
    Y₀ ≤ Subgroup.normalizer (((Rb : Subgroup Y) ⊓ K : Subgroup Y) : Set Y) := by
  have hU : IsPGroup p ((Rb : Subgroup Y) ⊓ K : Subgroup Y) := Rb.isPGroup'.to_inf_left
  have hconj : ∀ y ∈ Y₀, ∀ u ∈ (Rb : Subgroup Y) ⊓ K, y * u * y⁻¹ ∈ (Rb : Subgroup Y) ⊓ K := by
    intro y hy u hu
    have hVK : ((Rb : Subgroup Y) ⊓ K).map (MulAut.conj y).toMonoidHom ≤ K := by
      rintro _ ⟨v, hv, rfl⟩
      exact (inferInstance : K.Normal).conj_mem v hv.2 y
    have hVY₀ : ((Rb : Subgroup Y) ⊓ K).map (MulAut.conj y).toMonoidHom ≤ Y₀ := by
      rintro _ ⟨v, hv, rfl⟩
      exact Y₀.mul_mem (Y₀.mul_mem hy (hUY₀ hv)) (Y₀.inv_mem hy)
    exact le_sylow_inf_of_le_normalizer K Rb (hU.map _) hVK
      (fun x hx => hY₀K ⟨hVY₀ hx, hVK hx⟩) ⟨u, hu, rfl⟩
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨hconj y hy u, fun h => ?_⟩
  have h' := hconj y⁻¹ (Y₀.inv_mem hy) _ h
  have hu : y⁻¹ * (y * u * y⁻¹) * y⁻¹⁻¹ = u := by group
  rwa [hu] at h'

theorem isSolvable_of_le_normalizer_of_psl2GF {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hn : 1 ≤ n) {K : Subgroup Y} [K.Normal] (e : K ≃* PSL2GF p n)
    (hC : Subgroup.centralizer (K : Set Y) = ⊥) (Rb : Sylow p Y) {Y₀ : Subgroup Y}
    (hY₀ : Y₀ ≤ Subgroup.normalizer (((Rb : Subgroup Y) ⊓ K : Subgroup Y) : Set Y)) :
    Group.IsSolvable Y₀ := by
  let f : Y →* MulAut (PSL2GF p n) :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := K))
  have hinj : Function.Injective (MulAut.conjNormal (H := K) : Y →* MulAut K) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_conjNormal_eq_centralizer, hC]
  have hf : Function.Injective f := (MulAut.congr e).injective.comp hinj
  have hfe : ∀ (y : Y) (k : K), f y (e k) = e (MulAut.conjNormal y k) := fun y k => by
    simp [f, MulAut.congr]
  obtain ⟨T, hT⟩ := exists_sylow_map_subtype_eq_inf K Rb
  have hmemT : ∀ k : K, k ∈ (T : Subgroup K) ↔ (k : Y) ∈ (Rb : Subgroup Y) ⊓ K := fun k => by
    rw [← hT]
    exact (Subgroup.mem_map_iff_mem K.subtype_injective).symm
  have hes : Function.Surjective (e : K →* PSL2GF p n) := e.surjective
  set U : Sylow p (PSL2GF p n) := T.mapSurjective hes with hU
  have hUmem : ∀ k : K, e k ∈ (U : Subgroup (PSL2GF p n)) ↔ k ∈ (T : Subgroup K) := fun k => by
    rw [hU, Sylow.coe_mapSurjective]
    exact Subgroup.mem_map_iff_mem (f := (e : K →* PSL2GF p n)) e.injective
  have hA : ∀ α ∈ Y₀.map f,
      (U : Subgroup (PSL2GF p n)).map (α : PSL2GF p n ≃* PSL2GF p n).toMonoidHom = U := by
    rintro _ ⟨y, hy, rfl⟩
    refine Subgroup.eq_of_le_of_card_ge (fun z hz => ?_) (by
      rw [Subgroup.card_map_of_injective
        (f := ((f y : PSL2GF p n ≃* PSL2GF p n)).toMonoidHom) (f y).injective])
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
    obtain ⟨k, rfl⟩ := e.surjective x
    rw [hUmem, hmemT] at hx
    change f y (e k) ∈ (U : Subgroup (PSL2GF p n))
    rw [hfe, hUmem, hmemT, MulAut.conjNormal_apply]
    exact (Subgroup.mem_normalizer_iff.mp (hY₀ hy) _).mp hx
  have := kFactL2SylowNormalizerSolvable p n hp2 hn U (Y₀.map f) hA
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Y₀.equivMapOfInjective f hf).toMonoidHom) (Y₀.equivMapOfInjective f hf).injective

theorem pRank_top_le_of_psl2GF {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 1 ≤ n)
    {K : Subgroup Y} [K.Normal] (hK : Nonempty (K ≃* PSL2GF p n))
    (hC : Subgroup.centralizer (K : Set Y) = ⊥) : Open.pRank p (⊤ : Subgroup Y) ≤ n := by
  obtain ⟨e⟩ := hK
  let f : Y →* MulAut (PSL2GF p n) :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := K))
  have hinj : Function.Injective (MulAut.conjNormal (H := K) : Y →* MulAut K) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_conjNormal_eq_centralizer, hC]
  have hf : Function.Injective f := (MulAut.congr e).injective.comp hinj
  apply csSup_le'
  rintro k ⟨E, -, hE, hcard⟩
  have h := kFactL2AutElemRank p n hp2 hn (E.map f) (elementary_abelian_map p hE f)
  rw [Subgroup.card_map_of_injective hf, hcard] at h
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp h

theorem stmtLinTwoBorel :
    ∀ {Y : Type} [Group Y] [Finite Y] {p n : ℕ} [Fact p.Prime] (Rb : Sylow p Y) (Y₀ K : Subgroup Y),
      ReducedNongeneration p Y Rb Y₀ → 3 ≤ n → K.Normal → Nonempty (K ≃* PSL2GF p n) →
      Subgroup.centralizer (K : Set Y) = ⊥ →
      Y₀ ⊓ K = K ⊓ Subgroup.normalizer ((((Rb : Subgroup Y) ⊓ K : Subgroup Y)) : Set Y) ∧
      (∀ W : Subgroup Y, W ≤ Y₀ → Y₀ ≤ Subgroup.normalizer (W : Set Y) →
        W = ⊥ ∨ (Rb : Subgroup Y) ⊓ K ≤ W) ∧
      (∀ W : Subgroup Y, W ≤ Y₀ → Y₀ ≤ Subgroup.normalizer (W : Set Y) → IsPGroup p W →
        W ≤ (Rb : Subgroup Y) ⊓ K) ∧
      Group.IsSolvable Y₀ ∧ Open.pRank p (⊤ : Subgroup Y) ≤ n := by
  intro Y _ _ p n _ Rb Y₀ K hred hn hKn hK hC
  obtain ⟨e⟩ := hK
  have hp : p.Prime := hred.prime
  have hp2 : p ≠ 2 := hred.ne_two
  have hn1 : 1 ≤ n := by omega
  have h2 : (2 : GaloisField p n) ≠ 0 :=
    Ring.two_ne_zero (by rw [ringChar.eq (GaloisField p n) p]; exact hp2)
  set U : Subgroup Y := (Rb : Subgroup Y) ⊓ K
  obtain ⟨hUab, hUcard⟩ := isElemAbelian_sylow_inf_of_psl2GF hn1 e Rb
  have hrank : 3 ≤ Open.pRank p U :=
    hn.trans (le_csSup (pRank_bddAbove p hp _) ⟨_, le_rfl, hUab, hUcard⟩)
  have hN : Subgroup.normalizer (U : Set Y) ≤ Y₀ :=
    (normalizer_le_weakCore p inf_le_left (le_trans (by norm_num) hrank)
      (hrank.trans (pRank_mono p hp le_sup_left))).trans hred.weakCore_le
  have hKY₀ : ¬ K ≤ Y₀ := not_le_of_weakCore_le hp Rb hred.weakCore_le hred.ne_top hrank
  have hY₀K : Y₀ ⊓ K ≤ Subgroup.normalizer (U : Set Y) :=
    inf_le_normalizer_of_psl2GF hp2 hn1 e Rb hN hKY₀
  have hCU : Subgroup.centralizer (U : Set Y) ≤ U :=
    centralizer_sylow_inf_le_of_psl2GF kFactL2UnipotentCentralizer hp2 hn1 hKn ⟨e⟩ hC Rb
  have hUY₀ : U ≤ Y₀ := Subgroup.le_normalizer.trans hN
  have hY₀U : Y₀ ≤ Subgroup.normalizer (U : Set Y) := le_normalizer_sylow_inf K Rb hUY₀ hY₀K
  obtain ⟨ψ, hψinj, hψU, hψc⟩ :=
    exists_torus_param_of_mulEquiv_psl2GF hp2 hn1 e U inf_le_right hUcard
  have hcY₀ : ∀ μ : (GaloisField p n)ˣ, ∃ c ∈ K, c ∈ Y₀ ∧ ∀ a : Multiplicative (GaloisField p n),
      c * ψ a * c⁻¹ =
        ψ (Multiplicative.ofAdd ((μ : GaloisField p n) ^ 2 * Multiplicative.toAdd a)) := by
    intro μ
    obtain ⟨c, hcK, hc⟩ := hψc μ
    exact ⟨c, hcK, hN (hψU ▸ mem_normalizer_range_of_torus ψ μ.ne_zero hc), hc⟩
  refine ⟨le_antisymm (fun y hy => ⟨hy.2, hY₀K hy⟩) (fun y hy => ⟨hN hy.2, hy.1⟩), ?_, ?_,
    isSolvable_of_le_normalizer_of_psl2GF hp2 hn1 e hC Rb hY₀U,
    pRank_top_le_of_psl2GF hp2 hn1 ⟨e⟩ hC⟩
  ·
    intro W hWY₀ hY₀W
    rcases (W ⊓ U).bot_or_exists_ne_one with hWU | ⟨g, ⟨hgW, hgU⟩, hg1⟩
    ·
      left
      rw [eq_bot_iff]
      intro w hw
      have hwC : w ∈ Subgroup.centralizer (U : Set Y) := by
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        have hcW : w * u * w⁻¹ * u⁻¹ ∈ W := by
          have h := (Subgroup.mem_normalizer_iff.mp (hY₀W (hUY₀ hu)) w⁻¹).mp (W.inv_mem hw)
          simpa only [mul_assoc] using W.mul_mem hw h
        have hcomm : w * u * w⁻¹ * u⁻¹ ∈ W ⊓ U := ⟨hcW,
          U.mul_mem ((Subgroup.mem_normalizer_iff.mp (hY₀U (hWY₀ hw)) u).mp hu) (U.inv_mem hu)⟩
        rw [hWU, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hcomm
        exact hcomm.symm
      have hwWU : w ∈ W ⊓ U := ⟨hw, hCU hwC⟩
      rwa [hWU] at hwWU
    ·
      right
      rw [← hψU] at hgU ⊢
      obtain ⟨a, rfl⟩ := hgU
      refine range_le_of_torus h2 ψ (fun μ => ?_) hgW hg1
      obtain ⟨c, -, hcY₀, hc⟩ := hcY₀ μ
      exact ⟨c, hY₀W hcY₀, hc⟩
  ·
    intro W hWY₀ hY₀W hWp w hw
    have hWK : W ⊓ K ≤ U := le_sylow_inf_of_le_normalizer K Rb hWp.to_inf_left inf_le_right
      (fun x hx => hY₀K ⟨hWY₀ hx.1, hx.2⟩)
    obtain ⟨k, hk⟩ := hWp ⟨w, hw⟩
    have hwk : w ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hwU : ∀ a : Multiplicative (GaloisField p n), w * ψ a * w⁻¹ ∈ ψ.range := by
      intro a
      rw [hψU]
      exact (Subgroup.mem_normalizer_iff.mp (hY₀U (hWY₀ hw)) _).mp (hψU ▸ ⟨a, rfl⟩)
    have hwc : ∀ μ : (GaloisField p n)ˣ, ∃ c : Y, (∀ a : Multiplicative (GaloisField p n),
        c * ψ a * c⁻¹ =
          ψ (Multiplicative.ofAdd ((μ : GaloisField p n) ^ 2 * Multiplicative.toAdd a))) ∧
        w * c * w⁻¹ * c⁻¹ ∈ ψ.range := by
      intro μ
      obtain ⟨c, hcK, hcY₀, hc⟩ := hcY₀ μ
      have hcW : w * c * w⁻¹ * c⁻¹ ∈ W := by
        have h := (Subgroup.mem_normalizer_iff.mp (hY₀W hcY₀) w⁻¹).mp (W.inv_mem hw)
        simpa only [mul_assoc] using W.mul_mem hw h
      exact ⟨c, hc, hψU ▸ hWK ⟨hcW, K.mul_mem (hKn.conj_mem c hcK w) (K.inv_mem hcK)⟩⟩
    apply hCU
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    rw [← hψU] at hu
    obtain ⟨a, rfl⟩ := hu
    have h := conj_eq_of_torus p h2 ψ hψinj hwU hwc hwk a
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm

end Borel

end CFSG.AGLEmbedding
