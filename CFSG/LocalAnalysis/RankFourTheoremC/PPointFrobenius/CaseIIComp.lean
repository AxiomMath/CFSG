module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.CaseIIBasic
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Reduced3
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantConjugacy

public section

open Subgroup

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding (exists_mem_sylow_inf_component isElemAbelian_zpowers)
open CFSG.LocalAnalysis.RankThreeTheoremC
  (mem_normalizer_of_pow_mem isElemAbelian_iSup_zpowers add_le_pRank_of_commute)

theorem mem_normalizer_of_isComponentOf_of_pow_eq_one_abelian {Y : Type} [Group Y] [Finite Y]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hcore : primeComplementCore (G := Y) p = ⊥)
    (hab : ∀ Q : Sylow p Y, IsMulCommutative (Q : Subgroup Y)) {K : Subgroup Y}
    (hK : CFSG.Open.IsComponentOf K ⊤) {y : Y} (hy : y ^ p = 1) :
    y ∈ normalizer (K : Set Y) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hyK
  obtain ⟨R⟩ := (Sylow.nonempty : Nonempty (Sylow p Y))
  obtain ⟨t, htRK, hto, htC⟩ := exists_mem_sylow_inf_component hp hp2 hcore R hK
  have htK : t ∈ K := htRK.2
  have htp0 : t ^ p = 1 := hto ▸ pow_orderOf_eq_one t
  set f : ℕ → Subgroup Y := fun i => K.map (MulAut.conj (y ^ i)).toMonoidHom with hf
  have hfK : ∀ i, CFSG.Open.IsComponentOf (f i) ⊤ := fun i =>
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj (y ^ i)) K).mpr hK
  have key : ∀ i j : ℕ, i < j → j < p → f i ≠ f j := by
    intro i j hij hj hfij
    apply hyK
    refine mem_normalizer_of_pow_mem hp hy (m := j - i) ?_ ?_
    · exact (Nat.coprime_of_lt_prime (by omega) (by omega) hp).symm
    · rw [mem_normalizer_iff_map_conj_eq]
      have h1 : f j = (f (j - i)).map (MulAut.conj (y ^ i)).toMonoidHom := by
        simp only [hf]
        rw [← CFSG.RankThreeEvenClassification.Helpers.subgroup_map_conj_mul, ← pow_add,
          Nat.add_sub_cancel' hij.le]
      rw [h1] at hfij
      exact (map_injective (MulAut.conj (y ^ i)).injective hfij).symm
  have hKK : ∀ i j : Fin p, i ≠ j → f i.val ≤ centralizer (f j.val : Set Y) := by
    intro i j hij
    have hne : f i.val ≠ f j.val := by
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h' | h'
      · exact key _ _ h' j.2
      · exact (key _ _ h' i.2).symm
    exact commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ (hfK _) (hfK _) hne)
  set tt : ℕ → Y := fun i => y ^ i * t * (y ^ i)⁻¹ with htt
  have htt_succ : ∀ n, y * tt n * y⁻¹ = tt (n + 1) := by
    intro n
    simp only [htt, pow_succ']
    group
  have htt_mod : ∀ n, tt (n % p) = tt n := by
    intro n
    simp only [htt]
    rw [← pow_eq_pow_mod n hy]
  have htp : ∀ i : Fin p, tt i.val ^ p = 1 := by
    intro i
    simp only [htt]
    rw [conj_pow, htp0]
    simp
  have htKi : ∀ i : Fin p, tt i.val ∈ f i.val := fun i => ⟨t, htK, rfl⟩
  have htCi : ∀ i : Fin p, tt i.val ∉ centralizer (f i.val : Set Y) := by
    intro i hi
    apply htC
    rw [mem_centralizer_iff]
    intro k hk
    have h1 := mem_centralizer_iff.mp hi (y ^ i.val * k * (y ^ i.val)⁻¹) ⟨k, hk, rfl⟩
    have h2 : y ^ i.val * (k * t) * (y ^ i.val)⁻¹ = y ^ i.val * (t * k) * (y ^ i.val)⁻¹ := by
      calc y ^ i.val * (k * t) * (y ^ i.val)⁻¹
          = (y ^ i.val * k * (y ^ i.val)⁻¹) * tt i.val := by simp only [htt]; group
        _ = tt i.val * (y ^ i.val * k * (y ^ i.val)⁻¹) := h1
        _ = y ^ i.val * (t * k) * (y ^ i.val)⁻¹ := by simp only [htt]; group
    exact mul_left_cancel (mul_right_cancel h2)
  obtain ⟨hE, -⟩ := isElemAbelian_iSup_zpowers (Y := Y) hp
    (fun i : Fin p => f i.val) (fun i : Fin p => tt i.val) htp htKi htCi hKK Finset.univ
  set B : Subgroup Y := ⨆ i ∈ (Finset.univ : Finset (Fin p)), zpowers (tt i.val) with hB
  have hle : B.map (MulAut.conj y).toMonoidHom ≤ B := by
    simp only [hB, Subgroup.map_iSup]
    refine iSup₂_le fun i _ => ?_
    rw [MonoidHom.map_zpowers]
    have hs : (MulAut.conj y).toMonoidHom (tt i.val) = tt ((i.val + 1) % p) := by
      rw [htt_mod]
      exact htt_succ i.val
    rw [hs]
    exact le_iSup₂ (f := fun (j : Fin p) (_ : j ∈ (Finset.univ : Finset (Fin p))) =>
      zpowers (tt j.val)) ⟨(i.val + 1) % p, Nat.mod_lt _ hp.pos⟩ (Finset.mem_univ _)
  have hyB : y ∈ normalizer (B : Set Y) :=
    mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]))
  have hBp : IsPGroup p B := elementary_isPGroup p B hE
  have hyp : IsPGroup p (zpowers y) := elementary_isPGroup p _ (isElemAbelian_zpowers hy)
  have hsup : IsPGroup p (zpowers y ⊔ B : Subgroup Y) :=
    hyp.to_sup_of_normal_right' hBp (zpowers_le.mpr hyB)
  obtain ⟨Q, hQ⟩ := hsup.exists_le_sylow
  have hQab := hab Q
  have hyQ : y ∈ (Q : Subgroup Y) := hQ (mem_sup_left (mem_zpowers y))
  have htQ : t ∈ (Q : Subgroup Y) := by
    refine hQ (mem_sup_right ?_)
    have h0 : tt 0 = t := by simp [htt]
    rw [← h0]
    exact le_iSup₂ (f := fun (j : Fin p) (_ : j ∈ (Finset.univ : Finset (Fin p))) =>
      zpowers (tt j.val)) ⟨0, hp.pos⟩ (Finset.mem_univ _) (mem_zpowers _)
  have hcomm : y * t = t * y := setLike_mul_comm hyQ htQ
  have ht1 : tt 1 = t := by
    have : tt 1 = y * t * y⁻¹ := by simp [htt]
    rw [this, hcomm]
    group
  have hne01 : (⟨1, hp.one_lt⟩ : Fin p) ≠ ⟨0, hp.pos⟩ := fun h10 => by
    have := congrArg Fin.val h10
    simp at this
  have ht1f : t ∈ f (⟨1, hp.one_lt⟩ : Fin p).val := by
    have h1 := htKi ⟨1, hp.one_lt⟩
    rwa [show tt (⟨1, hp.one_lt⟩ : Fin p).val = t from ht1] at h1
  have hmem : t ∈ centralizer (f (⟨0, hp.pos⟩ : Fin p).val : Set Y) :=
    hKK ⟨1, hp.one_lt⟩ ⟨0, hp.pos⟩ hne01 ht1f
  have hf0 : f (⟨0, hp.pos⟩ : Fin p).val = K := by
    show f 0 = K
    have h1 : (MulAut.conj (y ^ 0)).toMonoidHom = MonoidHom.id Y := by
      ext g
      simp
    simp only [hf, h1, Subgroup.map_id]
  rw [hf0] at hmem
  exact htC hmem

namespace FrobCaseIIHyp

variable {p n : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y] {L U : Subgroup Y} {x : Y}

theorem le_normalizer_of_isComponentOf (h : FrobCaseIIHyp p n L U x) {K : Subgroup Y}
    (hK : CFSG.Open.IsComponentOf K ⊤) : L ≤ normalizer (K : Set Y) := by
  have hΩK : normalClosure {y : Y | y ^ p = 1} ≤ normalizer (K : Set Y) := by
    refine closure_le _ |>.mpr fun z hz => ?_
    obtain ⟨a, ha, hc⟩ := Group.mem_conjugatesOfSet_iff.mp hz
    obtain ⟨c, rfl⟩ := isConj_iff.mp hc
    refine mem_normalizer_of_isComponentOf_of_pow_eq_one_abelian h.prime
      (by have := h.five_le; omega) h.core_eq_bot h.abelian hK ?_
    rw [conj_pow, show a ^ p = 1 from ha, mul_one, mul_inv_cancel]
  have hUΩ : U ≤ normalClosure {y : Y | y ^ p = 1} := fun u hu =>
    subset_normalClosure (h.isElemAbelian.2 u hu)
  have := h.isSimpleGroup
  have : ((normalClosure {y : Y | y ^ p = 1}).subgroupOf L).Normal :=
    normalClosure_normal.subgroupOf L
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((normalClosure {y : Y | y ^ p = 1}).subgroupOf L) with h1 | h1
  · exfalso
    apply h.ne_bot
    have h2 : normalClosure {y : Y | y ^ p = 1} ⊓ L = ⊥ := by
      rw [← subgroupOf_map_subtype, h1, Subgroup.map_bot]
    exact le_bot_iff.mp (h2 ▸ le_inf hUΩ h.sylow.le)
  · exact (subgroupOf_eq_top.mp h1).trans hΩK

theorem exists_isComponentOf_not_le_centralizer (h : FrobCaseIIHyp p n L U x)
    (hCE : centralizer (CFSG.layer Y : Set Y) = ⊥) :
    ∃ K : Subgroup Y, CFSG.Open.IsComponentOf K ⊤ ∧ ¬ L ≤ centralizer (K : Set Y) := by
  by_contra hall
  push Not at hall
  have hLE : L ≤ centralizer (CFSG.layer Y : Set Y) := le_centralizer_iff.mpr
    (sSup_le fun K hK => le_centralizer_iff.mp (hall K ((CFSG.isComponent_iff_open K).mp hK)))
  rw [hCE] at hLE
  exact h.ne_bot (le_bot_iff.mp (h.sylow.le.trans hLE))

theorem map_conj_eq_of_isComponentOf (h : FrobCaseIIHyp p n L U x)
    (hL : CFSG.Open.IsComponentOf L ⊤) (g : Y) : L.map (MulAut.conj g).toMonoidHom = L := by
  by_contra hne
  have hLg : CFSG.Open.IsComponentOf (L.map (MulAut.conj g).toMonoidHom) ⊤ :=
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) L).mpr hL
  have hC : L.map (MulAut.conj g).toMonoidHom ≤ centralizer (L : Set Y) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hLg hL hne)
  have hV := CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p h.isElemAbelian
    (MulAut.conj g).toMonoidHom
  have hVc : Nat.card (U.map (MulAut.conj g).toMonoidHom) = p ^ n := by
    rw [card_map_of_injective (MulAut.conj g).injective, h.card_eq]
  have hVL : U.map (MulAut.conj g).toMonoidHom ≤ L.map (MulAut.conj g).toMonoidHom :=
    map_mono h.sylow.le
  have h4 := add_le_pRank_of_commute (P := ⊤) h.isElemAbelian hV h.card_eq hVc
    (fun a ha b hb => mem_centralizer_iff.mp (hC (hVL hb)) a (h.sylow.le ha))
    (disjoint_def.mpr fun hu hv => h.eq_one_of_mem_centralizer (h.sylow.le hu) (hC (hVL hv)))
    le_top le_top
  have := h.pRank_le
  have := h.three_le
  omega

end FrobCaseIIHyp

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
