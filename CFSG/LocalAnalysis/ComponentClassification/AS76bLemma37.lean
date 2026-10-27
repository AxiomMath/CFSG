module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma22Full
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma22FullL2

public section

namespace CFSG.ComponentClassification.AS76b

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Lemma34 Lemma22 Lemma37 Lemma22Full
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem exists_mulEquiv_sl_two_of_isSylowOf
    {Y P : Subgroup G} (hY : CFSG.Open.IsQuasisimple ↥Y) (hZ : Odd (Nat.card (center ↥Y)))
    (hB : fusionIsBenderGroup (↥Y ⧸ center ↥Y)) (hP : IsSylowOf 2 P Y)
    (hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) :
    ∃ n : ℕ, 2 ≤ n ∧ 2 ^ n = Nat.card P ∧ Nonempty (↥Y ≃* SL(2, GaloisField 2 n)) := by
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  have hQc : ∀ a ∈ (Q : Subgroup Y), ∀ b ∈ (Q : Subgroup Y), a * b = b * a := by
    intro a ha b hb
    rw [hQ, mem_subgroupOf] at ha hb
    exact Subtype.ext (hPc _ ha _ hb)
  obtain ⟨n, hn, hcard, he⟩ := exists_mulEquiv_sl_two hY hZ hB Q hQc
  refine ⟨n, hn, ?_, he⟩
  rw [hcard, hQ]
  exact Nat.card_congr (subgroupOfEquivOfLe hP.le).toEquiv

theorem lemma37_bender_of_le
    (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    {A W L R : Subgroup G} (hA : Hyp31 A) (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    (hWA : W ≤ A) (hL : CFSG.Open.IsQuasisimple ↥L) (hLA : L ≤ A ⊓ centralizer (W : Set G))
    (hNL : normalizer (A : Set G) ⊓ centralizer (W : Set G) ≤ normalizer (L : Set G))
    (hRL : IsSylowOf 2 R
      (centralizer (W : Set G) ⊓ centralizer (L : Set G) ⊓ normalizer (R : Set G))) :
    standardComponentIsStandard (L.subgroupOf (centralizer (W : Set G))) ∨
      ∃ c ∈ centralizer (W : Set G), conj L c ≤ centralizer (L : Set G) ∧
        centralizer (W : Set G) ⊓ centralizer (L : Set G) ≤ normalizer (conj L c : Set G) ∧
        R ≤ conj L c ∧
        ∃ n : ℕ, 2 ≤ n ∧ 2 ^ n = Nat.card R ∧ Nonempty (↥L ≃* SL(2, GaloisField 2 n)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKte := tightlyEmbedded_centralizer hA.standard
  have hK'te := tightlyEmbedded_oddCoreIn_sup h4 h32 h34 hA hR
  have hK'K : oddCoreIn (centralizer (A : Set G)) ⊔ R ≤ centralizer (A : Set G) :=
    sup_le (oddCoreIn_le _) hR.le
  have hKW : centralizer (A : Set G) ≤ centralizer (W : Set G) :=
    centralizer_le fun x hx => hWA hx
  have hLW : L ≤ centralizer (W : Set G) := hLA.trans inf_le_right
  have hRCL := isSylowOf_of_isSylowOf_inf_normalizer hRL
  have hNK' : normalizer ((oddCoreIn (centralizer (A : Set G)) ⊔ R : Subgroup G) : Set G) ⊓
      centralizer (W : Set G) ≤ normalizer (L : Set G) := by
    intro x hx
    obtain ⟨hxN, hxW⟩ := mem_inf.mp hx
    have hxA : x ∈ normalizer (A : Set G) := by
      rw [← normalizer_centralizer_eq hA.standard]
      exact normalizer_le_of_le_of_even hKte hK'K hK'te.1 hxN
    exact hNL ⟨hxA, hxW⟩
  rcases lemma22_bender_in (hK'K.trans hKW) hLW (isSolvable_oddCoreIn_sup hR) hK'te
      (hR.of_le le_sup_right hK'K) hL hNK' hRCL with
    h | ⟨c, hc, hc1, hc2, hc3, hodd, hB⟩
  · exact Or.inl h
  · right
    refine ⟨c, hc, hc1, hc2, hc3, ?_⟩
    have hcW : conj L c ≤ centralizer (W : Set G) := conj_le_of_mem hLW hc
    have hRc : IsSylowOf 2 R (conj L c) := hRCL.of_le hc3 (le_inf hcW hc1)
    have hRe : IsElemAbelian 2 R := h32 G A hA R hR
    have hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hRe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    let e : ↥L ≃* ↥(conj L c) :=
      L.equivMapOfInjective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective
    obtain ⟨n, hn, hcard, ⟨f⟩⟩ := exists_mulEquiv_sl_two_of_isSylowOf (isQuasisimple_conj hL c)
      (by rw [← card_center_congr e]; exact hodd)
      (CFSG.QuasithinUnique.RankOneRecog.fusionIsBenderGroup_of_mulEquiv (quotientCenterCongr e)
        hB) hRc hRcomm
    exact ⟨n, hn, hcard, ⟨e.trans f⟩⟩

theorem lemma37_bender
    (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    {A W R : Subgroup G} (hA : Hyp31 A) (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    (hWA : W ≤ A) (hL : CFSG.Open.IsQuasisimple ↥(layerCentralizer A W))
    (hRL : IsSylowOf 2 R (centralizer (W : Set G) ⊓
      centralizer (layerCentralizer A W : Set G) ⊓ normalizer (R : Set G))) :
    standardComponentIsStandard ((layerCentralizer A W).subgroupOf (centralizer (W : Set G))) ∨
      ∃ c ∈ centralizer (W : Set G),
        conj (layerCentralizer A W) c ≤ centralizer (layerCentralizer A W : Set G) ∧
        centralizer (W : Set G) ⊓ centralizer (layerCentralizer A W : Set G) ≤
          normalizer (conj (layerCentralizer A W) c : Set G) ∧
        R ≤ conj (layerCentralizer A W) c ∧
        ∃ n : ℕ, 2 ≤ n ∧ 2 ^ n = Nat.card R ∧
          Nonempty (↥(layerCentralizer A W) ≃* SL(2, GaloisField 2 n)) :=
  lemma37_bender_of_le h4 h32 h34 hA hR hWA hL (layerCentralizer_le A W)
    (normalizer_inf_le_normalizer_layerCentralizer A W) hRL

end CFSG.ComponentClassification.AS76b
