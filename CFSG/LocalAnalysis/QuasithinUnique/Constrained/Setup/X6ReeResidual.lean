module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ReeContainment
public import CFSG.LieType.Ree.BorelOvergroupClassification

public section

namespace CFSG.QuasithinUnique.Setup.X6

open CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.ABGLocalTools
open scoped Pointwise commutatorElement

section Containment

variable {t : ReeTag} {K : Type} [Field K] [Finite K] [CharP K t.prime] {a : ℕ}

theorem conj_mem_reeFixedTorus
    {m h : ModGL t.tag K} (hm : m ∈ t.reeFixedMonomial K a)
    (hh : h ∈ t.reeFixedTorus K a) : m * h * m⁻¹ ∈ t.reeFixedTorus K a := by
  have hN : ((t.reeFixedTorus K a).subgroupOf (t.reeFixedMonomial K a)).Normal := inferInstance
  have hHN : t.reeFixedTorus K a ≤ t.reeFixedMonomial K a :=
    inf_le_inf_right _ torusGroup_le_monomialSubgroup
  exact Subgroup.mem_subgroupOf.1
    (hN.conj_mem ⟨h, hHN hh⟩ (Subgroup.mem_subgroupOf.2 hh) ⟨m, hm⟩)

theorem canonicalRep_inv_mul_mul_mem_reeFixedPosUnipotent
    {w : WeylGroup t.tag}
    (hw : w ∈ t.relWeylRee) {S : Set (Fin t.tag.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot t.tag α)
    (hpos : ∀ α ∈ S, 0 < height (w⁻¹ • α)) {g : ModGL t.tag K}
    (hg : g ∈ rootSpan t.tag K S ⊓ t.reeGamma K a) :
    (canonicalRep (coxeterSystem t.tag) K w)⁻¹ * g * canonicalRep (coxeterSystem t.tag) K w ∈
      t.reeFixedPosUnipotent K a := by
  set n := canonicalRep (coxeterSystem t.tag) K w
  have hn : n ∈ t.reeGamma K a := (canonicalRep_mem_reeFixedMonomial t K a hw).2
  obtain ⟨hgS, hgΓ⟩ := Subgroup.mem_inf.1 hg
  have hmap := (canonical_weyl_root_transport t.tag K).1 w ((fun α => w⁻¹ • α) '' S)
    (by rintro _ ⟨α, hα, rfl⟩; exact IsRoot.smul (hS α hα) w⁻¹)
  rw [Set.image_image, Set.image_congr fun α _ => smul_inv_smul w α, Set.image_id'] at hmap
  rw [← hmap] at hgS
  obtain ⟨y, hy, hyg⟩ := hgS
  have hyg' : n * y * n⁻¹ = g := hyg
  have e : n⁻¹ * g * n = y := by rw [← hyg']; group
  rw [e]
  have hyΓ : y ∈ t.reeGamma K a := by
    rw [← e]
    exact mul_mem (mul_mem (inv_mem hn) hgΓ) hn
  refine Subgroup.mem_inf.2 ⟨rootSpan_mono ?_ hy, hyΓ⟩
  rintro _ ⟨α, hα, rfl⟩
  exact ⟨IsRoot.smul (hS α hα) w⁻¹, hpos α hα⟩

theorem reeFixedOrbitNegUnipotent_le_of_posUnipotent
    {A : Subgroup (ModGL t.tag K)}
    (hU : t.reeFixedPosUnipotent K a ≤ A) {w : WeylGroup t.tag} (hw : w ∈ t.relWeylRee)
    {h : ModGL t.tag K} (hh : h ∈ t.reeFixedTorus K a)
    (hz : h * canonicalRep (coxeterSystem t.tag) K w ∈ A) {j : Fin t.fixedOrbitCount}
    (hneg : ∀ α ∈ t.fixedOrbitRoots j, height (w⁻¹ • α) < 0) :
    t.reeFixedOrbitNegUnipotent K a j ≤ A := by
  intro y hy
  set n := canonicalRep (coxeterSystem t.tag) K w
  have hSr : ∀ α ∈ Neg.neg '' t.fixedOrbitRoots j, IsRoot t.tag α := fun _ hα =>
    isRoot_of_mem_neg_fixedOrbitRoots hα
  have hSp : ∀ α ∈ Neg.neg '' t.fixedOrbitRoots j, 0 < height (w⁻¹ • α) := by
    rintro _ ⟨β, hβ, rfl⟩
    rw [smul_neg, height_neg]
    linarith [hneg β hβ]
  obtain ⟨hyS, hyΓ⟩ := Subgroup.mem_inf.1 hy
  have hhT : h ∈ torusGroup t.tag K := (Subgroup.mem_inf.1 hh).1
  have hhΓ : h ∈ t.reeGamma K a := (Subgroup.mem_inf.1 hh).2
  have hg : h⁻¹ * y * h ∈ rootSpan t.tag K (Neg.neg '' t.fixedOrbitRoots j) ⊓ t.reeGamma K a := by
    refine Subgroup.mem_inf.2 ⟨?_, mul_mem (mul_mem (inv_mem hhΓ) hyΓ) hhΓ⟩
    have := (Subgroup.mem_normalizer_iff.1
      (torusGroup_le_normalizer_rootSpan (K := K) hSr (inv_mem hhT)) y).1 hyS
    rw [inv_inv] at this
    exact this
  have h1 := canonicalRep_inv_mul_mul_mem_reeFixedPosUnipotent hw hSr hSp hg
  have e : y = (h * n) * (n⁻¹ * (h⁻¹ * y * h) * n) * (h * n)⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem hz (hU h1)) (inv_mem hz)

end Containment

section LargeRee

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem canonicalRep_fixedOrbitElement_mem_of_reduced_of_posUnipotent
    {A : Subgroup (ModGL F4.tag K)} (hU : F4.reeFixedPosUnipotent K a ≤ A) :
    ∀ (ω : List (Fin F4.fixedOrbitCount)) {w : WeylGroup F4.tag},
      (ω.map F4.fixedOrbitElement).prod = w → ω.length = F4.fixedRelLength w →
      ∀ h ∈ F4.reeFixedTorus K a, h * canonicalRep (coxeterSystem F4.tag) K w ∈ A →
      ∀ j ∈ ω, canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈ A
  | [], _, _, _, _, _, _, j, hj => absurd hj List.not_mem_nil
  | i :: ω, w, hω, hred, h, hh, hz, j, hj => by
    have hw : w ∈ F4.relWeylRee := hω ▸ list_prod_map_fixedOrbitElement_mem (i :: ω)
    have hwv : w = F4.fixedOrbitElement i * (ω.map F4.fixedOrbitElement).prod := by
      rw [← hω, List.map_cons, List.prod_cons]
    have hzw : F4.fixedOrbitElement i * w = (ω.map F4.fixedOrbitElement).prod := by
      rw [hwv, ← mul_assoc, fixedOrbitElement_mul_self, one_mul]
    rw [List.length_cons] at hred
    have hneg : ∀ α ∈ F4.fixedOrbitRoots i, height (w⁻¹ • α) < 0 := by
      rcases fixedOrbitRoots_sign (inv_mem hw) i with h' | h'
      · have h1 := (lengths_fixedOrbitElement_mul_of_pos hw h').1
        rw [hzw] at h1
        have h2 := fixedRelLength_le (t := F4) (ω := ω) rfl
        omega
      · exact h'
    have hY := reeFixedOrbitNegUnipotent_le_of_posUnipotent hU hw hh hz hneg
    have hMi : F4.reeLocalBlock K a i ≤ A :=
      sup_le ((reeFixedOrbitUnipotent_le_reeFixedPosUnipotent i).trans hU) hY
    have hi : canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement i) ∈ A :=
      hMi (canonicalRep_fixedOrbitElement_mem_reeLocalBlock i)
    have hvred : ω.length = F4.fixedRelLength (ω.map F4.fixedOrbitElement).prod := by
      have h1 := (lengths_fixedOrbitElement_mul_of_neg hw hneg).1
      rw [hzw] at h1
      omega
    obtain ⟨h', hh', hm⟩ := exists_canonicalRep_inv_mul_eq (K := K) (a := a)
      (fixedOrbitElement_mem i) hw
    rw [fixedOrbitElement_inv, hzw] at hm
    set N := canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement i)
    set W := canonicalRep (coxeterSystem F4.tag) K w
    set V := canonicalRep (coxeterSystem F4.tag) K (ω.map F4.fixedOrbitElement).prod
    have hNm : N ∈ F4.reeFixedMonomial K a :=
      canonicalRep_mem_reeFixedMonomial F4 K a (fixedOrbitElement_mem i)
    have hVm : V ∈ F4.reeFixedMonomial K a :=
      canonicalRep_mem_reeFixedMonomial F4 K a (list_prod_map_fixedOrbitElement_mem ω)
    have h1 : N⁻¹ * h * N ∈ F4.reeFixedTorus K a := by
      have := conj_mem_reeFixedTorus (a := a) (inv_mem hNm) hh
      rwa [inv_inv] at this
    have h2 : V * h' * V⁻¹ ∈ F4.reeFixedTorus K a := conj_mem_reeFixedTorus hVm hh'
    have hWeq : W = N * (V * h') := by rw [← hm]; group
    have e : ((N⁻¹ * h * N) * (V * h' * V⁻¹)) * V = N⁻¹ * (h * W) := by rw [hWeq]; group
    have hz' : ((N⁻¹ * h * N) * (V * h' * V⁻¹)) * V ∈ A := by
      rw [e]
      exact mul_mem (inv_mem hi) hz
    rcases List.mem_cons.1 hj with rfl | hj'
    · exact hi
    · exact canonicalRep_fixedOrbitElement_mem_of_reduced_of_posUnipotent hU ω rfl hvred _
        (mul_mem h1 h2) hz' j hj'

theorem le_reeParabolic_of_posUnipotent_le
    {M : Subgroup (ModGL F4.tag K)}
    (hMΓ : M ≤ F4.reeGamma K a) (hU : F4.reeFixedPosUnipotent K a ≤ M) :
    M ≤ F4.reeParabolic K a
      {j | canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈ M} := by
  intro g hg
  have hgΓ : g ∈ (F4.reeGamma K a : Set (ModGL F4.tag K)) := hMΓ hg
  rw [reeGamma_eq_iUnion_reeFixedBruhatCell] at hgΓ
  obtain ⟨⟨w, hw⟩, hgw⟩ := Set.mem_iUnion.1 hgΓ
  obtain ⟨b, hb, b', hb', hgb⟩ := mem_reeFixedBruhatCell.1 hgw
  obtain ⟨u₁, hu₁, h₁, hh₁, rfl⟩ : b ∈ (F4.reeFixedPosUnipotent K a : Set (ModGL F4.tag K)) *
      (F4.reeFixedTorus K a : Set (ModGL F4.tag K)) := by
    rw [← reeFixedBorel_eq_mul']
    exact hb
  obtain ⟨h₂, hh₂, u₂, hu₂, rfl⟩ : b' ∈ (F4.reeFixedTorus K a : Set (ModGL F4.tag K)) *
      (F4.reeFixedPosUnipotent K a : Set (ModGL F4.tag K)) := by
    rw [← reeFixedBorel_eq_mul]
    exact hb'
  have hnm : canonicalRep (coxeterSystem F4.tag) K w ∈ F4.reeFixedMonomial K a :=
    canonicalRep_mem_reeFixedMonomial F4 K a hw
  have hh : canonicalRep (coxeterSystem F4.tag) K w * h₂ *
      (canonicalRep (coxeterSystem F4.tag) K w)⁻¹ ∈ F4.reeFixedTorus K a :=
    conj_mem_reeFixedTorus hnm hh₂
  have hz : (h₁ * (canonicalRep (coxeterSystem F4.tag) K w * h₂ *
      (canonicalRep (coxeterSystem F4.tag) K w)⁻¹)) * canonicalRep (coxeterSystem F4.tag) K w ∈
        M := by
    have e : (h₁ * (canonicalRep (coxeterSystem F4.tag) K w * h₂ *
        (canonicalRep (coxeterSystem F4.tag) K w)⁻¹)) * canonicalRep (coxeterSystem F4.tag) K w =
        u₁⁻¹ * g * u₂⁻¹ := by
      rw [← hgb]; group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (hU hu₁)) hg) (inv_mem (hU hu₂))
  obtain ⟨k, hk⟩ := exists_fixedRelElt_eq hw
  have hred : (F4.fixedRelWord k).length = F4.fixedRelLength w := by
    rw [← hk, fixedRelLength_fixedRelElt]
  have hletters := canonicalRep_fixedOrbitElement_mem_of_reduced_of_posUnipotent hU
    (F4.fixedRelWord k) hk hred _ (mul_mem hh₁ hh) hz
  have hnP := canonicalRep_list_prod_mem_reeParabolic (K := K) (a := a)
    (J := {j | canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈ M})
    (F4.fixedRelWord k) hletters
  change canonicalRep (coxeterSystem F4.tag) K (F4.fixedRelElt k) ∈ _ at hnP
  rw [hk] at hnP
  rw [← hgb]
  exact mul_mem (mul_mem (reeFixedBorel_le_reeParabolic F4 K a _ (mul_mem
    (reeFixedPosUnipotent_le_reeFixedBorel hu₁) (reeFixedTorus_le_reeFixedBorel hh₁))) hnP)
    (reeFixedBorel_le_reeParabolic F4 K a _ (mul_mem (reeFixedTorus_le_reeFixedBorel hh₂)
      (reeFixedPosUnipotent_le_reeFixedBorel hu₂)))

theorem large_Ree_positive_root_overgroup_parabolic_containment
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {M : Subgroup (ModGL F4.tag K)}
    (hMΓ : M ≤ F4.reeGamma K a) (hU : F4.reeFixedPosUnipotent K a ≤ M) :
    M ≤ F4.reeParabolic K a
        {j | canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈ M} ∧
    ({j | canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈ M} = Set.univ ↔
      M = F4.reeGamma K a) ∧
    (M ≠ F4.reeGamma K a → ∃ J : Set (Fin F4.fixedOrbitCount), J ≠ Set.univ ∧
      M ≤ F4.reeParabolic K a J ∧ F4.reeParabolic K a J ≠ F4.reeGamma K a) := by
  have hle := le_reeParabolic_of_posUnipotent_le hMΓ hU
  have hiff : {j | canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈ M} =
      Set.univ ↔ M = F4.reeGamma K a := by
    constructor
    · intro h
      refine le_antisymm hMΓ ?_
      rw [reeGamma_eq_iSup_reeLocalBlock (t := F4) hK
        reeFixedPosUnipotent_le_iSup_reeLocalBlock_F4]
      refine iSup_le fun j => sup_le ((reeFixedOrbitUnipotent_le_reeFixedPosUnipotent j).trans hU) ?_
      have hn : canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈ M := by
        have : j ∈ {j | canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈ M} := by
          rw [h]; trivial
        exact this
      exact reeFixedOrbitNegUnipotent_le_of_posUnipotent hU (fixedOrbitElement_mem j) (h := 1)
        (one_mem _) (by rwa [one_mul]) (fun α hα => by
          rw [fixedOrbitElement_inv]
          exact height_fixedOrbitElement_smul_neg hα)
    · rintro rfl
      exact Set.eq_univ_of_forall fun j =>
        (canonicalRep_mem_reeFixedMonomial F4 K a (fixedOrbitElement_mem j)).2
  refine ⟨hle, hiff, fun hne => ⟨_, fun h => hne (hiff.1 h), hle, fun hP => ?_⟩⟩
  have : ∀ j : Fin F4.fixedOrbitCount,
      j ∈ {j | canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement j) ∈ M} := fun j =>
    (canonicalRep_mem_reeParabolic_iff (t := F4) (K := K) (a := a)).1
      (hP ▸ (canonicalRep_mem_reeFixedMonomial F4 K a (fixedOrbitElement_mem j)).2)
  exact hne (hiff.1 (Set.eq_univ_of_forall this))

end LargeRee

end CFSG.QuasithinUnique.Setup.X6
