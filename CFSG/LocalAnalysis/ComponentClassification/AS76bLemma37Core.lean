module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma37Basic
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma21
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma22

public section

namespace CFSG.ComponentClassification.AS76b

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Lemma34 Lemma22 Lemma37

section Layer

variable {G : Type*} [Group G]

@[expose] def layerCentralizer (A W : Subgroup G) : Subgroup G :=
  (CFSG.layer ↥(A ⊓ centralizer (W : Set G))).map (A ⊓ centralizer (W : Set G)).subtype

theorem layerCentralizer_le (A W : Subgroup G) :
    layerCentralizer A W ≤ A ⊓ centralizer (W : Set G) :=
  map_subtype_le _

theorem normalizer_inf_le_normalizer_layerCentralizer (A W : Subgroup G) :
    normalizer (A : Set G) ⊓ centralizer (W : Set G) ≤
      normalizer (layerCentralizer A W : Set G) := by
  intro x hx
  obtain ⟨hxA, hxW⟩ := mem_inf.mp hx
  set Y := A ⊓ centralizer (W : Set G) with hY
  have hxY : x ∈ normalizer (Y : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    have hW : y ∈ centralizer (W : Set G) ↔ x * y * x⁻¹ ∈ centralizer (W : Set G) := by
      constructor
      · intro hy
        exact mul_mem (mul_mem hxW hy) (inv_mem hxW)
      · intro hy
        have h := mul_mem (mul_mem (inv_mem hxW) hy) hxW
        simpa [mul_assoc] using h
    rw [hY, mem_inf, mem_inf, ← mem_normalizer_iff.mp hxA y, hW]
  let φ : Y ≃* Y := ((MulAut.conj x).subgroupMap Y).trans
    (MulEquiv.subgroupCongr (conj_eq_self_iff.mpr hxY))
  have hmap : (CFSG.layer Y).map φ.toMonoidHom = CFSG.layer Y :=
    characteristic_iff_map_eq.mp CFSG.LocalCores.layer_characteristic φ
  rw [← conj_eq_self_iff, conj, layerCentralizer, ← hY, map_map]
  conv_rhs => rw [← hmap, map_map]
  congr 1

end Layer

section Transfer

variable {G : Type*} [Group G]

theorem inf_subgroupOf_eq (H K X : Subgroup G) :
    (H ⊓ K).subgroupOf X = H.subgroupOf X ⊓ K.subgroupOf X := by
  ext x
  simp [mem_subgroupOf]

theorem conj_le_of_mem {L X : Subgroup G} (hLX : L ≤ X) {c : G} (hc : c ∈ X) :
    conj L c ≤ X := by
  intro y hy
  have h := mul_mem (mul_mem hc (hLX (mem_conj_iff.mp hy))) (inv_mem hc)
  simpa [mul_assoc] using h

variable [Finite G]

theorem lemma22_core_in {X K R L : Subgroup G} (hKX : K ≤ X) (hLX : L ≤ X)
    (hKs : Group.IsSolvable ↥K) (hK : TightlyEmbedded K) (hR : IsSylowOf 2 R K)
    (hL : CFSG.Open.IsQuasisimple ↥L) (hNL : normalizer (K : Set G) ⊓ X ≤ normalizer (L : Set G))
    (hRL : IsSylowOf 2 R (X ⊓ centralizer (L : Set G))) :
    standardComponentIsStandard (L.subgroupOf X) ∨
      ∃ c ∈ X, conj L c ≤ centralizer (L : Set G) ∧
        X ⊓ centralizer (L : Set G) ≤ normalizer (conj L c : Set G) ∧
        IsSylowOf 2 (R ⊓ conj L c) (conj L c) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRX : R ≤ X := hR.le.trans hKX
  have hN : normalizer ((K.subgroupOf X : Subgroup X) : Set X) ≤
      normalizer ((L.subgroupOf X : Subgroup X) : Set X) := by
    intro x hx
    rw [← subgroupOf_normalizer_eq hKX, mem_subgroupOf] at hx
    rw [← subgroupOf_normalizer_eq hLX, mem_subgroupOf]
    exact hNL ⟨hx, x.2⟩
  have hS : IsSylowOf 2 (R.subgroupOf X)
      (centralizer ((L.subgroupOf X : Subgroup X) : Set X)) := by
    rw [centralizer_subgroupOf hLX, ← inf_subgroupOf_left (centralizer (L : Set G)) X]
    exact (isSylowOf_subgroupOf_iff hRX inf_le_left).mpr hRL
  rcases lemma22_core (isSolvable_subgroupOf hKX hKs) (tightlyEmbedded_subgroupOf hKX hK)
      ((isSylowOf_subgroupOf_iff hRX hKX).mpr hR) ((isQuasisimple_subgroupOf_iff hLX).mpr hL)
      hN hS with h | ⟨g, hg1, hg2, hg3, -⟩
  · exact Or.inl h
  · right
    have hcX : conj L (g : G) ≤ X := conj_le_of_mem hLX g.2
    rw [conj_subgroupOf, centralizer_subgroupOf hLX] at hg1
    rw [conj_subgroupOf, centralizer_subgroupOf hLX, ← subgroupOf_normalizer_eq hcX] at hg2
    rw [conj_subgroupOf, ← inf_subgroupOf_eq,
      isSylowOf_subgroupOf_iff (inf_le_right.trans hcX) hcX] at hg3
    refine ⟨g, g.2, fun y hy => ?_, fun y hy => ?_, hg3⟩
    · have hy' : (⟨y, hcX hy⟩ : X) ∈ (conj L (g : G)).subgroupOf X := hy
      exact hg1 hy'
    · obtain ⟨hyX, hyC⟩ := mem_inf.mp hy
      have hy' : (⟨y, hyX⟩ : X) ∈ (centralizer (L : Set G)).subgroupOf X := hyC
      exact hg2 hy'

end Transfer

section Hyp31

variable {G : Type} [Group G] [Finite G]

theorem not_normal_centralizer {A : Subgroup G} (hA : Hyp31 A) :
    ¬ (centralizer (A : Set G)).Normal := by
  intro hK
  apply hA.not_normal
  rw [← normalizer_eq_top_iff, ← normalizer_centralizer_eq hA.standard]
  exact normalizer_eq_top_iff.mpr hK

theorem tightlyEmbedded_oddCoreIn_sup (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    {A R : Subgroup G} (hA : Hyp31 A) (hR : IsSylowOf 2 R (centralizer (A : Set G))) :
    TightlyEmbedded (oddCoreIn (centralizer (A : Set G)) ⊔ R) :=
  (lemma21 h4 (tightlyEmbedded_centralizer hA.standard) hR (h32 G A hA R hR) (h34 G A hA).2
    (not_normal_centralizer hA)).1

theorem lemma37_core_of_le (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    {A W L R : Subgroup G} (hA : Hyp31 A) (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    (hWA : W ≤ A) (hL : CFSG.Open.IsQuasisimple ↥L) (hLA : L ≤ A ⊓ centralizer (W : Set G))
    (hNL : normalizer (A : Set G) ⊓ centralizer (W : Set G) ≤ normalizer (L : Set G))
    (hRL : IsSylowOf 2 R
      (centralizer (W : Set G) ⊓ centralizer (L : Set G) ⊓ normalizer (R : Set G))) :
    standardComponentIsStandard (L.subgroupOf (centralizer (W : Set G))) ∨
      ∃ c ∈ centralizer (W : Set G), conj L c ≤ centralizer (L : Set G) ∧
        centralizer (W : Set G) ⊓ centralizer (L : Set G) ≤ normalizer (conj L c : Set G) ∧
        IsSylowOf 2 (R ⊓ conj L c) (conj L c) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKte := tightlyEmbedded_centralizer hA.standard
  have hK'te := tightlyEmbedded_oddCoreIn_sup h4 h32 h34 hA hR
  have hK'K : oddCoreIn (centralizer (A : Set G)) ⊔ R ≤ centralizer (A : Set G) :=
    sup_le (oddCoreIn_le _) hR.le
  have hKW : centralizer (A : Set G) ≤ centralizer (W : Set G) :=
    centralizer_le fun x hx => hWA hx
  refine lemma22_core_in (hK'K.trans hKW) (hLA.trans inf_le_right) (isSolvable_oddCoreIn_sup hR)
    hK'te (hR.of_le le_sup_right hK'K) hL ?_ (isSylowOf_of_isSylowOf_inf_normalizer hRL)
  intro x hx
  obtain ⟨hxN, hxW⟩ := mem_inf.mp hx
  have hxA : x ∈ normalizer (A : Set G) := by
    rw [← normalizer_centralizer_eq hA.standard]
    exact normalizer_le_of_le_of_even hKte hK'K hK'te.1 hxN
  exact hNL ⟨hxA, hxW⟩

theorem lemma37_core (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    {A W R : Subgroup G} (hA : Hyp31 A) (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    (hWA : W ≤ A) (hL : CFSG.Open.IsQuasisimple ↥(layerCentralizer A W))
    (hRL : IsSylowOf 2 R (centralizer (W : Set G) ⊓
      centralizer (layerCentralizer A W : Set G) ⊓ normalizer (R : Set G))) :
    standardComponentIsStandard ((layerCentralizer A W).subgroupOf (centralizer (W : Set G))) ∨
      ∃ c ∈ centralizer (W : Set G),
        conj (layerCentralizer A W) c ≤ centralizer (layerCentralizer A W : Set G) ∧
        centralizer (W : Set G) ⊓ centralizer (layerCentralizer A W : Set G) ≤
          normalizer (conj (layerCentralizer A W) c : Set G) ∧
        IsSylowOf 2 (R ⊓ conj (layerCentralizer A W) c) (conj (layerCentralizer A W) c) :=
  lemma37_core_of_le h4 h32 h34 hA hR hWA hL (layerCentralizer_le A W)
    (normalizer_inf_le_normalizer_layerCentralizer A W) hRL

end Hyp31

end CFSG.ComponentClassification.AS76b
