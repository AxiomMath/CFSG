module

public import CFSG.LocalAnalysis.OddStandard.Seitz77PlaneLine
public import CFSG.LocalAnalysis.ComponentClassification.AS81L34Transport
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step15Points
public import CFSG.Blueprint.OddStandardExact
public import CFSG.Blueprint.RecognitionDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourL34Check
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.OddStandard.Seitz77FusionMain
public import CFSG.LocalAnalysis.OddStandard.Seitz77Thompson
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveRho
public import CFSG.Monster.Code.Weights
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Sporadic.SmallOddCore.CheckSpec

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AS81
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open LinearFlag Matrix CFSG.LieType.Chevalley

local notation "cIn" => CFSG.ComponentClassification.AS81.centerIn

section Matrices

variable {k : Type} [Field k]

theorem proj_levi_conj_mem_W_iff (i : Fin 2) (B : SL2 k) (c : k) :
    proj 3 k (levi k i B) * proj 3 k (unipU k 0 0 c) * (proj 3 k (levi k i B))⁻¹ ∈
      projCenterW k ↔ c * (B : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 := by
  have key : ∀ a b c' : k, proj 3 k (levi k i B) * proj 3 k (unipU k 0 0 c) *
      (proj 3 k (levi k i B))⁻¹ = proj 3 k (unipU k a b c') →
      (proj 3 k (unipU k a b c') ∈ projCenterW k ↔ a = 0 ∧ b = 0) := by
    intro a b c' _
    rw [mem_projCenterW]
    constructor
    · rintro ⟨c'', h⟩
      obtain ⟨h1, h2, -⟩ := unipU_eq_of_proj_eq h
      exact ⟨h1.symm, h2.symm⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨c', rfl⟩
  fin_cases i
  · have hconj : proj 3 k (leviOne k B) * proj 3 k (unipU k 0 0 c) *
        (proj 3 k (leviOne k B))⁻¹ = proj 3 k (unipU k (0 * (B : Matrix (Fin 2) (Fin 2) k) 1 1 -
          c * (B : Matrix (Fin 2) (Fin 2) k) 1 0) 0 (c * (B : Matrix (Fin 2) (Fin 2) k) 0 0 -
          0 * (B : Matrix (Fin 2) (Fin 2) k) 0 1)) := by
      rw [← map_inv, ← map_mul, ← map_mul, mul_inv_eq_iff_eq_mul.2 (leviOne_mul_unipU B 0 c)]
    change proj 3 k (leviOne k B) * proj 3 k (unipU k 0 0 c) *
        (proj 3 k (leviOne k B))⁻¹ ∈ projCenterW k ↔ _
    rw [hconj, key _ _ _ hconj]
    simp
  · have hconj : proj 3 k (leviTwo k B) * proj 3 k (unipU k 0 0 c) *
        (proj 3 k (leviTwo k B))⁻¹ = proj 3 k (unipU k 0 ((B : Matrix (Fin 2) (Fin 2) k) 1 0 * c +
          (B : Matrix (Fin 2) (Fin 2) k) 1 1 * 0) ((B : Matrix (Fin 2) (Fin 2) k) 0 0 * c +
          (B : Matrix (Fin 2) (Fin 2) k) 0 1 * 0)) := by
      rw [← map_inv, ← map_mul, ← map_mul, mul_inv_eq_iff_eq_mul.2 (leviTwo_mul_unipU B 0 c)]
    change proj 3 k (leviTwo k B) * proj 3 k (unipU k 0 0 c) *
        (proj 3 k (leviTwo k B))⁻¹ ∈ projCenterW k ↔ _
    rw [hconj, key _ _ _ hconj]
    simp [mul_comm]

theorem conj_mem_W_of_normalizer_projRad [Finite k] (hk : Nat.card k = 4) (i : Fin 2)
    {y : projectiveSL 3 k} (hy : y ∈ normalizer (projRad k i : Set (projectiveSL 3 k)))
    {w₀ : projectiveSL 3 k} (hw₀ : w₀ ∈ projCenterW k) (hw₀1 : w₀ ≠ 1)
    (hyw₀ : y * w₀ * y⁻¹ ∈ projCenterW k) : ∀ w ∈ projCenterW k, y * w * y⁻¹ ∈ projCenterW k := by
  have hLN : (leviProj k i).range ≤ normalizer (projRad k i : Set (projectiveSL 3 k)) := by
    rw [normalizer_projRad hk i]
    exact le_sup_right
  rw [normalizer_projRad hk i, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ (normalizer_projRad hk i ▸ hLN)] at hy
  obtain ⟨r, hr, δ, ⟨B, rfl⟩, rfl⟩ := hy
  have hδ : leviProj k i B = proj 3 k (levi k i B) := rfl
  have hconj : ∀ c : k, (r * leviProj k i B) * proj 3 k (unipU k 0 0 c) *
      (r * leviProj k i B)⁻¹ =
      proj 3 k (levi k i B) * proj 3 k (unipU k 0 0 c) * (proj 3 k (levi k i B))⁻¹ := by
    intro c
    have hwR : proj 3 k (unipU k 0 0 c) ∈ projRad k i :=
      projCenterW_le_projRad i (mem_projCenterW.2 ⟨c, rfl⟩)
    have hδN : proj 3 k (levi k i B) ∈ normalizer (projRad k i : Set (projectiveSL 3 k)) :=
      hLN ⟨B, rfl⟩
    have hx : proj 3 k (levi k i B) * proj 3 k (unipU k 0 0 c) * (proj 3 k (levi k i B))⁻¹ ∈
        projRad k i := (mem_normalizer_iff.mp hδN _).mp hwR
    have hrx := commute_of_mem_projRad i hr hx
    rw [hδ]
    calc r * proj 3 k (levi k i B) * proj 3 k (unipU k 0 0 c) *
          (r * proj 3 k (levi k i B))⁻¹
        = r * (proj 3 k (levi k i B) * proj 3 k (unipU k 0 0 c) *
          (proj 3 k (levi k i B))⁻¹) * r⁻¹ := by group
      _ = proj 3 k (levi k i B) * proj 3 k (unipU k 0 0 c) * (proj 3 k (levi k i B))⁻¹ := by
        rw [hrx]
        group
  obtain ⟨c₀, rfl⟩ := mem_projCenterW.1 hw₀
  have hc₀ : c₀ ≠ 0 := by
    rintro rfl
    apply hw₀1
    rw [unipU_zero, map_one]
  rw [hconj] at hyw₀
  have hB : (B : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 :=
    (mul_eq_zero.1 ((proj_levi_conj_mem_W_iff i B c₀).1 hyw₀)).resolve_left hc₀
  intro w hw
  obtain ⟨c, rfl⟩ := mem_projCenterW.1 hw
  rw [hconj]
  exact (proj_levi_conj_mem_W_iff i B c).2 (by rw [hB, mul_zero])

end Matrices

section Cover

variable {G : Type} [Group G] [Finite G]

theorem exists_cover_data {A H T : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥A)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))
    (hTsyl : IsSylowOf 2 T A) (hHT : H ≤ T) (hH : IsElemAbelian 2 H) (hH16 : Nat.card H = 16) :
    ∃ (c : L34Cover ↥A) (φ : ↥A →* projectiveSL 3 c.k) (i : Fin 2), Function.Surjective φ ∧
      φ.ker = center ↥A ∧ (H.subgroupOf A).map φ = projRad c.k i ∧
      ((cIn T).subgroupOf A).map φ = projCenterW c.k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c⟩ := nonempty_l34Cover_of_odd hq hL hodd
  have hO := oddCore_le_center hq.1 hq.2
  obtain ⟨T₀, hT₀⟩ := hTsyl
  have hTA : T ≤ A := hT₀ ▸ map_subtype_le _
  have hHA : H ≤ A := hHT.trans hTA
  obtain ⟨φ, hφs, hφk, hφT⟩ := c.exists_std hO T₀
  have hkerodd : Odd (Nat.card φ.ker) := by rw [hφk]; exact hodd
  have hTsub : T.subgroupOf A = T₀ := by
    rw [← hT₀]
    exact comap_map_eq_self_of_injective A.subtype_injective _
  have hT₀2 : IsPGroup 2 (T₀ : Subgroup ↥A) := T₀.2
  have hH₀T : H.subgroupOf A ≤ T₀ := fun x hx => hTsub ▸ (hHT (mem_subgroupOf.mp hx))
  have hH₀ : IsPGroup 2 (H.subgroupOf A) := hT₀2.to_le hH₀T
  have hsubodd : Odd (Nat.card A.subtype.ker) := by
    rw [ker_subtype, card_bot]
    exact odd_one
  have hW : (cIn T₀).map A.subtype = cIn T := by
    rw [map_centerIn_eq A.subtype hsubodd hT₀2, hT₀]
  have hW₀ : (cIn T).subgroupOf A = cIn (T₀ : Subgroup ↥A) := by
    rw [← hW]
    exact comap_map_eq_self_of_injective A.subtype_injective _
  have hH₀2' : ∀ x ∈ (H.subgroupOf A).map φ, x ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, show x ^ 2 = 1 from Subtype.ext (by simpa using hH.2 _ (mem_subgroupOf.mp hx)),
      map_one]
  have hH₀16 : Nat.card ((H.subgroupOf A).map φ) = 16 := by
    rw [card_map_of_isPGroup φ hkerodd hH₀, ← hH16]
    exact Nat.card_congr (subgroupOfEquivOfLe hHA).toEquiv
  have hH₀U : (H.subgroupOf A).map φ ≤ projUnip c.k := hφT ▸ map_mono hH₀T
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, (H.subgroupOf A).map φ = projRad c.k i := by
    rcases eq_projRad_of_le_projUnip c.card_k hH₀U hH₀2' hH₀16 with h0 | h1
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
  have hWφ : ((cIn T).subgroupOf A).map φ = projCenterW c.k := by
    rw [hW₀, map_centerIn_eq φ hkerodd hT₀2, hφT, ← center_projUnip]
    ext x
    constructor
    · rintro ⟨hxU, hxC⟩
      refine ⟨⟨x, hxU⟩, mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
      exact mem_centralizer_iff.mp hxC y y.2
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      show (y : projectiveSL 3 c.k) ∈ centralizer ((projUnip c.k : Subgroup _) : Set _)
      rw [mem_centralizer_iff]
      intro z hz
      exact congrArg Subtype.val (mem_center_iff.mp hy ⟨z, hz⟩)
  exact ⟨c, φ, i, hφs, hφk, hi, hWφ⟩

theorem spread_of_card_sixteen {A H T : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥A)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))
    (hTsyl : IsSylowOf 2 T A) (hHT : H ≤ T) (hH : IsElemAbelian 2 H) (hH16 : Nat.card H = 16)
    {a : G} (ha : a ∈ A ⊓ normalizer (H : Set G))
    (hex : ∃ u ∈ cIn T, u ≠ 1 ∧ a * u * a⁻¹ ∈ cIn T) :
    ∀ u ∈ cIn T, a * u * a⁻¹ ∈ cIn T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, φ, i, hφs, hφk, hi, hWφ⟩ := exists_cover_data hq hL hodd hTsyl hHT hH hH16
  have hkerodd : Odd (Nat.card φ.ker) := by rw [hφk]; exact hodd
  have hkerZ : φ.ker ≤ center ↥A := hφk.le
  have hTA : T ≤ A := hTsyl.le
  have hHA : H ≤ A := hHT.trans hTA
  have hT2 : IsPGroup 2 (T.subgroupOf A) := hTsyl.isPGroup.comap_subtype
  have hU₀2 : IsPGroup 2 ((cIn T).subgroupOf A) :=
    hT2.to_le fun x hx => mem_subgroupOf.mpr ((inf_le_left : cIn T ≤ T) (mem_subgroupOf.mp hx))
  set a₀ : ↥A := ⟨a, ha.1⟩ with ha₀
  have ha₀H : a₀ ∈ normalizer (H.subgroupOf A : Subgroup ↥A) := by
    rw [← subgroupOf_normalizer_eq hHA]
    exact mem_subgroupOf.mpr ha.2
  have hy : φ a₀ ∈ normalizer (projRad c.k i : Set (projectiveSL 3 c.k)) := by
    have := le_normalizer_map φ (Subgroup.mem_map_of_mem φ ha₀H)
    rwa [hi] at this
  obtain ⟨u₀, hu₀, hu₀1, hau₀⟩ := hex
  have hcT : ∀ u ∈ cIn T, u ∈ A := fun u hu => hTA ((inf_le_left : cIn T ≤ T) hu)
  set u₁ : ↥A := ⟨u₀, hcT u₀ hu₀⟩ with hu₁
  have hu₁U : u₁ ∈ (cIn T).subgroupOf A := mem_subgroupOf.mpr hu₀
  have hw₀ : φ u₁ ∈ projCenterW c.k := hWφ ▸ Subgroup.mem_map_of_mem φ hu₁U
  have hw₀1 : φ u₁ ≠ 1 := by
    intro h
    apply hu₀1
    have := eq_of_map_eq_of_isPGroup φ hkerodd hU₀2 hu₁U (one_mem _) (by rw [h, map_one])
    exact congrArg Subtype.val this
  have hyw₀ : φ a₀ * φ u₁ * (φ a₀)⁻¹ ∈ projCenterW c.k := by
    rw [← map_inv, ← map_mul, ← map_mul]
    exact hWφ ▸ Subgroup.mem_map_of_mem φ (mem_subgroupOf.mpr hau₀)
  have hall := conj_mem_W_of_normalizer_projRad c.card_k i hy hw₀ hw₀1 hyw₀
  have hP2 : IsPGroup 2 (((cIn T).subgroupOf A).map (MulAut.conj a₀).toMonoidHom) := hU₀2.map _
  have hle : ((cIn T).subgroupOf A).map (MulAut.conj a₀).toMonoidHom ≤ (cIn T).subgroupOf A := by
    refine le_of_isPGroup_of_le_sup_ker φ hkerZ hkerodd hU₀2 hP2 ?_
    rw [← comap_map_eq]
    rintro _ ⟨v, hv, rfl⟩
    show φ (a₀ * v * a₀⁻¹) ∈ ((cIn T).subgroupOf A).map φ
    rw [map_mul, map_mul, map_inv, hWφ]
    exact hall _ (hWφ ▸ Subgroup.mem_map_of_mem φ hv)
  intro u hu
  have hu' : (⟨u, hcT u hu⟩ : ↥A) ∈ (cIn T).subgroupOf A := mem_subgroupOf.mpr hu
  exact mem_subgroupOf.mp (hle ⟨_, hu', rfl⟩)

end Cover

section ASideProof

variable {G : Type} [Group G] [Finite G]

open CFSG.ComponentClassification.AschbacherTightEmbedding in
theorem aSide_of_l34 {A V W : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥A)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))
    (hV : IsSylowOf 2 V A) (hWV : W ≤ V) (hW : IsElemAbelian 2 W) (hW16 : Nat.card W = 16) :
    ASide A V W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hV.le, ?_, ?_, ?_⟩
  · intro w hw w' hw' hw1 hw1'
    exact exists_conj_eq_of_card_sixteen hq hL hodd (hWV.trans hV.le) hW hW16 hw hw' hw1 hw1'
  · intro g hg
    have hqB := isQuasisimple_rightConjugate g hq
    have hLB := typeL34_rightConjugate g hL
    have hoddB : Odd (Nat.card (center ↥(rightConjugate A g))) := by
      rw [card_center_rightConjugate]
      exact hodd
    have hVB : V ≤ rightConjugate A g := fun v hv => (mem_rightConjugate_iff A g v).mpr (hg v hv)
    have hVBsyl : IsSylowOf 2 V (rightConjugate A g) :=
      isSylowOf_of_card hVB (by rw [rightConjugate_card]; exact hV.card_eq)
    obtain ⟨y, hy, hfix⟩ := exists_torus_of_card_sixteen hqB hLB hoddB hVBsyl hWV hW hW16
    exact ⟨y, (mem_rightConjugate_iff A g y).mp hy.1.1, hy.1.2, hy.2, hfix⟩
  · intro a ha hex
    exact spread_of_card_sixteen hq hL hodd hV hWV hW hW16 ha hex

theorem Hyp.aSide {A : Subgroup G} (h : Hyp G A) (d : Datum A) {V₁ V₂ : Subgroup G}
    (hR : Radicals d.V V₁ V₂) {W : Subgroup G} (hW : W = V₁ ∨ W = V₂) : ASide A d.V W := by
  obtain ⟨hWV, hWe, hW16⟩ := hR.property hW
  exact aSide_of_l34 h.standard.1
    (CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h.model) h.odd
    d.V_isSylow hWV hWe hW16

end ASideProof

end CFSG.OddStandard.Seitz77
