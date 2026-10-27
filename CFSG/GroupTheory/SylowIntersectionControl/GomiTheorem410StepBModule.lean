module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2
public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepBSetting
public import CFSG.SignalizerFunctorTheorem.Inheritance.Basic

import CFSG.Quasithin.Background.AutOnSylow
import CFSG.Quasithin.Background.B2FactorizationBaumannAux
import CFSG.Quasithin.Background.B2FactorizationOffender

public section

namespace CFSG.GroupTheory

open CFSG CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.RankThree.PartOne Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (Pset PstarSet O2Trivial)

variable {Ω : Type} [Group Ω] [Finite Ω] {G : Subgroup Ω}

omit [Finite Ω] in
private theorem gomi410b_H_le_G_bmod {S L H W : Subgroup Ω}
    (hset : IsGomi410bSetting G S L H W) (hS : IsSylowTwoOf S G) : H ≤ G := by
  rw [hset.eq_sup]
  exact sup_le (sup_le hset.le hS.1) inf_le_left

omit [Finite Ω] in
private theorem gomi410b_S_le_H_bmod {S L H W : Subgroup Ω}
    (hset : IsGomi410bSetting G S L H W) : S ≤ H := by
  rw [hset.eq_sup]
  exact le_sup_right.trans le_sup_left

omit [Finite Ω] in
private theorem gomi410b_W_le_H_bmod {S L H W : Subgroup Ω}
    (hset : IsGomi410bSetting G S L H W) : W ≤ H := by
  have hVG : gomiV G ≤ G :=
    (B2F.omegaOneCenterOf_le_centerOf (pCoreOf 2 G)).trans
      (inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le (r := 2) G))
  have hVC : gomiV G ≤ Subgroup.centralizer (gomiV G : Set Ω) :=
    B2F.le_centralizer_self (B2F.isElemAbelian_omegaOneCenterOf (pCoreOf 2 G))
  have hVleC : gomiV G ≤ G ⊓ Subgroup.centralizer (gomiV G : Set Ω) := le_inf hVG hVC
  rw [hset.eq_sup]
  exact hset.le_gomiV.trans (hVleC.trans le_sup_right)

omit [Finite Ω] in
private theorem gomi410b_isSylowTwoOf_S_H_bmod {S L H W : Subgroup Ω}
    (hset : IsGomi410bSetting G S L H W) (hS : IsSylowTwoOf S G) : IsSylowTwoOf S H := by
  have hSH : S ≤ H := gomi410b_S_le_H_bmod hset
  refine ⟨hSH, hS.2.1, fun h2 => hS.2.2 ?_⟩
  have hrel : S.relIndex H * H.relIndex G = S.relIndex G :=
    Subgroup.relIndex_mul_relIndex S H G hSH (gomi410b_H_le_G_bmod hset hS)
  have hdiv : 2 ∣ S.relIndex G := by
    rw [← hrel]
    exact h2.mul_right (H.relIndex G)
  exact show 2 ∣ (S.subgroupOf G).index from hdiv

omit [Finite Ω] in
private theorem gomi410b_mem_preimage_bmod {H W : Subgroup Ω} {φ : ↥H →* ↥(autOn H W)}
    {P : Subgroup (MulAut ↥W)} (x : Ω) :
    x ∈ ((P.subgroupOf (autOn H W)).comap φ).map H.subtype ↔
      ∃ hx : x ∈ H, φ ⟨x, hx⟩ ∈ P.subgroupOf (autOn H W) := by
  constructor
  · intro hxN
    obtain ⟨g, hg, hgx⟩ := Subgroup.mem_map.1 hxN
    refine ⟨hgx ▸ g.2, ?_⟩
    have hge : (⟨x, hgx ▸ g.2⟩ : ↥H) = g := Subtype.ext hgx.symm
    rw [hge]
    exact hg
  · rintro ⟨hx, hxP⟩
    exact Subgroup.mem_map.2 ⟨⟨x, hx⟩, hxP, rfl⟩

omit [Finite Ω] in
private theorem gomi410b_preimage_normalizer_bmod {H W : Subgroup Ω}
    {φ : ↥H →* ↥(autOn H W)} {P : Subgroup (MulAut ↥W)} (hPle : P ≤ autOn H W)
    (hPnormal : (P.subgroupOf (autOn H W)).Normal) :
    H ≤ Subgroup.normalizer
      (((P.subgroupOf (autOn H W)).comap φ).map H.subtype : Set Ω) := by
  have hmemN := gomi410b_mem_preimage_bmod (H := H) (W := W) (φ := φ) (P := P)
  have hPN : autOn H W ≤ Subgroup.normalizer (P : Set (MulAut ↥W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPle).mp hPnormal
  have hforward : ∀ h ∈ H, ∀ x : Ω,
      x ∈ ((P.subgroupOf (autOn H W)).comap φ).map H.subtype →
        h * x * h⁻¹ ∈ ((P.subgroupOf (autOn H W)).comap φ).map H.subtype := by
    intro h hh x hxN
    obtain ⟨hx, hxP⟩ := (hmemN x).1 hxN
    refine (hmemN (h * x * h⁻¹)).2 ⟨H.mul_mem (H.mul_mem hh hx) (H.inv_mem hh), ?_⟩
    have heq : (⟨h * x * h⁻¹, H.mul_mem (H.mul_mem hh hx) (H.inv_mem hh)⟩ : ↥H) =
        ⟨h, hh⟩ * ⟨x, hx⟩ * ⟨h, hh⟩⁻¹ := by ext; rfl
    rw [heq, map_mul, map_mul, map_inv]
    have hconj := (Subgroup.mem_normalizer_iff.mp (hPN (φ ⟨h, hh⟩).2) (φ ⟨x, hx⟩).1).1
      (show (φ ⟨x, hx⟩ : MulAut ↥W) ∈ P from hxP)
    rw [Subgroup.mem_subgroupOf]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hconj
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  refine fun x => ⟨fun hx => hforward h hh x hx, fun hx => ?_⟩
  have hx' : h⁻¹ * (h * x * h⁻¹) * (h⁻¹)⁻¹ ∈
      ((P.subgroupOf (autOn H W)).comap φ).map H.subtype := hforward h⁻¹ (H.inv_mem hh) _ hx
  rwa [show h⁻¹ * (h * x * h⁻¹) * (h⁻¹)⁻¹ = x by group] at hx'

omit [Finite Ω] in
private theorem gomi410b_preimage_two_power_bmod {H W : Subgroup Ω}
    {φ : ↥H →* ↥(autOn H W)}
    (hφker : φ.ker = (Subgroup.centralizer (W : Set Ω)).subgroupOf H)
    {P : Subgroup (MulAut ↥W)} (hP2 : IsPGroup 2 P) :
    ∀ x ∈ ((P.subgroupOf (autOn H W)).comap φ).map H.subtype,
      ∃ k : ℕ, x ^ 2 ^ k ∈ Subgroup.centralizer (W : Set Ω) := by
  intro x hxN
  obtain ⟨hx, hxP⟩ :=
    (gomi410b_mem_preimage_bmod (H := H) (W := W) (φ := φ) (P := P) x).1 hxN
  obtain ⟨k, hk⟩ := hP2 ⟨(φ ⟨x, hx⟩ : MulAut ↥W),
    (show (φ ⟨x, hx⟩ : MulAut ↥W) ∈ P from hxP)⟩
  refine ⟨k, ?_⟩
  have hk' : (φ ⟨x, hx⟩ : ↥(autOn H W)) ^ 2 ^ k = 1 := by
    apply Subtype.ext
    simpa using congrArg Subtype.val hk
  have hmemker : (⟨x, hx⟩ : ↥H) ^ 2 ^ k ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_pow, hk']
  have hmemC : (⟨x, hx⟩ : ↥H) ^ 2 ^ k ∈
      (Subgroup.centralizer (W : Set Ω)).subgroupOf H := by
    rwa [← hφker]
  simpa using Subgroup.mem_subgroupOf.mp hmemC

omit [Finite Ω] in
open scoped IsMulCommutative in
private theorem gomi410b_o2Trivial_bmod {S L H W : Subgroup Ω} [IsMulCommutative ↥W]
    (hset : IsGomi410bSetting G S L H W) (hW : IsElemAbelian 2 W) :
    O2Trivial (autOn H W) := by
  obtain ⟨-, φ, hφsurj, hφker⟩ := gomi_moduleSetting hW hset.le_normalizer_W
  intro P hPle hPnormal hP2
  have hNH : ((P.subgroupOf (autOn H W)).comap φ).map H.subtype ≤ H :=
    Subgroup.map_subtype_le (H := H) _
  have hNnorm := gomi410b_preimage_normalizer_bmod (H := H) (W := W) (φ := φ)
    (P := P) hPle hPnormal
  have hNcent := gomi410b_preimage_two_power_bmod (H := H) (W := W) (φ := φ) (P := P)
    hφker hP2
  have hNle := hset.le_centralizer_of_normal _ hNH hNnorm hNcent
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  have hσ' : σ ∈ autOn H W := hPle hσ
  obtain ⟨g, hgσ⟩ := hφsurj ⟨σ, hσ'⟩
  have hgP' : φ g ∈ P.subgroupOf (autOn H W) := by rw [hgσ]; exact hσ
  have hgN : (g : Ω) ∈ ((P.subgroupOf (autOn H W)).comap φ).map H.subtype :=
    Subgroup.mem_map.2 ⟨g, hgP', rfl⟩
  have hgC : (g : Ω) ∈ Subgroup.centralizer (W : Set Ω) := hNle hgN
  have hgker : g ∈ φ.ker := by
    rw [hφker]
    exact hgC
  have h1 : φ g = 1 := MonoidHom.mem_ker.mp hgker
  have h2 : (⟨σ, hσ'⟩ : ↥(autOn H W)) = 1 := hgσ.symm.trans h1
  simpa using congrArg Subtype.val h2

open scoped IsMulCommutative in
private theorem gomi410b_pset_nonempty_bmod {S L H W : Subgroup Ω} [IsMulCommutative ↥W]
    (hset : IsGomi410bSetting G S L H W) (hS : IsSylowTwoOf S G) (hW : IsElemAbelian 2 W) :
    (Pset (autOn H W)).Nonempty := by
  have hSH : IsSylowTwoOf S H := gomi410b_isSylowTwoOf_S_H_bmod hset hS
  have hnot : ¬ thompsonJ H ≤ Subgroup.centralizer (W : Set Ω) := fun h =>
    hset.not_thompsonJ_le ((thompsonJ_le_thompsonJ_of_isSylowTwoOf hSH).trans h)
  have hne : (offenderImages hW H).Nonempty :=
    (offenderImages_nonempty_iff_not_le (hV := hW) (H := H)).2 hnot
  obtain ⟨B, hB⟩ := hne
  exact ⟨B, offenderImages_isFFStarOffender (hV := hW) (hVH := gomi410b_W_le_H_bmod hset)
    (hHN := hset.le_normalizer_W) hB⟩

private theorem gomi410b_isSylowIn_bmod {S L H W : Subgroup Ω}
    (hset : IsGomi410bSetting G S L H W) (hS : IsSylowTwoOf S G) :
    IsSylowIn 2 (autOn S W) (autOn H W) :=
  CFSG.Quasithin.AutOn.isSylowTwoOf_autOn (gomi410b_isSylowTwoOf_S_H_bmod hset hS)
    hset.le_normalizer_W

omit [Finite Ω] in
open scoped IsMulCommutative in
private theorem gomi410b_section_bmod {S L H W : Subgroup Ω} [IsMulCommutative ↥W]
    (hset : IsGomi410bSetting G S L H W) (hS : IsSylowTwoOf S G) :
    CFSG.SignalizerFunctorTheorem.IsSectionOf ↥(autOn H W) ↥G := by
  have hW : IsElemAbelian 2 W :=
    B2F.isElemAbelian_mono hset.le_gomiV (B2F.isElemAbelian_omegaOneCenterOf (pCoreOf 2 G))
  obtain ⟨-, φ, hφsurj, -⟩ := gomi_moduleSetting hW hset.le_normalizer_W
  refine ⟨H.subgroupOf G,
    φ.comp (Subgroup.subgroupOfEquivOfLe (gomi410b_H_le_G_bmod hset hS)).toMonoidHom, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := hφsurj y
  exact ⟨(Subgroup.subgroupOfEquivOfLe (gomi410b_H_le_G_bmod hset hS)).symm x, by simp [hx]⟩

open scoped IsMulCommutative in
theorem IsGomi410bSetting.moduleSetting {S L H W : Subgroup Ω} [IsMulCommutative ↥W]
    (hset : IsGomi410bSetting G S L H W) (hS : IsSylowTwoOf S G) :
    (∀ w : ↥W, w ^ 2 = 1) ∧ O2Trivial (autOn H W) ∧ (Pset (autOn H W)).Nonempty ∧
      IsSylowIn 2 (autOn S W) (autOn H W) ∧
      CFSG.SignalizerFunctorTheorem.IsSectionOf ↥(autOn H W) ↥G := by
  have hW : IsElemAbelian 2 W :=
    B2F.isElemAbelian_mono hset.le_gomiV (B2F.isElemAbelian_omegaOneCenterOf (pCoreOf 2 G))
  exact ⟨fun w => Subtype.ext (hW.2 w.1 w.2), gomi410b_o2Trivial_bmod hset hW,
    gomi410b_pset_nonempty_bmod hset hS hW, gomi410b_isSylowIn_bmod hset hS,
    gomi410b_section_bmod hset hS⟩

end CFSG.GroupTheory

end
