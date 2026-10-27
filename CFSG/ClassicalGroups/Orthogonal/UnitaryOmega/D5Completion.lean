module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.CompletionThreeDFive
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PureBlockDefs
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.BlockCast
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.D5Frame
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.D5Nodes
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PureBlocks

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.LieType.CurtisTits CFSG.LieType.Universal CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KCOrthogonal

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  {E : QuadExt F K (unitaryInvolution K 2 f)}

theorem map_normOmegaCast_normBlock_zero_one :
    (normBlock E 3 {0, 1}).map (normOmegaCast E (by norm_num : 3 ≤ 4)) = normBlock E 4 {0, 1} := by
  have h3 : normBlock E 3 {0, 1} = (normOmegaCast E (by norm_num : 2 ≤ 3)).range := by
    rw [range_normOmegaCast]
    congr 1
  have h4 : normBlock E 4 {0, 1} = (normOmegaCast E (by norm_num : 2 ≤ 4)).range := by
    rw [range_normOmegaCast]
    congr 1
  rw [h3, h4, ← MonoidHom.range_comp, normOmegaCast_comp]

theorem exists_d5Completion_of_frame {G : Type} [Group G]
    (Θ : spinGroup (quadPlus 5 F) ≃* normOmega E 4) {CA CP : Subgroup (normOmega E 4)}
    (hNP : ∀ k : Fin 5, k.val ≤ 2 →
      (spinTenRankOne F k).map Θ.toMonoidHom ≤ normPureBlock E 4 Finset.univ)
    (hNA : ∀ k : Fin 5, 2 ≤ k.val →
      (spinTenRankOne F k).map Θ.toMonoidHom ≤ normBlock E 4 {0, 1})
    (hN2 : (spinTenRankOne F 2).map Θ.toMonoidHom ≤ normPureBlock E 4 {0, 1})
    (hAgen : normBlock E 4 {0, 1} ≤
      ⨆ (k : Fin 5) (_ : 2 ≤ k.val), (spinTenRankOne F k).map Θ.toMonoidHom)
    (hPgen : normPureBlock E 4 Finset.univ ≤
      (⨆ (k : Fin 5) (_ : k.val ≤ 2), (spinTenRankOne F k).map Θ.toMonoidHom) ⊔
        normPureBlock E 4 {0, 1})
    (hNCP : ∀ k : Fin 5, k.val ≤ 1 → (spinTenRankOne F k).map Θ.toMonoidHom ≤ CP)
    (hNCA : ∀ k : Fin 5, 3 ≤ k.val → (spinTenRankOne F k).map Θ.toMonoidHom ≤ CA)
    (hCP : normPureBlock E 4 {0, 1} ≤ normPureBlock E 4 Finset.univ)
    (hCA : normPureBlock E 4 {0, 1} ≤ normBlock E 4 {0, 1})
    (φ : normPureBlock E 4 Finset.univ →* G) (a3 : normOmega E 3 →* G)
    (hagree : ∀ (x : normOmega E 3)
      (hx : normOmegaCast E (by norm_num : 3 ≤ 4) x ∈ normPureBlock E 4 Finset.univ),
      φ ⟨_, hx⟩ = a3 x)
    (hcross : ∀ (x : normOmega E 3) (y : normPureBlock E 4 Finset.univ),
      normOmegaCast E (by norm_num : 3 ≤ 4) x ∈ CA → (y : normOmega E 4) ∈ CP →
      Commute (a3 x) (φ y)) :
    ∃ Ψ : normOmega E 4 →* G, (∀ y : normPureBlock E 4 Finset.univ, Ψ y = φ y) ∧
      (∀ x ∈ normBlock E 3 {0, 1}, Ψ (normOmegaCast E (by norm_num : 3 ≤ 4) x) = a3 x) ∧
      Ψ.range = φ.range ⊔ (normBlock E 3 {0, 1}).map a3 := by
  set c34 := normOmegaCast E (by norm_num : 3 ≤ 4) with hc34
  have hinj : Function.Injective c34 := normOmegaCast_injective E _
  set B3 := normBlock E 3 {0, 1} with hB3
  have hAmap : B3.map c34 = normBlock E 4 {0, 1} := map_normOmegaCast_normBlock_zero_one
  let e : B3 ≃* B3.map c34 := Subgroup.equivMapOfInjective B3 c34 hinj
  let α : B3.map c34 →* G := (a3.comp B3.subtype).comp e.symm.toMonoidHom
  have hα : ∀ (z : B3.map c34) (x : normOmega E 3) (hx : x ∈ B3), c34 x = z → α z = a3 x := by
    intro z x hx hxz
    have hez : e ⟨x, hx⟩ = z :=
      Subtype.ext (by rw [Subgroup.coe_equivMapOfInjective_apply]; exact hxz)
    rw [← hez]
    show a3 (B3.subtype (e.symm (e ⟨x, hx⟩))) = a3 x
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hA : ∀ k : Fin 5, 2 ≤ k.val → (spinTenRankOne F k).map Θ.toMonoidHom ≤ B3.map c34 :=
    fun k hk => (hNA k hk).trans hAmap.ge
  have hCA' : normPureBlock E 4 {0, 1} ≤ B3.map c34 := hCA.trans hAmap.ge
  have hφα : ∀ (x : normOmega E 4) (hx : x ∈ normPureBlock E 4 {0, 1}),
      φ ⟨x, hCP hx⟩ = α ⟨x, hCA' hx⟩ := by
    intro x hx
    obtain ⟨x', hx', hxx⟩ := hCA' hx
    rw [hα ⟨x, hCA' hx⟩ x' hx' hxx]
    have h := hagree x' (by rw [hxx]; exact hCP hx)
    rw [← h]
    exact congrArg φ (Subtype.ext hxx.symm)
  have hcross' : ∀ (k l : Fin 5) (hk : k.val ≤ 1) (hl : 3 ≤ l.val) (x : spinTenRankOne F k)
      (y : spinTenRankOne F l),
      Commute (φ ⟨Θ x, hNP k (by omega) (Subgroup.mem_map_of_mem _ x.2)⟩)
        (α ⟨Θ y, hA l (by omega) (Subgroup.mem_map_of_mem _ y.2)⟩) := by
    intro k l hk hl x y
    obtain ⟨y', hy', hyy⟩ := hA l (by omega) (Subgroup.mem_map_of_mem _ y.2)
    rw [hα _ y' hy' hyy]
    refine (hcross y' _ ?_ ?_).symm
    · rw [hyy]
      exact hNCA l hl (Subgroup.mem_map_of_mem _ y.2)
    · exact hNCP k hk (Subgroup.mem_map_of_mem _ x.2)
  obtain ⟨Ψ, hΨP, hΨA, hΨr⟩ := exists_hom_spinTen_of_two_charts_of_generation Θ φ α hNP hA hCP
    hCA' hN2 hφα hcross' (hAmap.le.trans hAgen) hPgen
  refine ⟨Ψ, fun y => hΨP y y.2, fun x hx => ?_, ?_⟩
  · rw [hΨA _ (Subgroup.mem_map_of_mem _ hx)]
    exact hα _ x hx rfl
  · rw [hΨr]
    congr 1
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective, Subgroup.map_top,
      MonoidHom.range_comp, Subgroup.range_subtype]

theorem exists_d5Completion (hq : 4 ≤ Nat.card F) {G : Type} [Group G]
    (φ : normPureBlock E 4 Finset.univ →* G) (a3 : normOmega E 3 →* G)
    (hagree : ∀ (x : normOmega E 3)
      (hx : normOmegaCast E (by norm_num : 3 ≤ 4) x ∈ normPureBlock E 4 Finset.univ),
      φ ⟨_, hx⟩ = a3 x)
    (hcross : ∀ (x : normOmega E 3) (y : normPureBlock E 4 Finset.univ),
      normOmegaCast E (by norm_num : 3 ≤ 4) x ∈
        (supportedDerived (normHypForm E 4) (crossAnchor E)).subgroupOf (normOmega E 4) →
      (y : normOmega E 4) ∈
        (supportedDerived (normHypForm E 4) (crossPure E)).subgroupOf (normOmega E 4) →
      Commute (a3 x) (φ y)) :
    ∃ Ψ : normOmega E 4 →* G, (∀ y : normPureBlock E 4 Finset.univ, Ψ y = φ y) ∧
      (∀ x ∈ normBlock E 3 {0, 1}, Ψ (normOmegaCast E (by norm_num : 3 ≤ 4) x) = a3 x) ∧
      Ψ.range = φ.range ⊔ (normBlock E 3 {0, 1}).map a3 :=
  exists_d5Completion_of_frame (d5Equiv E)
    (fun _ hk => map_spinTenRankOne_le_normPureBlock E hk)
    (fun _ hk => map_spinTenRankOne_le_normBlock E hk)
    (map_spinTenRankOne_two_le E hq) (normBlock_zero_one_le_iSup E)
    (normPureBlock_univ_le_iSup E hq)
    (fun _ hk => map_spinTenRankOne_le_crossPure E hk)
    (fun _ hk => map_spinTenRankOne_le_crossAnchor E hk hq)
    (normPureBlock_mono E 4 (Finset.subset_univ _)) (normPureBlock_le_normBlock E 4 {0, 1})
    φ a3 hagree hcross

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

end
