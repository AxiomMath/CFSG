module

public import CFSG.ClassicalInvolution.Asc77.AscT7BAlpha
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameConn
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.CentQuotCongr
public import CFSG.ClassicalInvolution.Q3.TL4D4NCFam

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

namespace TwinDisc

section DataDef

variable {G : Type} [Group G]

structure Data (Ω : Set (Subgroup G)) (K K' : Subgroup G) (z u : G) (J : Subgroup G) (t : G)
    (W : Subgroup G) : Prop where
  frame : TwinFrameData Ω K K' z u J t
  hW : W ∈ WSet Ω
  hzW : z ∈ W
  htW : t ∈ W

end DataDef

section Exists

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_data (hΩ : HypOmegaGen Ω) {K K' : Subgroup G} {z : G} (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K)
    (hperp : KPerp Ω K ≠ twinSet Ω K) :
    ∃ (u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Data Ω K K' z u J t W := by
  obtain ⟨J, hJ, -⟩ := A7Q.Gen.exists_mem_omegaOfSet_twinSet hΩ hK hz hperp
  obtain ⟨t, ht⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ.1
  obtain ⟨u, W, hf, hW, hzW, htW⟩ := Hat2A7S.exists_twinFrameData hΩ hK hz hK' hne hJ ht
  exact ⟨u, J, t, W, ⟨hf, hW, hzW, htW⟩⟩

theorem isElemAbelian2_closure_uz {K K' J : Subgroup G} {z u t : G}
    (hΩ : HypOmegaGen Ω) (h : TwinFrameData Ω K K' z u J t) :
    IsElemAbelian2 (Subgroup.closure ({u, z} : Set G)) 2 := by
  obtain ⟨hB, -⟩ := TwinFrame.shape_of_frameData hΩ h
  have hmem := TwinFrame.closure_zu_mem h
  obtain ⟨hle, hcard⟩ := hmem
  rw [Set.pair_comm]
  refine ⟨by simpa using hcard, fun x hx => ?_⟩
  have h2 := hB.2 x (hle hx)
  simpa [pow_two] using h2

end Exists

section Normalizer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem rankTwoSpan_le_normalizer_alpha {B α₀ : Subgroup G} (hB : IsElemAbelian 2 B)
    (h : ∀ A : Subgroup G, A ≤ B → IsElemAbelian2 A 2 → alphaOf A = α₀) :
    Bootstrap.rankTwoSpan B ≤ Subgroup.normalizer (α₀ : Set G) := by
  refine iSup₂_le fun F hF => ?_
  obtain ⟨hFB, hcard⟩ := hF
  have hF2 : IsElemAbelian2 F 2 := ⟨by simpa using hcard, fun x hx => by
    have := hB.2 x (hFB hx)
    simpa [pow_two] using this⟩
  calc Subgroup.centralizer (F : Set G) ≤ Subgroup.normalizer (alphaOf F : Set G) :=
        T7B.centralizer_le_normalizer_alphaOf F
    _ = Subgroup.normalizer (α₀ : Set G) := by rw [h F hFB hF2]

theorem twin_le_normalizer_alpha (hΩ : HypOmegaGen Ω) {K K' J : Subgroup G} {z u t : G}
    (h : TwinFrameData Ω K K' z u J t)
    (hα : ∀ A : Subgroup G, A ≤ Subgroup.closure ({z, u, t} : Set G) → IsElemAbelian2 A 2 →
      alphaOf A = alphaOf (Subgroup.closure ({u, z} : Set G)))
    {L : Subgroup G} (hL : L ∈ twinSet Ω K) :
    L ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) := by
  obtain ⟨hB, -⟩ := TwinFrame.shape_of_frameData hΩ h
  exact (TwinFrame.twin_le_rankTwoSpan hΩ h hL).trans (rankTwoSpan_le_normalizer_alpha hB hα)

end Normalizer

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
