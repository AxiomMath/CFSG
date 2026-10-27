module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
import CFSG.LocalAnalysis.AGLEmbedding.A15ComponentsAux
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbBasic

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique
open CFSG.AGLEmbedding.ParabPrime (perfectJoin le_perfectJoin exists_perfect_map_eq)

namespace ToralCensus

theorem isCatalogGroup_of_isClassicalTwoOrG2 {X : Type} [Group X] (h : IsClassicalTwoOrG2 X) :
    IsCatalogGroup X := by
  rcases h with ⟨d, -, he⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, -, he⟩
  · exact ⟨.lie d, he⟩
  · have h5 : 5 ≤ n := by omega
    exact ⟨.alternating n h5, ⟨e⟩⟩
  · exact ⟨.lie d, he⟩

theorem perfect_le_sup_centralizer_of_comp (hSch : KFactCatalogSchreier) {Y : Type} [Group Y]
    [Finite Y] {L : Subgroup Y} (hL : IsComponentOf L ⊤)
    (htype : IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L)) {V : Subgroup Y} (hV : ⁅V, V⁆ = V)
    (hVN : V ≤ Subgroup.normalizer (L : Set Y)) : V ≤ L ⊔ Subgroup.centralizer (L : Set Y) :=
  perfect_le_sup_centralizer_of_outer
    (isSolvable_outer_of_component hSch hL (isCatalogGroup_of_isClassicalTwoOrG2 htype)) hV hVN

variable {Y : Type} [Group Y]

theorem le_normalizer_of_commute {J C : Subgroup Y} (hcomm : ∀ j ∈ J, ∀ c ∈ C, j * c = c * j) :
    J ≤ Subgroup.normalizer (C : Set Y) := by
  intro j hj
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    have : j * c * j⁻¹ = c := by rw [hcomm j hj c hc]; group
    rw [this]; exact hc
  · intro hc
    have hjc := hcomm j hj _ hc
    have h3 : j * (j * c * j⁻¹) = j * c := by rw [hjc]; group
    have : j * c * j⁻¹ = c := mul_left_cancel h3
    rw [← this]; exact hc

theorem perfect_le_perfectJoin_sup {J C V : Subgroup Y}
    (hcomm : ∀ j ∈ J, ∀ c ∈ C, j * c = c * j) (hV : ⁅V, V⁆ = V) (hVJC : V ≤ J ⊔ C) :
    V ≤ perfectJoin J ⊔ C := by
  let φ : ↥J × ↥C →* Y := MonoidHom.noncommCoprod J.subtype C.subtype
    (fun j c => hcomm j j.2 c c.2)
  have hVr : V ≤ φ.range := by
    intro v hv
    have hv' := hVJC hv
    rw [← SetLike.mem_coe,
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ (le_normalizer_of_commute hcomm)] at hv'
    obtain ⟨j, hj, c, hc, rfl⟩ := hv'
    exact ⟨(⟨j, hj⟩, ⟨c, hc⟩), rfl⟩
  have hker : φ.ker ≤ Subgroup.center (↥J × ↥C) := by
    rintro ⟨j, c⟩ hjc
    have h1 : (j : Y) * c = 1 := hjc
    have hcj : (c : Y) = (j : Y)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [Subgroup.mem_center_iff]
    rintro ⟨j', c'⟩
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · have hjC : (j : Y) ∈ C := by
        have : (j : Y) = (c : Y)⁻¹ := by rw [hcj, inv_inv]
        rw [this]
        exact C.inv_mem c.2
      exact hcomm j' j'.2 j hjC
    · have hcJ : (c : Y) ∈ J := by rw [hcj]; exact J.inv_mem j.2
      exact (hcomm c hcJ c' c'.2).symm
  obtain ⟨W, hW, -, hWV⟩ := exists_perfect_map_eq φ hker hV hVr
  set W₁ : Subgroup Y := (W.map (MonoidHom.fst ↥J ↥C)).map J.subtype with hW₁
  have hW₁J : W₁ ≤ J := by
    rintro _ ⟨_, _, rfl⟩
    exact Subtype.prop _
  have hW₁p : ⁅W₁, W₁⁆ = W₁ := by
    rw [hW₁, ← Subgroup.map_commutator, ← Subgroup.map_commutator, hW]
  have hW₁P : W₁ ≤ perfectJoin J := le_perfectJoin hW₁J hW₁p
  rw [← hWV]
  rintro _ ⟨⟨j, c⟩, hjc, rfl⟩
  have hj : (j : Y) ∈ W₁ := ⟨j, ⟨(j, c), hjc, rfl⟩, rfl⟩
  exact Subgroup.mul_mem_sup (hW₁P hj) c.2

theorem le_normalizer_centralizer (L : Subgroup Y) :
    L ≤ Subgroup.normalizer (Subgroup.centralizer (L : Set Y) : Set Y) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro c
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro hc x hx
    have h1 := hc (l⁻¹ * x * l) (L.mul_mem (L.mul_mem (L.inv_mem hl) hx) hl)
    calc x * (l * c * l⁻¹) = l * ((l⁻¹ * x * l) * c) * l⁻¹ := by group
      _ = l * (c * (l⁻¹ * x * l)) * l⁻¹ := by rw [h1]
      _ = l * c * l⁻¹ * x := by group
  · intro hc x hx
    have h1 := hc (l * x * l⁻¹) (L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl))
    calc x * c = l⁻¹ * ((l * x * l⁻¹) * (l * c * l⁻¹)) * l := by group
      _ = l⁻¹ * ((l * c * l⁻¹) * (l * x * l⁻¹)) * l := by rw [h1]
      _ = c * x := by group

end ToralCensus

open ToralCensus in
theorem glueVhyp_of (hSch : KFactCatalogSchreier) (hBT : ParabRadicalSelfNorm) : GlueVhyp := by
  intro Y _ _ L J hCP V hV hVL hVO
  have hJL : J ≤ L := hCP.parab.1
  have hVLC := perfect_le_sup_centralizer_of_comp hSch hCP.comp hCP.type hV hVL
  have hVJC : V ≤ J ⊔ Subgroup.centralizer (L : Set Y) := by
    intro v hv
    have hv' := hVLC hv
    rw [← SetLike.mem_coe,
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ (le_normalizer_centralizer L)] at hv'
    obtain ⟨l, hl, c, hc, rfl⟩ := hv'
    have hOL : ((pCoreOf 2 J : Subgroup Y) : Set Y) ⊆ L := fun x hx =>
      hJL (Subgroup.map_subtype_le _ hx)
    have hcO : c ∈ Subgroup.normalizer (pCoreOf 2 J : Set Y) :=
      Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hOL hc)
    have hlO : l ∈ Subgroup.normalizer (pCoreOf 2 J : Set Y) := by
      have h := Subgroup.mul_mem _ (hVO hv) (Subgroup.inv_mem _ hcO)
      simpa using h
    exact Subgroup.mul_mem_sup (hBT Y L J hCP ⟨hl, hlO⟩) hc
  have hcomm : ∀ j ∈ J, ∀ c ∈ Subgroup.centralizer (L : Set Y), j * c = c * j :=
    fun j hj c hc => Subgroup.mem_centralizer_iff.mp hc j (hJL hj)
  exact perfect_le_perfectJoin_sup hcomm hV hVJC

end CFSG.AGLEmbedding
