module

public import CFSG.GH74.Generic.S1.RLevelECore
public import CFSG.GH74.Generic.S1.RA4Facts
public import CFSG.GH74.Generic.S1.ROutLin
public import CFSG.GH74.Generic.S1.ROutUni

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
  CFSG.GH74.Generic CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan
open scoped MatrixGroups

theorem s1_hOut {G : Type} [Group G] [Finite G] (hgen : Gen4 G) {x : G}
    {K : Subgroup (CentralizerBar x)} [K.Normal] (hmodel : IsSL4Model ↥K)
    (hcent : Subgroup.centralizer (K : Set (CentralizerBar x)) ≤ K) :
    ∀ T : Subgroup (CentralizerBar x), IsPGroup 2 T → (K.subgroupOf T).index ≤ 2 := by
  intro T hT
  have hC : Gen4 (CentralizerBar x) := gen4_centralizerBar hgen x
  rcases hmodel with ⟨F, _, _, hF, ⟨e⟩⟩ | ⟨q, F, _, _, hF, hq, ⟨e⟩⟩
  · exact outBound_lin hF hC K (e.trans (specialLinearGroupEquivStatedSL 4 F).symm) hcent T hT
  · obtain ⟨p, f, h, rfl⟩ := rcard_exists_unitaryFieldData hF
    have hp2 : p ≠ 2 := by
      intro hp
      have hf := h.one_le
      subst hp
      have : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
      omega
    exact Uni.outBound_uni h hp2 hq hC K e hcent T hT


theorem s1Front_of_setup {G : Type} [Group G] [Finite G] {x : G}
    {K : Subgroup (CentralizerBar x)} (hset : S1Setup G x K) : S1Front G x K := by
  obtain ⟨hK1, -⟩ := hset.shape
  have hmodel : ShapeModel ↥K := Or.inl hK1
  obtain ⟨hxK', hlayer, hcentK, -, -, -, -, -, hB5, -⟩ :=
    generic_front_end_full frontDataStatement (outerStatement_of_three outerThreeStatement)
      hset.simple hset.nonab hset.gen4 hset.inv hset.comp hmodel
  have hKn : K.Normal := normal_of_layer_eq hlayer
  have hcentle : Subgroup.centralizer (K : Set (CentralizerBar x)) ≤ K := by
    rw [hcentK]
    exact (Subgroup.zpowers_le).2 hxK'
  exact ⟨hlayer, hcentK, hB5, goodSub_le_of_outerStatement
    (outerStatement_of_three outerThreeStatement) K hmodel hcentle⟩

theorem levelE_lin
    {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup (CentralizerBar x)}
    (hset : S1Setup G x K) (J : Fin 4 → Subgroup G) (p f : ℕ) (F : Type) [Field F] [Finite F]
    (hp : p.Prime) (hF : Nat.card F = p ^ f) (hq : 3 ≤ p ^ f) (hW : WeakCTA4 F J)
    (hlink : S1LinkedLin x K F J) (hnorm : S1NormalizerProp x J) : (⨆ i, J i : Subgroup G) = ⊤ := by
  have hfront := s1Front_of_setup hset
  have hKn : K.Normal := normal_of_layer_eq hfront.layer_eq
  have hxK : xbar x ∈ K := hset.shape.2
  have hfr : Q8Frame ↥K := IsSL4Model.q8Frame hset.shape.1
  have hcent : Subgroup.centralizer (K : Set (CentralizerBar x)) ≤ K := by
    rw [hfront.cent_eq]
    exact (Subgroup.zpowers_le).2 hxK
  have hOut := s1_hOut hset.gen4 hset.shape.1 hcent
  obtain ⟨y, hyJ, hy2, hyc, hnormQ⟩ := hnorm
  have hfacts := s1A4Facts_lin J p f F hp hF hq hW hlink hyJ hy2 hyc
  exact levelE_of_data hset.simple hset.nonab hset.gen4 hset.inv hxK hfr hfront.b5 hOut J hfacts.jc
    hfacts.hk hfacts.perf hfacts.cnt y hyJ hy2 hfacts.noncomm hnormQ hfacts.classes

theorem levelE_uni
    {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup (CentralizerBar x)}
    (hset : S1Setup G x K) (J : Fin 4 → Subgroup G) (p f : ℕ) (F : Type) [Field F] [Finite F]
    [Fact p.Prime] [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f)
    (hW : WeakPhanA4 F p f J) (hlink : S1LinkedUni x K F p f J) (hnorm : S1NormalizerProp x J) :
    (⨆ i, J i : Subgroup G) = ⊤ := by
  have hfront := s1Front_of_setup hset
  have hKn : K.Normal := normal_of_layer_eq hfront.layer_eq
  have hxK : xbar x ∈ K := hset.shape.2
  have hfr : Q8Frame ↥K := IsSL4Model.q8Frame hset.shape.1
  have hcent : Subgroup.centralizer (K : Set (CentralizerBar x)) ≤ K := by
    rw [hfront.cent_eq]
    exact (Subgroup.zpowers_le).2 hxK
  have hOut := s1_hOut hset.gen4 hset.shape.1 hcent
  obtain ⟨y, hyJ, hy2, hyc, hnormQ⟩ := hnorm
  have hfacts := s1A4Facts_uni J p f F hF hq hW hlink hyJ hy2 hyc
  exact levelE_of_data hset.simple hset.nonab hset.gen4 hset.inv hxK hfr hfront.b5 hOut J hfacts.jc
    hfacts.hk hfacts.perf hfacts.cnt y hyJ hy2 hfacts.noncomm hnormQ hfacts.classes

theorem s1LevelE :
    S1LevelE := by
  intro G _ _ x K hset J hJ
  obtain ⟨hcase, hnorm⟩ := hJ
  rcases hcase with ⟨p, f, F, _, _, hp, hF, hq, hW, hlink⟩ | ⟨p, f, F, _, _, _, _, hF, hq, hW, hlink⟩
  · exact levelE_lin hset J p f F hp hF hq hW hlink hnorm
  · exact levelE_uni hset J p f F hF hq hW hlink hnorm

end CFSG.GH74.Generic.S1
