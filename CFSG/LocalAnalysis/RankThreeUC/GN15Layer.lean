module

public import CFSG.LocalAnalysis.RankThreeUC.GN15Steps
public import CFSG.LocalAnalysis.RankThreeUC.GN15Climb2
import CFSG.LocalAnalysis.RankThreeUC.GN15DQNormal

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Open
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}

theorem GNAbsorbs.of_normal_decomp {A : Subgroup X} (hA : A.Normal)
    (h : ∀ u ∈ A, ∃ c ∈ Subgroup.centralizer (T₁ : Set X), ∃ p ∈ Y0 T T₁ T₂,
      ∃ r ∈ Subgroup.normalizer (T₂ : Set X),
        r ∈ Subgroup.normalizer (Y0 T T₁ T₂ : Set X) ∧ u = c * p * r) :
    GNAbsorbs T T₁ T₂ A := by
  intro a ha m hm
  obtain ⟨c₀, hc₀, y, hy, n, hn, rfl⟩ := mem_gnM_iff.mp hm
  have hu : c₀⁻¹ * a * c₀ ∈ A := by simpa using hA.conj_mem a ha c₀⁻¹
  obtain ⟨c, hc, p, hp, r, hr, hrY, hdec⟩ := h _ hu
  have hy' : r * y * r⁻¹ ∈ Y0 T T₁ T₂ := (Subgroup.mem_normalizer_iff.1 hrY y).1 hy
  refine mem_gnM_iff.mpr ⟨c₀ * c, mul_mem hc₀ hc, p * (r * y * r⁻¹), mul_mem hp hy', r * n,
    mul_mem hr hn, ?_⟩
  have ha' : a = c₀ * (c * p * r) * c₀⁻¹ := by rw [← hdec]; group
  rw [ha']
  group

theorem GNAbsorbs.of_normal_factor {A : Subgroup X} (hA : A.Normal)
    (h : ∀ u ∈ A, ∃ a ∈ Subgroup.centralizer (T₁ : Set X), ∃ b ∈ Subgroup.normalizer (T₂ : Set X),
      b ∈ Subgroup.normalizer (Y0 T T₁ T₂ : Set X) ∧ u = a * b) :
    GNAbsorbs T T₁ T₂ A := by
  refine GNAbsorbs.of_normal_decomp hA fun u hu => ?_
  obtain ⟨a, ha, b, hb, hbY, hab⟩ := h u hu
  exact ⟨a, ha, 1, one_mem _, b, hb, hbY, by rw [hab, mul_one]⟩

@[expose] noncomputable def gnKMin (T : Subgroup X) : Subgroup X :=
  Subgroup.normalClosure ((⁅gnHPre T, thompsonJ T⁆ : Subgroup X) : Set X)

omit [Finite X] in
instance gnKMin_normal : (gnKMin T).Normal := Subgroup.normalClosure_normal

omit [Finite X] in
theorem commutator_gnHPre_le_gnKMin : ⁅gnHPre T, thompsonJ T⁆ ≤ gnKMin T :=
  Subgroup.subset_normalClosure

omit [Finite X] in
theorem gnKMin_le_gnHPre : gnKMin T ≤ gnHPre T := by
  haveI : (gnHPre T).Normal := gnHPre_normal
  exact Subgroup.normalClosure_le_normal (Subgroup.commutator_le_left _ _)

theorem gnHPre_le_gnKMin_sup_normalizer (hX : GNSetting X T) :
    gnHPre T ≤ gnKMin T ⊔ Subgroup.normalizer (thompsonJ T : Set X) := by
  intro h hh
  obtain ⟨b, hb, n, hn, rfl⟩ := eq_mul_normalizer_thompsonJ_of_commutator_le hX.sylow
    gnKMin_normal gnKMin_le_gnHPre commutator_gnHPre_le_gnKMin h hh
  exact Subgroup.mul_mem_sup hb hn.2

theorem gnAbsorbs_H_of_gnKMin (hX : GNSetting X T) (hP : IsC118Pair T T₁ T₂)
    (hK : GNAbsorbs T T₁ T₂ (gnKMin T)) : GNAbsorbs T T₁ T₂ (gnHPre T) := by
  obtain ⟨-, h1, -, -, h2, h2c, -⟩ := hP
  exact GNAbsorbs.of_le_mul_normalizer_thompsonJ hX.sylow h1 h2 h2c gnKMin_normal gnHPre_normal
    gnKMin_le_gnHPre (gnHPre_le_gnKMin_sup_normalizer hX) hK

@[expose] def GNLayerFactor (T T₁ T₂ : Subgroup X) : Prop :=
  ∀ k ∈ gnKMin T, ∃ a ∈ Subgroup.centralizer (T₁ : Set X), ∃ b ∈ Subgroup.normalizer (T₂ : Set X),
    b ∈ Subgroup.normalizer (Y0 T T₁ T₂ : Set X) ∧ k = a * b

theorem gnAbsorbs_gnKMin (h : GNLayerFactor T T₁ T₂) : GNAbsorbs T T₁ T₂ (gnKMin T) :=
  GNAbsorbs.of_normal_factor gnKMin_normal h

theorem gnAbsorbs_H_of_layerFactor (hX : GNSetting X T) (hP : IsC118Pair T T₁ T₂)
    (hres : GNLayerFactor T T₁ T₂) : GNAbsorbs T T₁ T₂ (gnHPre T) :=
  gnAbsorbs_H_of_gnKMin hX hP (gnAbsorbs_gnKMin hres)

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
