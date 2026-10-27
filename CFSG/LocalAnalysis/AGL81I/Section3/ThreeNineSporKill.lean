module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporBigOvergroup

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporBig

theorem false_of_not_dvd_of_gLAPPrimeCoreOf_eq_bot {L : Type} [Group L] [Finite L] {p : ℕ}
    (hp : p.Prime) {Y J : Subgroup L} (hO : CFSG.Open.GLAPPrimeCoreOf p Y = ⊥) (hJY : J ≤ Y)
    (hJn : (J.subgroupOf Y).Normal) (hpJ : ¬ p ∣ Nat.card ↥J)
    (hJna : ∃ a b : ↥J, a * b ≠ b * a) : False := by
  have hS : ∀ g ∈ Y, ∀ x ∈ J, g * x * g⁻¹ ∈ J :=
    fun g hg x hx => (Subgroup.normal_subgroupOf_iff hJY).mp hJn x g hx hg
  have hle : J ≤ CFSG.Open.GLAPPrimeCoreOf p Y :=
    CFSG.HardMathSupport.Timmesfeld.Proving.le_GLAPPrimeCoreOf_of_normal hJY hS
      ((hp.coprime_iff_not_dvd).2 hpJ)
  rw [hO] at hle
  have hbot : J = ⊥ := le_bot_iff.mp hle
  have hsub : Subsingleton ↥J := by rw [hbot]; infer_instance
  obtain ⟨a, b, hab⟩ := hJna
  exact hab (by rw [hsub.allEq a b])

theorem le_of_forall_mem_inner {L : Type} [Group L] [Finite L] {Y J : Subgroup L}
    (hJY : J ≤ Y) (hJn : (J.subgroupOf Y).Normal)
    (hJC : Subgroup.centralizer (J : Set L) ⊓ Y = ⊥)
    (hinn : ∀ α : MulAut ↥J, α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥J) :
    Y ≤ J := by
  intro g hg
  have hnorm : (J.subgroupOf Y).Normal := hJn
  let e : ↥(J.subgroupOf Y) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJY
  let α : MulAut ↥J :=
    MulAut.congr e
      (@MulAut.conjNormal ↥Y _ (J.subgroupOf Y) hnorm (⟨g, hg⟩ : ↥Y))
  obtain ⟨j, hj⟩ := hinn α
  have hα : ∀ x : ↥J, ((α x : ↥J) : L) = g * (x : L) * g⁻¹ := by
    intro x
    change ((Subgroup.subgroupOfEquivOfLe hJY
      ((@MulAut.conjNormal ↥Y _ (J.subgroupOf Y) hnorm (⟨g, hg⟩ : ↥Y))
        ((Subgroup.subgroupOfEquivOfLe hJY).symm x)) : ↥J) : L) = g * (x : L) * g⁻¹
    rw [Subgroup.subgroupOfEquivOfLe_apply_coe, MulAut.conjNormal_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.subgroupOfEquivOfLe_symm_apply_coe_coe]
  have hconj : ∀ x : ↥J, (j : L) * (x : L) * (j : L)⁻¹ = g * (x : L) * g⁻¹ := by
    intro x
    have h := congrArg (fun f : MulAut ↥J => ((f x : ↥J) : L)) hj
    rw [MulAut.conj_apply] at h
    rw [hα x] at h
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h
  have hcomm : (j : L)⁻¹ * g ∈ Subgroup.centralizer (J : Set L) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h := hconj ⟨x, hx⟩
    calc x * ((j : L)⁻¹ * g) = (j : L)⁻¹ * ((j : L) * x * (j : L)⁻¹) * g := by group
      _ = (j : L)⁻¹ * (g * x * g⁻¹) * g := by rw [h]
      _ = ((j : L)⁻¹ * g) * x := by group
  have hmem : (j : L)⁻¹ * g ∈ Subgroup.centralizer (J : Set L) ⊓ Y :=
    ⟨hcomm, Y.mul_mem (Y.inv_mem (hJY j.2)) hg⟩
  rw [hJC] at hmem
  have hjg : (j : L)⁻¹ * g = 1 := by simpa using hmem
  have hgj : g = (j : L) := by
    calc g = (j : L) * ((j : L)⁻¹ * g) := by group
      _ = (j : L) := by rw [hjg, mul_one]
  rw [hgj]
  exact j.2

theorem index_modEq_one_of_data {L : Type} [Group L] [Finite L] {p d : ℕ} {Y : Subgroup L}
    (h : SporOvergroupData L p d Y) : Y.index ≡ 1 [MOD d] := by
  have hfact : Fact d.Prime := ⟨h.d_prime⟩
  obtain ⟨D, hDsyl, hDne, hDnorm⟩ := h.sylowD
  have hDindex : ¬ d ∣ D.index := by
    have h' :=
      (@CFSG.ABGLocalTools.isSylowOf_iff L _ d _ hfact D ⊤).mp hDsyl
    simpa [Subgroup.relIndex_top_right] using h'.2.2
  exact @CFSG.LocalAnalysis.AGL81I.Section3.index_modEq_one_of_normalizer_le
    L _ _ d hfact
    (@IsPGroup.toSylow d L _ hfact D hDsyl.isPGroup hDindex) Y
    (by rw [IsPGroup.toSylow_coe]; exact hDnorm D le_rfl hDne)

theorem false_of_four_le_pRank_of_data {L : Type} [Group L] [Finite L] {p d : ℕ}
    {Y : Subgroup L} (h : SporOvergroupData L p d Y) (J : Subgroup L)
    (hJ : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥J)) : False := by
  have hp : 1 < p := h.prime.one_lt
  have hle : CFSG.Open.pRank p (⊤ : Subgroup ↥J) ≤ CFSG.Open.pRank p (⊤ : Subgroup L) :=
    CFSG.SectionRank.pRank_top_le_of_injective (G := ↥J) (G' := L) hp
      J.subtype J.subtype_injective
  exact absurd (hJ.trans (hle.trans h.rank_le)) (by omega)

end CFSG.LocalAnalysis.AGL81I.Section3.SporBig
