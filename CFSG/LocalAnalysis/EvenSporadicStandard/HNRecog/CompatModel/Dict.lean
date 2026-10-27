module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CompatModel.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.HData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.SubModel

public section

namespace CFSG.EvenSporadicStandard.HNRecog.CompatModel

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3
  CFSG.EvenSporadicStandard.HNRecog.Section3Model CFSG.EvenSporadicStandard.HNRecog.Section4

structure VertexIso {G : Type} [Group G] (d z : G) (Ψ : ↥(Gx d) ≃* ↥P1408) : Prop where
  self_eq : Ψ (GxSelf d) = pA
  in2A : ∀ t : ↥(Gx d), IsConj d (t : G) ↔ In2A (Ψ t)
  in2B : ∀ t : ↥(Gx d), IsConj z (t : G) ↔ In2B (Ψ t)

theorem isConj_iff_of_isConj {H H' : Type} [Group H] [Group H'] (Ψ : H ≃* H') {x : H} {p : H'}
    (hp : IsConj p (Ψ x)) {t : H} : IsConj x t ↔ IsConj p (Ψ t) :=
  ⟨fun h => hp.trans (TwoHSData.isConj_map_mulEquiv Ψ h),
    fun h => TwoHSData.isConj_of_map_mulEquiv Ψ (hp.symm.trans h)⟩

theorem VertexIso.isConj_a_iff {G : Type} [Group G] {a z d : G} {Ψ : ↥(Gx d) ≃* ↥P1408}
    (hΨ : VertexIso d z Ψ) (hd : IsConj a d) (t : ↥(Gx d)) : IsConj a (t : G) ↔ In2A (Ψ t) :=
  ⟨fun ht => (hΨ.in2A t).1 (hd.symm.trans ht), fun ht => hd.trans ((hΨ.in2A t).2 ht)⟩

theorem exists_hSideData_at {G : Type} [Group G] {a z : G} (h : F5Std a z) {d : G}
    (hd : IsConj a d) : HSideData d z :=
  exists_hSideData h.iface (isF5Type_of_isConj h.typ hd (IsConj.refl z))
    (h.loc.fusion1 d z hd (IsConj.refl z)) (h.loc.fusion2 d z hd (IsConj.refl z))
    (h.loc.a8pictures d z hd (IsConj.refl z))

section Cert

theorem vertexIso_of_labelled {G : Type} [Group G] {d z : G} {z₀ b₀ u₀ : ↥(Gx d)}
    (L : HLab d z z₀ b₀ u₀) {Ψ : ↥(Gx d) ≃* ↥P1408} (hΨ : IsLabelled Ψ (GxSelf d) z₀ b₀ u₀) :
    VertexIso d z Ψ := by
  have hA : IsConj pA (Ψ (GxSelf d)) := by rw [hΨ.a_eq]
  have hAZ : IsConj (pA * pZ) (Ψ (GxSelf d * z₀)) := by
    rw [map_mul, hΨ.a_eq]
    obtain ⟨c, hc⟩ := isConj_iff.1 hΨ.z_conj
    exact isConj_iff.2 ⟨c, by
      rw [show c * (pA * pZ) * c⁻¹ = (c * pA * c⁻¹) * (c * pZ * c⁻¹) by group,
        conj_pA_eq' c, hc]⟩
  refine ⟨hΨ.a_eq, fun t => ?_, fun t => ?_⟩
  · rw [← L.isA_iff t]
    exact or_congr (isConj_iff_of_isConj Ψ hA) (or_congr (isConj_iff_of_isConj Ψ hAZ)
      (isConj_iff_of_isConj Ψ hΨ.b_conj))
  · rw [← L.isB_iff t]
    exact or_congr (isConj_iff_of_isConj Ψ hΨ.z_conj) (isConj_iff_of_isConj Ψ hΨ.z₁_conj)

theorem natCard_P1408_of_F5Std {G : Type} [Group G] {a z : G} (h : F5Std a z) :
    Nat.card ↥P1408 = 177408000 := by
  obtain ⟨E, hE⟩ := h.typ.cent_a
  exact card_P1408 (hsCtx_of_isHSCover hE.toIsHSCover)

theorem exists_vertexIso_at_pB {G : Type} [Group G] {a z : G} (h : F5Std a z) {d y : G}
    (hd : IsConj a d) (hy : y ∈ orb2A a d) :
    ∃ hyd : y ∈ Gx d, ∃ Ψ : ↥(Gx d) ≃* ↥P1408, VertexIso d z Ψ ∧ Ψ ⟨y, hyd⟩ = pB := by
  have hyd : y ∈ Gx d := h.mem_Gx_of_orb2A hd hy
  obtain ⟨E, z₀, b₀, u₀, hE, L, hD⟩ := exists_hSideData_at h hd
  have hyb : IsConj b₀ (⟨y, hyd⟩ : ↥(Gx d)) :=
    (L.isConj_b₀_iff _).2 ⟨hd.symm.trans hy.1, hd.symm.trans hy.2⟩
  obtain ⟨Ψ, hΨ, hΨy⟩ := exists_labelled_iso_at_b hE L.facts hD hyb
  exact ⟨hyd, Ψ, vertexIso_of_labelled L hΨ, hΨy⟩

end Cert

end CFSG.EvenSporadicStandard.HNRecog.CompatModel
