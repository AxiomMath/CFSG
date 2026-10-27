module

public import CFSG.GH74.Generic.S1.GlueLinFull
public import CFSG.GH74.Generic.S1.GlueUni
public import CFSG.GH74.Generic.S1.GlueLin

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic

variable {G : Type} [Group G] [Finite G]

theorem not_goodFixed_conjNormal {x : G} (hx : orderOf x = 2) {K : Subgroup (CentralizerBar x)}
    [K.Normal] (hxK : xbar x ∈ K) (hfront : S1Front G x K) {v : G}
    (hv : v ∈ centralizer ({x} : Set G)) (hconj : IsConj x v) (hvx : v ≠ x) (hv2 : v * v = 1) :
    ¬ GoodFixedCentral (ThreeModel ↥K) (MulAut.conjNormal (barOf hv) : MulAut ↥K) := by
  rintro ⟨H, hfix, hz, hgood⟩
  refine false_of_goodFixed hx hfront.good_le hfront.b5 hv hconj hvx hv2 (H.map K.subtype)
    (map_subtype_le_centralizer H hfix) ?_ (goodSub_map K.subtype hgood)
  refine ⟨⟨xbar x, hxK⟩, hz _ ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (xbar_comm x (g : CentralizerBar x))

omit [Finite G] in
theorem conjNormal_involutory {x : G} {K : Subgroup (CentralizerBar x)} [K.Normal]
    (hcentle : Subgroup.centralizer (K : Set (CentralizerBar x)) ≤ K) {v : G}
    (hv : v ∈ centralizer ({x} : Set G)) (hv2 : v * v = 1) (hvK : barOf hv ∉ K) :
    (MulAut.conjNormal (barOf hv) : MulAut ↥K) * MulAut.conjNormal (barOf hv) = 1 ∧
      ∀ k : ↥K, (MulAut.conjNormal (barOf hv) : MulAut ↥K) ≠ MulAut.conj k := by
  have hbar2 : barOf hv * barOf hv = 1 := by
    have : proj x ((⟨v, hv⟩ : ↥(centralizer ({x} : Set G))) * ⟨v, hv⟩) = 1 := by
      rw [show (⟨v, hv⟩ : ↥(centralizer ({x} : Set G))) * ⟨v, hv⟩ = 1 from Subtype.ext hv2,
        map_one]
    rwa [map_mul] at this
  refine ⟨?_, fun k h => hvK (mem_of_conjNormal_inner hcentle h)⟩
  rw [← map_mul, hbar2, map_one]

theorem outer_reflection_lin (hExo : S1ExoticExcludedExplicit) {y : G}
    {K : Subgroup (CentralizerBar y)} [K.Normal] (hset : S1Setup G y K) (hfront : S1Front G y K) {v : G}
    (hv : v ∈ centralizer ({y} : Set G)) (hconj : IsConj y v) (hvy : v ≠ y) (hv2 : v * v = 1)
    (hvK : barOf hv ∉ K) {F : Type} [Field F] [Finite F] (hF : Nat.card F % 4 = 3)
    (e : ↥K ≃* ↥(StatedSL 4 F)) :
    IsReflection (StatedSL 4 F) (MulAut.congr e (MulAut.conjNormal (barOf hv) : MulAut ↥K)) := by
  have hxK : xbar y ∈ K := hset.shape.2
  have hcentle : Subgroup.centralizer (K : Set (CentralizerBar y)) ≤ K := by
    rw [hfront.cent_eq]
    exact (Subgroup.zpowers_le).2 hxK
  obtain ⟨hα2, hout⟩ := conjNormal_involutory hcentle hv hv2 hvK
  have hnotA := not_goodFixed_conjNormal hset.inv hxK hfront hv hconj hvy hv2
  have hback : ∀ (hA : GoodFixedCentral (Nat.card F = 3)
      (MulAut.congr e (MulAut.conjNormal (barOf hv) : MulAut ↥K))), False := fun hA => by
    apply hnotA
    have h1 := (hA.of_mulEquiv e.symm).mono (T' := ThreeModel ↥K) (fun h => ⟨F, inferInstance,
      inferInstance, h, Or.inl ⟨e⟩⟩)
    rwa [congr_symm_congr] at h1
  rcases linClassify F hF (MulAut.congr e (MulAut.conjNormal (barOf hv) : MulAut ↥K))
    (congr_mul_self_eq_one e hα2) (congr_not_inner e hout) with hA | hR | hG
  · exact (hback hA).elim
  · exact hR
  · rcases graphLinRefine F hF (MulAut.congr e (MulAut.conjNormal (barOf hv) : MulAut ↥K))
      (congr_mul_self_eq_one e hα2) hG with hA | hE
    · exact (hback hA).elim
    · exact (hExo G y K hset hfront v hv hconj hvy hv2 hvK _
        (fun k => by simp [MulAut.conjNormal_apply]) (Or.inl ⟨F, inferInstance, inferInstance, e, hF, hE⟩)).elim

theorem outer_reflection_uni (hExo : S1ExoticExcludedExplicit) {y : G}
    {K : Subgroup (CentralizerBar y)} [K.Normal] (hset : S1Setup G y K) (hfront : S1Front G y K) {v : G}
    (hv : v ∈ centralizer ({y} : Set G)) (hconj : IsConj y v) (hvy : v ≠ y) (hv2 : v * v = 1)
    (hvK : barOf hv ∉ K) {q : ℕ} {F : Type} [Field F] [Finite F] (hF : Nat.card F = q ^ 2)
    (hq : q % 4 = 1) (e : ↥K ≃* ↥(StatedSU 4 q F)) :
    IsReflection (StatedSU 4 q F) (MulAut.congr e (MulAut.conjNormal (barOf hv) : MulAut ↥K)) := by
  have hxK : xbar y ∈ K := hset.shape.2
  have hcentle : Subgroup.centralizer (K : Set (CentralizerBar y)) ≤ K := by
    rw [hfront.cent_eq]
    exact (Subgroup.zpowers_le).2 hxK
  obtain ⟨hα2, hout⟩ := conjNormal_involutory hcentle hv hv2 hvK
  have hnotA := not_goodFixed_conjNormal hset.inv hxK hfront hv hconj hvy hv2
  have hback : ∀ (hA : GoodFixedCentral False
      (MulAut.congr e (MulAut.conjNormal (barOf hv) : MulAut ↥K))), False := fun hA => by
    apply hnotA
    have h1 := (hA.of_mulEquiv e.symm).mono (T' := ThreeModel ↥K) (fun h => h.elim)
    rwa [congr_symm_congr] at h1
  rcases uniClassify F q hF hq (MulAut.congr e (MulAut.conjNormal (barOf hv) : MulAut ↥K))
    (congr_mul_self_eq_one e hα2) (congr_not_inner e hout) with hA | hR | hG
  · exact (hback hA).elim
  · exact hR
  · rcases graphUniRefine F q hF hq (MulAut.congr e (MulAut.conjNormal (barOf hv) : MulAut ↥K))
      (congr_mul_self_eq_one e hα2) hG with hA | hE
    · exact (hback hA).elim
    · exact (hExo G y K hset hfront v hv hconj hvy hv2 hvK _
        (fun k => by simp [MulAut.conjNormal_apply])
        (Or.inr ⟨q, F, inferInstance, inferInstance, e, hF, hq, hE⟩)).elim

end CFSG.GH74.Generic.S1
