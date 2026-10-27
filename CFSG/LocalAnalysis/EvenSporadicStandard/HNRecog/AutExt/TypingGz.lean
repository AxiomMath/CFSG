module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.GzBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.XFusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.NotConj

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'}

private theorem Gx_inf_mul_eq {G : Type} [Group G] {w d : G} (hww : w * w = 1) :
    Gx w ⊓ Gx (w * d) = Gx w ⊓ Gx d := by
  have hd_eq : w * (w * d) = d := by rw [← mul_assoc, hww, one_mul]
  ext g
  simp only [Subgroup.mem_inf, mem_Gx]
  constructor
  · rintro ⟨hgw, hgwd⟩
    refine ⟨hgw, ?_⟩
    calc d * g = w * (w * d) * g := by rw [hd_eq]
      _ = w * ((w * d) * g) := by rw [mul_assoc]
      _ = w * (g * (w * d)) := by rw [hgwd]
      _ = (w * g) * (w * d) := by rw [← mul_assoc]
      _ = (g * w) * (w * d) := by rw [hgw]
      _ = g * (w * (w * d)) := by rw [mul_assoc]
      _ = g * d := by rw [hd_eq]
  · rintro ⟨hgw, hgd⟩
    refine ⟨hgw, ?_⟩
    calc (w * d) * g = w * (d * g) := by rw [mul_assoc]
      _ = w * (g * d) := by rw [hgd]
      _ = (w * g) * d := by rw [← mul_assoc]
      _ = (g * w) * d := by rw [hgw]
      _ = g * (w * d) := by rw [mul_assoc]

theorem typing_Gz (h : F5Std a z) (h' : F5Std a' z') {w : G} {w' : G'} (hw : IsConj z w)
    (hw' : IsConj z' w') {φ : G → G'} (hφ : IsIsoOn (Gx w) (Gx w') φ) {d : G}
    (hd : IsConj a d) (hdw : d ∈ Gx w ∧ IsConj z (w * d)) (hφd : IsConj a' (φ d)) :
    ∀ x ∈ Gx w, IsConj a x → IsConj a' (φ x) := by
  have hF : F5Std a w := h.of_isConj (IsConj.refl a) hw
  have hF' : F5Std a' w' := h'.of_isConj (IsConj.refl a') hw'
  have hO : GzOrbitFacts a w := hF.loc.gzOrbit.self
  have hO' : GzOrbitFacts a' w' := hF'.loc.gzOrbit.self
  have hC' : GzClassFacts a' w' := hF'.loc.gzClass.self
  have hφw : φ w = w' := iso_apply_self_Gz hF hF' hφ
  have hw2 : w ^ 2 = 1 := by
    simpa [h.orderOf_eq_two (Or.inr hw)] using pow_orderOf_eq_one w
  have hww : w * w = 1 := by simpa [pow_two] using hw2
  have hd1 : d ≠ 1 := by
    intro hd1
    have h2 := h.orderOf_eq_two (Or.inl hd)
    rw [hd1, orderOf_one] at h2
    omega
  have hinf : Gx w ⊓ Gx (w * d) = Gx w ⊓ Gx d := Gx_inf_mul_eq hww
  have hdO : d ∈ Gx w ∧ d ∉ Qz w ∧ IsConj a d := by
    refine ⟨hdw.1, ?_, hd⟩
    intro hdQ
    exfalso
    have hwQ : w ∈ Qz w := self_mem_Qz hw2
    have hwdQ : w * d ∈ Qz w := (Qz w).mul_mem hwQ hdQ
    have hconj : IsConj w (w * d) := hw.symm.trans hdw.2
    have hne : w * d ≠ w := by
      intro heq
      have h1 : d = 1 := by
        have h2 := congrArg (fun t => w⁻¹ * t) heq
        simp only [← mul_assoc, inv_mul_cancel, one_mul] at h2
        exact h2
      exact hd1 h1
    have hQB := hO.orbit_QB.2 (w * d) ⟨hwdQ, hconj, hne⟩
    have hQA := hO.orbit_QA.2 d ⟨hdQ, hd⟩
    rw [hinf, hQA] at hQB
    exact absurd hQB (by norm_num)
  intro x hxGx hx
  by_cases hxQ : x ∈ Qz w
  · have hφxQ : φ x ∈ Qz w' := (IsIsoOn.mem_Qz_iff hφ hxGx).mp hxQ
    have hφx2 : orderOf (φ x) = 2 :=
      (hφ.orderOf_eq hxGx).trans (h.orderOf_eq_two (Or.inl hx))
    rcases hC'.inv_two (φ x) hφx2 with hφxA | hφxw
    · exact hφxA
    · exfalso
      have hne : φ x ≠ w' := by
        intro heq
        have hxw : x = w := hφ.injOn x hxGx w (self_mem_Gx w) (heq.trans hφw.symm)
        have haw : IsConj a w := hxw ▸ hx
        exact (not_isConj_of_isF5Type h.iface h.typ) (haw.trans hw.symm)
      have hmem : φ x ∈ {q | q ∈ Qz w' ∧ IsConj w' q ∧ q ≠ w'} := ⟨hφxQ, hφxw, hne⟩
      have hQB := hO'.orbit_QB.2 (φ x) hmem
      have hQA := hO.orbit_QA.2 x ⟨hxQ, hx⟩
      have hcard := (hφ.restrict_cent hxGx).natCard_eq
      rw [hQA] at hcard
      rw [hQB] at hcard
      exact absurd hcard (by norm_num)
  · have hmem_x : x ∈ {q | q ∈ Gx w ∧ q ∉ Qz w ∧ IsConj a q} := ⟨hxGx, hxQ, hx⟩
    obtain ⟨k, hk, hkxd⟩ := hO.orbit_outA.1.transitive d hdO x hmem_x
    have hconj : IsConj (φ d) (φ x) := isConj_iff.mpr ⟨φ k, by
      rw [← hkxd, hφ.map_conj hk hdw.1]⟩
    exact hφd.trans hconj

end CFSG.EvenSporadicStandard.HNRecog.Section4
