
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4ClassBase
public import CFSG.Sporadic.J4.QTProof

@[expose] public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

def TwoAPure (V : Subgroup ↥J) : Prop :=
  ∀ v ∈ V, v ≠ 1 → IsConj (eta uJ 11 3) v

def HasTwoB (V : Subgroup ↥J) : Prop :=
  ∃ v ∈ V, IsConj (eta uJ 11 1) v

def HasCommonFixedPt (V : Subgroup ↥J) : Prop :=
  ∃ y ∈ Subgroup.normalizer (V : Set ↥J), orderOf y = 5 ∧ (∀ v ∈ V, y * v = v * y → v = 1) ∧
    ∃ g : ↥J, V ≤ Hj.map (cm g) ∧ y ∈ Hj.map (cm g)

theorem twoAPure_map_cm (m : ↥J) {V : Subgroup ↥J} (h : TwoAPure V) :
    TwoAPure (V.map (cm m)) := by
  rintro _ ⟨v, hv, rfl⟩ hne
  have hv1 : v ≠ 1 := by
    rintro rfl
    exact hne (map_one _)
  exact (h v hv hv1).trans (isConj_iff.2 ⟨m, rfl⟩)

theorem hasTwoB_map_cm (m : ↥J) {V : Subgroup ↥J} (h : HasTwoB V) : HasTwoB (V.map (cm m)) := by
  obtain ⟨v, hv, hc⟩ := h
  exact ⟨cm m v, ⟨v, hv, rfl⟩, hc.trans (isConj_iff.2 ⟨m, rfl⟩)⟩

theorem hasCommonFixedPt_map_cm (m : ↥J) {V : Subgroup ↥J} (h : HasCommonFixedPt V) :
    HasCommonFixedPt (V.map (cm m)) := by
  obtain ⟨y, hy, hy5, hfpf, g, hVg, hyg⟩ := h
  refine ⟨cm m y, ?_, ?_, ?_, m * g, ?_, ?_⟩
  · have e := normalizer_map_equiv_eq (MulAut.conj m) V
    change cm m y ∈ Subgroup.normalizer ((V.map (MulAut.conj m).toMonoidHom : Subgroup ↥J) :
      Set ↥J)
    rw [e]
    exact ⟨y, hy, rfl⟩
  · have h5 := (MulAut.conj m).orderOf_eq y
    rw [MulAut.conj_apply] at h5
    rw [cm_apply, h5]
    exact hy5
  · rintro _ ⟨v, hv, rfl⟩ hcomm
    have h1 : y * v = v * y := by
      have : m * y * m⁻¹ * (m * v * m⁻¹) = m * v * m⁻¹ * (m * y * m⁻¹) := hcomm
      have h2 : m * (y * v) * m⁻¹ = m * (v * y) * m⁻¹ := by
        calc m * (y * v) * m⁻¹ = m * y * m⁻¹ * (m * v * m⁻¹) := by group
          _ = m * v * m⁻¹ * (m * y * m⁻¹) := this
          _ = m * (v * y) * m⁻¹ := by group
      simpa using h2
    have := hfpf v hv h1
    rw [this]
    simp [cm_apply]
  · rw [← map_cm_map_cm]
    exact Subgroup.map_mono hVg
  · rw [← map_cm_map_cm]
    exact ⟨y, hyg, rfl⟩

end CFSG.QuasithinUnique.A5
