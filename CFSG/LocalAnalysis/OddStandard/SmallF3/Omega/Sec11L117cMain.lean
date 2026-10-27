module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117cI
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117cII
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117cJ
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117cU

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

namespace Sec11cCnt

variable {z : G} {R T C D Q1 Q2 : Subgroup G} {a x : G}

theorem bound [Finite G] (h : Sec11cCnt G z R T C D Q1 Q2 a x) {Y : Subgroup G}
    (hY : IsCyclic Y) (hYD : Y ≤ D) (hYi : Y.relIndex D = 2)
    (hnab : ∃ u ∈ D, ∃ v ∈ D, u * v ≠ v * u) {t : G} (ht2 : t * t = 1) (htz : t ≠ z)
    (hcl : ∀ g ∈ R, g * t * g⁻¹ ∈ conjClassIn D t → g ∈ T ⊔ D)
    (hR : R = T ⊔ D ∨ ∃ t' : G, t' * t' = 1 ∧ D = zpowers t ⊔ zpowers t')
    {V : Subgroup G} (hVR : V ≤ R) (hV : IsElemAbelianMod z V) :
    V ≤ D ⊔ (Q1 ⊔ Q2) ∨ Nat.card V ≤ 64 := by
  have hP : Sec11cProj G z D (Q1 ⊔ Q2) V := h.proj hVR hV
  by_cases hVTD : V ≤ T ⊔ D
  ·
    have hk8 : Nat.card ↥(D ⊓ (V ⊔ (Q1 ⊔ Q2))) ≤ 8 :=
      sec11c_card_le_eight hY hYD hYi h.cnt.z_sq inf_le_left hP.elemAb
    rcases h.caseI hVTD hV (k := 8) hk8 with hle | hcard
    · exact Or.inl hle
    · exact Or.inr (by norm_num at hcard; omega)
  ·
    obtain ⟨y, hyV, hyTD⟩ := SetLike.not_le_iff_exists.mp hVTD
    have hRne : R ≠ T ⊔ D := by
      intro heq
      exact hyTD (heq ▸ hVR hyV)
    rcases hR with heq | ⟨t', ht'2, ht'eq⟩
    · exact absurd heq hRne
    · have hdih : Sec11cDih G D t t' z :=
        { t_sq := ht2
          t'_sq := ht'2
          eq := ht'eq
          two := h.R_two.to_le h.D_le
          nonab := hnab
          z_mem := h.z_memD
          z_cent := fun d hd => h.R_z d (h.D_le hd)
          z_sq := h.cnt.z_sq
          z_ne := h.cnt.z_ne
          t_ne := htz }
      obtain ⟨hDV4, hV2, hVDQ32⟩ := h.caseII hdih hcl hVR hV hyV hyTD
      have hV0el : IsElemAbelianMod z (V ⊓ (T ⊔ D)) :=
        sec11_isElemAbelianMod_mono inf_le_left hV
      have hk4 : Nat.card ↥(D ⊓ ((V ⊓ (T ⊔ D)) ⊔ (Q1 ⊔ Q2))) ≤ 4 :=
        le_trans (Subgroup.card_le_of_le (Sec11cProj.proj_mono (D := D) (Q := Q1 ⊔ Q2)
          (V := V) (V' := V ⊓ (T ⊔ D)) inf_le_left)) hDV4
      have hV0le : Nat.card ↥(V ⊓ (T ⊔ D)) ≤ 32 := by
        rcases h.caseI (V := V ⊓ (T ⊔ D)) inf_le_right hV0el (k := 4) hk4 with hle | hcard
        · have hsub : V ⊓ (T ⊔ D) ≤ V ⊓ (D ⊔ (Q1 ⊔ Q2)) := le_inf inf_le_left hle
          exact le_trans (Subgroup.card_le_of_le hsub) hVDQ32
        · norm_num at hcard
          exact hcard
      refine Or.inr ?_
      calc Nat.card V ≤ 2 * Nat.card ↥(V ⊓ (T ⊔ D)) := hV2
        _ ≤ 2 * 32 := Nat.mul_le_mul_left 2 hV0le
        _ = 64 := by norm_num

theorem JMod_eq [Finite G] (h : Sec11cCnt G z R T C D Q1 Q2 a x) {Y : Subgroup G}
    (hY : IsCyclic Y) (hYD : Y ≤ D) (hYi : Y.relIndex D = 2)
    (hY4 : ∀ u ∈ D, u ∉ Y → u ^ 4 = 1) (hnab : ∃ u ∈ D, ∃ v ∈ D, u * v ≠ v * u) {t : G}
    (ht2 : t * t = 1) (htz : t ≠ z) (hcl : ∀ g ∈ R, g * t * g⁻¹ ∈ conjClassIn D t → g ∈ T ⊔ D)
    (hR : R = T ⊔ D ∨ ∃ t' : G, t' * t' = 1 ∧ D = zpowers t ⊔ zpowers t') :
    JMod z R = D ⊔ (Q1 ⊔ Q2) := by
  have hHR : D ⊔ (Q1 ⊔ Q2) ≤ R := sup_le h.D_le (h.Q_le_T.trans h.T_le)
  have hexY : ∃ u0 ∈ D, u0 ∉ Y := by
    by_contra hcon
    push_neg at hcon
    have hle : D ≤ Y := fun u hu => hcon u hu
    have h1 : Y.relIndex D = 1 := Subgroup.relIndex_eq_one.mpr hle
    rw [h1] at hYi
    norm_num at hYi
  obtain ⟨u0, hu0D, hu0Y⟩ := hexY
  obtain ⟨U0, hU0H, hzU0, hU0el, hU0card, -, hQU0⟩ :=
    h.exists_U hY hYD hYi hY4 hnab hu0D hu0Y
  refine sec11c_JMod_eq (N := 128) (H := D ⊔ (Q1 ⊔ Q2)) hHR ?_ ?_ ?_ ?_
  ·
    intro V hVR hzV hVel
    rcases h.bound hY hYD hYi hnab ht2 htz hcl hR hVR hVel with hle | hcard
    · exact Or.inl hle
    · exact Or.inr (by omega)
  ·
    intro V hVH hzV hVel
    exact h.card_le_of_le_DQ hY hYD hYi hVH hVel
  · exact ⟨U0, hU0H, hzU0, hU0el, hU0card⟩
  ·
    refine sup_le ?_ ?_
    · refine (sec11c_le_closure_compl hYD hYi).trans (Subgroup.closure_mono ?_)
      rintro u ⟨huD, huY⟩
      obtain ⟨U, hUH, hzU, hUel, hUcard, huU, -⟩ := h.exists_U hY hYD hYi hY4 hnab huD huY
      exact ⟨U, hUH, hzU, hUel, hUcard, huU⟩
    · refine hQU0.trans ?_
      intro q hq
      exact Subgroup.subset_closure ⟨U0, hU0H, hzU0, hU0el, hU0card, hq⟩

end Sec11cCnt

end CFSG.OddStandard.SmallF3.Omega
