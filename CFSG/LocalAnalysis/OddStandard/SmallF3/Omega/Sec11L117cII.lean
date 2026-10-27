module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117cCtx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117cDih
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117cX

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

namespace Sec11cCnt

variable {z : G} {R T C D Q1 Q2 : Subgroup G} {a x : G}

theorem caseII [Finite G] (h : Sec11cCnt G z R T C D Q1 Q2 a x) {t t' : G}
    (hdih : Sec11cDih G D t t' z) (hcl : ∀ g ∈ R, g * t * g⁻¹ ∈ conjClassIn D t → g ∈ T ⊔ D)
    {V : Subgroup G} (hVR : V ≤ R) (hV : IsElemAbelianMod z V) {y : G} (hyV : y ∈ V)
    (hy : y ∉ T ⊔ D) :
    Nat.card ↥(D ⊓ (V ⊔ (Q1 ⊔ Q2))) ≤ 4 ∧ Nat.card V ≤ 2 * Nat.card ↥(V ⊓ (T ⊔ D)) ∧
      Nat.card ↥(V ⊓ (D ⊔ (Q1 ⊔ Q2))) ≤ 32 := by
  have hP := h.proj hVR hV
  have hyD : ∀ d ∈ D, y * d * y⁻¹ ∈ D := h.R_normD y (hVR hyV)
  have hyz : y * z = z * y := h.R_z y (hVR hyV)
  have hyt : y * t * y⁻¹ ∉ conjClassIn D t := fun hmem => hy (hcl y (hVR hyV) hmem)
  have hDV_le : D ⊓ (V ⊔ (Q1 ⊔ Q2)) ≤ zpowers (t * t') := by
    intro d hd
    by_contra hdρ
    exact (Sec11cDih.comm_not_mem hdih hyD hyz hyt hd.1 hdρ) (hP.cent hyV d hd)
  have h1 : Nat.card ↥(D ⊓ (V ⊔ (Q1 ⊔ Q2))) ≤ 4 :=
    sec11c_card_le_four_of_cyclic (Subgroup.isCyclic_zpowers (t * t')) hDV_le h.cnt.z_sq
      (fun x hx => (hP.elemAb x hx x hx).2)
  have h2 : Nat.card V ≤ 2 * Nat.card ↥(V ⊓ (T ⊔ D)) := by
    refine sec11_card_le_of_cover (k := 2) (r := ![1, y]) ?_ ?_
    · intro i
      fin_cases i <;> simp [hyV]
    · intro g hg
      by_cases hgW : g ∈ T ⊔ D
      · exact ⟨0, by simpa using hgW⟩
      · have hgR : y⁻¹ * g ∈ R := R.mul_mem (R.inv_mem (hVR hyV)) (hVR hg)
        have hconj : (y⁻¹ * g) * t * (y⁻¹ * g)⁻¹ ∈ conjClassIn D t :=
          Sec11cDih.class_of_two hdih hyD hyz (h.R_normD _ hgR) (h.R_z _ hgR) hyt
            (fun hmem => hgW (hcl g (hVR hg) hmem))
        exact ⟨1, by simpa using hcl (y⁻¹ * g) hgR hconj⟩
  have hyDQ : y ∉ D ⊔ (Q1 ⊔ Q2) := fun hmem => hy (h.DQ_le_TD hmem)
  have h3 : Nat.card ↥(V ⊓ (D ⊔ (Q1 ⊔ Q2))) ≤ 32 := by
    have hQy : Nat.card ↥(sec11Qg z y (Q1 ⊔ Q2)) ≤ 16 := h.card_Qg_le (hVR hyV) hyDQ
    have hc := hP.count h.cnt.z_sq h.cnt.z_ne hyV
    have hbound : 2 * Nat.card ↥(V ⊓ (D ⊔ (Q1 ⊔ Q2))) ≤ 64 := by
      calc 2 * Nat.card ↥(V ⊓ (D ⊔ (Q1 ⊔ Q2)))
          ≤ Nat.card ↥(D ⊓ (V ⊔ (Q1 ⊔ Q2))) *
              Nat.card ↥(sec11Qg z y (Q1 ⊔ Q2)) := hc
        _ ≤ 4 * 16 := Nat.mul_le_mul h1 hQy
        _ = 64 := by norm_num
    omega
  exact ⟨h1, h2, h3⟩

end Sec11cCnt

end CFSG.OddStandard.SmallF3.Omega
