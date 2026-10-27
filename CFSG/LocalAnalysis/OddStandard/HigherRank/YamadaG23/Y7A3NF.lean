module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2P3
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1P1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7a_A_le_of_F (c : Ctx7 G L) (hH : F33Hyp c.s c.e) {D : Subgroup G}
    (hD : ∀ k ∈ normIn L c.s.fr.A, ∀ x ∈ D, k * x * k⁻¹ ∈ D) (hFD : c.s.fr.F ≤ D) :
    c.s.fr.A ≤ D := by
  have h := c.y7acfg hH
  have hVc : ∀ a ∈ c.s.fr.A, ∀ v ∈ V1 c.e, a * v = v * a :=
    fun a ha v hv => y6_C0_comm h.cfg a ha v (y7a_V_le_C0 h hv)
  have hDA_comm : ∀ a ∈ D ⊓ c.s.fr.A, ∀ v ∈ V1 c.e, a * v = v * a :=
    fun a ha v hv => hVc a (Subgroup.mem_inf.mp ha).2 v hv
  have hkX : ∀ k ∈ normIn L c.s.fr.A, k ∈ y7aX c :=
    fun k hk => y7a_Y_le_X c hH (s5_NLA_le_Y c.toCtx5 hH hk)
  have hkA : ∀ k ∈ normIn L c.s.fr.A, ∀ x ∈ c.s.fr.A, k * x * k⁻¹ ∈ c.s.fr.A :=
    fun k hk x hx => (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp hk).2 x).mp hx
  have hkV : ∀ k ∈ normIn L c.s.fr.A, ∀ v ∈ V1 c.e, k * v * k⁻¹ ∈ V1 c.e :=
    fun k hk v hv => (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp (hkX k hk)).2 v).mp hv
  have hD1inv : ∀ k ∈ normIn L c.s.fr.A, ∀ x ∈ (D ⊓ c.s.fr.A) ⊔ V1 c.e,
      k * x * k⁻¹ ∈ (D ⊓ c.s.fr.A) ⊔ V1 c.e := by
    intro k hk x hx
    obtain ⟨d, hd, v, hv, rfl⟩ :=
      CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.mem_sup_of_commute hDA_comm hx
    have hkx : k * (d * v) * k⁻¹ = (k * d * k⁻¹) * (k * v * k⁻¹) := by group
    rw [hkx]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right (hkV k hk v hv))
    exact Subgroup.mem_inf.mpr ⟨hD k hk d (Subgroup.mem_inf.mp hd).1,
      hkA k hk d (Subgroup.mem_inf.mp hd).2⟩
  have hzF : c.s.fr.z ∈ c.s.fr.F := by
    show c.s.fr.z ∈ closure {c.s.fr.a₁ * c.s.fr.a₂, c.s.fr.b₁ * c.s.fr.b₂, c.s.fr.z}
    exact Subgroup.subset_closure (by simp)
  have hbF : c.s.fr.b₁ * c.s.fr.b₂ ∈ c.s.fr.F := by
    show c.s.fr.b₁ * c.s.fr.b₂ ∈ closure {c.s.fr.a₁ * c.s.fr.a₂, c.s.fr.b₁ * c.s.fr.b₂, c.s.fr.z}
    exact Subgroup.subset_closure (by simp)
  have hb1 : c.s.fr.b₁ ∈ c.s.fr.A := by
    rw [h.cfg.hA]; exact Subgroup.subset_closure (by simp)
  have hb2 : c.s.fr.b₂ ∈ c.s.fr.A := by
    rw [h.cfg.hA]; exact Subgroup.subset_closure (by simp)
  have hb : c.s.fr.b₁ * c.s.fr.b₂ ∈ (D ⊓ c.s.fr.A) ⊔ V1 c.e :=
    Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hFD hbF, c.s.fr.A.mul_mem hb1 hb2⟩)
  have hAD₁ : c.s.fr.A ≤ (D ⊓ c.s.fr.A) ⊔ V1 c.e :=
    y7a_A_le_of_b1b2 c hH le_sup_right (sup_le_sup_right inf_le_right _) hD1inv hb
  intro a ha
  obtain ⟨d, hd, v, hv, hav⟩ :=
    CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.mem_sup_of_commute hDA_comm (hAD₁ ha)
  have hvA : v ∈ c.s.fr.A := by
    have hv_eq : v = d⁻¹ * a := by rw [hav]; group
    rw [hv_eq]
    exact c.s.fr.A.mul_mem (c.s.fr.A.inv_mem (Subgroup.mem_inf.mp hd).2) ha
  have hvZ : v ∈ zpowers c.s.fr.z := by
    rw [← y7a_A_inf_V h]
    exact Subgroup.mem_inf.mpr ⟨hvA, hv⟩
  have hvF : v ∈ c.s.fr.F := (Subgroup.zpowers_le.mpr hzF) hvZ
  rw [hav]
  exact D.mul_mem (Subgroup.mem_inf.mp hd).1 (hFD hvF)

end CFSG.OddStandard.HigherRank.YamadaG23
