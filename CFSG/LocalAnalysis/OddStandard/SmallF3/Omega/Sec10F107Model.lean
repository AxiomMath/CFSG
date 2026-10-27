
module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10F107ModelBase

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10F107Over
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TypesCert
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ModelF1051
public import Certificates.Certificate442006

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.ClassicalInvolution.Q3.TA3.Check
  CFSG.ComponentClassification.GSThmB

namespace Mo107

open Certificates.OmegaS107

local notation "P45" => Equiv.Perm (Fin 45)

theorem Q32_eq_Q0 :
    Q32 = Certificates.OmegaS107.Q0 := by
  have hle : Q32 ≤ Certificates.OmegaS107.Q0 := by
    rw [Q32, Subgroup.closure_le]
    intro x hx
    refine closeL_mem (fun g hg => Subgroup.subset_closure ?_) 6 [1] (fun s hs => ?_) x hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl <;> simp
    · rw [List.mem_singleton.1 hs]
      exact Subgroup.one_mem _
  exact Subgroup.eq_of_le_of_card_ge hle (by
    rw [Certificates.certificate442006.q0_card, card_Q32]
    norm_num)

theorem Q32_le_T0 :
    Q32 ≤ QT0.originalSubgroup := by
  rw [Q32_eq_Q0]
  exact Certificates.certificate442006.q0_le

theorem model107
    {T : Subgroup P45} (hT0 : QT0.originalSubgroup ≤ T)
    (hTA : T ≤ QA45.originalSubgroup) (hT2 : IsPGroup 2 T) {w : P45} (hw : w ∈ T)
    (hwT0 : w ∉ QT0.originalSubgroup) : ∃ B2 y2, Model107 T B2 y2 := by
  obtain ⟨B2, y2, hM⟩ := Certificates.certificate442006.model T hT0 hTA hT2 w hw hwT0
  have hN := normal_over hT0 hTA hT2 hw hwT0
  refine ⟨B2, y2,
    { le := hM.le
      comm := hM.comm
      sq := hM.sq
      card := hM.card
      normal := hM.normal
      normB0 := ?_
      y2_mem := hM.y2_mem
      y2_out := hM.y2_out
      y2_inv := Ty.invC_iff.1 hM.y2_inv
      mem_B2 := fun b => by rw [Q32_eq_Q0]; exact hM.mem_B2 b
      normal_elem := ?_
      meet := hM.meet }⟩
  · intro g hg b hb
    let X := B0.map (MulAut.conj g).toMonoidHom
    have hX : X = B0 := by
      refine eq_B0_of_abelian ?_ ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩
        exact hN g hg a (B0_le_T0 ha)
      · rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩
        have h := (bl0_closed.2.2 a (mem_B0_iff.1 ha)).2.2 c (mem_B0_iff.1 hc)
        simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
        calc g * a * g⁻¹ * (g * c * g⁻¹) = g * (a * c) * g⁻¹ := by group
          _ = g * (c * a) * g⁻¹ := by rw [h.2]
          _ = g * c * g⁻¹ * (g * a * g⁻¹) := by group
      · rw [Subgroup.card_map_of_injective (MulEquiv.injective _), card_B0]
    have hmem : g * b * g⁻¹ ∈ X := ⟨b, hb, rfl⟩
    rwa [hX] at hmem
  · intro X hXT hXc hXs hXcard hXn
    by_cases hXle : X ≤ QT0.originalSubgroup
    · exact Or.inl (eq_B0_of_abelian hXle hXc (by rw [hXcard]; norm_num))
    · exact Or.inr (hM.normal_elem X hXT hXc hXs hXcard hXn hXle)

end Mo107

end CFSG.OddStandard.SmallF3.Omega
