module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.L2Basic
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.IP
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Statements

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue

open Subgroup CFSG CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
  CFSG.GH74.GLS.Stage1.Thm6.Sec12b
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x : G} {Kb : Subgroup (CentralizerBar x)} [Kb.Normal]
  {F : Type} [Field F] [Finite F] {e : ↥Kb ≃* IVK.L2 F} {N : IVK.L2Notation e} {T : Subgroup G}

theorem ip_Rd_factor (h : SitFacts x Kb e N T) (h12a : IVK.IVK_1_2a_struct)
    (h12d : IVK.IVK_1_2d) : IP_Rd_factor T (Pg x Kb T) (Qg x Kb T) (Rdg x Kb e T) := by
  have hPQT : Pg x Kb T ⊔ Qg x Kb T ≤ T := sup_le inf_le_left (fun g hg => hg.1)
  by_cases hcase : ∀ u ∈ Rdg x Kb e T, u ∈ Pg x Kb T ⊔ Qg x Kb T
  · refine ⟨T, le_rfl, ?_, sup_eq_left.2 (fun g hg => hg.1)⟩
    exact le_antisymm (fun g hg => hcase g hg.2) (le_inf hPQT SitFacts.PQ_le_Rd)
  · push Not at hcase
    obtain ⟨u, huRd, huPQ⟩ := hcase
    have hD : (IVK.innDiagSub e).Normal := IVK.innDiagSub_normal e
    have hInn : (IVK.innAut ↥Kb).Normal := inferInstance
    have hFD : IVK.innDiagSub e ⊓ IVK.fieldAutSub e = ⊥ := IVK.innDiagSub_inf_fieldAutSub e
    have hDF : IVK.innDiagSub e ⊔ IVK.fieldAutSub e = ⊤ := IVK.innDiagSub_sup_fieldAutSub e
    obtain ⟨hdiag, -, -, -⟩ := h12d F h.hF ↥Kb e N
    obtain ⟨-, -, -, hcomm⟩ := h12a F h.hF ↥Kb e N
    let J : Subgroup (MulAut ↥Kb) := IVK.innAut ↥Kb ⊔ IVK.fieldAutSub e
    let B : Subgroup G :=
      { carrier := {s | s ∈ T ∧ s ∈ Cx x ∧ phig x Kb s ∈ J}
        one_mem' := ⟨T.one_mem, one_mem _, by rw [phig_one]; exact J.one_mem⟩
        mul_mem' := by
          rintro a b ⟨ha, haC, haJ⟩ ⟨hb, hbC, hbJ⟩
          exact ⟨T.mul_mem ha hb, mul_mem haC hbC, by rw [phig_mul x Kb haC hbC]; exact J.mul_mem haJ hbJ⟩
        inv_mem' := by
          rintro a ⟨ha, haC, haJ⟩
          exact ⟨T.inv_mem ha, inv_mem haC, by rw [phig_inv x Kb haC]; exact J.inv_mem haJ⟩ }
    have hmemB : ∀ s, s ∈ B ↔ s ∈ T ∧ s ∈ Cx x ∧ phig x Kb s ∈ J := fun s => Iff.rfl
    have huT := huRd.1
    have huC := huRd.2.1
    have huD := huRd.2.2
    have huInn : phig x Kb u ∉ IVK.innAut ↥Kb := fun hin => huPQ ((h.inn_iff huT).1 hin)
    refine ⟨B, fun s hs => hs.1, ?_, ?_⟩
    · apply le_antisymm
      · rintro s ⟨⟨hsT, hsC, hsJ⟩, -, -, hsD⟩
        obtain ⟨i, hi, f', hf', hif⟩ := Subgroup.mem_sup_of_normal_left.1 hsJ
        have hiD : i ∈ IVK.innDiagSub e := IVK.innAut_le_innDiagSub e hi
        have hf'D : f' ∈ IVK.innDiagSub e := by
          have : f' = i⁻¹ * phig x Kb s := by rw [← hif]; group
          rw [this]; exact mul_mem (inv_mem hiD) hsD
        have : f' ∈ IVK.innDiagSub e ⊓ IVK.fieldAutSub e := ⟨hf'D, hf'⟩
        rw [hFD] at this
        have hf1 : f' = 1 := this
        rw [hf1, mul_one] at hif
        exact (h.inn_iff hsT).1 (hif ▸ hi)
      · refine le_inf ?_ SitFacts.PQ_le_Rd
        intro s hs
        have hsT := hPQT hs
        exact ⟨hsT, h.T_le_C hsT, mem_sup_left (((h.inn_iff hsT).2 hs))⟩
    · apply le_antisymm
      · exact sup_le (fun s hs => hs.1) (fun s hs => hs.1)
      · intro s hs
        have hsC := h.T_le_C hs
        have hmem : phig x Kb s ∈ IVK.innDiagSub e ⊔ IVK.fieldAutSub e := by
          rw [hDF]; exact Subgroup.mem_top _
        obtain ⟨d, hd, f, hf, hdf⟩ := Subgroup.mem_sup_of_normal_left.1 hmem
        by_cases hdInn : d ∈ IVK.innAut ↥Kb
        · refine mem_sup_left ⟨hs, hsC, ?_⟩
          rw [← hdf]
          exact J.mul_mem (mem_sup_left hdInn) (mem_sup_right hf)
        ·
          have hidx : ((IVK.innAut ↥Kb).subgroupOf (IVK.innDiagSub e)).index = 2 :=
            IVK.innAut_relIndex_two e h.hF
          have hdδ : d * (phig x Kb u)⁻¹ ∈ IVK.innAut ↥Kb := by
            have := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨d, hd⟩ : ↥(IVK.innDiagSub e)))
              (b := ⟨(phig x Kb u)⁻¹, inv_mem huD⟩)).2 (by
                constructor
                · intro hh; exact absurd hh hdInn
                · intro hh; exact absurd (inv_mem_iff.1 hh) huInn)
            exact this
          have hδf : ⁅phig x Kb u, f⁆ ∈ IVK.innAut ↥Kb := by
            have := hcomm f hf (phig x Kb u) (by rw [hdiag]; exact huD)
            have h2 : ⁅phig x Kb u, f⁆ = (⁅f, phig x Kb u⁆)⁻¹ := (commutatorElement_inv _ _).symm
            rw [h2]; exact inv_mem this
          have hsu : s * u⁻¹ ∈ B := by
            refine ⟨T.mul_mem hs (T.inv_mem huT), mul_mem hsC (inv_mem huC), ?_⟩
            rw [phig_mul x Kb hsC (inv_mem huC), phig_inv x Kb huC, ← hdf]
            have : d * f * (phig x Kb u)⁻¹ = (d * (phig x Kb u)⁻¹) * ⁅phig x Kb u, f⁆ * f := by
              simp only [commutatorElement_def]; group
            rw [this]
            exact J.mul_mem (J.mul_mem (mem_sup_left hdδ) (mem_sup_left hδf)) (mem_sup_right hf)
          have hs' : s = (s * u⁻¹) * u := by group
          rw [hs']
          exact mul_mem (mem_sup_left hsu) (mem_sup_right huRd)

end CFSG.GH74.GLS.Stage1.Thm6.Glue
