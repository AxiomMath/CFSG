module

public import CFSG.LargeExtraspecial.S11MbKeyE
public import CFSG.LargeExtraspecial.S11MbSteps
public import CFSG.LargeExtraspecial.S11MbY

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u_G

variable {G : Type u_G} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O} {τ : S.M}
  {u : G}

theorem YData.apply_sub_mem_span {kb σ u₁ : G} (Y : YData S g t τ u kb σ u₁)
    (h : ∀ w ∈ S.QG, S.cl w ∈ Wt S g t →
      S.cl (w * σ * w⁻¹ * σ⁻¹) ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹))
    {w : S.Qt} (hw : w ∈ Wt S g t) :
    (S.ρ ⟨σ, Y.mem_M⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
  obtain ⟨w₀, hw₀, rfl⟩ := S.exists_cl w
  rw [← S.cl_commutator' Y.mem_M hw₀]
  exact h w₀ hw₀ hw

theorem Conf.not_two_of_seven_le (hy : Hyp S g) (K : Conf S g t τ u)
    (hCE : CentralExtInput.{u_G}) (hn : 7 ≤ S.width) : finrank (ZMod 2) (Vt S g t) ≠ 2 := by
  intro hm
  obtain ⟨kb, hb, hbs⟩ := K.exists_base_ne hy
  obtain ⟨h', hh', hha, hhb⟩ := K.exists_mem_Qa_commute hy hb hbs
  have hn6 : 6 ≤ S.width := by omega
  have Y := K.yData_conj hy hb hh' hha hhb hCE hn6
  obtain ⟨u₃, Y₃⟩ := K.yData_mul hy hb hh' hha hhb hCE hn6
  have hkd := K.conj_b_eq hb hh' hhb
  rcases Y.cases hy K hm hb hbs hCE hn hkd with h1 | h1
  · exact Y.false_of_case hy K hm (fun w hw => Y.apply_sub_mem_span h1 hw) hb hbs hCE hn
  rcases Y₃.cases hy K hm hb hbs hCE hn hkd with h3 | h3
  · exact Y₃.false_of_case hy K hm (fun w hw => Y₃.apply_sub_mem_span h3 hw) hb hbs hCE hn
  exact false_of_bad hy K hm hb hbs hCE hn6 Y h1 h3

end CFSG.LargeExtraspecial.S11
