module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Glue710a
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Glue710b

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

theorem lemma_7_10 (hII : II4_4_4_center) (hg : IG_10_32_P) (h31c : IVK_3_1c_lifted)
    (h410 : IVK.IVK_4_10) (hY : IVK_Y_unique) (hsupp : IVK_4_10_supp)
    (hne : IVK_PSp4_ne_LU) : Lemma7_10 := by
  intro G _ _ z S K₁ K₂ t u q w h hc hd Gs _ _ z' S' hmodel hz'o hZ'
  have hSp : IVK.IsSp4L4U4 Gs q := by
    rcases hmodel with ⟨-, hP⟩ | ⟨-, hLU⟩
    · exact Or.inl hP
    · exact Or.inr hLU
  have hz'mem : z' ∈ ((center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype) := by
    rw [hZ']
    exact mem_zpowers z'
  obtain ⟨c, hc', hcz⟩ := hz'mem
  have hcz' : (c : Gs) = z' := hcz
  have hz'S' : z' ∈ (S' : Subgroup Gs) := hcz' ▸ c.2
  have hz'c : ∀ x ∈ (S' : Subgroup Gs), x * z' = z' * x := by
    intro x hx
    have := Subgroup.mem_center_iff.1 hc' ⟨x, hx⟩
    rw [← hcz']
    exact congrArg Subtype.val this
  obtain ⟨t', w', E₁, E₂, ht'S, hw'S, ht'o, hw'o, hcomm', hprod', hinter', ht'c, hEz, hE₂, hsl2,
      hinterE, hcommE, hnormE, hw1iff, hcls, htzne, hEfus, hpgl, hwfus, -⟩ :=
    h410 Gs q h.ch.q_odd h.ch.q_ge hSp S' z' hz'S' hz'o hz'c
  have hdat : Dat410 q z' (S' : Subgroup Gs) t' w' E₁ E₂ :=
    ⟨ht'S, hw'S, ht'o, hw'o, hcomm'.eq, hprod', hinter', ht'c, hEz, hE₂, hsl2, hinterE, hcommE, hnormE, hcls,
      htzne, hEfus, hpgl, hwfus⟩
  have hww : w' = 1 ↔ w = 1 := by
    rcases hmodel with ⟨hw1, hP⟩ | ⟨hw1, hLU⟩
    · exact ⟨fun _ => hw1, fun _ => hw1iff.2 hP⟩
    · have hnP : ¬IVK.IsPSp4 Gs q := fun hP => by
        rcases hLU with ⟨-, hl⟩ | ⟨-, hl⟩
        · exact (hne Gs q hP).1 hl
        · exact (hne Gs q hP).2 hl
      exact ⟨fun h1 => absurd (hw1iff.1 h1) hnP, fun h1 => absurd h1 hw1⟩
  have hsupp' : w' ≠ 1 → ¬IsConj z' (t' * w' * z') :=
    hsupp Gs q h.ch.q_odd h.ch.q_ge hSp z' S' t' w' E₁ E₂ hz'o hz'c hz'S' hdat
  have hψ := hY G z S K₁ K₂ t u q w h hc Gs z' S' t' w' E₁ E₂ hmodel hz'o hZ' hdat hww
  have hPS : Pz S z ≤ S := (h.Pz_le_S1 hII).trans Cfg7.S1_le_S
  have hz'2 : z' * z' = 1 := mul_self_eq_one_of_orderOf_eq_two hz'o
  refine compat7_of_psi le_sup_right hPS (h.S_inf_Oz hII) (h.z_mem_S hII) h.z_ne
    (fun s hs => Subgroup.mem_centralizer_singleton_iff.1 (h.S_le_C hII hs)) h.ch.t_mem hc.1 hz'2 hZ'
    hψ ?_
  intro f hf hfS hfP hft hfw hfz
  exact h.fusion hII hg h31c hc hd hdat hsupp' hww hf hfS hfP hft hfw hfz

end CFSG.GH74.GLS.Stage1.Thm3.Sec7
