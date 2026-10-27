module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265EFin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ESLab
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ESetupA
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ESetupB

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)

section Data


theorem s265e_data {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω}
    {D K : Subgroup Ω} (h : QSNL 5 S B T x D K) (hE : catalogIs (PSimple 5 K) tyE) :
    ∃ (X : Type) (_ : Group X) (_ : Finite X) (A : Subgroup (MulAut X)) (β : MulAut X)
      (J : Subgroup X),
      (∃ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 ∧ Nonempty (X ≃* d.Group)) ∧
      IsElemAbelian 5 A ∧ 5 ^ 3 ≤ Nat.card A ∧ A ≤ innAutDerived X ∧ β ∈ A ∧ β ≠ 1 ∧
      IsComponentOf J (fixSubgroup β) ∧
      (LieModel (↥J ⧸ Subgroup.center ↥J) .twistedB2 0 2 5 ∨
        LieModel (↥J ⧸ Subgroup.center ↥J) .Tits 0 2 1) := by
  have cfg := h.cfg
  haveI hSn : S.Normal := cfg.normal
  have hnorm : ∀ g : Ω, g ∈ Subgroup.normalizer (S : Set Ω) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.2 hSn]
    exact Subgroup.mem_top g
  obtain ⟨lab, hlab⟩ := s265e_exists_label (S10.inner_of_innDiagOn cfg.comp cfg.quasi cfg.inn)
  have hLl : HasLabel ↥S (· = lab) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) (hlab x cfg.xB)
  obtain ⟨d₀, hd₀B, -, hd₀C, hKcomp⟩ := s265e_exists_d0 cfg
  have hβ1 := CanonSubcomp.centerQuotAut_conjAut_ne_one (hnorm d₀) hd₀C cfg.quasi.1
  have hKb := CanonInn.isComponentOf_fixSubgroup_conjAut S (hnorm d₀) hKcomp
  have hJcomp := CanonInn.isComponentOf_map_centerQuot _ hKb
  obtain ⟨eK⟩ := s265e_centerQuot_equiv_subgroupOf (hKcomp.1.trans inf_le_left)
  obtain ⟨eJ⟩ := s265e_centerQuot_equiv_map hKb.2.2.1
  have hmodel := s265e_lieModel hKcomp.2.2 hE (eK.trans eJ)
  obtain ⟨hAel, hAcard⟩ := s265e_actRange cfg
  have hβA : Y10F.centerQuotAut ↥S (Y10F.conjAut S d₀ (hnorm d₀)) ∈ B.map (S2019.actQuot S) := by
    rw [s265e_centerQuotAut_conjAut S (hnorm d₀)]
    exact ⟨d₀⁻¹, B.inv_mem hd₀B, rfl⟩
  rcases s265e_sside hLl with ⟨hnd, d, hd2, hXd⟩ | hsmall
  · refine ⟨↥S ⧸ Subgroup.center ↥S, inferInstance, inferInstance, B.map (S2019.actQuot S), _, _,
      ⟨d, hd2, hXd⟩, hAel, hAcard, ?_, hβA, hβ1, hJcomp, hmodel⟩
    rintro _ ⟨b, hb, rfl⟩
    have h1 := s265e_mem_innAutDerived (hnorm b⁻¹) (hlab b⁻¹ (B.inv_mem hb)) hnd
    rwa [s265e_centerQuotAut_conjAut S (hnorm b⁻¹), inv_inv] at h1
  · exact (s265e_order_contra hsmall hβ1 hJcomp hmodel).elim

end Data

end CFSG.LocalAnalysis.GLTheoremA.S265

end
