module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y53JrMap
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y53T1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma frameWith_Sσ_eq_sup (s : Setting3 G L) (g : G) :
    (frameWith s g).Sσ = s.fr.S ⊔ zpowers g := by
  show closure ({s.fr.a₁, s.fr.b₁, s.fr.a₂, s.fr.b₂, s.fr.h₀, g} : Set G) =
    s.fr.S ⊔ zpowers g
  rw [SFrame.S, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
  congr 1
  ext x
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
    or_false, false_or]
  tauto

theorem y53_jrG_T1 {c : Ctx5 G L} (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    SecProp c.e.T₁ c.s.fr.Z (fun Y _ _ π =>
      thompsonRank (((c.s.fr.S ⊔ zpowers c.g).subgroupOf c.e.T₁).map π) =
        (c.s.fr.A.subgroupOf c.e.T₁).map π) := by
  obtain ⟨_, _, hact, hg2, _⟩ := c.g_spec hRT
  have h3 : SecProp (c.s.fr.S ⊔ zpowers c.g) c.s.fr.Z (fun Y _ _ π =>
      thompsonRank (⊤ : Subgroup Y) =
        (c.s.fr.A.subgroupOf (c.s.fr.S ⊔ zpowers c.g)).map π) := by
    have h15 := (hH.hLF.sigma c.g hg2 hact).2.1
    have h3' := h15.2.2.1
    rw [frameWith_Sσ_eq_sup c.s c.g] at h3'
    exact h3'
  refine y53_section_transport (W := c.s.fr.S ⊔ zpowers c.g) (Z := c.s.fr.Z)
    (A := c.s.fr.A) (y5_Sg_le_T1 hH hRT) ?_ ?_ (y5_Z_normal_T1 hH) h3
  · exact (Subgroup.zpowers_le.mpr (s3_A_le_S c.s (s3_z_mem_A c.s))).trans le_sup_left
  · exact (s3_A_le_S c.s).trans le_sup_left

end CFSG.OddStandard.HigherRank.YamadaG23
