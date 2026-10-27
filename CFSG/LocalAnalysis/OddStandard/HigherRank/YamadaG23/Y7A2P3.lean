module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2Top
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Set

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y7a_isSylowIn_map_subtype_three_p3 {V : Subgroup G} (P : Sylow 3 ↥V) :
    IsSylowIn 3 V ((P : Subgroup ↥V).map V.subtype) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨Subgroup.map_subtype_le _, P.isPGroup'.map V.subtype, ?_⟩
  have h := Subgroup.relIndex_map_map_of_injective (f := V.subtype)
    (P : Subgroup ↥V) (⊤ : Subgroup ↥V) V.subtype_injective
  rw [Subgroup.map_top V.subtype, Subgroup.range_subtype, Subgroup.relIndex_top_right] at h
  rw [h]
  exact P.not_dvd_index

theorem y7a_exists_P3 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) :
    ∃ P₃ : Subgroup G, P₃ ≤ normIn L c.s.fr.A ∧
      (∀ k ∈ P₃, k * c.s.fr.z * k⁻¹ = c.s.fr.z) ∧
      IsOrbitMod P₃ (zpowers c.s.fr.z)
        ((closure {c.s.fr.a₁, c.s.fr.b₁} : Set G) \ (zpowers c.s.fr.z : Set G)) ∧
      IsOrbitMod P₃ (zpowers c.s.fr.z)
        ((closure {c.s.fr.a₂, c.s.fr.b₂} : Set G) \ (zpowers c.s.fr.z : Set G)) ∧
      IsOrbitMod P₃ (zpowers c.s.fr.z)
        ((c.s.fr.A : Set G) \ ((closure {c.s.fr.a₁, c.s.fr.b₁} : Set G) ∪
          (closure {c.s.fr.a₂, c.s.fr.b₂} : Set G))) := by
  obtain ⟨P₃, hP₃⟩ : ∃ P₃ : Subgroup G, IsSylowIn 3 (normIn L c.s.fr.A) P₃ :=
    ⟨_, y7a_isSylowIn_map_subtype_three_p3 (default : Sylow 3 ↥(normIn L c.s.fr.A))⟩
  have hP₃_cent : P₃ ≤ centEl L c.s.fr.z := by
    rw [← hH.hLF.fact18.1.1]; exact hP₃.1
  have hP3z : ∀ k ∈ P₃, k * c.s.fr.z * k⁻¹ = c.s.fr.z := by
    intro k hk
    have hkz : Commute k c.s.fr.z := by
      have hmem : k ∈ centralizer ({c.s.fr.z} : Set G) := (hP₃_cent hk).2
      rw [Subgroup.mem_centralizer_iff] at hmem
      exact (hmem c.s.fr.z (Set.mem_singleton c.s.fr.z)).symm
    rw [hkz.eq]; group
  have hOW := hH.hLF.fact18.1.2.2 P₃ hP₃
  refine ⟨P₃, hP₃.1, hP3z, ?_, ?_, ?_⟩
  · simpa only [SFrame.Z] using hOW.1
  · simpa only [SFrame.Z] using hOW.2.1
  · simpa only [SFrame.Z] using hOW.2.2

theorem y7a_A_le_of_b1b2 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) {D : Subgroup G}
    (hVD : V1 c.e ≤ D) (hDA : D ≤ AV1 c.e)
    (hDinv : ∀ k ∈ normIn L c.s.fr.A, ∀ x ∈ D, k * x * k⁻¹ ∈ D)
    (hb : c.s.fr.b₁ * c.s.fr.b₂ ∈ D) : c.s.fr.A ≤ D := by
  have h := c.y7acfg hH
  obtain ⟨P₃, hP₃, hP3z, hU, hW, h9⟩ := y7a_exists_P3 c hH
  have hVc : ∀ a ∈ c.s.fr.A, ∀ v ∈ V1 c.e, a * v = v * a :=
    fun a ha v hv => y6_C0_comm h.cfg a ha v (y7a_V_le_C0 h hv)
  have hb1 : c.s.fr.b₁ ∈ c.s.fr.A := by
    rw [h.cfg.hA]; exact Subgroup.subset_closure (by simp)
  have hb2 : c.s.fr.b₂ ∈ c.s.fr.A := by
    rw [h.cfg.hA]; exact Subgroup.subset_closure (by simp)
  obtain ⟨hn1, hn2⟩ := y7a_b1b2_notin h.cfg.rel h.cfg.z_ne h.cfg.card_A
  exact y7a_inv_top h.cfg.hA h.cfg.rel h.cfg.z_ne h.cfg.card_A hP3z hU hW h9
    (y7a_A_inf_V h) hVc hVD hDA (fun k hk x hx => hDinv k (hP₃ hk) x hx)
    ⟨_, hb, c.s.fr.A.mul_mem hb1 hb2, hn1, hn2⟩

end CFSG.OddStandard.HigherRank.YamadaG23
