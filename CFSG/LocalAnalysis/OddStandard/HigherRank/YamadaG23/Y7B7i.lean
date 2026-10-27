module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7Abs2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7Abs3
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B7f

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y7b_comm_bot_iff_centralizer (B : Subgroup G) {x : G} :
    (∀ u ∈ B, ⁅x, u⁆ ∈ (⊥ : Subgroup G)) ↔ x ∈ centralizer (B : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h u hu
    have h1 := h u hu
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  · intro h u hu
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (h u hu).symm

theorem y7b_exists_rhoV (c : Ctx7 G L) (hb : B5Std c) :
    ∃ ρ : ↥(y7bX c.s) →* Equiv.Perm (Fin 3),
      (∀ x : ↥(y7bX c.s), ρ x = 1 ↔ (x : G) ∈ y7bK c.s) ∧ Function.Surjective ρ := by
  obtain ⟨ρ, hρ⟩ := y7b_exists_perm3_hom (X := y7bX c.s) (M := (⊥ : Subgroup G))
    (U := cen c.s.fr.B) bot_le
    (by
      intro u _ m hm
      rw [Subgroup.mem_bot] at hm ⊢
      rw [hm]
      group)
    (by
      intro x hx u hu
      exact (Subgroup.mem_normalizer_iff.mp (y7b_X_le_NV c hb hx) u).mp hu)
    (by
      intro x _ m hm
      rw [Subgroup.mem_bot] at hm ⊢
      rw [hm]
      group)
    (by rw [Subgroup.relIndex_bot_left, y7b_card_V hb.hH])
    (by
      intro u hu
      rw [Subgroup.mem_bot]
      have h := (f3_V_isE2 hb.hH).1.2 (⟨u, hu⟩ : ↥(cen c.s.fr.B)) (Subgroup.mem_top _)
      simpa using h)
  refine ⟨ρ, fun x => ?_, ?_⟩
  · constructor
    · intro h
      rw [hρ x, y7b_comm_bot_iff_centralizer] at h
      rw [y7bK, Subgroup.mem_inf]
      exact ⟨x.2, h⟩
    · intro h
      rw [y7bK, Subgroup.mem_inf] at h
      rw [hρ x, y7b_comm_bot_iff_centralizer]
      exact h.2
  · intro σ
    obtain ⟨n, -, hn⟩ := y7b_perm3_surj_of_relIndex (X := y7bX c.s)
      (N := normIn L c.s.fr.B) (K := c.s.fr.B)
      (fun n hn => y7b_N_le_X c hb (Subgroup.mem_inf.mpr
        ⟨s3_L_le_H c.s hb.hH.hS (Subgroup.mem_inf.mp hn).1, (Subgroup.mem_inf.mp hn).2⟩))
      (fun b hbB => Subgroup.mem_inf.mpr ⟨f3_B_le_L c.s hbB, Subgroup.le_normalizer hbB⟩)
      ρ (fun n hn => by
        rw [hρ n, y7b_comm_bot_iff_centralizer]
        constructor
        · intro hc
          have hmem : (n : G) ∈ centIn L (cen c.s.fr.B) :=
            Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hn).1, hc⟩
          rwa [f3_centIn_L_V hb.hH] at hmem
        · intro hbB
          rw [Subgroup.mem_centralizer_iff]
          intro v hv
          exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hv).2 (n : G) hbB).symm)
      (y7b_relIndex_B_NLB hb.hH) σ
    exact ⟨n, hn⟩

theorem y7b_relIndex_K_X (c : Ctx7 G L) (hb : B5Std c) :
    (y7bK c.s).relIndex (y7bX c.s) = 6 := by
  obtain ⟨ρ, hker, hsurj⟩ := y7b_exists_rhoV c hb
  exact y7b_relIndex_eq_six ρ hsurj hker

end CFSG.OddStandard.HigherRank.YamadaG23
