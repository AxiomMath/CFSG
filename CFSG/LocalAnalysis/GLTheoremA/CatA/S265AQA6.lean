module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AQLab6
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AQA6Core
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F3Inv
import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GLayer
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F3Lift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.MI CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

section Main


theorem QUCfg.false_of_alt6 {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x b : Ω}
    (cfg : QUCfg 3 S B T x b) (hJ : catalogIs (PSimple 3 (Ipart 3 S b)) tyAlt6) : False := by
  classical
  obtain ⟨-, -, K, _, _, hK, ⟨e⟩⟩ := cfg.ident_alt6 hJ
  have hp : (3 : ℕ).Prime := Nat.prime_three
  haveI := Fact.mk hp
  haveI := cfg.normal
  have hnorm : ∀ g : Ω, g ∈ Subgroup.normalizer (S : Set Ω) := fun g => by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top g
  let Φ : Ω →* MulAut (PSimple 3 S) := (chevAut 3 S).comp ((MonoidHom.id Ω).codRestrict _ hnorm)
  have hΦ : ∀ g, Φ g = chevAut 3 S ⟨g, hnorm g⟩ := fun g => rfl
  obtain ⟨E₁, hE₁B, hE₁el, hE₁card, hE₁lay⟩ := cfg.gstar
  have hker : E₁ ⊓ Φ.ker ≤ Subgroup.zpowers x := by
    intro g hg
    obtain ⟨hgE, hgk⟩ := Subgroup.mem_inf.1 hg
    have h1 : chevAut 3 S ⟨g, hnorm g⟩ = 1 := hgk
    exact (cfg.centB g (hE₁B hgE)).1 ((chevAut_eq_one_iff hp cfg.comp (hnorm g)).1 h1)
  have hxord : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (cfg.elem.2 x cfg.xB) cfg.x1
  have hcard : 3 ^ 2 ≤ Nat.card (E₁.map Φ) :=
    S265F3.card_map_ge_of_inf_ker_le (by norm_num) Φ hE₁card hxord hker
  obtain ⟨P, hP⟩ := FR.exists_component_of_ne_bot _ hE₁lay
  have hPX : P ≤ S ⊓ cs E₁ := hP.1
  have hPS : P ≤ S := hPX.trans inf_le_left
  have hP'map : (P.subgroupOf S).map S.subtype = P := Subgroup.map_subgroupOf_eq_of_le hPS
  have hP'perf : ⁅P.subgroupOf S, P.subgroupOf S⁆ = P.subgroupOf S := by
    apply Subgroup.map_injective S.subtype_injective
    rw [Subgroup.map_commutator, hP'map, glaPComponent_perfect hP]
  have hQne : (P.subgroupOf S).map (chevQuotHom 3 S) ≠ ⊥ := by
    intro hQbot
    have hle : P.subgroupOf S ≤ (chevQuotHom 3 S).ker := by
      rw [← Subgroup.map_eq_bot_iff]
      exact hQbot
    have hcen : P.subgroupOf S ≤ Subgroup.center ↥S :=
      hle.trans (T156.ker_chevQuotHom_le_center cfg.core)
    have hbot : ⁅P.subgroupOf S, P.subgroupOf S⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro a ha c _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.1 (hcen ha) c).symm
    apply CFSG.LocalAnalysis.GLTheoremA.glaPComponent_ne_bot' hP
    rw [← hP'map, ← hP'perf, hbot, Subgroup.map_bot]
  refine spFourEight_false_of_fix hK e (Eb := E₁.map Φ) ?_ ?_ (le_trans (by norm_num) hcard)
    (J := (P.subgroupOf S).map (chevQuotHom 3 S)) (by rw [← Subgroup.map_commutator, hP'perf])
    hQne ?_
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg Φ (congrArg Subtype.val (hE₁el.1.is_comm.comm ⟨a, ha⟩ ⟨c, hc⟩))
  · rintro _ ⟨c, hc, rfl⟩
    rw [← map_pow, hE₁el.2 c hc, map_one]
  ·
    rintro _ ⟨g, hgE, rfl⟩ _ ⟨k, hk, rfl⟩
    rw [hΦ, chevAut_chevQuotHom]
    have hkE : (k : Ω) ∈ cs E₁ := (hPX (Subgroup.mem_subgroupOf.1 hk)).2
    have hkfix : k ∈ fixSubgroup (S.normalizerMonoidHom ⟨g, hnorm g⟩) := by
      rw [fixSubgroup_normalizerMonoidHom (hnorm g), Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      refine ⟨k.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := Subgroup.mem_centralizer_iff.1 hkE g hgE
      first
      | exact h
      | exact h.symm
    rw [mem_fixSubgroup.1 hkfix]

end Main

end CFSG.LocalAnalysis.GLTheoremA.S265

end
