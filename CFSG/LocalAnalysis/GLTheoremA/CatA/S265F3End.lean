module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F3Lift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F3Inv

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265F3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.S265
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem qUConcl_of_model {p : ℕ} {S B T : Subgroup Ω} {x b : Ω} (cfg : QUCfg p S B T x b)
    (hb : b ∈ Subgroup.normalizer (S : Set Ω))
    (hmodel : ∀ Eb : Subgroup (MulAut (PSimple p S)), (∀ c ∈ Eb, c ^ p = 1) →
      (∀ c ∈ Eb, chevAut p S ⟨b, hb⟩ * c = c * chevAut p S ⟨b, hb⟩) → p ^ 2 ≤ Nat.card Eb →
      ∀ t : PSimple p S, orderOf t = 2 → (∀ c ∈ Eb, c t = t) →
      ∃ c ∈ Eb, c ∉ Subgroup.zpowers (chevAut p S ⟨b, hb⟩) ∧
        GLAPLayer p (fixSubgroup (chevAut p S ⟨b, hb⟩) ⊓ fixSubgroup c) ≠ ⊥) :
    QUConcl p S B x b := by
  classical
  have hp := cfg.prime
  haveI := Fact.mk hp
  haveI := cfg.normal
  have hnorm : ∀ g : Ω, g ∈ Subgroup.normalizer (S : Set Ω) := fun g => by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top g
  let Φ : Ω →* MulAut (PSimple p S) := (chevAut p S).comp ((MonoidHom.id Ω).codRestrict _ hnorm)
  have hΦ : ∀ g, Φ g = chevAut p S ⟨g, hnorm g⟩ := fun g => rfl
  obtain ⟨E₁, hE₁B, hE₁el, hE₁card, hE₁lay⟩ := cfg.gstar
  have hΦx : Φ x = 1 := by
    rw [hΦ, chevAut_eq_one_iff hp cfg.comp]
    exact (cfg.centB x cfg.xB).2 (Subgroup.mem_zpowers x)
  have hker : E₁ ⊓ Φ.ker ≤ Subgroup.zpowers x := by
    intro g hg
    obtain ⟨hgE, hgk⟩ := Subgroup.mem_inf.1 hg
    have h1 : chevAut p S ⟨g, hnorm g⟩ = 1 := hgk
    exact (cfg.centB g (hE₁B hgE)).1 ((chevAut_eq_one_iff hp cfg.comp (hnorm g)).1 h1)
  have hxord : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (cfg.elem.2 x cfg.xB) cfg.x1
  have hcard : p ^ 2 ≤ Nat.card (E₁.map Φ) := card_map_ge_of_inf_ker_le hp.pos Φ hE₁card hxord hker
  have hE3 : ∀ c ∈ E₁.map Φ, c ^ p = 1 := by
    rintro _ ⟨g, hg, rfl⟩
    rw [← map_pow, hE₁el.2 g hg, map_one]
  have hcomm : ∀ c ∈ E₁.map Φ, chevAut p S ⟨b, hb⟩ * c = c * chevAut p S ⟨b, hb⟩ := by
    rintro _ ⟨g, hg, rfl⟩
    have hbg : b * g = g * b :=
      congrArg Subtype.val (cfg.elem.1.is_comm.comm ⟨b, cfg.hb⟩ ⟨g, hE₁B hg⟩)
    show Φ b * Φ g = Φ g * Φ b
    rw [← map_mul, ← map_mul, hbg]
  obtain ⟨t, ht2, htfix⟩ := exists_involution_fixed cfg.core hE₁lay
  have hEt : ∀ c ∈ E₁.map Φ, c t = t := by
    rintro _ ⟨g, hg, rfl⟩
    exact htfix g (hnorm g) hg
  obtain ⟨_, ⟨e₀, he₀E, rfl⟩, hcβ, hlay⟩ := hmodel (E₁.map Φ) hE3 hcomm hcard t ht2 hEt
  have hDle : Dgrp b x ≤ (Subgroup.zpowers (Φ b)).comap Φ := by
    rw [dgrp_eq]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap, hΦx]
      exact Subgroup.one_mem _
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
      exact Subgroup.mem_zpowers _
  have he₀D : e₀ ∉ Dgrp b x := fun h => hcβ (hDle h)
  have hne := glaPLayer_inf_cx_ne_bot_of_fix hp cfg.core hb (hnorm e₀) hlay
  have hSx : S ≤ Subgroup.centralizer ({x} : Set Ω) := fun s _ => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    first
    | exact cfg.xcen s
    | exact (cfg.xcen s).symm
  exact Or.inl (exists_e3_of_layer hp cfg.elem cfg.xB cfg.x1 hSx cfg.hb cfg.hbx (hE₁B he₀E) he₀D hne)

end CFSG.LocalAnalysis.GLTheoremA.S265F3

end
