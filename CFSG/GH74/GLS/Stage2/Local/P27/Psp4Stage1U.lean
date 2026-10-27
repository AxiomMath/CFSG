module

public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Canon
public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.Psp4Stage1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P27.Psp4

variable {G : Type} [Group G] [Finite G] {S P₁ P₂ : Subgroup G} {z t : G} {a : ℕ}

theorem exists_uhyp (d : Psp4.Data S P₁ P₂ z t a) : ∃ u : G, Psp4.UHyp S P₁ P₂ z u := by
  obtain ⟨a₀, b₀, M, ha, hb, hM, hN, hqg, hspan⟩ := d.exists_gens
  exact ⟨_, (Psp4.Canon.mk d ha hb hM hN hqg hspan).uhyp⟩

theorem isConj_of_uhyp {L₁ L₂ : Subgroup (CentralizerBar z)} {q : ℕ} {x₀ : G}
    (hx : TwoClassData G z S L₁ L₂ q x₀) {P₁ P₂ : Subgroup G} {u : G}
    (hu : Psp4.UHyp S P₁ P₂ z u) (hP : P₁ ⊔ P₂ = RC S z) : IsConj x₀ u := by
  have hmem : u ∈ LC z := (hP ▸ hu.mem : u ∈ RC S z).2
  have hord : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu.sq) hu.ne_one
  exact (hx.invol_L u hmem hord hu.ne_z).1

end CFSG.GH74.GLS.Stage2.Local.P27.Psp4Stage1
