module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93OneCls
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Cls
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93L4G

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P34 CFSG.ComponentClassification CFSG.Blueprint
open scoped MatrixGroups

@[expose] def Ivk93ResSL2 (M : Type) [Group M] (q : ℕ) : Prop :=
  ∃ (y : M) (E : Type) (_ : Field E) (_ : Finite E) (ψ : SL(2, E) →* M),
    orderOf y = 2 ∧ Nat.card E = q ^ 2 ∧ ψ ≠ 1 ∧ ∀ g, ψ g * y = y * ψ g

theorem Ivk93ResSL2.of_equiv {M N : Type} [Group M] [Group N] {q : ℕ} (e : M ≃* N)
    (h : Ivk93ResSL2 M q) : Ivk93ResSL2 N q := by
  obtain ⟨y, E, _, _, ψ, hy, hE, hψ, hc⟩ := h
  refine ⟨e y, E, inferInstance, inferInstance, e.toMonoidHom.comp ψ, ?_, hE, fun h1 => hψ ?_,
    fun g => ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact hy
  · ext g
    have := congrArg (fun φ : SL(2, E) →* N => e.symm (φ g)) h1
    simpa using this
  · show e (ψ g) * e y = e y * e (ψ g)
    rw [← map_mul, ← map_mul, hc g]

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem false_of_ResSL2 (hp : Stage1Pair G z S q L₁ L₂) (hz2 : orderOf z = 2)
    (hone : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) {H : Subgroup G}
    (hJ : Ivk93ResSL2 ↥(generalizedFitting (HBar H)) q) : False := by
  obtain ⟨y, E, _, _, ψ, hy, hE, hψ, hc⟩ := hJ
  refine false_of_sl2_centralizer hp hz2 hone (y := (y : HBar H)) ?_ hE
    ((generalizedFitting (HBar H)).subtype.comp ψ) (fun h1 => hψ ?_) (fun g => ?_)
  · rw [Subgroup.orderOf_coe]
    exact hy
  · ext g
    have h2 := congrArg (fun φ : SL(2, E) →* HBar H => φ g) h1
    have h3 : ((ψ g : ↥(generalizedFitting (HBar H))) : HBar H) = 1 := by simpa using h2
    simpa using h3
  · show (ψ g : HBar H) * (y : HBar H) = (y : HBar H) * (ψ g : HBar H)
    exact congrArg Subtype.val (hc g)

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt
