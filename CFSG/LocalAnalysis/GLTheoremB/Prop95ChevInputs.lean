module

public import CFSG.LieType.ChevTwo.Defs
public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvDefs
import CFSG.LieType.ChevTwo.OrthogonalAssembly

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv

open CFSG.Open CFSG.LieType.BorelTits CFSG.LieType.ChevTwo
open CFSG.LocalAnalysis.GLTheoremB (IsOmegaTwo HasFixedPointFreeOrder)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped commutatorElement

section Core

variable {X : Type} [Group X] (K : Subgroup X) [K.Normal]

abbrev rho : X →* MulAut ↥K := MulAut.conjNormal

theorem rho_injective (hC : Subgroup.centralizer (K : Set X) = ⊥) : Function.Injective (rho K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hg' : g ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 := congrArg (fun φ : MulAut ↥K => (φ ⟨k, hk⟩ : X)) hg
    simp only [rho, MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc k * g = (g * k * g⁻¹) * g := by rw [h1]
      _ = g * k := by group
  rw [hC] at hg'
  exact Subgroup.mem_bot.1 hg'

theorem mem_of_rho_mem_inner (hC : Subgroup.centralizer (K : Set X) = ⊥) {g : X}
    (h : rho K g ∈ inner ↥K) : g ∈ K := by
  obtain ⟨k, hk⟩ := h
  have : rho K g = rho K (k : X) := by
    rw [← hk, rho, MulAut.conjNormal_val]
  exact (rho_injective K hC this) ▸ k.2

theorem mem_pCoreOf_autCentralizer [Finite X] (E : Subgroup X) {y : X} (hyK : y ∈ K)
    (hy : y ∈ pCoreOf 2 (Subgroup.centralizer (E : Set X))) :
    (⟨y, hyK⟩ : ↥K) ∈ pCoreOf 2 (autCentralizer (E.map (rho K))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer (E : Set X) with hCdef
  set H : Subgroup ↥K := autCentralizer (E.map (rho K)) with hH
  set N : Subgroup ↥K := (pCoreOf 2 C ⊓ K).subgroupOf K with hN
  have hmemH : ∀ k : ↥K, k ∈ H ↔ (k : X) ∈ C := by
    intro k
    constructor
    · intro hk
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have h1 := hk (rho K e) ⟨e, he, rfl⟩
      have h2 := congrArg (fun z : ↥K => (z : X)) h1
      simp only [rho, MulAut.conjNormal_apply] at h2
      calc e * (k : X) = (e * k * e⁻¹) * e := by group
        _ = (k : X) * e := by rw [h2]
    · intro hk α hα
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hα
      have h1 := Subgroup.mem_centralizer_iff.1 hk e he
      apply Subtype.ext
      simp only [rho, MulAut.conjNormal_apply]
      rw [h1]; group
  have hNH : N ≤ H := by
    intro k hk
    have hk' : (k : X) ∈ pCoreOf 2 C := (Subgroup.mem_subgroupOf.1 hk).1
    exact (hmemH k).2 (pCoreOf_le 2 C hk')
  have hnorm : (N.subgroupOf H).Normal := by
    refine ⟨fun x hx h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [hN, Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have hhC : ((h : ↥K) : X) ∈ C := (hmemH h).1 h.2
      have := (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 C hhC) _).1 hx1
      simpa using this
    · simpa using Subgroup.mul_mem _ (Subgroup.mul_mem _ (h : ↥K).2 hx2)
        (Subgroup.inv_mem _ (h : ↥K).2)
  have hNp : IsPGroup 2 N :=
    ((pCoreOf_isPGroup 2 C).to_le inf_le_left).comap_of_injective K.subtype K.subtype_injective
  have hle := le_pCoreOf 2 hNH hnorm hNp
  exact hle (Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hy, hyK⟩))

end Core

@[expose] def Input19_20_3Core : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X) [K.Normal], IsSimpleGroup ↥K →
    Subgroup.centralizer (K : Set X) = ⊥ → ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∀ (D : Subgroup X) (Sd : X → Subgroup X), SignalizerFamily p D Sd →
        sigmaFam D Sd ⊓ K = ⊥ → ∀ (n : ℕ) (ε : Bool), 1 ≤ n → IsOmegaTwo ε (n + 1) ↥K →
          sigmaFam D Sd ≠ ⊥ →
            ActsAsTransvectionAt ε n (sigmaFam D Sd) K ∧ HasFixedPointFreeOrder ε n p

theorem input19_20_3Core_of (h1 : OmegaTwoAutTwoPart)
    (h2 : (∀ n : ℕ, 1 ≤ n → OmegaTwoAutInduced (StatedQuadMinus (n + 1) (ZMod 2) 1 1)) ∧
      (∀ n : ℕ, 2 ≤ n → n ≠ 3 → OmegaTwoAutInduced (StatedQuadPlus (n + 1) (ZMod 2))))
    (h2' : OmegaPlusEightInvolutions)
    (h3 : ∀ n : ℕ, 1 ≤ n → OrthOddCentCore (StatedQuadPlus (n + 1) (ZMod 2)) true n ∧
      OrthOddCentCore (StatedQuadMinus (n + 1) (ZMod 2) 1 1) false n) : Input19_20_3Core :=
  CFSG.LieType.ChevTwo.input19_20_3_assembly h1 h2 h2'

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
