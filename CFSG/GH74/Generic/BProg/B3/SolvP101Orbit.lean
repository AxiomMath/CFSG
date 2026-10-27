module

public import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace SolvP101

open Subgroup CFSG CFSG.ClassicalInvolution.Balance.LocalBalance CFSG.LocalCores
open scoped commutatorElement

variable {X : Type} [Group X]

theorem commutatorElement_commute {L : Subgroup X} {a b : X} (ha : ∀ z ∈ L, a * z = z * a)
    (hb : b ∈ normalizer (L : Set X)) : ∀ z ∈ L, ⁅a, b⁆ * z = z * ⁅a, b⁆ := by
  intro z hz
  have hz' : b⁻¹ * z * b ∈ L := by
    have := (mem_normalizer_iff.1 (inv_mem hb) z).1 hz
    simpa using this
  have h1 : a⁻¹ * (b⁻¹ * z * b) = (b⁻¹ * z * b) * a⁻¹ := by
    have h := ha _ hz'
    calc a⁻¹ * (b⁻¹ * z * b) = a⁻¹ * ((b⁻¹ * z * b) * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * (b⁻¹ * z * b)) * a⁻¹ := by rw [h]
      _ = (b⁻¹ * z * b) * a⁻¹ := by group
  rw [commutatorElement_def]
  calc a * b * a⁻¹ * b⁻¹ * z = (a * b) * (a⁻¹ * (b⁻¹ * z * b)) * b⁻¹ := by group
    _ = (a * b) * ((b⁻¹ * z * b) * a⁻¹) * b⁻¹ := by rw [h1]
    _ = (a * z) * (b * a⁻¹ * b⁻¹) := by group
    _ = (z * a) * (b * a⁻¹ * b⁻¹) := by rw [ha z hz]
    _ = z * (a * b * a⁻¹ * b⁻¹) := by group

variable [Finite X]

theorem conjSub_eq_of_two_comps {A B L R S : Subgroup X} (hA : IsComponent A) (hB : IsComponent B)
    (hL : IsComponent L) (hRAB : R ≤ A ⊔ B) (hSR : S ≤ normalizer (R : Set X))
    (h2 : ∀ g ∈ S, ∃ m : ℕ, Odd m ∧ g ^ m ∈ R)
    (hLnc : ¬ ∀ r ∈ R, ∀ z ∈ L, r * z = z * r) : ∀ g ∈ S, conjSub g L = L := by
  have hcen : ∀ (M N : Subgroup X), IsComponent M → IsComponent N → M ≠ N →
      M ≤ centralizer (N : Set X) := fun M N hM hN hne a ha =>
    mem_centralizer_iff.2 fun z hz => (commute_of_isComponent_of_ne hM hN hne a ha z hz).symm
  have hABn : ∀ M : Subgroup X, IsComponent M → A ⊔ B ≤ normalizer (M : Set X) := by
    intro M hM
    refine sup_le ?_ ?_
    · by_cases hAM : A = M
      · rw [hAM]
        exact le_normalizer
      · exact (hcen A M hA hM hAM).trans (Subgroup.centralizer_le_normalizer _)
    · by_cases hBM : B = M
      · rw [hBM]
        exact le_normalizer
      · exact (hcen B M hB hM hBM).trans (Subgroup.centralizer_le_normalizer _)
  have hAB : ∀ M : Subgroup X, IsComponent M → (¬ ∀ r ∈ R, ∀ z ∈ M, r * z = z * r) →
      M = A ∨ M = B := by
    intro M hM hnc
    by_contra hne
    push Not at hne
    apply hnc
    intro r hr z hz
    have hc : A ⊔ B ≤ centralizer (M : Set X) :=
      sup_le (hcen A M hA hM fun h => hne.1 h.symm) (hcen B M hB hM fun h => hne.2 h.symm)
    exact (mem_centralizer_iff.1 (hc (hRAB hr)) z hz).symm
  have hperm : ∀ g ∈ S, ∀ M : Subgroup X, IsComponent M → (¬ ∀ r ∈ R, ∀ z ∈ M, r * z = z * r) →
      IsComponent (conjSub g M) ∧ ¬ ∀ r ∈ R, ∀ z ∈ conjSub g M, r * z = z * r := by
    intro g hg M hM hnc
    refine ⟨isComponent_map_mulEquiv (MulAut.conj g) hM, fun hall => hnc fun r hr z hz => ?_⟩
    have hr' : g * r * g⁻¹ ∈ R := (mem_normalizer_iff.1 (hSR hg) r).1 hr
    have hz' : g * z * g⁻¹ ∈ conjSub g M := conj_mem_conjSub hz
    have h := hall _ hr' _ hz'
    have : g * (r * z) * g⁻¹ = g * (z * r) * g⁻¹ := by
      calc g * (r * z) * g⁻¹ = (g * r * g⁻¹) * (g * z * g⁻¹) := by group
        _ = (g * z * g⁻¹) * (g * r * g⁻¹) := h
        _ = g * (z * r) * g⁻¹ := by group
    simpa using this
  intro g hg
  by_contra hne
  obtain ⟨hL1c, hL1nc⟩ := hperm g hg L hL hLnc
  obtain ⟨hL2c, hL2nc⟩ := hperm g hg _ hL1c hL1nc
  have h0 := hAB L hL hLnc
  have h1 := hAB _ hL1c hL1nc
  have h2' := hAB _ hL2c hL2nc
  have hcinj : ∀ M N : Subgroup X, conjSub g M = conjSub g N → M = N := by
    intro M N h
    have := congrArg (conjSub g⁻¹) h
    rwa [conjSub_conjSub, conjSub_conjSub, inv_mul_cancel, conjSub_one, conjSub_one] at this
  have hinj : conjSub g (conjSub g L) ≠ conjSub g L := fun h => hne (hcinj _ _ h)
  have hL2 : conjSub g (conjSub g L) = L := by
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2' with h2' | h2' <;>
      first
        | exact (hne (h1.trans h0.symm)).elim
        | exact (hinj (h2'.trans h1.symm)).elim
        | exact h2'.trans h0.symm
  obtain ⟨m, hm, hgm2⟩ := h2 g hg
  have hgmL : conjSub (g ^ m) L = L := conjSub_eq_of_mem_normalizer (hABn L hL (hRAB hgm2))
  obtain ⟨j, rfl⟩ := hm
  have hsq : conjSub (g ^ 2) L = L := by
    rw [sq, ← conjSub_conjSub]
    exact hL2
  have hodd : conjSub (g ^ (2 * j + 1)) L = conjSub g L := by
    rw [pow_succ', pow_mul, ← conjSub_conjSub, conjSub_pow_eq hsq j]
  exact hne (hodd.symm.trans hgmL)

end SolvP101

end CFSG.GH74.Generic.BProg.B3
