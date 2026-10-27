module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Xhat
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Orbit
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Core
public import CFSG.GroupTheory.OrderBelowSixtySolvable

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG.EvenSporadicStandard.HSStd CFSG.Blueprint
open scoped commutatorElement

local notation "A6" => alternatingGroup (Fin 6)

section Helpers

variable {T : Type} [Group T] [Finite T]

theorem perfect_le_centralizer_of_card_le_four (F : Subgroup T) [F.Normal] (hF : Nat.card F ≤ 4)
    (E : Subgroup T) (hE : ⁅E, E⁆ = E) : E ≤ centralizer (F : Set T) := by
  have htop : (⊤ : Subgroup ↥E).map E.subtype = E := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hcomm : _root_.commutator ↥E = ⊤ := by
    have h1 : (_root_.commutator ↥E).map E.subtype = E := by
      rw [_root_.commutator_def, Subgroup.map_commutator, htop, hE]
    exact Subgroup.map_injective E.subtype_injective (h1.trans htop.symm)
  let φ : ↥E →* MulAut ↥F := (MulAut.conjNormal : T →* MulAut ↥F).comp E.subtype
  have hsol : Group.IsSolvable (MulAut ↥F) := by
    apply CFSG.GroupTheory.groups_order_below_sixty_solvable
    have hinj : Function.Injective (MulAut.toPerm ↥F) := by
      intro a b h
      apply MulEquiv.ext
      intro x
      exact congrArg (fun p : Equiv.Perm ↥F => p x) h
    have h1 : Nat.card (MulAut ↥F) ≤ Nat.card (Equiv.Perm ↥F) := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_perm] at h1
    have h2 : (Nat.card ↥F).factorial ≤ (4 : ℕ).factorial := Nat.factorial_le hF
    have h3 : (4 : ℕ).factorial = 24 := by decide
    omega
  have hRperf : ⁅φ.range, φ.range⁆ = φ.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def, hcomm]
  have hR : φ.range = ⊥ := by
    by_contra hne
    have := Group.IsSolvable.commutator_lt_of_ne_bot hne
    rw [hRperf] at this
    exact lt_irrefl _ this
  intro x hx
  have h1 : φ ⟨x, hx⟩ = 1 := by
    have : φ ⟨x, hx⟩ ∈ φ.range := ⟨_, rfl⟩
    rw [hR] at this
    exact this
  rw [mem_centralizer_iff]
  intro f hf
  have h2 := congrArg (fun a : MulAut ↥F => ((a ⟨f, hf⟩ : ↥F) : T)) h1
  simp only [φ, MonoidHom.comp_apply, Subgroup.subtype_apply, MulAut.one_apply] at h2
  exact (mul_inv_eq_iff_eq_mul.1 h2).symm

variable {X : Type} [Group X] [Finite X]

theorem le_centralizer_of_inverted (κ : T →* X) (hκ : Function.Surjective κ)
    (A F : Subgroup T) [A.Normal] [F.Normal] (hker : κ.ker ≤ F ⊔ A)
    (hFA : F ≤ centralizer (A : Set T)) (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {t : T}
    (ht : t * t = 1) (hinv : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹) (E : Subgroup T) [E.Normal]
    (hN : ∀ M : Subgroup X, M.Normal → M ≤ E.map κ →
      (∀ g ∈ E, κ (t * g * t⁻¹ * g⁻¹) ∈ M) → M = E.map κ) :
    E ≤ centralizer (A : Set T) := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hcomm : ∀ g : T, t * g * t⁻¹ * g⁻¹ ∈ centralizer (A : Set T) := by
    intro g
    rw [mem_centralizer_iff]
    intro a ha
    have hb : g⁻¹ * a * g ∈ A := by
      simpa using ‹A.Normal›.conj_mem a ha g⁻¹
    have e1 : t⁻¹ * (g⁻¹ * a * g) * t = (g⁻¹ * a * g)⁻¹ := by
      have := hinv _ hb
      rw [ht'] at this ⊢
      exact this
    have e2 : t * a * t⁻¹ = a⁻¹ := hinv a ha
    have key : (t * g * t⁻¹ * g⁻¹) * a * (t * g * t⁻¹ * g⁻¹)⁻¹ = a := by
      calc (t * g * t⁻¹ * g⁻¹) * a * (t * g * t⁻¹ * g⁻¹)⁻¹
          = t * g * (t⁻¹ * (g⁻¹ * a * g) * t) * g⁻¹ * t⁻¹ := by group
        _ = t * g * (g⁻¹ * a * g)⁻¹ * g⁻¹ * t⁻¹ := by rw [e1]
        _ = t * a⁻¹ * t⁻¹ := by group
        _ = (t * a * t⁻¹)⁻¹ := by group
        _ = a := by rw [e2, inv_inv]
    exact (mul_inv_eq_iff_eq_mul.1 key).symm
  have hC : A ≤ centralizer (A : Set T) := fun a ha =>
    mem_centralizer_iff.2 fun b hb => hAab b hb a ha
  have hFAC : F ⊔ A ≤ centralizer (A : Set T) := sup_le hFA hC
  haveI hEC : (E ⊓ centralizer (A : Set T)).Normal := inferInstance
  have hM : (E ⊓ centralizer (A : Set T)).map κ = E.map κ := by
    apply hN
    · exact Subgroup.Normal.map hEC κ hκ
    · exact Subgroup.map_mono inf_le_left
    · intro g hg
      refine ⟨t * g * t⁻¹ * g⁻¹, ⟨?_, hcomm g⟩, rfl⟩
      exact E.mul_mem (‹E.Normal›.conj_mem g hg t) (E.inv_mem hg)
  intro e he
  have : κ e ∈ (E ⊓ centralizer (A : Set T)).map κ := by
    rw [hM]; exact ⟨e, he, rfl⟩
  obtain ⟨c, ⟨-, hcC⟩, hce⟩ := this
  have hq : c⁻¹ * e ∈ κ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hce, inv_mul_cancel]
  have hqC := hFAC (hker hq)
  have : e = c * (c⁻¹ * e) := by group
  rw [this]
  exact (centralizer (A : Set T)).mul_mem hcC hqC

end Helpers

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
