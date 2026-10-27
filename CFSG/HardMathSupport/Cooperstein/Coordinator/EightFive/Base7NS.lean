module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base7Ctx
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base7B42
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ModuleFF

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin CFSG.QuasithinUnique Equiv Equiv.Perm

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {n : ℕ} {ψ : ↥H →* Perm (Fin n)}

@[expose] def altPreRes (ψ : ↥H →* Perm (Fin n)) : ↥(altPre ψ) →* Perm (Fin n) :=
  ψ.comp (Subgroup.inclusion altPre_le)

theorem altPre_altPreRes : altPre (altPreRes ψ) = altPre ψ := by
  refine le_antisymm altPre_le fun x hx => mem_altPre_iff.2 ⟨hx, ?_⟩
  exact (coe_mem_altPre_iff (ψ := ψ) (x := ⟨x, altPre_le hx⟩)).1 hx

theorem altPreRes_injective (hψ : Function.Injective ψ) : Function.Injective (altPreRes ψ) :=
  fun _ _ hxy => Subtype.ext (congrArg (fun z : ↥H => (z : MulAut V)) (hψ hxy))

theorem le_range_altPreRes (hA : alternatingGroup (Fin n) ≤ ψ.range) :
    alternatingGroup (Fin n) ≤ (altPreRes ψ).range := by
  intro σ hσ
  obtain ⟨l, hl⟩ := altPreHom_surjective hA ⟨σ, hσ⟩
  exact ⟨l, by rw [altPreRes, MonoidHom.comp_apply, ← coe_altPreHom, hl]⟩

variable [Finite V]

theorem qOf_autSec_eq_one (hV : ∀ v : V, v ^ 2 = 1)
    {ψ : ↥H →* Perm (Fin 7)} (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin 7) ≤ ψ.range) {Y₀ Y₁ : Subgroup V} (h01 : Y₀ ≤ Y₁)
    (hH₀ : H ≤ stabSub Y₀) (hH₁ : H ≤ stabSub Y₁) (hL : ¬ IsCentralSec (altPre ψ) Y₀ Y₁)
    (hirr : ∀ Y : Subgroup V, (∀ l ∈ altPre ψ, ∀ y ∈ Y, l y ∈ Y) → Y₀ ≤ Y → Y ≤ Y₁ →
      Y = Y₀ ∨ Y = Y₁)
    {A₀ : Subgroup (MulAut (Sec Y₁ Y₀))} (hA₀ : IsFFStarOffender (autSec H Y₁ Y₀) A₀) :
    qOf (autSec H Y₁ Y₀) = ((1 : ℚ) : WithTop ℚ) := by
  have hlt : Y₀ < Y₁ := by
    refine lt_of_le_of_ne h01 fun h => hL fun l _ y hy => ?_
    rw [h]
    exact Y₁.mul_mem ((hH₁ (altPre_le ‹l ∈ altPre ψ›) y).2 hy) (Y₁.inv_mem hy)
  have C := ctx_autSec (Or.inr rfl) hψ hA hH₀ hH₁ hL
  have hI := isIrrSec_autSec (altPre_le.trans hH₀) (altPre_le.trans hH₁) hlt hirr
  rcases asB42Alt7_ctx (sq_eq_one_sec hV Y₁ Y₀) C hI hA₀ with h5 | h7
  · exact h5.2
  · exact h7.2.2.2.2.1

theorem card_le_index_fixV_autSec_of_irr
    (hV : ∀ v : V, v ^ 2 = 1) {ψ : ↥H →* Perm (Fin 7)} (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin 7) ≤ ψ.range) {Y₀ Y₁ : Subgroup V} (h01 : Y₀ ≤ Y₁)
    (hH₀ : H ≤ stabSub Y₀) (hH₁ : H ≤ stabSub Y₁) (hL : ¬ IsCentralSec (altPre ψ) Y₀ Y₁)
    (hirr : ∀ Y : Subgroup V, (∀ l ∈ altPre ψ, ∀ y ∈ Y, l y ∈ Y) → Y₀ ≤ Y → Y ≤ Y₁ →
      Y = Y₀ ∨ Y = Y₁)
    {B : Subgroup (MulAut V)} (hBH : B ≤ H) (hB : B ≠ ⊥) (hel : IsElemAbelian2 B) :
    Nat.card B ≤ (fixV (autSec B Y₁ Y₀)).index := by
  by_contra hlt
  push Not at hlt
  obtain ⟨A₀, -, hA₀, hstrong⟩ :=
    exists_strong_isFFStarOffender_autSec (by omega) hψ hA hH₀ hH₁ hL hBH hB hel hlt
  have hq := qOf_autSec_eq_one hV hψ hA h01 hH₀ hH₁ hL hirr hA₀
  have h1 := card_le_index_fixV_of_one_le_qOf (sq_eq_one_sec hV Y₁ Y₀) (hq ▸ le_rfl) hA₀.1
    hA₀.2.1 hA₀.2.2.1
  omega

theorem card_sec_ge_of_noncentral {ψ : ↥H →* Perm (Fin 7)} (hV : ∀ v : V, v ^ 2 = 1)
    (hψ : Function.Injective ψ) (hA : alternatingGroup (Fin 7) ≤ ψ.range) {Y₀ Y₁ : Subgroup V}
    (hH₀ : H ≤ stabSub Y₀) (hH₁ : H ≤ stabSub Y₁) (hL : ¬ IsCentralSec (altPre ψ) Y₀ Y₁) :
    2 ^ 4 ≤ Nat.card (Sec Y₁ Y₀) := by
  have C := ctx_autSec (Or.inr rfl) hψ hA hH₀ hH₁ hL
  exact B42A57.card_ge_of_faithful C fun s => by
    simpa [pow_two] using sq_eq_one_sec hV Y₁ Y₀ s

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
