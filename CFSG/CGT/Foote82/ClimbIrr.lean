module

public import CFSG.CGT.Foote82.Setup
import CFSG.Quasithin.Background.G11Basic
import CFSG.CGT.Foote82.Lemma61

public section

namespace CFSG.CGT.Foote82

open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

private theorem commSpace_commSpace_of_perfect {A : Subgroup (GLV V)} (hperf : ⁅A, A⁆ = A)
    {X : Submodule (ZMod 2) V} (hX : Invariant A X) :
    commSpace A (commSpace A X) = commSpace A X := by
  have hconj : ∀ k' ∈ A, ∀ k ∈ A, k' * k * k'⁻¹ ∈ A := fun k' hk' k hk =>
    A.mul_mem (A.mul_mem hk' hk) (A.inv_mem hk')
  refine le_antisymm (commSpace_le_of_invariant (invariant_commSpace hconj hX)) ?_
  set M : Submodule (ZMod 2) V := commSpace A (commSpace A X) with hM
  let K : Subgroup (GLV V) :=
    { carrier := {k | k ∈ A ∧ ∀ v ∈ X, k v - v ∈ M}
      mul_mem' := fun {a b} ha hb => by
        refine ⟨A.mul_mem ha.1 hb.1, fun v hv => ?_⟩
        have h := M.add_mem (ha.2 (b v) (hX b hb.1 v hv)) (hb.2 v hv)
        rwa [sub_add_sub_cancel] at h
      one_mem' := ⟨A.one_mem, fun v _ => by simp⟩
      inv_mem' := fun {a} ha => by
        refine ⟨A.inv_mem ha.1, fun v hv => ?_⟩
        have h := M.neg_mem (ha.2 (a⁻¹ v) (hX a⁻¹ (A.inv_mem ha.1) v hv))
        simpa using h }
  have hcomm : ⁅A, A⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    refine ⟨A.mul_mem (A.mul_mem (A.mul_mem hg hh) (A.inv_mem hg)) (A.inv_mem hh),
      fun v hv => ?_⟩
    have key : ∀ u ∈ X, (g * h * g⁻¹ * h⁻¹) (h (g u)) - h (g u) ∈ M := by
      intro u hu
      have e1 : (g * h * g⁻¹ * h⁻¹) (h (g u)) = g (h u) := by simp
      have e2 : g (h u) - h (g u) = (g (h u - u) - (h u - u)) - (h (g u - u) - (g u - u)) := by
        simp only [map_sub]
        abel
      rw [e1, e2]
      exact M.sub_mem (sub_mem_commSpace hg (sub_mem_commSpace hh hu))
        (sub_mem_commSpace hh (sub_mem_commSpace hg hu))
    have hu : g⁻¹ (h⁻¹ v) ∈ X := hX g⁻¹ (A.inv_mem hg) _ (hX h⁻¹ (A.inv_mem hh) v hv)
    have e : h (g (g⁻¹ (h⁻¹ v))) = v := by simp
    have := key _ hu
    rw [e] at this
    exact this
  rw [hperf] at hcomm
  exact commSpace_le_iff.2 fun l hl v hv => (hcomm hl).2 v hv

theorem trivial_of_commSpace_le_fixedSpace_of_perfect {A : Subgroup (GLV V)} (hperf : ⁅A, A⁆ = A)
    {X : Submodule (ZMod 2) V} (hX : Invariant A X) (h : commSpace A X ≤ fixedSpace A) :
    ∀ a ∈ A, ∀ x ∈ X, a x = x := by
  have h0 : commSpace A (commSpace A X) = ⊥ :=
    commSpace_eq_bot_iff.2 fun l hl w hw => h hw l hl
  rw [commSpace_commSpace_of_perfect hperf hX] at h0
  exact commSpace_eq_bot_iff.1 h0

private theorem le_of_forall_conj_mem {B A K : Subgroup (GLV V)} (hBA : B ≤ normalClosure B A)
    (h : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ K) : B ≤ K := by
  refine hBA.trans ?_
  rw [normalClosure, Subgroup.closure_le]
  rintro _ ⟨b, hb, a, ha, rfl⟩
  exact h b hb a ha

private theorem commSpace_top_ne_bot {A : Subgroup (GLV V)} (hA : HasIrrTildeV A) :
    commSpace A ⊤ ≠ ⊥ :=
  (bot_le.trans_lt hA.1).ne'

private theorem fixedSpace_ne_top {B A : Subgroup (GLV V)} (hAB : A ≤ B) (hA : HasIrrTildeV A) :
    fixedSpace B ≠ ⊤ := by
  intro h
  refine commSpace_top_ne_bot hA (commSpace_eq_bot_iff.2 fun a ha u _ => ?_)
  rw [fixedSpace_eq_top_iff.1 h a (hAB ha)]
  rfl

theorem eq_bot_or_eq_top_of_le_normalClosure {G₀ B A : Subgroup (GLV V)} (hirr : IsIrr G₀ ⊤)
    (hBG : ∀ γ ∈ G₀, ∀ b ∈ B, γ * b * γ⁻¹ ∈ B) (hAB : A ≤ B) (hBA : B ≤ normalClosure B A)
    (hperf : ⁅A, A⁆ = A) (hA : HasIrrTildeV A) {U : Submodule (ZMod 2) V} (hU : Invariant B U) :
    U = ⊥ ∨ U = ⊤ := by
  have hconj : ∀ k' ∈ A, ∀ k ∈ A, k' * k * k'⁻¹ ∈ A := fun k' hk' k hk =>
    A.mul_mem (A.mul_mem hk' hk) (A.inv_mem hk')
  have hWne : commSpace A ⊤ ≠ ⊥ := commSpace_top_ne_bot hA
  have hfne : fixedSpace B ≠ ⊤ := fixedSpace_ne_top hAB hA
  obtain ⟨-, hmin⟩ : IrrSec A (tildeVBot A) (commSpace A ⊤) := hA
  have hUA : Invariant A U := hU.mono hAB
  have hWinv : Invariant A (commSpace A ⊤) := invariant_commSpace hconj (invariant_top A)
  have hCinv : Invariant A (tildeVBot A) := fun a ha u hu => by
    rw [hu.1 a ha]
    exact hu
  have hJinv : Invariant A (U ⊓ commSpace A ⊤ ⊔ tildeVBot A) := (hUA.inf hWinv).sup hCinv
  rcases hmin _ hJinv le_sup_right (sup_le inf_le_right inf_le_right) with hJ | hJ
  ·
    have hcomm : commSpace A U ≤ fixedSpace A := by
      refine commSpace_le_iff.2 fun a ha u hu => ?_
      have hmem : a u - u ∈ U ⊓ commSpace A ⊤ :=
        ⟨U.sub_mem (hUA a ha u hu) hu, sub_mem_commSpace ha Submodule.mem_top⟩
      have : a u - u ∈ tildeVBot A := by
        rw [← hJ]
        exact Submodule.mem_sup_left hmem
      exact this.1
    have hfix := trivial_of_commSpace_le_fixedSpace_of_perfect hperf hUA hcomm
    have hB : B ≤ centralizerOn B U := le_of_forall_conj_mem hBA fun b hb a ha => by
      refine ⟨B.mul_mem (B.mul_mem hb (hAB ha)) (B.inv_mem hb), fun u hu => ?_⟩
      have h1 : (b⁻¹ : GLV V) u ∈ U := hU b⁻¹ (B.inv_mem hb) u hu
      calc (b * a * b⁻¹) u = b (a (b⁻¹ u)) := rfl
        _ = b (b⁻¹ u) := by rw [hfix a ha _ h1]
        _ = u := by simp
    have hUB : U ≤ fixedSpace B := fun u hu b hb => (hB hb).2 u hu
    left
    rcases hirr.eq_bot_or_eq (invariant_fixedSpace hBG) le_top with h | h
    · rw [eq_bot_iff, ← h]
      exact hUB
    · exact absurd h hfne
  ·
    have hWJ : commSpace A ⊤ ≤ U ⊓ commSpace A ⊤ ⊔ tildeVBot A := hJ.ge
    have hAW : commSpace A (commSpace A ⊤) ≤ U := by
      refine commSpace_le_iff.2 fun a ha x hx => ?_
      obtain ⟨y, hy, c, hc, rfl⟩ := Submodule.mem_sup.1 (hWJ hx)
      have e : a (y + c) - (y + c) = (a y - y) + (a c - c) := by
        rw [map_add]
        abel
      rw [e, hc.1 a ha, sub_self, add_zero]
      exact U.sub_mem (hUA a ha y hy.1) hy.1
    have hWU : commSpace A ⊤ ≤ U := (commSpace_commSpace_top_of_perfect hperf).ge.trans hAW
    let K : Subgroup (GLV V) :=
      { carrier := {k | ∀ v, k v - v ∈ U}
        mul_mem' := fun {a b} ha hb v => by
          have h := U.add_mem (ha (b v)) (hb v)
          rwa [sub_add_sub_cancel] at h
        one_mem' := fun v => by simp
        inv_mem' := fun {a} ha v => by
          have h := U.neg_mem (ha (a⁻¹ v))
          simpa using h }
    have hB : B ≤ K := le_of_forall_conj_mem hBA fun b hb a ha v => by
      have e : (b * a * b⁻¹) v - v = b (a (b⁻¹ v) - b⁻¹ v) := by simp
      show (b * a * b⁻¹) v - v ∈ U
      rw [e]
      exact hU b hb _ (hWU (sub_mem_commSpace ha Submodule.mem_top))
    have hBU : commSpace B ⊤ ≤ U := commSpace_le_iff.2 fun b hb v _ => hB hb v
    have hinv : Invariant G₀ (commSpace B ⊤) := invariant_commSpace hBG (invariant_top G₀)
    have hne : commSpace B ⊤ ≠ ⊥ := by
      intro h
      apply hWne
      rw [eq_bot_iff, ← h]
      exact commSpace_mono hAB le_rfl
    right
    rcases hirr.eq_bot_or_eq hinv le_top with h | h
    · exact absurd h hne
    · rw [h] at hBU
      exact top_le_iff.1 hBU

theorem fixedSpace_eq_bot_of_le_normalClosure {G₀ B A : Subgroup (GLV V)} (hirr : IsIrr G₀ ⊤)
    (hBG : ∀ γ ∈ G₀, ∀ b ∈ B, γ * b * γ⁻¹ ∈ B) (hAB : A ≤ B) (hBA : B ≤ normalClosure B A)
    (hperf : ⁅A, A⁆ = A) (hA : HasIrrTildeV A) : fixedSpace B = ⊥ := by
  have hBB : ∀ b' ∈ B, ∀ b ∈ B, b' * b * b'⁻¹ ∈ B := fun b' hb' b hb =>
    B.mul_mem (B.mul_mem hb' hb) (B.inv_mem hb')
  exact (eq_bot_or_eq_top_of_le_normalClosure hirr hBG hAB hBA hperf hA
    (invariant_fixedSpace hBB)).resolve_right (fixedSpace_ne_top hAB hA)

end CFSG.CGT.Foote82
