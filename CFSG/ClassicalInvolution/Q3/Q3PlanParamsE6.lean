module

public import CFSG.ClassicalInvolution.Q3.Q3PlanParamsAdjoint
public import CFSG.ClassicalInvolution.Q3.Q3PlanParamsCentral

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Blueprint.Chevalley CFSG.ClassicalInvolution.Generic
open CFSG.LieType.Chevalley (center_adjointGroup_eq_bot)

open CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LieType.CurtisTits in
theorem false_of_isClassicalMember3_e6 {r e : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) (he : 1 ≤ e)
    (h5 : 5 ≤ r ^ e) [Finite ↥(e6Data_valid.minGroup (GaloisField r e))] {X : Type} [Group X]
    [Finite X] (ψ : ↥(e6Data_valid.minGroup (GaloisField r e)) →* X)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center _) {L : Subgroup X} {z : X}
    (h : IsClassicalMember3 L z) : False := by
  set F := GaloisField r e with hF
  have hqs := isQuasisimple_e6 F
  have hθs := e6Isogeny_surjective F
  have hθker : (e6Isogeny F).ker ≤ Subgroup.center _ :=
    ker_le_center_of_isQuasisimple hqs (e6Isogeny_ne_one F)
  have hKodd : Odd (Nat.card F) := CFSG.ClassicalInvolution.Upgrade.odd_card_galoisField hr2 he
  have hZ : Subgroup.center ↥(adjointGroup .E6 F) = ⊥ := center_adjointGroup_eq_bot
  have hkerψθ : ψ.ker ≤ (e6Isogeny F).ker := by
    intro k hk
    have : e6Isogeny F k ∈ Subgroup.center ↥(adjointGroup .E6 F) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨k', rfl⟩ := hθs y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hker hk) k']
    rw [hZ, Subgroup.mem_bot] at this
    exact this
  let φ : X →* ↥(adjointGroup .E6 F) := (MonoidHom.liftOfSurjective ψ hψ) ⟨e6Isogeny F, hkerψθ⟩
  have hφψ : ∀ k, φ (ψ k) = e6Isogeny F k := fun k =>
    MonoidHom.liftOfRightInverse_comp_apply ψ (Function.surjInv hψ)
      (Function.rightInverse_surjInv hψ) ⟨e6Isogeny F, hkerψθ⟩ k
  have hφs : Function.Surjective φ := fun y => by
    obtain ⟨k, rfl⟩ := hθs y
    exact ⟨ψ k, hφψ k⟩
  have hφker : φ.ker ≤ Subgroup.center X := by
    intro x hx
    obtain ⟨k, rfl⟩ := hψ x
    have hk : k ∈ (e6Isogeny F).ker := by
      rw [MonoidHom.mem_ker, ← hφψ]
      exact hx
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨k', rfl⟩ := hψ y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hθker hk) k']
  have hXq : CFSG.Open.IsQuasisimple X := by
    obtain ⟨k, hk⟩ := hψ z
    exact CFSG.ClassicalInvolution.ModelFacts.open_isQuasisimple
      (CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hqs hψ ⟨k, by rw [hk]; exact h.ne_one⟩)
  have hφz : φ z ≠ 1 := fun h1 =>
    h.not_mem_center_of_quasisimple hXq (hφker (MonoidHom.mem_ker.mpr h1))
  have : Finite ↥(adjointGroup .E6 F) := Finite.of_surjective φ hφs
  exact false_of_isClassicalMember3_adjoint (τ := .E6) (Or.inr (Or.inr (Or.inl rfl))) hr2 he h5
    (MonoidHom.id _) Function.surjective_id (by simp) (h.map_central φ hφs hφker hφz)

theorem classicalMemberParameters3At_E6 : ClassicalMemberParameters3At .E6 := by
  intro n r e hr hr2 hadm hne X _ _ ψ hψ hker L z h
  have : Fact r.Prime := ⟨hr⟩
  obtain rfl : n = 0 := hadm.2.2
  have hfin : Finite (modelUniv .E6 0 r e hr).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv hr2 hr trivial hadm
  have : Finite ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup (GaloisField r e)) := hfin
  exact false_of_isClassicalMember3_e6 hr2 hadm.2.1
    (five_le_pow_of_odd_prime_of_ne_three hr hr2 hadm.2.1 hne) ψ hψ hker h

end CFSG.ClassicalInvolution.Q3
