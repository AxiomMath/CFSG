module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.PiFrame

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0

open CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator Equiv Equiv.Perm

variable {N : ℕ} {W : Type*} [AddCommGroup W] {M : Type*} [Group M]
variable {θ : M →* Perm (Fin N)} {ρ : M →* AddMonoid.End W} {U : AddSubgroup W}
  {π : U →+ altHeart N} {L S : Subgroup M}

theorem exists_two_off {Δ : Finset (Fin N)} (hΔ : 4 ≤ (Finset.univ \ Δ).card) (i j : Fin N) :
    ∃ k r : Fin N, k ∉ Δ ∧ r ∉ Δ ∧ k ≠ i ∧ k ≠ j ∧ r ≠ i ∧ r ≠ j ∧ r ≠ k := by
  classical
  have h1 : 2 ≤ ((Finset.univ \ Δ) \ {i, j}).card := by
    have := Finset.le_card_sdiff {i, j} (Finset.univ \ Δ)
    have h2 : ({i, j} : Finset (Fin N)).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨k, hk, r, hr, hkr⟩ := Finset.one_lt_card.1 (show 1 < _ from h1)
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, not_or] at hk hr
  exact ⟨k, r, hk.1, hr.1, hk.2.1, hk.2.2, hr.2.1, hr.2.2, fun h => hkr h.symm⟩

theorem support_lemma (F : PiFrame θ ρ U π L S) {s : M} (hs : s ∈ S) (Δ : Finset (Fin N))
    (hΔ : 4 ≤ (Finset.univ \ Δ).card) (hsΔ : ∀ i, i ∉ Δ → θ s i = i) (w : W) (i j : Fin N)
    (hi : i ∉ Δ) (hj : j ∉ Δ) :
    altHeartCoord i (π ⟨ρ s w - w, F.sTriv s hs w⟩) j = 0 := by
  classical
  by_cases hij : i = j
  · subst hij; exact altHeartCoord_self _ _
  obtain ⟨k, r, hkΔ, hrΔ, hki, hkj, hri, hrj, hrk⟩ := exists_two_off hΔ i j
  set σ : Perm (Fin N) := swap i j * swap j k with hσ
  have hσi : σ i = j := by
    simp only [hσ, Perm.mul_apply]
    rw [swap_apply_of_ne_of_ne hij hki.symm, swap_apply_left]
  have hσr : σ r = r := by
    simp only [hσ, Perm.mul_apply]
    rw [swap_apply_of_ne_of_ne hrj hrk, swap_apply_of_ne_of_ne hri hrj]
  have hσinv : σ⁻¹ j = i := by
    rw [Perm.inv_eq_iff_eq]; exact hσi.symm
  have hσalt : σ ∈ alternatingGroup (Fin N) := by
    rw [Perm.mem_alternatingGroup, hσ, Perm.sign_mul, Perm.sign_swap hij,
      Perm.sign_swap (Ne.symm hkj)]
    decide
  obtain ⟨l, hl, hθl⟩ := F.alt σ hσalt
  have hdisj : (θ s).Disjoint σ := by
    intro x
    by_cases hx : x ∈ Δ
    · right
      have hxi : x ≠ i := fun h => hi (h ▸ hx)
      have hxj : x ≠ j := fun h => hj (h ▸ hx)
      have hxk : x ≠ k := fun h => hkΔ (h ▸ hx)
      simp only [hσ, Perm.mul_apply]
      rw [swap_apply_of_ne_of_ne hxj hxk, swap_apply_of_ne_of_ne hxi hxj]
    · left; exact hsΔ x hx
  have hcom : θ s * θ l = θ l * θ s := by
    rw [hθl]; exact hdisj.commute
  have hρ := F.comm hcom
  set y : W := ρ s w - w with hy
  have hyU : y ∈ U := F.sTriv s hs w
  set w' : W := ρ l w - w with hw'
  have hw'U : w' ∈ U := F.lTriv l hl w
  have hpt : ρ s (ρ l w) = ρ l (ρ s w) := congrArg (fun f : AddMonoid.End W => f w) hρ
  have key1 : ρ l y - y = ρ s w' - w' := by
    rw [hy, hw', map_sub, map_sub, hpt]
    abel
  have key2 : altAct (θ l) (π ⟨y, hyU⟩) - π ⟨y, hyU⟩ =
      altAct (θ s) (π ⟨w', hw'U⟩) - π ⟨w', hw'U⟩ := by
    rw [← F.pi_sub l ⟨y, hyU⟩, ← F.pi_sub s ⟨w', hw'U⟩]
    congr 1
    exact Subtype.ext key1
  rw [hθl] at key2
  have hsr : θ s r = r := hsΔ r hrΔ
  have hsj : (θ s)⁻¹ j = j := by
    rw [Perm.inv_eq_iff_eq]; exact (hsΔ j hj).symm
  have key3 : altHeartCoord r (altAct σ (π ⟨y, hyU⟩) - π ⟨y, hyU⟩) j =
      altHeartCoord r (altAct (θ s) (π ⟨w', hw'U⟩) - π ⟨w', hw'U⟩) j := by rw [key2]
  rw [map_sub, map_sub] at key3
  simp only [Pi.sub_apply] at key3
  rw [altHeartCoord_altAct hσr, altHeartCoord_altAct hsr, hσinv, hsj] at key3
  have key4 : altHeartCoord r (π ⟨y, hyU⟩) i = altHeartCoord r (π ⟨y, hyU⟩) j := by
    exact sub_eq_zero.mp (key3.trans (sub_self _))
  have := altHeartCoord_rebase i r (π ⟨y, hyU⟩) j
  rw [this, key4]
  generalize altHeartCoord r (π ⟨y, hyU⟩) j = a
  revert a
  decide

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0
