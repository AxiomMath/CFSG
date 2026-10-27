module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.Detect

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry Equiv Equiv.Perm Classical

variable {N : ℕ} {W : Type*} [AddCommGroup W] {M : Type*} [Group M]
variable {θ : M →* Perm (Fin N)} {ρ : M →* AddMonoid.End W} {U : AddSubgroup W}
  {π : U →+ altHeart N} {L S : Subgroup M} {P : Subgroup (Perm (Fin N))} {ω : Perm (Fin N)}
  {Δ₀ : Finset (Fin N)} {Y : AddSubgroup W}

namespace E0Frame

variable (E : E0Frame θ ρ U π L S P ω Δ₀ Y)
include E

theorem coord_pairEW {x : Fin N} (hx : x ∉ Δ₀) {r : Fin N} (hr : r ∈ Δ₀) (j : Fin N) :
    altHeartCoord r (pairEW x (ω x) : altHeart N) j = if j = x ∨ j = ω x then 1 else 0 := by
  have hrx : r ≠ x := fun e => hx (e ▸ hr)
  have hrω : r ≠ ω x := fun e => E.shape.ω_not_mem hx (e ▸ hr)
  have hxω : x ≠ ω x := E.shape.ω_ne_self hx
  rw [altHeartCoord_mk, pairEW_apply, pairEW_apply]
  by_cases h1 : j = x
  · subst h1
    simp [hrx, hrω, hxω]
  · by_cases h2 : j = ω x
    · subst h2
      simp [hrx, hrω, h1]
    · simp [h1, h2, hrx, hrω]

theorem formula_one {s : M} (hs : s ∈ S) (h1 : θ s = 1) (y : W) (r : Fin N) (j : Fin N) :
    altHeartCoord r (π ⟨ρ s y - y, E.F.sTriv s hs y⟩) j = 0 := by
  have hρ : ρ s = 1 := E.F.ker s h1
  have : (⟨ρ s y - y, E.F.sTriv s hs y⟩ : U) = 0 := by
    apply Subtype.ext
    simp [hρ]
  rw [this, map_zero]
  simp

theorem pairs_formula {r₀ : Fin N} (hr₀ : r₀ ∈ Δ₀) (k : ℕ) :
    ∀ (s : M) (hs : s ∈ S) (σ : Perm (Fin N)), θ s = σ → PairPerm ω Δ₀ σ →
      (Finset.univ.filter fun x => σ x ≠ x).card ≤ k → ∀ (y : W) (j : Fin N),
      altHeartCoord r₀ (π ⟨ρ s y - y, E.F.sTriv s hs y⟩) j =
        if (j ∉ Δ₀ ∧ σ j ≠ j) ∧ E.Det y j then 1 else 0 := by
  induction k with
  | zero =>
    intro s hs σ hθσ _ hk y j
    have hall : ∀ x, σ x = x := by
      intro x
      by_contra hx
      have : x ∈ (Finset.univ.filter fun x => σ x ≠ x) := by simp [hx]
      have := Finset.card_pos.2 ⟨x, this⟩
      omega
    have hσ1 : σ = 1 := by ext x; simp [hall x]
    subst hσ1
    rw [E.formula_one hs hθσ y r₀ j]
    simp
  | succ k ih =>
    intro s hs σ hθσ hσ hk y j
    by_cases hσ1 : σ = 1
    · subst hσ1
      rw [E.formula_one hs hθσ y r₀ j]
      simp
    obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
      by_contra hcon
      push Not at hcon
      exact hσ1 (by ext z; simp [hcon z])
    obtain ⟨hxΔ, hσx, hσωx⟩ := E0Shape.PairPerm.moved E.shape hσ hx
    obtain ⟨hstep, hσ'x, hσ'ωx, hσ'other⟩ := E0Shape.PairPerm.step E.shape hσ hx
    obtain ⟨t, ht, hθt⟩ := (E.img (swap x (ω x))).2 (E0Shape.swap_mem_E0grp hxΔ)
    have hs' : s * t ∈ S := mul_mem hs ht
    have hθs' : θ (s * t) = σ * swap x (ω x) := by rw [map_mul, hθσ, hθt]
    have hxmem : x ∈ (Finset.univ.filter fun z => σ z ≠ z) := by simp [hx]
    have hcard' : (Finset.univ.filter fun z => (σ * swap x (ω x)) z ≠ z).card ≤ k := by
      have hsub : (Finset.univ.filter fun z => (σ * swap x (ω x)) z ≠ z) ⊆
          (Finset.univ.filter fun z => σ z ≠ z).erase x := by
        intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
        simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
        have hzx : z ≠ x := fun e => hz (e ▸ hσ'x)
        have hzω : z ≠ ω x := fun e => hz (e ▸ hσ'ωx)
        refine ⟨hzx, ?_⟩
        rw [← hσ'other z hzx hzω]
        exact hz
      calc _ ≤ ((Finset.univ.filter fun z => σ z ≠ z).erase x).card := Finset.card_le_card hsub
        _ = (Finset.univ.filter fun z => σ z ≠ z).card - 1 := Finset.card_erase_of_mem hxmem
        _ ≤ k := by omega
    have IH := ih (s * t) hs' _ hθs' hstep hcard' y
    have hρt : ρ t⁻¹ = ρ t := E.rho_eq (by rw [map_inv, hθt, Equiv.swap_inv])
    have hρs : ρ s = ρ (s * t) * ρ t := by
      have e : s = (s * t) * t⁻¹ := by group
      conv_lhs => rw [e]
      rw [map_mul, hρt]
    have hs_apply : ρ s y = ρ (s * t) (ρ t y) := by rw [hρs]; rfl
    have hztU : ρ t y - y ∈ U := E.F.sTriv t ht y
    have hel : (⟨ρ s y - y, E.F.sTriv s hs y⟩ : U) =
        ⟨ρ t y - y, hztU⟩ + ⟨ρ (s * t) (ρ t y - y) - (ρ t y - y), E.F.sub_mem_U (s * t) hztU⟩ +
          ⟨ρ (s * t) y - y, E.F.sTriv (s * t) hs' y⟩ := by
      apply Subtype.ext
      simp only [AddSubgroup.coe_add]
      rw [hs_apply, map_sub]
      abel
    have hzt : π ⟨ρ t y - y, hztU⟩ = if E.Det y x then (pairEW x (ω x) : altHeart N) else 0 := by
      by_cases hD : E.Det y x
      · simp only [hD, ↓reduceIte]
        exact (E.det_iff hxΔ ht hθt).1 hD
      · simp only [hD, ↓reduceIte]
        rcases E.pair_parity' ht hxΔ hθt y with h0 | h1
        · exact h0
        · exact absurd ((E.det_iff hxΔ ht hθt).2 h1) hD
    have hfix : altAct (σ * swap x (ω x)) (π ⟨ρ t y - y, hztU⟩) = π ⟨ρ t y - y, hztU⟩ := by
      rw [hzt]
      split_ifs
      · rw [altAct_mk, evenWeightPerm_pairEW, hσ'x, hσ'ωx]
      · exact map_zero _
    have hmid : π ⟨ρ (s * t) (ρ t y - y) - (ρ t y - y), E.F.sub_mem_U (s * t) hztU⟩ = 0 := by
      have := E.F.pi_sub (s * t) ⟨ρ t y - y, hztU⟩
      rw [hθs', hfix, sub_self] at this
      exact this
    have hcoord : altHeartCoord r₀ (π ⟨ρ s y - y, E.F.sTriv s hs y⟩) j =
        altHeartCoord r₀ (π ⟨ρ t y - y, hztU⟩) j +
          altHeartCoord r₀ (π ⟨ρ (s * t) y - y, E.F.sTriv (s * t) hs' y⟩) j := by
      rw [hel]
      simp only [map_add, Pi.add_apply]
      rw [hmid]
      simp only [map_zero, Pi.zero_apply, add_zero]
    rw [hcoord, IH j, hzt]
    have hωxΔ : ω x ∉ Δ₀ := E.shape.ω_not_mem hxΔ
    have hxne : x ≠ ω x := E.shape.ω_ne_self hxΔ
    by_cases hjx : j = x
    · subst hjx
      have hc : altHeartCoord r₀ (if E.Det y j then (pairEW j (ω j) : altHeart N) else 0) j =
          if E.Det y j then 1 else 0 := by
        split_ifs
        · rw [E.coord_pairEW hxΔ hr₀]; simp
        · simp
      rw [hc]
      by_cases hD : E.Det y j
      · simp [hD, hσ'x, hxΔ, hx]
      · simp [hD, hσ'x]
    · by_cases hjω : j = ω x
      · subst hjω
        have hc : altHeartCoord r₀ (if E.Det y x then (pairEW x (ω x) : altHeart N) else 0) (ω x) =
            if E.Det y x then 1 else 0 := by
          split_ifs
          · rw [E.coord_pairEW hxΔ hr₀]; simp
          · simp
        rw [hc]
        have hne2 : σ (ω x) ≠ ω x := by rw [hσωx]; exact hxne
        by_cases hD : E.Det y x
        · have hD' : E.Det y (ω x) := E.det_symm.1 hD
          simp [hD, hD', hσ'ωx, hωxΔ, hne2]
        · have hD' : ¬ E.Det y (ω x) := fun h => hD (E.det_symm.2 h)
          simp [hD, hD', hσ'ωx]
      · have hc : altHeartCoord r₀ (if E.Det y x then (pairEW x (ω x) : altHeart N) else 0) j = 0 := by
          split_ifs
          · rw [E.coord_pairEW hxΔ hr₀]; simp [hjx, hjω]
          · simp
        rw [hc, hσ'other j hjx hjω]
        simp

end E0Frame

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0
