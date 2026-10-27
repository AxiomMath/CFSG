module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.Formula
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.Quad

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry Equiv Equiv.Perm Classical

variable {N : ℕ} {W : Type*} [AddCommGroup W] {M : Type*} [Group M]
variable {θ : M →* Perm (Fin N)} {ρ : M →* AddMonoid.End W} {U : AddSubgroup W}
  {π : U →+ altHeart N} {L S : Subgroup M} {P : Subgroup (Perm (Fin N))} {ω : Perm (Fin N)}
  {Δ₀ : Finset (Fin N)} {Y : AddSubgroup W}

theorem perm_inv_apply_self {α : Type*} (σ : Perm α) (x : α) : σ⁻¹ (σ x) = x :=
  σ.symm_apply_apply x

namespace E0Frame

variable (E : E0Frame θ ρ U π L S P ω Δ₀ Y)
include E

theorem support_of_noDet (hD : ∀ y ∈ Y, ∀ x, x ∉ Δ₀ → ¬ E.Det y x) {s : M} (hs : s ∈ S) {y : W}
    (hy : y ∈ Y) :
    ∀ i j, i ∉ Δ₀ → j ∉ Δ₀ → altHeartCoord i (π ⟨ρ s y - y, E.F.sTriv s hs y⟩) j = 0 := by
  obtain ⟨a, ha⟩ := E.exists_in
  have hε := (E.img (θ s)).1 ⟨s, hs, rfl⟩
  obtain ⟨⟨p, hp, hpx⟩, hpair⟩ := E0Shape.mem_E0grp_prop E.shape hε
  obtain ⟨v, hv, hθv⟩ := (E.img p).2 (E0Shape.P_le_E0grp hp)
  have hs₂S : v⁻¹ * s ∈ S := mul_mem (inv_mem hv) hs
  have hθs₂ : θ (v⁻¹ * s) = p⁻¹ * θ s := by rw [map_mul, map_inv, hθv]
  have hPP : PairPerm ω Δ₀ (p⁻¹ * θ s) := by
    refine ⟨fun y' hy' => ?_, fun x hx => ?_⟩
    · rw [Perm.mul_apply, hpx y' hy']
      exact perm_inv_apply_self p y'
    · have hnot : ∀ w, w ∉ Δ₀ → p⁻¹ w = w := fun w hw => E.shape.Pfix _ (inv_mem hp) w hw
      rw [Perm.mul_apply]
      rcases hpair x hx with h1 | h1
      · left; rw [h1]; exact hnot x hx
      · right; rw [h1]; exact hnot _ (E.shape.ω_not_mem hx)
  have hzero : ∀ j, altHeartCoord a (π ⟨ρ (v⁻¹ * s) y - y, E.F.sTriv _ hs₂S y⟩) j = 0 := by
    intro j
    rw [E.pairs_formula ha _ (v⁻¹ * s) hs₂S _ hθs₂ hPP le_rfl y j]
    have : ¬ ((j ∉ Δ₀ ∧ (p⁻¹ * θ s) j ≠ j) ∧ E.Det y j) := by
      rintro ⟨⟨hj, -⟩, hdet⟩
      exact hD y hy j hj hdet
    exact ite_eq_right_iff.2 (fun h => absurd h this)
  have hπk : π ⟨ρ (v⁻¹ * s) y - y, E.F.sTriv _ hs₂S y⟩ = 0 := by
    apply altHeartCoord_injective a
    funext j
    rw [hzero j]
    simp
  have hρk := E.F.sK v hv ⟨ρ (v⁻¹ * s) y - y, E.F.sTriv _ hs₂S y⟩ hπk
  have hρs : ρ s = ρ v * ρ (v⁻¹ * s) := by rw [← map_mul]; congr 1; group
  have hel : (⟨ρ s y - y, E.F.sTriv s hs y⟩ : U) =
      ⟨ρ (v⁻¹ * s) y - y, E.F.sTriv _ hs₂S y⟩ + ⟨ρ v y - y, E.F.sTriv v hv y⟩ := by
    apply Subtype.ext
    simp only [AddSubgroup.coe_add]
    have h1 : ρ s y = ρ v (ρ (v⁻¹ * s) y) := by rw [hρs]; rfl
    have h2 : ρ (v⁻¹ * s) y = (ρ (v⁻¹ * s) y - y) + y := by abel
    have h3 : ρ v (ρ (v⁻¹ * s) y - y) = ρ (v⁻¹ * s) y - y := hρk
    rw [h1, h2, map_add, h3]
    abel
  intro i j hi hj
  rw [hel, map_add, map_add]
  simp only [Pi.add_apply]
  rw [hπk]
  have hcard : 4 ≤ (Finset.univ \ Δ₀).card := by
    rw [Finset.card_univ_sdiff, Fintype.card_fin, E.shape.card]
    have := E.hN
    omega
  have hsΔ : ∀ i, i ∉ Δ₀ → θ v i = i := fun i hi => by rw [hθv]; exact E.shape.Pfix p hp i hi
  have := support_lemma E.F hv Δ₀ hcard hsΔ y i j hi hj
  simp [this]

theorem central_of_noDet (hD : ∀ y ∈ Y, ∀ x, x ∉ Δ₀ → ¬ E.Det y x) {x₁ x₂ x₃ r : Fin N}
    (h1 : x₁ ∉ Δ₀) (h2 : x₂ ∉ Δ₀) (h3 : x₃ ∉ Δ₀) (hr : r ∉ Δ₀)
    (h12 : x₂ ≠ x₁) (h13 : x₃ ≠ x₁) (h23 : x₃ ≠ x₂) (hr1 : r ≠ x₁) (hr2 : r ≠ x₂)
    (hr3 : r ≠ x₃) {g : M} (hg : g ∈ L) (hθg : θ g = swap x₁ x₂ * swap x₁ x₃) {s : M}
    (hs : s ∈ S) {y : W} (hy : y ∈ Y) : ρ g (ρ s y - y) = ρ s y - y := by
  set σ : Perm (Fin N) := swap x₁ x₂ * swap x₁ x₃ with hσ
  have hzU : ρ s y - y ∈ U := E.F.sTriv s hs y
  have hsupp := E.support_of_noDet hD hs hy
  have hσΔ : ∀ w ∈ Δ₀, σ w = w := by
    intro w hw
    have e1 : w ≠ x₁ := fun e => h1 (e ▸ hw)
    have e2 : w ≠ x₂ := fun e => h2 (e ▸ hw)
    have e3 : w ≠ x₃ := fun e => h3 (e ▸ hw)
    rw [hσ, Perm.mul_apply, swap_apply_of_ne_of_ne e1 e3, swap_apply_of_ne_of_ne e1 e2]
  have hσr : σ r = r := by
    rw [hσ, Perm.mul_apply, swap_apply_of_ne_of_ne hr1 hr3, swap_apply_of_ne_of_ne hr1 hr2]
  have hσinv : ∀ j, j ∉ Δ₀ → σ⁻¹ j ∉ Δ₀ := by
    intro j hj hmem
    apply hj
    have := hσΔ _ hmem
    rw [perm_apply_inv_self] at this
    exact this ▸ hmem
  have hπ0 : π ⟨ρ g (ρ s y - y) - (ρ s y - y), E.F.sub_mem_U g hzU⟩ = 0 := by
    apply altHeartCoord_injective r
    funext j
    rw [E.F.pi_sub g ⟨ρ s y - y, hzU⟩, hθg]
    rw [map_sub, Pi.sub_apply, altHeartCoord_altAct hσr]
    by_cases hj : j ∈ Δ₀
    · have : σ⁻¹ j = j := by rw [Perm.inv_eq_iff_eq]; exact (hσΔ j hj).symm
      rw [this]; simp; exact sub_self _
    · rw [hsupp r _ hr hj, hsupp r _ hr (hσinv j hj)]
      simp; exact sub_self _
  have hρk := E.lK g hg ⟨ρ g (ρ s y - y) - (ρ s y - y), E.F.sub_mem_U g hzU⟩ hπ0
  have hcyc : (swap x₁ x₂ * swap x₁ x₃).IsThreeCycle :=
    isThreeCycle_swap_mul_swap_same (Ne.symm h12) (Ne.symm h13) (Ne.symm h23)
  have hord : (σ * σ) * σ = 1 := by
    have := pow_orderOf_eq_one σ
    rw [hcyc.orderOf] at this
    simpa [pow_succ] using this
  have hg3 : ρ g * ρ g * ρ g = 1 := by
    rw [← map_mul, ← map_mul]
    apply E.F.ker
    rw [map_mul, map_mul, hθg]
    exact hord
  set z := ρ s y - y with hz
  have hk : ρ g (ρ g z - z) = ρ g z - z := hρk
  rw [map_sub] at hk
  have h2z : ∀ w : W, w + w = 0 := E.F.two
  have hTT : ρ g (ρ g z) = z := by
    calc ρ g (ρ g z) = (ρ g (ρ g z) - ρ g z) + ρ g z := by abel
      _ = (ρ g z - z) + ρ g z := by rw [hk]
      _ = (ρ g z + ρ g z) - z := by abel
      _ = 0 - z := by rw [h2z]
      _ = z := by rw [zero_sub]; exact neg_eq_of_add_eq_zero_right (h2z z)
  have h3z : ρ g (ρ g (ρ g z)) = z := by
    have := congrArg (fun f : AddMonoid.End W => f z) hg3
    exact this
  rw [hTT] at h3z
  exact h3z

end E0Frame

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0
