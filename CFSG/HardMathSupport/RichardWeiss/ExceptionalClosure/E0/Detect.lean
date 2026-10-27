module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.Frame
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.PairPerm
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.PairParity

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry Equiv Equiv.Perm

variable {N : ℕ} {W : Type*} [AddCommGroup W] {M : Type*} [Group M]
variable {θ : M →* Perm (Fin N)} {ρ : M →* AddMonoid.End W} {U : AddSubgroup W}
  {π : U →+ altHeart N} {L S : Subgroup M} {P : Subgroup (Perm (Fin N))} {ω : Perm (Fin N)}
  {Δ₀ : Finset (Fin N)} {Y : AddSubgroup W}

namespace E0Frame

variable (E : E0Frame θ ρ U π L S P ω Δ₀ Y)
include E

theorem exists_third (a b : Fin N) : ∃ c : Fin N, c ≠ a ∧ c ≠ b := by
  classical
  have hN := E.hN
  have h1 : 3 ≤ (Finset.univ : Finset (Fin N)).card := by simp; omega
  have h2 : ({a, b} : Finset (Fin N)).card ≤ 2 := Finset.card_le_two
  obtain ⟨c, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := ({a, b} : Finset (Fin N)))
    (t := Finset.univ) (by omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  exact ⟨c, hc.2.1, hc.2.2⟩

theorem pair_parity' {t : M} (ht : t ∈ S) {x : Fin N} (hx : x ∉ Δ₀)
    (hθt : θ t = swap x (ω x)) (y : W) :
    π ⟨ρ t y - y, E.F.sTriv t ht y⟩ = 0 ∨
      π ⟨ρ t y - y, E.F.sTriv t ht y⟩ = (pairEW x (ω x) : altHeart N) :=
  pair_parity E.F E.even (by have := E.hN; omega) ht (E.shape.ω_ne_self hx) hθt y

theorem det_iff {y : W} {x : Fin N} (hx : x ∉ Δ₀) {t : M} (ht : t ∈ S)
    (hθt : θ t = swap x (ω x)) :
    E.Det y x ↔ π ⟨ρ t y - y, E.F.sTriv t ht y⟩ = (pairEW x (ω x) : altHeart N) := by
  have hab : x ≠ ω x := E.shape.ω_ne_self hx
  obtain ⟨c, hc1, hc2⟩ := E.exists_third x (ω x)
  have hne : (pairEW x (ω x) : altHeart N) ≠ 0 := mk_pairEW_ne_zero hab hc1 hc2
  unfold E0Frame.Det
  constructor
  · rintro ⟨t', ht', hθt', hne'⟩
    have hρ : ρ t' = ρ t := E.rho_eq (hθt'.trans hθt.symm)
    have hel : (⟨ρ t' y - y, E.F.sTriv t' ht' y⟩ : U) = ⟨ρ t y - y, E.F.sTriv t ht y⟩ := by
      apply Subtype.ext
      simp only [hρ]
    rw [hel] at hne'
    rcases E.pair_parity' ht hx hθt y with h0 | h1
    · exact absurd h0 hne'
    · exact h1
  · intro h
    exact ⟨t, ht, hθt, by rw [h]; exact hne⟩

theorem det_symm_aux {y : W} {x : Fin N} : E.Det y x → E.Det y (ω x) := by
  unfold E0Frame.Det
  rintro ⟨t, ht, hθt, hne⟩
  refine ⟨t, ht, ?_, hne⟩
  rw [hθt, E.shape.ωω, swap_comm]

theorem det_symm {y : W} {x : Fin N} : E.Det y x ↔ E.Det y (ω x) :=
  ⟨E.det_symm_aux, fun h => by
    have := E.det_symm_aux h
    rwa [E.shape.ωω] at this⟩

theorem det_transport {m : M} (hm : ∀ s ∈ S, m * s * m⁻¹ ∈ S) {x : Fin N}
    (hσω : θ m (ω x) = ω (θ m x)) {y : W} (hy : E.Det y x) : E.Det (ρ m y) (θ m x) := by
  unfold E0Frame.Det at hy ⊢
  obtain ⟨t, ht, hθt, hne⟩ := hy
  refine ⟨m * t * m⁻¹, hm t ht, ?_, ?_⟩
  · rw [map_mul, map_mul, map_inv, hθt, ← hσω]
    exact (swap_apply_apply (θ m) x (ω x)).symm
  · intro h0
    apply hne
    have hρ : ρ (m * t * m⁻¹) (ρ m y) = ρ m (ρ t y) := by
      have e : m * t * m⁻¹ * m = m * t := by group
      calc ρ (m * t * m⁻¹) (ρ m y) = (ρ (m * t * m⁻¹) * ρ m) y := rfl
        _ = ρ (m * t * m⁻¹ * m) y := by rw [map_mul ρ (m * t * m⁻¹) m]
        _ = ρ (m * t) y := by rw [e]
        _ = ρ m (ρ t y) := by rw [map_mul ρ m t]; rfl
    have hel : (⟨ρ (m * t * m⁻¹) (ρ m y) - ρ m y,
        E.F.sTriv (m * t * m⁻¹) (hm t ht) (ρ m y)⟩ : U) =
        ⟨ρ m (ρ t y - y), E.F.stable m _ (E.F.sTriv t ht y)⟩ := by
      apply Subtype.ext
      simp only [hρ, map_sub]
    rw [hel, E.F.equiv m ⟨ρ t y - y, E.F.sTriv t ht y⟩] at h0
    have := congrArg (altAct (θ m)⁻¹) h0
    rw [altAct_inv_apply, map_zero] at this
    exact this

theorem normalizes_of_pairTransp {a b : Fin N} (ha : a ∉ Δ₀) (hb : b ∉ Δ₀)
    (hba : b ≠ ω a) {m : M} (hθm : θ m = pairTransp ω a b) :
    ∀ s ∈ S, m * s * m⁻¹ ∈ S := by
  intro s hs
  have hΔ : ∀ y ∈ Δ₀, pairTransp ω a b y = y := fun y hy => E.shape.pairTransp_fix ha hb hy
  have hω : ∀ z, z ∉ Δ₀ → pairTransp ω a b (ω z) = ω (pairTransp ω a b z) := by
    intro z _
    have := congrArg (fun f : Perm (Fin N) => f z)
      (E.shape.pairTransp_comm_ω ha hb hba)
    simpa [Perm.mul_apply] using this.symm
  have h1 : pairTransp ω a b * θ s * (pairTransp ω a b)⁻¹ ∈ E0grp P ω Δ₀ :=
    E0Shape.conj_mem_E0grp E.shape hΔ hω ((E.img (θ s)).1 ⟨s, hs, rfl⟩)
  have h2 : θ (m * s * m⁻¹) ∈ E0grp P ω Δ₀ := by
    rw [map_mul, map_mul, map_inv, hθm]; exact h1
  obtain ⟨s', hs', hθs'⟩ := (E.img _).2 h2
  have h3 : θ (s'⁻¹ * (m * s * m⁻¹)) = 1 := by
    rw [map_mul θ s'⁻¹ (m * s * m⁻¹), map_inv, hθs']; exact inv_mul_cancel _
  have h4 := E.kerS _ h3
  have : m * s * m⁻¹ = s' * (s'⁻¹ * (m * s * m⁻¹)) := by group
  rw [this]
  exact mul_mem hs' h4

theorem det_exists_all {y₀ : W} (hy₀ : y₀ ∈ Y) {x₀ : Fin N} (hx₀ : x₀ ∉ Δ₀)
    (h : E.Det y₀ x₀) {x : Fin N} (hx : x ∉ Δ₀) : ∃ y ∈ Y, E.Det y x := by
  by_cases h1 : x = x₀
  · subst h1; exact ⟨y₀, hy₀, h⟩
  by_cases h2 : x = ω x₀
  · subst h2; exact ⟨y₀, hy₀, E.det_symm.1 h⟩
  have hab : x ≠ x₀ := h1
  have hba : x ≠ ω x₀ := h2
  obtain ⟨m, hmL, hθm⟩ := E.F.alt (pairTransp ω x₀ x) (pairTransp_even hab)
  have hmS := E.normalizes_of_pairTransp hx₀ hx hba hθm
  have hσx₀ : θ m x₀ = x := by
    rw [hθm]; exact E.shape.pairTransp_apply_left hx₀ hba
  have hσω : θ m (ω x₀) = ω (θ m x₀) := by
    rw [hθm, E.shape.pairTransp_apply_ωa hx₀ hx hba, E.shape.pairTransp_apply_left hx₀ hba]
  have := E.det_transport hmS hσω h
  rw [hσx₀] at this
  exact ⟨ρ m y₀, E.hY2 m hmS y₀ hy₀, this⟩

end E0Frame

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0
