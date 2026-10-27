module

public import CFSG.CGT.PushingUpLit.BHS.FourSymA
public import CFSG.CGT.PushingUpLit.BHS.FourSymE

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Permutation.SymmetricCoxeter CFSG.CGT.PushingUpLit.BHSSym

section Perm

variable {n : ℕ}

theorem adjSwap_fix_last_iff {i : ℕ} (hi : i < n) :
    adjSwap n i (Fin.last n) = Fin.last n ↔ i ≠ n - 1 := by
  rw [adjSwap_of_lt hi]
  constructor
  · intro h hin
    have hl : (⟨i + 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by
      show i + 1 = n
      omega)
    rw [← hl, Equiv.swap_apply_right] at h
    have := congrArg Fin.val h
    simp at this
  · intro hin
    refine Equiv.swap_apply_of_ne_of_ne ?_ ?_ <;> simp [Fin.ext_iff] <;> omega

theorem swap_mul_swap_not_comm {α : Type*} [DecidableEq α] {a b c : α} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) :
    Equiv.swap a b * Equiv.swap b c ≠ Equiv.swap b c * Equiv.swap a b := by
  intro h
  have h1 := congrArg (fun f : Equiv.Perm α => f a) h
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne hab hac] at h1
  exact hbc h1

theorem adjSwap_succ_not_comm {i : ℕ} (hi : i + 1 < n) :
    adjSwap n i * adjSwap n (i + 1) ≠ adjSwap n (i + 1) * adjSwap n i := by
  rw [adjSwap_of_lt (by omega : i < n), adjSwap_of_lt hi]
  exact swap_mul_swap_not_comm (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]; omega)
    (by simp [Fin.ext_iff])

theorem adjSwap_inj_of_lt {i j : ℕ} (hi : i < n) (hj : j < n) (h : adjSwap n i = adjSwap n j) :
    i = j := by
  rw [adjSwap_of_lt hi, adjSwap_of_lt hj] at h
  rcases swap_eq_swap (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) h with
    ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact congrArg Fin.val h1
  · have h1' := congrArg Fin.val h1
    have h2' := congrArg Fin.val h2
    simp at h1' h2'
    omega

end Perm

section Chain

variable {V : Type} [CommGroup V] [Finite V] {D : Set (Subgroup (MulAut V))}
  {E : Subgroup (MulAut V)} {m : ℕ}

theorem SymCore.exists_transv_swap (d : SymCore D E m) (h : Hyp41 E D)
    (hV : ∀ v : V, v ^ 2 = 1) (hD2 : ∀ B ∈ D, Nat.card B = 2) {a b : Fin m} (hab : a ≠ b)
    {x : MulAut V} (hx : x ∈ E) (hθ : d.θ ⟨x, hx⟩ = Equiv.swap a b) :
    ∃ u : V, IsTransv x u ∧ Subgroup.zpowers x ∈ D := by
  obtain ⟨B, hB, hBiff⟩ := d.cls a b hab
  have hxB : x ∈ B := (hBiff ⟨x, hx⟩).2 (Or.inr hθ)
  have hBD : B ∈ D := hB.1
  obtain ⟨x', u, hx't, -, hBx', -⟩ := exists_transv_of_card_two h hV hBD (hD2 B hBD)
  have hxx' : x ∈ Subgroup.zpowers x' := hBx' ▸ hxB
  have hx1 : x ≠ 1 := by
    intro h1
    have h2 : (⟨x, hx⟩ : ↥E) = 1 := Subtype.ext h1
    rw [h2, map_one] at hθ
    have h3 := congrArg (fun f : Equiv.Perm (Fin m) => f a) hθ
    simp at h3
    exact hab h3
  rcases eq_one_or_of_mem_zpowers hx't.sq hxx' with h1 | h1
  · exact absurd h1 hx1
  · rw [h1]
    exact ⟨u, hx't, hBx' ▸ hBD⟩

theorem SymCore.exists_chain (d : SymCore D E m) (h : Hyp41 E D)
    (hV : ∀ v : V, v ^ 2 = 1) (hD2 : ∀ B ∈ D, Nat.card B = 2) (i₀ : Fin m) :
    ∃ (y : ℕ → MulAut V) (u : ℕ → V),
      (∀ i < m - 1, IsTransv (y i) (u i) ∧ y i ∈ E ∧ Subgroup.zpowers (y i) ∈ D) ∧
      (∀ i, i + 1 < m - 1 → y i * y (i + 1) ≠ y (i + 1) * y i) ∧
      (∀ i j, i + 2 ≤ j → j < m - 1 → y i * y j = y j * y i) ∧
      (∀ i < m - 1, ∀ j < m - 1, i ≠ j → y i ≠ y j) ∧
      Subgroup.closure (y '' Set.Iio (m - 1)) = E ∧
      (∀ i < m - 1, ∀ hi : y i ∈ E, (d.θ ⟨y i, hi⟩ i₀ = i₀ ↔ i ≠ m - 2)) := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by have := d.three_le; omega⟩
  have e1 : n + 1 - 1 = n := by omega
  have e2 : n + 1 - 2 = n - 1 := by omega
  rw [e1, e2]
  obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm (Fin (n + 1)), τ (Fin.last n) = i₀ :=
    ⟨Equiv.swap i₀ (Fin.last n), Equiv.swap_apply_right _ _⟩
  let Ξ : Equiv.Perm (Fin (n + 1)) →* MulAut V :=
    E.subtype.comp (d.θ.symm.toMonoidHom.comp (MulAut.conj τ).toMonoidHom)
  have hΞ : ∀ z, Ξ z = ((d.θ.symm (τ * z * τ⁻¹) : ↥E) : MulAut V) := fun z => rfl
  have hΞE : ∀ z, Ξ z ∈ E := fun z => by
    rw [hΞ]
    exact (d.θ.symm (τ * z * τ⁻¹)).2
  have hΞinj : Function.Injective Ξ := by
    intro z w hzw
    have h1 : d.θ.symm (τ * z * τ⁻¹) = d.θ.symm (τ * w * τ⁻¹) := Subtype.ext (by
      rw [← hΞ, ← hΞ]
      exact hzw)
    have h2 := d.θ.symm.injective h1
    simpa using h2
  have hΞθ : ∀ (z : Equiv.Perm (Fin (n + 1))) (hz : Ξ z ∈ E), d.θ ⟨Ξ z, hz⟩ = τ * z * τ⁻¹ := by
    intro z hz
    have h1 : (⟨Ξ z, hz⟩ : ↥E) = d.θ.symm (τ * z * τ⁻¹) := Subtype.ext (hΞ z)
    rw [h1]
    exact d.θ.apply_symm_apply _
  have hΞrange : Ξ.range = E := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨z, rfl⟩
      exact hΞE z
    · intro x hx
      refine ⟨τ⁻¹ * d.θ ⟨x, hx⟩ * τ, ?_⟩
      rw [hΞ]
      have h1 : τ * (τ⁻¹ * d.θ ⟨x, hx⟩ * τ) * τ⁻¹ = d.θ ⟨x, hx⟩ := by group
      rw [h1]
      exact congrArg Subtype.val (d.θ.symm_apply_apply ⟨x, hx⟩)
  have hcox : IsCoxeterA n (fun i => Ξ (adjSwap n i)) := IsCoxeterA.map Ξ (isCoxeterA_adjSwap n)
  have hex : ∀ i : ℕ, ∃ u : V, i < n → IsTransv (Ξ (adjSwap n i)) u ∧
      Subgroup.zpowers (Ξ (adjSwap n i)) ∈ D := by
    intro i
    by_cases hi : i < n
    · have hne : τ ⟨i, by omega⟩ ≠ τ ⟨i + 1, by omega⟩ := fun e => by
        have := congrArg Fin.val (τ.injective e)
        simp at this
      have hθ : d.θ ⟨Ξ (adjSwap n i), hΞE _⟩ =
          Equiv.swap (τ ⟨i, by omega⟩) (τ ⟨i + 1, by omega⟩) := by
        rw [hΞθ, adjSwap_of_lt hi, Equiv.swap_apply_apply]
      obtain ⟨u, hu⟩ := d.exists_transv_swap h hV hD2 hne (hΞE _) hθ
      exact ⟨u, fun _ => hu⟩
    · exact ⟨1, fun h' => absurd h' hi⟩
  choose u hu using hex
  refine ⟨fun i => Ξ (adjSwap n i), u, fun i hi => ⟨(hu i hi).1, hΞE _, (hu i hi).2⟩, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro i hi h1
    refine adjSwap_succ_not_comm hi (hΞinj ?_)
    rw [map_mul, map_mul]
    exact h1
  · exact fun i j hij hj => hcox.comm i j hij hj
  · intro i hi j hj hij h1
    exact hij (adjSwap_inj_of_lt hi hj (hΞinj h1))
  · show Subgroup.closure ((fun i => Ξ (adjSwap n i)) '' Set.Iio n) = E
    have h1 : (fun i => Ξ (adjSwap n i)) '' Set.Iio n = Ξ '' (adjSwap n '' Set.Iio n) := by
      rw [Set.image_image]
    rw [h1, ← MonoidHom.map_closure, closure_adjSwap, Subgroup.map_top, hΞrange]
  · intro i hi hyi
    show d.θ ⟨Ξ (adjSwap n i), hyi⟩ (i₀) = i₀ ↔ i ≠ n - 1
    rw [hΞθ]
    have h1 : τ⁻¹ i₀ = Fin.last n := by
      rw [Equiv.Perm.inv_eq_iff_eq, hτ]
    have h2 : (τ * adjSwap n i * τ⁻¹) i₀ = τ (adjSwap n i (Fin.last n)) := by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1]
    rw [h2, ← adjSwap_fix_last_iff hi, ← hτ]
    exact τ.injective.eq_iff

end Chain

end CFSG.CGT.PushingUpLit.BHS
