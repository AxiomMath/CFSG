module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameAlpha

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Asc77.FrameVertex
open scoped commutatorElement

section DescentCore

variable {S H P : Type} [Group S] [Group H] [Group P]

private noncomputable def s26_conjPre (ψ : S →* H) {v : H}
    (hv : v ∈ Subgroup.normalizer (ψ.range : Set H)) (s : S) : S :=
  Classical.choose ((Subgroup.mem_normalizer_iff.mp hv (ψ s)).mp ⟨s, rfl⟩)

private theorem s26_psi_conjPre (ψ : S →* H) {v : H}
    (hv : v ∈ Subgroup.normalizer (ψ.range : Set H)) (s : S) :
    ψ (s26_conjPre ψ hv s) = v * ψ s * v⁻¹ :=
  Classical.choose_spec ((Subgroup.mem_normalizer_iff.mp hv (ψ s)).mp ⟨s, rfl⟩)

private theorem s26_conjPre_mul_mem_ker (ψ : S →* H) {v : H}
    (hv : v ∈ Subgroup.normalizer (ψ.range : Set H)) (s t : S) :
    s26_conjPre ψ hv (s * t) * (s26_conjPre ψ hv s * s26_conjPre ψ hv t)⁻¹ ∈ ψ.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, s26_psi_conjPre, s26_psi_conjPre,
    s26_psi_conjPre, map_mul]
  group

private noncomputable def s26_descentHom (ψ : S →* H) (hψ : ψ.ker ≤ Subgroup.center S) (π : S →* P)
    (hπk : π.ker = Subgroup.center S) {v : H}
    (hv : v ∈ Subgroup.normalizer (ψ.range : Set H)) : S →* P :=
  MonoidHom.mk' (fun s => π (s26_conjPre ψ hv s)) fun s t => by
    have h := s26_conjPre_mul_mem_ker ψ hv s t
    have h1 : π (s26_conjPre ψ hv (s * t) * (s26_conjPre ψ hv s * s26_conjPre ψ hv t)⁻¹) = 1 := by
      rw [← MonoidHom.mem_ker, hπk]
      exact hψ h
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    rw [h1, map_mul]

private theorem s26_center_le_ker_descentHom [Group.IsPerfect S] (ψ : S →* H)
    (hψ : ψ.ker ≤ Subgroup.center S) (π : S →* P) (hπk : π.ker = Subgroup.center S) {v : H}
    (hv : v ∈ Subgroup.normalizer (ψ.range : Set H)) :
    π.ker ≤ (s26_descentHom ψ hψ π hπk hv).ker := by
  intro s hs
  rw [hπk] at hs
  rw [MonoidHom.mem_ker]
  show π (s26_conjPre ψ hv s) = 1
  rw [← MonoidHom.mem_ker, hπk]
  refine mem_center_of_commutators_central (S := S) fun t => ?_
  apply hψ
  rw [MonoidHom.mem_ker, map_commutatorElement, s26_psi_conjPre]
  have hc : ∀ y ∈ ψ.range, ψ s * y = y * ψ s := by
    rintro _ ⟨u, rfl⟩
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hs u)]
  have hvi : v⁻¹ ∈ Subgroup.normalizer (ψ.range : Set H) := Subgroup.inv_mem _ hv
  have hmem : v⁻¹ * ψ t * v⁻¹⁻¹ ∈ ψ.range :=
    (Subgroup.mem_normalizer_iff.mp hvi (ψ t)).mp ⟨t, rfl⟩
  have h1 := hc _ hmem
  rw [commutatorElement_def]
  calc v * ψ s * v⁻¹ * ψ t * (v * ψ s * v⁻¹)⁻¹ * (ψ t)⁻¹
      = v * (ψ s * (v⁻¹ * ψ t * v) * (ψ s)⁻¹ * (v⁻¹ * (ψ t)⁻¹ * v)) * v⁻¹ := by group
    _ = 1 := by
      have e : ψ s * (v⁻¹ * ψ t * v) * (ψ s)⁻¹ = v⁻¹ * ψ t * v := by
        have h1' : ψ s * (v⁻¹ * ψ t * v⁻¹⁻¹) = (v⁻¹ * ψ t * v⁻¹⁻¹) * ψ s := h1
        simp only [inv_inv] at h1'
        calc ψ s * (v⁻¹ * ψ t * v) * (ψ s)⁻¹ = (ψ s * (v⁻¹ * ψ t * v)) * (ψ s)⁻¹ := by group
          _ = ((v⁻¹ * ψ t * v) * ψ s) * (ψ s)⁻¹ := by rw [h1']
          _ = v⁻¹ * ψ t * v := by group
      rw [e]
      group

theorem s26_exists_descent_core [Group.IsPerfect S] (ψ : S →* H) (hψ : ψ.ker ≤ Subgroup.center S)
    (π : S →* P) (hπ : Function.Surjective π) (hπk : π.ker = Subgroup.center S) {v : H}
    (hv : v ∈ Subgroup.normalizer (ψ.range : Set H)) :
    ∃ φ : P ≃* P, ∀ s s' : S, v * ψ s * v⁻¹ = ψ s' → φ (π s) = π s' := by
  have hvi : v⁻¹ ∈ Subgroup.normalizer (ψ.range : Set H) := Subgroup.inv_mem _ hv
  let f₀ : S →* P := s26_descentHom ψ hψ π hπk hv
  let f₁ : S →* P := s26_descentHom ψ hψ π hπk hvi
  let φ₀ : P →* P :=
    MonoidHom.liftOfSurjective π hπ ⟨f₀, s26_center_le_ker_descentHom ψ hψ π hπk hv⟩
  let φ₁ : P →* P :=
    MonoidHom.liftOfSurjective π hπ ⟨f₁, s26_center_le_ker_descentHom ψ hψ π hπk hvi⟩
  have h₀ : ∀ s, φ₀ (π s) = π (s26_conjPre ψ hv s) := fun s =>
    MonoidHom.liftOfRightInverse_comp_apply π (Function.surjInv hπ)
      (Function.rightInverse_surjInv hπ) ⟨f₀, s26_center_le_ker_descentHom ψ hψ π hπk hv⟩ s
  have h₁ : ∀ s, φ₁ (π s) = π (s26_conjPre ψ hvi s) := fun s =>
    MonoidHom.liftOfRightInverse_comp_apply π (Function.surjInv hπ)
      (Function.rightInverse_surjInv hπ) ⟨f₁, s26_center_le_ker_descentHom ψ hψ π hπk hvi⟩ s
  have key : ∀ s t : S, ψ s = ψ t → π s = π t := fun s t h => by
    have : s * t⁻¹ ∈ ψ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
    have h2 : π (s * t⁻¹) = 1 := by rw [← MonoidHom.mem_ker, hπk]; exact hψ this
    rwa [map_mul, map_inv, mul_inv_eq_one] at h2
  have hcomp : ∀ s, φ₀ (φ₁ (π s)) = π s := by
    intro s
    rw [h₁, h₀]
    apply key
    rw [s26_psi_conjPre, s26_psi_conjPre]
    group
  have hcomp' : ∀ s, φ₁ (φ₀ (π s)) = π s := by
    intro s
    rw [h₀, h₁]
    apply key
    rw [s26_psi_conjPre, s26_psi_conjPre]
    group
  refine ⟨MonoidHom.toMulEquiv φ₀ φ₁ ?_ ?_, fun s s' hs => ?_⟩
  · ext x
    obtain ⟨s, rfl⟩ := hπ x
    exact hcomp' s
  · ext x
    obtain ⟨s, rfl⟩ := hπ x
    exact hcomp s
  · show φ₀ (π s) = π s'
    rw [h₀]
    apply key
    rw [s26_psi_conjPre, hs]

theorem s26_commutes_of_descent_trivial_core [Group.IsPerfect S] (ψ : S →* H) (π : S →* P)
    (hπk : π.ker = Subgroup.center S) {v : H}
    (hv : v ∈ Subgroup.normalizer (ψ.range : Set H))
    (h : ∀ s s' : S, v * ψ s * v⁻¹ = ψ s' → π s' = π s) :
    ∀ y ∈ ψ.range, v * y = y * v := by
  have hκ : ∀ s : S, ∃ c ∈ Subgroup.center S, v * ψ s * v⁻¹ * (ψ s)⁻¹ = ψ c := by
    intro s
    refine ⟨s26_conjPre ψ hv s * s⁻¹, ?_, ?_⟩
    · rw [← hπk, MonoidHom.mem_ker, map_mul, map_inv,
        h s _ (s26_psi_conjPre ψ hv s).symm, mul_inv_cancel]
    · rw [map_mul, map_inv, s26_psi_conjPre]
  have hcen : ∀ s u : S, ψ u * (v * ψ s * v⁻¹ * (ψ s)⁻¹) =
      (v * ψ s * v⁻¹ * (ψ s)⁻¹) * ψ u := by
    intro s u
    obtain ⟨c, hc, hcs⟩ := hκ s
    rw [hcs, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc u]
  let κ : S →* H := MonoidHom.mk' (fun s => v * ψ s * v⁻¹ * (ψ s)⁻¹) fun s t => by
    have e1 : (ψ s)⁻¹ * (v * ψ t * v⁻¹ * (ψ t)⁻¹) = (v * ψ t * v⁻¹ * (ψ t)⁻¹) * (ψ s)⁻¹ := by
      calc (ψ s)⁻¹ * (v * ψ t * v⁻¹ * (ψ t)⁻¹)
          = (ψ s)⁻¹ * (v * ψ t * v⁻¹ * (ψ t)⁻¹) * ψ s * (ψ s)⁻¹ := by group
        _ = (ψ s)⁻¹ * (ψ s * (v * ψ t * v⁻¹ * (ψ t)⁻¹)) * (ψ s)⁻¹ := by
          rw [hcen t s]; group
        _ = (v * ψ t * v⁻¹ * (ψ t)⁻¹) * (ψ s)⁻¹ := by group
    calc v * ψ (s * t) * v⁻¹ * (ψ (s * t))⁻¹
        = (v * ψ s * v⁻¹) * ((v * ψ t * v⁻¹ * (ψ t)⁻¹) * (ψ s)⁻¹) := by
          rw [map_mul]; group
      _ = (v * ψ s * v⁻¹) * ((ψ s)⁻¹ * (v * ψ t * v⁻¹ * (ψ t)⁻¹)) := by rw [e1]
      _ = (v * ψ s * v⁻¹ * (ψ s)⁻¹) * (v * ψ t * v⁻¹ * (ψ t)⁻¹) := by group
  have hperf : Group.IsPerfect κ.range := Group.IsPerfect.range κ
  have hcomm : ∀ a b : κ.range, a * b = b * a := by
    rintro ⟨_, s, rfl⟩ ⟨_, t, rfl⟩
    obtain ⟨c, hc, hcs⟩ := hκ s
    obtain ⟨d, hd, hdt⟩ := hκ t
    apply Subtype.ext
    show κ s * κ t = κ t * κ s
    have e : ∀ x : S, κ x = v * ψ x * v⁻¹ * (ψ x)⁻¹ := fun x => rfl
    rw [e, e, hcs, hdt, ← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hc d)]
  have : IsMulCommutative κ.range := ⟨⟨hcomm⟩⟩
  have hs : Subsingleton κ.range := Group.IsPerfect.subsingleton_of_isMulCommutative
  intro y hy
  obtain ⟨s, rfl⟩ := hy
  have h1 : (⟨κ s, s, rfl⟩ : κ.range) = 1 := Subsingleton.elim _ _
  have h2 : v * ψ s * v⁻¹ * (ψ s)⁻¹ = 1 := congrArg Subtype.val h1
  calc v * ψ s = (v * ψ s * v⁻¹ * (ψ s)⁻¹) * ψ s * v := by group
    _ = ψ s * v := by rw [h2, one_mul]

end DescentCore

section Descent

variable {S Y P : Type} [Group S] [Group Y] [Group P]

@[expose] def S26IsDescent (ψ : S →* Y) (π : S →* P) (γ : MulAut Y) (φ : MulAut P) : Prop :=
  ∀ s s' : S, γ (ψ s) = ψ s' → φ (π s) = π s'

@[expose] def s26LeftReg (ψ : S →* Y) : S →* Equiv.Perm Y :=
  MonoidHom.mk' (fun s => Equiv.mulLeft (ψ s)) fun a b => by
    ext y
    simp

theorem s26LeftReg_apply (ψ : S →* Y) (s : S) (y : Y) : s26LeftReg ψ s y = ψ s * y := rfl

variable {ψ : S →* Y} {π : S →* P}

theorem s26LeftReg_conj (γ : MulAut Y) {s s' : S} (h : γ (ψ s) = ψ s') :
    γ.toEquiv * s26LeftReg ψ s * γ.toEquiv⁻¹ = s26LeftReg ψ s' := by
  ext y
  have e1 : (γ.toEquiv * s26LeftReg ψ s * γ.toEquiv⁻¹) y = γ (ψ s * γ⁻¹ y) := rfl
  have e2 : γ (γ⁻¹ y) = y := γ.apply_symm_apply y
  rw [e1, map_mul, h, e2, s26LeftReg_apply]

theorem s26LeftReg_normalizer (hψ : Function.Surjective ψ) (γ : MulAut Y) :
    γ.toEquiv ∈ Subgroup.normalizer ((s26LeftReg ψ).range : Set (Equiv.Perm Y)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨s', hs'⟩ := hψ (γ (ψ s))
    exact ⟨s', (s26LeftReg_conj γ hs'.symm).symm⟩
  · rintro ⟨s', hs'⟩
    obtain ⟨s'', hs''⟩ := hψ (γ⁻¹ (ψ s'))
    refine ⟨s'', ?_⟩
    have e : γ.toEquiv * s26LeftReg ψ s'' * γ.toEquiv⁻¹ = s26LeftReg ψ s' :=
      s26LeftReg_conj γ (by rw [hs'']; exact γ.apply_symm_apply _)
    have e' : γ.toEquiv * s26LeftReg ψ s'' * γ.toEquiv⁻¹ = γ.toEquiv * h * γ.toEquiv⁻¹ := by
      rw [e]
      exact hs'
    exact mul_right_cancel (mul_left_cancel e')

theorem s26LeftReg_ker_le (hker : ψ.ker ≤ Subgroup.center S) :
    (s26LeftReg ψ).ker ≤ Subgroup.center S := by
  intro s hs
  apply hker
  rw [MonoidHom.mem_ker] at hs ⊢
  have := congrArg (fun σ : Equiv.Perm Y => σ 1) hs
  simpa [s26LeftReg_apply] using this

theorem S26IsDescent.one (hk : ψ.ker ≤ π.ker) : S26IsDescent ψ π 1 1 := by
  intro s s' h
  have h1 : ψ s = ψ s' := h
  have h2 : s' * s⁻¹ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
  have h3 := hk h2
  rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at h3
  exact h3.symm

theorem S26IsDescent.mul (hψ : Function.Surjective ψ) {γ₁ γ₂ : MulAut Y} {φ₁ φ₂ : MulAut P}
    (h₁ : S26IsDescent ψ π γ₁ φ₁) (h₂ : S26IsDescent ψ π γ₂ φ₂) :
    S26IsDescent ψ π (γ₁ * γ₂) (φ₁ * φ₂) := by
  intro s s' h
  obtain ⟨s₂, hs₂⟩ := hψ (γ₂ (ψ s))
  have e₂ : φ₂ (π s) = π s₂ := h₂ s s₂ hs₂.symm
  have e₁ : φ₁ (π s₂) = π s' := h₁ s₂ s' (by rw [hs₂]; exact h)
  rw [MulAut.mul_apply, e₂, e₁]

theorem S26IsDescent.inv {γ : MulAut Y} {φ : MulAut P} (h : S26IsDescent ψ π γ φ) :
    S26IsDescent ψ π γ⁻¹ φ⁻¹ := by
  intro s s' hs
  have h1 : γ (ψ s') = ψ s := by
    rw [← hs]
    exact γ.apply_symm_apply (ψ s)
  have h2 : φ (π s') = π s := h s' s h1
  rw [← h2]
  exact φ.symm_apply_apply (π s')

theorem S26IsDescent.pow (hψ : Function.Surjective ψ) (hk : ψ.ker ≤ π.ker) {γ : MulAut Y}
    {φ : MulAut P} (h : S26IsDescent ψ π γ φ) (k : ℕ) : S26IsDescent ψ π (γ ^ k) (φ ^ k) := by
  induction k with
  | zero => simpa using S26IsDescent.one hk
  | succ k ih => simpa [pow_succ] using ih.mul hψ h

theorem S26IsDescent.conj (hk : ψ.ker ≤ π.ker) (x : S) :
    S26IsDescent ψ π (MulAut.conj (ψ x)) (MulAut.conj (π x)) := by
  intro s s' h
  have h1 : ψ x * ψ s * (ψ x)⁻¹ = ψ s' := by simpa using h
  have h2 : ψ (x * s * x⁻¹) = ψ s' := by rw [map_mul, map_mul, map_inv, h1]
  have h3 : s' * (x * s * x⁻¹)⁻¹ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h2, mul_inv_cancel]
  have h4 := hk h3
  rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at h4
  rw [h4]
  simp [map_mul, map_inv]

theorem s26_exists_isDescent [Group.IsPerfect S] (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center S) (hπ : Function.Surjective π)
    (hπk : π.ker = Subgroup.center S) (γ : MulAut Y) : ∃ φ : MulAut P, S26IsDescent ψ π γ φ := by
  obtain ⟨φ, hφ⟩ := s26_exists_descent_core (s26LeftReg ψ) (s26LeftReg_ker_le hker) π hπ hπk
    (s26LeftReg_normalizer hψ γ)
  exact ⟨φ, fun s s' h => hφ s s' (s26LeftReg_conj γ h)⟩

theorem s26_eq_one_of_isDescent_one [Group.IsPerfect S] (hψ : Function.Surjective ψ)
    (hπk : π.ker = Subgroup.center S) {γ : MulAut Y} (h : S26IsDescent ψ π γ 1) : γ = 1 := by
  have hdesc : ∀ s s' : S, γ.toEquiv * s26LeftReg ψ s * γ.toEquiv⁻¹ = s26LeftReg ψ s' →
      π s' = π s := by
    intro s s' hs
    have h1 : γ (ψ s) = ψ s' := by
      have := congrArg (fun σ : Equiv.Perm Y => σ 1) hs
      have e1 : (γ.toEquiv * s26LeftReg ψ s * γ.toEquiv⁻¹) 1 = γ (ψ s * γ⁻¹ 1) := rfl
      simp only [e1, s26LeftReg_apply, map_one, mul_one] at this
      exact this
    exact (h s s' h1).symm
  have hcomm := s26_commutes_of_descent_trivial_core (s26LeftReg ψ) π hπk
    (s26LeftReg_normalizer hψ γ) hdesc
  ext y
  obtain ⟨s, rfl⟩ := hψ y
  have h2 := congrArg (fun σ : Equiv.Perm Y => σ 1) (hcomm (s26LeftReg ψ s) ⟨s, rfl⟩)
  simpa [s26LeftReg_apply] using h2

end Descent

end CFSG.ClassicalInvolution.Asc77
