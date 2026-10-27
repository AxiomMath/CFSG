module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameAlpha

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

open CFSG.ClassicalInvolution.Asc77.FrameVertex
open scoped commutatorElement

section Descent

variable {S H P : Type} [Group S] [Group H] [Group P]

private noncomputable def conjPre (ψ : S →* H) {v : H}
    (hv : v ∈ Subgroup.normalizer (ψ.range : Set H)) (s : S) : S :=
  Classical.choose ((Subgroup.mem_normalizer_iff.mp hv (ψ s)).mp ⟨s, rfl⟩)

private theorem psi_conjPre (ψ : S →* H) {v : H}
    (hv : v ∈ Subgroup.normalizer (ψ.range : Set H)) (s : S) :
    ψ (conjPre ψ hv s) = v * ψ s * v⁻¹ :=
  Classical.choose_spec ((Subgroup.mem_normalizer_iff.mp hv (ψ s)).mp ⟨s, rfl⟩)

private theorem conjPre_mul_mem_ker (ψ : S →* H) {v : H}
    (hv : v ∈ Subgroup.normalizer (ψ.range : Set H)) (s t : S) :
    conjPre ψ hv (s * t) * (conjPre ψ hv s * conjPre ψ hv t)⁻¹ ∈ ψ.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, psi_conjPre, psi_conjPre, psi_conjPre,
    map_mul]
  group

private noncomputable def descentHom (ψ : S →* H) (hψ : ψ.ker ≤ Subgroup.center S) (π : S →* P)
    (hπk : π.ker = Subgroup.center S) {v : H}
    (hv : v ∈ Subgroup.normalizer (ψ.range : Set H)) : S →* P :=
  MonoidHom.mk' (fun s => π (conjPre ψ hv s)) fun s t => by
    have h := conjPre_mul_mem_ker ψ hv s t
    have h1 : π (conjPre ψ hv (s * t) * (conjPre ψ hv s * conjPre ψ hv t)⁻¹) = 1 := by
      rw [← MonoidHom.mem_ker, hπk]
      exact hψ h
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    rw [h1, map_mul]

private theorem center_le_ker_descentHom [Group.IsPerfect S] (ψ : S →* H)
    (hψ : ψ.ker ≤ Subgroup.center S) (π : S →* P) (hπk : π.ker = Subgroup.center S) {v : H}
    (hv : v ∈ Subgroup.normalizer (ψ.range : Set H)) :
    π.ker ≤ (descentHom ψ hψ π hπk hv).ker := by
  intro s hs
  rw [hπk] at hs
  rw [MonoidHom.mem_ker]
  show π (conjPre ψ hv s) = 1
  rw [← MonoidHom.mem_ker, hπk]
  refine mem_center_of_commutators_central (S := S) fun t => ?_
  apply hψ
  rw [MonoidHom.mem_ker, map_commutatorElement, psi_conjPre]
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

theorem exists_descent [Group.IsPerfect S] (ψ : S →* H) (hψ : ψ.ker ≤ Subgroup.center S)
    (π : S →* P) (hπ : Function.Surjective π) (hπk : π.ker = Subgroup.center S) {v : H}
    (hv : v ∈ Subgroup.normalizer (ψ.range : Set H)) :
    ∃ φ : P ≃* P, ∀ s s' : S, v * ψ s * v⁻¹ = ψ s' → φ (π s) = π s' := by
  have hvi : v⁻¹ ∈ Subgroup.normalizer (ψ.range : Set H) := Subgroup.inv_mem _ hv
  let f₀ : S →* P := descentHom ψ hψ π hπk hv
  let f₁ : S →* P := descentHom ψ hψ π hπk hvi
  let φ₀ : P →* P := MonoidHom.liftOfSurjective π hπ ⟨f₀, center_le_ker_descentHom ψ hψ π hπk hv⟩
  let φ₁ : P →* P := MonoidHom.liftOfSurjective π hπ ⟨f₁, center_le_ker_descentHom ψ hψ π hπk hvi⟩
  have h₀ : ∀ s, φ₀ (π s) = π (conjPre ψ hv s) := fun s =>
    MonoidHom.liftOfRightInverse_comp_apply π (Function.surjInv hπ)
      (Function.rightInverse_surjInv hπ) ⟨f₀, center_le_ker_descentHom ψ hψ π hπk hv⟩ s
  have h₁ : ∀ s, φ₁ (π s) = π (conjPre ψ hvi s) := fun s =>
    MonoidHom.liftOfRightInverse_comp_apply π (Function.surjInv hπ)
      (Function.rightInverse_surjInv hπ) ⟨f₁, center_le_ker_descentHom ψ hψ π hπk hvi⟩ s
  have key : ∀ s t : S, ψ s = ψ t → π s = π t := fun s t h => by
    have : s * t⁻¹ ∈ ψ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
    have h2 : π (s * t⁻¹) = 1 := by rw [← MonoidHom.mem_ker, hπk]; exact hψ this
    rwa [map_mul, map_inv, mul_inv_eq_one] at h2
  have hcomp : ∀ s, φ₀ (φ₁ (π s)) = π s := by
    intro s
    rw [h₁, h₀]
    apply key
    rw [psi_conjPre, psi_conjPre]
    group
  have hcomp' : ∀ s, φ₁ (φ₀ (π s)) = π s := by
    intro s
    rw [h₀, h₁]
    apply key
    rw [psi_conjPre, psi_conjPre]
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
    rw [psi_conjPre, hs]

theorem commutes_of_descent_trivial [Group.IsPerfect S] (ψ : S →* H) (π : S →* P)
    (hπk : π.ker = Subgroup.center S) {v : H}
    (hv : v ∈ Subgroup.normalizer (ψ.range : Set H))
    (h : ∀ s s' : S, v * ψ s * v⁻¹ = ψ s' → π s' = π s) :
    ∀ y ∈ ψ.range, v * y = y * v := by
  have hκ : ∀ s : S, ∃ c ∈ Subgroup.center S, v * ψ s * v⁻¹ * (ψ s)⁻¹ = ψ c := by
    intro s
    refine ⟨conjPre ψ hv s * s⁻¹, ?_, ?_⟩
    · rw [← hπk, MonoidHom.mem_ker, map_mul, map_inv,
        h s _ (psi_conjPre ψ hv s).symm, mul_inv_cancel]
    · rw [map_mul, map_inv, psi_conjPre]
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

end Descent

end CFSG.ClassicalInvolution.ModelFacts.Orth15
