module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.BaseEmb

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup

private theorem coord_cases (q : Multiplicative (ZMod 2)) :
    q = 1 ∨ q = Multiplicative.ofAdd 1 := by
  rcases (show ∀ e : ZMod 2, e = 0 ∨ e = 1 by decide) (Multiplicative.toAdd q) with h | h
  · left
    rw [← ofAdd_toAdd q, h]
    rfl
  · right
    rw [← ofAdd_toAdd q, h]

private theorem ofAdd_one_ne_one :
    (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2)) ≠ 1 := by
  decide

private theorem sigmaC2_mul_self :
    (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd (1 : ZMod 2) = 1 := by
  decide

theorem A5WrTwo.exists_conj_baseEmb {u : A5WrTwo} (hu : u ∉ commutator A5WrTwo) (hu2 : u ^ 2 = 1) :
    ∃ x₀ : alternatingGroup (Fin 5), ∀ x y : alternatingGroup (Fin 5),
      u * A5WrTwo.baseEmb (x, y) * u⁻¹ = A5WrTwo.baseEmb (x₀ * y * x₀⁻¹, x₀⁻¹ * x * x₀) := by
  have hu_ne : u.right ≠ 1 := by
    intro h
    exact hu (by rw [A5WrTwo.commutator_eq_ker]; exact h)
  have hur : u.right = Multiplicative.ofAdd (1 : ZMod 2) := by
    rcases coord_cases u.right with h | h
    · exact absurd h hu_ne
    · exact h
  let s : A5WrTwo := ⟨1, Multiplicative.ofAdd 1⟩
  let b : A5WrTwo := ⟨u.left, 1⟩
  have hs2 : s * s = 1 := by
    apply RegularWreathProduct.ext
    · funext q
      simp [s, RegularWreathProduct.mul_def]
    · simp [s, RegularWreathProduct.mul_def, sigmaC2_mul_self]
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hswap : ∀ x y, s * A5WrTwo.baseEmb (x, y) * s⁻¹ = A5WrTwo.baseEmb (y, x) := by
    intro x y
    simpa [s] using A5WrTwo.swap_mul_baseEmb_mul_inv x y
  have hub : u = b * s := by
    apply RegularWreathProduct.ext
    · funext q
      simp [b, s]
    · simp [b, s, hur]
  have hb_range : b ∈ A5WrTwo.baseEmb.range := by
    rw [A5WrTwo.range_baseEmb, A5WrTwo.commutator_eq_ker]
    exact MonoidHom.mem_ker.mpr rfl
  obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hb_range
  have hp_pair : A5WrTwo.baseEmb (p.1, p.2) = b := by simpa using hp
  have hsbs : s * b * s = b⁻¹ := by
    have h : (b * s) * (b * s) = 1 := by
      rw [← hub]
      simpa [pow_two] using hu2
    have h2 : b * (s * b * s) = 1 := by simpa only [mul_assoc] using h
    exact eq_inv_of_mul_eq_one_right h2
  have hb_inv : b⁻¹ = A5WrTwo.baseEmb (p.1⁻¹, p.2⁻¹) := by
    rw [← hp, ← map_inv]
    rfl
  have hp2 : p.2 = p.1⁻¹ := by
    have h1 : s * b * s = A5WrTwo.baseEmb (p.2, p.1) := by
      have h := hswap p.1 p.2
      rw [hp_pair] at h
      rwa [hsinv] at h
    have h3 : A5WrTwo.baseEmb (p.2, p.1) = A5WrTwo.baseEmb (p.1⁻¹, p.2⁻¹) := by
      rw [← h1, hsbs, hb_inv]
    exact congrArg Prod.fst (A5WrTwo.baseEmb_injective h3)
  refine ⟨p.1, ?_⟩
  intro x y
  calc u * A5WrTwo.baseEmb (x, y) * u⁻¹
      = (b * s) * A5WrTwo.baseEmb (x, y) * (b * s)⁻¹ := by rw [hub]
    _ = b * (s * A5WrTwo.baseEmb (x, y) * s⁻¹) * b⁻¹ := by group
    _ = b * A5WrTwo.baseEmb (y, x) * b⁻¹ := by rw [hswap x y]
    _ = A5WrTwo.baseEmb p * A5WrTwo.baseEmb (y, x) * A5WrTwo.baseEmb p⁻¹ := by
          rw [← hp, ← map_inv]
    _ = A5WrTwo.baseEmb (p * (y, x) * p⁻¹) := by rw [← map_mul, ← map_mul]
    _ = A5WrTwo.baseEmb (p.1 * y * p.1⁻¹, p.1⁻¹ * x * p.1) := by
          apply congrArg A5WrTwo.baseEmb
          ext <;> simp [Prod.mk_mul_mk, hp2]

theorem eq_top_of_diag_mem (x₀ : alternatingGroup (Fin 5))
    (K : Subgroup (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)))
    (hD : ∀ y : alternatingGroup (Fin 5), (x₀ * y * x₀⁻¹, y) ∈ K)
    (h1 : ∃ x : alternatingGroup (Fin 5), x ≠ 1 ∧ (x, 1) ∈ K)
    (h2 : ∃ y : alternatingGroup (Fin 5), y ≠ 1 ∧ (1, y) ∈ K) : K = ⊤ := by
  let K₁ : Subgroup (alternatingGroup (Fin 5)) :=
    K.comap (MonoidHom.inl (alternatingGroup (Fin 5)) (alternatingGroup (Fin 5)))
  let K₂ : Subgroup (alternatingGroup (Fin 5)) :=
    K.comap (MonoidHom.inr (alternatingGroup (Fin 5)) (alternatingGroup (Fin 5)))
  have hK₁normal : K₁.Normal :=
    ⟨fun x hx h => by
      have hxK : (x, 1) ∈ K := by simpa [K₁, MonoidHom.inl_apply] using hx
      have hdK : (x₀ * (x₀⁻¹ * h * x₀) * x₀⁻¹, x₀⁻¹ * h * x₀) ∈ K := hD (x₀⁻¹ * h * x₀)
      have hg : x₀ * (x₀⁻¹ * h * x₀) * x₀⁻¹ = h := by group
      have hconj : (x₀ * (x₀⁻¹ * h * x₀) * x₀⁻¹, x₀⁻¹ * h * x₀) * (x, 1) *
          (x₀ * (x₀⁻¹ * h * x₀) * x₀⁻¹, x₀⁻¹ * h * x₀)⁻¹ = (h * x * h⁻¹, 1) := by
        simp [Prod.mk_mul_mk, hg]
      have hmem : (x₀ * (x₀⁻¹ * h * x₀) * x₀⁻¹, x₀⁻¹ * h * x₀) * (x, 1) *
          (x₀ * (x₀⁻¹ * h * x₀) * x₀⁻¹, x₀⁻¹ * h * x₀)⁻¹ ∈ K :=
        K.mul_mem (K.mul_mem hdK hxK) (K.inv_mem hdK)
      rw [hconj] at hmem
      simpa [K₁, MonoidHom.inl_apply] using hmem⟩
  have hK₂normal : K₂.Normal :=
    ⟨fun y hy g => by
      have hyK : (1, y) ∈ K := by simpa [K₂, MonoidHom.inr_apply] using hy
      have hdK : (x₀ * g * x₀⁻¹, g) ∈ K := hD g
      have hconj : (x₀ * g * x₀⁻¹, g) * (1, y) * (x₀ * g * x₀⁻¹, g)⁻¹ = (1, g * y * g⁻¹) := by
        simp [Prod.mk_mul_mk]
      have hmem : (x₀ * g * x₀⁻¹, g) * (1, y) * (x₀ * g * x₀⁻¹, g)⁻¹ ∈ K :=
        K.mul_mem (K.mul_mem hdK hyK) (K.inv_mem hdK)
      rw [hconj] at hmem
      simpa [K₂, MonoidHom.inr_apply] using hmem⟩
  have hK₁ne : K₁ ≠ ⊥ := by
    obtain ⟨x, hxne, hxK⟩ := h1
    intro hbot
    have : x ∈ K₁ := by simpa [K₁, MonoidHom.inl_apply] using hxK
    rw [hbot] at this
    exact hxne (by simpa using this)
  have hK₂ne : K₂ ≠ ⊥ := by
    obtain ⟨y, hyne, hyK⟩ := h2
    intro hbot
    have : y ∈ K₂ := by simpa [K₂, MonoidHom.inr_apply] using hyK
    rw [hbot] at this
    exact hyne (by simpa using this)
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hK₁top : K₁ = ⊤ := by
    haveI := hK₁normal
    exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal K₁).resolve_left hK₁ne
  have hK₂top : K₂ = ⊤ := by
    haveI := hK₂normal
    exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal K₂).resolve_left hK₂ne
  rw [Subgroup.eq_top_iff']
  intro p
  obtain ⟨a, b⟩ := p
  have ha : a ∈ K₁ := by rw [hK₁top]; exact Subgroup.mem_top a
  have hb : b ∈ K₂ := by rw [hK₂top]; exact Subgroup.mem_top b
  have haK : (a, 1) ∈ K := by simpa [K₁, MonoidHom.inl_apply] using ha
  have hbK : (1, b) ∈ K := by simpa [K₂, MonoidHom.inr_apply] using hb
  have hmem : (a, 1) * (1, b) ∈ K := K.mul_mem haK hbK
  simpa using hmem

end CFSG.EvenSporadicStandard.HNRecog