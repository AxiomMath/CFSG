module

public import CFSG.Goldschmidt.StrongClosure

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def rconj (g : G) (U : Set G) : Set G := (MulAut.conj g⁻¹) '' U

theorem mem_rconj {g x : G} {U : Set G} : x ∈ rconj g U ↔ g * x * g⁻¹ ∈ U := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa [mul_assoc] using hu
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [mul_assoc]⟩

theorem conj_mem_rconj {g u : G} {U : Set G} (hu : u ∈ U) : g⁻¹ * u * g ∈ rconj g U :=
  mem_rconj.2 (by simpa [mul_assoc] using hu)

@[simp] theorem rconj_one (U : Set G) : rconj 1 U = U := by
  ext x
  simp [mem_rconj]

theorem rconj_mul (g h : G) (U : Set G) : rconj (g * h) U = rconj h (rconj g U) := by
  ext x
  simp only [mem_rconj, mul_inv_rev]
  constructor <;> intro hx <;> simpa [mul_assoc] using hx

theorem rconj_inv_rconj (g : G) (U : Set G) : rconj g⁻¹ (rconj g U) = U := by
  rw [← rconj_mul, mul_inv_cancel, rconj_one]

theorem rconj_rconj_inv (g : G) (U : Set G) : rconj g (rconj g⁻¹ U) = U := by
  rw [← rconj_mul, inv_mul_cancel, rconj_one]

theorem rconj_mono {g : G} {U V : Set G} (h : U ⊆ V) : rconj g U ⊆ rconj g V :=
  Set.image_mono h

theorem rconj_mul_set (g : G) (U V : Set G) : rconj g (U * V) = rconj g U * rconj g V :=
  Set.image_mul (MulAut.conj g⁻¹)

theorem coe_conjSub (g : G) (A : Subgroup G) : ((conjSub g A : Subgroup G) : Set G) =
    rconj g (A : Set G) := by
  ext x
  simp [mem_rconj, mem_conjSub]

theorem rconj_eq_of_mem_normalizer {g : G} {A : Subgroup G}
    (hg : g ∈ normalizer (A : Set G)) : rconj g (A : Set G) = A := by
  ext x
  rw [mem_rconj, SetLike.mem_coe, SetLike.mem_coe]
  exact ((mem_normalizer_iff.mp hg) x).symm

theorem conjSub_eq_of_mem_normalizer {g : G} {A : Subgroup G}
    (hg : g ∈ normalizer (A : Set G)) : conjSub g A = A := by
  apply SetLike.coe_injective
  rw [coe_conjSub, rconj_eq_of_mem_normalizer hg]

theorem mem_normalizer_of_conjSub_eq {g : G} {A : Subgroup G} (hg : conjSub g A = A) :
    g ∈ normalizer (A : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : x ∈ conjSub g A := by rw [hg]; exact hx
    exact mem_conjSub.1 this
  · intro hx
    have : g⁻¹ * (g * x * g⁻¹) * g ∈ conjSub g A := conj_mem_conjSub hx
    rw [hg] at this
    simpa [mul_assoc] using this

theorem rconj_subset_of_mem_normalizer {g : G} {A : Subgroup G} {U : Set G}
    (hg : g ∈ normalizer (A : Set G)) (hU : U ⊆ A) : rconj g U ⊆ A := by
  rw [← rconj_eq_of_mem_normalizer hg]
  exact rconj_mono hU

theorem rconj_eq_self_of_mem_centralizer {g : G} {A : Subgroup G} {U : Set G}
    (hg : g ∈ centralizer (A : Set G)) (hU : U ⊆ A) : rconj g U = U := by
  ext x
  rw [mem_rconj]
  constructor
  · intro hx
    have hc := mem_centralizer_iff.mp hg _ (hU hx)
    have h1 : g * x = g * (g * x * g⁻¹) := by
      calc g * x = g * x * g⁻¹ * g := by group
        _ = g * (g * x * g⁻¹) := hc
    have : x = g * x * g⁻¹ := mul_left_cancel h1
    rwa [← this] at hx
  · intro hx
    have hc := mem_centralizer_iff.mp hg x (hU hx)
    have : g * x * g⁻¹ = x := by
      calc g * x * g⁻¹ = x * g * g⁻¹ := by rw [hc]
        _ = x := by group
    rwa [this]

theorem rconj_subset_iff {g : G} {U V : Set G} : rconj g U ⊆ V ↔ U ⊆ rconj g⁻¹ V := by
  constructor
  · intro h x hx
    rw [mem_rconj, inv_inv]
    have := h (conj_mem_rconj (g := g) hx)
    simpa [mul_assoc] using this
  · intro h x hx
    rw [mem_rconj] at hx
    have := h hx
    rw [mem_rconj, inv_inv] at this
    simpa [mul_assoc] using this

theorem image_rconj {H : Type*} [Group H] (f : G →* H) (g : G) (U : Set G) :
    f '' rconj g U = rconj (f g) (f '' U) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_rconj] at hx
    refine mem_rconj.2 ⟨g * x * g⁻¹, hx, by simp [map_mul, map_inv]⟩
  · intro hy
    rw [mem_rconj] at hy
    obtain ⟨u, hu, hfu⟩ := hy
    refine ⟨g⁻¹ * u * g, conj_mem_rconj hu, ?_⟩
    rw [map_mul, map_mul, map_inv, hfu]
    group

end CFSG.Goldschmidt75
