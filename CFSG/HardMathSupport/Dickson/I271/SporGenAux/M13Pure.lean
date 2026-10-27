module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.M13Act

public section

namespace CFSG.HardMathSupport.Dickson.I271.M13

open CFSG.HardMathSupport.Dickson.I271

variable {G : Type*} [Group G]

structure PureData (g d c x₁ x₂ y₁ y₂ y₄ : G) : Prop where
  plane : PlaneData d c
  hc1 : c ≠ 1
  gc : g * c * g⁻¹ = c
  gd : g * d * g⁻¹ = d * c ^ 9
  y1c : y₁ * c * y₁⁻¹ = c ^ 12
  y1d : y₁ * d * y₁⁻¹ = d ^ 12 * c ^ 12
  y2c : y₂ * c * y₂⁻¹ = d ^ 12
  y2d : y₂ * d * y₂⁻¹ = c
  y4c : y₄ * c * y₄⁻¹ = c ^ 12
  y4d : y₄ * d * y₄⁻¹ = d ^ 8 * c ^ 10
  x1c : x₁ * c * x₁⁻¹ = c ^ 6
  x2c : x₂ * c * x₂⁻¹ = c

namespace PureData

@[expose] def H (d c : G) : Subgroup G :=
  Subgroup.closure (centSet (Subgroup.closure ({d, c} : Set G)))

theorem hdA (d c : G) : d ∈ Subgroup.closure ({d, c} : Set G) := Subgroup.subset_closure (by simp)

theorem hcA (d c : G) : c ∈ Subgroup.closure ({d, c} : Set G) := Subgroup.subset_closure (by simp)

variable {g d c x₁ x₂ y₁ y₂ y₄ : G} (D : PureData g d c x₁ x₂ y₁ y₂ y₄)

include D

theorem actG : Act d c g 1 9 0 1 := ⟨by rw [D.gd, pow_one], by rw [D.gc]; simp⟩

theorem actY1 : Act d c y₁ 12 12 0 12 := ⟨D.y1d, by rw [D.y1c]; simp⟩

theorem actY2 : Act d c y₂ 0 1 12 0 := ⟨by rw [D.y2d]; simp, by rw [D.y2c]; simp⟩

theorem actY4 : Act d c y₄ 8 10 0 12 := ⟨D.y4d, by rw [D.y4c]; simp⟩

theorem actGi : Act d c g⁻¹ 1 4 0 1 :=
  Act.inv D.plane D.actG (by decide) (by decide) (by decide) (by decide)

theorem actY1i : Act d c y₁⁻¹ 12 1 0 12 :=
  Act.inv D.plane D.actY1 (by decide) (by decide) (by decide) (by decide)

theorem actY2i : Act d c y₂⁻¹ 0 12 1 0 :=
  Act.inv D.plane D.actY2 (by decide) (by decide) (by decide) (by decide)

theorem actY4i : Act d c y₄⁻¹ 5 11 0 12 :=
  Act.inv D.plane D.actY4 (by decide) (by decide) (by decide) (by decide)

theorem fixer {n : G} {p q r s : ℕ} (h : Act d c n p q r s) (j k : ℕ)
    (hj : (p * j + r * k) % 13 = j % 13) (hk : (q * j + s * k) % 13 = k % 13)
    (hne : ¬ (j % 13 = 0 ∧ k % 13 = 0)) : n ∈ H d c :=
  Subgroup.subset_closure (Act.mem_centSet D.plane (hdA d c) (hcA d c) h j k hj hk hne)

theorem g_mem : g ∈ H d c :=
  Subgroup.subset_closure ⟨c, hcA d c, D.hc1, by rw [← mul_inv_eq_iff_eq_mul]; exact D.gc⟩

theorem x2_mem : x₂ ∈ H d c :=
  Subgroup.subset_closure ⟨c, hcA d c, D.hc1, by rw [← mul_inv_eq_iff_eq_mul]; exact D.x2c⟩

theorem c_mem : c ∈ H d c :=
  Subgroup.subset_closure ⟨c, hcA d c, D.hc1, rfl⟩

theorem d_mem : d ∈ H d c :=
  Subgroup.subset_closure ⟨c, hcA d c, D.hc1, D.plane.comm.eq⟩

theorem y1_mem : y₁ ∈ H d c := by
  have h1 : y₄ * y₄ ∈ H d c :=
    D.fixer (Act.mul D.plane D.actY4 D.actY4) 0 1 (by decide) (by decide) (by decide)
  have h2 : y₄⁻¹ * y₄⁻¹ * y₁ ∈ H d c :=
    D.fixer (Act.mul D.plane (Act.mul D.plane D.actY4i D.actY4i) D.actY1) 1 10 (by decide)
      (by decide) (by decide)
  have e : y₁ = (y₄ * y₄) * (y₄⁻¹ * y₄⁻¹ * y₁) := by group
  rw [e]
  exact Subgroup.mul_mem _ h1 h2

theorem y2_mem : y₂ ∈ H d c := by
  have h1 : y₁ * y₁ ∈ H d c :=
    D.fixer (Act.mul D.plane D.actY1 D.actY1) 0 1 (by decide) (by decide) (by decide)
  have h2 : y₁⁻¹ * y₁⁻¹ * y₂ ∈ H d c :=
    D.fixer (Act.mul D.plane (Act.mul D.plane D.actY1i D.actY1i) D.actY2) 1 12 (by decide)
      (by decide) (by decide)
  have e : y₂ = (y₁ * y₁) * (y₁⁻¹ * y₁⁻¹ * y₂) := by group
  rw [e]
  exact Subgroup.mul_mem _ h1 h2

theorem y4_mem : y₄ ∈ H d c := by
  have h1 : y₄⁻¹ * y₁ ∈ H d c :=
    D.fixer (Act.mul D.plane D.actY4i D.actY1) 0 1 (by decide) (by decide) (by decide)
  have h2 : y₁⁻¹ * y₄ * y₄ ∈ H d c :=
    D.fixer (Act.mul D.plane (Act.mul D.plane D.actY1i D.actY4) D.actY4) 1 10 (by decide)
      (by decide) (by decide)
  have e : y₄ = (y₄⁻¹ * y₁) * (y₁⁻¹ * y₄ * y₄) := by group
  rw [e]
  exact Subgroup.mul_mem _ h1 h2

theorem x1_mem : x₁ ∈ H d c := by
  have h1 : g⁻¹ * y₂⁻¹ * y₄ ∈ H d c :=
    D.fixer (Act.mul D.plane (Act.mul D.plane D.actGi D.actY2i) D.actY4) 1 9 (by decide)
      (by decide) (by decide)
  have h2 : y₂ * g * y₂⁻¹ * y₄⁻¹ ∈ H d c :=
    D.fixer (Act.mul D.plane (Act.mul D.plane (Act.mul D.plane D.actY2 D.actG) D.actY2i) D.actY4i)
      1 12 (by decide) (by decide) (by decide)
  have hz := Act.mul D.plane (Act.mul D.plane (Act.mul D.plane D.actGi D.actY2i) D.actY4)
    (Act.mul D.plane (Act.mul D.plane (Act.mul D.plane D.actY2 D.actG) D.actY2i) D.actY4i)
  have h3 : (g⁻¹ * y₂⁻¹ * y₄ * (y₂ * g * y₂⁻¹ * y₄⁻¹))⁻¹ * x₁ ∈ H d c :=
    Subgroup.subset_closure (Act.inv_mul_mem_centSet D.plane (hcA d c) D.hc1 (r := 0) (s := 6)
      (by rw [D.x1c]; simp) hz (by decide) (by decide))
  have e : x₁ = (g⁻¹ * y₂⁻¹ * y₄ * (y₂ * g * y₂⁻¹ * y₄⁻¹)) *
      ((g⁻¹ * y₂⁻¹ * y₄ * (y₂ * g * y₂⁻¹ * y₄⁻¹))⁻¹ * x₁) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) h3

end PureData

end CFSG.HardMathSupport.Dickson.I271.M13
