module

public import CFSG.GH74.BNPair.Cells

public section

open scoped Pointwise

namespace CFSG.GH74.BNPair

section Cells

variable {X : Type*} [Group X] {B N : Subgroup X} [(cartan B N).Normal]
  {S : Finset (WeylGroup B N)}

private theorem eq_of_mem_dc (T : IsTitsSystem B N S) {x : X} {w w' : WeylGroup B N}
    (h : x ∈ dc B N w) (h' : x ∈ dc B N w') : w = w' :=
  T.dc_injective (dc_eq_of_mem h h')

private theorem false_of_mem_dc_of_mem_B_or_dc (T : IsTitsSystem B N S) {s t : WeylGroup B N}
    {x : X} (hs : x ∈ dc B N s) (hx : x ∈ B ∨ x ∈ dc B N t) (h₁ : s ≠ 1) (h₂ : s ≠ t) : False :=
  hx.elim (fun h => h₁ (eq_of_mem_dc T hs (mem_dc_one.2 h))) fun h => h₂ (eq_of_mem_dc T hs h)

private theorem false_of_mul_mem_dc (T : IsTitsSystem B N S) {s t : WeylGroup B N} (ht : t ∈ S)
    {a c : X} (ha : a ∈ B ∨ a ∈ dc B N t) (hc : c ∈ B ∨ c ∈ dc B N s)
    (hac : a * c ∈ dc B N (s * t)) (h₁ : s * t ≠ 1) (h₂ : s * t ≠ s) (h₃ : s * t ≠ t)
    (h₄ : s * t ≠ t * s) : False := by
  rcases ha with ha | ha <;> rcases hc with hc | hc
  · exact h₁ (eq_of_mem_dc T hac (mem_dc_one.2 (B.mul_mem ha hc)))
  · exact h₂ (eq_of_mem_dc T hac (mem_dc_of_mem hc ha B.one_mem (mul_one _).symm))
  · exact h₃ (eq_of_mem_dc T hac (mem_dc_of_mem ha B.one_mem hc (by rw [one_mul])))
  · rcases T.bnCore.mul_subset t (Finset.mem_coe.2 ht) s (Set.mul_mem_mul ha hc) with h | h
    · exact h₄ (eq_of_mem_dc T hac h)
    · exact h₂ (eq_of_mem_dc T hac h)

end Cells

namespace RankTwoSystem

section BigCell

variable {X : Type*} [Group X] {n : ℕ} (D : RankTwoSystem X n)

theorem UwMinus_w₀ {m : D.N} (hm : (m : D.Weyl) = D.w₀) : D.UwMinus m = (D.U : Set X) :=
  (D.eq30_5_A le_rfl m hm).1.trans D.roots.carrier_eq.symm

theorem mem_dc_w₀_iff {x : X} :
    x ∈ dc D.B D.N D.w₀ ↔ ∃ b ∈ D.B, ∃ u ∈ D.U, x = b * (D.lift D.w₀ : X) * u := by
  rw [D.mem_dc_iff_coord (D.lift D.w₀) (D.lift_mk D.w₀), D.UwMinus_w₀ (D.lift_mk D.w₀)]
  rfl

end BigCell

section Weyl

variable {X : Type*} [Group X] (D : RankTwoSystem X 3)

private theorem mem_P₁_iff {x : X} : x ∈ D.P₁ ↔ x ∈ D.B ∨ x ∈ dc D.B D.N D.w₁ :=
  mem_parabolic_single_iff D.isTits (D.rank2.gen_mem true)

private theorem mem_P₂_iff {x : X} : x ∈ D.P₂ ↔ x ∈ D.B ∨ x ∈ dc D.B D.N D.w₂ :=
  mem_parabolic_single_iff D.isTits (D.rank2.gen_mem false)

private theorem w₁_ne_one : D.w₁ ≠ 1 := D.isTits.gen_ne_one (D.rank2.gen_mem true)

private theorem w₂_ne_one : D.w₂ ≠ 1 := D.isTits.gen_ne_one (D.rank2.gen_mem false)

private theorem w₁_mul_w₂_ne_one : D.w₁ * D.w₂ ≠ 1 := fun h => by
  rw [mul_eq_one_iff_eq_inv, D.rank2.dih.inv_b] at h
  exact D.w₁_ne_w₂ h

private theorem w₂_mul_w₁_ne_one : D.w₂ * D.w₁ ≠ 1 := fun h => by
  rw [mul_eq_one_iff_eq_inv, D.rank2.dih.inv_a] at h
  exact D.w₁_ne_w₂ h.symm

private theorem w₁_mul_w₂_ne_w₁ : D.w₁ * D.w₂ ≠ D.w₁ := fun h => D.w₂_ne_one (mul_eq_left.1 h)

private theorem w₁_mul_w₂_ne_w₂ : D.w₁ * D.w₂ ≠ D.w₂ := fun h => D.w₁_ne_one (mul_eq_right.1 h)

private theorem w₂_mul_w₁_ne_w₁ : D.w₂ * D.w₁ ≠ D.w₁ := fun h => D.w₂_ne_one (mul_eq_right.1 h)

private theorem w₂_mul_w₁_ne_w₂ : D.w₂ * D.w₁ ≠ D.w₂ := fun h => D.w₁_ne_one (mul_eq_left.1 h)

private theorem w₁_mul_w₂_ne_w₂_mul_w₁ : D.w₁ * D.w₂ ≠ D.w₂ * D.w₁ := by
  have h := D.rank2.dih.altWord_ne (i := 2) (j := 2) (by norm_num) (by norm_num) (by norm_num)
  simpa only [altWord, one_mul] using h.symm

private theorem weyl_cases (w : D.Weyl) :
    w = 1 ∨ w = D.w₁ ∨ w = D.w₂ ∨ w = D.w₁ * D.w₂ ∨ w = D.w₂ * D.w₁ ∨ w = D.w₀ := by
  obtain ⟨t, ht, rfl | rfl⟩ := D.rank2.dih.exists_altWord w
  · interval_cases t
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (by simp only [altWord, one_mul]))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by simp only [altWord, one_mul])))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  · interval_cases t
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl (by simp only [altWord, one_mul])))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by simp only [altWord, one_mul]))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr D.rank2.dih.altWord_eq.symm))))

end Weyl

section Polarity

variable {X : Type*} [Group X]

structure IsPolarity (D : RankTwoSystem X 3) (θ : X ≃* X) : Prop where
  mem_B : ∀ b ∈ D.B, θ b ∈ D.B
  mem_U : ∀ u ∈ D.U, θ u ∈ D.U
  P₁_P₂ : ∀ x ∈ D.P₁, θ x ∈ D.P₂
  P₂_P₁ : ∀ x ∈ D.P₂, θ x ∈ D.P₁

variable {D : RankTwoSystem X 3} {θ : X ≃* X}

theorem IsPolarity.fixed_mem_B_or_top (h : D.IsPolarity θ) {g : X} (hg : θ g = g) :
    g ∈ D.B ∨ g ∈ dc D.B D.N D.w₀ := by
  obtain ⟨w, hw⟩ := D.exists_dc g
  rcases D.weyl_cases w with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (mem_dc_one.1 hw)
  · refine (false_of_mem_dc_of_mem_B_or_dc D.isTits hw ?_ D.w₁_ne_one D.w₁_ne_w₂).elim
    rw [← hg]
    exact (D.mem_P₂_iff).1 (h.P₁_P₂ g ((D.mem_P₁_iff).2 (Or.inr hw)))
  · refine (false_of_mem_dc_of_mem_B_or_dc D.isTits hw ?_ D.w₂_ne_one D.w₁_ne_w₂.symm).elim
    rw [← hg]
    exact (D.mem_P₁_iff).1 (h.P₂_P₁ g ((D.mem_P₂_iff).2 (Or.inr hw)))
  · obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.1 (dc_mul_subset_of D.w₁ D.w₂ hw)
    exact (false_of_mul_mem_dc D.isTits (D.rank2.gen_mem false)
      ((D.mem_P₂_iff).1 (h.P₁_P₂ x ((D.mem_P₁_iff).2 (Or.inr hx))))
      ((D.mem_P₁_iff).1 (h.P₂_P₁ y ((D.mem_P₂_iff).2 (Or.inr hy))))
      (by rwa [← map_mul, hg]) D.w₁_mul_w₂_ne_one D.w₁_mul_w₂_ne_w₁ D.w₁_mul_w₂_ne_w₂
      D.w₁_mul_w₂_ne_w₂_mul_w₁).elim
  · obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.1 (dc_mul_subset_of D.w₂ D.w₁ hw)
    exact (false_of_mul_mem_dc D.isTits (D.rank2.gen_mem true)
      ((D.mem_P₁_iff).1 (h.P₂_P₁ x ((D.mem_P₂_iff).2 (Or.inr hx))))
      ((D.mem_P₂_iff).1 (h.P₁_P₂ y ((D.mem_P₁_iff).2 (Or.inr hy))))
      (by rwa [← map_mul, hg]) D.w₂_mul_w₁_ne_one D.w₂_mul_w₁_ne_w₂ D.w₂_mul_w₁_ne_w₁
      D.w₁_mul_w₂_ne_w₂_mul_w₁.symm).elim
  · exact Or.inr hw

theorem top_unique {c₀ : X} (hc₀ : c₀ ∈ dc D.B D.N D.w₀) {b b' u u' : X} (hb : b ∈ D.B)
    (hb' : b' ∈ D.B) (hu : u ∈ D.U) (hu' : u' ∈ D.U) (e : b * c₀ * u = b' * c₀ * u') :
    b = b' ∧ u = u' := by
  obtain ⟨b₂, hb₂, u₂, hu₂, rfl⟩ := (D.mem_dc_w₀_iff).1 hc₀
  have key := D.coord_unique (D.lift D.w₀) (D.B.mul_mem hb hb₂) (D.B.mul_mem hb' hb₂)
    (u := u₂ * u) (u' := u₂ * u')
    (by rw [D.UwMinus_w₀ (D.lift_mk D.w₀)]; exact D.U.mul_mem hu₂ hu)
    (by rw [D.UwMinus_w₀ (D.lift_mk D.w₀)]; exact D.U.mul_mem hu₂ hu')
    (by simpa only [mul_assoc] using e)
  have hu_eq : u = u' := mul_left_cancel key
  subst hu_eq
  exact ⟨mul_right_cancel (mul_right_cancel e), rfl⟩

theorem top_exists {c₀ g : X} (hc₀ : c₀ ∈ dc D.B D.N D.w₀) (hg : g ∈ dc D.B D.N D.w₀) :
    ∃ b ∈ D.B, ∃ u ∈ D.U, g = b * c₀ * u := by
  obtain ⟨b₂, hb₂, u₂, hu₂, rfl⟩ := (D.mem_dc_w₀_iff).1 hc₀
  obtain ⟨b₁, hb₁, u₁, hu₁, rfl⟩ := (D.mem_dc_w₀_iff).1 hg
  exact ⟨b₁ * b₂⁻¹, D.B.mul_mem hb₁ (D.B.inv_mem hb₂), u₂⁻¹ * u₁,
    D.U.mul_mem (D.U.inv_mem hu₂) hu₁, by group⟩

theorem U_meet_top {c₀ : X} (hc₀ : c₀ ∈ dc D.B D.N D.w₀) {u : X} (hu : u ∈ D.U)
    (h : c₀ * u * c₀⁻¹ ∈ D.B) : u = 1 := by
  have := top_unique hc₀ h D.B.one_mem D.U.one_mem hu
    (b := c₀ * u * c₀⁻¹) (b' := 1) (u := 1) (u' := u) (by group)
  exact this.2.symm

theorem IsPolarity.top_decomp (h : D.IsPolarity θ) {c₀ g : X} (hc₀ : c₀ ∈ dc D.B D.N D.w₀)
    (hg : g ∈ dc D.B D.N D.w₀) (hc₀f : θ c₀ = c₀) (hgf : θ g = g) :
    ∃ b ∈ D.B, θ b = b ∧ ∃ u ∈ D.U, θ u = u ∧ g = b * c₀ * u := by
  obtain ⟨b, hb, u, hu, rfl⟩ := top_exists hc₀ hg
  have e : θ b * c₀ * θ u = b * c₀ * u := by
    have := hgf
    rw [map_mul, map_mul, hc₀f] at this
    exact this
  obtain ⟨h1, h2⟩ := top_unique hc₀ (h.mem_B b hb) hb (h.mem_U u hu) hu e
  exact ⟨b, hb, h1, u, hu, h2, rfl⟩

end Polarity

end RankTwoSystem

end CFSG.GH74.BNPair
