module

public import CFSG.GH74.GLS.Stage4.RestZA
public import CFSG.GH74.GLS.Stage4.RestPre
public import CFSG.GH74.GLS.Stage4.RestSetup

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage4
  CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.BNPair CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage4.Rest.T2
  CFSG.GH74.GLS.Stage4.Rest.ZA

variable {G : Type} [Group G]

section SL2K

variable {K : Subgroup G} {F : Type} [Field F] [Finite F]

theorem phi_z (hF : Odd (Nat.card F)) (φ : ↥K ≃* SL2 F) {z : G} (hzK : z ∈ K) (hz2 : z * z = 1)
    (hz1 : z ≠ 1) : φ ⟨z, hzK⟩ = negOne F := by
  have h2 := two_ne_zero_of_card_odd hF
  apply eq_negOne_of_involution h2
  · rw [← map_mul]
    have : (⟨z, hzK⟩ : ↥K) * ⟨z, hzK⟩ = 1 := Subtype.ext hz2
    rw [this, map_one]
  · intro h
    apply hz1
    have := φ.injective (h.trans (map_one φ).symm)
    exact congrArg Subtype.val this

theorem inv_eq_one_or_z (hF : Odd (Nat.card F)) (φ : ↥K ≃* SL2 F) {z : G} (hzK : z ∈ K)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) {x : G} (hxK : x ∈ K) (hx : x * x = 1) : x = 1 ∨ x = z := by
  have hφz := phi_z hF φ hzK hz2 hz1
  have h2 := two_ne_zero_of_card_odd hF
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  · right
    have hφx : φ ⟨x, hxK⟩ = negOne F := by
      apply eq_negOne_of_involution h2
      · rw [← map_mul]
        have : (⟨x, hxK⟩ : ↥K) * ⟨x, hxK⟩ = 1 := Subtype.ext hx
        rw [this, map_one]
      · intro h
        apply hx1
        have := φ.injective (h.trans (map_one φ).symm)
        exact congrArg Subtype.val this
    have := φ.injective (hφx.trans hφz.symm)
    exact congrArg Subtype.val this

theorem center_eq_one_or_z (hF : Odd (Nat.card F)) (φ : ↥K ≃* SL2 F) {z : G} (hzK : z ∈ K)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) {c : G} (hcK : c ∈ K) (hc : ∀ k ∈ K, c * k = k * c) :
    c = 1 ∨ c = z := by
  have hφz := phi_z hF φ hzK hz2 hz1
  have h2 := two_ne_zero_of_card_odd hF
  have hcent : φ ⟨c, hcK⟩ ∈ Subgroup.center (SL2 F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := φ.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc k k.2).symm
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hcent
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have hr' : r = 1 ∨ r = -1 := by
    have : (r - 1) * (r + 1) = 0 := by linear_combination hr2
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases hr' with rfl | rfl
  · left
    have : φ ⟨c, hcK⟩ = 1 := by
      apply Subtype.ext
      rw [← hrA]
      simp
    have := φ.injective (this.trans (map_one φ).symm)
    exact congrArg Subtype.val this
  · right
    have : φ ⟨c, hcK⟩ = negOne F := by
      apply Subtype.ext
      rw [← hrA, t2B_negOne_eq]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have := φ.injective (this.trans hφz.symm)
    exact congrArg Subtype.val this

theorem conj_of_sq_eq_z (hF : Odd (Nat.card F)) (φ : ↥K ≃* SL2 F) {z : G} (hzK : z ∈ K)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) {x y : G} (hxK : x ∈ K) (hyK : y ∈ K) (hx : x * x = z)
    (hy : y * y = z) : ∃ k ∈ K, k * y * k⁻¹ = x := by
  have hφz := phi_z hF φ hzK hz2 hz1
  have hφx : φ ⟨x, hxK⟩ * φ ⟨x, hxK⟩ = negOne F := by
    rw [← map_mul, ← hφz]
    congr 1
    exact Subtype.ext hx
  have hφy : φ ⟨y, hyK⟩ * φ ⟨y, hyK⟩ = negOne F := by
    rw [← map_mul, ← hφz]
    congr 1
    exact Subtype.ext hy
  obtain ⟨g, hg⟩ := sl2_conj_of_sq_negOne hF hφx hφy
  refine ⟨((φ.symm g : ↥K) : G), (φ.symm g).2, ?_⟩
  have := congrArg φ.symm hg
  have e : φ.symm (g * φ ⟨y, hyK⟩ * g⁻¹) = (φ.symm g) * ⟨y, hyK⟩ * (φ.symm g)⁻¹ := by
    simp
  rw [e, MulEquiv.symm_apply_apply] at this
  have := congrArg Subtype.val this
  simpa using this

end SL2K

structure SL2Facts (K : Subgroup G) (z : G) : Prop where
  inv : ∀ x ∈ K, x * x = 1 → x = 1 ∨ x = z
  center : ∀ c ∈ K, (∀ k ∈ K, c * k = k * c) → c = 1 ∨ c = z
  conj : ∀ x ∈ K, ∀ y ∈ K, x * x = z → y * y = z → ∃ k ∈ K, k * y * k⁻¹ = x

theorem sl2Facts_of_iso {K : Subgroup G} {F : Type} [Field F] [Finite F] (hF : Odd (Nat.card F))
    (φ : ↥K ≃* SL2 F) {z : G} (hzK : z ∈ K) (hz2 : z * z = 1) (hz1 : z ≠ 1) : SL2Facts K z where
  inv := fun _ hx hx2 => inv_eq_one_or_z hF φ hzK hz2 hz1 hx hx2
  center := fun _ hc hcc => center_eq_one_or_z hF φ hzK hz2 hz1 hc hcc
  conj := fun _ hx _ hy hxx hyy => conj_of_sq_eq_z hF φ hzK hz2 hz1 hx hy hxx hyy

variable {D : Ch6Notation G}

theorem Ch6Basics.z_mul_z (h : Ch6Basics D) : D.z * D.z = 1 := by
  have := pow_orderOf_eq_one D.z
  rwa [h.z_ord, pow_two] at this

theorem Ch6Basics.z_ne_one (h : Ch6Basics D) : D.z ≠ 1 := by
  intro h1
  have := h.z_ord
  rw [h1, orderOf_one] at this
  omega

theorem Ch6Basics.sl2Facts₁ (h : Ch6Basics D) : SL2Facts D.K₁ D.z := by
  obtain ⟨F, hF, hFin, hcard, ⟨φ⟩⟩ := h.iso₁
  have hodd : Odd (Nat.card F) := by rw [hcard]; exact h.q₁_odd
  exact sl2Facts_of_iso hodd φ h.z_mem_K₁ h.z_mul_z h.z_ne_one

theorem Ch6Basics.sl2Facts₂ (h : Ch6Basics D) : SL2Facts D.K₂ D.z := by
  obtain ⟨F, hF, hFin, hcard, ⟨φ⟩⟩ := h.iso₂
  have hodd : Odd (Nat.card F) := by rw [hcard]; exact h.q₂_odd
  exact sl2Facts_of_iso hodd φ h.z_mem_K₂ h.z_mul_z h.z_ne_one

theorem Ch6Basics.involution_of_K (h : Ch6Basics D) {t : G} (htK : t ∈ D.K₁ ⊔ D.K₂)
    (ht : orderOf t = 2) :
    t = D.z ∨ ∃ x y : G, x ∈ D.K₁ ∧ y ∈ D.K₂ ∧ x * x = D.z ∧ y * y = D.z ∧ t = x * y := by
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_sup_iff_of_comm h.K_comm t).1 htK
  have hyx : y * x = x * y := (h.K_comm x hx y hy).symm
  have htt : x * y * (x * y) = 1 := by
    have := pow_orderOf_eq_one (x * y)
    rwa [ht, pow_two] at this
  have e : x * y * (x * y) = (x * x) * (y * y) := by
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hyx]
      _ = (x * x) * (y * y) := by group
  rw [e] at htt
  have hc : x * x = (y * y)⁻¹ := eq_inv_of_mul_eq_one_left htt
  have hcK₁ : x * x ∈ D.K₁ := D.K₁.mul_mem hx hx
  have hcK₂ : x * x ∈ D.K₂ := by rw [hc]; exact D.K₂.inv_mem (D.K₂.mul_mem hy hy)
  have hcent : ∀ k ∈ D.K₁, (x * x) * k = k * (x * x) := fun k hk => (h.K_comm k hk _ hcK₂).symm
  rcases h.sl2Facts₁.center _ hcK₁ hcent with hc1 | hcz
  ·
    left
    have hx2 := h.sl2Facts₁.inv x hx hc1
    have hyy : y * y = 1 := by
      have : (y * y)⁻¹ = 1 := by rw [← hc]; exact hc1
      exact inv_eq_one.1 this
    have hy2 := h.sl2Facts₂.inv y hy hyy
    have hne : x * y ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at ht
      omega
    rcases hx2 with rfl | rfl <;> rcases hy2 with rfl | rfl
    · exact absurd (by simp) hne
    · simp
    · simp
    · exact absurd h.z_mul_z hne
  · right
    refine ⟨x, y, hx, hy, hcz, ?_, rfl⟩
    have : (y * y)⁻¹ = D.z := by rw [← hc]; exact hcz
    have h2 : y * y = D.z⁻¹ := by
      rw [← this]
      simp
    rw [h2]
    exact inv_eq_of_mul_eq_one_right h.z_mul_z

theorem Ch6Notation.w₁_mem_N (D : Ch6Notation G) : D.w₁ ∈ D.N :=
  Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_insert _ _))

theorem Ch6Notation.r₂_mem_N (D : Ch6Notation G) : D.r₂ ∈ D.N :=
  Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

theorem Ch6Basics.w₂_mem_N (h : Ch6Basics D) : D.w₂ ∈ D.N := by
  have e : D.w₂ = D.a * D.r₂ * D.a⁻¹ := by
    simp only [Ch6Notation.r₂]
    group
  rw [e]
  exact D.N.mul_mem (D.N.mul_mem h.a_mem_N D.r₂_mem_N) (D.N.inv_mem h.a_mem_N)

theorem Ch6Core.K₁_le_G₀ (h : Ch6Core D) : D.K₁ ≤ (D.H ⊔ D.P) ⊔ D.N := by
  have hX₁ : D.X₁ ≤ D.P := by
    have := h.root_le_P (i := 1) (by norm_num) (by norm_num)
    rwa [root_p1] at this
  have hX₁G : D.X₁ ≤ (D.H ⊔ D.P) ⊔ D.N := hX₁.trans (le_sup_right.trans le_sup_left)
  rw [h.K₁_eq]
  refine sup_le hX₁G ?_
  intro x hx
  have hw : D.w₁ ∈ (D.H ⊔ D.P) ⊔ D.N := Subgroup.mem_sup_right D.w₁_mem_N
  have hXG := hX₁G (h.w₁_swap' x hx)
  have := mul_mem (mul_mem (inv_mem hw) hXG) hw
  rwa [show D.w₁⁻¹ * (D.w₁ * x * D.w₁⁻¹) * D.w₁ = x by group] at this

theorem Ch6Core.K₂_le_G₀ (h : Ch6Core D) : D.K₂ ≤ (D.H ⊔ D.P) ⊔ D.N := by
  have hX₂ : D.X₂ ≤ D.P := by
    have := h.root_le_P (i := 4) (by norm_num) (by norm_num)
    rwa [root_p4] at this
  have hX₂G : D.X₂ ≤ (D.H ⊔ D.P) ⊔ D.N := hX₂.trans (le_sup_right.trans le_sup_left)
  rw [h.K₂_eq]
  refine sup_le hX₂G ?_
  intro x hx
  have hw : D.w₂ ∈ (D.H ⊔ D.P) ⊔ D.N := Subgroup.mem_sup_right h.w₂_mem_N
  have hXG := hX₂G (h.w₂_swap' x hx)
  have := mul_mem (mul_mem (inv_mem hw) hXG) hw
  rwa [show D.w₂⁻¹ * (D.w₂ * x * D.w₂⁻¹) * D.w₂ = x by group] at this

@[expose] def Ch6Notation.ZFusion (D : Ch6Notation G) : Prop :=
  ∃ v ∈ D.K₁ ⊔ D.K₂, orderOf v = 2 ∧ v ≠ D.z ∧ ∃ g ∈ (D.H ⊔ D.P) ⊔ D.N, g * D.z * g⁻¹ = v

theorem Ch6Core.zclass_of_zfusion (h : Ch6Core D) (hf : D.ZFusion) : D.ZClass := by
  intro t htS ht2
  obtain ⟨v, hvK, hv2, hvz, g₀, hg₀, hgv⟩ := hf
  have htK : t ∈ D.K₁ ⊔ D.K₂ := htS.2
  have hKG : D.K₁ ⊔ D.K₂ ≤ (D.H ⊔ D.P) ⊔ D.N := sup_le h.K₁_le_G₀ h.K₂_le_G₀
  rcases h.toCh6Basics.involution_of_K htK ht2 with htz | ⟨x, y, hx, hy, hxx, hyy, htxy⟩
  · exact ⟨1, Subgroup.one_mem _, by simp [htz]⟩
  rcases h.toCh6Basics.involution_of_K hvK hv2 with hvz' | ⟨x₀, y₀, hx₀, hy₀, hx₀x₀, hy₀y₀, hv⟩
  · exact absurd hvz' hvz
  obtain ⟨k₁, hk₁, hk₁e⟩ := h.toCh6Basics.sl2Facts₁.conj x hx x₀ hx₀ hxx hx₀x₀
  obtain ⟨k₂, hk₂, hk₂e⟩ := h.toCh6Basics.sl2Facts₂.conj y hy y₀ hy₀ hyy hy₀y₀
  have hk₁G : k₁ ∈ (D.H ⊔ D.P) ⊔ D.N := h.K₁_le_G₀ hk₁
  have hk₂G : k₂ ∈ (D.H ⊔ D.P) ⊔ D.N := h.K₂_le_G₀ hk₂
  refine ⟨(k₁ * k₂) * g₀, Subgroup.mul_mem _ (Subgroup.mul_mem _ hk₁G hk₂G) hg₀, ?_⟩
  have e1 : (k₁ * k₂ * g₀) * D.z * (k₁ * k₂ * g₀)⁻¹ = (k₁ * k₂) * (g₀ * D.z * g₀⁻¹) * (k₁ * k₂)⁻¹ := by
    group
  rw [e1, hgv, hv, htxy, ← hk₁e, ← hk₂e]
  have hc1 : k₂ * x₀ = x₀ * k₂ := (h.K_comm x₀ hx₀ k₂ hk₂).symm
  have hy' : k₂ * y₀ * k₂⁻¹ ∈ D.K₂ := D.K₂.mul_mem (D.K₂.mul_mem hk₂ hy₀) (D.K₂.inv_mem hk₂)
  have hc2 : k₁⁻¹ * (k₂ * y₀ * k₂⁻¹) = (k₂ * y₀ * k₂⁻¹) * k₁⁻¹ :=
    h.K_comm k₁⁻¹ (D.K₁.inv_mem hk₁) _ hy'
  calc k₁ * k₂ * (x₀ * y₀) * (k₁ * k₂)⁻¹ = k₁ * (k₂ * x₀) * y₀ * k₂⁻¹ * k₁⁻¹ := by group
    _ = k₁ * (x₀ * k₂) * y₀ * k₂⁻¹ * k₁⁻¹ := by rw [hc1]
    _ = k₁ * x₀ * (k₂ * y₀ * k₂⁻¹) * k₁⁻¹ := by group
    _ = k₁ * x₀ * ((k₂ * y₀ * k₂⁻¹) * k₁⁻¹) := by group
    _ = k₁ * x₀ * (k₁⁻¹ * (k₂ * y₀ * k₂⁻¹)) := by rw [hc2]
    _ = k₁ * x₀ * k₁⁻¹ * (k₂ * y₀ * k₂⁻¹) := by group

theorem Ch6Basics.u_mul_u (h : Ch6Basics D) : D.u * D.u = 1 := by
  have e : D.u * D.u = D.a⁻¹ * (D.z * D.z) * D.a := by
    simp only [Ch6Notation.u]
    group
  rw [e, h.z_mul_z]
  group

theorem Ch6Basics.u_ne_one (h : Ch6Basics D) : D.u ≠ 1 := by
  intro h1
  apply h.z_ne_one
  have e : D.z = D.a * D.u * D.a⁻¹ := by
    simp only [Ch6Notation.u]
    group
  rw [e, h1]
  group

theorem Ch6Basics.u_ne_z (h : Ch6Basics D) (hcyc : D.a⁻¹ * D.u * D.a = D.z * D.u) : D.u ≠ D.z := by
  intro huz
  have hdef : D.u = D.a⁻¹ * D.z * D.a := rfl
  have h2 : D.a⁻¹ * D.u * D.a = D.u := by
    calc D.a⁻¹ * D.u * D.a = D.a⁻¹ * D.z * D.a := by rw [huz]
      _ = D.u := hdef.symm
  have h3 : D.z * D.u = D.u := hcyc.symm.trans h2
  exact h.z_ne_one (mul_right_cancel (h3.trans (one_mul D.u).symm))

theorem Ch6Core.zfusion_of_u_mem (h : Ch6Core D) (huz : D.u ≠ D.z) (hu : D.u ∈ D.K₁ ⊔ D.K₂) :
    D.ZFusion := by
  refine ⟨D.u, hu, orderOf_eq_prime (by rw [pow_two]; exact h.toCh6Basics.u_mul_u)
    h.toCh6Basics.u_ne_one, huz, D.a⁻¹, ?_, ?_⟩
  · exact Subgroup.mem_sup_right (D.N.inv_mem h.a_mem_N)
  · simp only [Ch6Notation.u]
    group

end CFSG.GH74.GLS.Stage4.Rest
