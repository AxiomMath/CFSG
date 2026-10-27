module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GroupTheory.TwoWeights

variable {G : Type*} [Group G]

theorem closure_comm {S : Set G} (hc : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s) :
    ∀ g ∈ Subgroup.closure S, ∀ h ∈ Subgroup.closure S, g * h = h * g := by
  intro g hg h hh
  have h1 : Subgroup.closure S ≤ Subgroup.centralizer S := by
    rw [Subgroup.closure_le]
    intro s hs
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro t ht
    exact hc t ht s hs
  have h2 : Subgroup.closure S ≤ Subgroup.centralizer ({h} : Set G) := by
    rw [Subgroup.closure_le]
    intro s hs
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.1 (h1 hh) s hs
  exact Subgroup.mem_centralizer_singleton_iff.1 (h2 hg)

theorem closure_pow_eq_one {S : Set G} {n : ℕ} (hS : ∀ s ∈ S, s ^ n = 1)
    (hc : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s) : ∀ g ∈ Subgroup.closure S, g ^ n = 1 := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact hS s hs
  | one => exact one_pow n
  | mul g h hg hh ihg ihh =>
    have hcomm : Commute g h := closure_comm hc g hg h hh
    rw [hcomm.mul_pow, ihg, ihh, one_mul]
  | inv g hg ih => rw [inv_pow, ih, inv_one]

theorem conj_mem_closure {S : Set G} (g : G)
    (h : ∀ s ∈ S, g * s * g⁻¹ ∈ Subgroup.closure S) :
    ∀ k ∈ Subgroup.closure S, g * k * g⁻¹ ∈ Subgroup.closure S := by
  intro k hk
  induction hk using Subgroup.closure_induction with
  | mem s hs => exact h s hs
  | one => simp
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

theorem mem_normalizer_closure {S : Set G} {g : G}
    (h1 : ∀ s ∈ S, g * s * g⁻¹ ∈ Subgroup.closure S)
    (h2 : ∀ s ∈ S, g⁻¹ * s * g ∈ Subgroup.closure S) :
    g ∈ Subgroup.normalizer (Subgroup.closure S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨conj_mem_closure g h1 k, fun hk => ?_⟩
  have h3 : g⁻¹ * (g * k * g⁻¹) * g⁻¹⁻¹ ∈ Subgroup.closure S :=
    conj_mem_closure g⁻¹ (fun s hs => by simpa using h2 s hs) _ hk
  have h4 : g⁻¹ * (g * k * g⁻¹) * g⁻¹⁻¹ = k := by group
  rwa [h4] at h3

structure Data (a u₁ u₂ u₃ x y : G) : Prop where
  a_a : a * a = 1
  u₁_u₁ : u₁ * u₁ = 1
  u₂_u₂ : u₂ * u₂ = 1
  u₃_u₃ : u₃ * u₃ = 1
  u₁_u₂ : u₁ * u₂ = u₂ * u₁
  u₁_u₃ : u₁ * u₃ = u₃ * u₁
  u₁_a : u₁ * a = a * u₁
  u₂_u₃ : u₂ * u₃ = u₃ * u₂
  u₂_a : u₂ * a = a * u₂
  u₃_a : u₃ * a = a * u₃
  a_x : a * x = x * a
  a_y : a * y = y * a
  x_u₁ : x * u₁ = u₁ * a * x
  x_u₂ : x * u₂ = u₃ * a * x
  x_u₃ : x * u₃ = u₂ * a * x
  xi_u₁ : x⁻¹ * u₁ = u₁ * a * x⁻¹
  xi_u₂ : x⁻¹ * u₂ = u₃ * a * x⁻¹
  xi_u₃ : x⁻¹ * u₃ = u₂ * a * x⁻¹
  y_u₁ : y * u₁ = u₁ * y
  y_u₂ : y * u₂ = u₂ * a * y
  y_u₃ : y * u₃ = u₁ * u₃ * a * y
  yi_u₁ : y⁻¹ * u₁ = u₁ * y⁻¹
  yi_u₂ : y⁻¹ * u₂ = u₂ * a * y⁻¹
  yi_u₃ : y⁻¹ * u₃ = u₁ * u₃ * a * y⁻¹
  xx : x * x = a
  yy : y * y = a
  xy4 : x * y * x * y * x * y * x * y = a

theorem Data.map {H : Type*} [Group H] (f : G →* H) {a u₁ u₂ u₃ x y : G}
    (D : Data a u₁ u₂ u₃ x y) : Data (f a) (f u₁) (f u₂) (f u₃) (f x) (f y) := by
  exact ⟨by simpa only [map_mul, map_inv, map_one] using congrArg f D.a_a,
    by simpa only [map_mul, map_inv, map_one] using congrArg f D.u₁_u₁,
    by simpa only [map_mul, map_inv, map_one] using congrArg f D.u₂_u₂,
    by simpa only [map_mul, map_inv, map_one] using congrArg f D.u₃_u₃,
    by simpa only [map_mul, map_inv, map_one] using congrArg f D.u₁_u₂,
    by simpa only [map_mul, map_inv, map_one] using congrArg f D.u₁_u₃,
    by simpa only [map_mul, map_inv, map_one] using congrArg f D.u₁_a,
    by simpa only [map_mul, map_inv, map_one] using congrArg f D.u₂_u₃,
    by simpa only [map_mul, map_inv, map_one] using congrArg f D.u₂_a,
    by simpa only [map_mul, map_inv, map_one] using congrArg f D.u₃_a,
    by simpa only [map_mul, map_inv, map_one] using congrArg f D.a_x,
    by simpa only [map_mul, map_inv, map_one] using congrArg f D.a_y,
    by simpa only [map_mul, map_inv, map_one] using congrArg f D.x_u₁,
    by simpa only [map_mul, map_inv, map_one] using congrArg f D.x_u₂,
    by simpa only [map_mul, map_inv, map_one] using congrArg f D.x_u₃,
    by simpa only [map_mul, map_inv, map_one] using congrArg f D.xi_u₁,
    by simpa only [map_mul, map_inv, map_one] using congrArg f D.xi_u₂,
    by simpa only [map_mul, map_inv, map_one] using congrArg f D.xi_u₃,
    by simpa only [map_mul, map_inv, map_one] using congrArg f D.y_u₁,
    by simpa only [map_mul, map_inv, map_one] using congrArg f D.y_u₂,
    by simpa only [map_mul, map_inv, map_one] using congrArg f D.y_u₃,
    by simpa only [map_mul, map_inv, map_one] using congrArg f D.yi_u₁,
    by simpa only [map_mul, map_inv, map_one] using congrArg f D.yi_u₂,
    by simpa only [map_mul, map_inv, map_one] using congrArg f D.yi_u₃,
    by simpa only [map_mul, map_inv, map_one] using congrArg f D.xx,
    by simpa only [map_mul, map_inv, map_one] using congrArg f D.yy,
    by simpa only [map_mul, map_inv, map_one] using congrArg f D.xy4⟩

variable {a u₁ u₂ u₃ x y : G}

theorem conj_of_comm {g s t : G} (h : g * s = t * g) : g * s * g⁻¹ = t := by
  rw [h]
  group

namespace Data

theorem V_sq (D : Data a u₁ u₂ u₃ x y) :
    ∀ s ∈ ({u₁, u₂, u₃, a} : Set G), s * s = 1 := by
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl | rfl
  exacts [D.u₁_u₁, D.u₂_u₂, D.u₃_u₃, D.a_a]

theorem V_comm (D : Data a u₁ u₂ u₃ x y) :
    ∀ s ∈ ({u₁, u₂, u₃, a} : Set G), ∀ t ∈ ({u₁, u₂, u₃, a} : Set G), s * t = t * s := by
  intro s hs t ht
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
  rcases hs with rfl | rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl | rfl <;>
    first | rfl | exact D.u₁_u₂ | exact D.u₁_u₃ | exact D.u₁_a | exact D.u₂_u₃ | exact D.u₂_a |
      exact D.u₃_a | exact D.u₁_u₂.symm | exact D.u₁_u₃.symm | exact D.u₁_a.symm |
      exact D.u₂_u₃.symm | exact D.u₂_a.symm | exact D.u₃_a.symm

theorem isPGroup_V (D : Data a u₁ u₂ u₃ x y) :
    IsPGroup 2 (Subgroup.closure ({u₁, u₂, u₃, a} : Set G)) := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  have h : (g : G) ^ 2 = 1 := by
    have := closure_pow_eq_one (n := 2) (fun s hs => by rw [sq]; exact D.V_sq s hs) D.V_comm g g.2
    exact this
  simpa using h

theorem x_mem_normalizer (D : Data a u₁ u₂ u₃ x y) :
    x ∈ Subgroup.normalizer (Subgroup.closure ({u₁, u₂, u₃, a} : Set G) : Set G) := by
  have hax : x * a * x⁻¹ = a := by rw [← D.a_x]; group
  have hax' : x⁻¹ * a * x = a := by
    calc x⁻¹ * a * x = x⁻¹ * (a * x) := by group
      _ = x⁻¹ * (x * a) := by rw [D.a_x]
      _ = a := by group
  have c1 := conj_of_comm D.x_u₁
  have c2 := conj_of_comm D.x_u₂
  have c3 := conj_of_comm D.x_u₃
  have d1 := conj_of_comm D.xi_u₁
  have d2 := conj_of_comm D.xi_u₂
  have d3 := conj_of_comm D.xi_u₃
  rw [inv_inv] at d1 d2 d3
  have m1 : u₁ ∈ Subgroup.closure ({u₁, u₂, u₃, a} : Set G) := Subgroup.subset_closure (by simp)
  have m2 : u₂ ∈ Subgroup.closure ({u₁, u₂, u₃, a} : Set G) := Subgroup.subset_closure (by simp)
  have m3 : u₃ ∈ Subgroup.closure ({u₁, u₂, u₃, a} : Set G) := Subgroup.subset_closure (by simp)
  have m4 : a ∈ Subgroup.closure ({u₁, u₂, u₃, a} : Set G) := Subgroup.subset_closure (by simp)
  refine mem_normalizer_closure (fun s hs => ?_) (fun s hs => ?_) <;>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs <;>
    rcases hs with rfl | rfl | rfl | rfl
  · rw [c1]; exact Subgroup.mul_mem _ m1 m4
  · rw [c2]; exact Subgroup.mul_mem _ m3 m4
  · rw [c3]; exact Subgroup.mul_mem _ m2 m4
  · rw [hax]; exact m4
  · rw [d1]; exact Subgroup.mul_mem _ m1 m4
  · rw [d2]; exact Subgroup.mul_mem _ m3 m4
  · rw [d3]; exact Subgroup.mul_mem _ m2 m4
  · rw [hax']; exact m4

theorem y_mem_normalizer (D : Data a u₁ u₂ u₃ x y) :
    y ∈ Subgroup.normalizer (Subgroup.closure ({u₁, u₂, u₃, a} : Set G) : Set G) := by
  have hay : y * a * y⁻¹ = a := by rw [← D.a_y]; group
  have hay' : y⁻¹ * a * y = a := by
    calc y⁻¹ * a * y = y⁻¹ * (a * y) := by group
      _ = y⁻¹ * (y * a) := by rw [D.a_y]
      _ = a := by group
  have c1 := conj_of_comm D.y_u₁
  have c2 := conj_of_comm D.y_u₂
  have c3 := conj_of_comm D.y_u₃
  have d1 := conj_of_comm D.yi_u₁
  have d2 := conj_of_comm D.yi_u₂
  have d3 := conj_of_comm D.yi_u₃
  rw [inv_inv] at d1 d2 d3
  have m1 : u₁ ∈ Subgroup.closure ({u₁, u₂, u₃, a} : Set G) := Subgroup.subset_closure (by simp)
  have m2 : u₂ ∈ Subgroup.closure ({u₁, u₂, u₃, a} : Set G) := Subgroup.subset_closure (by simp)
  have m3 : u₃ ∈ Subgroup.closure ({u₁, u₂, u₃, a} : Set G) := Subgroup.subset_closure (by simp)
  have m4 : a ∈ Subgroup.closure ({u₁, u₂, u₃, a} : Set G) := Subgroup.subset_closure (by simp)
  refine mem_normalizer_closure (fun s hs => ?_) (fun s hs => ?_) <;>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs <;>
    rcases hs with rfl | rfl | rfl | rfl
  · rw [c1]; exact m1
  · rw [c2]; exact Subgroup.mul_mem _ m2 m4
  · rw [c3]; exact Subgroup.mul_mem _ (Subgroup.mul_mem _ m1 m3) m4
  · rw [hay]; exact m4
  · rw [d1]; exact m1
  · rw [d2]; exact Subgroup.mul_mem _ m2 m4
  · rw [d3]; exact Subgroup.mul_mem _ (Subgroup.mul_mem _ m1 m3) m4
  · rw [hay']; exact m4

theorem inv_x (D : Data a u₁ u₂ u₃ x y) : x⁻¹ = a * x :=
  (eq_inv_of_mul_eq_one_left (by rw [mul_assoc, D.xx, D.a_a])).symm

theorem inv_y (D : Data a u₁ u₂ u₃ x y) : y⁻¹ = a * y :=
  (eq_inv_of_mul_eq_one_left (by rw [mul_assoc, D.yy, D.a_a])).symm

theorem x_conj_xy (D : Data a u₁ u₂ u₃ x y) : x * (x * y) * x⁻¹ = (x * y)⁻¹ := by
  calc x * (x * y) * x⁻¹ = (x * x) * y * x⁻¹ := by group
    _ = a * y * x⁻¹ := by rw [D.xx]
    _ = y⁻¹ * x⁻¹ := by rw [D.inv_y]
    _ = (x * y)⁻¹ := (mul_inv_rev x y).symm

theorem x_conj_xy' (D : Data a u₁ u₂ u₃ x y) : x⁻¹ * (x * y) * x = (x * y)⁻¹ := by
  calc x⁻¹ * (x * y) * x = y * x := by group
    _ = y * (a * a) * x := by rw [D.a_a, mul_one]
    _ = (y * a) * (a * x) := by group
    _ = (a * y) * (a * x) := by rw [D.a_y]
    _ = y⁻¹ * x⁻¹ := by rw [D.inv_y, D.inv_x]
    _ = (x * y)⁻¹ := (mul_inv_rev x y).symm

theorem isPGroup_closure (D : Data a u₁ u₂ u₃ x y) :
    IsPGroup 2 (Subgroup.closure ({u₁, u₂, u₃, a, x, y} : Set G)) := by
  set V : Subgroup G := Subgroup.closure ({u₁, u₂, u₃, a} : Set G) with hVdef
  have hV : IsPGroup 2 V := D.isPGroup_V
  have hxV := D.x_mem_normalizer
  have hyV := D.y_mem_normalizer
  have hx4 : x ^ 4 = 1 := by
    calc x ^ 4 = (x * x) * (x * x) := by simp [pow_succ, mul_assoc]
      _ = 1 := by rw [D.xx, D.a_a]
  have hxy8 : (x * y) ^ 8 = 1 := by
    calc (x * y) ^ 8 = (x * y * x * y * x * y * x * y) * (x * y * x * y * x * y * x * y) := by
          simp [pow_succ, mul_assoc]
      _ = 1 := by rw [D.xy4, D.a_a]
  have hxp : IsPGroup 2 (Subgroup.zpowers x) := by
    refine IsPGroup.of_card_dvd_pow (n := 2) ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hx4
  have hxyp : IsPGroup 2 (Subgroup.zpowers (x * y)) := by
    refine IsPGroup.of_card_dvd_pow (n := 3) ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hxy8
  have hxn : Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers (x * y) : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.zpowers_eq_closure]
    refine mem_normalizer_closure (fun s hs => ?_) (fun s hs => ?_)
    · rw [Set.mem_singleton_iff] at hs
      rw [hs, D.x_conj_xy]
      exact Subgroup.inv_mem _ (Subgroup.subset_closure rfl)
    · rw [Set.mem_singleton_iff] at hs
      rw [hs, D.x_conj_xy']
      exact Subgroup.inv_mem _ (Subgroup.subset_closure rfl)
  have hH : IsPGroup 2 (Subgroup.zpowers x ⊔ Subgroup.zpowers (x * y) : Subgroup G) :=
    hxp.to_sup_of_normal_right' hxyp hxn
  have hHV : (Subgroup.zpowers x ⊔ Subgroup.zpowers (x * y) : Subgroup G) ≤
      Subgroup.normalizer (V : Set G) :=
    sup_le (Subgroup.zpowers_le.2 hxV)
      (Subgroup.zpowers_le.2 (Subgroup.mul_mem _ hxV hyV))
  have hB : IsPGroup 2 ((Subgroup.zpowers x ⊔ Subgroup.zpowers (x * y)) ⊔ V : Subgroup G) :=
    hH.to_sup_of_normal_right' hV hHV
  refine hB.to_le ((Subgroup.closure_le _).2 ?_)
  have hxH : x ∈ (Subgroup.zpowers x ⊔ Subgroup.zpowers (x * y) : Subgroup G) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hxyH : x * y ∈ (Subgroup.zpowers x ⊔ Subgroup.zpowers (x * y) : Subgroup G) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hyH : y ∈ (Subgroup.zpowers x ⊔ Subgroup.zpowers (x * y) : Subgroup G) := by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hxH) hxyH
    simpa using this
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  have hVB : ∀ v ∈ V, v ∈ ((Subgroup.zpowers x ⊔ Subgroup.zpowers (x * y)) ⊔ V : Subgroup G) :=
    fun v hv => Subgroup.mem_sup_right hv
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hVB _ (Subgroup.subset_closure (by simp))
  · exact hVB _ (Subgroup.subset_closure (by simp))
  · exact hVB _ (Subgroup.subset_closure (by simp))
  · exact hVB _ (Subgroup.subset_closure (by simp))
  · exact Subgroup.mem_sup_left hxH
  · exact Subgroup.mem_sup_left hyH

theorem closure_le_centralizer (D : Data a u₁ u₂ u₃ x y) :
    Subgroup.closure ({u₁, u₂, u₃, a, x, y} : Set G) ≤ Subgroup.centralizer ({a} : Set G) := by
  rw [Subgroup.closure_le]
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact D.u₁_a
  · exact D.u₂_a
  · exact D.u₃_a
  · rfl
  · exact D.a_x.symm
  · exact D.a_y.symm

end Data

end CFSG.GroupTheory.TwoWeights
