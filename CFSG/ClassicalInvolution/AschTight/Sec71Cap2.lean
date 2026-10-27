module

public import CFSG.ClassicalInvolution.AschTight.Sec71Cap

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W R K T J : Subgroup G} {u r z v t j : G}

theorem mem_normalizer_UV {u v g : G}
    (hu : g * u * g⁻¹ ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v)
    (hv : g * v * g⁻¹ ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq]
  refine Sec7.conjSub_eq_of_le_self ?_
  rw [conjSub, Subgroup.map_sup, ← conjSub, ← conjSub, AscL62.conjSub_zpowers_eq,
    AscL62.conjSub_zpowers_eq]
  exact sup_le (Subgroup.zpowers_le.mpr hu) (Subgroup.zpowers_le.mpr hv)

omit [Finite G] in
theorem u_mem_Y₀ (u v : G) (W : Subgroup G) :
    u ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v ⊔ OCW W :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers u))

omit [Finite G] in
theorem U_le_Y₀ (u v : G) (W : Subgroup G) :
    Subgroup.zpowers u ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers v ⊔ OCW W :=
  le_sup_left.trans le_sup_left

omit [Finite G] in
theorem V_le_Y₀ (u v : G) (W : Subgroup G) :
    Subgroup.zpowers v ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers v ⊔ OCW W :=
  le_sup_right.trans le_sup_left

omit [Finite G] in
theorem not_comm_of_inv {x u : G} (hx : x * u * x⁻¹ = u⁻¹) (hu : u * u ≠ 1) : x * u ≠ u * x := by
  intro h
  apply hu
  have : x * u * x⁻¹ = u := by rw [h]; group
  rw [hx] at this
  calc u * u = u * u⁻¹ := by rw [this]
    _ = 1 := mul_inv_cancel u

theorem cap_case_one (hΩ : HypOmegaMod p f Ω) (hd : DData Ω W R K u r z)
    (hd' : DData Ω W T K v t j) (hW2 : IsPGroup 2 W) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) :
    (R ⊔ T ⊔ OCW W) ⊓ W = Subgroup.closure {u, v} := by
  have hVU : Subgroup.zpowers v = Subgroup.zpowers u := hd'.inf_eq.symm.trans hd.inf_eq
  have hrN : r ∈ Subgroup.normalizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v ⊔ OCW W : Subgroup G) : Set G) := by
    refine mem_normalizer_Y₀ hd.r_normW (mem_normalizer_UV ?_ ?_)
    · rw [hd.conj_u]
      exact Subgroup.mem_sup_left (Subgroup.inv_mem _ (Subgroup.mem_zpowers u))
    · have hv : v ∈ Subgroup.zpowers u := hVU ▸ Subgroup.mem_zpowers v
      obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      rw [← conj_zpow, hd.conj_u]
      exact Subgroup.mem_sup_left (Subgroup.zpow_mem _ (Subgroup.inv_mem _
        (Subgroup.mem_zpowers u)) a)
  set F : Set G := {1, r} with hF
  have hFN : ∀ x ∈ F, x ∈ Subgroup.normalizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v ⊔ OCW W : Subgroup G) : Set G) := by
    rintro x (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact hrN
  have hr : ∀ x ∈ F, ∃ y ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v ⊔ OCW W, ∃ x' ∈ F,
      x * r = y * x' := by
    rintro x (rfl | rfl)
    · exact ⟨1, Subgroup.one_mem _, r, by simp [hF], by group⟩
    · exact ⟨z, U_le_Y₀ u v W hd.z_mem, 1, by simp [hF], by rw [hd.sq_r, mul_one]⟩
  have hRstep := step_of_table (R := R) (T := R) (t := r) (v := u) le_sup_right
    (U_le_Y₀ u v W) (U_le_Y₀ u v W) hFN hd.cover hd.cover hr hr
  have hRX : R ≤ Subgroup.normalizer ((OCW W : Subgroup G) : Set G) :=
    fun x hx => Sec7.normalizer_le_normalizer_OCW W (hd.memD.2 hx)
  refine inf_eq_of_table (F := F) hW2 hWc hd.u_memW hd'.u_memW (hd.U_le_R (Subgroup.mem_zpowers u))
    (hd'.U_le_R (Subgroup.mem_zpowers v)) (by simp [hF]) ?_ ?_
  · intro x hx s hs
    rcases hs with (hsR | hsT) | hsX
    · exact hRstep x hx s (Or.inl (Or.inl hsR))
    · have hsK : s ∈ K ⊓ Subgroup.normalizer (W : Set G) := ⟨hd'.le hsT, hd'.memD.2 hsT⟩
      obtain ⟨ρ, hρ, c, hc, rfl⟩ := exists_mul_of_mem_sup hRX (hd.inf_normalizer_le hΩ hsK)
      obtain ⟨y, hy, x', hx', he⟩ := hRstep x hx ρ (Or.inl (Or.inl hρ))
      refine ⟨y * (x' * c * x'⁻¹), Subgroup.mul_mem _ hy
        (conj_mem_of_mem_normalizer (hFN x' hx') (Subgroup.mem_sup_right hc)), x', hx', ?_⟩
      calc x * (ρ * c) = (x * ρ) * c := by group
        _ = y * x' * c := by rw [he]
        _ = y * (x' * c * x'⁻¹) * x' := by group
    · exact hRstep x hx s (Or.inr hsX)
  · rintro x (rfl | rfl) hu _
    · rfl
    · exact absurd hu (not_comm_of_inv hd.conj_u hd.u_sq_ne)

theorem comm_of_mem_OCW {W : Subgroup G} (hW2 : IsPGroup 2 W) {a b : G}
    (h1 : a * b * a⁻¹ * b⁻¹ ∈ OCW W) (h2 : a * b * a⁻¹ * b⁻¹ ∈ W) : a * b = b * a := by
  have h3 : a * b * a⁻¹ * b⁻¹ ∈ OCW W ⊓ W := ⟨h1, h2⟩
  rw [OCW_inf_eq_bot hW2, Subgroup.mem_bot] at h3
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = b * a := by rw [h3, one_mul]

theorem cap_case_two (hd : DData Ω W R K u r z) (hd' : DData Ω W T J v t j)
    (hW2 : IsPGroup 2 W) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    (hcomm : ∀ a ∈ R, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ OCW W) :
    (R ⊔ T ⊔ OCW W) ⊓ W = Subgroup.closure {u, v} := by
  have huR := hd.U_le_R (Subgroup.mem_zpowers u)
  have hvT := hd'.U_le_R (Subgroup.mem_zpowers v)
  have hW1 : ∀ {a b : G}, a ∈ W → b ∈ Subgroup.normalizer (W : Set G) →
      a * b * a⁻¹ * b⁻¹ ∈ W := fun {a b} ha hb => by
    have h : a * (b * a⁻¹ * b⁻¹) ∈ W :=
      W.mul_mem ha (conj_mem_of_mem_normalizer hb (W.inv_mem ha))
    simpa [mul_assoc] using h
  have hW2' : ∀ {a b : G}, a ∈ Subgroup.normalizer (W : Set G) → b ∈ W →
      a * b * a⁻¹ * b⁻¹ ∈ W := fun {a b} ha hb =>
    W.mul_mem (conj_mem_of_mem_normalizer ha hb) (W.inv_mem hb)
  have hut : u * t = t * u :=
    comm_of_mem_OCW hW2 (hcomm u huR t hd'.r_mem) (hW1 hd.u_memW hd'.r_normW)
  have hrv : r * v = v * r :=
    comm_of_mem_OCW hW2 (hcomm r hd.r_mem v hvT) (hW2' hd.r_normW hd'.u_memW)
  have htu : t * u * t⁻¹ = u := by rw [← hut]; group
  have hrv' : r * v * r⁻¹ = v := by rw [hrv]; group
  have hrN : r ∈ Subgroup.normalizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v ⊔ OCW W : Subgroup G) : Set G) := by
    refine mem_normalizer_Y₀ hd.r_normW (mem_normalizer_UV ?_ ?_)
    · rw [hd.conj_u]
      exact Subgroup.mem_sup_left (Subgroup.inv_mem _ (Subgroup.mem_zpowers u))
    · rw [hrv']
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers v)
  have htN : t ∈ Subgroup.normalizer
      ((Subgroup.zpowers u ⊔ Subgroup.zpowers v ⊔ OCW W : Subgroup G) : Set G) := by
    refine mem_normalizer_Y₀ hd'.r_normW (mem_normalizer_UV ?_ ?_)
    · rw [htu]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers u)
    · rw [hd'.conj_u]
      exact Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers v))
  have hc : t * r * t⁻¹ * r⁻¹ ∈ OCW W := by
    have := (OCW W).inv_mem (hcomm r hd.r_mem t hd'.r_mem)
    rwa [show (r * t * r⁻¹ * t⁻¹)⁻¹ = t * r * t⁻¹ * r⁻¹ by group] at this
  set Y₀ := Subgroup.zpowers u ⊔ Subgroup.zpowers v ⊔ OCW W with hY₀
  have hX : OCW W ≤ Y₀ := le_sup_right
  set F : Set G := {1, r, t, r * t} with hF
  have hFN : ∀ x ∈ F, x ∈ Subgroup.normalizer (Y₀ : Set G) := by
    intro x hx
    simp only [hF, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h | h <;> subst x
    · exact Subgroup.one_mem _
    · exact hrN
    · exact htN
    · exact Subgroup.mul_mem _ hrN htN
  have hr : ∀ x ∈ F, ∃ y ∈ Y₀, ∃ x' ∈ F, x * r = y * x' := by
    intro x hx
    simp only [hF, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h | h <;> subst x
    · exact ⟨1, Y₀.one_mem, r, by simp [hF], by group⟩
    · exact ⟨z, U_le_Y₀ u v W hd.z_mem, 1, by simp [hF], by rw [hd.sq_r, mul_one]⟩
    · exact ⟨t * r * t⁻¹ * r⁻¹, hX hc, r * t, by simp [hF], by group⟩
    · refine ⟨r * (t * r * t⁻¹ * r⁻¹) * r⁻¹ * z, Y₀.mul_mem
        (conj_mem_of_mem_normalizer hrN (hX hc)) (U_le_Y₀ u v W hd.z_mem), t, by simp [hF], ?_⟩
      rw [← hd.sq_r]
      group
  have ht : ∀ x ∈ F, ∃ y ∈ Y₀, ∃ x' ∈ F, x * t = y * x' := by
    intro x hx
    simp only [hF, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h | h <;> subst x
    · exact ⟨1, Y₀.one_mem, t, by simp [hF], by group⟩
    · exact ⟨1, Y₀.one_mem, r * t, by simp [hF], by group⟩
    · exact ⟨j, V_le_Y₀ u v W hd'.z_mem, 1, by simp [hF], by rw [hd'.sq_r, mul_one]⟩
    · refine ⟨r * j * r⁻¹, conj_mem_of_mem_normalizer hrN (V_le_Y₀ u v W hd'.z_mem), r,
        by simp [hF], ?_⟩
      rw [← hd'.sq_r]
      group
  refine inf_eq_of_table (F := F) hW2 hWc hd.u_memW hd'.u_memW huR hvT (by simp [hF])
    (step_of_table hX (U_le_Y₀ u v W) (V_le_Y₀ u v W) hFN hd.cover hd'.cover hr ht) ?_
  intro x hx hu hv
  simp only [hF, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with h | h | h | h <;> subst x
  · rfl
  · exact absurd hu (not_comm_of_inv hd.conj_u hd.u_sq_ne)
  · exact absurd hv (not_comm_of_inv hd'.conj_u hd'.u_sq_ne)
  · refine absurd hu (not_comm_of_inv ?_ hd.u_sq_ne)
    calc r * t * u * (r * t)⁻¹ = r * (t * u * t⁻¹) * r⁻¹ := by group
      _ = u⁻¹ := by rw [htu, hd.conj_u]

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71
