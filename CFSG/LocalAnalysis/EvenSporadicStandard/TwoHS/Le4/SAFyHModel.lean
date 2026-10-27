module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyHTheta
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyRel

public section

namespace CFSG.EvenSporadicStandard.TwoHS

namespace FyHModel

variable {G Λ : Type*} [Group G] [Group Λ]

@[expose] def emb {L : Subgroup G} (ι : L ≃* Λ) : Λ →* G := L.subtype.comp ι.symm.toMonoidHom

theorem emb_injective {L : Subgroup G} (ι : L ≃* Λ) : Function.Injective (emb ι) :=
  Subtype.val_injective.comp ι.symm.injective

theorem emb_mem {L : Subgroup G} (ι : L ≃* Λ) (p : Λ) : emb ι p ∈ L := (ι.symm p).2

structure Embed (e : Λ →* G) (σ : Λ →* Λ) (z : Λ) (f y₁ : G) : Prop where
  inj : Function.Injective e
  comm_f : ∀ p, e p * f = f * e p
  f4 : f ^ 4 = 1
  z_eq : e z = f ^ 2
  y_sq : y₁ * y₁ = 1
  y_f : y₁ * f = f⁻¹ * y₁
  sigma : ∀ p, y₁ * e p = e (σ p) * y₁

variable {e : Λ →* G} {σ : Λ →* Λ} {z : Λ} {f y₁ : G}

theorem Embed.f_inv (h : Embed e σ z f y₁) : f⁻¹ = e z * f := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [h.z_eq]
  calc f * (f ^ 2 * f) = f ^ 4 := by group
    _ = 1 := h.f4

theorem Embed.x_mul_x (h : Embed e σ z f y₁) (u v : Λ) :
    e u * f * (e v * f) = e (u * v * z) := by
  rw [Commute.mul_mul_mul_comm (show Commute f (e v) from (h.comm_f v).symm), map_mul, map_mul,
    h.z_eq, pow_two]

theorem Embed.x_mul_x_mul_x (h : Embed e σ z f y₁) (u v w : Λ) :
    e u * f * (e v * f) * (e w * f) = e (u * v * z * w) * f := by
  rw [h.x_mul_x, mul_assoc, ← mul_assoc (e _), ← map_mul]

theorem Embed.y_mul_x (h : Embed e σ z f y₁) (p : Λ) :
    y₁ * (e p * f) = e (σ p * z) * f * y₁ := by
  calc y₁ * (e p * f) = (y₁ * e p) * f := (mul_assoc _ _ _).symm
    _ = e (σ p) * (y₁ * f) := by rw [h.sigma, mul_assoc]
    _ = e (σ p) * (e z * f * y₁) := by rw [h.y_f, h.f_inv]
    _ = e (σ p * z) * f * y₁ := by simp only [map_mul, mul_assoc]

theorem Embed.conj_yr (h : Embed e σ z f y₁) (p q : Λ) :
    e p * (e q * y₁) * (e p)⁻¹ = e (p * q * (σ p)⁻¹) * y₁ := by
  have hy : y₁ * (e p)⁻¹ = e (σ p)⁻¹ * y₁ := by
    rw [← map_inv, h.sigma, map_inv]
  calc e p * (e q * y₁) * (e p)⁻¹ = e p * e q * (y₁ * (e p)⁻¹) := by simp only [mul_assoc]
    _ = e p * e q * (e (σ p)⁻¹ * y₁) := by rw [hy]
    _ = e (p * q * (σ p)⁻¹) * y₁ := by simp only [map_mul, mul_assoc]

theorem Embed.f_inv_mul_yr_mul_x (h : Embed e σ z f y₁) (q p : Λ) :
    f⁻¹ * (e q * y₁) * (e p * f) = e (q * (σ p * z)) * y₁ := by
  have hc : ∀ s, f⁻¹ * e s = e s * f⁻¹ := fun s =>
    (show Commute (e s) f from h.comm_f s).inv_right.eq.symm
  calc f⁻¹ * (e q * y₁) * (e p * f) = f⁻¹ * e q * (y₁ * (e p * f)) := by simp only [mul_assoc]
    _ = e q * f⁻¹ * (e (σ p * z) * f * y₁) := by rw [h.y_mul_x, hc q]
    _ = e q * (f⁻¹ * e (σ p * z)) * f * y₁ := by simp only [mul_assoc]
    _ = e q * (e (σ p * z) * f⁻¹) * f * y₁ := by rw [hc]
    _ = e q * e (σ p * z) * (f⁻¹ * f) * y₁ := by simp only [mul_assoc]
    _ = e (q * (σ p * z)) * y₁ := by rw [inv_mul_cancel, mul_one, ← map_mul]

section Rel

variable {R A l : Λ} {c : ℕ → Λ}

theorem a_sigma_c (hrel : FyRel σ z R A l c) {i : ℕ} (hi : i < 4) :
    A * (σ (c i) * z) = c i * A := by
  rw [hrel.c_a i hi, hrel.z_central A, mul_assoc, hrel.z_central (σ (c i))]

theorem mul_mul_z_mul (hrel : FyRel σ z R A l c) (p q r : Λ) :
    p * q * z * r = z * (p * q * r) := by
  rw [← hrel.z_central (p * q), mul_assoc]

theorem eq_of_mul_mul_z_eq_one (hrel : FyRel σ z R A l c) {u v : Λ} (hu : u * u = z)
    (h : u * v * z = 1) : v = u := by
  have hz : z⁻¹ = z := inv_eq_of_mul_eq_one_right hrel.z_sq
  have hui : u⁻¹ = u * z := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hu, hrel.z_sq])
  calc v = u⁻¹ * (u * v * z) * z⁻¹ := by group
    _ = u := by rw [h, hz, hui, mul_one, mul_assoc, hrel.z_sq, mul_one]

theorem eq_mul_z_of_mul_mul_z_eq_z (hrel : FyRel σ z R A l c) {u v : Λ} (hu : u * u = z)
    (h : u * v * z = z) : v = u * z := by
  have h1 : u * v = 1 := mul_right_cancel (h.trans (one_mul z).symm)
  have h2 : u * (u * z) = 1 := by rw [← mul_assoc, hu, hrel.z_sq]
  exact mul_left_cancel (h1.trans h2.symm)

theorem c02_sq (hrel : FyRel σ z R A l c) : c 0 * c 2 * z * (c 0 * c 2 * z) = 1 := by
  have h1 : c 0 * c 2 * (c 0 * c 2) = 1 :=
    calc c 0 * c 2 * (c 0 * c 2) = c 0 * (c 2 * c 0) * c 2 := by simp only [mul_assoc]
      _ = c 0 * (c 0 * c 2) * c 2 := by rw [← hrel.comm02]
      _ = c 0 * c 0 * (c 2 * c 2) := by simp only [mul_assoc]
      _ = 1 := by rw [hrel.c_sq 0 (by norm_num), hrel.c_sq 2 (by norm_num), hrel.z_sq]
  calc c 0 * c 2 * z * (c 0 * c 2 * z) = c 0 * c 2 * (z * (c 0 * c 2)) * z := by
        simp only [mul_assoc]
    _ = c 0 * c 2 * (c 0 * c 2) * (z * z) := by
        rw [hrel.z_central (c 0 * c 2)]; simp only [mul_assoc]
    _ = 1 := by rw [h1, hrel.z_sq, mul_one]

end Rel

theorem Embed.thetaData (h : Embed e σ z f y₁) {R A l : Λ} {c : ℕ → Λ}
    (hrel : FyRel σ z R A l c) (hf2 : f ^ 2 ≠ 1) :
    FyThetaData f (e A * y₁) (e R) (fun i => e (c i) * f) where
  f4 := h.f4
  t_ne := hf2
  yr_sq := by
    calc e A * y₁ * (e A * y₁) = e A * (y₁ * e A) * y₁ := by simp only [mul_assoc]
      _ = e (A * σ A) * (y₁ * y₁) := by rw [h.sigma]; simp only [map_mul, mul_assoc]
      _ = 1 := by rw [hrel.a_sig, h.y_sq, map_one, mul_one]
  yr_f := by
    have hy : y₁⁻¹ = y₁ := inv_eq_of_mul_eq_one_right h.y_sq
    have hc : e A * f⁻¹ = f⁻¹ * e A := (show Commute (e A) f from h.comm_f A).inv_right.eq
    calc e A * y₁ * f * (e A * y₁)⁻¹ = e A * (y₁ * f) * (y₁ * (e A)⁻¹) := by
          rw [mul_inv_rev, hy]; simp only [mul_assoc]
      _ = e A * f⁻¹ * (y₁ * y₁) * (e A)⁻¹ := by rw [h.y_f]; simp only [mul_assoc]
      _ = f⁻¹ := by rw [h.y_sq, mul_one, hc]; group
  r3 := by rw [← map_pow, hrel.r3, map_one]
  r_ne := fun h1 => hrel.r_ne (h.inj (h1.trans (map_one e).symm))
  r_f := h.comm_f R
  r_yr := by
    calc e R * (e A * y₁) = e (R * A) * y₁ := by rw [map_mul, mul_assoc]
      _ = e A * (e (σ R) * y₁) := by rw [← hrel.a_r, map_mul, mul_assoc]
      _ = e A * y₁ * e R := by rw [← h.sigma, mul_assoc]
  r_x := fun i hi => by
    show e R * (e (c i) * f) = e (c i) * f * e R
    calc e R * (e (c i) * f) = e (R * c i) * f := by rw [map_mul, mul_assoc]
      _ = e (c i) * (e R * f) := by rw [← hrel.c_r i hi, map_mul, mul_assoc]
      _ = e (c i) * f * e R := by rw [h.comm_f R, mul_assoc]
  f_x := fun i _ => by
    show f * (e (c i) * f) = e (c i) * f * f
    rw [← mul_assoc, ← h.comm_f]
  yr_x := fun i hi => by
    show e A * y₁ * (e (c i) * f) = e (c i) * f * (e A * y₁)
    calc e A * y₁ * (e (c i) * f) = e A * (y₁ * (e (c i) * f)) := mul_assoc _ _ _
      _ = e (A * (σ (c i) * z)) * f * y₁ := by
        rw [h.y_mul_x, ← mul_assoc, ← mul_assoc, map_mul e A]
      _ = e (c i * A) * f * y₁ := by rw [a_sigma_c hrel hi]
      _ = e (c i) * (e A * f) * y₁ := by rw [map_mul]; simp only [mul_assoc]
      _ = e (c i) * (f * e A) * y₁ := by rw [h.comm_f A]
      _ = e (c i) * f * (e A * y₁) := by simp only [mul_assoc]
  cox := by
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i j hij hj => ?_⟩
    · show e (c i) * f * (e (c i) * f) = 1
      rw [h.x_mul_x, hrel.c_sq i hi, hrel.z_sq, map_one]
    · show e (c i) * f * (e (c (i + 1)) * f) * (e (c i) * f) =
        e (c (i + 1)) * f * (e (c i) * f) * (e (c (i + 1)) * f)
      rw [h.x_mul_x_mul_x, h.x_mul_x_mul_x, mul_mul_z_mul hrel, mul_mul_z_mul hrel,
        hrel.braid i (by omega)]
    · show e (c i) * f * (e (c j) * f) = e (c j) * f * (e (c i) * f)
      rw [h.x_mul_x, h.x_mul_x]
      have : (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 3) := by omega
      rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hrel.comm02]
      · rw [hrel.comm03]
      · rw [hrel.comm13]
  x01 := by
    show e (c 0) * f * (e (c 1) * f) ≠ 1
    intro h1
    rw [h.x_mul_x] at h1
    exact hrel.c01 (eq_of_mul_mul_z_eq_one hrel (hrel.c_sq 0 (by norm_num))
      (h.inj (h1.trans (map_one e).symm))).symm

theorem Embed.fusion (h : Embed e σ z f y₁) {R A l : Λ} {c : ℕ → Λ}
    (hrel : FyRel σ z R A l c) :
    e l * (e A * y₁) * (e l)⁻¹ = f⁻¹ * (e A * y₁) * (e (c 0) * f) := by
  have h1 : l * A * (σ l)⁻¹ = A * (σ (c 0) * z) := by
    rw [hrel.fusion]; group
  rw [h.conj_yr, h.f_inv_mul_yr_mul_x, h1]

theorem Embed.x02_sq (h : Embed e σ z f y₁) {R A l : Λ} {c : ℕ → Λ}
    (hrel : FyRel σ z R A l c) :
    e (c 0) * f * (e (c 2) * f) * (e (c 0) * f * (e (c 2) * f)) = 1 := by
  rw [h.x_mul_x, ← map_mul, c02_sq hrel, map_one]

theorem Embed.x02_ne_one (h : Embed e σ z f y₁) {R A l : Λ} {c : ℕ → Λ}
    (hrel : FyRel σ z R A l c) : e (c 0) * f * (e (c 2) * f) ≠ 1 := fun h1 => by
  rw [h.x_mul_x] at h1
  exact hrel.c20 (eq_of_mul_mul_z_eq_one hrel (hrel.c_sq 0 (by norm_num))
    (h.inj (h1.trans (map_one e).symm)))

theorem Embed.x02_ne_t (h : Embed e σ z f y₁) {R A l : Λ} {c : ℕ → Λ}
    (hrel : FyRel σ z R A l c) : e (c 0) * f * (e (c 2) * f) ≠ f ^ 2 := fun h1 => by
  rw [h.x_mul_x, ← h.z_eq] at h1
  exact hrel.c20z (eq_mul_z_of_mul_mul_z_eq_z hrel (hrel.c_sq 0 (by norm_num)) (h.inj h1))

theorem embed_of_model {L : Subgroup G} {f y₁ : G} (ι : L ≃* Λ) (σ : Λ →* Λ) {z : Λ}
    (hfL : ∀ u ∈ L, u * f = f * u) (hf4 : f ^ 4 = 1) (hf2L : f ^ 2 ∈ L)
    (hy₁ : y₁ * y₁ = 1) (hy₁f : y₁ * f * y₁⁻¹ = f⁻¹)
    (hσ : ∀ x : L, y₁ * (x : G) * y₁⁻¹ = (ι.symm (σ (ι x)) : G))
    (hz : ι ⟨f ^ 2, hf2L⟩ = z) : Embed (emb ι) σ z f y₁ where
  inj := emb_injective ι
  comm_f := fun p => hfL _ (emb_mem ι p)
  f4 := hf4
  z_eq := by
    rw [← hz]
    show ((ι.symm (ι ⟨f ^ 2, hf2L⟩) : L) : G) = f ^ 2
    rw [MulEquiv.symm_apply_apply]
  y_sq := hy₁
  y_f := mul_inv_eq_iff_eq_mul.1 hy₁f
  sigma := fun p => by
    have := hσ (ι.symm p)
    rw [MulEquiv.apply_symm_apply] at this
    exact mul_inv_eq_iff_eq_mul.1 this

end FyHModel

theorem thetaData_of_model {G Λ : Type} [Group G] [Group Λ] {L : Subgroup G} {f y₁ : G}
    (ι : L ≃* Λ) (σ : Λ →* Λ) {z R A l : Λ} {c : ℕ → Λ} (hrel : FyRel σ z R A l c)
    (hfL : ∀ u ∈ L, u * f = f * u) (hf4 : f ^ 4 = 1) (hf2 : f ^ 2 ≠ 1) (hf2L : f ^ 2 ∈ L)
    (hy₁ : y₁ * y₁ = 1) (hy₁f : y₁ * f * y₁⁻¹ = f⁻¹)
    (hσ : ∀ x : L, y₁ * (x : G) * y₁⁻¹ = (ι.symm (σ (ι x)) : G))
    (hz : ι ⟨f ^ 2, hf2L⟩ = z) :
    ∃ (r yr : G) (x : ℕ → G), FyThetaData f yr r x ∧ r ∈ L ∧ (∃ a ∈ L, yr = a * y₁) ∧
      (∀ i < 4, ∃ c' ∈ L, x i = c' * f) ∧
      (∃ n₀ ∈ L, n₀ * yr * n₀⁻¹ = f⁻¹ * yr * x 0) ∧
      (x 0 * x 2 ∈ L ∧ (x 0 * x 2) * (x 0 * x 2) = 1 ∧ x 0 * x 2 ≠ 1 ∧ x 0 * x 2 ≠ f ^ 2) := by
  have h := FyHModel.embed_of_model ι σ hfL hf4 hf2L hy₁ hy₁f hσ hz
  refine ⟨FyHModel.emb ι R, FyHModel.emb ι A * y₁, fun i => FyHModel.emb ι (c i) * f,
    h.thetaData hrel hf2, FyHModel.emb_mem ι R, ⟨_, FyHModel.emb_mem ι A, rfl⟩,
    fun i _ => ⟨_, FyHModel.emb_mem ι (c i), rfl⟩,
    ⟨_, FyHModel.emb_mem ι l, h.fusion hrel⟩, ?_, h.x02_sq hrel, h.x02_ne_one hrel,
    h.x02_ne_t hrel⟩
  show FyHModel.emb ι (c 0) * f * (FyHModel.emb ι (c 2) * f) ∈ L
  rw [h.x_mul_x]
  exact FyHModel.emb_mem ι _

end CFSG.EvenSporadicStandard.TwoHS
