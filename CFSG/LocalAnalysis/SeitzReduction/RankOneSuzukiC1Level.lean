module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1LevelS
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1Orbit
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiC1Weights

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace SzC1

variable {G : Type*} [Group G]

theorem exists_addMonoidHom₂_of_hom₂ {K : Type*} [Field K] {M : Subgroup G} {S : G → K}
    {B : G → G → K} (hS : ∀ m ∈ M, ∀ m' ∈ M, S (m * m') = S m + S m')
    (hSsurj : ∀ s : K, ∃ m ∈ M, S m = s)
    (hB₁ : ∀ m ∈ M, ∀ m' ∈ M, ∀ n ∈ M, B (m * m') n = B m n + B m' n)
    (hB₂ : ∀ m ∈ M, ∀ n ∈ M, ∀ n' ∈ M, B m (n * n') = B m n + B m n')
    (hker₁ : ∀ m ∈ M, S m = 0 → ∀ n ∈ M, B m n = 0)
    (hker₂ : ∀ n ∈ M, S n = 0 → ∀ m ∈ M, B m n = 0) :
    ∃ D : K →+ K →+ K, ∀ m ∈ M, ∀ n ∈ M, B m n = D (S m) (S n) := by
  choose sec hsecM hsecS using hSsurj
  have key : ∀ m ∈ M, ∀ n ∈ M, B m n = B m (sec (S n)) := by
    intro m hm n hn
    have hz : (sec (S n))⁻¹ * n ∈ M := mul_mem (inv_mem (hsecM _)) hn
    have hSz : S ((sec (S n))⁻¹ * n) = 0 := by
      have h1 := hS _ (hsecM (S n)) _ hz
      rw [mul_inv_cancel_left, hsecS] at h1
      exact left_eq_add.mp h1
    have h2 := hB₂ m hm _ (hsecM (S n)) _ hz
    rw [mul_inv_cancel_left, hker₂ _ hz hSz m hm, add_zero] at h2
    exact h2
  obtain ⟨D, hD⟩ := exists_addMonoidHom₂_of_hom (Φ := fun m b => B m (sec b)) hS
    (fun s => ⟨sec s, hsecM s, hsecS s⟩)
    (fun m hm m' hm' b => hB₁ m hm m' hm' _ (hsecM b))
    (fun m hm b b' => by
      show B m (sec (b + b')) = B m (sec b) + B m (sec b')
      have hmul := mul_mem (hsecM b) (hsecM b')
      rw [← hB₂ m hm _ (hsecM b) _ (hsecM b'), key m hm _ hmul, hS _ (hsecM b) _ (hsecM b'),
        hsecS, hsecS])
    (fun m hm hSm b => hker₁ m hm hSm _ (hsecM b))
  exact ⟨D, fun m hm n hn => by rw [key m hm n hn]; exact hD m hm (S n)⟩

theorem comm_conj_eq_of_dev {A : Subgroup G} (hA : ∀ b ∈ A, ∀ b' ∈ A, b * b' = b' * b)
    {x y w : G} (hx : ∀ b ∈ A, x * b * x⁻¹ = b) (hy : ∀ b ∈ A, y * b * y⁻¹ = b)
    (hxw : w⁻¹ * (x * w * x⁻¹) ∈ A) (hyw : w⁻¹ * (y * w * y⁻¹) ∈ A) :
    x * y * x⁻¹ * y⁻¹ * w * (x * y * x⁻¹ * y⁻¹)⁻¹ = w := by
  have hinv : ∀ z : G, (∀ b ∈ A, z * b * z⁻¹ = b) → ∀ b ∈ A, z⁻¹ * b * z = b := by
    intro z hz b hb
    calc z⁻¹ * b * z = z⁻¹ * (z * b * z⁻¹) * z := by rw [hz b hb]
      _ = b := by group
  obtain ⟨p, hpA, hp⟩ : ∃ p ∈ A, x * w * x⁻¹ = w * p := ⟨_, hxw, by group⟩
  obtain ⟨q, hqA, hq⟩ : ∃ q ∈ A, y * w * y⁻¹ = w * q := ⟨_, hyw, by group⟩
  have hback : ∀ z p : G, (∀ b ∈ A, z * b * z⁻¹ = b) → p ∈ A → z * w * z⁻¹ = w * p →
      z⁻¹ * w * z = w * p⁻¹ := by
    intro z p hz hp' hzp
    calc z⁻¹ * w * z = z⁻¹ * (w * p) * z * (z⁻¹ * p * z)⁻¹ := by group
      _ = z⁻¹ * (z * w * z⁻¹) * z * p⁻¹ := by rw [← hzp, hinv z hz p hp']
      _ = w * p⁻¹ := by group
  have h1 := hback y q hy hqA hq
  have h2 := hback x p hx hpA hp
  have hxq : x⁻¹ * q⁻¹ * x = q⁻¹ := hinv x hx _ (inv_mem hqA)
  have hyp : y * p⁻¹ * y⁻¹ = p⁻¹ := hy _ (inv_mem hpA)
  have hyq : y * q⁻¹ * y⁻¹ = q⁻¹ := hy _ (inv_mem hqA)
  have hxp : x * p⁻¹ * x⁻¹ = p⁻¹ := hx _ (inv_mem hpA)
  have hxq' : x * q * x⁻¹ = q := hx _ hqA
  have hxq'' : x * q⁻¹ * x⁻¹ = q⁻¹ := hx _ (inv_mem hqA)
  calc x * y * x⁻¹ * y⁻¹ * w * (x * y * x⁻¹ * y⁻¹)⁻¹ =
        x * (y * (x⁻¹ * (y⁻¹ * w * y) * x) * y⁻¹) * x⁻¹ := by group
    _ = x * (y * ((x⁻¹ * w * x) * (x⁻¹ * q⁻¹ * x)) * y⁻¹) * x⁻¹ := by rw [h1]; group
    _ = x * ((y * w * y⁻¹) * (y * p⁻¹ * y⁻¹) * (y * q⁻¹ * y⁻¹)) * x⁻¹ := by
        rw [h2, hxq]; group
    _ = (x * w * x⁻¹) * (x * q * x⁻¹) * (x * p⁻¹ * x⁻¹) * (x * q⁻¹ * x⁻¹) := by
        rw [hq, hyp, hyq]; group
    _ = w * (p * q * p⁻¹ * q⁻¹) := by rw [hp, hxq', hxp, hxq'']; group
    _ = w := by rw [hA p hpA q hqA]; group

end SzC1

namespace SzC1Stage

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f a : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ}

theorem comm_t_conj_d (h : SzC1Stage G L f a t T d V U U₁ k) (y : G) :
    d⁻¹ * y * d * t * (d⁻¹ * y * d)⁻¹ * t⁻¹ = d⁻¹ * (y * t * y⁻¹ * t⁻¹) * d := by
  have hdt : d * t = t * d := (mem_centralizer_singleton_iff.mp h.d_norm.2)
  have e1 : d * t * d⁻¹ = t := by rw [hdt, mul_inv_cancel_right]
  have e2 : d * t⁻¹ * d⁻¹ = t⁻¹ := by rw [h.t_inv, e1]
  calc d⁻¹ * y * d * t * (d⁻¹ * y * d)⁻¹ * t⁻¹ =
        d⁻¹ * (y * (d * t * d⁻¹) * y⁻¹ * (d * t⁻¹ * d⁻¹)) * d := by group
    _ = _ := by rw [e1, e2]

theorem chi_eq_one_of_mem_szA₁ (h : SzC1Stage G L f a t T d V U U₁ k) {x : G} (hx : x ∈ U₁)
    {b : G} (hb : b ∈ szA₁ (szT₁ L T)) : b⁻¹ * (x * b * x⁻¹) = 1 := by
  rw [h.conj_szA₁ x (h.U₁_le hx) b hb, inv_mul_cancel]

theorem szA₁_comm (h : SzC1Stage G L f a t T d V U U₁ k) :
    ∀ b ∈ szA₁ (szT₁ L T), ∀ b' ∈ szA₁ (szT₁ L T), b * b' = b' * b := fun b hb b' hb' =>
  h.comm b (h.le hb) b' (h.le hb')

theorem isPGroup_U (h : SzC1Stage G L f a t T d V U U₁ k) : IsPGroup 2 U :=
  IsPGroup.of_card (n := 1 + f * (k + 3)) (by rw [h.card_U]; ring)

section Coords

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {u v : G → K} {κ : K}
  (h : SzC1Stage G L f a t T d V U U₁ k) (hK : Fintype.card K = 2 ^ f)
  (hc : SzRootCoords (szT₁ L T) a d u v κ)
include h hK hc

theorem B_mul_left {x x' y : G} (hx : x ∈ U₁) (hx' : x' ∈ U₁) (hy : y ∈ U₁) :
    v ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * x' * (y * t * y⁻¹ * t⁻¹) * (x * x')⁻¹)) =
      v ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹)) +
        v ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x' * (y * t * y⁻¹ * t⁻¹) * x'⁻¹)) := by
  have hσ := h.comm_t_mem (h.U₁_le hy)
  rw [h.chi_mul_left hx hx' hσ, hc.v_mul_szA₁ h.ha (h.card_K hK hc) (h.conj_V₁ x hx _ hσ)
    (h.conj_V₁ x' hx' _ hσ)]

theorem B_mul_right {x y y' : G} (hx : x ∈ U₁) (hy : y ∈ U₁) (hy' : y' ∈ U₁) :
    v ((y * y' * t * (y * y')⁻¹ * t⁻¹)⁻¹ * (x * (y * y' * t * (y * y')⁻¹ * t⁻¹) * x⁻¹)) =
      v ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹)) +
        v ((y' * t * y'⁻¹ * t⁻¹)⁻¹ * (x * (y' * t * y'⁻¹ * t⁻¹) * x⁻¹)) := by
  have hK' := h.card_K hK hc
  have hb := h.comm_t_mem (h.U₁_le hy)
  have hb' := h.comm_t_mem (h.U₁_le hy')
  have ha := h.conj_V hy hb'
  have hcA := h.conj_V₁ y hy _ hb'
  have e1 : y * (y' * t * y'⁻¹ * t⁻¹) * y⁻¹ = (y' * t * y'⁻¹ * t⁻¹) *
      ((y' * t * y'⁻¹ * t⁻¹)⁻¹ * (y * (y' * t * y'⁻¹ * t⁻¹) * y⁻¹)) := by group
  rw [SzC1.comm_t_mul, h.chi_mul_right hx ha hb, e1, h.chi_mul_right hx hb' (h.le hcA),
    h.chi_eq_one_of_mem_szA₁ hx hcA, mul_one,
    hc.v_mul_szA₁ h.ha hK' (h.conj_V₁ x hx _ hb') (h.conj_V₁ x hx _ hb), add_comm]

theorem B_eq_zero_left {x : G} (hx : x ∈ U₁) (h0 : v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ k) = 0)
    {y : G} (hy : y ∈ U₁) : v ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹)) = 0 := by
  rw [h.chi_eq_one_of_mem_sup (h.mem_sup_of_S_eq_zero hK hc hx h0) (h.comm_t_mem (h.U₁_le hy)),
    hc.v_one]

theorem B_eq_zero_right {y : G} (hy : y ∈ U₁) (h0 : v ((y * t * y⁻¹ * t⁻¹) ^ 2 ^ k) = 0)
    {x : G} (hx : x ∈ U₁) : v ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹)) = 0 := by
  obtain ⟨y₀, hy₀, r, hr, rfl⟩ := h.exists_mul_of_mem_sup (h.mem_sup_of_S_eq_zero hK hc hy h0)
  rw [h.comm_t_of_mem_sup hy₀ hr, sq, h.chi_mul_right hx hr hr, ← sq,
    hc.sq_eq_one_of_mem_szA₁ h.ha (h.card_K hK hc) (h.conj_V₁ x hx r hr), hc.v_one]

theorem B_conj_d {x y : G} (hx : x ∈ U₁) (hy : y ∈ U₁) :
    v ((d⁻¹ * y * d * t * (d⁻¹ * y * d)⁻¹ * t⁻¹)⁻¹ *
        (d⁻¹ * x * d * (d⁻¹ * y * d * t * (d⁻¹ * y * d)⁻¹ * t⁻¹) * (d⁻¹ * x * d)⁻¹)) =
      κ ^ (2 ^ (a + 1) + 1) * v ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹)) := by
  rw [h.comm_t_conj_d y]
  have e : (d⁻¹ * (y * t * y⁻¹ * t⁻¹) * d)⁻¹ * (d⁻¹ * x * d * (d⁻¹ * (y * t * y⁻¹ * t⁻¹) * d) *
      (d⁻¹ * x * d)⁻¹) = d⁻¹ * ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹)) * d := by
    group
  rw [e, hc.v_conj_szA₁ h.ha (h.card_K hK hc) (h.conj_V₁ x hx _ (h.comm_t_mem (h.U₁_le hy)))]

theorem exists_mu (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w) :
    ∃ μ' : K, ∀ x ∈ U₁, ∀ y ∈ U₁,
      v ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹)) =
        μ' * (v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ k) * v ((y * t * y⁻¹ * t⁻¹) ^ 2 ^ k)) ^ 2 ^ (f - 1) := by
  have hcardK : Nat.card K = 2 ^ (2 * a + 1) := by rw [Nat.card_eq_fintype_card, h.card_K hK hc]
  have hμ := pow_theta_succ_generator_of_generator h.ha hcardK hκ
  obtain ⟨D, hD⟩ := SzC1.exists_addMonoidHom₂_of_hom₂ (M := U₁)
    (S := fun x => v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ k))
    (B := fun x y => v ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹)))
    (fun x hx y hy => h.S_mul hK hc hx hy) (h.S_surj hK hc hκ)
    (fun x hx x' hx' y hy => h.B_mul_left hK hc hx hx' hy)
    (fun x hx y hy y' hy' => h.B_mul_right hK hc hx hy hy')
    (fun x hx h0 y hy => h.B_eq_zero_left hK hc hx h0 hy)
    (fun y hy h0 x hx => h.B_eq_zero_right hK hc hy h0 hx)
  have hdU₁ : ∀ x ∈ U₁, d⁻¹ * x * d ∈ U₁ := fun x hx => by
    simpa using (mem_normalizer_iff.mp (inv_mem h.d_mem_U₁) x).mp hx
  obtain ⟨c, hc'⟩ := bilinear_eq_mul_sqrt_of_equivariant hK (by rw [h.hfa]; omega) D hμ
    fun s s' => by
      obtain ⟨x, hx, rfl⟩ := h.S_surj hK hc hκ s
      obtain ⟨y, hy, rfl⟩ := h.S_surj hK hc hκ s'
      rw [← h.S_conj_d hK hc hx, ← h.S_conj_d hK hc hy, ← hD _ (hdU₁ x hx) _ (hdU₁ y hy),
        ← hD x hx y hy]
      exact h.B_conj_d hK hc hx hy
  exact ⟨c, fun x hx y hy => by rw [hD x hx y hy, hc']⟩

end Coords


theorem comm_mem_szA₁ (h : SzC1Stage G L f a t T d V U U₁ k) :
    ∀ x ∈ U₁, ∀ y ∈ U₁, x * y * x⁻¹ * y⁻¹ ∈ szA₁ (szT₁ L T) := by
  obtain ⟨K, _, _, _, u, v, κ, hK, hc, hκ⟩ := h.coords
  have hK' := h.card_K hK hc
  obtain ⟨μ', hμ'⟩ := h.exists_mu hK hc hκ
  intro x hx y hy
  have hxU := h.U₁_le hx
  have hyU := h.U₁_le hy
  have hσx := h.comm_t_mem hxU
  have hσy := h.comm_t_mem hyU
  have hχx := h.conj_V₁ x hx _ hσy
  have hχy := h.conj_V₁ y hy _ hσx
  have hsym : (y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹) =
      (x * t * x⁻¹ * t⁻¹)⁻¹ * (y * (x * t * x⁻¹ * t⁻¹) * y⁻¹) :=
    hc.inj _ (szA₁_le _ hχx) _ (szA₁_le _ hχy)
      (by rw [hc.u_eq_zero_of_mem_szA₁ h.ha hK' hχx, hc.u_eq_zero_of_mem_szA₁ h.ha hK' hχy])
      (by rw [hμ' x hx y hy, hμ' y hy x hx, mul_comm (v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ k))])
  set c := x * y * x⁻¹ * y⁻¹ with hcdef
  have hcU₁ : c ∈ U₁ := mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  have hcV : ∀ r ∈ V, c * r * c⁻¹ = r := fun r hr =>
    SzC1.comm_conj_eq_of_dev h.szA₁_comm (h.conj_szA₁ x hxU) (h.conj_szA₁ y hyU)
      (h.conj_V₁ x hx r hr) (h.conj_V₁ y hy r hr)
  set P := (y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹) with hP
  have hPV : P ∈ V := h.le hχx
  have e1 : x * y * t * (x * y)⁻¹ * t⁻¹ = (y * t * y⁻¹ * t⁻¹) * P * (x * t * x⁻¹ * t⁻¹) := by
    rw [SzC1.comm_t_mul, hP]
    group
  have e2 : y * x * t * (y * x)⁻¹ * t⁻¹ = (x * t * x⁻¹ * t⁻¹) * P * (y * t * y⁻¹ * t⁻¹) := by
    rw [SzC1.comm_t_mul, hsym]
    group
  have e3 : (y * t * y⁻¹ * t⁻¹) * P * (x * t * x⁻¹ * t⁻¹) =
      (x * t * x⁻¹ * t⁻¹) * P * (y * t * y⁻¹ * t⁻¹) := by
    rw [mul_assoc, h.comm P hPV _ hσx, ← mul_assoc, h.comm _ hσy _ hσx, mul_assoc,
      h.comm _ hσy P hPV, ← mul_assoc]
  have e4 : x * y * t * (x * y)⁻¹ * t⁻¹ =
      (y * x * t * (y * x)⁻¹ * t⁻¹) * (c * t * c⁻¹ * t⁻¹) := by
    have h4 := SzC1.comm_t_mul c (y * x) t
    rw [show c * (y * x) = x * y by rw [hcdef]; group] at h4
    rw [h4, hcV _ (h.comm_t_mem (mul_mem hyU hxU))]
  rw [e1, e3, ← e2] at e4
  have hσc : c * t * c⁻¹ * t⁻¹ = 1 := (mul_eq_left.mp e4.symm)
  have hct : c * t = t * c := by
    calc c * t = (c * t * c⁻¹ * t⁻¹) * t * c := by group
      _ = t * c := by rw [hσc, one_mul]
  have hcT₁ := h.mem_T₁_of_comm hcU₁ hct
  refine mem_szA₁.mpr ⟨hcT₁, mem_centralizer_iff.mpr fun y₀ hy₀ => ?_⟩
  have h5 := SzC1.comm_conj_eq_of_dev h.szA₁_comm (h.conj_szA₁ x hxU) (h.conj_szA₁ y hyU)
    (h.conj_T₁ x hxU y₀ hy₀) (h.conj_T₁ y hyU y₀ hy₀)
  rw [← hcdef] at h5
  calc y₀ * c = (c * y₀ * c⁻¹) * c := by rw [h5]
    _ = c * y₀ := by group

theorem card_le_of_le_centralizer
    (h : SzC1Stage G L f a t T d V U U₁ k) {P : Subgroup G}
    (hP : P ≤ centralizer ({t} : Set G)) (hP2 : IsPGroup 2 P) :
    Nat.card P ≤ 2 * 2 ^ f * 2 ^ f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := h.start.sylow
  have hTcard : Nat.card T = 2 * 2 ^ f * 2 ^ f := h.start.facts.2.2.1
  have hP' : IsPGroup 2 (P.subgroupOf (centralizer ({t} : Set G))) :=
    hP2.of_equiv (subgroupOfEquivOfLe hP).symm
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  calc Nat.card P = Nat.card (P.subgroupOf (centralizer ({t} : Set G))) :=
        Nat.card_congr (subgroupOfEquivOfLe hP).toEquiv.symm
    _ ≤ Nat.card Q := Subgroup.card_le_of_le hQ
    _ = Nat.card P₀ := Nat.card_congr (Sylow.equiv Q P₀).toEquiv
    _ = Nat.card (T.subgroupOf (centralizer ({t} : Set G))) := by rw [hP₀]
    _ = Nat.card T := Nat.card_congr (subgroupOfEquivOfLe h.start.le).toEquiv
    _ = _ := hTcard

theorem conj_not_mem_U₁
    (h : SzC1Stage G L f a t T d V U U₁ k) (g : G) : g * t * g⁻¹ ∉ U₁ := by
  obtain ⟨K, _, _, _, u, v, κ, hK, hc, -⟩ := h.coords
  intro hx
  have hk := h.one_le_k hK hc
  have hbound := card_le_card_centralizer_mul_card_of_comm_mem (H := U₁)
    (A := szA₁ (szT₁ L T)) (x := g * t * g⁻¹) fun w hw => h.comm_mem_szA₁ w hw _ hx
  rw [h.card_U₁, h.card_szA₁ hK hc] at hbound
  set C := (centralizer ({g * t * g⁻¹} : Set G)).subgroupOf U₁ with hC
  set P : Subgroup G := C.map U₁.subtype with hPdef
  have hPcard : Nat.card P = Nat.card C := Subgroup.card_map_of_injective U₁.subtype_injective
  have hP2 : IsPGroup 2 P := h.isPGroup_U.to_le ((map_subtype_le C).trans h.U₁_le)
  have hPx : P ≤ centralizer ({g * t * g⁻¹} : Set G) := by
    rintro _ ⟨w, hw, rfl⟩
    exact mem_subgroupOf.mp hw
  have hq : 2 < 2 ^ f := by
    have ha := h.ha
    have hf : 2 ≤ f := by rw [h.hfa]; omega
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  have hq0 : 0 < 2 ^ f := by positivity
  have h1 : (2 ^ f) ^ (k + 2) ≤ Nat.card C := by
    have h2 : (2 ^ f) ^ (k + 2) * 2 ^ f ≤ Nat.card C * 2 ^ f := by rw [← pow_succ]; exact hbound
    exact Nat.le_of_mul_le_mul_right h2 hq0
  have h3 : 2 * 2 ^ f * 2 ^ f < (2 ^ f) ^ (k + 2) := by
    calc 2 * 2 ^ f * 2 ^ f < 2 ^ f * 2 ^ f * 2 ^ f := by
          have : 0 < 2 ^ f * 2 ^ f := by positivity
          nlinarith
      _ = (2 ^ f) ^ 3 := by ring
      _ ≤ (2 ^ f) ^ (k + 2) := Nat.pow_le_pow_right hq0 (by omega)
  exact not_conj_of_card_lt (fun Q hQ hQ2 => h.card_le_of_le_centralizer hQ hQ2) hP2 hPx
    (by rw [hPcard]; omega) g rfl

theorem false_of_isSylow
    (h : SzC1Stage G L f a t T d V U U₁ k) (hU : ∃ S : Sylow 2 G, (S : Subgroup G) = U) :
    False := by
  have : IsSimpleGroup G := h.start.setting.1
  obtain ⟨S, hS⟩ := hU
  exact RankOne.Endings.not_exists_normal_index_two h.start.setting.2.1
    (CFSG.SeitzReduction.exists_normal_index_two_of_not_fused_of_sylow_le h.start.inv
      h.t_mem_normalizer_U₁ h.t_not_mem ⟨S, by rw [hS, h.sup_eq]⟩
      fun g hg => h.conj_not_mem_U₁ g⁻¹ (by simpa using hg))


theorem sq_mem_V (h : SzC1Stage G L f a t T d V U U₁ k) {x : G} (hx : x ∈ U₁) : x ^ 2 ∈ V := by
  obtain ⟨K, _, _, _, u, v, κ, hK, hc, -⟩ := h.coords
  have hK' := h.card_K hK hc
  have hxU := h.U₁_le hx
  have hS : v ((x * x * t * (x * x)⁻¹ * t⁻¹) ^ 2 ^ k) = 0 := by
    rw [h.S_mul hK hc hx hx, CharTwo.add_self_eq_zero]
  obtain ⟨y, hy, r, hr, hyr⟩ :=
    h.exists_mul_of_mem_sup (h.mem_sup_of_S_eq_zero hK hc (mul_mem hx hx) hS)
  have hcent : ∀ y₀ ∈ szT₁ L T, y₀ * (x * x) = x * x * y₀ := by
    intro y₀ hy₀
    have e := h.delta_mul_left hxU hxU hy₀
    have hδ := hc.sq_eq_one_of_mem_szA₁ h.ha hK' (h.conj_T₁ x hxU y₀ hy₀)
    rw [sq] at hδ
    rw [hδ] at e
    have e2 : x * x * y₀ * (x * x)⁻¹ = y₀ := by
      calc x * x * y₀ * (x * x)⁻¹ = y₀ * (y₀⁻¹ * (x * x * y₀ * (x * x)⁻¹)) := by group
        _ = y₀ := by rw [e, mul_one]
    calc y₀ * (x * x) = (x * x * y₀ * (x * x)⁻¹) * (x * x) := by rw [e2]
      _ = x * x * y₀ := by group
  have hy' : y = x * x * r⁻¹ := by rw [hyr]; group
  have hyA : y ∈ szA₁ (szT₁ L T) := by
    refine mem_szA₁.mpr ⟨hy, mem_centralizer_iff.mpr fun y₀ hy₀ => ?_⟩
    calc y₀ * y = y₀ * (x * x) * r⁻¹ := by rw [hy']; group
      _ = x * x * y₀ * r⁻¹ := by rw [hcent y₀ hy₀]
      _ = x * x * (y₀ * r⁻¹) := by group
      _ = x * x * (r⁻¹ * y₀) := by rw [h.V_comm (inv_mem hr) hy₀]
      _ = y * y₀ := by rw [hy']; group
  rw [sq, hyr]
  exact mul_mem (h.le hyA) hr

section Coords

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {u v : G → K} {κ : K}
  (h : SzC1Stage G L f a t T d V U U₁ k) (hK : Fintype.card K = 2 ^ f)
  (hc : SzRootCoords (szT₁ L T) a d u v κ)
include h hK hc

theorem mu_eq_zero_or_one (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w) :
    ∃ μ' : K, (μ' = 0 ∨ μ' = 1) ∧ (2 ≤ k → μ' = 0) ∧ ∀ x ∈ U₁, ∀ y ∈ U₁,
      v ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹)) =
        μ' * (v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ k) * v ((y * t * y⁻¹ * t⁻¹) ^ 2 ^ k)) ^ 2 ^ (f - 1) := by
  have hK' := h.card_K hK hc
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨μ', hμ'⟩ := h.exists_mu hK hc hκ
  obtain ⟨u₀, hu₀, hS1⟩ := h.S_surj hK hc hκ 1
  have hsqV := h.sq_mem_V hu₀
  obtain ⟨y₀, hy₀, hy₀σ⟩ := h.exists_comm_t_eq hK hc hκ hsqV
  have hB0 := hμ' u₀ hu₀ y₀ hy₀
  rw [hy₀σ, show u₀ * u₀ ^ 2 * u₀⁻¹ = u₀ ^ 2 by group, inv_mul_cancel, hc.v_one, hS1,
    one_mul] at hB0
  have hσuV := h.comm_t_mem (h.U₁_le hu₀)
  obtain ⟨σu, hσu⟩ : ∃ σu, σu = u₀ * t * u₀⁻¹ * t⁻¹ := ⟨_, rfl⟩
  rw [← hσu] at hσuV hS1
  have hχA : σu⁻¹ * (u₀ * σu * u₀⁻¹) ∈ szA₁ (szT₁ L T) := h.conj_V₁ u₀ hu₀ σu hσuV
  have hBuu := hμ' u₀ hu₀ u₀ hu₀
  rw [← hσu, hS1, one_mul, one_pow, mul_one] at hBuu
  have e1 : (u₀ ^ 2) ^ 2 = σu ^ 2 * (σu⁻¹ * (u₀ * σu * u₀⁻¹)) := by
    rw [← h.comm_t_of_mem_V hsqV, sq u₀, SzC1.comm_t_mul, ← hσu]
    rw [show u₀ * σu * u₀⁻¹ * σu = σu * (σu⁻¹ * (u₀ * σu * u₀⁻¹)) * σu by group, mul_assoc,
      h.comm _ (h.le hχA) σu hσuV, ← mul_assoc, ← sq]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := h.one_le_k hK hc; omega⟩
  have e2 : (u₀ ^ 2) ^ 2 ^ (j + 1) =
      σu ^ 2 ^ (j + 1) * (σu⁻¹ * (u₀ * σu * u₀⁻¹)) ^ 2 ^ j := by
    calc (u₀ ^ 2) ^ 2 ^ (j + 1) = ((u₀ ^ 2) ^ 2) ^ 2 ^ j := by
          rw [← pow_mul (u₀ ^ 2) 2 (2 ^ j), ← pow_succ']
      _ = _ := by
        rw [e1, (Commute.mul_pow (h.comm _ (pow_mem hσuV 2) _ (h.le hχA)) _), ← pow_mul,
          ← pow_succ']
  rw [e2] at hB0
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    simp only [zero_add, pow_zero, pow_one] at hB0 hS1
    have hσ2 : σu ^ 2 ∈ szA₁ (szT₁ L T) := by simpa using h.pow_mem_szA₁ hσuV
    rw [hc.v_mul_szA₁ h.ha hK' hσ2 hχA, hS1, hBuu] at hB0
    refine ⟨μ', ?_, fun h2 => absurd h2 (by norm_num), hμ'⟩
    rcases mul_eq_zero.mp hB0.symm with h0 | h0
    · exact Or.inl h0
    · right
      have h3 := pow_eq_zero_iff ((pow_ne_zero (f - 1) two_ne_zero)) |>.mp h0
      linear_combination h3 - h2K
  · have hχ1 : (σu⁻¹ * (u₀ * σu * u₀⁻¹)) ^ 2 ^ j = 1 := by
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rw [pow_succ', pow_mul, hc.sq_eq_one_of_mem_szA₁ h.ha hK' hχA, one_pow]
    rw [hχ1, mul_one, hS1, one_pow, mul_one] at hB0
    exact ⟨μ', Or.inl hB0.symm, fun _ => hB0.symm, hμ'⟩

theorem mem_sup_of_mem_centralizer_V' (hκ : ∀ w : K, w ≠ 0 → ∃ m : ℕ, κ ^ m = w)
    (hμ : ¬ U₁ ≤ centralizer (V : Set G)) {w : G} (hw : w ∈ U₁)
    (hwV : w ∈ centralizer (V : Set G)) : w ∈ szT₁ L T ⊔ V := by
  have hK' := h.card_K hK hc
  obtain ⟨μ', hμ01, -, hμ'⟩ := h.mu_eq_zero_or_one hK hc hκ
  rcases hμ01 with h0 | h1
  · refine absurd (fun x hx => mem_centralizer_iff.mpr fun r hr => ?_) hμ
    obtain ⟨y, hy, rfl⟩ := h.exists_comm_t_eq hK hc hκ hr
    have e := hμ' x hx y hy
    rw [h0, zero_mul] at e
    have e1 := hc.eq_one_of_v_eq_zero h.ha hK' (h.conj_V₁ x hx _ (h.comm_t_mem (h.U₁_le hy))) e
    calc (y * t * y⁻¹ * t⁻¹) * x =
          (y * t * y⁻¹ * t⁻¹) * ((y * t * y⁻¹ * t⁻¹)⁻¹ * (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹)) * x := by
          rw [e1, mul_one]
      _ = x * (y * t * y⁻¹ * t⁻¹) := by group
  · obtain ⟨y, hy, hS1⟩ := h.S_surj hK hc hκ 1
    have e := hμ' w hw y hy
    have hc1 : (y * t * y⁻¹ * t⁻¹)⁻¹ * (w * (y * t * y⁻¹ * t⁻¹) * w⁻¹) = 1 := by
      rw [← mem_centralizer_iff.mp hwV _ (h.comm_t_mem (h.U₁_le hy))]
      group
    rw [hc1, hc.v_one, h1, one_mul, hS1, mul_one] at e
    exact h.mem_sup_of_S_eq_zero hK hc hw ((pow_eq_zero_iff (pow_ne_zero _ two_ne_zero)).mp e.symm)

end Coords

theorem mem_sup_of_mem_centralizer_V (h : SzC1Stage G L f a t T d V U U₁ k)
    (hμ : ¬ U₁ ≤ centralizer (V : Set G)) {w : G} (hw : w ∈ U₁)
    (hwV : w ∈ centralizer (V : Set G)) : w ∈ szT₁ L T ⊔ V := by
  obtain ⟨K, _, _, _, u, v, κ, hK, hc, hκ⟩ := h.coords
  exact h.mem_sup_of_mem_centralizer_V' hK hc hκ hμ hw hwV

end SzC1Stage

end CFSG.SeitzReduction.RankOne
