module

public import CFSG.Quasithin.Background.B19Basic
public import CFSG.Quasithin.Background.D2Coprime

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin

variable {V : Type} [CommGroup V]

theorem le_stabSub_of_commV_le {X : Subgroup (MulAut V)} {U : Subgroup V} (h : commV X ≤ U) :
    X ≤ stabSub U := by
  intro x hx u
  have hc : x u * u⁻¹ ∈ U := h (Subgroup.subset_closure ⟨x, hx, u, rfl⟩)
  constructor
  · intro hu
    have hu' : u = (x u * u⁻¹)⁻¹ * x u := by group
    rw [hu']
    exact U.mul_mem (U.inv_mem hc) hu
  · intro hu
    have hu' : x u = x u * u⁻¹ * u := by group
    rw [hu']
    exact U.mul_mem hc hu

theorem inf_centSub_eq_bot_of_commV_le (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    {U : Subgroup V} (hX : IsPGroup 3 X) (h : commV X ≤ U) : X ⊓ centSub U = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  obtain ⟨hxX, hxU⟩ := Subgroup.mem_inf.1 hx
  have h2 : x ^ 2 = 1 := by
    ext v
    have hc : x v * v⁻¹ ∈ U := h (Subgroup.subset_closure ⟨x, hxX, v, rfl⟩)
    have h1 : x (x v * v⁻¹) = x v * v⁻¹ := (mem_centSub.1 hxU) _ hc
    rw [map_mul, map_inv, mul_inv_eq_iff_eq_mul] at h1
    have hv : v⁻¹ = v := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hV])
    rw [pow_two, MulAut.mul_apply, MulAut.one_apply, h1, mul_right_comm, ← pow_two, hV,
      one_mul, hv]
  obtain ⟨k, hk⟩ := hX ⟨x, hxX⟩
  have hk' : x ^ (3 ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨j, hj⟩ : Odd (3 ^ k) := Odd.pow (by decide)
  rwa [hj, pow_succ, pow_mul, h2, one_pow, one_mul] at hk'

theorem card_dvd_card_mulAut_of_commV_le (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    {U : Subgroup V} (hX : IsPGroup 3 X) (h : commV X ≤ U) :
    Nat.card X ∣ Nat.card (MulAut U) := by
  have h1 := card_autSub_mul (le_stabSub_of_commV_le h)
  rw [inf_centSub_eq_bot_of_commV_le hV hX h, Subgroup.card_bot, mul_one] at h1
  rw [← h1]
  exact Subgroup.card_subgroup_dvd_card _

theorem rk_eq_two_of_card_eq_four {W : Subgroup V} (h : Nat.card W = 4) : rk W = 2 := by
  unfold rk
  rw [h]
  show padicValNat 2 (2 ^ 2) = 2
  exact padicValNat.prime_pow 2

theorem three_pow_dvd_of_dvd_card_gl {n r : ℕ} (hr : r ≤ 4)
    (h : 3 ^ n ∣ ∏ i : Fin r, (2 ^ r - 2 ^ (i : ℕ))) : 3 ^ n ∣ 9 ∧ (r ≤ 3 → 3 ^ n ∣ 3) := by
  have c2 : (3 ^ n).Coprime 2 := Nat.Coprime.pow_left n (by norm_num)
  have c56 : (3 ^ n).Coprime 56 := Nat.Coprime.pow_left n (by norm_num)
  have c2240 : (3 ^ n).Coprime 2240 := Nat.Coprime.pow_left n (by norm_num)
  have h39 : (3 : ℕ) ∣ 9 := by norm_num
  interval_cases r
  · have h1 : 3 ^ n ∣ 1 := by simpa using h
    exact ⟨h1.trans (one_dvd _), fun _ => h1.trans (one_dvd _)⟩
  · have h1 : 3 ^ n ∣ 1 := by simpa using h
    exact ⟨h1.trans (one_dvd _), fun _ => h1.trans (one_dvd _)⟩
  · have h1 : 3 ^ n ∣ 3 * 2 := by
      have h6 : ∏ i : Fin 2, (2 ^ 2 - 2 ^ (i : ℕ)) = 3 * 2 := by decide
      rwa [h6] at h
    have h3 := c2.dvd_of_dvd_mul_right h1
    exact ⟨h3.trans h39, fun _ => h3⟩
  · have h1 : 3 ^ n ∣ 3 * 56 := by
      have h6 : ∏ i : Fin 3, (2 ^ 3 - 2 ^ (i : ℕ)) = 3 * 56 := by decide
      rwa [h6] at h
    have h3 := c56.dvd_of_dvd_mul_right h1
    exact ⟨h3.trans h39, fun _ => h3⟩
  · have h1 : 3 ^ n ∣ 9 * 2240 := by
      have h6 : ∏ i : Fin 4, (2 ^ 4 - 2 ^ (i : ℕ)) = 9 * 2240 := by decide
      rwa [h6] at h
    exact ⟨c2240.dvd_of_dvd_mul_right h1, fun h4 => absurd h4 (by norm_num)⟩

theorem commV_le_fixV_of_commute {X Y : Subgroup (MulAut V)} (hXY : commV X ⊓ commV Y = ⊥)
    (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) : commV X ≤ fixV Y := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨x, hx, v, rfl⟩
  rw [SetLike.mem_coe, mem_fixV]
  intro y hy
  have h1 : y (x v * v⁻¹) * (x v * v⁻¹)⁻¹ ∈ commV X := by
    have hyx : y (x v) = x (y v) := by
      rw [← MulAut.mul_apply, ← hc x hx y hy, MulAut.mul_apply]
    rw [map_mul, map_inv, hyx]
    exact (commV X).mul_mem (Subgroup.subset_closure ⟨x, hx, y v, rfl⟩)
      ((commV X).inv_mem (Subgroup.subset_closure ⟨x, hx, v, rfl⟩))
  have h2 : y (x v * v⁻¹) * (x v * v⁻¹)⁻¹ ∈ commV Y :=
    Subgroup.subset_closure ⟨y, hy, _, rfl⟩
  have h3 : y (x v * v⁻¹) * (x v * v⁻¹)⁻¹ ∈ commV X ⊓ commV Y := Subgroup.mem_inf.2 ⟨h1, h2⟩
  rw [hXY, Subgroup.mem_bot] at h3
  exact mul_inv_eq_one.1 h3

variable [Finite V]

theorem conj_three_commute (hV : ∀ v : V, v ^ 2 = 1)
    {N E₁ E₂ : Subgroup (MulAut V)} (hN : IsPGroup 3 N) (h₁ : E₁ ≤ N) (h₂ : E₂ ≤ N)
    (hc₁ : Nat.card E₁ = 3) (hc₂ : Nat.card E₂ = 3)
    (hW₁ : Nat.card (commV E₁) = 4) (hW₂ : Nat.card (commV E₂) = 4) (hne : E₁ ≠ E₂) :
    commV E₁ ⊓ commV E₂ = ⊥ ∧ commV E₂ ≤ fixV E₁ ∧ commV E₁ ≤ fixV E₂ ∧
      ∀ x ∈ E₁, ∀ y ∈ E₂, x * y = y * x := by
  have hLp : IsPGroup 3 ↥(E₁ ⊔ E₂) := hN.to_le (sup_le h₁ h₂)
  have hdvd := card_dvd_card_mulAut_of_commV_le hV hLp (B19.commV_sup E₁ E₂).le
  rw [card_mulAut_eq (fun u => Subtype.ext (hV u))] at hdvd
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hLp
  rw [hn] at hdvd
  have hr := rk_sup_add_rk_inf (commV E₁) (commV E₂)
  rw [rk_eq_two_of_card_eq_four hW₁, rk_eq_two_of_card_eq_four hW₂] at hr
  have hr' : rk ↥(commV E₁ ⊔ commV E₂) ≤ 4 := by omega
  obtain ⟨h9, h3⟩ := three_pow_dvd_of_dvd_card_gl hr' hdvd
  have hsmall : ¬ 3 ^ n ∣ 3 := by
    intro h
    rw [← hn] at h
    have hle := Nat.le_of_dvd (by norm_num) h
    have e₁ := Subgroup.eq_of_le_of_card_ge (le_sup_left : E₁ ≤ E₁ ⊔ E₂) (by rw [hc₁]; exact hle)
    have e₂ := Subgroup.eq_of_le_of_card_ge (le_sup_right : E₂ ≤ E₁ ⊔ E₂) (by rw [hc₂]; exact hle)
    exact hne (e₁.trans e₂.symm)
  have hr4 : rk ↥(commV E₁ ⊔ commV E₂) = 4 := by
    by_contra h4
    exact hsmall (h3 (by omega))
  have hinf : commV E₁ ⊓ commV E₂ = ⊥ := (rk_eq_zero_iff hV).1 (by omega)
  have hn2 : n = 2 := by
    have h2 : n ≤ 2 :=
      (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).1 (show 3 ^ n ∣ 3 ^ 2 from h9)
    have h0 : n ≠ 0 := by rintro rfl; exact hsmall (by norm_num)
    have h1 : n ≠ 1 := by rintro rfl; exact hsmall (by norm_num)
    omega
  have hcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (hn.trans (by rw [hn2]))
  have hxy : ∀ x ∈ E₁, ∀ y ∈ E₂, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (hcomm.is_comm.comm (⟨x, Subgroup.mem_sup_left hx⟩ : ↥(E₁ ⊔ E₂))
      ⟨y, Subgroup.mem_sup_right hy⟩)
  exact ⟨hinf, commV_le_fixV_of_commute (by rw [inf_comm]; exact hinf)
    (fun y hy x hx => (hxy x hx y hy).symm), commV_le_fixV_of_commute hinf hxy, hxy⟩
