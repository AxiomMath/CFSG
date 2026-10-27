module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.CGT.Stroth76.TModel
public import CFSG.CGT.Stroth77.Extension22

public section

namespace CFSG.CGT.Stroth76

open CFSG.CGT.Stroth77 CFSG.CGT.Stroth77.Arch76

@[expose] def torusToCo (y : Torus (Type100.k 1)) : Co := (y 0, y 1, y 2)

theorem torusToCo_add (y y' : Torus (Type100.k 1)) :
    torusToCo (y + y') = torusToCo y + torusToCo y' := rfl

theorem torusToCo_injective : Function.Injective torusToCo := by
  intro y y' h
  have h0 : y 0 = y' 0 := congrArg (fun p : Co => p.1) h
  have h1 : y 1 = y' 1 := congrArg (fun p : Co => p.2.1) h
  have h2 : y 2 = y' 2 := congrArg (fun p : Co => p.2.2) h
  funext i
  fin_cases i
  exacts [h0, h1, h2]

theorem torusToCo_φuv : ∀ y : Torus (Type100.k 1),
    torusToCo ((StrothTypeIndex.t100 1).action.φuv y) = fuv (torusToCo y) := by decide +kernel

theorem torusToCo_φt : ∀ y : Torus (Type100.k 1),
    torusToCo ((StrothTypeIndex.t100 1).action.φt y) = ft (torusToCo y) := by decide +kernel

theorem torusToCo_φu : ∀ y : Torus (Type100.k 1),
    torusToCo ((StrothTypeIndex.t100 1).action.φu y) = fu (torusToCo y) := by decide +kernel

theorem torusToCo_φρ : ∀ y : Torus (Type100.k 1),
    torusToCo ((StrothTypeIndex.t100 1).action.φρ y) = fρ (torusToCo y) := by decide +kernel

theorem fρ_surjective : Function.Surjective fρ := by
  intro v
  refine ⟨fρ (fρ v), ?_⟩
  revert v
  decide +kernel

theorem fρ_cube : ∀ v : Co, fρ (fρ (fρ v)) = v := by decide +kernel

theorem fuv_surjective : Function.Surjective fuv := fun v => ⟨fuv v, by revert v; decide +kernel⟩
theorem ft_surjective : Function.Surjective ft := fun v => ⟨ft v, by revert v; decide +kernel⟩
theorem fu_surjective : Function.Surjective fu := fun v => ⟨fu v, by revert v; decide +kernel⟩

theorem torusToCo_c : torusToCo (Torus.c : Torus (Type100.k 1)) = (1, 0, 0) := by decide
theorem torusToCo_a : torusToCo (Torus.a : Torus (Type100.k 1)) = (0, 1, 0) := by decide
theorem torusToCo_b : torusToCo (Torus.b : Torus (Type100.k 1)) = (0, 0, 1) := by decide

section Data

variable {X : Type*} [Group X] (K : Config X)

theorem mem_normalizer_A_of_conj_ev {g : X} {f : Co → Co}
    (hf : ∀ v, g⁻¹ * K.ev v * g = K.ev (f v)) (hsurj : Function.Surjective f) :
    g ∈ Subgroup.normalizer (K.A : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨v, rfl⟩ := K.exists_ev hh
    obtain ⟨v', rfl⟩ := hsurj v
    rw [← hf v', show g * (g⁻¹ * K.ev v' * g) * g⁻¹ = K.ev v' by group]
    exact K.ev_mem v'
  · intro hh
    obtain ⟨v, hv⟩ := K.exists_ev hh
    rw [show h = g⁻¹ * (g * h * g⁻¹) * g by group, ← hv, hf]
    exact K.ev_mem _

theorem uv_mem_normalizer_A : K.uv ∈ Subgroup.normalizer (K.A : Set X) :=
  (mem_normalizer_A_of_conj_ev K) K.conj_uv_ev fuv_surjective
theorem t_mem_normalizer_A : K.t ∈ Subgroup.normalizer (K.A : Set X) :=
  (mem_normalizer_A_of_conj_ev K) K.conj_t_ev ft_surjective
theorem u_mem_normalizer_A : K.u ∈ Subgroup.normalizer (K.A : Set X) :=
  (mem_normalizer_A_of_conj_ev K) K.conj_u_ev fu_surjective
theorem ρ_mem_normalizer_A : K.ρ ∈ Subgroup.normalizer (K.A : Set X) :=
  (mem_normalizer_A_of_conj_ev K) K.conj_ρ_ev fρ_surjective

theorem rho_cube_mem_centralizer :
    K.ρ * K.ρ * K.ρ ∈ Subgroup.centralizer (K.A : Set X) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  obtain ⟨v, rfl⟩ := K.exists_ev ha
  have h : (K.ρ * K.ρ * K.ρ)⁻¹ * K.ev v * (K.ρ * K.ρ * K.ρ) = K.ev v := by
    calc (K.ρ * K.ρ * K.ρ)⁻¹ * K.ev v * (K.ρ * K.ρ * K.ρ)
        = K.ρ⁻¹ * (K.ρ⁻¹ * (K.ρ⁻¹ * K.ev v * K.ρ) * K.ρ) * K.ρ := by group
      _ = K.ev v := by rw [K.conj_ρ_ev, K.conj_ρ_ev, K.conj_ρ_ev, fρ_cube]
  calc K.ev v * (K.ρ * K.ρ * K.ρ)
      = (K.ρ * K.ρ * K.ρ) * ((K.ρ * K.ρ * K.ρ)⁻¹ * K.ev v * (K.ρ * K.ρ * K.ρ)) := by group
    _ = (K.ρ * K.ρ * K.ρ) * K.ev v := by rw [h]

theorem rho_cube_eq_one [Finite X] (hρodd : Odd (orderOf K.ρ)) {n : ℕ}
    (hC : Nat.card (Subgroup.centralizer (K.A : Set X)) ∣ 2 ^ n) :
    K.ρ * K.ρ * K.ρ = 1 := by
  have h1 : orderOf (K.ρ * K.ρ * K.ρ) ∣ 2 ^ n :=
    (Subgroup.orderOf_dvd_natCard _ (rho_cube_mem_centralizer K)).trans hC
  have h2 : orderOf (K.ρ * K.ρ * K.ρ) ∣ orderOf K.ρ := by
    rw [show K.ρ * K.ρ * K.ρ = K.ρ ^ 3 by rw [pow_three, mul_assoc]]
    exact orderOf_pow_dvd 3
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  rcases j with _ | j
  · have h0 : orderOf (K.ρ * K.ρ * K.ρ) = 1 := by rw [hj, pow_zero]
    exact orderOf_eq_one_iff.mp h0
  · exfalso
    rw [hj] at h2
    exact (Nat.not_even_iff_odd.mpr hρodd)
      (even_iff_two_dvd.mpr ((dvd_pow_self 2 (Nat.succ_ne_zero j)).trans h2))

@[expose] noncomputable def torusHomA : Torus (Type100.k 1) →+ Additive K.A :=
  AddMonoidHom.mk' (fun y => Additive.ofMul (K.evA (torusToCo y))) (fun y y' => by
    rw [torusToCo_add, K.evA_add]; rfl)

theorem coe_torusHomA (y : Torus (Type100.k 1)) :
    ((Additive.toMul ((torusHomA K) y) : K.A) : X) = K.ev (torusToCo y) := by
  simp [torusHomA, Config.coe_evA]

theorem torusHomA_bijective : Function.Bijective (torusHomA K) := by
  haveI : Finite K.A := Nat.finite_of_card_ne_zero (by rw [K.hAcard]; norm_num)
  haveI : Finite (Additive K.A) := Finite.of_equiv _ Additive.ofMul
  refine Function.Injective.bijective_of_nat_card_le ?_ ?_
  · intro y y' h
    apply torusToCo_injective
    apply K.ev_injective
    rw [← coe_torusHomA, ← coe_torusHomA, h]
  · rw [natCard_torus, Nat.card_congr Additive.toMul, K.hAcard]
    decide

@[expose] noncomputable def torusEquivA : Torus (Type100.k 1) ≃+ Additive K.A :=
  AddEquiv.ofBijective (torusHomA K) (torusHomA_bijective K)

theorem coe_torusEquivA (y : Torus (Type100.k 1)) :
    ((Additive.toMul ((torusEquivA K) y) : K.A) : X) = K.ev (torusToCo y) :=
  (coe_torusHomA K) y

theorem torusEquivA_symm_conjBy {g : X} (hg : g ∈ Subgroup.normalizer (K.A : Set X))
    {φ : Torus (Type100.k 1) →+ Torus (Type100.k 1)} {f : Co → Co}
    (hf : ∀ v, g⁻¹ * K.ev v * g = K.ev (f v)) (hφ : ∀ y, torusToCo (φ y) = f (torusToCo y))
    (x : K.A) :
    (torusEquivA K).symm (Additive.ofMul (conjBy hg x)) =
      φ ((torusEquivA K).symm (Additive.ofMul x)) := by
  apply (torusEquivA K).injective
  rw [AddEquiv.apply_symm_apply]
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [toMul_ofMul, coe_torusEquivA, hφ, ← hf]
  have hx : ((Additive.toMul ((torusEquivA K) ((torusEquivA K).symm (Additive.ofMul x))) : K.A) : X) =
      (x : X) := by
    rw [AddEquiv.apply_symm_apply, toMul_ofMul]
  rw [coe_torusEquivA] at hx
  simp [conjBy, hx]

@[expose] noncomputable def dataA (hρ3 : K.ρ * K.ρ * K.ρ = 1) :
    StrothTypeData K.A (StrothTypeIndex.t100 1) where
  e := (torusEquivA K).symm
  uv := K.uv
  t := K.t
  u := K.u
  ρ := K.ρ
  uv_sq := uv_mul_self K
  t_sq := t_mul_self K
  uv_comm_t := K.huvt
  rho_cube := hρ3
  u_sq := u_mul_self K
  u_rho := by
    have h : K.u * K.ρ * K.u = K.ρ⁻¹ := by
      have := K.hρu
      rwa [u_inv K] at this
    rw [h, inv_mul_cancel]
  uv_rho := by
    have h := K.hρuv
    calc K.uv * K.ρ = K.ρ * (K.ρ⁻¹ * K.uv * K.ρ) := by group
      _ = K.ρ * K.t := by rw [h]
  t_rho := by
    have h := K.hρt
    calc K.t * K.ρ = K.ρ * (K.ρ⁻¹ * K.t * K.ρ) := by group
      _ = K.ρ * K.uv * K.t := by rw [h]; group
  uv_comm_u := K.huvu
  t_u := by
    have h := K.htu
    calc K.t * K.u = K.u * (K.u⁻¹ * K.t * K.u) := by group
      _ = K.u * K.uv * K.t := by rw [h]; group
  uv_mem := (uv_mem_normalizer_A K)
  t_mem := (t_mem_normalizer_A K)
  u_mem := (u_mem_normalizer_A K)
  ρ_mem := (ρ_mem_normalizer_A K)
  uv_conj := (torusEquivA_symm_conjBy K) _ K.conj_uv_ev torusToCo_φuv
  t_conj := (torusEquivA_symm_conjBy K) _ K.conj_t_ev torusToCo_φt
  u_conj := (torusEquivA_symm_conjBy K) _ K.conj_u_ev torusToCo_φu
  ρ_conj := (torusEquivA_symm_conjBy K) _ K.conj_ρ_ev torusToCo_φρ

variable {K}

theorem dataA_c (hρ3 : K.ρ * K.ρ * K.ρ = 1) : (((dataA K) hρ3).c : X) = K.w := by
  show ((Additive.toMul ((torusEquivA K) Torus.c) : K.A) : X) = K.w
  rw [coe_torusEquivA, torusToCo_c]
  simp [Config.ev, show (1 : ZMod 2).val = 1 from rfl]

theorem dataA_a (hρ3 : K.ρ * K.ρ * K.ρ = 1) : (((dataA K) hρ3).a : X) = K.x := by
  show ((Additive.toMul ((torusEquivA K) Torus.a) : K.A) : X) = K.x
  rw [coe_torusEquivA, torusToCo_a]
  simp [Config.ev, show (1 : ZMod 4).val = 1 from rfl]

theorem dataA_b (hρ3 : K.ρ * K.ρ * K.ρ = 1) : (((dataA K) hρ3).b : X) = K.y := by
  show ((Additive.toMul ((torusEquivA K) Torus.b) : K.A) : X) = K.y
  rw [coe_torusEquivA, torusToCo_b]
  simp [Config.ev, show (1 : ZMod 4).val = 1 from rfl]

theorem dataA_L (hρ3 : K.ρ * K.ρ * K.ρ = 1) :
    ((dataA K) hρ3).L = Subgroup.closure {K.uv, K.t, K.u, K.ρ} := rfl

end Data

end CFSG.CGT.Stroth76
