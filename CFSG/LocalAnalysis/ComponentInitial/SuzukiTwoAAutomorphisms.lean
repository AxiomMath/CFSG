module

public import CFSG.LocalAnalysis.ComponentInitial.SuzukiTwoA
public import CFSG.LocalAnalysis.ComponentInitial.TwistedProductRigidity

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open BinExt
open scoped commutatorElement

variable {K : Type*} [Field K] [Module (ZMod 2) K] {φ : K ≃+* K}

theorem suzukiA_mul_fst (p q : SuzukiA K φ) : (p * q).fst = p.fst + q.fst := rfl

theorem suzukiA_mul_snd (p q : SuzukiA K φ) :
    (p * q).snd = p.snd + q.snd + p.fst * φ q.fst := rfl

theorem suzukiA_eq_mul (p : SuzukiA K φ) :
    p = (⟨p.fst, 0⟩ : SuzukiA K φ) * ⟨0, p.snd⟩ := by
  refine BinExt.ext ?_ ?_
  · change p.fst = p.fst + 0
    rw [add_zero]
  · change p.snd = 0 + p.snd + p.fst * φ 0
    rw [map_zero, mul_zero, zero_add, add_zero]

theorem suzukiA_sq_eq_one_iff (p : SuzukiA K φ) : p ^ 2 = 1 ↔ p.fst = 0 := by
  rw [sq_def, one_def]
  constructor
  · intro h
    have h' : p.fst * φ p.fst = 0 := (BinExt.mk.inj h).2
    rcases mul_eq_zero.1 h' with h0 | h0
    · exact h0
    · exact (map_eq_zero_iff φ φ.injective).1 h0
  · intro h
    refine BinExt.ext rfl ?_
    change p.fst * φ p.fst = 0
    rw [h, zero_mul]

theorem aut_fst_eq_zero (α : MulAut (SuzukiA K φ)) {p : SuzukiA K φ} (hp : p.fst = 0) :
    (α p).fst = 0 := by
  rw [← suzukiA_sq_eq_one_iff] at hp ⊢
  rw [← map_pow, hp, map_one]

theorem aut_fst_congr (α : MulAut (SuzukiA K φ)) {p q : SuzukiA K φ} (h : p.fst = q.fst) :
    (α p).fst = (α q).fst := by
  have hpq : (q⁻¹ * p).fst = 0 := by
    change q.fst + p.fst = 0
    rw [h]
    exact add_self_zmod q.fst
  rw [← mul_inv_cancel_left q p, map_mul, suzukiA_mul_fst, aut_fst_eq_zero α hpq, add_zero]

@[expose] def suzukiQuotFun (α : MulAut (SuzukiA K φ)) (x : K) : K :=
  (α ⟨x, 0⟩).fst

theorem suzukiQuotFun_fst (α : MulAut (SuzukiA K φ)) (p : SuzukiA K φ) :
    suzukiQuotFun α p.fst = (α p).fst :=
  aut_fst_congr α rfl

theorem suzukiQuotFun_mul (α β : MulAut (SuzukiA K φ)) (x : K) :
    suzukiQuotFun (α * β) x = suzukiQuotFun α (suzukiQuotFun β x) :=
  (suzukiQuotFun_fst α (β ⟨x, 0⟩)).symm

theorem suzukiQuotFun_one (x : K) : suzukiQuotFun (1 : MulAut (SuzukiA K φ)) x = x :=
  rfl

theorem suzukiQuotFun_add (α : MulAut (SuzukiA K φ)) (x y : K) :
    suzukiQuotFun α (x + y) = suzukiQuotFun α x + suzukiQuotFun α y := by
  rw [show x + y = ((⟨x, 0⟩ : SuzukiA K φ) * ⟨y, 0⟩).fst from rfl, suzukiQuotFun_fst, map_mul,
    suzukiA_mul_fst]
  rfl

@[expose] def suzukiQuotLin (α : MulAut (SuzukiA K φ)) : K →ₗ[ZMod 2] K :=
  AddMonoidHom.toZModLinearMap 2 (AddMonoidHom.mk' (suzukiQuotFun α) (suzukiQuotFun_add α))

@[expose] def suzukiQuotAction :
    MulAut (SuzukiA K φ) →* LinearMap.GeneralLinearGroup (ZMod 2) K where
  toFun α :=
    { val := suzukiQuotLin α
      inv := suzukiQuotLin α⁻¹
      val_inv := LinearMap.ext fun x => by
        change suzukiQuotFun α (suzukiQuotFun α⁻¹ x) = x
        rw [← suzukiQuotFun_mul, mul_inv_cancel]
        rfl
      inv_val := LinearMap.ext fun x => by
        change suzukiQuotFun α⁻¹ (suzukiQuotFun α x) = x
        rw [← suzukiQuotFun_mul, inv_mul_cancel]
        rfl }
  map_one' := Units.ext (LinearMap.ext fun _ => rfl)
  map_mul' α β := Units.ext (LinearMap.ext fun x => suzukiQuotFun_mul α β x)

theorem suzukiQuotAction_apply (α : MulAut (SuzukiA K φ)) (x : K) :
    (suzukiQuotAction α : K →ₗ[ZMod 2] K) x = (α ⟨x, 0⟩).fst :=
  rfl

@[expose] def suzukiResFun (α : MulAut (SuzukiA K φ)) (z : K) : K :=
  (α ⟨0, z⟩).snd

theorem aut_mk_zero (α : MulAut (SuzukiA K φ)) (z : K) :
    α ⟨0, z⟩ = ⟨0, suzukiResFun α z⟩ :=
  BinExt.ext (aut_fst_eq_zero α rfl) rfl

theorem suzukiResFun_add (α : MulAut (SuzukiA K φ)) (z w : K) :
    suzukiResFun α (z + w) = suzukiResFun α z + suzukiResFun α w := by
  have h : (⟨0, z + w⟩ : SuzukiA K φ) = ⟨0, z⟩ * ⟨0, w⟩ := by
    refine BinExt.ext ?_ ?_
    · change (0 : K) = 0 + 0
      rw [add_zero]
    · change z + w = z + w + 0 * φ 0
      rw [zero_mul, add_zero]
  rw [suzukiResFun, h, map_mul, aut_mk_zero, aut_mk_zero]
  change suzukiResFun α z + suzukiResFun α w + 0 * φ 0 = _
  rw [zero_mul, add_zero]

theorem suzukiResFun_mul_self (α : MulAut (SuzukiA K φ)) (x : K) :
    suzukiResFun α (x * φ x) = suzukiQuotFun α x * φ (suzukiQuotFun α x) := by
  have h := congrArg α (sq_def (⟨x, 0⟩ : SuzukiA K φ))
  rw [map_pow, sq_def, aut_mk_zero] at h
  exact ((BinExt.mk.inj h).2).symm

omit [Module (ZMod 2) K] in
theorem ringAut_pow_apply_of_sq {σ : K ≃+* K} (hσ : ∀ a, σ a = a ^ 2) (m : ℕ) (x : K) :
    (σ ^ m) x = x ^ 2 ^ m := by
  induction m generalizing x with
  | zero => rw [pow_zero, pow_zero, pow_one]; rfl
  | succ m ih => rw [pow_succ, RingAut.mul_apply, ih, hσ, ← pow_mul, ← pow_succ']

omit [Module (ZMod 2) K] in
theorem exists_frobenius_pow_eq [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (τ : K ≃+* K) : ∃ s < n, (∀ x, τ x = x ^ 2 ^ s) ∧ ∀ m : ℕ, τ ^ m = 1 ↔ n ∣ m * s := by
  obtain ⟨σ, hσ, hord, hz, -, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two hn hK
  have hfin : IsOfFinOrder σ := orderOf_pos_iff.1 (by rw [hord]; omega)
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1 (hfin.mem_powers_iff_mem_zpowers.2
    (by rw [hz]; exact Subgroup.mem_top τ))
  have hτ : τ = σ ^ (k % n) := by rw [← hk, ← hord, pow_mod_orderOf]
  refine ⟨k % n, Nat.mod_lt _ (by omega), fun x => by rw [hτ, ringAut_pow_apply_of_sq hσ],
    fun m => ?_⟩
  rw [hτ, ← pow_mul, ← orderOf_dvd_iff_pow_eq_one, hord, mul_comm]

omit [Module (ZMod 2) K] in
theorem frobenius_pow_comm {s i : ℕ} (σ τ : K ≃+* K) (hσ : ∀ x, σ x = x ^ 2 ^ s)
    (hτ : ∀ x, τ x = x ^ 2 ^ i) (x : K) : σ (τ x) = τ (σ x) := by
  rw [hσ, hτ, hτ, hσ, ← pow_mul, ← pow_mul, mul_comm]

@[expose] def suzukiSemilinearAut (c : Kˣ) (σ : K ≃+* K) (hσφ : ∀ x, φ (σ x) = σ (φ x)) :
    MulAut (SuzukiA K φ) where
  toFun p := ⟨c * σ p.fst, c * φ c * σ p.snd⟩
  invFun p := ⟨σ.symm ((c : K)⁻¹ * p.fst), σ.symm (((c : K) * φ c)⁻¹ * p.snd)⟩
  left_inv p := by
    have hc : (c : K) * φ c ≠ 0 :=
      mul_ne_zero c.ne_zero ((map_ne_zero φ).2 c.ne_zero)
    refine BinExt.ext ?_ ?_
    · change σ.symm ((c : K)⁻¹ * (c * σ p.fst)) = p.fst
      rw [inv_mul_cancel_left₀ c.ne_zero, RingEquiv.symm_apply_apply]
    · change σ.symm (((c : K) * φ c)⁻¹ * (c * φ c * σ p.snd)) = p.snd
      rw [inv_mul_cancel_left₀ hc, RingEquiv.symm_apply_apply]
  right_inv p := by
    have hc : (c : K) * φ c ≠ 0 :=
      mul_ne_zero c.ne_zero ((map_ne_zero φ).2 c.ne_zero)
    refine BinExt.ext ?_ ?_
    · change (c : K) * σ (σ.symm ((c : K)⁻¹ * p.fst)) = p.fst
      rw [RingEquiv.apply_symm_apply, mul_inv_cancel_left₀ c.ne_zero]
    · change (c : K) * φ c * σ (σ.symm (((c : K) * φ c)⁻¹ * p.snd)) = p.snd
      rw [RingEquiv.apply_symm_apply, mul_inv_cancel_left₀ hc]
  map_mul' p q := by
    refine BinExt.ext ?_ ?_
    · change (c : K) * σ (p.fst + q.fst) = c * σ p.fst + c * σ q.fst
      rw [map_add, mul_add]
    · change (c : K) * φ c * σ (p.snd + q.snd + p.fst * φ q.fst) =
        c * φ c * σ p.snd + c * φ c * σ q.snd + c * σ p.fst * φ (c * σ q.fst)
      rw [map_add, map_add, map_mul, map_mul, hσφ]
      ring

theorem suzukiQuotAction_suzukiSemilinearAut (c : Kˣ) (σ : K ≃+* K)
    (hσφ : ∀ x, φ (σ x) = σ (φ x)) (x : K) :
    (suzukiQuotAction (suzukiSemilinearAut c σ hσφ) : K →ₗ[ZMod 2] K) x = c * σ x :=
  rfl

@[expose] def suzukiShearAut (h : K →+ K) : MulAut (SuzukiA K φ) where
  toFun p := ⟨p.fst, p.snd + h p.fst⟩
  invFun p := ⟨p.fst, p.snd - h p.fst⟩
  left_inv p := BinExt.ext rfl (add_sub_cancel_right _ _)
  right_inv p := BinExt.ext rfl (sub_add_cancel _ _)
  map_mul' p q := BinExt.ext rfl (by
    change p.snd + q.snd + p.fst * φ q.fst + h (p.fst + q.fst) =
      p.snd + h p.fst + (q.snd + h q.fst) + p.fst * φ q.fst
    rw [map_add]
    ring)

theorem suzukiShearAut_apply (h : K →+ K) (p : SuzukiA K φ) :
    suzukiShearAut h p = ⟨p.fst, p.snd + h p.fst⟩ :=
  rfl

theorem suzuki_two_A_automorphism_solvable [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) (φ : K ≃+* K) (hφ : φ ^ 4 ≠ 1) :
    (∀ (α : MulAut (SuzukiA K φ)) (p : SuzukiA K φ),
      (suzukiQuotAction α : K →ₗ[ZMod 2] K) p.fst = (α p).fst) ∧
    Set.range (suzukiQuotAction (K := K) (φ := φ)) =
      {g : LinearMap.GeneralLinearGroup (ZMod 2) K | ∃ (c : Kˣ) (σ : K ≃+* K),
        ∀ x, (g : K →ₗ[ZMod 2] K) x = c * σ x} ∧
    (∀ (α : MulAut (SuzukiA K φ)) (c : Kˣ) (σ : K ≃+* K),
      (∀ x, (suzukiQuotAction α : K →ₗ[ZMod 2] K) x = c * σ x) →
        ∀ z, α ⟨0, z⟩ = ⟨0, c * φ c * σ z⟩) ∧
    (∃ e : Multiplicative (K →+ K) ≃* (suzukiQuotAction (K := K) (φ := φ)).ker,
      ∀ (h : K →+ K) (x z : K),
        (e (Multiplicative.ofAdd h) : MulAut (SuzukiA K φ)) ⟨x, z⟩ = ⟨x, z + h x⟩) ∧
    CFSG.IsElementaryAbelian 2 (suzukiQuotAction (K := K) (φ := φ)).ker ∧
    Nat.card (suzukiQuotAction (K := K) (φ := φ)).ker = 2 ^ (n ^ 2) ∧
    Nat.card (MulAut (SuzukiA K φ)) = 2 ^ (n ^ 2) * (2 ^ n - 1) * n ∧
    derivedSeries (MulAut (SuzukiA K φ)) 3 = ⊥ ∧
    Group.IsSolvable (MulAut (SuzukiA K φ)) := by
  classical
  obtain ⟨s, hs, hφs, hφpow⟩ := exists_frobenius_pow_eq hn hK φ
  have h4s : ¬ n ∣ 4 * s := fun h => hφ ((hφpow 4).2 h)
  obtain ⟨hrig, -⟩ := twisted_product_quadratic_similarity_rigidity hn hK hs h4s
  obtain ⟨σ₂, hσ₂, -, -, hcardAut, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two hn hK
  have hfrob : ∀ (i : ℕ) (x : K), (σ₂ ^ i) x = x ^ 2 ^ i := ringAut_pow_apply_of_sq hσ₂
  have hcommφ : ∀ σ : K ≃+* K, ∀ x, φ (σ x) = σ (φ x) := fun σ x => by
    obtain ⟨i, -, hσi, -⟩ := exists_frobenius_pow_eq hn hK σ
    exact frobenius_pow_comm φ σ hφs hσi x
  set Ψ := suzukiQuotAction (K := K) (φ := φ) with hΨ
  have hform : ∀ α : MulAut (SuzukiA K φ), ∃ (c : Kˣ) (i : ℕ),
      (∀ x, suzukiQuotFun α x = c * x ^ 2 ^ i) ∧
        ∀ z, suzukiResFun α z = c * (c : K) ^ 2 ^ s * z ^ 2 ^ i := by
    intro α
    let f : K →+ K := AddMonoidHom.mk' (suzukiQuotFun α) (suzukiQuotFun_add α)
    let g : K →+ K := AddMonoidHom.mk' (suzukiResFun α) (suzukiResFun_add α)
    have hinv : suzukiQuotFun α⁻¹ (suzukiQuotFun α 1) = 1 := by
      rw [← suzukiQuotFun_mul, inv_mul_cancel]
      rfl
    have hf0 : f ≠ 0 := fun h0 => one_ne_zero (by
      have h1 : suzukiQuotFun α 1 = 0 := DFunLike.congr_fun h0 1
      have h2 : suzukiQuotFun α⁻¹ 0 = 0 :=
        (AddMonoidHom.mk' (suzukiQuotFun α⁻¹) (suzukiQuotFun_add α⁻¹)).map_zero
      rw [h1, h2] at hinv
      exact hinv.symm)
    have hfg : ∀ x, g (x * x ^ 2 ^ s) = f x * f x ^ 2 ^ s := fun x => by
      have h := suzukiResFun_mul_self α x
      simp only [hφs] at h
      exact h
    obtain ⟨⟨c, i⟩, ⟨hf, hg⟩, -⟩ := hrig f g hf0 hfg
    exact ⟨c, i, hf, hg⟩
  have hres : ∀ (α : MulAut (SuzukiA K φ)) (c : Kˣ) (σ : K ≃+* K),
      (∀ x, (Ψ α : K →ₗ[ZMod 2] K) x = c * σ x) → ∀ z, α ⟨0, z⟩ = ⟨0, c * φ c * σ z⟩ := by
    intro α c σ hα z
    obtain ⟨c', i, hf, hg⟩ := hform α
    have hc : (c : K) = c' := by
      have h1 := hα 1
      have h2 := hf 1
      rw [map_one σ, mul_one] at h1
      rw [one_pow, mul_one] at h2
      exact h1.symm.trans h2
    have hσ : ∀ x, σ x = x ^ 2 ^ i := fun x => by
      have h1 : (c : K) * σ x = c * x ^ 2 ^ i := by
        rw [← hα x, hc]
        exact hf x
      exact mul_left_cancel₀ c.ne_zero h1
    rw [aut_mk_zero, hg, hσ, hφs, hc]
  have hrange : Set.range Ψ =
      {g : LinearMap.GeneralLinearGroup (ZMod 2) K | ∃ (c : Kˣ) (σ : K ≃+* K),
        ∀ x, (g : K →ₗ[ZMod 2] K) x = c * σ x} := by
    ext g
    constructor
    · rintro ⟨α, rfl⟩
      obtain ⟨c, i, hf, -⟩ := hform α
      exact ⟨c, σ₂ ^ i, fun x => by rw [hfrob]; exact hf x⟩
    · rintro ⟨c, σ, hg⟩
      exact ⟨suzukiSemilinearAut c σ (hcommφ σ), Units.ext (LinearMap.ext fun x => (hg x).symm)⟩
  have hshear_ker : ∀ h : K →+ K, suzukiShearAut (φ := φ) h ∈ Ψ.ker := fun h =>
    (MonoidHom.mem_ker).2 (Units.ext (LinearMap.ext fun _ => rfl))
  let Λ : Multiplicative (K →+ K) →* Ψ.ker :=
    { toFun := fun h => ⟨suzukiShearAut h.toAdd, hshear_ker h.toAdd⟩
      map_one' := Subtype.ext (MulEquiv.ext fun p => BinExt.ext rfl (by
        change p.snd + (Multiplicative.toAdd (1 : Multiplicative (K →+ K))) p.fst = p.snd
        rw [toAdd_one, AddMonoidHom.zero_apply, add_zero]))
      map_mul' := fun h₁ h₂ => Subtype.ext (MulEquiv.ext fun p => BinExt.ext rfl (by
        change p.snd + (Multiplicative.toAdd (h₁ * h₂)) p.fst =
          p.snd + h₂.toAdd p.fst + h₁.toAdd p.fst
        rw [toAdd_mul, AddMonoidHom.add_apply]
        ring)) }
  have hΛ : ∀ h p, ((Λ h : Ψ.ker) : MulAut (SuzukiA K φ)) p = ⟨p.fst, p.snd + h.toAdd p.fst⟩ :=
    fun _ _ => rfl
  have hΛinj : Function.Injective Λ := by
    intro h₁ h₂ heq
    refine Multiplicative.toAdd.injective (AddMonoidHom.ext fun x => ?_)
    have h := congrArg (fun k : Ψ.ker => ((k : MulAut (SuzukiA K φ)) ⟨x, 0⟩).snd) heq
    change (0 : K) + h₁.toAdd x = 0 + h₂.toAdd x at h
    rwa [zero_add, zero_add] at h
  have hΛsurj : Function.Surjective Λ := by
    rintro ⟨α, hα⟩
    have hα1 : ∀ x, (α ⟨x, 0⟩).fst = x := fun x =>
      congrArg (fun u : LinearMap.GeneralLinearGroup (ZMod 2) K => (u : K →ₗ[ZMod 2] K) x)
        ((MonoidHom.mem_ker).1 hα)
    have hW : ∀ z, α ⟨0, z⟩ = ⟨0, z⟩ := by
      intro z
      rw [hres α 1 1 (fun x => by rw [Units.val_one, one_mul]; exact hα1 x) z]
      refine BinExt.ext rfl ?_
      change ((1 : Kˣ) : K) * φ ((1 : Kˣ) : K) * (1 : K ≃+* K) z = z
      rw [Units.val_one, map_one, one_mul, one_mul]
      rfl
    have hsplit : ∀ x y : K, (⟨x + y, x * φ y⟩ : SuzukiA K φ) = ⟨x, 0⟩ * ⟨y, 0⟩ := by
      intro x y
      refine BinExt.ext rfl ?_
      change x * φ y = 0 + 0 + x * φ y
      rw [add_zero, zero_add]
    have hsplit' : ∀ x y : K, (⟨x + y, x * φ y⟩ : SuzukiA K φ) = ⟨x + y, 0⟩ * ⟨0, x * φ y⟩ := by
      intro x y
      refine BinExt.ext ?_ ?_
      · change x + y = x + y + 0
        rw [add_zero]
      · change x * φ y = 0 + x * φ y + (x + y) * φ 0
        rw [map_zero, mul_zero, add_zero, zero_add]
    let h : K →+ K := AddMonoidHom.mk' (fun x => (α ⟨x, 0⟩).snd) (fun x y => by
      have e := congrArg (fun p => (α p).snd) ((hsplit x y).symm.trans (hsplit' x y))
      simp only [map_mul, hW, suzukiA_mul_snd, hα1] at e
      change (α ⟨x, 0⟩).snd + (α ⟨y, 0⟩).snd + x * φ y =
        (α ⟨x + y, 0⟩).snd + x * φ y + (x + y) * φ 0 at e
      rw [map_zero, mul_zero, add_zero] at e
      exact (add_right_cancel e).symm)
    refine ⟨Multiplicative.ofAdd h, Subtype.ext (MulEquiv.ext fun p => ?_)⟩
    rw [hΛ]
    conv_rhs => rw [suzukiA_eq_mul p, map_mul, hW]
    refine BinExt.ext ?_ ?_
    · change p.fst = (α ⟨p.fst, 0⟩).fst + 0
      rw [add_zero, hα1]
    · change p.snd + (α ⟨p.fst, 0⟩).snd =
        (α ⟨p.fst, 0⟩).snd + p.snd + (α ⟨p.fst, 0⟩).fst * φ 0
      rw [map_zero, mul_zero, add_zero, add_comm]
  set e := MulEquiv.ofBijective Λ ⟨hΛinj, hΛsurj⟩ with he
  have hkercomm : ∀ a b : Ψ.ker, a * b = b * a := by
    intro a b
    obtain ⟨a, rfl⟩ := hΛsurj a
    obtain ⟨b, rfl⟩ := hΛsurj b
    rw [← map_mul, ← map_mul, mul_comm]
  have h2hom : ∀ h : K →+ K, h + h = 0 := fun h => AddMonoidHom.ext fun x => add_self_zmod (h x)
  have hkerel : CFSG.IsElementaryAbelian 2 Ψ.ker := by
    refine { toIsMulCommutative := ⟨⟨hkercomm⟩⟩
             exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => ?_ }
    obtain ⟨a, rfl⟩ := hΛsurj a
    have ha : a * a = 1 := Multiplicative.toAdd.injective (by rw [toAdd_mul, h2hom, toAdd_one])
    rw [← map_pow, sq, ha, map_one]
  have hfr : Module.finrank (ZMod 2) K = n := finrank_eq_of_card hK
  have : Module.Finite (ZMod 2) K := Module.Finite.of_finite
  have hcardHom : Nat.card (K →+ K) = 2 ^ (n ^ 2) := by
    rw [Nat.card_congr (AddMonoidHom.toZModLinearMapEquiv 2).toEquiv]
    have : Finite (K →ₗ[ZMod 2] K) := Module.finite_of_finite (ZMod 2)
    let _ := Fintype.ofFinite (K →ₗ[ZMod 2] K)
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card,
      Module.finrank_linearMap, hfr, sq]
  have hcardKer : Nat.card Ψ.ker = 2 ^ (n ^ 2) := by
    rw [← Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, hcardHom]
  have hcardRange : Nat.card Ψ.range = (2 ^ n - 1) * n := by
    let m : Kˣ × (K ≃+* K) → LinearMap.GeneralLinearGroup (ZMod 2) K := fun cσ =>
      Ψ (suzukiSemilinearAut cσ.1 cσ.2 (hcommφ cσ.2))
    have hm_inj : Function.Injective m := by
      rintro ⟨c, σ⟩ ⟨c', σ'⟩ hcc
      have hx : ∀ x, (c : K) * σ x = c' * σ' x := fun x =>
        congrArg (fun u : LinearMap.GeneralLinearGroup (ZMod 2) K => (u : K →ₗ[ZMod 2] K) x) hcc
      have hc : c = c' := Units.ext (by simpa using hx 1)
      subst hc
      exact Prod.ext rfl (RingEquiv.ext fun x => mul_left_cancel₀ c.ne_zero (hx x))
    have hm_range : Set.range m = (Ψ.range : Set (LinearMap.GeneralLinearGroup (ZMod 2) K)) := by
      rw [MonoidHom.coe_range, hrange]
      ext g
      constructor
      · rintro ⟨⟨c, σ⟩, rfl⟩
        exact ⟨c, σ, fun x => rfl⟩
      · rintro ⟨c, σ, hg⟩
        exact ⟨(c, σ), Units.ext (LinearMap.ext fun x => (hg x).symm)⟩
    have h1 : Nat.card Ψ.range = Nat.card (Set.range m) := by
      rw [hm_range]
      rfl
    rw [h1, Nat.card_range_of_injective hm_inj, Nat.card_prod, Nat.card_units, hK, hcardAut]
  have hcardAll : Nat.card (MulAut (SuzukiA K φ)) = 2 ^ (n ^ 2) * (2 ^ n - 1) * n := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange Ψ).toEquiv, hcardRange, hcardKer]
    ring
  let Zs : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) K) :=
    { carrier := {u | ∃ μ : K, ∀ x, (u : K →ₗ[ZMod 2] K) x = μ * x}
      mul_mem' := by
        rintro u v ⟨μ, hu⟩ ⟨ν, hv⟩
        refine ⟨μ * ν, fun x => ?_⟩
        change (u : K →ₗ[ZMod 2] K) ((v : K →ₗ[ZMod 2] K) x) = _
        rw [hv, hu, mul_assoc]
      one_mem' := ⟨1, fun x => (one_mul x).symm⟩
      inv_mem' := by
        rintro u ⟨μ, hu⟩
        have hinv : ∀ x, μ * ((u⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) K) :
            K →ₗ[ZMod 2] K) x = x := fun x => by
          rw [← hu]
          change ((u * u⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) K) :
            K →ₗ[ZMod 2] K) x = x
          rw [mul_inv_cancel]
          rfl
        have hμ : μ ≠ 0 := by
          rintro rfl
          have := hinv 1
          rw [zero_mul] at this
          exact zero_ne_one this
        refine ⟨μ⁻¹, fun x => ?_⟩
        calc ((u⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) K) : K →ₗ[ZMod 2] K) x =
            μ⁻¹ * (μ * ((u⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) K) :
              K →ₗ[ZMod 2] K) x) := by rw [← mul_assoc, inv_mul_cancel₀ hμ, one_mul]
          _ = μ⁻¹ * x := by rw [hinv] }
  have hcommZ : ∀ u ∈ Zs, ∀ v ∈ Zs, u * v = v * u := by
    rintro u ⟨μ, hu⟩ v ⟨ν, hv⟩
    refine Units.ext (LinearMap.ext fun x => ?_)
    change (u : K →ₗ[ZMod 2] K) ((v : K →ₗ[ZMod 2] K) x) =
      (v : K →ₗ[ZMod 2] K) ((u : K →ₗ[ZMod 2] K) x)
    simp only [hu, hv]
    ring
  have hcomm1 : ∀ α β : MulAut (SuzukiA K φ), ⁅Ψ α, Ψ β⁆ ∈ Zs := by
    intro α β
    obtain ⟨c, i, hf, -⟩ := hform α
    obtain ⟨c', j, hf', -⟩ := hform β
    have hfa : ∀ x, (Ψ α : K →ₗ[ZMod 2] K) x = c * x ^ 2 ^ i := hf
    have hfb : ∀ x, (Ψ β : K →ₗ[ZMod 2] K) x = c' * x ^ 2 ^ j := hf'
    have hne : (c' : K) * (c : K) ^ 2 ^ j ≠ 0 := mul_ne_zero c'.ne_zero (pow_ne_zero _ c.ne_zero)
    refine ⟨c * (c' : K) ^ 2 ^ i * ((c' : K) * (c : K) ^ 2 ^ j)⁻¹, fun y => ?_⟩
    obtain ⟨x, rfl⟩ : ∃ x, ((Ψ β * Ψ α : LinearMap.GeneralLinearGroup (ZMod 2) K) :
        K →ₗ[ZMod 2] K) x = y :=
      ⟨(((Ψ β * Ψ α)⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) K) : K →ₗ[ZMod 2] K) y, by
        rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Module.End.one_apply]⟩
    have hgrp : ⁅Ψ α, Ψ β⁆ * (Ψ β * Ψ α) = Ψ α * Ψ β := by
      rw [commutatorElement_def]
      group
    rw [← Module.End.mul_apply, ← Units.val_mul, hgrp]
    simp only [Units.val_mul, Module.End.mul_apply, hfa, hfb]
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm (2 ^ j) (2 ^ i)]
    field_simp
  have hD1 : derivedSeries (MulAut (SuzukiA K φ)) 1 ≤ Zs.comap Ψ := by
    rw [derivedSeries_one, _root_.commutator_def, Subgroup.commutator_le]
    intro α _ β _
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact hcomm1 α β
  have hD2 : derivedSeries (MulAut (SuzukiA K φ)) 2 ≤ Ψ.ker := by
    rw [derivedSeries_succ, Subgroup.commutator_le]
    intro α hα β hβ
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcommZ _ (hD1 hα) _ (hD1 hβ)
  have hD3 : derivedSeries (MulAut (SuzukiA K φ)) 3 = ⊥ := by
    rw [eq_bot_iff, derivedSeries_succ, Subgroup.commutator_le]
    intro α hα β hβ
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact congrArg Subtype.val (hkercomm ⟨α, hD2 hα⟩ ⟨β, hD2 hβ⟩)
  exact ⟨fun α p => suzukiQuotFun_fst α p, hrange, hres, ⟨e, fun h x z => rfl⟩, hkerel,
    hcardKer, hcardAll, hD3, ⟨⟨3, hD3⟩⟩⟩

end CFSG.LocalAnalysis.ComponentInitial
