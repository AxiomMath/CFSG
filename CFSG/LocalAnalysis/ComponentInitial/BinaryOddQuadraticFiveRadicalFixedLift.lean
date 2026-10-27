module

public import CFSG.LocalAnalysis.ComponentInitial.BinaryOddQuadraticFiveInvariants
public import CFSG.ClassicalGroups.Alternating.Generation
public import Mathlib.RepresentationTheory.Basic

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OddQuadraticFive

open BinarySymplecticTransvection

variable {E : Type} [AddCommGroup E] [Module (ZMod 2) E] {b : LinearMap.BilinForm (ZMod 2) E}
  {Q : QuadraticForm (ZMod 2) E} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

namespace RadicalLift

theorem tau_mul_self (hb : b.IsAlt) (u : E) : tau hb u * tau hb u = 1 :=
  Subtype.ext (mul_self hb u)

theorem tau_zero (hb : b.IsAlt) : tau hb (0 : E) = 1 :=
  Subtype.ext (zero_eq_one hb)

theorem tau_comm (hb : b.IsAlt) {u w : E} (h : b u w = 0) :
    tau hb u * tau hb w = tau hb w * tau hb u := by
  have h1 : tau hb u * tau hb w * tau hb u = tau hb w := Subtype.ext (by
    change binarySymplecticTransvection b hb u * binarySymplecticTransvection b hb w *
      binarySymplecticTransvection b hb u = binarySymplecticTransvection b hb w
    rw [mul_mul_self, symm_apply hb u w, h, zero_smul, add_zero])
  calc tau hb u * tau hb w = tau hb u * tau hb w * (tau hb u * tau hb u) := by
        rw [tau_mul_self, mul_one]
    _ = tau hb u * tau hb w * tau hb u * tau hb u := (mul_assoc _ _ _).symm
    _ = tau hb w * tau hb u := by rw [h1]

theorem tau_braid (hb : b.IsAlt) {u w : E} (h : b u w = 1) :
    tau hb u * tau hb w * tau hb u = tau hb (u + w) := Subtype.ext (by
  change binarySymplecticTransvection b hb u * binarySymplecticTransvection b hb w *
    binarySymplecticTransvection b hb u = binarySymplecticTransvection b hb (u + w)
  rw [mul_mul_self, symm_apply hb u w, h, one_smul, add_comm])

@[expose] def nOp (σ : Representation (ZMod 2) (bilinIsometryGroup b) W) (hb : b.IsAlt)
    (u : E) : W →ₗ[ZMod 2] W :=
  σ (tau hb u) + LinearMap.id

theorem nOp_apply (σ : Representation (ZMod 2) (bilinIsometryGroup b) W) (hb : b.IsAlt) (u : E)
    (y : W) : nOp σ hb u y = σ (tau hb u) y + y :=
  rfl

theorem nOp_nOp (σ : Representation (ZMod 2) (bilinIsometryGroup b) W) (hb : b.IsAlt) (u : E)
    (y : W) : nOp σ hb u (nOp σ hb u y) = 0 := by
  have h : σ (tau hb u) (σ (tau hb u) y) = y := by
    rw [← Module.End.mul_apply, ← map_mul, tau_mul_self, map_one, Module.End.one_apply]
  rw [nOp_apply, nOp_apply, map_add, h, add_comm (σ (tau hb u) y) y, add_self_eq_zero_zmod_two]

theorem nOp_comm (σ : Representation (ZMod 2) (bilinIsometryGroup b) W) (hb : b.IsAlt)
    {u w : E} (huw : b u w = 0) (y : W) :
    nOp σ hb u (nOp σ hb w y) = nOp σ hb w (nOp σ hb u y) := by
  have hc : σ (tau hb u) (σ (tau hb w) y) = σ (tau hb w) (σ (tau hb u) y) := by
    have h := congrArg (fun g => σ g y) (tau_comm hb huw)
    simpa only [map_mul, Module.End.mul_apply] using h
  simp only [nOp_apply, map_add, hc]
  abel

theorem nOp_iota (hb : b.IsAlt) {σ : Representation (ZMod 2) (bilinIsometryGroup b) W}
    {ι : E →ₗ[ZMod 2] W} (hισ : ∀ (s : bilinIsometryGroup b) x, ι (sE s x) = σ s (ι x))
    (u e : E) : nOp σ hb u (ι e) = ι (b e u • u) := by
  rw [nOp_apply, ← hισ, sE_tau, map_add, add_comm (ι e), add_assoc, add_self_eq_zero_zmod_two,
    add_zero]

theorem rho_nOp (hb : b.IsAlt) (hQ : QuadraticMap.polarBilin Q = b)
    {σ : Representation (ZMod 2) (bilinIsometryGroup b) W} {ρ : W →ₗ[ZMod 2] E × ZMod 2}
    (hρσ : ∀ (s : bilinIsometryGroup b) y,
      ρ (σ s y) = (sE s (ρ y).1, (ρ y).2 + Q (ρ y).1 + Q (sE s (ρ y).1)))
    (u : E) (y : W) : ρ (nOp σ hb u y) = b (ρ y).1 u • (u, Q u + 1) := by
  rw [nOp_apply, map_add, hρσ, sE_tau, Q_add hQ, Q_smul, map_smul, smul_eq_mul]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.smul_fst]
    rw [add_comm (ρ y).1, add_assoc, add_self_eq_zero_zmod_two, add_zero]
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    have key : ∀ t q₁ q₂ c : ZMod 2, t + q₁ + (q₁ + c * q₂ + c * c) + t = c * (q₂ + 1) := by
      decide
    exact key _ _ _ _

theorem exists_dual (hnd : b.Nondegenerate) {u w : E} (hu : u ≠ 0)
    (huw : u ≠ w) : ∃ u', b u' u = 1 ∧ b u' w = 0 := by
  obtain ⟨x, hx⟩ := exists_apply_eq_one hnd hu
  rcases zmod_two_cases (b x w) with hxw | hxw
  · exact ⟨x, hx, hxw⟩
  obtain ⟨z, hz⟩ := exists_apply_eq_one hnd (fun h : u + w = 0 => huw (eq_of_add_eq_zero_zmod2 h))
  rw [map_add] at hz
  rcases zmod_two_cases (b z u) with hzu | hzu
  · refine ⟨x + z, ?_, ?_⟩
    · rw [map_add, LinearMap.add_apply, hx, hzu, add_zero]
    · rw [hzu, zero_add] at hz
      rw [map_add, LinearMap.add_apply, hxw, hz]
      decide
  · refine ⟨z, hzu, ?_⟩
    rw [hzu] at hz
    rcases zmod_two_cases (b z w) with h | h
    · exact h
    · rw [h] at hz
      exact absurd hz (by decide)

theorem eps_add_of_orth (hb : b.IsAlt) (hQ : QuadraticMap.polarBilin Q = b)
    {σ : Representation (ZMod 2) (bilinIsometryGroup b) W} {ι : E →ₗ[ZMod 2] W}
    (hι : Function.Injective ι) (hισ : ∀ (s : bilinIsometryGroup b) x, ι (sE s x) = σ s (ι x))
    {ρ : W →ₗ[ZMod 2] E × ZMod 2} (hρ : Function.Surjective ρ)
    (hρσ : ∀ (s : bilinIsometryGroup b) y,
      ρ (σ s y) = (sE s (ρ y).1, (ρ y).2 + Q (ρ y).1 + Q (sE s (ρ y).1)))
    (hmem : ∀ y, ρ y = 0 → ∃ e, ι e = y) {ξ₀ : W} (hξ₀ : ρ ξ₀ = (0, 1)) {ε : E → ZMod 2}
    (hNξ : ∀ x, nOp σ hb x ξ₀ = ι (ε x • x)) {u w u' w' : E} (huw : b u w = 0)
    (hu'u : b u' u = 1) (hu'w : b u' w = 0) (hw'u : b w' u = 0) (hw'w : b w' w = 1) :
    ε (u + w) = ε u + ε w := by
  obtain ⟨ι', hι'⟩ := ι.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hι)
  have hι'e : ∀ e, ι' (ι e) = e := fun e => LinearMap.congr_fun hι' e
  have hwu : b w u = 0 := by rw [symm_apply hb, huw]
  have hvu : b (u + w) u = 0 := by rw [map_add, LinearMap.add_apply, hb.self_eq_zero, hwu, add_zero]
  have hvw : b (u + w) w = 0 := by rw [map_add, LinearMap.add_apply, huw, hb.self_eq_zero, add_zero]
  have hwv : b w (u + w) = 0 := by rw [map_add, hwu, hb.self_eq_zero, add_zero]
  have hQv : Q (u + w) = Q u + Q w := by rw [Q_add hQ, huw, add_zero]
  have hNι := nOp_iota hb hισ
  have hρN := rho_nOp hb hQ hρσ
  obtain ⟨y, hy⟩ := hρ (u', 0)
  obtain ⟨z, hz⟩ := hρ (w', 0)
  obtain ⟨γw, hγw⟩ := hmem (nOp σ hb w y) (by rw [hρN, hy, hu'w, zero_smul])
  obtain ⟨γu, hγu⟩ := hmem (nOp σ hb u z) (by rw [hρN, hz, hw'u, zero_smul])
  set uh := nOp σ hb u y + (Q u + 1) • ξ₀ with huh
  set wh := nOp σ hb w z + (Q w + 1) • ξ₀ with hwh
  have h4 : ∀ a c : E, a + c + a + c = 0 := fun a c => by
    rw [show a + c + a + c = (a + a) + (c + c) by abel, add_self_eq_zero_zmod_two,
      add_self_eq_zero_zmod_two, add_zero]
  have hρuh : ρ uh = (u, 0) := by
    rw [huh, map_add ρ, map_smul ρ, hρN, hy, hu'u, one_smul, hξ₀, Prod.smul_mk, smul_zero,
      smul_eq_mul, mul_one, Prod.mk_add_mk, add_zero, add_self_eq_zero_zmod_two]
  have hρwh : ρ wh = (w, 0) := by
    rw [hwh, map_add ρ, map_smul ρ, hρN, hz, hw'w, one_smul, hξ₀, Prod.smul_mk, smul_zero,
      smul_eq_mul, mul_one, Prod.mk_add_mk, add_zero, add_self_eq_zero_zmod_two]
  have hρv : ∀ x : W, b (ρ x).1 (u + w) = 1 → (ρ x).2 = 0 →
      ρ (nOp σ hb (u + w) x + uh + wh + (Q (u + w) + 1) • ξ₀) = 0 := fun x h1 h2 => by
    rw [map_add ρ, map_add ρ, map_add ρ, map_smul ρ, hρN, h1, one_smul, hρuh, hρwh, hξ₀]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.smul_fst, smul_zero, add_zero, Prod.fst_zero]
      exact h4 u w
    · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, mul_one, add_zero, Prod.snd_zero]
      exact add_self_eq_zero_zmod_two _
  obtain ⟨γv, hγv⟩ := hmem _ (hρv y (by rw [hy, map_add, hu'u, hu'w, add_zero])
    (by rw [hy]))
  obtain ⟨γv', hγv'⟩ := hmem _ (hρv z (by rw [hz, map_add, hw'u, hw'w, zero_add])
    (by rw [hz]))
  have h7 : ∀ a p q r : W, a + p + q + r + p + q + r = a := fun a p q r => by
    rw [show a + p + q + r + p + q + r = a + (p + p) + (q + q) + (r + r) by abel,
      add_self_eq_zero_zmod_two, add_self_eq_zero_zmod_two, add_self_eq_zero_zmod_two, add_zero,
      add_zero, add_zero]
  have hsolve : ∀ {x : W} {e : E},
      ι e = nOp σ hb (u + w) x + uh + wh + (Q (u + w) + 1) • ξ₀ →
      nOp σ hb (u + w) x = ι e + uh + wh + (Q (u + w) + 1) • ξ₀ := fun h => by
    rw [h, h7]
  have hNvy := hsolve hγv
  have hNvz := hsolve hγv'
  have P1 : nOp σ hb u uh = (Q u + 1) • ι (ε u • u) := by
    rw [huh, map_add (nOp σ hb u), map_smul (nOp σ hb u), nOp_nOp, zero_add, hNξ]
  have P2 : nOp σ hb u wh = ι (b γu w • w) + (Q w + 1) • ι (ε u • u) := by
    rw [hwh, map_add (nOp σ hb u), map_smul (nOp σ hb u), nOp_comm σ hb huw, ← hγu, hNι, hNξ]
  have P3 : nOp σ hb w uh = ι (b γw u • u) + (Q u + 1) • ι (ε w • w) := by
    rw [huh, map_add (nOp σ hb w), map_smul (nOp σ hb w), nOp_comm σ hb hwu, ← hγw, hNι, hNξ]
  have P4 : nOp σ hb w wh = (Q w + 1) • ι (ε w • w) := by
    rw [hwh, map_add (nOp σ hb w), map_smul (nOp σ hb w), nOp_nOp, zero_add, hNξ]
  have P5 : nOp σ hb (u + w) uh =
      nOp σ hb u (nOp σ hb (u + w) y) + (Q u + 1) • ι (ε (u + w) • (u + w)) := by
    rw [huh, map_add (nOp σ hb (u + w)), map_smul (nOp σ hb (u + w)), nOp_comm σ hb hvu, hNξ]
  have P6 : nOp σ hb (u + w) wh =
      nOp σ hb w (nOp σ hb (u + w) z) + (Q w + 1) • ι (ε (u + w) • (u + w)) := by
    rw [hwh, map_add (nOp σ hb (u + w)), map_smul (nOp σ hb (u + w)), nOp_comm σ hb hvw, hNξ]
  have hNuNvy : nOp σ hb u (nOp σ hb (u + w) y) = ι (b γv u • u) + (Q u + 1) • ι (ε u • u) +
      (ι (b γu w • w) + (Q w + 1) • ι (ε u • u)) + (Q (u + w) + 1) • ι (ε u • u) := by
    rw [hNvy, map_add (nOp σ hb u), map_add (nOp σ hb u), map_add (nOp σ hb u),
      map_smul (nOp σ hb u), hNι, P1, P2, hNξ]
  have hNwNvz : nOp σ hb w (nOp σ hb (u + w) z) = ι (b γv' w • w) +
      (ι (b γw u • u) + (Q u + 1) • ι (ε w • w)) + (Q w + 1) • ι (ε w • w) +
      (Q (u + w) + 1) • ι (ε w • w) := by
    rw [hNvz, map_add (nOp σ hb w), map_add (nOp σ hb w), map_add (nOp σ hb w),
      map_smul (nOp σ hb w), hNι, P3, P4, hNξ]
  have hNwNvy : nOp σ hb w (nOp σ hb (u + w) y) = ι (b γv w • w) +
      (ι (b γw u • u) + (Q u + 1) • ι (ε w • w)) + (Q w + 1) • ι (ε w • w) +
      (Q (u + w) + 1) • ι (ε w • w) := by
    rw [hNvy, map_add (nOp σ hb w), map_add (nOp σ hb w), map_add (nOp σ hb w),
      map_smul (nOp σ hb w), hNι, P3, P4, hNξ]
  have E1 := nOp_nOp σ hb (u + w) y
  conv_lhs at E1 => rw [hNvy, map_add (nOp σ hb (u + w)), map_add (nOp σ hb (u + w)),
    map_add (nOp σ hb (u + w)), map_smul (nOp σ hb (u + w)), hNι, P5, P6, hNuNvy, hNwNvz, hNξ]
  have E2 := nOp_comm σ hb hwv y
  rw [hNwNvy, ← hγw, hNι] at E2
  have A := congrArg (fun x => b u' (ι' x)) E1
  have B1 := congrArg (fun x => b w' (ι' x)) E2
  have B2 := congrArg (fun x => b u' (ι' x)) E2
  simp only [map_add, map_smul, hι'e, smul_eq_mul, map_zero, hu'u, hu'w, hw'u, hw'w,
    mul_one, mul_zero, add_zero, zero_add] at A B1 B2
  rw [hQv] at A B1
  have key : ∀ a₁ a₂ a₃ a₄ qu qw eu ew ev : ZMod 2,
      a₁ + a₂ + (a₁ + (qu + 1) * eu + (qw + 1) * eu + (qu + qw + 1) * eu + (qu + 1) * ev) +
          (a₃ + (qw + 1) * ev) + (qu + qw + 1) * ev = 0 →
        a₂ + (qu + 1) * ew + (qw + 1) * ew + (qu + qw + 1) * ew = a₃ + a₄ →
        a₃ = a₃ + a₄ → ev = eu + ew := by
    decide
  exact key _ _ _ _ _ _ _ _ _ A B1 B2

theorem eps_add_of_hyp (hb : b.IsAlt) {σ : Representation (ZMod 2) (bilinIsometryGroup b) W}
    {ι : E →ₗ[ZMod 2] W} (hι : Function.Injective ι)
    (hισ : ∀ (s : bilinIsometryGroup b) x, ι (sE s x) = σ s (ι x)) {ξ₀ : W} {ε : E → ZMod 2}
    (hNξ : ∀ x, nOp σ hb x ξ₀ = ι (ε x • x)) {u w : E} (huw : b u w = 1) :
    ε (u + w) = ε u + ε w := by
  have hwu : b w u = 1 := by rw [symm_apply hb, huw]
  have hξ : ∀ x, σ (tau hb x) ξ₀ = ι (ε x • x) + ξ₀ := fun x => by
    rw [← hNξ, nOp_apply, add_assoc, add_self_eq_zero_zmod_two, add_zero]
  have hstep : ∀ x e, σ (tau hb x) (ι e + ξ₀) = ι (sE (tau hb x) e + ε x • x) + ξ₀ :=
    fun x e => by
      rw [map_add, ← hισ, hξ, map_add, add_assoc]
  have hbr := congrArg (fun g => σ g ξ₀) (tau_braid hb huw)
  simp only [map_mul, Module.End.mul_apply] at hbr
  rw [hξ u, hstep, hstep, hξ (u + w)] at hbr
  have hp := congrArg (fun x => b x u) (hι (add_right_cancel hbr))
  simp only [sE_tau, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hb.self_eq_zero, huw, hwu, mul_zero, mul_one, add_zero, zero_add] at hp
  exact hp.symm

end RadicalLift

open RadicalLift

theorem binary_odd_quadratic_five_by_natural_four_radical_fixed_lift
    [FiniteDimensional (ZMod 2) E] (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hQ : QuadraticMap.polarBilin Q = b)
    (σ : Representation (ZMod 2) (bilinIsometryGroup b) W)
    (ι : E →ₗ[ZMod 2] W) (hι : Function.Injective ι)
    (hισ : ∀ (s : bilinIsometryGroup b) (x : E), ι (sE s x) = σ s (ι x))
    (ρ : W →ₗ[ZMod 2] E × ZMod 2) (hρ : Function.Surjective ρ)
    (hρσ : ∀ (s : bilinIsometryGroup b) (y : W),
      ρ (σ s y) = (sE s (ρ y).1, (ρ y).2 + Q (ρ y).1 + Q (sE s (ρ y).1)))
    (hker : LinearMap.ker ρ = LinearMap.range ι) :
    ∃ ξ : W, (∀ s : bilinIsometryGroup b, σ s ξ = ξ) ∧ ρ ξ = (0, 1) := by
  have hmem : ∀ y, ρ y = 0 → ∃ e, ι e = y := fun y hy => by
    have h : y ∈ LinearMap.range ι := hker ▸ LinearMap.mem_ker.mpr hy
    exact h
  have hρι : ∀ e, ρ (ι e) = 0 := fun e => by
    have h : ι e ∈ LinearMap.ker ρ := hker ▸ LinearMap.mem_range_self ι e
    exact h
  obtain ⟨ξ₀, hξ₀⟩ := hρ (0, 1)
  have hC : ∀ u, ∃ e, ι e = nOp σ hb u ξ₀ := fun u => hmem _ (by
    rw [rho_nOp hb hQ hρσ, hξ₀, map_zero, LinearMap.zero_apply, zero_smul])
  choose C hC using hC
  have hC0 : C 0 = 0 := hι (by
    rw [hC, map_zero, nOp_apply, tau_zero, map_one, Module.End.one_apply,
      add_self_eq_zero_zmod_two])
  have hNι := nOp_iota hb hισ
  have hCorth : ∀ u w, b u w = 0 → b (C u) w = 0 := by
    intro u w huw
    by_cases hu : u = 0
    · rw [hu, hC0, map_zero, LinearMap.zero_apply]
    by_cases hw : w = 0
    · rw [hw, map_zero]
    have hu2 : b (C u) u • u = 0 := hι (by
      rw [map_zero, ← nOp_nOp σ hb u ξ₀, ← hC, hNι])
    by_cases hwu : w = u
    · rw [hwu]
      exact (smul_eq_zero.mp hu2).resolve_right hu
    have h := nOp_comm σ hb huw ξ₀
    rw [← hC, ← hC, hNι, hNι] at h
    have h' : b (C w) u • u + b (C u) w • w = 0 := hι (by
      rw [map_add, h, add_self_eq_zero_zmod_two, map_zero])
    exact (smul_add_smul_eq_zero hu hw (Ne.symm hwu) h').2
  have hε : ∀ u, ∃ c : ZMod 2, C u = c • u ∧ (u = 0 → c = 0) := by
    intro u
    by_cases hu : u = 0
    · exact ⟨0, by rw [hu, hC0, smul_zero], fun _ => rfl⟩
    obtain ⟨x, hx⟩ := exists_apply_eq_one hnd hu
    rw [symm_apply hb] at hx
    have hline : ∀ y, b (C u) y = b u y * b (C u) x := fun y => by
      have h0 : b u (y + b u y • x) = 0 := by
        rw [map_add, map_smul, smul_eq_mul, hx, mul_one, zmod2_add_self]
      have h1 := hCorth u _ h0
      rw [map_add, map_smul, smul_eq_mul] at h1
      exact eq_of_add_eq_zero_zmod2 h1
    refine ⟨b (C u) x, eq_of_add_eq_zero_zmod2 (hnd.1 _ fun y => ?_), fun h => absurd h hu⟩
    rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hline,
      mul_comm, zmod2_add_self]
  choose ε hεC hε0 using hε
  have hNξ : ∀ x, nOp σ hb x ξ₀ = ι (ε x • x) := fun x => by rw [← hC, hεC]
  have hadd : ∀ u w, ε (u + w) = ε u + ε w := by
    intro u w
    by_cases hu : u = 0
    · rw [hu, zero_add, hε0 0 rfl, zero_add]
    by_cases hw : w = 0
    · rw [hw, add_zero, hε0 0 rfl, add_zero]
    by_cases huw : u = w
    · rw [huw, add_self_eq_zero_zmod_two, hε0 0 rfl, zmod2_add_self]
    rcases zmod_two_cases (b u w) with h0 | h1
    · obtain ⟨u', hu'u, hu'w⟩ := exists_dual hnd hu huw
      obtain ⟨w', hw'w, hw'u⟩ := exists_dual hnd hw (Ne.symm huw)
      exact eps_add_of_orth hb hQ hι hισ hρ hρσ hmem hξ₀ hNξ h0 hu'u hu'w hw'u hw'w
    · exact eps_add_of_hyp hb hι hισ hNξ h1
  let ℓ : E →ₗ[ZMod 2] ZMod 2 := (AddMonoidHom.mk' ε hadd).toZModLinearMap 2
  have ha : ∀ x, b ((b.toDual hnd).symm ℓ) x = ε x := fun x => by
    rw [← LinearMap.BilinForm.toDual_def hnd, LinearEquiv.apply_symm_apply]
    rfl
  set a := (b.toDual hnd).symm ℓ
  have h3 : ∀ p q r : W, p + q + (r + p) = q + r := fun p q r => by
    rw [show p + q + (r + p) = (p + p) + q + r by abel, add_self_eq_zero_zmod_two, zero_add]
  have hfixτ : ∀ x, σ (tau hb x) (ξ₀ + ι a) = ξ₀ + ι a := fun x => by
    have h' : σ (tau hb x) ξ₀ = ι (ε x • x) + ξ₀ := by
      rw [← hNξ, nOp_apply, add_assoc, add_self_eq_zero_zmod_two, add_zero]
    rw [map_add, h', ← hισ, sE_tau, map_add, ha x, h3]
  refine ⟨ξ₀ + ι a, fun s => ?_, by rw [map_add, hξ₀, hρι, add_zero]⟩
  have hle := CFSG.ClassicalGroups.Alternating.closure_symplecticTransvection_le_bilinIsometryGroup
    (K := ZMod 2) hb
  have hs : (s : LinearMap.GeneralLinearGroup (ZMod 2) E) ∈ Subgroup.closure
      {g | ∃ (a : E) (c : ZMod 2),
        g = CFSG.ClassicalGroups.Alternating.symplecticTransvection b hb a c} := by
    rw [← CFSG.ClassicalGroups.Alternating.alternating_transvection_generation hb hnd]
    exact s.2
  obtain ⟨g, hg⟩ := s
  change σ ⟨g, hle hs⟩ (ξ₀ + ι a) = ξ₀ + ι a
  refine Subgroup.closure_induction (p := fun g hg => σ ⟨g, hle hg⟩ (ξ₀ + ι a) = ξ₀ + ι a)
    ?_ ?_ ?_ ?_ hs
  · rintro x ⟨a', c, rfl⟩
    rcases zmod_two_cases c with rfl | rfl
    · have h1 : (⟨_, hle (Subgroup.subset_closure ⟨a', 0, rfl⟩)⟩ : bilinIsometryGroup b) = 1 :=
        Subtype.ext (CFSG.ClassicalGroups.Alternating.symplecticTransvection_zero hb a')
      rw [h1, map_one, Module.End.one_apply]
    · have h1 : (⟨_, hle (Subgroup.subset_closure ⟨a', 1, rfl⟩)⟩ : bilinIsometryGroup b) =
          tau hb a' := Subtype.ext (gl_ext fun x => by
        rw [CFSG.ClassicalGroups.Alternating.symplecticTransvection_apply, one_mul]
        rfl)
      rw [h1, hfixτ]
  · change σ 1 (ξ₀ + ι a) = ξ₀ + ι a
    rw [map_one, Module.End.one_apply]
  · intro x y hx hy ihx ihy
    change σ (⟨x, hle hx⟩ * ⟨y, hle hy⟩) (ξ₀ + ι a) = ξ₀ + ι a
    rw [map_mul, Module.End.mul_apply, ihy, ihx]
  · intro x hx ihx
    change σ (⟨x, hle hx⟩ : bilinIsometryGroup b)⁻¹ (ξ₀ + ι a) = ξ₀ + ι a
    conv_lhs => rw [← ihx]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

end CFSG.LocalAnalysis.ComponentInitial.OddQuadraticFive
