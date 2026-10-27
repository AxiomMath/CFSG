module

public import CFSG.LocalAnalysis.EvenBN.U4.Prelim.Semilinear
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Module Subgroup

section TwoPartPlane

variable {H F W : Type*} [Group H] [Field F] [Finite F] [AddCommGroup W] [Module F W]

theorem card_generalLinearGroup_plane {f : ℕ} (hF : Nat.card F = 2 ^ f) (hW : finrank F W = 2) :
    ∃ m, Odd m ∧ Nat.card (LinearMap.GeneralLinearGroup F W) = 2 ^ f * m := by
  classical
  have := Fintype.ofFinite F
  have : Module.Finite F W := Module.finite_of_finrank_eq_succ hW
  let b := Module.finBasisOfFinrankEq F W hW
  have hq : Fintype.card F = 2 ^ f := by rw [← Nat.card_eq_fintype_card, hF]
  have hf : 1 ≤ f := by
    by_contra hf0
    have : f = 0 := by omega
    have h1 : Fintype.card F = 1 := by rw [hq, this, pow_zero]
    have := Fintype.one_lt_card (α := F)
    omega
  rw [← Nat.card_congr (Matrix.GeneralLinearGroup.toLin' b).toEquiv, Matrix.card_GL_field,
    Fin.prod_univ_two, hq]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  have hq2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  refine ⟨((2 ^ f) ^ 2 - 1) * (2 ^ f - 1), ?_, ?_⟩
  · have hodd1 : Odd ((2 ^ f) ^ 2 - 1) := by
      have : Even ((2 ^ f) ^ 2) := by
        rw [← pow_mul]
        exact Nat.even_pow.2 ⟨even_two, by omega⟩
      exact Nat.Even.sub_odd (Nat.one_le_iff_ne_zero.2 (by positivity)) this odd_one
    have hodd2 : Odd (2 ^ f - 1) := by
      have : Even (2 ^ f) := Nat.even_pow.2 ⟨even_two, by omega⟩
      exact Nat.Even.sub_odd (by omega) this odd_one
    exact hodd1.mul hodd2
  · have e : (2 ^ f) ^ 2 - 2 ^ f = 2 ^ f * (2 ^ f - 1) := by
      rw [Nat.mul_sub, mul_one, sq]
    rw [e]
    ring

theorem not_two_pow_two_mul_dvd_index_ker [Finite H] {f : ℕ} (hF : Nat.card F = 2 ^ f)
    (hW : finrank F W = 2) (ρ : H →* AddMonoid.End W)
    (hρ : ∀ h, ∃ σ : F →+* F, ∀ (c : F) (w : W), ρ h (c • w) = σ c • ρ h w) :
    ¬ 2 ^ (2 * f) ∣ ρ.ker.index := by
  classical
  have : Module.Finite F W := Module.finite_of_finrank_eq_succ hW
  have : Nontrivial W := Module.nontrivial_of_finrank_eq_succ hW
  obtain ⟨v₀, hv₀⟩ : ∃ v : W, v ≠ 0 := exists_ne 0
  have hinv : ∀ (h : H) (w : W), ρ h (ρ h⁻¹ w) = w := fun h w => by
    change (ρ h * ρ h⁻¹) w = w
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  have hne : ∀ h : H, ρ h v₀ ≠ 0 := fun h e => hv₀ (by
    have := hinv h⁻¹ v₀
    rw [inv_inv, e, map_zero] at this
    exact this.symm)
  choose σ hσ using hρ
  have huniq : ∀ (h : H) (τ : F →+* F), (∀ (c : F) (w : W), ρ h (c • w) = τ c • ρ h w) →
      τ = σ h := by
    intro h τ hτ
    ext c
    apply smul_left_injective F (hne h)
    change τ c • ρ h v₀ = σ h c • ρ h v₀
    rw [← hτ, hσ]
  let Φ : H →* (F →+* F) :=
    { toFun := σ
      map_one' := (huniq 1 (RingHom.id F) (fun c w => by rw [map_one]; rfl)).symm
      map_mul' := fun h h' => (huniq (h * h') ((σ h).comp (σ h')) (fun c w => by
        rw [map_mul]
        change ρ h (ρ h' (c • w)) = _ • ρ h (ρ h' w)
        rw [hσ, hσ]
        rfl)).symm }
  set H₀ := Φ.toHomUnits.ker with hH₀def
  have hH₀ : ∀ h : H, h ∈ H₀ ↔ σ h = RingHom.id F := by
    intro h
    rw [MonoidHom.mem_ker, Units.ext_iff]
    rfl
  have hlin : ∀ h ∈ H₀, ∀ (c : F) (w : W), ρ h (c • w) = c • ρ h w := fun h hh c w => by
    rw [hσ, (hH₀ h).1 hh, RingHom.id_apply]
  let toLin : H₀ → (W →ₗ[F] W) := fun h =>
    { toFun := ρ h
      map_add' := map_add (ρ h)
      map_smul' := fun c w => hlin h h.2 c w }
  have htoLin : ∀ (h : H₀) (w : W), toLin h w = ρ h w := fun _ _ => rfl
  let lam : H₀ →* LinearMap.GeneralLinearGroup F W :=
    { toFun := fun h => ⟨toLin h, toLin h⁻¹, LinearMap.ext fun w => by
          change ρ h (ρ (h⁻¹ : H₀) w) = w
          exact hinv h w,
        LinearMap.ext fun w => by
          change ρ (h⁻¹ : H₀) (ρ h w) = w
          have := hinv (h : H)⁻¹ w
          rwa [inv_inv] at this⟩
      map_one' := Units.ext (LinearMap.ext fun w => by
        change ρ 1 w = w
        rw [map_one]
        rfl)
      map_mul' := fun h h' => Units.ext (LinearMap.ext fun w => by
        change ρ (h * h' : H) w = ρ h (ρ h' w)
        rw [map_mul]
        rfl) }
  have hkerlam : lam.ker = ρ.ker.subgroupOf H₀ := by
    ext h
    rw [MonoidHom.mem_ker, mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro h1
      ext w
      have := congrArg (fun u : LinearMap.GeneralLinearGroup F W => (u : W →ₗ[F] W) w) h1
      exact this
    · intro h1
      refine Units.ext (LinearMap.ext fun w => ?_)
      change ρ h w = w
      rw [h1]
      rfl
  have hker : ρ.ker ≤ H₀ := by
    intro h hh
    rw [hH₀]
    exact (huniq h (RingHom.id F) (fun c w => by
      rw [(MonoidHom.mem_ker).mp hh]; rfl)).symm
  have hidx : ρ.ker.index = ρ.ker.relIndex H₀ * H₀.index := (relIndex_mul_index hker).symm
  obtain ⟨m, hm, hGL⟩ := card_generalLinearGroup_plane hF hW
  have hrel : ρ.ker.relIndex H₀ ∣ 2 ^ f * m := by
    rw [relIndex, ← hkerlam, index_ker, ← hGL]
    exact card_subgroup_dvd_card _
  have hH₀idx : H₀.index ≤ f := by
    have : Finite (F →+* F) :=
      Finite.of_injective (fun τ : F →+* F => (τ : F → F)) DFunLike.coe_injective
    rw [index_ker]
    calc Nat.card Φ.toHomUnits.range ≤ Nat.card (F →+* F)ˣ :=
          Nat.card_le_card_of_injective _ Subtype.val_injective
      _ ≤ Nat.card (F →+* F) := Nat.card_le_card_of_injective _ Units.val_injective
      _ ≤ f := card_ringHom_le hF
  have hpos : 0 < H₀.index := Nat.pos_of_ne_zero index_ne_zero_of_finite
  intro hdvd
  rw [hidx] at hdvd
  have h1 : 2 ^ (2 * f) ∣ 2 ^ f * m * H₀.index := hdvd.trans (Nat.mul_dvd_mul_right hrel _)
  have h2 : 2 ^ f ∣ m * H₀.index := by
    rw [show 2 * f = f + f by ring, pow_add, mul_assoc] at h1
    exact (Nat.mul_dvd_mul_iff_left (by positivity)).1 h1
  have hcop : Nat.Coprime (2 ^ f) m := Nat.Coprime.pow_left f (Nat.coprime_two_left.2 hm)
  have h3 := Nat.le_of_dvd hpos (hcop.dvd_of_dvd_mul_left h2)
  have h4 : f < 2 ^ f := Nat.lt_two_pow_self
  omega

end TwoPartPlane

end CFSG.LocalAnalysis.EvenBN.U4
