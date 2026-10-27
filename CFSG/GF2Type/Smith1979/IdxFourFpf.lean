module

public import CFSG.GF2Type.Smith1979.CaseI25U43
public import CFSG.GF2Type.Smith1980Orth.W4SigmaGL
import CFSG.ClassicalGroups.Unitary.Simple

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.IdxFour

open Module
open CFSG.LieType.Multipliers.U43 (F9 X₀)
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.U43Six
open Case25.U43Weights

theorem twenty_le_finrank_of_faithful {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] (φ : X₀ →* (V ≃ₗ[ZMod 2] V)) (hφ : Function.Injective φ) :
    20 ≤ finrank (ZMod 2) V := by
  let ρ : Representation (ZMod 2) A4 V :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (φ.comp thetaBar)
  have hfaith : Function.Injective ρ := by
    intro x y hxy
    apply thetaBar_injective
    apply hφ
    exact LinearEquiv.ext fun v => LinearMap.congr_fun hxy v
  haveI : Nontrivial A4 := ⟨⟨Multiplicative.ofAdd (1, 0, 0, 0), 1, by decide⟩⟩
  have hβ : ∀ (w : List Gen) (a : A4) (v : V),
      ρ (sw w a) (φ (levWord w) v) = φ (levWord w) (ρ a v) := by
    intro w a v
    have h := levWord_conj w a
    rw [mul_inv_eq_iff_eq_mul] at h
    show φ (thetaBar (sw w a)) (φ (levWord w) v) = φ (levWord w) (φ (thetaBar a) v)
    rw [← LinearEquiv.mul_apply, ← map_mul, ← h, map_mul, LinearEquiv.mul_apply]
  have h := LemmaW.two_mul_le_finrank ρ pow_three_eq_one_gen hfaith (fun w => φ (levWord w)) sw
    hβ (m := 10) ten_le_ncard_orbit
  omega

theorem not_three_pow_seven_dvd_card_GL {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (hW : finrank (ZMod 2) W ≤ 11) :
    ¬ 3 ^ 7 ∣ Nat.card (W ≃ₗ[ZMod 2] W) := by
  rw [Smith1980Orth.W4Sigma.card_linearEquiv_eq_prod (V := W) rfl]
  generalize finrank (ZMod 2) W = n at hW ⊢
  interval_cases n <;>
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.val_zero, Fin.val_succ] <;> omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

@[expose] def projP (θ : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V :=
  (θ ^ 2 : V ≃ₗ[ZMod 2] V).toLinearMap + θ.toLinearMap + LinearMap.id

theorem projP_apply (θ : V ≃ₗ[ZMod 2] V) (v : V) : projP θ v = θ (θ v) + θ v + v := by
  simp [projP, pow_two, LinearEquiv.mul_apply]

theorem add_self_zmod2 (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem theta_projP {θ : V ≃ₗ[ZMod 2] V} (h3 : θ ^ 3 = 1) (v : V) :
    θ (projP θ v) = projP θ v := by
  have h3v : θ (θ (θ v)) = v := by
    have := congrArg (fun g : V ≃ₗ[ZMod 2] V => g v) h3
    simpa [pow_succ, LinearEquiv.mul_apply] using this
  rw [projP_apply, map_add, map_add, h3v]
  abel

theorem projP_of_fix {θ : V ≃ₗ[ZMod 2] V} {v : V} (hv : θ v = v) : projP θ v = v := by
  rw [projP_apply, hv, hv, add_self_zmod2, zero_add]

theorem projP_projP {θ : V ≃ₗ[ZMod 2] V} (h3 : θ ^ 3 = 1) (v : V) :
    projP θ (projP θ v) = projP θ v :=
  projP_of_fix (theta_projP h3 v)

theorem projP_comm {θ e : V ≃ₗ[ZMod 2] V} (h : e * θ = θ * e) (v : V) :
    e (projP θ v) = projP θ (e v) := by
  have h1 : ∀ w, e (θ w) = θ (e w) := fun w => by
    rw [← LinearEquiv.mul_apply, h, LinearEquiv.mul_apply]
  rw [projP_apply, projP_apply, map_add, map_add, h1, h1]

theorem fixedPointFree_of_center {E : Type*} [Group E] (ι : E →* (V ≃ₗ[ZMod 2] V))
    (hι : Function.Injective ι) (hV : finrank (ZMod 2) V = 12) {θ : E} (hθ3 : θ ^ 3 = 1)
    (hθc : ∀ e : E, e * θ = θ * e) (π : E →* X₀) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.zpowers θ) (h37 : 3 ^ 7 ∣ Nat.card E) (v : V)
    (hv : ι θ v = v) : v = 0 := by
  classical
  by_contra hv0
  have ht3 : ι θ ^ 3 = 1 := by rw [← map_pow, hθ3, map_one]
  set P := projP (ι θ) with hPdef
  set C : Submodule (ZMod 2) V := LinearMap.range P with hC
  set D : Submodule (ZMod 2) V := LinearMap.ker P with hD
  have hPP : ∀ w, P (P w) = P w := projP_projP ht3
  have hθP : ∀ w, ι θ (P w) = P w := theta_projP ht3
  have hcommP : ∀ (e : E) (w : V), ι e (P w) = P (ι e w) := fun e w =>
    projP_comm (by rw [← map_mul, hθc e, map_mul]) w
  have hinvapp : ∀ (e : E) (w : V), ι e (ι e⁻¹ w) = w := fun e w => by
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hfixC : ∀ w ∈ C, ι θ w = w := by
    intro w hw
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hw
    exact hθP u
  have hvC : v ∈ C := LinearMap.mem_range.mpr ⟨v, projP_of_fix hv⟩
  have hEC : ∀ e : E, C.map (ι e : V →ₗ[ZMod 2] V) = C := by
    intro e
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hx
      exact LinearMap.mem_range.mpr ⟨ι e w, (hcommP e w).symm⟩
    · intro x hx
      obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hx
      refine ⟨P (ι e⁻¹ w), LinearMap.mem_range_self P _, ?_⟩
      show ι e (P (ι e⁻¹ w)) = P w
      rw [hcommP, hinvapp]
  have hED : ∀ e : E, D.map (ι e : V →ₗ[ZMod 2] V) = D := by
    intro e
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      have hx' : P x = 0 := LinearMap.mem_ker.mp hx
      refine LinearMap.mem_ker.mpr ?_
      show P (ι e x) = 0
      rw [← hcommP, hx', map_zero]
    · intro x hx
      have hx' : P x = 0 := LinearMap.mem_ker.mp hx
      refine ⟨ι e⁻¹ x, LinearMap.mem_ker.mpr ?_, hinvapp e x⟩
      show P (ι e⁻¹ x) = 0
      rw [← hcommP, hx', map_zero]
  let ρC : E →* (C ≃ₗ[ZMod 2] C) :=
    { toFun := fun e => (ι e).ofSubmodules C C (hEC e)
      map_one' := LinearEquiv.ext fun x => Subtype.ext (by simp)
      map_mul' := fun a b => LinearEquiv.ext fun x => Subtype.ext (by
        simp [LinearEquiv.mul_apply]) }
  let ρD : E →* (D ≃ₗ[ZMod 2] D) :=
    { toFun := fun e => (ι e).ofSubmodules D D (hED e)
      map_one' := LinearEquiv.ext fun x => Subtype.ext (by simp)
      map_mul' := fun a b => LinearEquiv.ext fun x => Subtype.ext (by
        simp [LinearEquiv.mul_apply]) }
  have hθN : θ ∈ ρC.ker := by
    rw [MonoidHom.mem_ker]
    exact LinearEquiv.ext fun x => Subtype.ext (hfixC x x.2)
  have hle : π.ker ≤ ρC.ker := by
    rw [hker]
    exact Subgroup.zpowers_le.mpr hθN
  haveI : IsSimpleGroup X₀ := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F9 3 1
      (by rw [Nat.card_eq_fintype_card, F9.card_eq]; norm_num) 4 (by norm_num) (by decide)
    rwa [pow_one] at h
  have hsum : finrank (ZMod 2) C + finrank (ZMod 2) D = finrank (ZMod 2) V :=
    LinearMap.finrank_range_add_finrank_ker P
  have hCle : finrank (ZMod 2) C ≤ finrank (ZMod 2) V := Submodule.finrank_le C
  haveI : (ρC.ker.map π).Normal := Subgroup.Normal.map inferInstance π hπ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ρC.ker.map π) with hbot | htop
  ·
    let φ : X₀ →* (C ≃ₗ[ZMod 2] C) :=
      π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ) ⟨ρC, hle⟩
    have hφ : ∀ e : E, φ (π e) = ρC e := fun e =>
      MonoidHom.liftOfRightInverse_comp_apply (f := π) (f_inv := Function.surjInv hπ)
        (hf := Function.rightInverse_surjInv hπ) (g := ⟨ρC, hle⟩) (x := e)
    have hφinj : Function.Injective φ := by
      intro a b hab
      obtain ⟨a', rfl⟩ := hπ a
      obtain ⟨b', rfl⟩ := hπ b
      rw [hφ, hφ] at hab
      have hmem : a'⁻¹ * b' ∈ ρC.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
      have h1 : π (a'⁻¹ * b') ∈ ρC.ker.map π := Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
      rw [hbot, Subgroup.mem_bot, map_mul, map_inv, inv_mul_eq_one] at h1
      exact h1
    have h20 := twenty_le_finrank_of_faithful φ hφinj
    omega
  ·
    have hall : ∀ e : E, ρC e = 1 := by
      intro e
      obtain ⟨n, hn, hne⟩ := Subgroup.mem_map.mp
        (show π e ∈ ρC.ker.map π by rw [htop]; exact Subgroup.mem_top _)
      have h1 : n⁻¹ * e ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hne, inv_mul_cancel]
      have h2 := ρC.ker.mul_mem hn (hle h1)
      rw [mul_inv_cancel_left] at h2
      exact MonoidHom.mem_ker.mp h2
    have hfixall : ∀ (e : E) (w : V), w ∈ C → ι e w = w := fun e w hw =>
      congrArg (fun f : C ≃ₗ[ZMod 2] C => ((f ⟨w, hw⟩ : C) : V)) (hall e)
    have hinj : Function.Injective ρD := by
      rw [injective_iff_map_eq_one]
      intro e he
      apply hι
      rw [map_one]
      refine LinearEquiv.ext fun w => ?_
      have hwD : w - P w ∈ D := LinearMap.mem_ker.mpr (by
        show P (w - P w) = 0
        rw [map_sub, hPP, sub_self])
      have h1 : ι e (P w) = P w := hfixall e _ (LinearMap.mem_range_self P w)
      have h2 : ι e (w - P w) = w - P w :=
        congrArg (fun f : D ≃ₗ[ZMod 2] D => ((f ⟨w - P w, hwD⟩ : D) : V)) he
      have hw : w = P w + (w - P w) := by abel
      rw [hw, map_add, h1, h2]
      rfl
    have hCpos : finrank (ZMod 2) C ≠ 0 := by
      intro h
      rw [Submodule.finrank_eq_zero] at h
      rw [h, Submodule.mem_bot] at hvC
      exact hv0 hvC
    exact not_three_pow_seven_dvd_card_GL (W := D) (by omega)
      (h37.trans (Subgroup.card_dvd_of_injective ρD hinj))

end CFSG.GF2Type.Smith1979.IdxFour
