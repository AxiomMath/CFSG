module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelSuzukiRoot
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelSuzukiTriple

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC

open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFAppendixIII

namespace BorelSuzuki

variable (m : ℕ)

local notation "K" => BinaryGaloisField (2 * m + 1)
local notation "G" => SuzukiMatrixGroup m

theorem torus_conj_root (x : Kˣ) (a b : K) :
    (suzukiCoverTorusHom m x : G) * suzukiCoverRootElement m a b *
        (suzukiCoverTorusHom m x : G)⁻¹ =
      suzukiCoverRootElement m ((x : K) * a) ((x : K) * suzukiCoverTits m (x : K) * b) :=
  congrArg (fun z : suzukiCoverRoot m => (z : G)) (suzukiCoverTorus_action_root m x a b)

theorem torus_transitive (hm : 0 < m) (w w' : G) (hw : InCenterOf (suzukiCoverRoot m) w)
    (hw1 : w ≠ 1) (hw' : InCenterOf (suzukiCoverRoot m) w') (hw'1 : w' ≠ 1) :
    ∃ d ∈ suzukiCoverTorus m, d⁻¹ * w * d = w' := by
  obtain ⟨b, rfl⟩ := (inCenterOf_iff m hm w).mp hw
  obtain ⟨b', rfl⟩ := (inCenterOf_iff m hm w').mp hw'
  have hne : ∀ c : K, (suzukiCoverRootElement m 0 c : G) ≠ 1 → c ≠ 0 := by
    rintro c hc rfl
    exact hc (by rw [suzukiCoverRootElement_zero_zero]; rfl)
  have hb := hne b hw1
  have hb' := hne b' hw'1
  obtain ⟨x, hx⟩ := (suzukiCoverNorm_bijective m).2 (Units.mk0 (b' / b) (div_ne_zero hb' hb))
  have hx' : (x : K) * suzukiCoverTits m (x : K) = b' / b := by
    rw [← suzukiCoverNorm_coe, hx, Units.val_mk0]
  refine ⟨(suzukiCoverTorusHom m x : G)⁻¹, inv_mem (suzukiCoverTorusHom m x).2, ?_⟩
  rw [inv_inv, torus_conj_root, mul_zero, hx', div_mul_cancel₀ _ hb]

theorem forms_symm (β : G → G → ZMod 2)
    (h1 : ∀ a ∈ suzukiCoverRoot m, ∀ b ∈ suzukiCoverRoot m, ∀ c ∈ suzukiCoverRoot m,
      β (a * b) c = β a c + β b c)
    (h2 : ∀ a ∈ suzukiCoverRoot m, ∀ b ∈ suzukiCoverRoot m, ∀ c ∈ suzukiCoverRoot m,
      β a (b * c) = β a b + β a c)
    (h3 : ∀ a ∈ suzukiCoverRoot m, β a a = 0) {a b : G} (ha : a ∈ suzukiCoverRoot m)
    (hb : b ∈ suzukiCoverRoot m) : β a b = β b a := by
  have hab := (suzukiCoverRoot m).mul_mem ha hb
  have h := h3 _ hab
  rw [h1 a ha b hb _ hab, h2 a ha a ha b hb, h2 b hb a ha b hb, h3 a ha, h3 b hb, zero_add,
    add_zero] at h
  exact CharTwo.add_eq_zero.mp h

theorem torus_forms (hm : 0 < m) (β : G → G → ZMod 2)
    (h1 : ∀ a ∈ suzukiCoverRoot m, ∀ b ∈ suzukiCoverRoot m, ∀ c ∈ suzukiCoverRoot m,
      β (a * b) c = β a c + β b c)
    (h2 : ∀ a ∈ suzukiCoverRoot m, ∀ b ∈ suzukiCoverRoot m, ∀ c ∈ suzukiCoverRoot m,
      β a (b * c) = β a b + β a c)
    (h3 : ∀ a ∈ suzukiCoverRoot m, β a a = 0)
    (h4 : ∀ a ∈ suzukiCoverRoot m, ∀ b : G, InCenterOf (suzukiCoverRoot m) b → β a b = 0)
    (h5 : ∀ d ∈ suzukiCoverTorus m, ∀ a ∈ suzukiCoverRoot m, ∀ b ∈ suzukiCoverRoot m,
      β (d⁻¹ * a * d) (d⁻¹ * b * d) = β a b) :
    ∀ a ∈ suzukiCoverRoot m, ∀ b ∈ suzukiCoverRoot m, β a b = 0 := by
  let S : K → K → G := fun a b => suzukiCoverRootElement m a b
  have hS : ∀ a b, S a b ∈ suzukiCoverRoot m := fun a b => (suzukiCoverRootElement m a b).2
  have hZ : ∀ b, InCenterOf (suzukiCoverRoot m) (S 0 b) := inCenterOf_root_zero m hm
  have hZr : ∀ a b c, β (S a b) (S 0 c) = 0 := fun a b c => h4 _ (hS a b) _ (hZ c)
  have hZl : ∀ a b c, β (S 0 c) (S a b) = 0 := fun a b c => by
    rw [forms_symm m β h1 h2 h3 (hS 0 c) (hS a b), hZr]
  have hred : ∀ a b c d, β (S a b) (S c d) = β (S a 0) (S c 0) := by
    intro a b c d
    change β (suzukiCoverRootElement m a b : G) (suzukiCoverRootElement m c d) = _
    rw [root_eq_mul m hm a b, root_eq_mul m hm c d, h1 _ (hS a 0) _ (hS 0 b) _
      ((suzukiCoverRoot m).mul_mem (hS c 0) (hS 0 d)), h2 _ (hS a 0) _ (hS c 0) _ (hS 0 d),
      h2 _ (hS 0 b) _ (hS c 0) _ (hS 0 d)]
    simp only [hZr, hZl, add_zero]
  have hmul : ∀ a c, S a 0 * S c 0 = S (a + c) (a * suzukiCoverTits m c) := by
    intro a c
    change (suzukiCoverRootElement m a 0 : G) * suzukiCoverRootElement m c 0 = _
    rw [root_mul m hm, zero_add, zero_add]
  have hcard : 4 < Nat.card K := by
    rw [GaloisField.card 2 (2 * m + 1) (by omega)]
    calc 4 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hf := biadditive_eq_zero_of_smul_invariant (F := K) hcard
    (fun a c : K => β (S a 0) (S c 0))
    (fun a a' c => by
      change β (S (a + a') 0) (S c 0) = β (S a 0) (S c 0) + β (S a' 0) (S c 0)
      rw [← h1 _ (hS a 0) _ (hS a' 0) _ (hS c 0), hmul, hred _ (a * suzukiCoverTits m a')])
    (fun a c c' => by
      change β (S a 0) (S (c + c') 0) = β (S a 0) (S c 0) + β (S a 0) (S c' 0)
      rw [← h2 _ (hS a 0) _ (hS c 0) _ (hS c' 0), hmul, hred a 0 _ (c * suzukiCoverTits m c')])
    (fun x hx a c => by
      change β (S (x * a) 0) (S (x * c) 0) = β (S a 0) (S c 0)
      let t : G := suzukiCoverTorusHom m (Units.mk0 x hx)
      have ht : ∀ a, t * S a 0 * t⁻¹ = S (x * a) 0 := fun a => by
        change (suzukiCoverTorusHom m (Units.mk0 x hx) : G) * suzukiCoverRootElement m a 0 *
          (suzukiCoverTorusHom m (Units.mk0 x hx) : G)⁻¹ = _
        rw [torus_conj_root, mul_zero, Units.val_mk0]
      have h := h5 t⁻¹ (inv_mem (suzukiCoverTorusHom m (Units.mk0 x hx)).2) _ (hS a 0) _ (hS c 0)
      rwa [inv_inv, ht, ht] at h)
  intro a ha b hb
  obtain ⟨x, u, rfl⟩ := exists_eq_root m ha
  obtain ⟨y, v, rfl⟩ := exists_eq_root m hb
  exact (hred x u y v).trans (hf x y)

end BorelSuzuki

end CFSG.ProperTwoGeneratedCore.TheoremC
