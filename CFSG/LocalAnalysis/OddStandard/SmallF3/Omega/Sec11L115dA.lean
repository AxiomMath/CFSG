module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109A2Gen

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec11d_descent {A B X : Type*} [Group A] [Group B] [Group X] (Pi : A →* B)
    (hPi : Function.Surjective Pi) (c : X →* MulAut A)
    (hker : ∀ (x : X) (a : A), Pi a = 1 → Pi (c x a) = 1) :
    ∃ f : X →* MulAut B, ∀ (x : X) (a : A), f x (Pi a) = Pi (c x a) := by
  classical
  set s : B → A := Function.surjInv hPi with hs
  have hss : ∀ b, Pi (s b) = b := Function.surjInv_eq hPi
  have hwd : ∀ (x : X) (a a' : A), Pi a = Pi a' → Pi (c x a) = Pi (c x a') := by
    intro x a a' h
    have h1 : Pi (a'⁻¹ * a) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have h2 := hker x _ h1
    rw [map_mul, map_inv, map_mul, map_inv] at h2
    exact (inv_mul_eq_one.mp h2).symm
  let F : X → B → B := fun x b => Pi (c x (s b))
  have hF : ∀ (x : X) (a : A), F x (Pi a) = Pi (c x a) := fun x a => hwd x _ _ (hss _)
  have hFmul : ∀ (x : X) (b b' : B), F x (b * b') = F x b * F x b' := by
    intro x b b'
    have e : b * b' = Pi (s b * s b') := by rw [map_mul, hss, hss]
    rw [e, hF, map_mul, map_mul]
  have hF1 : ∀ b : B, F 1 b = b := by
    intro b
    obtain ⟨a, rfl⟩ := hPi b
    rw [hF, map_one]
    rfl
  have hFcomp : ∀ (x x' : X) (b : B), F (x * x') b = F x (F x' b) := by
    intro x x' b
    obtain ⟨a, rfl⟩ := hPi b
    have h2 : c (x * x') a = c x (c x' a) :=
      congrArg (fun φ : MulAut A => φ a) (map_mul c x x')
    rw [hF x' a, hF x (c x' a), hF (x * x') a, h2]
  let f : X → MulAut B := fun x =>
    { toFun := F x
      invFun := F x⁻¹
      left_inv := fun b => by rw [← hFcomp, inv_mul_cancel, hF1]
      right_inv := fun b => by rw [← hFcomp, mul_inv_cancel, hF1]
      map_mul' := hFmul x }
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, fun x a => hF x a⟩
  · exact MulEquiv.ext hF1
  · intro x x'
    exact MulEquiv.ext fun b => hFcomp x x' b

theorem IsDirectSplit.exists_proj {N K K0 : Subgroup G} (D : IsDirectSplit N K K0) :
    ∃ Pr : ↥K0 →* ↥K, (∀ x : ↥K0, ∃ n ∈ N, (x : G) = n * (Pr x : G)) ∧
      ∀ (x : ↥K0) (n : G) (κ : ↥K), n ∈ N → (x : G) = n * (κ : G) → Pr x = κ := by
  classical
  have hex : ∀ x : ↥K0, ∃ n ∈ N, ∃ k ∈ K, (x : G) = n * k := fun x => D.dec _ x.2
  choose nn hnn kk hkk hx using hex
  have huniq : ∀ (x : ↥K0) (n κ : G), n ∈ N → κ ∈ K → (x : G) = n * κ → kk x = κ := by
    intro x n κ hn hκ h
    exact (D.unique (hnn x) hn (hkk x) hκ ((hx x).symm.trans h)).2
  refine ⟨{ toFun := fun x => ⟨kk x, hkk x⟩, map_one' := ?_, map_mul' := ?_ },
    fun x => ⟨nn x, hnn x, hx x⟩, fun x n κ hn h => Subtype.ext (huniq x n κ hn κ.2 h)⟩
  · exact Subtype.ext (huniq 1 1 1 N.one_mem K.one_mem (by simp))
  · intro x y
    have hc := D.comm (nn y) (hnn y) (kk x) (hkk x)
    refine Subtype.ext (huniq (x * y) (nn x * nn y) (kk x * kk y)
      (N.mul_mem (hnn x) (hnn y)) (K.mul_mem (hkk x) (hkk y)) ?_)
    calc ((x * y : ↥K0) : G) = (x : G) * (y : G) := rfl
      _ = (nn x * kk x) * (nn y * kk y) := by rw [hx x, hx y]
      _ = nn x * (kk x * nn y) * kk y := by group
      _ = nn x * (nn y * kk x) * kk y := by rw [← hc]
      _ = (nn x * nn y) * (kk x * kk y) := by group

theorem sec11d_mem_sup {A N : Subgroup G} (h : ∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) :
    ∀ x ∈ A ⊔ N, ∃ a ∈ A, ∃ n ∈ N, x = a * n := by
  let U : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ n ∈ N, x = a * n}
      mul_mem' := by
        rintro _ _ ⟨a, ha, n, hn, rfl⟩ ⟨a', ha', n', hn', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', (a'⁻¹ * n * a'⁻¹⁻¹) * n', ?_, ?_⟩
        · exact N.mul_mem (h a'⁻¹ (A.inv_mem ha') n hn) hn'
        · group
      one_mem' := ⟨1, A.one_mem, 1, N.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, n, hn, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, a * n⁻¹ * a⁻¹, h a ha n⁻¹ (N.inv_mem hn), ?_⟩
        group }
  have hle : A ⊔ N ≤ U :=
    sup_le (fun x hx => ⟨x, hx, 1, N.one_mem, by simp⟩) (fun x hx => ⟨1, A.one_mem, x, hx, by simp⟩)
  intro x hx
  exact hle hx

end CFSG.OddStandard.SmallF3.Omega
