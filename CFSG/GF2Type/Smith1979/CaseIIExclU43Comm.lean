module

public import CFSG.GF2Type.Smith1979.CaseIIExclU43Orb

public section

namespace CFSG.GF2Type.Smith1979.Case2.U43Grp

@[expose] def cmG {G : Type} [Group G] (a b : G) : G := a * b * a⁻¹ * b⁻¹

section Commutators

variable {G : Type} [Group G]

theorem cmG_mul_left (a b c : G) : cmG (a * b) c = a * cmG b c * a⁻¹ * cmG a c := by
  simp only [cmG]
  group

theorem cmG_mul_right (a b c : G) : cmG a (b * c) = cmG a b * (b * cmG a c * b⁻¹) := by
  simp only [cmG]
  group

theorem cmG_self (a : G) : cmG a a = 1 := by
  simp only [cmG]
  group

theorem cmG_mul_central {z : G} (hz : ∀ g : G, z * g = g * z) (a b : G) :
    cmG (a * z) b = cmG a b := by
  have hzb : z * b = b * z := hz b
  calc cmG (a * z) b = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by
        simp only [cmG]
        group
    _ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [hzb]
    _ = cmG a b := by
        simp only [cmG]
        group

theorem cmG_mul_central_right {z : G} (hz : ∀ g : G, z * g = g * z) (a b : G) :
    cmG a (b * z) = cmG a b := by
  have h : z * a⁻¹ = a⁻¹ * z := hz a⁻¹
  calc cmG a (b * z) = a * b * (z * a⁻¹) * z⁻¹ * b⁻¹ := by
        simp only [cmG]
        group
    _ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by rw [h]
    _ = cmG a b := by
        simp only [cmG]
        group

theorem cmG_sq_eq_one {a b : G} (hq : ∀ g : G, a * a * g = g * (a * a))
    (hc : ∀ g : G, cmG a b * g = g * cmG a b) : cmG a b * cmG a b = 1 := by
  set c := cmG a b with hcdef
  have hab : a * b = c * b * a := by
    rw [hcdef]
    simp only [cmG]
    group
  have hac : a * c = c * a := (hc a).symm
  have h1 : a * a * b = c * (c * (b * (a * a))) := by
    calc a * a * b = a * (a * b) := by group
      _ = a * (c * b * a) := by rw [hab]
      _ = (a * c) * b * a := by group
      _ = (c * a) * b * a := by rw [hac]
      _ = c * (a * b * a) := by group
      _ = c * (c * (b * (a * a))) := by rw [hab]; group
  have h2 : a * a * b = b * (a * a) := hq b
  have h3 : c * c * (b * (a * a)) = 1 * (b * (a * a)) := by
    rw [one_mul]
    calc c * c * (b * (a * a)) = c * (c * (b * (a * a))) := by group
      _ = a * a * b := h1.symm
      _ = b * (a * a) := h2
  exact mul_right_cancel h3

end Commutators

structure LiftSetup (G X : Type) [Group G] [Group X] where
  ψ : G →* X
  lift : X → G
  hlift : ∀ x, ψ (lift x) = x
  neg : G
  neg_ne_one : neg ≠ 1
  neg_mul_self : neg * neg = 1
  ker_neg : ψ neg = 1
  ker_central : ∀ z : G, ψ z = 1 → ∀ g : G, z * g = g * z
  ker_pow_four : ∀ z : G, ψ z = 1 → z ^ 4 = 1
  ker_sq : ∀ z : G, ψ z = 1 → z * z = 1 → z = 1 ∨ z = neg
  ker_sqrt : ∃ i : G, ψ i = 1 ∧ i * i = neg

namespace LiftSetup

variable {G X : Type} [Group G] [Group X]

@[expose] def beta (D : LiftSetup G X) (x x' : X) : G := cmG (D.lift x) (D.lift x')

variable (D : LiftSetup G X)

theorem psi_beta (x x' : X) : D.ψ (D.beta x x') = cmG x x' := by
  simp only [beta, cmG, map_mul, map_inv, D.hlift]

theorem comm_of_mem {S : Subgroup X} (hS2 : ∀ s ∈ S, s * s = 1) {a b : X} (ha : a ∈ S)
    (hb : b ∈ S) : a * b = b * a := by
  have hab := hS2 _ (S.mul_mem ha hb)
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [inv_eq_of_mul_eq_one_right (hS2 b hb),
        inv_eq_of_mul_eq_one_right (hS2 a ha)]

theorem beta_ker {S : Subgroup X} (hS2 : ∀ s ∈ S, s * s = 1) {x x' : X} (hx : x ∈ S)
    (hx' : x' ∈ S) : D.ψ (D.beta x x') = 1 := by
  rw [psi_beta]
  have h := comm_of_mem hS2 hx hx'
  simp only [cmG]
  calc x * x' * x⁻¹ * x'⁻¹ = x' * x * x⁻¹ * x'⁻¹ := by rw [h]
    _ = 1 := by group

theorem beta_central {S : Subgroup X} (hS2 : ∀ s ∈ S, s * s = 1) {x x' : X} (hx : x ∈ S)
    (hx' : x' ∈ S) (g : G) : D.beta x x' * g = g * D.beta x x' :=
  D.ker_central _ (D.beta_ker hS2 hx hx') g

theorem beta_self (x : X) : D.beta x x = 1 := cmG_self _

theorem beta_sq {S : Subgroup X} (hS2 : ∀ s ∈ S, s * s = 1) {x x' : X} (hx : x ∈ S)
    (hx' : x' ∈ S) : D.beta x x' * D.beta x x' = 1 := by
  apply cmG_sq_eq_one
  · intro g
    apply D.ker_central
    rw [map_mul, D.hlift, hS2 x hx]
  · intro g
    exact D.beta_central hS2 hx hx' g

theorem beta_val {S : Subgroup X} (hS2 : ∀ s ∈ S, s * s = 1) {x x' : X} (hx : x ∈ S)
    (hx' : x' ∈ S) : D.beta x x' = 1 ∨ D.beta x x' = D.neg :=
  D.ker_sq _ (D.beta_ker hS2 hx hx') (D.beta_sq hS2 hx hx')

theorem beta_mul_left {S : Subgroup X} (hS2 : ∀ s ∈ S, s * s = 1) {x x' z : X} (hx : x ∈ S)
    (hx' : x' ∈ S) (hz : z ∈ S) : D.beta (x * x') z = D.beta x z * D.beta x' z := by
  have hcomm : x' * z = z * x' := comm_of_mem hS2 hx' hz
  set k := (D.lift x * D.lift x')⁻¹ * D.lift (x * x') with hk
  have hkψ : D.ψ k = 1 := by
    rw [hk, map_mul, map_inv, map_mul, D.hlift, D.hlift, D.hlift]
    group
  have hkc : ∀ g, k * g = g * k := D.ker_central k hkψ
  have hlift' : D.lift (x * x') = D.lift x * D.lift x' * k := by
    rw [hk]
    group
  have hbeta : D.beta (x * x') z = cmG (D.lift x * D.lift x') (D.lift z) := by
    unfold beta
    rw [hlift', cmG_mul_central hkc]
  rw [hbeta, cmG_mul_left]
  have hc : ∀ g, D.beta x' z * g = g * D.beta x' z := D.beta_central hS2 hx' hz
  show D.lift x * D.beta x' z * (D.lift x)⁻¹ * D.beta x z = D.beta x z * D.beta x' z
  rw [← hc (D.lift x), mul_inv_cancel_right]
  exact hc (D.beta x z)

theorem beta_mul_right {S : Subgroup X} (hS2 : ∀ s ∈ S, s * s = 1) {x z z' : X} (hx : x ∈ S)
    (hz : z ∈ S) (hz' : z' ∈ S) : D.beta x (z * z') = D.beta x z * D.beta x z' := by
  have hcomm : x * z' = z' * x := comm_of_mem hS2 hx hz'
  set k := (D.lift z * D.lift z')⁻¹ * D.lift (z * z') with hk
  have hkψ : D.ψ k = 1 := by
    rw [hk, map_mul, map_inv, map_mul, D.hlift, D.hlift, D.hlift]
    group
  have hkc : ∀ g, k * g = g * k := D.ker_central k hkψ
  have hlift' : D.lift (z * z') = D.lift z * D.lift z' * k := by
    rw [hk]
    group
  have hbeta : D.beta x (z * z') = cmG (D.lift x) (D.lift z * D.lift z') := by
    unfold beta
    rw [hlift', cmG_mul_central_right hkc]
  rw [hbeta, cmG_mul_right]
  have hc : ∀ g, D.beta x z' * g = g * D.beta x z' := D.beta_central hS2 hx hz'
  show D.beta x z * (D.lift z * D.beta x z' * (D.lift z)⁻¹) = D.beta x z * D.beta x z'
  rw [← hc (D.lift z), mul_inv_cancel_right]

theorem beta_symm {S : Subgroup X} (hS2 : ∀ s ∈ S, s * s = 1) {x x' : X} (hx : x ∈ S)
    (hx' : x' ∈ S) : D.beta x' x = D.beta x x' := by
  have hu : x * x' ∈ S := S.mul_mem hx hx'
  have hcomm := comm_of_mem hS2 hx hx'
  have h0 : D.beta (x * x') (x * x') = 1 := beta_self D _
  have h1 : D.beta (x * x') (x * x') = D.beta x (x * x') * D.beta x' (x * x') :=
    D.beta_mul_left hS2 hx hx' hu
  have h2 : D.beta x (x * x') = D.beta x x' := by
    rw [D.beta_mul_right hS2 hx hx hx', D.beta_self, one_mul]
  have h3 : D.beta x' (x * x') = D.beta x' x := by
    rw [D.beta_mul_right hS2 hx' hx hx', D.beta_self, mul_one]
  rw [h2, h3] at h1
  have h4 : D.beta x x' * D.beta x' x = 1 := h1.symm.trans h0
  have h5 : D.beta x x' * D.beta x x' = 1 := D.beta_sq hS2 hx hx'
  calc D.beta x' x = (D.beta x x')⁻¹ := (eq_inv_of_mul_eq_one_right h4)
    _ = D.beta x x' := inv_eq_of_mul_eq_one_right h5

theorem beta_one_left (x : X) : D.beta 1 x = 1 := by
  have hψ : D.ψ (D.lift 1) = 1 := D.hlift 1
  have hc := D.ker_central _ hψ (D.lift x)
  unfold beta
  simp only [cmG]
  rw [hc]
  group

theorem beta_one_right (x : X) : D.beta x 1 = 1 := by
  have hψ : D.ψ (D.lift 1) = 1 := D.hlift 1
  have hc := D.ker_central _ hψ (D.lift x)
  unfold beta
  simp only [cmG]
  rw [← hc]
  group

end LiftSetup

end CFSG.GF2Type.Smith1979.Case2.U43Grp
