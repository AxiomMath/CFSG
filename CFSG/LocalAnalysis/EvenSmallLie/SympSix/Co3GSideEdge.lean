module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentBridge
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentRigid
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentCube

public section

namespace CFSG.EvenSmallLie.SympSix.Co3Ident

open Subgroup CFSG.Sporadic.Schreier.Co3

theorem orderOf_conj_eq {X : Type*} [Group X] (c x : X) : orderOf (c * x * c⁻¹) = orderOf x := by
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]

theorem mul_self_of_orderOf {X : Type*} [Group X] {x : X} (h : orderOf x = 2) : x * x = 1 := by
  rw [← pow_two, ← h, pow_orderOf_eq_one]

theorem orderOf_of_mem_classA
    {x : co3M} (hx : x ∈ classA) : orderOf x = 2 := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hx
  rw [orderOf_conj_eq]
  exact involutions.1

theorem co3ZM_mul_self
    : co3ZM * co3ZM = 1 := mul_self_of_orderOf orderOf_co3ZM

theorem ma_ne_co3ZM :
    ma ≠ co3ZM := by
  rw [← me_eq]
  exact involutions.2.2

section Generic

variable {X : Type*} [Group X]

theorem comm_conj_inv {c s f x : X} (hc : c * s * c⁻¹ = f) (hx : x * f = f * x) :
    (c⁻¹ * x * c) * s = s * (c⁻¹ * x * c) := by
  subst hc
  calc c⁻¹ * x * c * s = c⁻¹ * (x * (c * s * c⁻¹)) * c := by group
    _ = c⁻¹ * ((c * s * c⁻¹) * x) * c := by rw [hx]
    _ = s * (c⁻¹ * x * c) := by group

theorem conj_eq_of_eq_conj_inv {c s x : X} (h : s = c⁻¹ * x * c) : x = c * s * c⁻¹ := by
  rw [h]
  group

theorem conj_conj_eq {c m s x : X} (hm : m * (c⁻¹ * s * c) * m⁻¹ = c⁻¹ * x * c) :
    c * m * c⁻¹ * s * (c * m * c⁻¹)⁻¹ = x := by
  calc c * m * c⁻¹ * s * (c * m * c⁻¹)⁻¹ = c * (m * (c⁻¹ * s * c) * m⁻¹) * c⁻¹ := by group
    _ = c * (c⁻¹ * x * c) * c⁻¹ := by rw [hm]
    _ = x := by group

theorem conj_conj_fix {c m s f : X} (hc : c * s * c⁻¹ = f) (hm : m * s = s * m) :
    c * m * c⁻¹ * f * (c * m * c⁻¹)⁻¹ = f := by
  subst hc
  calc c * m * c⁻¹ * (c * s * c⁻¹) * (c * m * c⁻¹)⁻¹ = c * ((m * s) * m⁻¹) * c⁻¹ := by group
    _ = c * s * c⁻¹ := by rw [hm, mul_inv_cancel_right]

theorem conj_swap_of_fix {g s a f : X} (h1 : g * s * g⁻¹ = a) (h2 : g * f * g⁻¹ = f)
    (hf : f = s * a) (hss : s * s = 1) (haa : a * a = 1) (has : a * s = s * a) :
    g * a * g⁻¹ = s := by
  have ha : a = s * f := by rw [hf, ← mul_assoc, hss, one_mul]
  calc g * a * g⁻¹ = (g * s * g⁻¹) * (g * f * g⁻¹) := by rw [ha]; group
    _ = a * (s * a) := by rw [h1, h2, hf]
    _ = s := by rw [← mul_assoc, has, mul_assoc, haa, mul_one]

theorem conj_comm_conj {g a x : X} (hx : x * a = a * x) :
    (g * x * g⁻¹) * (g * a * g⁻¹) = (g * a * g⁻¹) * (g * x * g⁻¹) := by
  calc (g * x * g⁻¹) * (g * a * g⁻¹) = g * (x * a) * g⁻¹ := by group
    _ = g * (a * x) * g⁻¹ := by rw [hx]
    _ = (g * a * g⁻¹) * (g * x * g⁻¹) := by group

theorem inv_conj_of_conj {g a b : X} (h : g * a * g⁻¹ = b) : g⁻¹ * b * g⁻¹⁻¹ = a := by
  rw [← h]
  group

theorem comm_of_conj_eq {u a : X} (h : u * a * u⁻¹ = a) : u * a = a * u := by
  calc u * a = u * a * u⁻¹ * u := by group
    _ = a * u := by rw [h]

theorem cube_comm {u a b c : X} (h1 : u * a * u⁻¹ = b) (h2 : u * b * u⁻¹ = c)
    (h3 : u * c * u⁻¹ = a) : u ^ 3 * a = a * u ^ 3 := by
  calc u ^ 3 * a = u * (u * (u * a * u⁻¹) * u⁻¹) * u⁻¹ * u ^ 3 := by rw [pow_three]; group
    _ = a * u ^ 3 := by rw [h1, h2, h3]

theorem mul_mul_self_of_comm {a b : X} (hab : a * b = b * a) (ha : a * a = 1) (hb : b * b = 1) :
    a * b * (a * b) = 1 := by
  calc a * b * (a * b) = a * (b * a) * b := by group
    _ = 1 := by rw [← hab, ← mul_assoc, ha, one_mul, hb]

end Generic

section Theta

variable
    {G : Type*} [Group G] {s : G} (θ : co3M ≃* centralizer ({s} : Set G))

@[expose] noncomputable def thetaHom :
    co3M →* G :=
  (centralizer ({s} : Set G)).subtype.comp θ.toMonoidHom

theorem thetaHom_apply
    (x : co3M) : thetaHom θ x = (θ x : G) := rfl

theorem theta_inj
    {x y : co3M} (h : (θ x : G) = θ y) : x = y :=
  θ.injective (Subtype.ext h)

theorem theta_mul
    (x y : co3M) : (θ (x * y) : G) = θ x * θ y := by simp

theorem theta_inv
    (x : co3M) : (θ x⁻¹ : G) = (θ x : G)⁻¹ := by simp

theorem theta_one : (θ 1 : G) = 1 := by simp

theorem theta_conj
    (c x : co3M) :
    (θ (c * x * c⁻¹) : G) = (θ c : G) * θ x * (θ c : G)⁻¹ := by simp

theorem theta_comm_s
    (x : co3M) : (θ x : G) * s = s * θ x :=
  mem_centralizer_singleton_iff.1 (θ x).2

theorem exists_theta_eq
    {g : G} (hg : g * s = s * g) : ∃ x : co3M, (θ x : G) = g :=
  ⟨θ.symm ⟨g, mem_centralizer_singleton_iff.2 hg⟩, by simp⟩

theorem theta_comm_iff
    (x y : co3M) : (θ x : G) * θ y = θ y * θ x ↔ x * y = y * x := by
  rw [← theta_mul, ← theta_mul]
  exact ⟨fun h => theta_inj θ h, fun h => by rw [h]⟩

theorem theta_orderOf
    (x : co3M) : orderOf (θ x : G) = orderOf x := by
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]

theorem theta_me
    (hθ : (θ co3ZM : G) = s) : (θ me : G) = s := by rw [me_eq, hθ]

theorem theta_eH
    (hθ : (θ co3ZM : G) = s) : (θ (eH : co3M) : G) = s := theta_me θ hθ

theorem s_mul_self
    (hθ : (θ co3ZM : G) = s) : s * s = 1 := by
  rw [← hθ, ← theta_mul, co3ZM_mul_self, theta_one]

theorem s_ne_one
    (hθ : (θ co3ZM : G) = s) : s ≠ 1 := by
  intro h
  have h1 := theta_orderOf θ co3ZM
  rw [hθ, h, orderOf_one, orderOf_co3ZM] at h1
  exact absurd h1 (by decide)

theorem theta_ma_mul_self :
    (θ ma : G) * θ ma = 1 := by
  rw [← theta_mul, ma_mul_self, theta_one]

theorem theta_ma_comm :
    (θ ma : G) * s = s * θ ma :=
  theta_comm_s θ ma

theorem theta_ma_ne_s
    (hθ : (θ co3ZM : G) = s) : (θ ma : G) ≠ s := fun h =>
  ma_ne_co3ZM (theta_inj θ (h.trans hθ.symm))

theorem mem_edgeGroup_of_theta
    {x : co3M} (h : (θ x : G) * θ ma = θ ma * θ x) : x ∈ edgeGroup :=
  mem_centralizer_singleton_iff.2 ((theta_comm_iff θ x ma).1 h)

theorem theta_comm_ma
    (x : edgeGroup) : (θ (x : co3M) : G) * θ ma = θ ma * θ (x : co3M) :=
  (theta_comm_iff θ _ _).2 (mem_centralizer_singleton_iff.1 x.2)

theorem theta_edge_inj
    {x y : edgeGroup} (h : (θ (x : co3M) : G) = θ (y : co3M)) : x = y :=
  Subtype.ext (theta_inj θ h)

theorem theta_edge_mul
    (x y : edgeGroup) :
    (θ ((x * y : edgeGroup) : co3M) : G) = θ (x : co3M) * θ (y : co3M) := by
  rw [Subgroup.coe_mul, theta_mul]

theorem exists_edge_swap
    (hθ : (θ co3ZM : G) = s)
    (hH2 : ∀ x : co3M, orderOf x = 2 → (IsConj s (θ x : G) ↔ x = co3ZM ∨ x ∈ classA)) :
    ∃ g : G, g * s * g⁻¹ = θ ma ∧ g * θ ma * g⁻¹ = s := by
  have he := theta_me θ hθ
  have hss := s_mul_self θ hθ
  have haa := theta_ma_mul_self θ
  have has := theta_ma_comm θ
  have hea : me * ma ∈ classA := classA_facts.2.1
  obtain ⟨c, hc⟩ := isConj_iff.1 ((hH2 _ (orderOf_of_mem_classA hea)).2 (Or.inr hea))
  set f : G := (θ (me * ma) : G) with hfdef
  have hf : f = s * θ ma := by rw [hfdef, theta_mul, he]
  have hfs : s * f = f * s := (theta_comm_s θ _).symm
  have hfa : (θ ma : G) * f = f * θ ma := by
    rw [hf, ← mul_assoc, ← has, mul_assoc]
  obtain ⟨x₁, hx₁⟩ := exists_theta_eq θ (comm_conj_inv hc hfs)
  obtain ⟨x₂, hx₂⟩ := exists_theta_eq θ (comm_conj_inv hc hfa)
  have ho₁ : orderOf x₁ = 2 := by
    rw [← theta_orderOf θ, hx₁, show c⁻¹ * s * c = c⁻¹ * s * c⁻¹⁻¹ by rw [inv_inv],
      orderOf_conj_eq, ← he, theta_orderOf, me_eq, orderOf_co3ZM]
  have ho₂ : orderOf x₂ = 2 := by
    rw [← theta_orderOf θ, hx₂, show c⁻¹ * θ ma * c = c⁻¹ * θ ma * c⁻¹⁻¹ by rw [inv_inv],
      orderOf_conj_eq, theta_orderOf]
    exact involutions.1
  have hs₁ : IsConj s (θ x₁ : G) := by
    rw [hx₁]
    exact isConj_iff.2 ⟨c⁻¹, by rw [inv_inv]⟩
  have hs₂ : IsConj s (θ x₂ : G) := by
    rw [hx₂]
    exact ((hH2 ma involutions.1).2 (Or.inr (IsConj.refl ma))).trans
      (isConj_iff.2 ⟨c⁻¹, by rw [inv_inv]⟩)
  have hz₁ : x₁ ≠ co3ZM := by
    intro h
    rw [h, hθ] at hx₁
    have h' : (θ (me * ma) : G) = θ me := by
      rw [← hfdef, ← hc, he, ← conj_eq_of_eq_conj_inv hx₁]
    exact ma_ne_one (mul_eq_left.1 (theta_inj θ h'))
  have hz₂ : x₂ ≠ co3ZM := by
    intro h
    rw [h, hθ] at hx₂
    have h' : (θ (me * ma) : G) = θ ma := by
      rw [← hfdef, ← hc, ← conj_eq_of_eq_conj_inv hx₂]
    have he1 : me = 1 := mul_eq_right.1 (theta_inj θ h')
    exact s_ne_one θ hθ (by rw [← he, he1, theta_one])
  have hA₁ := ((hH2 x₁ ho₁).1 hs₁).resolve_left hz₁
  have hA₂ := ((hH2 x₂ ho₂).1 hs₂).resolve_left hz₂
  obtain ⟨m, hm⟩ := isConj_iff.1 ((isConj_comm.1 hA₁).trans hA₂)
  have hm' : (θ m : G) * (c⁻¹ * s * c) * (θ m : G)⁻¹ = c⁻¹ * θ ma * c := by
    rw [← hx₁, ← hx₂, ← theta_conj, hm]
  have key1 := conj_conj_eq hm'
  exact ⟨_, key1, conj_swap_of_fix key1 (conj_conj_fix hc (theta_comm_s θ m)) hf hss haa has⟩

section Swap

variable {g : G}

theorem swap_comm_s
    (h2 : g * θ ma * g⁻¹ = s) (x : edgeGroup) :
    (g * θ (x : co3M) * g⁻¹) * s = s * (g * θ (x : co3M) * g⁻¹) := by
  have h := conj_comm_conj (g := g) (theta_comm_ma θ x)
  rwa [h2] at h

theorem swap_mem
    (h1 : g * s * g⁻¹ = θ ma) {x : edgeGroup} {y : co3M}
    (hy : (θ y : G) = g * θ (x : co3M) * g⁻¹) : y ∈ edgeGroup := by
  refine mem_edgeGroup_of_theta θ ?_
  rw [hy, ← h1]
  exact conj_comm_conj (theta_comm_s θ _)

@[expose] noncomputable def swapFun
    (h1 : g * s * g⁻¹ = θ ma) (h2 : g * θ ma * g⁻¹ = s)
    (x : edgeGroup) : edgeGroup :=
  ⟨θ.symm ⟨g * θ (x : co3M) * g⁻¹, mem_centralizer_singleton_iff.2 (swap_comm_s θ h2 x)⟩,
    swap_mem θ h1 (x := x) (by simp)⟩

theorem theta_swapFun
    (h1 : g * s * g⁻¹ = θ ma) (h2 : g * θ ma * g⁻¹ = s) (x : edgeGroup) :
    (θ (swapFun θ h1 h2 x : co3M) : G) = g * θ (x : co3M) * g⁻¹ := by
  simp [swapFun]

@[expose] noncomputable def swapAut
    (h1 : g * s * g⁻¹ = θ ma) (h2 : g * θ ma * g⁻¹ = s) :
    MulAut edgeGroup where
  toFun := swapFun θ h1 h2
  invFun := swapFun θ (inv_conj_of_conj h2) (inv_conj_of_conj h1)
  left_inv x := theta_edge_inj θ (by rw [theta_swapFun, theta_swapFun]; group)
  right_inv x := theta_edge_inj θ (by rw [theta_swapFun, theta_swapFun]; group)
  map_mul' x y := theta_edge_inj θ (by
    rw [theta_edge_mul, theta_swapFun, theta_swapFun, theta_swapFun, theta_edge_mul]
    group)

theorem theta_swapAut
    (h1 : g * s * g⁻¹ = θ ma) (h2 : g * θ ma * g⁻¹ = s) (x : edgeGroup) :
    (θ (swapAut θ h1 h2 x : co3M) : G) = g * θ (x : co3M) * g⁻¹ :=
  theta_swapFun θ h1 h2 x

theorem swapAut_eH
    (hθ : (θ co3ZM : G) = s) (h1 : g * s * g⁻¹ = θ ma)
    (h2 : g * θ ma * g⁻¹ = s) : swapAut θ h1 h2 eH = aH :=
  theta_edge_inj θ (by rw [theta_swapAut, theta_eH θ hθ, h1]; rfl)

theorem swapAut_aH
    (hθ : (θ co3ZM : G) = s) (h1 : g * s * g⁻¹ = θ ma)
    (h2 : g * θ ma * g⁻¹ = s) : swapAut θ h1 h2 aH = eH :=
  theta_edge_inj θ (by rw [theta_eH θ hθ, theta_swapAut]; exact h2)

end Swap

theorem exists_cube
    {u : G} (hs : u * s * u⁻¹ = θ yM) (hy : u * θ yM * u⁻¹ = θ ma)
    (ha : u * θ ma * u⁻¹ = s) :
    ∃ k : edgeGroup, k * yH = yH * k ∧ (θ (k : co3M) : G) = u ^ 3 := by
  obtain ⟨w, hw⟩ := exists_theta_eq θ (cube_comm hs hy ha)
  have hwH : w ∈ edgeGroup := mem_edgeGroup_of_theta θ (by rw [hw]; exact cube_comm ha hs hy)
  refine ⟨⟨w, hwH⟩, Subtype.ext ?_, hw⟩
  show w * yM = yM * w
  exact (theta_comm_iff θ w yM).1 (by rw [hw]; exact cube_comm hy ha hs)

theorem chain_of_conj
    {u : G} {μ : edgeGroup → co3M}
    (hμ : ∀ x, (θ (μ x) : G) = u * θ (x : co3M) * u⁻¹) {k : edgeGroup}
    (hk : (θ (k : co3M) : G) = u ^ 3) (x₀ x₁ x₂ : edgeGroup) (h1 : (x₁ : co3M) = μ x₀)
    (h2 : (x₂ : co3M) = μ x₁) : μ x₂ = ((k * x₀ * k⁻¹ : edgeGroup) : co3M) := by
  apply theta_inj θ
  rw [hμ, h2, hμ, h1, hμ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, theta_conj, hk,
    pow_three]
  group

theorem planeTest_swapAut
    (hθ : (θ co3ZM : G) = s) {g : G} (h1 : g * s * g⁻¹ = θ ma)
    (h2 : g * θ ma * g⁻¹ = s) : PlaneTest (swapAut θ h1 h2) := by
  intro h hh
  set σ := swapAut θ h1 h2 with hσ
  set u : G := (θ bcbM : G) * g * θ (h : co3M) with hu
  have hμ : ∀ x : edgeGroup,
      (θ (bcbM * σ (h * x * h⁻¹) * bcbM⁻¹) : G) = u * θ (x : co3M) * u⁻¹ := by
    intro x
    rw [theta_conj, hσ, theta_swapAut, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      theta_conj, hu]
    group
  have hs : u * s * u⁻¹ = θ yM := by
    have e1 : u * s * u⁻¹ = θ bcbM * (g * ((θ (h : co3M) : G) * s * (θ (h : co3M) : G)⁻¹) *
        g⁻¹) * (θ bcbM : G)⁻¹ := by
      rw [hu]
      group
    rw [e1, theta_comm_s θ, mul_inv_cancel_right, h1, ← theta_conj, bcb_facts.2.1]
  have hy : u * θ yM * u⁻¹ = θ ma := by
    rw [← coe_yH, ← hμ, hh, coe_yH, bcb_facts.2.2.1]
  have ha : u * θ ma * u⁻¹ = s := by
    have e1 := hμ aH
    rw [conj_apply_central aH_mem_center, hσ, swapAut_aH θ hθ] at e1
    rw [show (θ ma : G) = θ (aH : co3M) from rfl, ← e1,
      show ((eH : edgeGroup) : co3M) = me from rfl, me_comm bcbM, mul_inv_cancel_right,
      theta_me θ hθ]
  obtain ⟨k, hk, hku⟩ := exists_cube θ hs hy ha
  exact ⟨k, hk, fun x₀ x₁ x₂ _ e1 e2 => chain_of_conj θ hμ hku x₀ x₁ x₂ e1 e2⟩

theorem exists_edge_involution
    (hθ : (θ co3ZM : G) = s) {g : G} (h1 : g * s * g⁻¹ = θ ma)
    (h2 : g * θ ma * g⁻¹ = s) :
    ∃ sG : G, sG * sG = 1 ∧ ∀ x : edgeGroup, sG * θ (x : co3M) * sG⁻¹ = θ (psi x : co3M) := by
  obtain ⟨v, hv⟩ := edgeRigidity (swapAut θ h1 h2) (swapAut_eH θ hθ h1 h2)
    (swapAut_aH θ hθ h1 h2) (planeTest_swapAut θ hθ h1 h2)
  set s₂ : G := (θ (v : co3M) : G)⁻¹ * g with hs₂
  have hψ : ∀ x : edgeGroup, s₂ * θ (x : co3M) * s₂⁻¹ = θ (psi x : co3M) := by
    intro x
    have e := theta_swapAut θ h1 h2 x
    rw [hv x, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, theta_mul, theta_mul,
      theta_inv] at e
    calc s₂ * θ (x : co3M) * s₂⁻¹ = (θ (v : co3M) : G)⁻¹ * (g * θ (x : co3M) * g⁻¹) *
          θ (v : co3M) := by rw [hs₂]; group
      _ = θ (psi x : co3M) := by rw [← e]; group
  have hsq : ∀ x : edgeGroup, (s₂ * s₂) * θ (x : co3M) * (s₂ * s₂)⁻¹ = θ (x : co3M) := by
    intro x
    calc (s₂ * s₂) * θ (x : co3M) * (s₂ * s₂)⁻¹ = s₂ * (s₂ * θ (x : co3M) * s₂⁻¹) * s₂⁻¹ := by
          group
      _ = θ (x : co3M) := by rw [hψ, hψ, modelFacts.psi_facts.2.2.2.2.1 x]
  have hse := comm_of_conj_eq (hsq eH)
  rw [theta_eH θ hθ] at hse
  obtain ⟨w, hw⟩ := exists_theta_eq θ hse
  have hwH : w ∈ edgeGroup := mem_edgeGroup_of_theta θ (by
    rw [hw]
    exact comm_of_conj_eq (hsq aH))
  set w' : edgeGroup := ⟨w, hwH⟩ with hw'
  have hw'θ : (θ (w' : co3M) : G) = s₂ * s₂ := hw
  have hcen : w' ∈ center edgeGroup := by
    rw [mem_center_iff]
    intro x
    apply theta_edge_inj θ
    rw [theta_edge_mul, theta_edge_mul, hw'θ]
    exact (comm_of_conj_eq (hsq x)).symm
  have hfix : psi w' = w' := by
    apply theta_edge_inj θ
    rw [← hψ, hw'θ]
    group
  have hss := s_mul_self θ hθ
  rcases (cubeData.2 w' hcen).1 hfix with h | h
  · refine ⟨s₂, ?_, hψ⟩
    rw [← hw'θ, h]
    exact theta_one θ
  · refine ⟨s * s₂, ?_, fun x => ?_⟩
    · have e1 : s₂ * s * s₂⁻¹ = θ ma := by
        have e := hψ eH
        rw [theta_eH θ hθ, psi_eH] at e
        exact e
      have e2 : s₂ * s₂ = θ (me * ma) := by
        rw [← hw'θ, h]
        rfl
      calc s * s₂ * (s * s₂) = s * (s₂ * s * s₂⁻¹) * (s₂ * s₂) := by group
        _ = s * θ ma * (s * θ ma) := by rw [e1, e2, theta_mul, theta_me θ hθ]
        _ = 1 := mul_mul_self_of_comm (theta_ma_comm θ).symm hss (theta_ma_mul_self θ)
    · calc s * s₂ * θ (x : co3M) * (s * s₂)⁻¹ = s * (s₂ * θ (x : co3M) * s₂⁻¹) * s⁻¹ := by
            group
        _ = θ (psi x : co3M) := by rw [hψ, ← theta_comm_s θ, mul_inv_cancel_right]

end Theta

end CFSG.EvenSmallLie.SympSix.Co3Ident
