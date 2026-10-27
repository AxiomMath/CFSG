module

public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverRoots
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFieldFourKernel

open Subgroup Matrix LinearFlag LinearFieldFour LinearCover CFSG.ComponentClassification
open scoped commutatorElement

variable {k E : Type*} [Field k] [Group E]

section Lifts

variable (η : E →* projectiveSL 3 k) (hη : Function.Surjective η)

@[expose] def lift (g : projectiveSL 3 k) : E := (hη g).choose

theorem map_lift (g : projectiveSL 3 k) : η (lift η hη g) = g :=
  (hη g).choose_spec

@[expose] def rootComm (a b : k) : E := ⁅lift η hη (xP a), lift η hη (yP b)⁆

@[expose] def wxComm (c a : k) : E := ⁅lift η hη (wP c), lift η hη (xP a)⁆

@[expose] def wyComm (c b : k) : E := ⁅lift η hη (wP c), lift η hη (yP b)⁆

@[expose] def normComm (ω a b : k) : E :=
  rootComm η hη a b * rootComm η hη (ω * a) (ω * b) * rootComm η hη (ω * (ω * a)) (ω * (ω * b))

end Lifts

section Cover

variable (η : E →* projectiveSL 3 k) (hη : Function.Surjective η)
  (hker : ∀ z, η z = 1 → z ∈ center E)

include hker in
theorem comm_eq {x x' y y' : E} (hx : η x = η x') (hy : η y = η y') : ⁅x, y⁆ = ⁅x', y'⁆ :=
  HeisenbergRoots.commutatorElement_eq_of_map_eq η hker hx hy

include hker in
theorem commutatorElement_eq_one_of_map_eq_one_right {x y : E} (hy : η y = 1) : ⁅x, y⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp (hker y hy) x)

include hker in
theorem commutatorElement_eq_one_of_map_eq_one_left {x y : E} (hx : η x = 1) : ⁅x, y⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp (hker x hx) y).symm

theorem map_rootComm (a b : k) : η (rootComm η hη a b) = wP (a * b) := by
  rw [rootComm, map_commutatorElement, map_lift, map_lift, commutatorElement_xP_yP]

theorem map_wxComm (c a : k) : η (wxComm η hη c a) = 1 := by
  rw [wxComm, map_commutatorElement, map_lift, map_lift, commutatorElement_eq_one_iff_mul_comm]
  exact wP_mul_xP c a

theorem map_wyComm (c b : k) : η (wyComm η hη c b) = 1 := by
  rw [wyComm, map_commutatorElement, map_lift, map_lift, commutatorElement_eq_one_iff_mul_comm]
  exact wP_mul_yP c b

include hker in
theorem wxComm_mem_center (c a : k) : wxComm η hη c a ∈ center E :=
  hker _ (map_wxComm η hη c a)

include hker in
theorem wyComm_mem_center (c b : k) : wyComm η hη c b ∈ center E :=
  hker _ (map_wyComm η hη c b)

include hker in
theorem rootComm_mul_comm [CharP k 2] (a b a' b' : k) :
    rootComm η hη a b * rootComm η hη a' b' = rootComm η hη a' b' * rootComm η hη a b :=
  (projRoots (K := k)).preimage_w_comm η hker hη _ _ ⟨_, map_rootComm η hη a b⟩
    ⟨_, map_rootComm η hη a' b'⟩

include hker in
theorem wxComm_add_left (c c' a : k) :
    wxComm η hη (c + c') a = wxComm η hη c a * wxComm η hη c' a := by
  have h : wxComm η hη (c + c') a = ⁅lift η hη (wP c) * lift η hη (wP c'), lift η hη (xP a)⁆ :=
    comm_eq η hker (by rw [map_lift, map_mul, map_lift, map_lift, wP_add]) rfl
  rw [h, commutatorElement_mul_left_of_mem_center (wxComm_mem_center η hη hker c' a)]
  rfl

include hker in
theorem wyComm_add_left (c c' b : k) :
    wyComm η hη (c + c') b = wyComm η hη c b * wyComm η hη c' b := by
  have h : wyComm η hη (c + c') b = ⁅lift η hη (wP c) * lift η hη (wP c'), lift η hη (yP b)⁆ :=
    comm_eq η hker (by rw [map_lift, map_mul, map_lift, map_lift, wP_add]) rfl
  rw [h, commutatorElement_mul_left_of_mem_center (wyComm_mem_center η hη hker c' b)]
  rfl

include hker in
theorem wxComm_zero_left (a : k) : wxComm η hη 0 a = 1 :=
  commutatorElement_eq_one_of_map_eq_one_left η hker (by rw [map_lift, (wP_eq_one_iff 0).mpr rfl])

include hker in
theorem wxComm_zero_right (c : k) : wxComm η hη c 0 = 1 :=
  commutatorElement_eq_one_of_map_eq_one_right η hker
    (by rw [map_lift, (xP_eq_one_iff 0).mpr rfl])

include hker in
theorem wyComm_zero_left (b : k) : wyComm η hη 0 b = 1 :=
  commutatorElement_eq_one_of_map_eq_one_left η hker (by rw [map_lift, (wP_eq_one_iff 0).mpr rfl])

include hker in
theorem wyComm_zero_right (c : k) : wyComm η hη c 0 = 1 :=
  commutatorElement_eq_one_of_map_eq_one_right η hker
    (by rw [map_lift, (yP_eq_one_iff 0).mpr rfl])

include hker in
theorem rootComm_zero_left (b : k) : rootComm η hη 0 b = 1 :=
  commutatorElement_eq_one_of_map_eq_one_left η hker (by rw [map_lift, (xP_eq_one_iff 0).mpr rfl])

include hker in
theorem rootComm_zero_right (a : k) : rootComm η hη a 0 = 1 :=
  commutatorElement_eq_one_of_map_eq_one_right η hker
    (by rw [map_lift, (yP_eq_one_iff 0).mpr rfl])

include hker in
theorem wxComm_mul_self [CharP k 2] (z : k) : wxComm η hη z 1 * wxComm η hη z 1 = 1 := by
  rw [← wxComm_add_left η hη hker, CharTwo.add_self_eq_zero, wxComm_zero_left η hη hker]

include hker in
theorem lift_xP_sq_mem_center [CharP k 2] (a : k) :
    lift η hη (xP a) * lift η hη (xP a) ∈ center E :=
  hker _ (by rw [map_mul, map_lift, ← xP_add, CharTwo.add_self_eq_zero, (xP_eq_one_iff 0).mpr rfl])

include hker in
theorem lift_yP_sq_mem_center [CharP k 2] (b : k) :
    lift η hη (yP b) * lift η hη (yP b) ∈ center E :=
  hker _ (by rw [map_mul, map_lift, ← yP_add, CharTwo.add_self_eq_zero, (yP_eq_one_iff 0).mpr rfl])

include hker in
theorem rootComm_sq [CharP k 2] (a b : k) : rootComm η hη a b ^ 2 = wxComm η hη (a * b) a := by
  have h := (commutatorElement_commutatorElement_eq_sq
    (mem_center_iff.mp (lift_xP_sq_mem_center η hη hker a) (lift η hη (yP b))).symm
    (mem_center_iff.mp (lift_yP_sq_mem_center η hη hker b) (lift η hη (xP a))).symm).1
  rw [← rootComm] at h
  rw [← h]
  exact comm_eq η hker (by rw [map_rootComm, map_lift]) rfl

include hker in
theorem wxComm_eq_wyComm [CharP k 2] (a b : k) : wxComm η hη (a * b) a = wyComm η hη (a * b) b := by
  have h := commutatorElement_commutatorElement_eq_sq
    (mem_center_iff.mp (lift_xP_sq_mem_center η hη hker a) (lift η hη (yP b))).symm
    (mem_center_iff.mp (lift_yP_sq_mem_center η hη hker b) (lift η hη (xP a))).symm
  rw [← rootComm] at h
  have e1 : ⁅rootComm η hη a b, lift η hη (xP a)⁆ = wxComm η hη (a * b) a :=
    comm_eq η hker (by rw [map_rootComm, map_lift]) rfl
  have e2 : ⁅rootComm η hη a b, lift η hη (yP b)⁆ = wyComm η hη (a * b) b :=
    comm_eq η hker (by rw [map_rootComm, map_lift]) rfl
  rw [← e1, ← e2, h.1, h.2]

variable {ω : k} (hω3 : ω * ω * ω = 1) (u : E) (hu : η u = hP ω hω3)

include hu in
theorem map_conj_lift_xP (a : k) : η (u * lift η hη (xP a) * u⁻¹) = xP (ω * a) := by
  rw [map_mul, map_mul, map_inv, map_lift, hu, hP_conj_xP]

include hu in
theorem map_conj_lift_yP (b : k) : η (u * lift η hη (yP b) * u⁻¹) = yP (ω * b) := by
  rw [map_mul, map_mul, map_inv, map_lift, hu, hP_conj_yP]

include hu in
theorem map_conj_lift_wP (c : k) : η (u * lift η hη (wP c) * u⁻¹) = wP (ω * ω * c) := by
  rw [map_mul, map_mul, map_inv, map_lift, hu, hP_conj_wP]

theorem conj_commutatorElement (x y : E) : u * ⁅x, y⁆ * u⁻¹ = ⁅u * x * u⁻¹, u * y * u⁻¹⁆ := by
  simp only [commutatorElement_def]
  group

theorem conj_of_mem_center {z : E} (hz : z ∈ center E) : u * z * u⁻¹ = z := by
  rw [mem_center_iff.mp hz u, mul_inv_cancel_right]

include hker hu in
theorem rootComm_conj (a b : k) :
    u * rootComm η hη a b * u⁻¹ = rootComm η hη (ω * a) (ω * b) := by
  rw [rootComm, conj_commutatorElement]
  exact comm_eq η hker (by rw [map_conj_lift_xP η hη hω3 u hu, map_lift])
    (by rw [map_conj_lift_yP η hη hω3 u hu, map_lift])

include hker hu in
theorem wxComm_conj (c a : k) : wxComm η hη (ω * ω * c) (ω * a) = wxComm η hη c a := by
  have h := conj_commutatorElement u (lift η hη (wP c)) (lift η hη (xP a))
  change u * wxComm η hη c a * u⁻¹ = _ at h
  rw [conj_of_mem_center u (wxComm_mem_center η hη hker c a)] at h
  rw [h]
  exact comm_eq η hker (by rw [map_lift, map_conj_lift_wP η hη hω3 u hu])
    (by rw [map_lift, map_conj_lift_xP η hη hω3 u hu])

include hker hu in
theorem wyComm_conj (c b : k) : wyComm η hη (ω * ω * c) (ω * b) = wyComm η hη c b := by
  have h := conj_commutatorElement u (lift η hη (wP c)) (lift η hη (yP b))
  change u * wyComm η hη c b * u⁻¹ = _ at h
  rw [conj_of_mem_center u (wyComm_mem_center η hη hker c b)] at h
  rw [h]
  exact comm_eq η hker (by rw [map_lift, map_conj_lift_wP η hη hω3 u hu])
    (by rw [map_lift, map_conj_lift_yP η hη hω3 u hu])

include hker hu in
theorem wxComm_shift (c a : k) : wxComm η hη c (ω * a) = wxComm η hη (ω * c) a := by
  have h := wxComm_conj η hη hker hω3 u hu (ω * c) a
  rwa [show ω * ω * (ω * c) = c by linear_combination c * hω3] at h

include hker hu in
theorem wyComm_shift (c b : k) : wyComm η hη c (ω * b) = wyComm η hη (ω * c) b := by
  have h := wyComm_conj η hη hker hω3 u hu (ω * c) b
  rwa [show ω * ω * (ω * c) = c by linear_combination c * hω3] at h

theorem mul_shuffle {G : Type*} [Group G] {a b c a' b' c' : G} (h1 : a' * b = b * a')
    (h2 : a' * c = c * a') (h3 : b' * c = c * b') :
    a * a' * (b * b') * (c * c') = a * b * c * (a' * b' * c') := by
  calc a * a' * (b * b') * (c * c') = a * (a' * b) * b' * (c * c') := by group
    _ = a * (b * a') * b' * (c * c') := by rw [h1]
    _ = a * b * a' * (b' * c) * c' := by group
    _ = a * b * a' * (c * b') * c' := by rw [h3]
    _ = a * b * (a' * c) * b' * c' := by group
    _ = a * b * (c * a') * b' * c' := by rw [h2]
    _ = a * b * c * (a' * b' * c') := by group

theorem mul_central_three {G : Type*} [Group G] {x₁ x₂ x₃ W₁ W₂ W₃ : G}
    (h₁ : W₁ ∈ center G) (h₂ : W₂ ∈ center G) :
    x₁ * W₁ * (x₂ * W₂) * (x₃ * W₃) = x₁ * x₂ * x₃ * (W₁ * W₂ * W₃) := by
  calc x₁ * W₁ * (x₂ * W₂) * (x₃ * W₃) = x₁ * (W₁ * x₂) * W₂ * (x₃ * W₃) := by group
    _ = x₁ * (x₂ * W₁) * W₂ * (x₃ * W₃) := by rw [← mem_center_iff.mp h₁ x₂]
    _ = x₁ * x₂ * ((W₁ * W₂) * x₃) * W₃ := by group
    _ = x₁ * x₂ * (x₃ * (W₁ * W₂)) * W₃ := by rw [← mem_center_iff.mp (mul_mem h₁ h₂) x₃]
    _ = x₁ * x₂ * x₃ * (W₁ * W₂ * W₃) := by group

theorem inv_mul_inv_mul_inv {G : Type*} [Group G] {a b c : G} (h1 : Commute a b)
    (h2 : Commute a c) (h3 : Commute b c) : a⁻¹ * b⁻¹ * c⁻¹ = (a * b * c)⁻¹ := by
  rw [show (a * b * c)⁻¹ = c⁻¹ * b⁻¹ * a⁻¹ by group]
  have e1 : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := h1.inv_inv
  have e2 : a⁻¹ * c⁻¹ = c⁻¹ * a⁻¹ := h2.inv_inv
  have e3 : b⁻¹ * c⁻¹ = c⁻¹ * b⁻¹ := h3.inv_inv
  calc a⁻¹ * b⁻¹ * c⁻¹ = b⁻¹ * (a⁻¹ * c⁻¹) := by rw [e1, mul_assoc]
    _ = b⁻¹ * (c⁻¹ * a⁻¹) := by rw [e2]
    _ = b⁻¹ * c⁻¹ * a⁻¹ := by rw [mul_assoc]
    _ = c⁻¹ * b⁻¹ * a⁻¹ := by rw [e3]

theorem conj_eq_commutatorElement_mul {G : Type*} [Group G] (g z : G) :
    g * z * g⁻¹ = ⁅g, z⁆ * z := by
  rw [commutatorElement_def]
  group

theorem mul_self_mul_mul_self (hk : Nat.card k = 4) (z : k) : z * z * (z * z) = z := by
  linear_combination pow_four_eq_self hk z

variable (hk : Nat.card k = 4) (hω0 : ω ≠ 0) (hω1 : ω ≠ 1)

include hker hu hk hω0 hω1 in
theorem wxComm_eq_one (c a : k) : wxComm η hη c a = wxComm η hη (c * a) 1 := by
  have hω2 : ω * ω = ω + 1 := omega_mul_omega hk hω0 hω1
  rcases eq_zero_or_eq_one_or hk hω0 hω1 a with rfl | rfl | rfl | rfl
  · rw [wxComm_zero_right η hη hker, mul_zero, wxComm_zero_left η hη hker]
  · rw [mul_one]
  · have e := wxComm_shift η hη hker hω3 u hu c 1
    rw [mul_one] at e
    rw [e, mul_comm]
  · have e1 := wxComm_shift η hη hker hω3 u hu c ω
    have e2 := wxComm_shift η hη hker hω3 u hu (ω * c) 1
    rw [mul_one] at e2
    rw [← hω2, e1, e2, show c * (ω * ω) = ω * (ω * c) by ring]

include hker hu hk hω0 hω1 in
theorem wyComm_eq_one (c b : k) : wyComm η hη c b = wyComm η hη (c * b) 1 := by
  have hω2 : ω * ω = ω + 1 := omega_mul_omega hk hω0 hω1
  rcases eq_zero_or_eq_one_or hk hω0 hω1 b with rfl | rfl | rfl | rfl
  · rw [wyComm_zero_right η hη hker, mul_zero, wyComm_zero_left η hη hker]
  · rw [mul_one]
  · have e := wyComm_shift η hη hker hω3 u hu c 1
    rw [mul_one] at e
    rw [e, mul_comm]
  · have e1 := wyComm_shift η hη hker hω3 u hu c ω
    have e2 := wyComm_shift η hη hker hω3 u hu (ω * c) 1
    rw [mul_one] at e2
    rw [← hω2, e1, e2, show c * (ω * ω) = ω * (ω * c) by ring]

include hker hu hk hω0 hω1 in
theorem wyComm_eq [CharP k 2] (c b : k) :
    wyComm η hη c b = wxComm η hη (c * b * (c * b)) 1 := by
  have hLM : ∀ z : k, wxComm η hη z 1 = wyComm η hη (z * z) 1 := fun z => by
    have h := wxComm_eq_wyComm η hη hker 1 z
    rw [one_mul] at h
    rw [h, wyComm_eq_one η hη hker hω3 u hu hk hω0 hω1 z z]
  rw [wyComm_eq_one η hη hker hω3 u hu hk hω0 hω1 c b, hLM (c * b * (c * b)),
    mul_self_mul_mul_self hk]

include hker in
theorem rootComm_add_left [CharP k 2] (a a' b : k) :
    rootComm η hη (a + a') b =
      rootComm η hη a b * rootComm η hη a' b * (wxComm η hη (a' * b) a)⁻¹ := by
  have h1 : rootComm η hη (a + a') b =
      ⁅lift η hη (xP a) * lift η hη (xP a'), lift η hη (yP b)⁆ :=
    comm_eq η hker (by rw [map_lift, map_mul, map_lift, map_lift, xP_add]) rfl
  have h3 : ⁅lift η hη (xP a), rootComm η hη a' b⁆ = (wxComm η hη (a' * b) a)⁻¹ := by
    rw [wxComm, commutatorElement_inv]
    exact comm_eq η hker rfl (by rw [map_rootComm, map_lift])
  have hc := inv_mem (wxComm_mem_center η hη hker (a' * b) a)
  rw [h1, commutatorElement_mul_left_eq]
  change lift η hη (xP a) * rootComm η hη a' b * (lift η hη (xP a))⁻¹ * rootComm η hη a b = _
  rw [conj_eq_commutatorElement_mul, h3]
  calc (wxComm η hη (a' * b) a)⁻¹ * rootComm η hη a' b * rootComm η hη a b
      = (wxComm η hη (a' * b) a)⁻¹ * (rootComm η hη a' b * rootComm η hη a b) := mul_assoc _ _ _
    _ = rootComm η hη a' b * rootComm η hη a b * (wxComm η hη (a' * b) a)⁻¹ :=
        (mem_center_iff.mp hc _).symm
    _ = _ := by rw [rootComm_mul_comm η hη hker a' b a b]

include hker in
theorem rootComm_add_right (a b b' : k) :
    rootComm η hη a (b + b') =
      rootComm η hη a b * rootComm η hη a b' * (wyComm η hη (a * b') b)⁻¹ := by
  have h1 : rootComm η hη a (b + b') =
      ⁅lift η hη (xP a), lift η hη (yP b) * lift η hη (yP b')⁆ :=
    comm_eq η hker rfl (by rw [map_lift, map_mul, map_lift, map_lift, yP_add])
  have h3 : ⁅lift η hη (yP b), rootComm η hη a b'⁆ = (wyComm η hη (a * b') b)⁻¹ := by
    rw [wyComm, commutatorElement_inv]
    exact comm_eq η hker rfl (by rw [map_rootComm, map_lift])
  have hc := inv_mem (wyComm_mem_center η hη hker (a * b') b)
  rw [h1, commutatorElement_mul_right_eq]
  change rootComm η hη a b * (lift η hη (yP b) * rootComm η hη a b' * (lift η hη (yP b))⁻¹) = _
  rw [conj_eq_commutatorElement_mul, h3, ← mem_center_iff.mp hc (rootComm η hη a b'),
    mul_assoc]

include hω3 in
theorem map_normComm (hω4 : 1 + ω + ω * ω = 0) (a b : k) : η (normComm η hη ω a b) = 1 := by
  rw [normComm, map_mul, map_mul, map_rootComm, map_rootComm, map_rootComm, ← wP_add, ← wP_add,
    wP_eq_one_iff]
  linear_combination (a * b) * hω4 + (a * b * ω) * hω3

include hker hω3 in
theorem normComm_smul [CharP k 2] (a b : k) :
    normComm η hη ω (ω * a) (ω * b) = normComm η hη ω a b := by
  have ha : ω * (ω * (ω * a)) = a := by linear_combination a * hω3
  have hb : ω * (ω * (ω * b)) = b := by linear_combination b * hω3
  simp only [normComm]
  rw [ha, hb, mul_assoc, rootComm_mul_comm η hη hker (ω * (ω * a)), ← mul_assoc,
    rootComm_mul_comm η hη hker (ω * a) (ω * b) a b]

include hker hu hk hω0 hω1 in
theorem normComm_sq [CharP k 2] (a b : k) :
    normComm η hη ω a b ^ 2 = wxComm η hη (a * b * a) 1 := by
  have hcomm := rootComm_mul_comm η hη hker
  have h12 : Commute (rootComm η hη a b) (rootComm η hη (ω * a) (ω * b)) := hcomm _ _ _ _
  have h13 : Commute (rootComm η hη a b) (rootComm η hη (ω * (ω * a)) (ω * (ω * b))) :=
    hcomm _ _ _ _
  have h23 : Commute (rootComm η hη (ω * a) (ω * b))
      (rootComm η hη (ω * (ω * a)) (ω * (ω * b))) := hcomm _ _ _ _
  rw [normComm, (h13.mul_left h23).mul_pow, h12.mul_pow, rootComm_sq η hη hker,
    rootComm_sq η hη hker, rootComm_sq η hη hker,
    wxComm_eq_one η hη hker hω3 u hu hk hω0 hω1 (a * b),
    wxComm_eq_one η hη hker hω3 u hu hk hω0 hω1 (ω * a * (ω * b)),
    wxComm_eq_one η hη hker hω3 u hu hk hω0 hω1 (ω * (ω * a) * (ω * (ω * b))),
    show ω * a * (ω * b) * (ω * a) = a * b * a by linear_combination (a * b * a) * hω3,
    show ω * (ω * a) * (ω * (ω * b)) * (ω * (ω * a)) = a * b * a by
      linear_combination (a * b * a) * (ω * ω * ω + 1) * hω3,
    wxComm_mul_self η hη hker, one_mul]

include hker in
theorem normComm_add_left [CharP k 2] (a a' b : k) :
    normComm η hη ω (a + a') b = normComm η hη ω a b * normComm η hη ω a' b *
      ((wxComm η hη (a' * b) a)⁻¹ * (wxComm η hη (ω * a' * (ω * b)) (ω * a))⁻¹ *
        (wxComm η hη (ω * (ω * a') * (ω * (ω * b))) (ω * (ω * a)))⁻¹) := by
  have hcomm := rootComm_mul_comm η hη hker
  have hc : ∀ c a'' : k, (wxComm η hη c a'')⁻¹ ∈ center E := fun c a'' =>
    inv_mem (wxComm_mem_center η hη hker c a'')
  simp only [normComm, mul_add]
  rw [rootComm_add_left η hη hker a, rootComm_add_left η hη hker (ω * a),
    rootComm_add_left η hη hker (ω * (ω * a)), mul_central_three (hc _ _) (hc _ _),
    mul_shuffle (hcomm _ _ _ _) (hcomm _ _ _ _) (hcomm _ _ _ _)]

include hker in
theorem normComm_add_right [CharP k 2] (a b b' : k) :
    normComm η hη ω a (b + b') = normComm η hη ω a b * normComm η hη ω a b' *
      ((wyComm η hη (a * b') b)⁻¹ * (wyComm η hη (ω * a * (ω * b')) (ω * b))⁻¹ *
        (wyComm η hη (ω * (ω * a) * (ω * (ω * b'))) (ω * (ω * b)))⁻¹) := by
  have hcomm := rootComm_mul_comm η hη hker
  have hc : ∀ c b'' : k, (wyComm η hη c b'')⁻¹ ∈ center E := fun c b'' =>
    inv_mem (wyComm_mem_center η hη hker c b'')
  simp only [normComm, mul_add]
  rw [rootComm_add_right η hη hker a, rootComm_add_right η hη hker (ω * a),
    rootComm_add_right η hη hker (ω * (ω * a)), mul_central_three (hc _ _) (hc _ _),
    mul_shuffle (hcomm _ _ _ _) (hcomm _ _ _ _) (hcomm _ _ _ _)]


include hker hu hk hω0 hω1 in
theorem wxComm_one_mem_closure [CharP k 2] (z : k) :
    wxComm η hη z 1 ∈ closure {normComm η hη ω 1 1, normComm η hη ω ω 1} := by
  set G₂ := closure {normComm η hη ω 1 1, normComm η hη ω ω 1}
  have hω2 : ω * ω = ω + 1 := omega_mul_omega hk hω0 hω1
  have hk1 : normComm η hη ω 1 1 ∈ G₂ := subset_closure (Set.mem_insert _ _)
  have hkω : normComm η hη ω ω 1 ∈ G₂ := subset_closure (Set.mem_insert_of_mem _ rfl)
  have hL1 : wxComm η hη 1 1 ∈ G₂ := by
    have h := normComm_sq η hη hker hω3 u hu hk hω0 hω1 1 1
    rw [show (1 : k) * 1 * 1 = 1 by ring] at h
    rw [← h]
    exact pow_mem hk1 2
  have hLω2 : wxComm η hη (ω + 1) 1 ∈ G₂ := by
    have h := normComm_sq η hη hker hω3 u hu hk hω0 hω1 ω 1
    rw [show ω * 1 * ω = ω + 1 by rw [mul_one, hω2]] at h
    rw [← h]
    exact pow_mem hkω 2
  have hLω : wxComm η hη ω 1 ∈ G₂ := by
    have h := wxComm_add_left η hη hker (ω + 1) 1 1
    rw [show ω + 1 + 1 = ω by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]] at h
    rw [h]
    exact mul_mem hLω2 hL1
  rcases eq_zero_or_eq_one_or hk hω0 hω1 z with rfl | rfl | rfl | rfl
  · rw [wxComm_zero_left η hη hker]
    exact one_mem _
  · exact hL1
  · exact hLω
  · exact hLω2

include hker hu hk hω0 hω1 in
theorem normComm_mem_closure [CharP k 2] (a b : k) :
    normComm η hη ω a b ∈ closure {normComm η hη ω 1 1, normComm η hη ω ω 1} := by
  set G₂ := closure {normComm η hη ω 1 1, normComm η hη ω ω 1}
  have hω2 : ω * ω = ω + 1 := omega_mul_omega hk hω0 hω1
  have hk1 : normComm η hη ω 1 1 ∈ G₂ := subset_closure (Set.mem_insert _ _)
  have hkω : normComm η hη ω ω 1 ∈ G₂ := subset_closure (Set.mem_insert_of_mem _ rfl)
  have hW : ∀ c a'' : k, wxComm η hη c a'' ∈ G₂ := fun c a'' => by
    rw [wxComm_eq_one η hη hker hω3 u hu hk hω0 hω1]
    exact wxComm_one_mem_closure η hη hker hω3 u hu hk hω0 hω1 _
  have hW' : ∀ c b'' : k, wyComm η hη c b'' ∈ G₂ := fun c b'' => by
    rw [wyComm_eq η hη hker hω3 u hu hk hω0 hω1]
    exact wxComm_one_mem_closure η hη hker hω3 u hu hk hω0 hω1 _
  have hleft : ∀ a a' b : k, normComm η hη ω a b ∈ G₂ → normComm η hη ω a' b ∈ G₂ →
      normComm η hη ω (a + a') b ∈ G₂ := fun a a' b h h' => by
    rw [normComm_add_left η hη hker]
    exact mul_mem (mul_mem h h') (mul_mem (mul_mem (inv_mem (hW _ _)) (inv_mem (hW _ _)))
      (inv_mem (hW _ _)))
  have hright : ∀ a b b' : k, normComm η hη ω a b ∈ G₂ → normComm η hη ω a b' ∈ G₂ →
      normComm η hη ω a (b + b') ∈ G₂ := fun a b b' h h' => by
    rw [normComm_add_right η hη hker]
    exact mul_mem (mul_mem h h') (mul_mem (mul_mem (inv_mem (hW' _ _)) (inv_mem (hW' _ _)))
      (inv_mem (hW' _ _)))
  have hzero_right : ∀ a : k, normComm η hη ω a 0 ∈ G₂ := fun a => by
    simp only [normComm, mul_zero, rootComm_zero_right η hη hker, mul_one]
    exact one_mem _
  have hzero_left : ∀ b : k, normComm η hη ω 0 b ∈ G₂ := fun b => by
    simp only [normComm, mul_zero, rootComm_zero_left η hη hker, mul_one]
    exact one_mem _
  have hωω : normComm η hη ω ω ω ∈ G₂ := by
    have h := normComm_smul η hη hker hω3 1 1
    rw [mul_one] at h
    rw [h]
    exact hk1
  have h1ω : normComm η hη ω 1 ω ∈ G₂ := by
    have h := normComm_smul η hη hker hω3 1 ω
    rw [mul_one, hω2] at h
    rw [← h]
    exact hright ω ω 1 hωω hkω
  have hbase : ∀ b : k, normComm η hη ω 1 b ∈ G₂ ∧ normComm η hη ω ω b ∈ G₂ := fun b => by
    rcases eq_zero_or_eq_one_or hk hω0 hω1 b with rfl | rfl | rfl | rfl
    · exact ⟨hzero_right 1, hzero_right ω⟩
    · exact ⟨hk1, hkω⟩
    · exact ⟨h1ω, hωω⟩
    · exact ⟨hright 1 ω 1 h1ω hk1, hright ω ω 1 hωω hkω⟩
  rcases eq_zero_or_eq_one_or hk hω0 hω1 a with rfl | rfl | rfl | rfl
  · exact hzero_left b
  · exact (hbase b).1
  · exact (hbase b).2
  · exact hleft ω 1 b (hbase b).2 (hbase b).1

@[expose] def normConj (u r : E) : E := r * (u * r * u⁻¹) * (u * (u * r * u⁻¹) * u⁻¹)

include hker hu hη in
theorem normConj_mul [CharP k 2] {r₁ r₂ : E} (h₁ : ∃ c, η r₁ = wP c) (h₂ : ∃ c, η r₂ = wP c) :
    normConj u (r₁ * r₂) = normConj u r₁ * normConj u r₂ := by
  have hW : ∀ z, (∃ c, η z = wP c) → ∃ c, η (u * z * u⁻¹) = wP c := fun z ⟨c, hc⟩ =>
    ⟨ω * ω * c, by rw [map_mul, map_mul, map_inv, hc, hu, hP_conj_wP]⟩
  have hcomm := (projRoots (K := k)).preimage_w_comm η hker hη
  have e : ∀ z₁ z₂ : E, u * (z₁ * z₂) * u⁻¹ = (u * z₁ * u⁻¹) * (u * z₂ * u⁻¹) := fun _ _ => by
    group
  simp only [normConj]
  rw [e, e]
  exact mul_shuffle (hcomm _ _ h₂ (hW _ h₁)) (hcomm _ _ h₂ (hW _ (hW _ h₁)))
    (hcomm _ _ (hW _ h₂) (hW _ (hW _ h₁)))

include hker hu hη in
theorem normConj_inv [CharP k 2] {r : E} (h : ∃ c, η r = wP c) :
    normConj u r⁻¹ = (normConj u r)⁻¹ := by
  have hW : ∀ z, (∃ c, η z = wP c) → ∃ c, η (u * z * u⁻¹) = wP c := fun z ⟨c, hc⟩ =>
    ⟨ω * ω * c, by rw [map_mul, map_mul, map_inv, hc, hu, hP_conj_wP]⟩
  have hcomm := (projRoots (K := k)).preimage_w_comm η hker hη
  have e : ∀ z : E, u * z⁻¹ * u⁻¹ = (u * z * u⁻¹)⁻¹ := fun _ => by group
  simp only [normConj]
  rw [e, e]
  exact inv_mul_inv_mul_inv (hcomm _ _ h (hW _ h)) (hcomm _ _ h (hW _ (hW _ h)))
    (hcomm _ _ (hW _ h) (hW _ (hW _ h)))

include hker hu in
theorem normConj_rootComm (a b : k) : normConj u (rootComm η hη a b) = normComm η hη ω a b := by
  simp only [normConj, normComm]
  rw [rootComm_conj η hη hker hω3 u hu, rootComm_conj η hη hker hω3 u hu]

theorem normConj_of_mem_center {z : E} (hz : z ∈ center E) : normConj u z = z * z * z := by
  simp only [normConj]
  rw [conj_of_mem_center u hz, conj_of_mem_center u hz]

theorem pow_three_pow_eq_self {z : E} {n : ℕ} (hz : z ^ 2 ^ n = 1) :
    (z ^ 3) ^ 3 ^ (Nat.totient (2 ^ n) - 1) = z := by
  have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right _ (by norm_num)
  have hφ1 : 1 ≤ Nat.totient (2 ^ n) := Nat.totient_pos.mpr (pow_pos two_pos _)
  rw [← pow_mul, ← pow_succ', Nat.sub_add_cancel hφ1]
  conv_rhs => rw [← pow_one z]
  rw [pow_eq_pow_iff_modEq]
  exact (Nat.ModEq.pow_totient hcop).of_dvd (orderOf_dvd_of_pow_eq_one hz)

include hker hu hk hω0 hω1 in
theorem twoPart_le_closure_normComm [CharP k 2] [Finite E] [Group.IsPerfect E] (z : E)
    (hz : η z = 1) (hn : ∃ n : ℕ, z ^ 2 ^ n = 1) :
    z ∈ closure {normComm η hη ω 1 1, normComm η hη ω ω 1} := by
  have := finite_of_card_eq_four hk
  set G₂ := closure {normComm η hη ω 1 1, normComm η hη ω ω 1}
  let lx : k → E := fun a => lift η hη (xP a)
  let ly : k → E := fun b => lift η hη (yP b)
  let lw : k → E := fun c => lift η hη (wP c)
  set X : Set E := (η.ker : Set E) ∪ Set.range lx ∪ Set.range ly ∪ Set.range lw
  set Λ : Subgroup E := closure (Set.range fun z : k => wxComm η hη z 1)
  set R : Subgroup E := closure (Set.range (fun p : k × k => rootComm η hη p.1 p.2) ∪
    Set.range fun z : k => wxComm η hη z 1)
  have hΛc : Λ ≤ center E := closure_le _ |>.mpr fun _ ⟨z, hz⟩ =>
    hz ▸ wxComm_mem_center η hη hker z 1
  have hΛR : Λ ≤ R := closure_mono Set.subset_union_right
  have hcommW := (projRoots (K := k)).preimage_w_comm η hker hη
  have hN : ∀ g ∈ closure X, ∀ r : E, (∃ c, η r = wP c) → ⁅g, r⁆ ∈ Λ := by
    intro g hg r ⟨c, hc⟩
    induction hg using Subgroup.closure_induction with
    | mem s hs =>
      rcases hs with ((hs | ⟨a, rfl⟩) | ⟨b, rfl⟩) | ⟨c', rfl⟩
      · rw [commutatorElement_eq_one_of_map_eq_one_left η hker hs]
        exact one_mem _
      · rw [← commutatorElement_inv, show ⁅r, lx a⁆ = wxComm η hη c a from
          comm_eq η hker (by rw [hc, map_lift]) rfl, wxComm_eq_one η hη hker hω3 u hu hk hω0 hω1]
        exact inv_mem (subset_closure ⟨_, rfl⟩)
      · rw [← commutatorElement_inv, show ⁅r, ly b⁆ = wyComm η hη c b from
          comm_eq η hker (by rw [hc, map_lift]) rfl, wyComm_eq η hη hker hω3 u hu hk hω0 hω1]
        exact inv_mem (subset_closure ⟨_, rfl⟩)
      · have h1 : ⁅lw c', r⁆ = 1 :=
          commutatorElement_eq_one_iff_mul_comm.mpr (hcommW _ _ ⟨c', map_lift η hη _⟩ ⟨c, hc⟩)
        rw [h1]
        exact one_mem _
    | one => rw [commutatorElement_one_left]; exact one_mem _
    | mul g₁ g₂ _ _ ih₁ ih₂ =>
      rw [commutatorElement_mul_left_eq, conj_of_mem_center g₁ (hΛc ih₂)]
      exact mul_mem ih₂ ih₁
    | inv g _ ih =>
      have h' : ⁅g⁻¹, r⁆ = g⁻¹ * ⁅g, r⁆⁻¹ * g⁻¹⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [h', conj_of_mem_center g⁻¹ (inv_mem (hΛc ih))]
      exact inv_mem ih
  have hRW : ∀ r ∈ R, ∃ c, η r = wP c := by
    intro r hr
    induction hr using Subgroup.closure_induction with
    | mem s hs =>
      rcases hs with ⟨p, rfl⟩ | ⟨z, rfl⟩
      · exact ⟨_, map_rootComm η hη p.1 p.2⟩
      · exact ⟨0, by rw [(wP_eq_one_iff 0).mpr rfl]; exact map_wxComm η hη z 1⟩
    | one => exact ⟨0, by rw [map_one, (wP_eq_one_iff 0).mpr rfl]⟩
    | mul r₁ r₂ _ _ ih₁ ih₂ =>
      obtain ⟨c₁, h₁⟩ := ih₁
      obtain ⟨c₂, h₂⟩ := ih₂
      exact ⟨c₁ + c₂, by rw [map_mul, h₁, h₂, wP_add]⟩
    | inv r _ ih =>
      obtain ⟨c, h⟩ := ih
      exact ⟨-c, by rw [map_inv, h, inv_eq_iff_mul_eq_one, ← wP_add, add_neg_cancel,
        (wP_eq_one_iff 0).mpr rfl]⟩
  have hX : ∀ s ∈ X, ∀ s' ∈ X, ⁅s, s'⁆ ∈ R := by
    have hsub : ∀ s ∈ X, s ∈ closure X := fun s hs => subset_closure hs
    have hWX : ∀ s ∈ X, (s ∈ (η.ker : Set E) ∨ s ∈ Set.range lw) → ∃ c, η s = wP c := by
      rintro s - (hs | ⟨c, rfl⟩)
      · exact ⟨0, by rw [(wP_eq_one_iff 0).mpr rfl]; exact hs⟩
      · exact ⟨c, map_lift η hη _⟩
    intro s hs s' hs'
    by_cases hs'W : s' ∈ (η.ker : Set E) ∨ s' ∈ Set.range lw
    · exact hΛR (hN s (hsub s hs) s' (hWX s' hs' hs'W))
    by_cases hsW : s ∈ (η.ker : Set E) ∨ s ∈ Set.range lw
    · rw [← commutatorElement_inv]
      exact inv_mem (hΛR (hN s' (hsub s' hs') s (hWX s hs hsW)))
    rcases hs with ((hs | ⟨a, rfl⟩) | ⟨b, rfl⟩) | ⟨c, rfl⟩
    · exact absurd (Or.inl hs) hsW
    · rcases hs' with ((hs' | ⟨a', rfl⟩) | ⟨b', rfl⟩) | ⟨c', rfl⟩
      · exact absurd (Or.inl hs') hs'W
      · have h1 : ⁅lx a, lx a'⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
          ((projRoots (K := k)).preimage_x_comm η hker hη _ _ ⟨a, map_lift η hη _⟩
            ⟨a', map_lift η hη _⟩)
        rw [h1]
        exact one_mem _
      · exact subset_closure (Or.inl ⟨(a, b'), rfl⟩)
      · exact absurd (Or.inr ⟨c', rfl⟩) hs'W
    · rcases hs' with ((hs' | ⟨a', rfl⟩) | ⟨b', rfl⟩) | ⟨c', rfl⟩
      · exact absurd (Or.inl hs') hs'W
      · rw [← commutatorElement_inv]
        exact inv_mem (subset_closure (Or.inl ⟨(a', b), rfl⟩))
      · have h1 : ⁅ly b, ly b'⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
          ((projRoots (K := k)).preimage_y_comm η hker hη _ _ ⟨b, map_lift η hη _⟩
            ⟨b', map_lift η hη _⟩)
        rw [h1]
        exact one_mem _
      · exact absurd (Or.inr ⟨c', rfl⟩) hs'W
    · exact absurd (Or.inr ⟨c, rfl⟩) hsW
  have hnorm : ∀ g ∈ closure X, ∀ r ∈ R, g * r * g⁻¹ ∈ R := fun g hg r hr => by
    rw [conj_eq_commutatorElement_mul]
    exact mul_mem (hΛR (hN g hg r (hRW r hr))) hr
  have hTX : (projRoots (K := k)).S.comap η ≤ closure X :=
    (projRoots (K := k)).comap_S_le_closure η lx ly lw (fun _ => map_lift η hη _)
      (fun _ => map_lift η hη _) (fun _ => map_lift η hη _)
  obtain ⟨S, hS⟩ := exists_sylow_projUnitriangular (K := k) 2 (n := 3) (by norm_num)
  obtain ⟨P, hP, hzP⟩ := exists_sylow_map_eq_twoPart_le η hη
    (fun z hz => hker z hz) S
  have hPT : (P : Subgroup E) ≤ (projRoots (K := k)).S.comap η := by
    rw [← map_le_iff_le_comap, hP, hS]
    exact le_rfl
  have hzR : z ∈ R := by
    have h := hzP z hz hn
    exact (commutator_le.mpr fun g₁ hg₁ g₂ hg₂ =>
      commutatorElement_mem_of_mem_closure hnorm hX (hTX (hPT hg₁)) (hTX (hPT hg₂))) h
  have hNR : ∀ r ∈ R, normConj u r ∈ G₂ := by
    intro r hr
    have key : ∀ r ∈ R, (∃ c, η r = wP c) ∧ normConj u r ∈ G₂ := by
      intro r hr
      induction hr using Subgroup.closure_induction with
      | mem s hs =>
        refine ⟨hRW s (subset_closure hs), ?_⟩
        rcases hs with ⟨p, rfl⟩ | ⟨z, rfl⟩
        · rw [normConj_rootComm η hη hker hω3 u hu]
          exact normComm_mem_closure η hη hker hω3 u hu hk hω0 hω1 p.1 p.2
        · rw [normConj_of_mem_center u (wxComm_mem_center η hη hker z 1)]
          have hL := wxComm_one_mem_closure η hη hker hω3 u hu hk hω0 hω1 z
          exact mul_mem (mul_mem hL hL) hL
      | one =>
        refine ⟨⟨0, by rw [map_one, (wP_eq_one_iff 0).mpr rfl]⟩, ?_⟩
        rw [normConj_of_mem_center u (one_mem _), mul_one, mul_one]
        exact one_mem _
      | mul r₁ r₂ _ _ ih₁ ih₂ =>
        obtain ⟨⟨c₁, h₁⟩, hN₁⟩ := ih₁
        obtain ⟨⟨c₂, h₂⟩, hN₂⟩ := ih₂
        refine ⟨⟨c₁ + c₂, by rw [map_mul, h₁, h₂, wP_add]⟩, ?_⟩
        rw [normConj_mul η hη hker hω3 u hu ⟨c₁, h₁⟩ ⟨c₂, h₂⟩]
        exact mul_mem hN₁ hN₂
      | inv r _ ih =>
        obtain ⟨⟨c, h⟩, hN⟩ := ih
        refine ⟨⟨-c, by rw [map_inv, h, inv_eq_iff_mul_eq_one, ← wP_add, add_neg_cancel,
          (wP_eq_one_iff 0).mpr rfl]⟩, ?_⟩
        rw [normConj_inv η hη hker hω3 u hu ⟨c, h⟩]
        exact inv_mem hN
    exact (key r hr).2
  have hz3 : z ^ 3 ∈ G₂ := by
    have h := hNR z hzR
    rwa [normConj_of_mem_center u (hker z hz), ← pow_three'] at h
  obtain ⟨n, hn⟩ := hn
  rw [← pow_three_pow_eq_self hn]
  exact pow_mem hz3 _

end Cover

end LinearFieldFourKernel

end CFSG.LocalAnalysis.ComponentInitial
