module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneJhatIndex

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.Jhat

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)
local notation "𝕊" => {X : Matrix (Fin 3) (Fin 3) (ZMod 2) // X ∈ binarySymMatrices 3}

variable {G : Type} [Group G]

theorem mem_Dh_of_J {Dh E : Subgroup G} {x : G} (hx : x ∈ Dh ⊓ centralizer (E : Set G)) :
    x ∈ Dh :=
  (mem_inf.1 hx).1

theorem comm_of_J {Dh E : Subgroup G} {x e : G} (hx : x ∈ Dh ⊓ centralizer (E : Set G))
    (he : e ∈ E) : e * x = x * e :=
  mem_centralizer_iff.1 (mem_inf.1 hx).2 e he

namespace JBase

variable {τ : Multiplicative 𝕊 →* G} {lev : GL (Fin 3) (ZMod 2) →* G} {z : G} {ν : G → 𝕊}
  {A D C E Dh : Subgroup G}

theorem mem_C_of_J (h : JBase τ lev z ν A D C E Dh) {x : G}
    (hx : x ∈ Dh ⊓ centralizer (E : Set G)) (hw : wvec z ν x = 0) : x ∈ C := by
  rw [← h.J_inf_D]
  exact mem_inf.2 ⟨hx, (h.wvec_eq_zero_iff (mem_Dh_of_J hx)).1 hw⟩

theorem mul_inv_mem_C (h : JBase τ lev z ν A D C E Dh) {x y : G}
    (hx : x ∈ Dh ⊓ centralizer (E : Set G)) (hy : y ∈ Dh ⊓ centralizer (E : Set G))
    (hxy : wvec z ν x = wvec z ν y) : x * y⁻¹ ∈ C := by
  rw [← h.J_inf_D]
  exact mem_inf.2 ⟨mul_mem hx (inv_mem hy), h.mul_inv_mem_D (mem_Dh_of_J hx) (mem_Dh_of_J hy) hxy⟩

theorem wvec_z (h : JBase τ lev z ν A D C E Dh) : wvec z ν z = 0 :=
  (h.wvec_eq_zero_iff h.z_Dh).2 h.z_D

theorem exists_J_wvec (h : JBase τ lev z ν A D C E Dh) (v : Fin 3 → ZMod 2) :
    ∃ x ∈ Dh ⊓ centralizer (E : Set G), wvec z ν x = v := by
  obtain ⟨t, ht, htv⟩ := h.exists_wvec v
  rcases h.good_all ht with h1 | h1
  · exact ⟨t, h1, htv⟩
  · refine ⟨t * z, h1, ?_⟩
    rw [h.wvec_mul ht h.z_Dh, h.wvec_z, add_zero, htv]

theorem comm_mem_C (h : JBase τ lev z ν A D C E Dh) {x y : G}
    (hx : x ∈ Dh ⊓ centralizer (E : Set G)) (hy : y ∈ Dh ⊓ centralizer (E : Set G)) :
    x⁻¹ * y⁻¹ * x * y ∈ C := by
  have hx' := mem_Dh_of_J hx
  have hy' := mem_Dh_of_J hy
  refine h.mem_C_of_J (mul_mem (mul_mem (mul_mem (inv_mem hx) (inv_mem hy)) hx) hy) ?_
  rw [h.wvec_mul (mul_mem (mul_mem (inv_mem hx') (inv_mem hy')) hx') hy',
    h.wvec_mul (mul_mem (inv_mem hx') (inv_mem hy')) hx', h.wvec_mul (inv_mem hx') (inv_mem hy'),
    h.wvec_inv hx', h.wvec_inv hy']
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize wvec z ν x i = a
  generalize wvec z ν y i = b
  revert a b
  decide

theorem sq_mem_C (h : JBase τ lev z ν A D C E Dh) {x : G}
    (hx : x ∈ Dh ⊓ centralizer (E : Set G)) : x * x ∈ C :=
  h.mem_C_of_J (mul_mem hx hx) (by rw [h.wvec_mul (mem_Dh_of_J hx) (mem_Dh_of_J hx), vec_add_self])

theorem dν_lev (h : JBase τ lev z ν A D C E Dh) (g : GL (Fin 3) (ZMod 2)) {k : G} (hk : k ∈ C) :
    symThreeDiag (ν (lev g * k * (lev g)⁻¹) : M₃) = (g : M₃) *ᵥ symThreeDiag (ν k : M₃) := by
  rw [(h.ν_lev g k hk).2, symThreeDiag_coe_congr]

theorem dν_conj (h : JBase τ lev z ν A D C E Dh) {k t : G} (hk : k ∈ C) (ht : t ∈ Dh) :
    symThreeDiag (ν (t⁻¹ * k * t) : M₃) = symThreeDiag (ν k : M₃) := by
  have he := h.C_Dh k hk t ht
  have e : t⁻¹ * k * t = k * (k⁻¹ * t⁻¹ * k * t) := by group
  rw [e, h.dν_mul hk (h.E_C he), h.dν_E he, add_zero]

theorem dν_comm_mul (h : JBase τ lev z ν A D C E Dh) {x y c c' : G}
    (hx : x ∈ Dh ⊓ centralizer (E : Set G)) (hy : y ∈ Dh ⊓ centralizer (E : Set G))
    (hc : c ∈ C) (hc' : c' ∈ C) :
    symThreeDiag (ν ((c * x)⁻¹ * (c' * y)⁻¹ * (c * x) * (c' * y)) : M₃) =
      symThreeDiag (ν (x⁻¹ * y⁻¹ * x * y) : M₃) := by
  have hx' := mem_Dh_of_J hx
  have hy' := mem_Dh_of_J hy
  have hcy : c' * y ∈ Dh ⊓ centralizer (E : Set G) := mul_mem (h.C_le_J hc') hy
  have e1 : (c * x)⁻¹ * (c' * y)⁻¹ * (c * x) * (c' * y) =
      (x⁻¹ * (c⁻¹ * (c' * y)⁻¹ * c * (c' * y)) * x) * (x⁻¹ * (c' * y)⁻¹ * x * (c' * y)) := by
    group
  have hu : x⁻¹ * (c⁻¹ * (c' * y)⁻¹ * c * (c' * y)) * x ∈ E :=
    h.conj_inv_mem_E hx' (h.C_Dh c hc _ (mem_Dh_of_J hcy))
  have e2 : x⁻¹ * (c' * y)⁻¹ * x * (c' * y) =
      (x⁻¹ * y⁻¹ * x * y) * (y⁻¹ * (c'⁻¹ * x⁻¹ * c' * x)⁻¹ * y) := by
    group
  have hv : y⁻¹ * (c'⁻¹ * x⁻¹ * c' * x)⁻¹ * y ∈ E :=
    h.conj_inv_mem_E hy' (inv_mem (h.C_Dh c' hc' x hx'))
  rw [e1, h.dν_mul (h.E_C hu) (h.comm_mem_C hx hcy), h.dν_E hu, zero_add, e2,
    h.dν_mul (h.comm_mem_C hx hy) (h.E_C hv), h.dν_E hv, add_zero]

theorem lev_comm (lev : GL (Fin 3) (ZMod 2) →* G) (g : GL (Fin 3) (ZMod 2)) (x y : G) :
    lev g * (x⁻¹ * y⁻¹ * x * y) * (lev g)⁻¹ =
      (lev g * x * (lev g)⁻¹)⁻¹ * (lev g * y * (lev g)⁻¹)⁻¹ * (lev g * x * (lev g)⁻¹) *
        (lev g * y * (lev g)⁻¹) := by
  group

theorem lev_conj_eq (h : JBase τ lev z ν A D C E Dh) (g : GL (Fin 3) (ZMod 2)) {x y : G}
    (hx : x ∈ Dh ⊓ centralizer (E : Set G)) (hy : y ∈ Dh ⊓ centralizer (E : Set G))
    (hg : (g : M₃) *ᵥ wvec z ν x = wvec z ν y) :
    ∃ c ∈ C, lev g * x * (lev g)⁻¹ = c * y := by
  have hx' := h.lev_conj_mem_J g hx
  refine ⟨lev g * x * (lev g)⁻¹ * y⁻¹, h.mul_inv_mem_C hx' hy ?_, by group⟩
  rw [h.wvec_lev g (mem_Dh_of_J hx), hg]

theorem comm_basis (h : JBase τ lev z ν A D C E Dh) {x₁ x₂ : G}
    (hx₁ : x₁ ∈ Dh ⊓ centralizer (E : Set G)) (hx₂ : x₂ ∈ Dh ⊓ centralizer (E : Set G))
    (hw₁ : wvec z ν x₁ = ![1, 0, 0]) (hw₂ : wvec z ν x₂ = ![0, 1, 0]) :
    x₁⁻¹ * x₂⁻¹ * x₁ * x₂ ∈ E := by
  have hk := h.comm_mem_C hx₁ hx₂
  refine (h.ν_E _ hk).1 (fix_pair_check _ ?_ ?_)
  · obtain ⟨c₁, hc₁, e₁⟩ := h.lev_conj_eq glTransThreeOne hx₁ hx₁
      (by rw [hw₁, glTransThreeOne_e1])
    obtain ⟨c₂, hc₂, e₂⟩ := h.lev_conj_eq glTransThreeOne hx₂ hx₂
      (by rw [hw₂, glTransThreeOne_e2])
    rw [← h.dν_lev _ hk, lev_comm, e₁, e₂, h.dν_comm_mul hx₁ hx₂ hc₁ hc₂]
  · obtain ⟨c₁, hc₁, e₁⟩ := h.lev_conj_eq glRot hx₁ hx₂ (by rw [hw₁, hw₂, glRot_e1])
    obtain ⟨c₂, hc₂, e₂⟩ := h.lev_conj_eq glRot hx₂ (mul_mem hx₁ hx₂)
      (by rw [hw₂, h.wvec_mul (mem_Dh_of_J hx₁) (mem_Dh_of_J hx₂), hw₁, hw₂, glRot_e2,
        e1_add_e2])
    rw [← h.dν_lev _ hk, lev_comm, e₁, e₂, h.dν_comm_mul hx₂ (mul_mem hx₁ hx₂) hc₁ hc₂]
    have e3 : x₂⁻¹ * (x₁ * x₂)⁻¹ * x₂ * (x₁ * x₂) =
        x₂⁻¹ * (x₁⁻¹ * x₂⁻¹ * x₁ * x₂)⁻¹ * x₂ := by
      group
    rw [e3, h.dν_conj (inv_mem hk) (mem_Dh_of_J hx₂), h.ν_inv hk]

theorem comm_mem_E (h : JBase τ lev z ν A D C E Dh) {x y : G}
    (hx : x ∈ Dh ⊓ centralizer (E : Set G)) (hy : y ∈ Dh ⊓ centralizer (E : Set G)) :
    x⁻¹ * y⁻¹ * x * y ∈ E := by
  obtain ⟨x₁, hx₁, hw₁⟩ := h.exists_J_wvec ![1, 0, 0]
  obtain ⟨x₂, hx₂, hw₂⟩ := h.exists_J_wvec ![0, 1, 0]
  have h12 := h.comm_basis hx₁ hx₂ hw₁ hw₂
  by_cases hwx : wvec z ν x = 0
  · exact h.C_Dh x (h.mem_C_of_J hx hwx) y (mem_Dh_of_J hy)
  by_cases hwy : wvec z ν y = 0
  · have e : x⁻¹ * y⁻¹ * x * y = (y⁻¹ * x⁻¹ * y * x)⁻¹ := by group
    rw [e]
    exact inv_mem (h.C_Dh y (h.mem_C_of_J hy hwy) x (mem_Dh_of_J hx))
  by_cases hxy : wvec z ν x = wvec z ν y
  · have hc := h.mul_inv_mem_C hx hy hxy
    have e : x⁻¹ * y⁻¹ * x * y = y⁻¹ * ((x * y⁻¹)⁻¹ * y⁻¹ * (x * y⁻¹) * y) * y := by group
    rw [e]
    exact h.conj_inv_mem_E (mem_Dh_of_J hy) (h.C_Dh _ hc y (mem_Dh_of_J hy))
  · obtain ⟨g, hg₁, hg₂⟩ := exists_gl_pair hwx hwy hxy
    obtain ⟨c, hc, ec⟩ := h.lev_conj_eq g hx₁ hx (by rw [hw₁, hg₁])
    obtain ⟨c', hc', ec'⟩ := h.lev_conj_eq g hx₂ hy (by rw [hw₂, hg₂])
    refine (h.ν_E _ (h.comm_mem_C hx hy)).1 ?_
    rw [← h.dν_comm_mul hx hy hc hc', ← ec, ← ec', ← lev_comm,
      h.dν_lev g (h.comm_mem_C hx₁ hx₂), h.dν_E h12, mulVec_zero]

theorem sq_mem_A (h : JBase τ lev z ν A D C E Dh) {c : G} (hc : c ∈ C) : c * c ∈ A := by
  rw [← h.A_sq]
  exact subset_closure ⟨c, hc, pow_two c⟩

theorem dν_sq_mul (h : JBase τ lev z ν A D C E Dh) {c x : G} (hc : c ∈ C)
    (hx : x ∈ Dh ⊓ centralizer (E : Set G)) :
    symThreeDiag (ν ((c * x) * (c * x)) : M₃) = symThreeDiag (ν (x * x) : M₃) := by
  have hcc := h.sq_mem_A hc
  have he : c⁻¹ * x * c * x⁻¹ ∈ E := by
    have := h.C_Dh c hc x⁻¹ (inv_mem (mem_Dh_of_J hx))
    rwa [inv_inv] at this
  have e : (c * x) * (c * x) = (c * c) * ((c⁻¹ * x * c * x⁻¹) * (x * x)) := by group
  rw [e, h.dν_mul (h.A_C hcc) (mul_mem (h.E_C he) (h.sq_mem_C hx)), h.dν_E (h.A_E hcc), zero_add,
    h.dν_mul (h.E_C he) (h.sq_mem_C hx), h.dν_E he, zero_add]

theorem dν_sq_of_wvec (h : JBase τ lev z ν A D C E Dh) (g : GL (Fin 3) (ZMod 2)) {x₁ x : G}
    (hx₁ : x₁ ∈ Dh ⊓ centralizer (E : Set G)) (hx : x ∈ Dh ⊓ centralizer (E : Set G))
    (hg : (g : M₃) *ᵥ wvec z ν x₁ = wvec z ν x) :
    symThreeDiag (ν (x * x) : M₃) = (g : M₃) *ᵥ symThreeDiag (ν (x₁ * x₁) : M₃) := by
  obtain ⟨c, hc, ec⟩ := h.lev_conj_eq g hx₁ hx hg
  have e : lev g * (x₁ * x₁) * (lev g)⁻¹ = (c * x) * (c * x) := by
    rw [← ec]
    group
  rw [← h.dν_lev g (h.sq_mem_C hx₁), e, h.dν_sq_mul hc hx]

theorem nu_comm_z_mul (h : JBase τ lev z ν A D C E Dh)
    (hcen : ∀ c ∈ C, ∀ y ∈ Dh ⊓ centralizer (E : Set G), c * y = y * c) {x y : G}
    (hx : x ∈ Dh ⊓ centralizer (E : Set G)) (hy : y ∈ Dh ⊓ centralizer (E : Set G)) :
    ν (z⁻¹ * ((x * y)⁻¹ * z * (x * y))) = ν (z⁻¹ * (x⁻¹ * z * x)) + ν (z⁻¹ * (y⁻¹ * z * y)) := by
  have hkx := h.zt_C x (mem_Dh_of_J hx)
  have hky := h.zt_C y (mem_Dh_of_J hy)
  have e : z⁻¹ * ((x * y)⁻¹ * z * (x * y)) =
      (z⁻¹ * (y⁻¹ * z * y)) * (z⁻¹ * (x⁻¹ * z * x)) := by
    calc z⁻¹ * ((x * y)⁻¹ * z * (x * y)) =
          (z⁻¹ * (y⁻¹ * z * y)) * (y⁻¹ * ((z⁻¹ * (x⁻¹ * z * x)) * y)) := by group
      _ = (z⁻¹ * (y⁻¹ * z * y)) * (y⁻¹ * (y * (z⁻¹ * (x⁻¹ * z * x)))) := by
          rw [hcen _ hkx y hy]
      _ = (z⁻¹ * (y⁻¹ * z * y)) * (z⁻¹ * (x⁻¹ * z * x)) := by group
  rw [e, h.ν_mul _ hky _ hkx, add_comm]

theorem nu_comm_z_C (h : JBase τ lev z ν A D C E Dh) {c : G} (hc : c ∈ C) :
    ν (z⁻¹ * (c⁻¹ * z * c)) = 0 := by
  have hA : z⁻¹ * (c⁻¹ * z * c) ∈ A := by
    rw [h.zcomm c (h.C_D hc)]
    exact h.τ_mem _
  exact (h.ν_A _ (h.A_C hA)).2 hA

theorem nu_comm_z_lev (h : JBase τ lev z ν A D C E Dh) (g : GL (Fin 3) (ZMod 2)) {x : G}
    (hx : x ∈ Dh) :
    ν (z⁻¹ * ((lev g * x * (lev g)⁻¹)⁻¹ * z * (lev g * x * (lev g)⁻¹))) =
      symThreeCongr g (ν (z⁻¹ * (x⁻¹ * z * x))) := by
  have hz : (lev g)⁻¹ * z = z * (lev g)⁻¹ := by
    rw [← map_inv]
    exact h.lev_z g⁻¹
  have hz' : z⁻¹ * lev g = lev g * z⁻¹ := by
    calc z⁻¹ * lev g = z⁻¹ * (lev g * z) * z⁻¹ := by group
      _ = z⁻¹ * (z * lev g) * z⁻¹ := by rw [h.lev_z g]
      _ = lev g * z⁻¹ := by group
  have e : z⁻¹ * ((lev g * x * (lev g)⁻¹)⁻¹ * z * (lev g * x * (lev g)⁻¹)) =
      lev g * (z⁻¹ * (x⁻¹ * z * x)) * (lev g)⁻¹ := by
    calc z⁻¹ * ((lev g * x * (lev g)⁻¹)⁻¹ * z * (lev g * x * (lev g)⁻¹)) =
          (z⁻¹ * lev g) * x⁻¹ * ((lev g)⁻¹ * z) * lev g * x * (lev g)⁻¹ := by group
      _ = (lev g * z⁻¹) * x⁻¹ * (z * (lev g)⁻¹) * lev g * x * (lev g)⁻¹ := by rw [hz, hz']
      _ = lev g * (z⁻¹ * (x⁻¹ * z * x)) * (lev g)⁻¹ := by group
  rw [e, (h.ν_lev g _ (h.zt_C x hx)).2]

theorem coe_sym_eta3 (B : 𝕊) :
    (B : M₃) = !![(B : M₃) 0 0, (B : M₃) 0 1, (B : M₃) 0 2; (B : M₃) 0 1, (B : M₃) 1 1,
      (B : M₃) 1 2; (B : M₃) 0 2, (B : M₃) 1 2, (B : M₃) 2 2] := by
  have hB : (B : M₃)ᵀ = B := B.2
  have h10 : (B : M₃) 1 0 = (B : M₃) 0 1 := congrFun (congrFun hB 0) 1
  have h20 : (B : M₃) 2 0 = (B : M₃) 0 2 := congrFun (congrFun hB 0) 2
  have h21 : (B : M₃) 2 1 = (B : M₃) 1 2 := congrFun (congrFun hB 1) 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10, h20, h21]

theorem false_of_sq_eq (h : JBase τ lev z ν A D C E Dh) {x₁ : G}
    (hx₁ : x₁ ∈ Dh ⊓ centralizer (E : Set G)) (hw₁ : wvec z ν x₁ = ![1, 0, 0])
    (hs₁ : symThreeDiag (ν (x₁ * x₁) : M₃) = ![1, 0, 0]) : False := by
  have hs : ∀ x ∈ Dh ⊓ centralizer (E : Set G),
      symThreeDiag (ν (x * x) : M₃) = wvec z ν x := by
    intro x hx
    by_cases hw : wvec z ν x = 0
    · rw [hw]
      exact h.dν_E (h.A_E (h.sq_mem_A (h.mem_C_of_J hx hw)))
    · obtain ⟨v, hv0, hv⟩ := exists_ne_zero_ne (wvec z ν x)
      obtain ⟨g, hg, -⟩ := exists_gl_pair hw hv0 hv
      rw [h.dν_sq_of_wvec g hx₁ hx (by rw [hw₁, hg]), hs₁, hg]
  have hsq : ∀ x ∈ Dh ⊓ centralizer (E : Set G), ∀ y ∈ Dh ⊓ centralizer (E : Set G),
      (x * x) * y = y * (x * x) := by
    intro x hx y hy
    have hk := h.comm_mem_E hx hy
    have hkx := comm_of_J hx hk
    have hkk := h.E_sq _ hk
    generalize hkdef : x⁻¹ * y⁻¹ * x * y = k at hk hkx hkk
    have e1 : y⁻¹ * x * y = x * k := by rw [← hkdef]; group
    calc (x * x) * y = y * ((y⁻¹ * x * y) * (y⁻¹ * x * y)) := by group
      _ = y * (x * (k * x) * k) := by rw [e1]; group
      _ = y * (x * (x * k) * k) := by rw [hkx]
      _ = y * (x * x * (k * k)) := by group
      _ = y * (x * x) := by rw [hkk, mul_one]
  have hcen : ∀ c ∈ C, ∀ y ∈ Dh ⊓ centralizer (E : Set G), c * y = y * c := by
    intro c hc y hy
    obtain ⟨x, hx, hxw⟩ := h.exists_J_wvec (symThreeDiag (ν c : M₃))
    have he := h.mul_inv_mem_E_of_dν_eq hc (h.sq_mem_C hx) (by rw [hs x hx, hxw])
    have hey := comm_of_J hy he
    have e : c = (c * (x * x)⁻¹) * (x * x) := by group
    rw [e, mul_assoc, hsq x hx y hy, ← mul_assoc, hey, mul_assoc]
  have hfixB : ∀ p : GL (Fin 3) (ZMod 2), (p : M₃) *ᵥ ![1, 0, 0] = ![1, 0, 0] →
      symThreeCongr p (ν (z⁻¹ * (x₁⁻¹ * z * x₁))) = ν (z⁻¹ * (x₁⁻¹ * z * x₁)) := by
    intro p hp
    obtain ⟨c, hc, ec⟩ := h.lev_conj_eq p hx₁ hx₁ (by rw [hw₁, hp])
    rw [← h.nu_comm_z_lev p (mem_Dh_of_J hx₁), ec, h.nu_comm_z_mul hcen (h.C_le_J hc) hx₁,
      h.nu_comm_z_C hc, zero_add]
  have hx₂ : lev glSwapOneTwo * x₁ * (lev glSwapOneTwo)⁻¹ ∈ Dh ⊓ centralizer (E : Set G) :=
    h.lev_conj_mem_J _ hx₁
  obtain ⟨c, hc, ec⟩ := h.lev_conj_eq glRot⁻¹ hx₁ (mul_mem hx₁ hx₂)
    (by rw [hw₁, h.wvec_mul (mem_Dh_of_J hx₁) (mem_Dh_of_J hx₂), hw₁,
      h.wvec_lev _ (mem_Dh_of_J hx₁), hw₁, glSwapOneTwo_e1, glRot_inv_e1, e1_add_e2])
  have key := h.nu_comm_z_lev glRot⁻¹ (mem_Dh_of_J hx₁)
  rw [ec, h.nu_comm_z_mul hcen (h.C_le_J hc) (mul_mem hx₁ hx₂), h.nu_comm_z_C hc, zero_add,
    h.nu_comm_z_mul hcen hx₁ hx₂, h.nu_comm_z_lev glSwapOneTwo (mem_Dh_of_J hx₁)] at key
  have hdB : symThreeDiag (ν (z⁻¹ * (x₁⁻¹ * z * x₁)) : M₃) = ![1, 0, 0] := hw₁
  have hfix : ∀ p : GL (Fin 3) (ZMod 2), (p : M₃) *ᵥ ![1, 0, 0] = ![1, 0, 0] →
      (p : M₃) * (ν (z⁻¹ * (x₁⁻¹ * z * x₁)) : M₃) * (p : M₃)ᵀ =
        (ν (z⁻¹ * (x₁⁻¹ * z * x₁)) : M₃) := fun p hp => by
    have := congrArg Subtype.val (hfixB p hp)
    rwa [coe_symThreeCongr] at this
  have h1 := hfix _ glSwapTwoThree_e1
  have h2 := hfix _ glTransTwoOne_e1
  have h3 := hfix _ glTransThreeTwo_e1
  have h4 := congrArg Subtype.val key
  change (ν (z⁻¹ * (x₁⁻¹ * z * x₁)) : M₃) +
      ((symThreeCongr glSwapOneTwo (ν (z⁻¹ * (x₁⁻¹ * z * x₁))) : M₃)) =
    ((symThreeCongr glRot⁻¹ (ν (z⁻¹ * (x₁⁻¹ * z * x₁))) : M₃)) at h4
  rw [coe_symThreeCongr, coe_symThreeCongr] at h4
  generalize ν (z⁻¹ * (x₁⁻¹ * z * x₁)) = B at hdB h1 h2 h3 h4
  rw [coe_sym_eta3 B] at h1 h2 h3 h4
  exact sym_check _ _ _ _ _ _ (congrFun hdB 0) (congrFun hdB 1) (congrFun hdB 2) h1 h2 h3 h4

theorem sq_mem_E (h : JBase τ lev z ν A D C E Dh) {x : G}
    (hx : x ∈ Dh ⊓ centralizer (E : Set G)) : x * x ∈ E := by
  obtain ⟨x₁, hx₁, hw₁⟩ := h.exists_J_wvec ![1, 0, 0]
  have hfix : ∀ p : GL (Fin 3) (ZMod 2), (p : M₃) *ᵥ ![1, 0, 0] = ![1, 0, 0] →
      (p : M₃) *ᵥ symThreeDiag (ν (x₁ * x₁) : M₃) = symThreeDiag (ν (x₁ * x₁) : M₃) :=
    fun p hp => (h.dν_sq_of_wvec p hx₁ hx₁ (by rw [hw₁, hp])).symm
  rcases fix_one_check _ (hfix _ glTransTwoOne_e1) (hfix _ glTransThreeOne_e1) with hs₁ | hs₁
  · refine (h.ν_E _ (h.sq_mem_C hx)).1 ?_
    by_cases hw : wvec z ν x = 0
    · exact h.dν_E (h.A_E (h.sq_mem_A (h.mem_C_of_J hx hw)))
    · obtain ⟨v, hv0, hv⟩ := exists_ne_zero_ne (wvec z ν x)
      obtain ⟨g, hg, -⟩ := exists_gl_pair hw hv0 hv
      rw [h.dν_sq_of_wvec g hx₁ hx (by rw [hw₁, hg]), hs₁, mulVec_zero]
  · exact (h.false_of_sq_eq hx₁ hw₁ hs₁).elim

end JBase

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64.Jhat
