module

public import CFSG.ClassicalInvolution.WeakCT.A2Signs
public import CFSG.ClassicalInvolution.WeakCT.B2Signs

public section

namespace CFSG.ClassicalInvolution.WeakCT

structure V2Data (G F : Type*) [Group G] [Field F] where
  xa : F → G
  xa' : F → G
  xb : F → G
  xc : F → G
  ν : F
  μ : F
  ηb : F
  ηc : F
  add_a : ∀ s t, xa (s + t) = xa s * xa t
  add_a' : ∀ s t, xa' (s + t) = xa' s * xa' t
  add_b : ∀ s t, xb (s + t) = xb s * xb t
  add_c : ∀ s t, xc (s + t) = xc s * xc t
  comm_bc : ∀ s t, xb s * xc t = xc t * xb s
  conj_a_b : ∀ t v, xa t * xb v * xa (-t) = xb v * xc (ν * t * v)
  conj_a_c : ∀ t v, xa t * xc v * xa (-t) = xc v
  conj_a'_b : ∀ t v, xa' t * xb v * xa' (-t) = xb v
  conj_a'_c : ∀ t v, xa' t * xc v * xa' (-t) = xc v * xb (μ * t * v)
  conj_n_b : ∀ v, xa 1 * xa' (-1) * xa 1 * xb v * (xa 1 * xa' (-1) * xa 1)⁻¹ = xc (ηb * v)
  conj_n_c : ∀ v, xa 1 * xa' (-1) * xa 1 * xc v * (xa 1 * xa' (-1) * xa 1)⁻¹ = xb (ηc * v)
  ext : ∀ u₁ u₂ u₁' u₂', xb u₁ * xc u₂ = xb u₁' * xc u₂' → u₁ = u₁' ∧ u₂ = u₂'

namespace V2Data

variable {G F : Type*} [Group G] [Field F] (D : V2Data G F)

theorem xb_zero : D.xb 0 = 1 := by
  have h := D.add_b 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem xc_zero : D.xc 0 = 1 := by
  have h := D.add_c 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem xa_zero : D.xa 0 = 1 := by
  have h := D.add_a 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem xa'_zero : D.xa' 0 = 1 := by
  have h := D.add_a' 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem xa_neg (t : F) : D.xa (-t) = (D.xa t)⁻¹ := by
  have h := D.add_a t (-t)
  rw [add_neg_cancel, D.xa_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem xa'_neg (t : F) : D.xa' (-t) = (D.xa' t)⁻¹ := by
  have h := D.add_a' t (-t)
  rw [add_neg_cancel, D.xa'_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

def Φ (v : F × F) : G := D.xb v.1 * D.xc v.2

theorem Φ_add (u v : F × F) : D.Φ (u + v) = D.Φ u * D.Φ v := by
  obtain ⟨u₁, u₂⟩ := u
  obtain ⟨v₁, v₂⟩ := v
  simp only [Φ, Prod.fst_add, Prod.snd_add, D.add_b, D.add_c]
  have h2 : D.xc u₂ * D.xb v₁ = D.xb v₁ * D.xc u₂ := (D.comm_bc v₁ u₂).symm
  calc D.xb u₁ * D.xb v₁ * (D.xc u₂ * D.xc v₂)
      = D.xb u₁ * (D.xb v₁ * D.xc u₂) * D.xc v₂ := by group
    _ = D.xb u₁ * (D.xc u₂ * D.xb v₁) * D.xc v₂ := by rw [h2]
    _ = _ := by group

theorem Φ_zero_left (v₂ : F) : D.Φ (0, v₂) = D.xc v₂ := by
  simp [Φ, D.xb_zero]

theorem Φ_zero_right (v₁ : F) : D.Φ (v₁, 0) = D.xb v₁ := by
  simp [Φ, D.xc_zero]

theorem Φ_inj {u v : F × F} (h : D.Φ u = D.Φ v) : u = v := by
  obtain ⟨h1, h2⟩ := D.ext u.1 u.2 v.1 v.2 h
  exact Prod.ext h1 h2

def Mf (t : F) (v : F × F) : F × F := (v.1, v.2 + D.ν * t * v.1)

def Lf (t : F) (v : F × F) : F × F := (v.1 + D.μ * t * v.2, v.2)

theorem conj_a_Φ (t : F) (v : F × F) : D.xa t * D.Φ v * D.xa (-t) = D.Φ (D.Mf t v) := by
  obtain ⟨v₁, v₂⟩ := v
  have e : D.xa t * D.Φ (v₁, v₂) * D.xa (-t) =
      (D.xa t * D.xb v₁ * D.xa (-t)) * (D.xa t * D.xc v₂ * D.xa (-t)) := by
    rw [D.xa_neg]
    simp only [Φ]
    group
  rw [e, D.conj_a_b, D.conj_a_c]
  have e2 : D.xb v₁ * D.xc (D.ν * t * v₁) * D.xc v₂ =
      D.Φ (v₁, D.ν * t * v₁) * D.Φ (0, v₂) := by
    rw [D.Φ_zero_left]
    rfl
  rw [e2, ← D.Φ_add]
  congr 1
  simp only [Mf, Prod.mk_add_mk, add_zero]
  exact Prod.ext rfl (by simp only; ring)

theorem conj_a'_Φ (t : F) (v : F × F) : D.xa' t * D.Φ v * D.xa' (-t) = D.Φ (D.Lf t v) := by
  obtain ⟨v₁, v₂⟩ := v
  have e : D.xa' t * D.Φ (v₁, v₂) * D.xa' (-t) =
      (D.xa' t * D.xb v₁ * D.xa' (-t)) * (D.xa' t * D.xc v₂ * D.xa' (-t)) := by
    rw [D.xa'_neg]
    simp only [Φ]
    group
  rw [e, D.conj_a'_b, D.conj_a'_c]
  have e2 : D.xb v₁ * (D.xc v₂ * D.xb (D.μ * t * v₂)) =
      D.Φ (v₁, 0) * D.Φ (D.μ * t * v₂, v₂) := by
    rw [D.Φ_zero_right]
    simp only [Φ]
    have h1 : D.xc v₂ * D.xb (D.μ * t * v₂) = D.xb (D.μ * t * v₂) * D.xc v₂ :=
      (D.comm_bc _ _).symm
    rw [h1]
  rw [e2, ← D.Φ_add]
  congr 1
  simp only [Lf, Prod.mk_add_mk, zero_add]

theorem conj_n_Φ (v : F × F) :
    (D.xa 1 * D.xa' (-1) * D.xa 1) * D.Φ v * (D.xa 1 * D.xa' (-1) * D.xa 1)⁻¹ =
      D.Φ (D.ηc * v.2, D.ηb * v.1) := by
  obtain ⟨v₁, v₂⟩ := v
  have e : (D.xa 1 * D.xa' (-1) * D.xa 1) * D.Φ (v₁, v₂) *
      (D.xa 1 * D.xa' (-1) * D.xa 1)⁻¹ =
      ((D.xa 1 * D.xa' (-1) * D.xa 1) * D.xb v₁ * (D.xa 1 * D.xa' (-1) * D.xa 1)⁻¹) *
        ((D.xa 1 * D.xa' (-1) * D.xa 1) * D.xc v₂ * (D.xa 1 * D.xa' (-1) * D.xa 1)⁻¹) := by
    simp only [Φ]
    group
  rw [e, D.conj_n_b, D.conj_n_c]
  simp only [Φ]
  exact (D.comm_bc _ _).symm

theorem key (v : F × F) : D.Mf 1 (D.Lf (-1) (D.Mf 1 v)) = (D.ηc * v.2, D.ηb * v.1) := by
  apply D.Φ_inj
  rw [← D.conj_n_Φ v]
  have e : (D.xa 1 * D.xa' (-1) * D.xa 1) * D.Φ v * (D.xa 1 * D.xa' (-1) * D.xa 1)⁻¹ =
      D.xa 1 * (D.xa' (-1) * (D.xa 1 * D.Φ v * D.xa (-1)) * D.xa' (-(-1))) * D.xa (-1) := by
    rw [D.xa_neg 1, D.xa'_neg (-1)]
    group
  rw [e, D.conj_a_Φ, D.conj_a'_Φ, D.conj_a_Φ]

theorem result : D.ν = D.ηb ∧ D.μ = -D.ηc ∧ D.μ * D.ν = 1 := by
  have k1 := D.key (1, 0)
  have k2 := D.key (0, 1)
  simp only [Mf, Lf, Prod.mk.injEq] at k1 k2
  obtain ⟨a1, b1⟩ := k1
  obtain ⟨a2, b2⟩ := k2
  have h1 : D.μ * D.ν = 1 := by linear_combination -a1
  refine ⟨?_, ?_, h1⟩
  · linear_combination b1 + D.ν * h1
  · linear_combination -a2

end V2Data

section Cone

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Timmesfeld
  CFSG.Timmesfeld.LevisExtras
open scoped commutatorElement

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : Steinberg.CommOrder (Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}
  {i j : Fin D.rank}

theorem unit_zpow_sq {F : Type} [Field F] (t : Fˣ) (ht : t = 1 ∨ t = -1) (k : ℤ) :
    ((t ^ k : Fˣ) : F) * ((t ^ k : Fˣ) : F) = 1 := by
  rcases ht with rfl | rfl
  · simp
  · rcases Int.even_or_odd k with hk | hk
    · rw [hk.neg_one_zpow]; simp
    · rw [hk.neg_one_zpow]; simp

variable (hE : Steinberg.ChevalleyExtras D F x C O)
include hE

theorem Nz_cone_sq (hdiv : D.divisible = ∅) (hij : i ≠ j) (hcij : D.cartan i j = -1)
    (hcji : D.cartan j i = -1) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (t : Fˣ) (ht : t = 1 ∨ t = -1)
    (hn : x (pair i j (σ, 0)) 1 * x (pair i j (-σ, 0)) (-1) * x (pair i j (σ, 0)) 1 =
      Steinberg.weylElement x i t) :
    Nz F C i j (σ, 0) (0, σ) * Nz F C i j (σ, 0) (0, σ) = 1 := by
  have mA : ((σ, 0) : ℤ × ℤ) ∈ zEdge := by rcases hσ with rfl | rfl <;> decide
  have mA' : ((-σ, 0) : ℤ × ℤ) ∈ zEdge := by rcases hσ with rfl | rfl <;> decide
  have mB : ((0, σ) : ℤ × ℤ) ∈ zEdge := by rcases hσ with rfl | rfl <;> decide
  have mC : ((σ, σ) : ℤ × ℤ) ∈ zEdge := by rcases hσ with rfl | rfl <;> decide
  have zAB : ((σ, 0) : ℤ × ℤ) + (0, σ) = (σ, σ) := by rcases hσ with rfl | rfl <;> decide
  have zA'C : ((-σ, 0) : ℤ × ℤ) + (σ, σ) = (0, σ) := by rcases hσ with rfl | rfl <;> decide
  have zAC : ((σ, 0) : ℤ × ℤ) + (σ, σ) ∉ zEdge := by rcases hσ with rfl | rfl <;> decide
  have zA'B : ((-σ, 0) : ℤ × ℤ) + (0, σ) ∉ zEdge := by rcases hσ with rfl | rfl <;> decide
  have zBC : ((0, σ) : ℤ × ℤ) + (σ, σ) ∉ zEdge := by rcases hσ with rfl | rfl <;> decide
  have nAC : ((σ, 0) : ℤ × ℤ) + (σ, σ) ≠ 0 := by rcases hσ with rfl | rfl <;> decide
  have nA'B : ((-σ, 0) : ℤ × ℤ) + (0, σ) ≠ 0 := by rcases hσ with rfl | rfl <;> decide
  have nBC : ((0, σ) : ℤ × ℤ) + (σ, σ) ≠ 0 := by rcases hσ with rfl | rfl <;> decide
  have rA := pair_mem_roots_zEdge hcij hcji _ mA
  have rA' := pair_mem_roots_zEdge hcij hcji _ mA'
  have rB := pair_mem_roots_zEdge hcij hcji _ mB
  have rC := pair_mem_roots_zEdge hcij hcji _ mC
  have cBC : ∀ u v, x (pair i j (0, σ)) u * x (pair i j (σ, σ)) v =
      x (pair i j (σ, σ)) v * x (pair i j (0, σ)) u := fun u v =>
    (commute_A2 hdiv hcij hcji hE hij mB mC nBC zBC u v).eq
  have hweyl : ∀ z ∈ ({(0, σ), (σ, σ)} : Finset (ℤ × ℤ)), ∀ u : F,
      Steinberg.weylElement x i t * x (pair i j z) u * (Steinberg.weylElement x i t)⁻¹ =
        x (pair i j (rL z))
          (wsign hE i (pair i j z) * ((t ^ (-(2 * z.1 - z.2)) : Fˣ) : F) * u) := by
    intro z hz u
    have hzm : z ∈ zEdge := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    rw [(wsign_spec hE (pair_mem_roots_zEdge hcij hcji z hzm)).2 t u, reflection_pair_rL hcij,
      sum_cartan_pair_left hcij]
  have hsq := fun k : ℤ => unit_zpow_sq (F := F) t ht k
  let V : V2Data K F :=
    { xa := x (pair i j (σ, 0))
      xa' := x (pair i j (-σ, 0))
      xb := x (pair i j (0, σ))
      xc := x (pair i j (σ, σ))
      ν := Nz F C i j (σ, 0) (0, σ)
      μ := Nz F C i j (-σ, 0) (σ, σ)
      ηb := wsign hE i (pair i j (0, σ)) * ((t ^ (-(2 * 0 - σ)) : Fˣ) : F)
      ηc := wsign hE i (pair i j (σ, σ)) * ((t ^ (-(2 * σ - σ)) : Fˣ) : F)
      add_a := x_add' hE rA
      add_a' := x_add' hE rA'
      add_b := x_add' hE rB
      add_c := x_add' hE rC
      comm_bc := cBC
      conj_a_b := fun t' v => by
        rw [conj_eq_comm hE rA, rel_A2 hdiv hcij hcji hE hij mA mB zAB mC]
        exact (cBC _ _).symm
      conj_a_c := fun t' v => by
        rw [conj_eq_comm hE rA, commutatorElement_eq_one_iff_commute.2
          (commute_A2 hdiv hcij hcji hE hij mA mC nAC zAC t' v), one_mul]
      conj_a'_b := fun t' v => by
        rw [conj_eq_comm hE rA', commutatorElement_eq_one_iff_commute.2
          (commute_A2 hdiv hcij hcji hE hij mA' mB nA'B zA'B t' v), one_mul]
      conj_a'_c := fun t' v => by
        rw [conj_eq_comm hE rA', rel_A2 hdiv hcij hcji hE hij mA' mC zA'C mB]
        exact cBC _ _
      conj_n_b := fun v => by
        rw [hn, hweyl (0, σ) (by simp) v, show rL (0, σ) = (σ, σ) by simp [rL]]
      conj_n_c := fun v => by
        rw [hn, hweyl (σ, σ) (by simp) v, show rL (σ, σ) = (0, σ) by simp [rL]]
      ext := fun u₁ u₂ u₁' u₂' h =>
        ext2 hE rB rC (fun e => by
          have := pair_injective hij e
          rcases hσ with rfl | rfl <;> simp at this) (funcl i j (0, σ))
          (by rw [funcl_pair hij]; rcases hσ with rfl | rfl <;> decide)
          (by rw [funcl_pair hij]; rcases hσ with rfl | rfl <;> decide)
          (fun u v => commute_A2 hdiv hcij hcji hE hij mB mC nBC zBC u v) h }
  obtain ⟨h1, -, -⟩ := V.result
  have hη : V.ηb * V.ηb = 1 := by
    show wsign hE i (pair i j (0, σ)) * ((t ^ (-(2 * 0 - σ)) : Fˣ) : F) *
      (wsign hE i (pair i j (0, σ)) * ((t ^ (-(2 * 0 - σ)) : Fˣ) : F)) = 1
    have hw := wsign_mul_self hE (k := i) (pair_mem_roots_zEdge hcij hcji _ mB)
    calc _ = (wsign hE i (pair i j (0, σ)) * wsign hE i (pair i j (0, σ))) *
          (((t ^ (-(2 * 0 - σ)) : Fˣ) : F) * ((t ^ (-(2 * 0 - σ)) : Fˣ) : F)) := by ring
      _ = 1 := by rw [hw, hsq, one_mul]
  have h2 : V.ν = V.ηb := h1
  calc Nz F C i j (σ, 0) (0, σ) * Nz F C i j (σ, 0) (0, σ) = V.ν * V.ν := rfl
    _ = V.ηb * V.ηb := by rw [h2]
    _ = 1 := hη

theorem Nz_pos_sq (hdiv : D.divisible = ∅) (hij : i ≠ j) (hcij : D.cartan i j = -1)
    (hcji : D.cartan j i = -1) :
    Nz F C i j (1, 0) (0, 1) * Nz F C i j (1, 0) (0, 1) = 1 :=
  Nz_cone_sq hE hdiv hij hcij hcji (σ := 1) (Or.inl rfl) 1 (Or.inl rfl)
    (by simp [Steinberg.weylElement, pair_one_zero, pair_neg_one_zero])

theorem Nz_neg_sq (hdiv : D.divisible = ∅) (hij : i ≠ j) (hcij : D.cartan i j = -1)
    (hcji : D.cartan j i = -1) :
    Nz F C i j (-1, 0) (0, -1) * Nz F C i j (-1, 0) (0, -1) = 1 := by
  have h := Nz_cone_sq hE hdiv hij hcij hcji (σ := -1) (Or.inr rfl) (-1) (Or.inr rfl)
    (by simpa [pair_one_zero, pair_neg_one_zero] using weylElement_neg_one_eq hE i)
  simpa using h

end Cone

end CFSG.ClassicalInvolution.WeakCT
