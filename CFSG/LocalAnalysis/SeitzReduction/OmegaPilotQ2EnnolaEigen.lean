module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2EnnolaRot
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2EnnolaHyp

public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Matrix
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.LieType.Universal.Spin (quadPlus quadPlus_apply coe_quadPlus)

section HypGL

variable {F : Type} [Field F] {m : ℕ}

theorem exists_gl_of_hypBasis' (Q₂ : QuadraticForm F (Fin m ⊕ Fin m → F))
    (w : Fin m ⊕ Fin m → Fin m ⊕ Fin m → F) (hQ : ∀ l, Q₂ (w l) = 0)
    (hB : ∀ l l', polar Q₂ (w l) (w l') = if l' = Sum.swap l then 1 else 0) :
    ∃ P : GL (Fin m ⊕ Fin m) F, (∀ s l, (P : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) s l = w l s) ∧
      ∀ v, Q₂ ((P : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) *ᵥ v) = StatedQuadPlus m F v := by
  set P : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F := Matrix.of fun s l => w l s with hP
  set P' : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F :=
    Matrix.of fun l s => polar Q₂ (w (Sum.swap l)) (Pi.single s 1) with hP'
  have h1 : P' * P = 1 := by
    ext l l'
    have h := hB (Sum.swap l) l'
    have hsum : polar Q₂ (w (Sum.swap l)) (w l') =
        ∑ s, polar Q₂ (w (Sum.swap l)) (Pi.single s 1) * w l' s := by
      conv_lhs => rw [eq_sum_smul_single (w l')]
      rw [← polarBilin_apply_apply, map_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [map_smul, polarBilin_apply_apply, smul_eq_mul, mul_comm]
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [hP, hP', Matrix.of_apply]
    rw [← hsum, h, Sum.swap_swap]
    by_cases hl : l = l'
    · simp [hl]
    · simp [hl, Ne.symm hl]
  have h2 : P * P' = 1 := mul_eq_one_comm.mp h1
  refine ⟨⟨P, P', h2, h1⟩, fun s l => rfl, fun v => ?_⟩
  have hPv : P *ᵥ v = ∑ l, v l • w l := by
    funext s
    simp [hP, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  change Q₂ (P *ᵥ v) = StatedQuadPlus m F v
  rw [hPv, ← coe_quadPlus]
  conv_rhs => rw [eq_sum_smul_single v]
  exact quad_sum_smul_eq_of_gram _ _ _ _ (fun l => by rw [hQ, quadPlus_single])
    (fun l l' _ => by rw [hB, polar_quadPlus_single]) v

end HypGL

section Pairs

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} {F : Type} [Field F] [CharP F 2]

structure EnnolaPairData (Q : QuadraticForm K (Fin d → K)) (E : EnnolaParam K F) (N : ℕ)
    (Q₂ : QuadraticForm F (Fin (N + 1) ⊕ Fin (N + 1) → F)) (W : Submodule K (Fin d → K)) where
  pa : Fin (N + 1) → Fin d → K
  pb : Fin (N + 1) → Fin d → K
  unit : Fin (N + 1) → Bool
  pa_mem : ∀ k, pa k ∈ W
  pb_mem : ∀ k, pb k ∈ W
  unit_plane : ∀ k, unit k = true → IsUnitPlane Q (pa k) (pb k)
  hyp : ∀ k, unit k = false → Q (pa k) = 0 ∧ Q (pb k) = 0 ∧ polar Q (pa k) (pb k) = 1
  orth : ∀ k k', k ≠ k' → polar Q (pa k) (pa k') = 0 ∧ polar Q (pa k) (pb k') = 0 ∧
    polar Q (pb k) (pa k') = 0 ∧ polar Q (pb k) (pb k') = 0
  J : (Fin d → K) →+ (Fin (N + 1) ⊕ Fin (N + 1) → F)
  J_smul : ∀ (c : K) (v : Fin d → K), J (c • v) = E.ι c • J v
  quad_J : ∀ v ∈ W, Q₂ (J v) = E.ι (Q v)

variable {Q : QuadraticForm K (Fin d → K)} {E : EnnolaParam K F} {N : ℕ}
  {Q₂ : QuadraticForm F (Fin (N + 1) ⊕ Fin (N + 1) → F)} {W : Submodule K (Fin d → K)}

namespace EnnolaPairData

variable (D : EnnolaPairData Q E N Q₂ W)

theorem polar_J {v w : Fin d → K} (hv : v ∈ W) (hw : w ∈ W) :
    polar Q₂ (D.J v) (D.J w) = E.ι (polar Q v w) := by
  rw [QuadraticMap.polar, QuadraticMap.polar, ← map_add, D.quad_J _ (W.add_mem hv hw),
    D.quad_J _ hv, D.quad_J _ hw, map_sub, map_sub]

theorem quad_combo {a b : Fin d → K} (ha : a ∈ W) (hb : b ∈ W) (α β : F) :
    Q₂ (α • D.J a + β • D.J b) =
      α ^ 2 * E.ι (Q a) + β ^ 2 * E.ι (Q b) + α * β * E.ι (polar Q a b) := by
  rw [QuadraticMap.map_add Q₂, QuadraticMap.map_smul, QuadraticMap.map_smul, polar_smul_left,
    polar_smul_right, D.quad_J _ ha, D.quad_J _ hb, D.polar_J ha hb]
  simp only [smul_eq_mul]
  ring

theorem polar_combo {a b c e : Fin d → K} (ha : a ∈ W) (hb : b ∈ W) (hc : c ∈ W) (he : e ∈ W)
    (α β γ δ : F) :
    polar Q₂ (α • D.J a + β • D.J b) (γ • D.J c + δ • D.J e) =
      α * γ * E.ι (polar Q a c) + α * δ * E.ι (polar Q a e) + β * γ * E.ι (polar Q b c) +
        β * δ * E.ι (polar Q b e) := by
  simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, smul_eq_mul,
    D.polar_J ha hc, D.polar_J ha he, D.polar_J hb hc, D.polar_J hb he]
  ring

theorem polar_self_pair (k : Fin (N + 1)) :
    polar Q (D.pa k) (D.pb k) = 1 ∧ polar Q (D.pb k) (D.pa k) = 1 := by
  cases hk : D.unit k
  · have h := D.hyp k hk
    exact ⟨h.2.2, by rw [polar_comm]; exact h.2.2⟩
  · have hu := D.unit_plane k hk
    exact ⟨hu.polar_eq, hu.polar_symm⟩

@[expose] def idx (l : Fin (N + 1) ⊕ Fin (N + 1)) : Fin (N + 1) := Sum.elim id id l

@[expose] def coefA (l : Fin (N + 1) ⊕ Fin (N + 1)) : F :=
  Sum.elim (fun _ => 1) (fun k => if D.unit k then 1 else 0) l

@[expose] def coefB (l : Fin (N + 1) ⊕ Fin (N + 1)) : F :=
  Sum.elim (fun k => if D.unit k then E.ω else 0) (fun k => if D.unit k then E.ω + 1 else 1) l

@[expose] def w (l : Fin (N + 1) ⊕ Fin (N + 1)) : Fin (N + 1) ⊕ Fin (N + 1) → F :=
  D.coefA l • D.J (D.pa (idx l)) + D.coefB l • D.J (D.pb (idx l))

theorem quad_w (l : Fin (N + 1) ⊕ Fin (N + 1)) : Q₂ (D.w l) = 0 := by
  have hsq := E.sq
  rw [w, D.quad_combo (D.pa_mem _) (D.pb_mem _)]
  cases hk : D.unit (idx l)
  · obtain ⟨h1, h2, h3⟩ := D.hyp _ hk
    rw [h1, h2, h3, map_zero, map_one]
    rcases l with k | k <;> simp only [idx, Sum.elim_inl, Sum.elim_inr, id] at hk <;>
      simp only [coefA, coefB, Sum.elim_inl, Sum.elim_inr, hk] <;> simp
  · have hu := D.unit_plane _ hk
    rw [hu.map_left, hu.map_right, hu.polar_eq, map_one]
    rcases l with k | k <;> simp only [idx, Sum.elim_inl, Sum.elim_inr, id] at hk <;>
      simp only [coefA, coefB, Sum.elim_inl, Sum.elim_inr, hk, ↓reduceIte] <;> grind

theorem polar_w (l l' : Fin (N + 1) ⊕ Fin (N + 1)) :
    polar Q₂ (D.w l) (D.w l') = if l' = Sum.swap l then 1 else 0 := by
  have hsq := E.sq
  rw [w, w, D.polar_combo (D.pa_mem _) (D.pb_mem _) (D.pa_mem _) (D.pb_mem _)]
  by_cases hidx : idx l = idx l'
  · obtain ⟨b1, b2⟩ := D.polar_self_pair (idx l)
    rw [← hidx, polar_self_charTwo, polar_self_charTwo, b1, b2]
    simp only [map_zero, map_one, mul_zero, mul_one, zero_add, add_zero]
    rcases l with k | k <;> rcases l' with k' | k' <;>
      simp only [idx, Sum.elim_inl, Sum.elim_inr, id] at hidx <;>
      obtain rfl : k = k' := hidx <;>
      simp only [coefA, coefB, Sum.elim_inl, Sum.elim_inr, Sum.swap_inl, Sum.swap_inr,
        reduceCtorEq, ↓reduceIte] <;>
      split_ifs <;> grind
  · have ho := D.orth _ _ hidx
    rw [ho.1, ho.2.1, ho.2.2.1, ho.2.2.2]
    simp only [map_zero, mul_zero, add_zero]
    have hne : l' ≠ Sum.swap l := by
      intro h
      apply hidx
      rw [h]
      rcases l with k | k <;> rfl
    simp only [hne, ↓reduceIte]

theorem mulVec_w (G : (Fin d → K) →ₗ[K] (Fin d → K)) (k₀ : Fin (N + 1)) (hk₀ : D.unit k₀ = true)
    (x : Fˣ) (hGa : G (D.pa k₀) = (E.param x).1 • D.pa k₀ + (E.param x).2 • D.pb k₀)
    (hGb : G (D.pb k₀) = (E.param x).2 • D.pa k₀ + ((E.param x).1 + (E.param x).2) • D.pb k₀)
    (hGo : ∀ k, k ≠ k₀ → G (D.pa k) = D.pa k ∧ G (D.pb k) = D.pb k)
    (M : Matrix (Fin (N + 1) ⊕ Fin (N + 1)) (Fin (N + 1) ⊕ Fin (N + 1)) F)
    (hM : ∀ v ∈ W, M *ᵥ D.J v = D.J (G v)) (l : Fin (N + 1) ⊕ Fin (N + 1)) :
    M *ᵥ D.w l = SymplecticPilot.diagSpEntry (Pi.mulSingle k₀ x) l • D.w l := by
  have hsq := E.sq
  rw [w, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hM _ (D.pa_mem _),
    hM _ (D.pb_mem _)]
  by_cases hidx : idx l = k₀
  · rw [hidx, hGa, hGb, map_add, map_add, D.J_smul, D.J_smul, D.J_smul, D.J_smul, map_add]
    rcases l with k | k <;> simp only [idx, Sum.elim_inl, Sum.elim_inr, id] at hidx <;>
      subst hidx
    · have hx := E.ell_param x
      simp only [coefA, coefB, Sum.elim_inl, hk₀, ↓reduceIte, SymplecticPilot.diagSpEntry_inl,
        Pi.mulSingle_eq_same, idx, id]
      rw [← hx]
      match_scalars <;> grind
    · have hx := E.ell_conj_param x.ne_zero
      simp only [coefA, coefB, Sum.elim_inr, hk₀, ↓reduceIte, SymplecticPilot.diagSpEntry_inr,
        Pi.mulSingle_eq_same, Units.val_inv_eq_inv_val, idx, id]
      rw [← hx]
      match_scalars <;> grind
  · obtain ⟨h1, h2⟩ := hGo _ hidx
    rw [h1, h2]
    have hμ : SymplecticPilot.diagSpEntry (Pi.mulSingle k₀ x) l = 1 := by
      rcases l with k | k <;> simp only [idx, Sum.elim_inl, Sum.elim_inr, id] at hidx <;>
        simp [SymplecticPilot.diagSpEntry, Pi.mulSingle_eq_of_ne hidx]
    rw [hμ, one_smul]

end EnnolaPairData

end Pairs

end CFSG.SeitzReduction.OmegaPilot
