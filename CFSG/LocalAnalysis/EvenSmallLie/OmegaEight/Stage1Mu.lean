module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Basis
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Coh

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open Subgroup Matrix

variable {G : Type*} [Group G]

theorem kap_conj (g x y : G) : kap (g * x * g⁻¹) (g * y * g⁻¹) = g * kap x y * g⁻¹ := by
  rw [kap, kap]; group

namespace Setup

variable {ε : Eps} {t : G} {L U Q P : Subgroup G} {a : G} {ψ : V6 → G} {p : Fin 6 → G}
  (hS : Setup ε t L U Q P a ψ p)
  (hZ : ∀ v, v ∈ Zset t Q ψ)
include hS hZ

@[expose] noncomputable def gam [Finite G] (x y : ℕ) : V6 :=
  coord ψ (kap (hS.dB hZ x) (hS.dB hZ y))

@[expose] noncomputable def eGA [Finite G] (g : Fin 6) (x : ℕ) : G :=
  p g * hS.dB hZ x * (p g)⁻¹ * (hS.dV hZ (genMat ε g *ᵥ basisVec x))⁻¹

theorem conj_dB_mem [Finite G] (g : Fin 6) (x : ℕ) : p g * hS.dB hZ x * (p g)⁻¹ ∈ Dsub t Q :=
  hS.conj_mem_D (hS.rad.p_mem g) (hS.dB_mem hZ x)

theorem tauD_conj_dB [Finite G] (g : Fin 6) (x : ℕ) :
    tauD t ψ (p g * hS.dB hZ x * (p g)⁻¹) = genMat ε g *ᵥ basisVec x := by
  rw [hS.tauD_conj hZ (hS.rad.p_mem g) (hS.dB_mem hZ x), hS.tauD_dB hZ, hS.rad.lin_p]

theorem eGA_mem_E [Finite G] (g : Fin 6) (x : ℕ) :
    hS.eGA hZ g x ∈ (Q ⊔ zpowers t : Subgroup G) := by
  have h1 := hS.conj_dB_mem hZ g x
  have h2 := hS.dV_mem hZ (genMat ε g *ᵥ basisVec x)
  unfold eGA
  rw [← hS.tauD_eq_zero_iff hZ (mul_mem h1 (inv_mem h2))]
  have h3 : tauD t ψ ((hS.dV hZ (genMat ε g *ᵥ basisVec x))⁻¹) =
      genMat ε g *ᵥ basisVec x := by
    have := hS.tauD_mul hZ h2 (inv_mem h2)
    rw [mul_inv_cancel, (hS.tauD_eq_zero_iff hZ (one_mem _)).2 (one_mem _), hS.tauD_dV] at this
    have h4 : ∀ w w' : V6, 0 = w + w' → w' = w := fun w w' h => by
      rw [eq_comm, add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
      exact h.symm
    exact h4 _ _ this
  rw [hS.tauD_mul hZ h1 (inv_mem h2), hS.tauD_conj_dB hZ, h3, CharTwo.add_self_eq_zero]

theorem conj_dB_eq [Finite G] (g : Fin 6) (x : ℕ) :
    p g * hS.dB hZ x * (p g)⁻¹ = hS.eGA hZ g x * hS.dV hZ (genMat ε g *ᵥ basisVec x) := by
  rw [eGA, inv_mul_cancel_right]

open Classical in
theorem coord_kap_E [Finite G] {e : G} (he : e ∈ (Q ⊔ zpowers t : Subgroup G)) {y : G}
    (hy : y ∈ Dsub t Q) : coord ψ (kap e y) = (if e ∈ Q then 0 else 1) • tauD t ψ y := by
  obtain ⟨w, h | h⟩ := hS.mem_E_iff.1 he
  · have heQ : e ∈ Q := h ▸ hS.rad.ψ_mem w
    simp only [heQ, ite_true, zero_smul]
    rw [Setup.kap_Q_left heQ hy, hS.rad.coord_one]
  · have heQ : e ∉ Q := fun h' => by
      apply hS.shape.not_mem
      have := Q.mul_mem h' (Q.inv_mem (hS.rad.ψ_mem w))
      rw [h, mul_inv_cancel_right] at this
      exact hS.rad.Q_le_L this
    simp only [heQ, ite_false, one_smul]
    rw [h, hS.kap_mul_left hZ hS.t_mem_D (hS.E_le_D (mem_sup_left
      (hS.rad.ψ_mem w))) hy, Setup.kap_Q_left (hS.rad.ψ_mem w) hy, mul_one, hS.kap_t_left hZ hy,
      hS.rad.coord_ψ]

open Classical in
@[expose] noncomputable def lamGA [Finite G] (g : Fin 6) (x : ℕ) : ZMod 2 :=
  if hS.eGA hZ g x ∈ Q then 0 else 1

theorem gam_eq [Finite G] (g : Fin 6) (x y : ℕ) :
    genMat ε g *ᵥ hS.gam hZ x y = hS.lamGA hZ g x • (genMat ε g *ᵥ basisVec y) +
      hS.lamGA hZ g y • (genMat ε g *ᵥ basisVec x) +
      ∑ i : Fin 6, ∑ j : Fin 6, ((genMat ε g *ᵥ basisVec x) i * (genMat ε g *ᵥ basisVec y) j) •
        hS.gam hZ i j := by
  set ua := genMat ε g *ᵥ basisVec x
  set ub := genMat ε g *ᵥ basisVec y
  have hea := hS.E_le_D (hS.eGA_mem_E hZ g x)
  have heb := hS.E_le_D (hS.eGA_mem_E hZ g y)
  have hda := hS.dV_mem hZ ua
  have hdb := hS.dV_mem hZ ub
  have hkQ := hS.kap_mem_Q hZ (hS.dB_mem hZ x) (hS.dB_mem hZ y)
  have hL : coord ψ (kap (p g * hS.dB hZ x * (p g)⁻¹) (p g * hS.dB hZ y * (p g)⁻¹)) =
      genMat ε g *ᵥ hS.gam hZ x y := by
    rw [kap_conj, ← hS.rad.ψ_coord hkQ, hS.rad.p_act, hS.rad.coord_ψ]
    rfl
  rw [← hL, hS.conj_dB_eq hZ, hS.conj_dB_eq hZ, hS.kap_mul_left hZ hea hda (mul_mem heb hdb),
    hS.kap_mul_right hZ hea heb hdb, hS.kap_mul_right hZ hda heb hdb]
  have q1 := hS.kap_mem_Q hZ hea heb
  have q2 := hS.kap_mem_Q hZ hea hdb
  have q3 := hS.kap_mem_Q hZ hda heb
  have q4 := hS.kap_mem_Q hZ hda hdb
  rw [hS.rad.coord_mul (mul_mem q1 q2) (mul_mem q3 q4), hS.rad.coord_mul q1 q2,
    hS.rad.coord_mul q3 q4]
  have h1 : coord ψ (kap (hS.eGA hZ g x) (hS.eGA hZ g y)) = 0 := by
    rw [kap_eq_one_iff.2 (hS.E_comm (hS.eGA_mem_E hZ g x) (hS.eGA_mem_E hZ g y)),
      hS.rad.coord_one]
  have h2 : coord ψ (kap (hS.eGA hZ g x) (hS.dV hZ ub)) = hS.lamGA hZ g x • ub := by
    rw [hS.coord_kap_E hZ (hS.eGA_mem_E hZ g x) hdb, hS.tauD_dV hZ]
    by_cases h : hS.eGA hZ g x ∈ Q <;> simp [lamGA, h]
  have h3 : coord ψ (kap (hS.dV hZ ua) (hS.eGA hZ g y)) = hS.lamGA hZ g y • ua := by
    rw [hS.kap_symm hZ heb hda, hS.coord_kap_E hZ (hS.eGA_mem_E hZ g y) hda, hS.tauD_dV hZ]
    by_cases h : hS.eGA hZ g y ∈ Q <;> simp [lamGA, h]
  rw [h1, h2, h3, hS.coord_kap_dV hZ, zero_add, add_assoc]
  rfl

theorem gam_symm [Finite G] (x y : ℕ) : hS.gam hZ y x = hS.gam hZ x y := by
  rw [gam, gam, hS.kap_symm hZ (hS.dB_mem hZ x) (hS.dB_mem hZ y)]

theorem gam_self [Finite G] (x : ℕ) : hS.gam hZ x x = 0 := by
  rw [gam, kap_self, hS.rad.coord_one]

omit hS hZ in
theorem mulVec_basisVec (M : Mat6) (b : Fin 6) : M *ᵥ basisVec b = fun c => M c b := by
  rw [basisVec, toVec_two_pow', mulVec_single_one]
  rfl

theorem exists_mu [Finite G] :
    ∃ μ : V6, ∀ x y : Fin 6, hS.gam hZ x y = μ y • basisVec x + μ x • basisVec y := by
  obtain ⟨μ, hμ⟩ := exists_mu_of_gamma ε (fun c => Matrix.of fun a b => hS.gam hZ a b c)
    (Matrix.of fun g a => hS.lamGA hZ g a)
    (fun c => by
      ext a b
      simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.zero_apply]
      rw [hS.gam_symm hZ b a, CharTwo.add_self_eq_zero])
    (fun c a => by simp only [Matrix.of_apply]; rw [hS.gam_self hZ, Pi.zero_apply])
    (fun g c => by
      ext a b
      have h := congrFun (hS.gam_eq hZ g a b) c
      simp only [mulVec_basisVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
        at h
      have hS2 : ((genMat ε g)ᵀ * (Matrix.of fun (a b : Fin 6) => hS.gam hZ a b c : Mat6) *
          genMat ε g) a b =
          ∑ i : Fin 6, ∑ j : Fin 6, genMat ε g i a * genMat ε g j b * hS.gam hZ i j c := by
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      have hS1 : ((∑ d : Fin 6, genMat ε g c d •
          (Matrix.of fun (a b : Fin 6) => hS.gam hZ a b d : Mat6)) : Mat6) a b =
          (genMat ε g *ᵥ hS.gam hZ a b) c := by
        simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mulVec,
          dotProduct]
      simp only [Matrix.add_apply, Matrix.zero_apply, hS1, hS2, outerM6, Matrix.of_apply, h]
      have h2 : ∀ u v w : ZMod 2, u + v + w + w + (u + v) = 0 := by decide
      have := h2 (hS.lamGA hZ g a * genMat ε g c b) (hS.lamGA hZ g b * genMat ε g c a)
        (∑ i : Fin 6, ∑ j : Fin 6, genMat ε g i a * genMat ε g j b * hS.gam hZ i j c)
      convert this using 2
      ring)
  refine ⟨μ, fun x y => ?_⟩
  ext c
  have := hμ c x y
  simp only [Matrix.of_apply] at this
  rw [this, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, basisVec, basisVec, toVec_two_pow',
    toVec_two_pow', smul_eq_mul, smul_eq_mul]
  by_cases hx : x = c <;> by_cases hy : y = c <;> simp [hx, hy, eq_comm]

end Setup

end CFSG.EvenSmallLie.OmegaEight.Stage1
