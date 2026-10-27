module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59C3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59C4


public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal

variable {G : Type} [Group G] {t s lam rho u : G} {b : Fin 3 → Fin 2 → G}

theorem fzl59c_lam_b1 (hg : Fz59Grid t s lam rho b) (k : Fin 2) :
    lam * b 1 k * lam⁻¹ = b 0 k := by
  have h2 : lam * lam = 1 := by
    rw [← sq]
    exact hg.lam_sq
  calc lam * b 1 k * lam⁻¹ = lam * (lam * b 0 k * lam⁻¹) * lam⁻¹ := by rw [hg.lam_01 k]
    _ = (lam * lam) * b 0 k * (lam * lam)⁻¹ := by group
    _ = b 0 k := by
      rw [h2]
      simp

theorem fzl59c_lam_z0 (hg : Fz59Grid t s lam rho b) : lam * b 0 0 ^ 2 * lam⁻¹ = b 1 0 ^ 2 := by
  rw [← conj_pow, hg.lam_01]

theorem fzl59c_lam_z1 (hg : Fz59Grid t s lam rho b) : lam * b 1 0 ^ 2 * lam⁻¹ = b 0 0 ^ 2 := by
  rw [← conj_pow, fzl59c_lam_b1 hg]

theorem fzl59c_lam_s (hg : Fz59Grid t s lam rho b) : lam * s * lam⁻¹ = s := by
  calc lam * s * lam⁻¹
      = (lam * b 0 1 * lam⁻¹) * (lam * b 1 1 * lam⁻¹) * (lam * b 2 1 * lam⁻¹) := by
        rw [hg.s_eq]
        group
    _ = b 1 1 * b 0 1 * b 2 1 := by rw [hg.lam_01 1, fzl59c_lam_b1 hg 1, hg.lam_2 1]
    _ = s := by rw [hg.s_eq, ← (hg.comm 0 1 (by decide) 1 1).eq]

theorem fzl59c_lam_t (hg : Fz59Grid t s lam rho b) : lam * t * lam⁻¹ = t := by
  calc lam * t * lam⁻¹
      = (lam * b 0 0 * lam⁻¹) * (lam * b 1 0 * lam⁻¹) * (lam * b 2 0 * lam⁻¹) := by
        rw [hg.t_eq]
        group
    _ = b 1 0 * b 0 0 * b 2 0 := by rw [hg.lam_01 0, fzl59c_lam_b1 hg 0, hg.lam_2 0]
    _ = t := by rw [hg.t_eq, ← (hg.comm 0 1 (by decide) 0 0).eq]

theorem fzl59c_u_z_good (hg : Fz59Grid t s lam rho b) (hu : Fz59UGood t s lam rho u b)
    (i : Fin 3) : u * b i 0 ^ 2 * u⁻¹ = b i 0 ^ 2 := by
  rw [← conj_pow, hu.b0 i]
  have hc : Commute (b i 0 * b i 1) (b (i - 1) 0 ^ 2) :=
    ((fzl59c_commute_z hg (i - 1) i 0).symm).mul_left ((fzl59c_commute_z hg (i - 1) i 1).symm)
  rw [hc.mul_pow, ← (hg.quat i).mul_left.2.1, fzl59c_sq_sq (hg.quat (i - 1)), mul_one]

theorem fzl59c_u_z_bad (hg : Fz59Grid t s lam rho b) (hu : Fz59UBad t s lam rho u b)
    (i : Fin 3) : u * b i 0 ^ 2 * u⁻¹ = b i 0 ^ 2 := by
  rw [← conj_pow, hu.b0 i, ← (hg.quat i).mul_left.2.1]

theorem fzl59c_u_z (hg : Fz59Grid t s lam rho b)
    (hu : Fz59UGood t s lam rho u b ∨ Fz59UBad t s lam rho u b) (i : Fin 3) :
    u * b i 0 ^ 2 * u⁻¹ = b i 0 ^ 2 :=
  hu.elim (fun h => fzl59c_u_z_good hg h i) (fun h => fzl59c_u_z_bad hg h i)

theorem fzl59c_u_sq (hu : Fz59UGood t s lam rho u b ∨ Fz59UBad t s lam rho u b) : u ^ 2 = 1 :=
  hu.elim (fun h => h.sq) (fun h => h.sq)

theorem fzl59c_u_t (hu : Fz59UGood t s lam rho u b ∨ Fz59UBad t s lam rho u b) :
    u * t * u⁻¹ = t * s :=
  hu.elim (fun h => h.t_conj) (fun h => h.t_conj)

theorem fzl59c_u_s (hg : Fz59Grid t s lam rho b)
    (hu : Fz59UGood t s lam rho u b ∨ Fz59UBad t s lam rho u b) : u * s * u⁻¹ = s := by
  have hb1 : ∀ i, u * b i 1 * u⁻¹ = (b i 1)⁻¹ := hu.elim (fun h => h.b1) (fun h => h.b1)
  have c01 : Commute (b 0 1) (b 1 1) := hg.comm 0 1 (by decide) 1 1
  have c02 : Commute (b 0 1) (b 2 1) := hg.comm 0 2 (by decide) 1 1
  have c12 : Commute (b 1 1) (b 2 1) := hg.comm 1 2 (by decide) 1 1
  have hs2 : s * s = 1 := by
    rw [← sq]
    exact fzl59c_s_sq hg
  have e : u * s * u⁻¹ = (u * b 0 1 * u⁻¹) * (u * b 1 1 * u⁻¹) * (u * b 2 1 * u⁻¹) := by
    rw [hg.s_eq]
    group
  have hinv : s⁻¹ = (b 0 1)⁻¹ * (b 1 1)⁻¹ * (b 2 1)⁻¹ := by
    rw [hg.s_eq, (c02.mul_left c12).mul_inv, c01.mul_inv]
  rw [e, hb1 0, hb1 1, hb1 2, ← hinv]
  exact inv_eq_of_mul_eq_one_right hs2

theorem fzl59c_z_mem {Z : Subgroup G} (hg : Fz59Grid t s lam rho b)
    (hZ : Z = closure {b 0 0 ^ 2, b 1 0 ^ 2}) (i : Fin 3) : b i 0 ^ 2 ∈ Z := by
  have h0 : b 0 0 ^ 2 ∈ Z := by
    rw [hZ]
    exact subset_closure (Set.mem_insert _ _)
  have h1 : b 1 0 ^ 2 ∈ Z := by
    rw [hZ]
    exact subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  match i with
  | 0 => exact h0
  | 1 => exact h1
  | 2 =>
    rw [hg.sq_eq]
    exact Z.mul_mem h0 h1

theorem fzl59c_conj_Z_of {Z : Subgroup G} {z₀ z₁ g : G} (hZ : Z = closure {z₀, z₁})
    (h₀ : g * z₀ * g⁻¹ ∈ Z) (h₁ : g * z₁ * g⁻¹ ∈ Z) : ∀ z ∈ Z, g * z * g⁻¹ ∈ Z := by
  intro z hz
  have hz' : z ∈ closure {z₀, z₁} := by rwa [hZ] at hz
  refine fzl59c_conj_closure (S := {z₀, z₁}) (F := Z) (fun x hx => ?_) z hz'
  rcases hx with rfl | rfl
  · exact h₀
  · exact h₁

theorem fzl59c_gen_p {Z : Subgroup G} (hg : Fz59Grid t s lam rho b)
    (hZ : Z = closure {b 0 0 ^ 2, b 1 0 ^ 2}) (i : Fin 3) : fzl59c_Gen Z s t (b i 0) := by
  have hzm := fzl59c_z_mem hg hZ
  refine ⟨hzm i, ?_, ⟨b i 0 ^ 2, hzm i, fzl59c_p_s hg i⟩,
    ⟨1, one_mem _, by rw [fzl59c_p_t hg i, mul_one]⟩⟩
  refine fzl59c_conj_Z_of hZ ?_ ?_
  · rw [((fzl59c_commute_z hg 0 i 0).symm).mul_inv_cancel]
    exact hzm 0
  · rw [((fzl59c_commute_z hg 1 i 0).symm).mul_inv_cancel]
    exact hzm 1

theorem fzl59c_gen_q {Z : Subgroup G} (hg : Fz59Grid t s lam rho b)
    (hZ : Z = closure {b 0 0 ^ 2, b 1 0 ^ 2}) (i : Fin 3) : fzl59c_Gen Z s t (b i 1) := by
  have hzm := fzl59c_z_mem hg hZ
  refine ⟨?_, ?_, ⟨1, one_mem _, by rw [fzl59c_q_s hg i, mul_one]⟩,
    ⟨b i 0 ^ 2, Subgroup.mem_sup_left (hzm i), fzl59c_q_t hg i⟩⟩
  · rw [(hg.quat i).2.1]
    exact hzm i
  · refine fzl59c_conj_Z_of hZ ?_ ?_
    · rw [((fzl59c_commute_z hg 0 i 1).symm).mul_inv_cancel]
      exact hzm 0
    · rw [((fzl59c_commute_z hg 1 i 1).symm).mul_inv_cancel]
      exact hzm 1

theorem fzl59c_gen_lam {Z : Subgroup G} (hg : Fz59Grid t s lam rho b)
    (hZ : Z = closure {b 0 0 ^ 2, b 1 0 ^ 2}) : fzl59c_Gen Z s t lam := by
  have hzm := fzl59c_z_mem hg hZ
  refine ⟨by rw [hg.lam_sq]; exact one_mem _, ?_, ⟨1, one_mem _, by rw [fzl59c_lam_s hg, mul_one]⟩,
    ⟨1, one_mem _, by rw [fzl59c_lam_t hg, mul_one]⟩⟩
  refine fzl59c_conj_Z_of hZ ?_ ?_
  · rw [fzl59c_lam_z0 hg]
    exact hzm 1
  · rw [fzl59c_lam_z1 hg]
    exact hzm 0

theorem fzl59c_gen_u {Z : Subgroup G} (hg : Fz59Grid t s lam rho b)
    (hZ : Z = closure {b 0 0 ^ 2, b 1 0 ^ 2})
    (hu : Fz59UGood t s lam rho u b ∨ Fz59UBad t s lam rho u b) : fzl59c_Gen Z s t u := by
  have hzm := fzl59c_z_mem hg hZ
  refine ⟨by rw [fzl59c_u_sq hu]; exact one_mem _, ?_,
    ⟨1, one_mem _, by rw [fzl59c_u_s hg hu, mul_one]⟩,
    ⟨s, Subgroup.mem_sup_right (mem_zpowers s), fzl59c_u_t hu⟩⟩
  refine fzl59c_conj_Z_of hZ ?_ ?_
  · rw [fzl59c_u_z hg hu 0]
    exact hzm 0
  · rw [fzl59c_u_z hg hu 1]
    exact hzm 1

end CFSG.OddStandard.SmallF3.FritzII
