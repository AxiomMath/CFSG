module


public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59C2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL59C4

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal

variable {G : Type} [Group G] {t s lam rho u : G} {b : Fin 3 → Fin 2 → G}

theorem fzl59c_commute_z_s (hg : Fz59Grid t s lam rho b) (i : Fin 3) : Commute (b i 0 ^ 2) s := by
  rw [hg.s_eq]
  exact ((fzl59c_commute_z hg i 0 1).mul_right (fzl59c_commute_z hg i 1 1)).mul_right
    (fzl59c_commute_z hg i 2 1)

theorem fzl59c_commute_z_t (hg : Fz59Grid t s lam rho b) (i : Fin 3) : Commute (b i 0 ^ 2) t := by
  rw [hg.t_eq]
  exact ((fzl59c_commute_z hg i 0 0).mul_right (fzl59c_commute_z hg i 1 0)).mul_right
    (fzl59c_commute_z hg i 2 0)

theorem fzl59c_Z_comm_of {Z : Subgroup G} {z₀ z₁ y : G} (hZ : Z = closure {z₀, z₁})
    (h₀ : z₀ * y = y * z₀) (h₁ : z₁ * y = y * z₁) : ∀ z ∈ Z, z * y = y * z := by
  intro z hz
  have h : Z ≤ centralizer ({y} : Set G) := by
    rw [hZ, closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact mem_centralizer_singleton_iff.mpr h₀
    · exact mem_centralizer_singleton_iff.mpr h₁
  exact mem_centralizer_singleton_iff.mp (h hz)

theorem fzl59c_Z_comm_b {Z : Subgroup G} (hg : Fz59Grid t s lam rho b)
    (hZ : Z = closure {b 0 0 ^ 2, b 1 0 ^ 2}) (i : Fin 3) (k : Fin 2) :
    ∀ z ∈ Z, z * b i k = b i k * z :=
  fzl59c_Z_comm_of hZ (fzl59c_commute_z hg 0 i k).eq (fzl59c_commute_z hg 1 i k).eq

theorem fzl59c_Z_comm_s {Z : Subgroup G} (hg : Fz59Grid t s lam rho b)
    (hZ : Z = closure {b 0 0 ^ 2, b 1 0 ^ 2}) : ∀ z ∈ Z, z * s = s * z :=
  fzl59c_Z_comm_of hZ (fzl59c_commute_z_s hg 0).eq (fzl59c_commute_z_s hg 1).eq

theorem fzl59c_Z_comm_t {Z : Subgroup G} (hg : Fz59Grid t s lam rho b)
    (hZ : Z = closure {b 0 0 ^ 2, b 1 0 ^ 2}) : ∀ z ∈ Z, z * t = t * z :=
  fzl59c_Z_comm_of hZ (fzl59c_commute_z_t hg 0).eq (fzl59c_commute_z_t hg 1).eq

theorem fzl59c_cent_B_of {Z : Subgroup G} {s y : G} (hZ : ∀ z ∈ Z, z * y = y * z)
    (hs : s * y = y * s) : ∀ x ∈ Z ⊔ zpowers s, y * x * y⁻¹ = x := by
  intro x hx
  have h : Z ⊔ zpowers s ≤ centralizer ({y} : Set G) :=
    sup_le (fun z hz => mem_centralizer_singleton_iff.mpr (hZ z hz))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hs))
  have hxy : x * y = y * x := mem_centralizer_singleton_iff.mp (h hx)
  rw [mul_inv_eq_iff_eq_mul]
  exact hxy.symm

theorem fzl59c_abs {Z : Subgroup G} (hg : Fz59Grid t s lam rho b)
    (hZ : Z = closure {b 0 0 ^ 2, b 1 0 ^ 2}) (hZe : CFSG.Open.IsElemAbelian 2 Z)
    (hZc : Nat.card ↥Z = 4) : fzl59c_Abs Z s t where
  Z_comm := fun z hz z' hz' => by
    haveI := hZe.1
    exact setLike_mul_comm hz hz'
  Z_sq := hZe.2
  card_Z := hZc
  s_sq := fzl59c_s_sq hg
  t_sq := fzl59c_t_sq hg
  s_comm := fun z hz => (fzl59c_Z_comm_s hg hZ z hz).symm
  t_comm := fun z hz => (fzl59c_Z_comm_t hg hZ z hz).symm
  st_comm := fzl59c_ts_comm hg
  s_not := by
    intro hs
    have h1 : b 0 0 * s = s * b 0 0 := (fzl59c_Z_comm_b hg hZ 0 0 s hs).symm
    have h2 : b 0 0 * s * (b 0 0)⁻¹ = s := by
      rw [h1]
      group
    rw [fzl59c_p_s hg 0] at h2
    have h3 : b 0 0 ^ 2 = 1 := by
      calc b 0 0 ^ 2 = s⁻¹ * (s * b 0 0 ^ 2) := by group
        _ = s⁻¹ * s := by rw [h2]
        _ = 1 := by group
    exact (hg.quat 0).2.2.2 h3
  t_not := by
    intro ht
    have hq : ∀ x ∈ Z ⊔ zpowers s, b 0 1 * x * (b 0 1)⁻¹ = x := by
      refine fzl59c_cent_B_of (fun z hz => fzl59c_Z_comm_b hg hZ 0 1 z hz) ?_
      have h := fzl59c_q_s hg 0
      rw [mul_inv_eq_iff_eq_mul] at h
      exact h.symm
    have h2 := hq t ht
    rw [fzl59c_q_t hg 0] at h2
    have h3 : b 0 0 ^ 2 = 1 := by
      calc b 0 0 ^ 2 = t⁻¹ * (t * b 0 0 ^ 2) := by group
        _ = t⁻¹ * t := by rw [h2]
        _ = 1 := by group
    exact (hg.quat 0).2.2.2 h3

end CFSG.OddStandard.SmallF3.FritzII
