module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.FrameD

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

variable {G : Type} [Group G] [Finite G] {z : G} {ι : Perm (Fin 10) →* G}

theorem exists_conj_z_mul_a (hC : CentData z ι) (hx : IsConj z (ι τ₀))
    (hP2 : ¬ IsConj z (z * ι τ₀)) (hp : pairOrder (ι τ₀) (ι (swap 0 1)) = N10 2) :
    ∃ s : G, s ∈ centralizer ({z * ι τ₀} : Set G) ∧ s * s = 1 ∧
      s * z * s⁻¹ = z * ι (swap 0 1 * swap 2 3) := by
  classical
  obtain ⟨ιd, hCd, hιz, -, hN2⟩ := exists_frame_at_d hC hx hP2
  let sperm : Perm (Fin 10) := swap 0 2 * swap 1 3
  let s : G := ιd sperm
  have hsperm : sperm * sperm = 1 := by decide
  have hs2 : s * s = 1 := by
    change ιd sperm * ιd sperm = 1
    rw [← map_mul, hsperm, map_one]
  have hsignτ : Equiv.Perm.sign τ₀ = -1 := by
    rw [τ₀]
    exact Equiv.Perm.sign_swap (by decide)
  have hneτ : Equiv.Perm.sign τ₀ ≠ 1 := by rw [hsignτ]; decide
  have hιdτ : ιd τ₀ = ι τ₀ * (z * ι (swap 0 1)) := by
    have h := hN2 hp τ₀ (by decide) (by decide)
    rwa [if_neg hneτ] at h
  have hd_comm : ι (swap 0 1) * ι τ₀ = ι τ₀ * ι (swap 0 1) := by
    rw [← map_mul, ← map_mul]
    congr 1
    decide
  have hdd' : (swap 0 1 : Perm (Fin 10)) * swap 0 1 = 1 := by decide
  have hdd : ι (swap 0 1) * ι (swap 0 1) = 1 := by
    rw [← map_mul, hdd', map_one]
  have hdz : ι (swap 0 1) * z = z * ι (swap 0 1) := (hC.comm (swap 0 1)).symm
  have hzx2 : ι (swap 0 1) * ιd τ₀ = z * ι τ₀ := by
    rw [hιdτ]
    calc ι (swap 0 1) * (ι τ₀ * (z * ι (swap 0 1)))
        = (ι (swap 0 1) * ι τ₀) * (z * ι (swap 0 1)) := by group
      _ = (ι τ₀ * ι (swap 0 1)) * (z * ι (swap 0 1)) := by rw [hd_comm]
      _ = ι τ₀ * ((ι (swap 0 1) * z) * ι (swap 0 1)) := by group
      _ = ι τ₀ * ((z * ι (swap 0 1)) * ι (swap 0 1)) := by rw [hdz]
      _ = ι τ₀ * (z * (ι (swap 0 1) * ι (swap 0 1))) := by group
      _ = ι τ₀ * z := by rw [hdd, mul_one]
      _ = z * ι τ₀ := (hC.comm τ₀).symm
  have hcomm23 : ι (swap 2 3) * ι (swap 0 1) = ι (swap 0 1) * ι (swap 2 3) := by
    rw [← map_mul, ← map_mul]
    congr 1
    decide
  have hsd : s * ι (swap 0 1) = ι (swap 0 1) * s := (hCd.comm sperm).symm
  have hst : s * ιd τ₀ = ιd τ₀ * s := by
    change ιd sperm * ιd τ₀ = ιd τ₀ * ιd sperm
    rw [← map_mul, ← map_mul]
    congr 1
    decide
  have hsx : s * (ι (swap 0 1) * ιd τ₀) = (ι (swap 0 1) * ιd τ₀) * s := by
    calc s * (ι (swap 0 1) * ιd τ₀)
        = (s * ι (swap 0 1)) * ιd τ₀ := by group
      _ = (ι (swap 0 1) * s) * ιd τ₀ := by rw [hsd]
      _ = ι (swap 0 1) * (s * ιd τ₀) := by group
      _ = ι (swap 0 1) * (ιd τ₀ * s) := by rw [hst]
      _ = (ι (swap 0 1) * ιd τ₀) * s := by group
  have hsconj : s * z * s⁻¹ = ιd (swap 2 3) := by
    have hσ : sperm * swap 0 1 * sperm⁻¹ = (swap 2 3 : Perm (Fin 10)) := by decide
    change ιd sperm * z * (ιd sperm)⁻¹ = ιd (swap 2 3)
    rw [← hιz, ← map_mul, ← map_inv, ← map_mul, hσ]
  have hsign23 : Equiv.Perm.sign (swap 2 3 : Perm (Fin 10)) = -1 :=
    Equiv.Perm.sign_swap (by decide)
  have hne23 : Equiv.Perm.sign (swap 2 3 : Perm (Fin 10)) ≠ 1 := by
    rw [hsign23]; decide
  have hιd_swap23 : ιd (swap 2 3 : Perm (Fin 10)) =
      ι (swap 2 3 : Perm (Fin 10)) * (z * ι (swap 0 1)) := by
    have h := hN2 hp (swap 2 3 : Perm (Fin 10)) (by decide) (by decide)
    rwa [if_neg hne23] at h
  have hfinal : ι (swap 2 3) * (z * ι (swap 0 1)) = z * ι (swap 0 1 * swap 2 3) := by
    rw [map_mul]
    calc ι (swap 2 3) * (z * ι (swap 0 1))
        = (ι (swap 2 3) * z) * ι (swap 0 1) := by group
      _ = (z * ι (swap 2 3)) * ι (swap 0 1) := by rw [(hC.comm (swap 2 3)).symm]
      _ = z * (ι (swap 2 3) * ι (swap 0 1)) := by group
      _ = z * (ι (swap 0 1) * ι (swap 2 3)) := by rw [hcomm23]
  refine ⟨s, ?_, hs2, ?_⟩
  · rw [mem_centralizer_singleton_iff, ← hzx2]
    exact hsx
  · rw [hsconj, hιd_swap23]
    exact hfinal

end CFSG.OddStandard.AltStdSec.SwapPartner
