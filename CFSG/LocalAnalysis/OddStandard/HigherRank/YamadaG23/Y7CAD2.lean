module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAD2a
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAN24Def

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {Γ M : Type} [Group Γ] [Finite Γ] [Group M] [Finite M] {ρ : Γ →* MulAut M}
  {t : Γ} {J Q P M6 M7 : Subgroup Γ}

theorem y7c_D2_false (hN24 : Nar24) (c : K7Abs ρ t J Q P M6 M7) {N : Subgroup Γ}
    (hN : N = Subgroup.normalClosure (J : Set Γ)) (hq : CFSG.IsQuasisimple ↥N)
    (hker : ∀ n m : Γ, ρ n = 1 → m ∈ N → n * m = m * n)
    (hZ : ∀ z ∈ N, (∀ n ∈ N, z * n = n * z) → ρ z = 1) : False := by
  obtain ⟨hs, hna, h64, -⟩ := y7c_D2_simple c hN hq hker hZ ρ (fun _ => Iff.rfl)
  have hNnormal : N.Normal := by rw [hN]; infer_instance
  have hJN : J ≤ N := by rw [hN]; exact Subgroup.le_normalClosure
  have hinjJ : Function.Injective (ρ.subgroupMap J) := by
    rw [← MonoidHom.ker_eq_bot_iff (ρ.subgroupMap J), Subgroup.ker_subgroupMap]
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, Subgroup.mem_bot]
    exact ⟨fun hfz => Subtype.ext (by simpa using c.ρ_inj (x : Γ) x.2 hfz),
      fun hx => by rw [hx]; simp⟩
  let eJ : ↥J ≃* ↥(J.map ρ) :=
    MulEquiv.ofBijective (ρ.subgroupMap J) ⟨hinjJ, ρ.subgroupMap_surjective J⟩
  refine hN24 M c.M_E (N.map ρ) (J.map ρ) (ρ t) hs hna h64 (Subgroup.map_mono hJN)
    ⟨eJ.symm.trans c.J_iso.some⟩ ?_ ?_ ?_ ?_ ?_
  ·
    intro x hx hx7 hx1 m hm
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hx
    have hj7 : j ^ 7 = 1 :=
      c.ρ_inj _ (J.pow_mem hj 7) (by rw [map_pow]; exact hx7)
    have hj1 : j ≠ 1 := fun h => hx1 (by rw [h, map_one])
    exact c.J_fpf j hj hj7 hj1 m hm
  ·
    rw [← map_pow, c.t_sq, map_one]
  ·
    intro d hd
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hd
    rw [← map_mul, ← map_mul, c.J_cent j hj]
  ·
    intro h hh
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hh
    exact Subgroup.mem_map.mpr
      ⟨t * n * t⁻¹, hNnormal.conj_mem n hn t, by simp only [map_mul, map_inv]⟩
  ·
    intro x hxH hx d hd
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hxH
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hd
    have hρu : ρ (t * n * t⁻¹ * n⁻¹) = 1 := by
      have h1 : ρ t * ρ n = ρ n * ρ t := hx.symm
      simp only [map_mul, map_inv]
      calc ρ t * ρ n * (ρ t)⁻¹ * (ρ n)⁻¹ = (ρ n * ρ t) * (ρ t)⁻¹ * (ρ n)⁻¹ := by rw [h1]
        _ = 1 := by group
    have hmemJ : ∀ j' ∈ J, (n * j' * n⁻¹) * t = t * (n * j' * n⁻¹) := by
      intro j' hj'
      have hj'N : j' ∈ N := hJN hj'
      have htj' : t * j' * t⁻¹ = j' := by
        rw [← c.J_cent j' hj', mul_assoc, mul_inv_cancel, mul_one]
      have hcomm := hker (t * n * t⁻¹ * n⁻¹) (n * j' * n⁻¹) hρu
        (hNnormal.conj_mem j' hj'N n)
      have hkey : t * (n * j' * n⁻¹) * t⁻¹ = n * j' * n⁻¹ := by
        have hstep : t * (n * j' * n⁻¹) * t⁻¹
            = (t * n * t⁻¹) * (t * j' * t⁻¹) * (t * n * t⁻¹)⁻¹ := by group
        rw [hstep, htj']
        have htn : t * n * t⁻¹ = (t * n * t⁻¹ * n⁻¹) * n := by group
        rw [htn]
        have hstep2 : ((t * n * t⁻¹ * n⁻¹) * n) * j' * ((t * n * t⁻¹ * n⁻¹) * n)⁻¹
            = (t * n * t⁻¹ * n⁻¹) * (n * j' * n⁻¹) * (t * n * t⁻¹ * n⁻¹)⁻¹ := by
          group
        rw [hstep2, hcomm]
        group
      have hAt : t * (n * j' * n⁻¹) = (n * j' * n⁻¹) * t := by
        calc t * (n * j' * n⁻¹) = t * (n * j' * n⁻¹) * t⁻¹ * t := by group
          _ = (n * j' * n⁻¹) * t := by rw [hkey]
      exact hAt.symm
    exact Subgroup.mem_map.mpr
      ⟨n * j * n⁻¹, y7c_conjSub_J_le c n hmemJ (y7c_mul_mem_conjSub hj),
        by simp only [map_mul, map_inv]⟩

end CFSG.OddStandard.HigherRank.YamadaG23
