module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwistConjData
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.FrameAlt
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSwapTable

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern CFSG.OddStandard.AltStdBal

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {z u : G}

structure SwapFrame (h : Setting G L 10) (d : Cyc L Q z) (ι : Perm (Fin 10) →* G) : Prop where
  cent : CentData z ι
  alt : (alternatingGroup (Fin 10)).map ι = L
  conj : IsConj z (ι τ₀)

theorem exists_swapFrame (h : Setting G L 10) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin 10)) {y : G} (hy : y ∈ centralizer ({z} : Set G))
    (hsw : (permOf h d e hy).IsSwap) (hc : IsConj z y) :
    ∃ ι : Perm (Fin 10) →* G, SwapFrame h d ι := by
  have hC₀ : CentData z (swapIotaHom h d T e) := centData_swapIotaHom h d T e
  have hσ2 : permOf h d e hy * permOf h d e hy = 1 := by
    obtain ⟨a, b, hab, hswap⟩ := hsw
    rw [hswap, Equiv.swap_mul_self]
  have hcases : y = swapIotaHom h d T e (permOf h d e hy) ∨
      y = z * swapIotaHom h d T e (permOf h d e hy) := by
    rcases eq_swapIota_or h d T e hy with h' | h'
    · left
      exact h'.trans (swapIotaHom_apply h d T e (permOf h d e hy)).symm
    · right
      exact h'.trans (congrArg (fun t : G => z * t)
        (swapIotaHom_apply h d T e (permOf h d e hy)).symm)
  have hy2 : y * y = 1 := by
    rcases hcases with h' | h'
    · rw [h', ← map_mul, hσ2, map_one]
    · rw [h']
      calc (z * swapIotaHom h d T e (permOf h d e hy)) *
              (z * swapIotaHom h d T e (permOf h d e hy))
          = z * (swapIotaHom h d T e (permOf h d e hy) * z) *
              swapIotaHom h d T e (permOf h d e hy) := by group
        _ = z * (z * swapIotaHom h d T e (permOf h d e hy)) *
              swapIotaHom h d T e (permOf h d e hy) := by
              rw [← hC₀.comm (permOf h d e hy)]
        _ = (z * z) * (swapIotaHom h d T e (permOf h d e hy) *
              swapIotaHom h d T e (permOf h d e hy)) := by group
        _ = 1 := by rw [hC₀.mul_self, one_mul, ← map_mul, hσ2, map_one]
  have hord : pairOrder z y = N10 1 := by
    rcases hcases with h' | h'
    · rw [h', pairOrder_z_ι hC₀ hσ2, card_cycleType_of_isSwap hsw]
    · rw [h', pairOrder_mul_right (hC₀.comm (permOf h d e hy)),
        pairOrder_z_ι hC₀ hσ2, card_cycleType_of_isSwap hsw]
  obtain ⟨ι₁, d', hC₁, hswap, hev⟩ := exists_frame_of_pairOrder hC₀ hy hy2 hord
  exact ⟨ι₁, hC₁,
    (map_alternatingGroup_eq_of_even hev).trans (map_alternatingGroup_swapIotaHom h d T e),
    by rw [hswap]; exact hc⟩

theorem swapFrame_cases {h : Setting G L 10} {d : Cyc L Q z} {ι : Perm (Fin 10) →* G}
    (F : SwapFrame h d ι) :
    pairOrder (ι τ₀) (ι (swap 0 1)) = N10 1 ∨ pairOrder (ι τ₀) (ι (swap 0 1)) = N10 2 := by
  obtain ⟨ι₁, ε, χ, D⟩ := exists_twistData F.cent F.conj
  have hpair := D.pair_one r₁' r₁'_mul_self
  rw [liftS8_r₁', card_cycleType_r₁'] at hpair
  by_cases he : ε r₁' = -1
  · right
    rw [if_pos he] at hpair
    exact hpair
  · left
    rw [if_neg he] at hpair
    exact hpair

end CFSG.OddStandard.AltStdSec.SwapPartner
