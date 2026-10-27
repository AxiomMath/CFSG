module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GPData
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Burnside
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3K0)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem a10_K_data (hS : Setting G) (hX : A10Facts) (hc : PointConfig IsA10Type G 5 P M x J)
    (hP : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G)) :
    ∃ N D : Subgroup G, A10KData (M ⊓ Subgroup.centralizer ({x} : Set G)) N D ∧
      M ⊓ Subgroup.centralizer ({x} : Set G) ⊓ u3K0 5 x J ≤ N ⊔ D := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hpd := a10_pdata hX hc hP
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  have hPW : (P : Subgroup G) ≤ M ⊓ Subgroup.centralizer ({x} : Set G) := le_inf hPM hP
  obtain ⟨N₀, -, hN₀C, hN₀cop, hK⟩ :=
    Generic49U3.u3_K0_pComplement_core hc hP hpd.D_cyc hpd.x_mem hpd.x_ord
  refine ⟨(M ⊓ Subgroup.centralizer ({x} : Set G)) ⊓ N₀, (P : Subgroup G) ⊓ u3K0 5 x J,
    ⟨inf_le_left, inf_le_left.trans hPW, ?_, ?_, hpd.D_cyc⟩, ?_⟩
  · intro w hw n hn
    exact ⟨(M ⊓ Subgroup.centralizer ({x} : Set G)).mul_mem
      ((M ⊓ Subgroup.centralizer ({x} : Set G)).mul_mem hw hn.1)
      ((M ⊓ Subgroup.centralizer ({x} : Set G)).inv_mem hw), hN₀C w hw.2 n hn.2⟩
  · intro h5
    obtain ⟨n, hn⟩ := exists_prime_orderOf_dvd_card' (G := ↥((M ⊓ Subgroup.centralizer ({x} : Set G)) ⊓ N₀)) 5 h5
    have h1 := hN₀cop (n : G) n.2.2
    rw [Subgroup.orderOf_coe, hn] at h1
    exact absurd h1 (by norm_num)
  · intro k hk
    obtain ⟨n, hn, d, hd, rfl⟩ := hK k hk.2
    have hnW : n ∈ M ⊓ Subgroup.centralizer ({x} : Set G) := by
      have e : n = (n * d) * d⁻¹ := by simp
      rw [e]
      exact (M ⊓ Subgroup.centralizer ({x} : Set G)).mul_mem hk.1
        ((M ⊓ Subgroup.centralizer ({x} : Set G)).inv_mem (hPW hd.1))
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hnW, hn⟩) (Subgroup.mem_sup_right hd)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
