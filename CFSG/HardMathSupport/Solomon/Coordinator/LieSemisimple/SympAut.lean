module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympInner
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympField
import CFSG.RankThree.PartOne.KC.SymplecticInnerPlane

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

variable {r : ℕ} {K : Type} [Field K]

theorem exists_proj_eq_pow_eq_one_sp [Finite K] (hr : 1 ≤ r) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {a : StatedProj (StatedSp r K)} (ha : a ^ p = 1) :
    ∃ x : StatedSp r K, SymplecticFlag.proj r K x = a ∧ x ^ p = 1 := by
  obtain ⟨x₀, rfl⟩ := SymplecticHigher.proj_surjective (r := r) (K := K) a
  have hker : SymplecticFlag.proj r K (x₀ ^ p) = 1 := by rw [map_pow]; exact ha
  have hsq : (x₀ ^ p) ^ 2 = 1 := CFSG.RankThree.PartOne.sq_eq_one_of_proj_eq_one hr hker
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
  refine ⟨x₀ ^ (p + 1), ?_, ?_⟩
  · rw [map_pow, pow_succ, ha, one_mul]
  · calc (x₀ ^ (p + 1)) ^ p = (x₀ ^ p) ^ (p + 1) := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = ((x₀ ^ p) ^ 2) ^ (m + 1) := by
          rw [← pow_mul (x₀ ^ p) 2 (m + 1)]
          congr 1
          omega
      _ = 1 := by rw [hsq, one_pow]

private theorem center_eq_bot_of_simple_perfect {T : Type*} [Group T] (hs : IsSimpleGroup T)
    (hperf : Group.IsPerfect T) : Subgroup.center T = ⊥ := by
  have := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
  · exact h
  · exfalso
    have hcomm : commutator T = ⊥ := by
      rw [commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro g _
      rw [Subgroup.mem_centralizer_iff]
      intro k _
      have : k ∈ Subgroup.center T := h ▸ Subgroup.mem_top k
      exact (Subgroup.mem_center_iff.mp this g).symm
    have htop : (⊤ : Subgroup T) = ⊥ := by rw [← hcomm]; exact hperf.commutator_eq_top.symm
    obtain ⟨a, b, hab⟩ := exists_pair_ne T
    have ha : a ∈ (⊥ : Subgroup T) := htop ▸ Subgroup.mem_top a
    have hb : b ∈ (⊥ : Subgroup T) := htop ▸ Subgroup.mem_top b
    rw [Subgroup.mem_bot] at ha hb
    exact hab (ha.trans hb.symm)

theorem perfectInLayer_projSp {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hr : 2 ≤ r) (hne : ¬(r = 2 ∧ ℓ ^ f = 2)) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (β : MulAut (StatedProj (StatedSp r K))) (hβ : β ^ p = 1) :
    PerfectInLayer β := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hℓ.ne_zero)
  have hO := CFSG.RankThree.PartOne.KCSpComm.spOuter (K := K) hℓ hf hr hK
  have hodd : Odd (orderOf β) :=
    (hp.odd_of_ne_two hp2).of_dvd_nat (orderOf_dvd_of_pow_eq_one hβ)
  have hE : β ∈ spSemilinearAutGroup r K :=
    CFSG.RankThree.PartOne.KCSpComm.mem_of_odd_orderOf_of_index_dvd_two _ hO.index_dvd hodd
  by_cases hD : β ∈ spLinearAutGroup r K
  ·
    have : (inner (StatedProj (StatedSp r K))).Normal := inner_normal _
    have hrel : (inner (StatedProj (StatedSp r K))).relIndex (spLinearAutGroup r K) ∣ 2 :=
      hO.relIndex_dvd.trans (Nat.gcd_dvd_left 2 _)
    have hinn := CFSG.RankThree.PartOne.KCSpComm.mem_of_pow_eq_one_of_relIndex_dvd_two hrel hp
      hp2 hD hβ
    obtain ⟨t, rfl⟩ := hinn
    obtain ⟨hsimple, hperf⟩ :=
      CFSG.RankThree.PartOne.KCSpComm.simple_perfect_statedProj (k := K) hr (by rwa [hK])
    have ht : t ^ p = 1 := by
      have hc : t ^ p ∈ Subgroup.center (StatedProj (StatedSp r K)) := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h1 := congrArg (fun φ : MulAut (StatedProj (StatedSp r K)) => φ g)
          (show MulAut.conj (t ^ p) = 1 by rw [map_pow]; exact hβ)
        simp only [MulAut.conj_apply, MulAut.one_apply] at h1
        calc g * t ^ p = t ^ p * g * (t ^ p)⁻¹ * t ^ p := by rw [h1]
          _ = t ^ p * g := by group
      rw [center_eq_bot_of_simple_perfect hsimple hperf, Subgroup.mem_bot] at hc
      exact hc
    obtain ⟨x, hx, hxp⟩ := exists_proj_eq_pow_eq_one_sp (by omega) hp hp2 ht
    rw [← hx]
    exact perfectInLayer_conj_sp hℓ hf hK (by omega) hp hp2 hpℓ x hxp
  ·
    have : Fact p.Prime := ⟨hp⟩
    have hne1 : β ≠ 1 := fun h => hD (h ▸ one_mem _)
    have hord : orderOf β = p := orderOf_eq_prime hβ hne1
    obtain ⟨-, σ, hσ, h, -, hβeq⟩ := hO.descent p hp β hE hD hord
    rw [hβeq]
    exact perfectInLayer_conj h _ (perfectInLayer_fieldAut_sp hr hp hp2 σ
      (by rw [← hσ]; exact pow_orderOf_eq_one σ))

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
