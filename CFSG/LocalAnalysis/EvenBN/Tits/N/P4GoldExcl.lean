module

public import CFSG.Goldschmidt.Steps.GoldType

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P4

open CFSG.Open CFSG.Goldschmidt Subgroup
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter)

section

theorem goldExcl_centralizes {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hK : goldschmidtSimpleType K) (T : Sylow 2 K)
    (hΩ : IsMulCommutative (Omega1 (T : Subgroup K))) :
    ∀ x ∈ (T : Subgroup K), ∀ u ∈ Omega1 (T : Subgroup K), x * u = u * x := by
  by_cases hTc : IsMulCommutative (T : Subgroup K)
  · obtain ⟨hsq, -⟩ := N11a K hK T hΩ
    have hsq' := hsq hTc
    have hΩT : Omega1 (T : Subgroup K) = (T : Subgroup K) := GoldType.omega1_eq_self hsq'
    intro x hx u hu
    rw [hΩT] at hu
    exact hTc.is_comm.comm ⟨x, hx⟩ ⟨u, hu⟩ |> fun h => congrArg Subtype.val h
  · obtain ⟨-, hnc⟩ := N11a K hK T hΩ
    obtain ⟨hω, -⟩ := N11c K (hnc hTc) T
    intro x hx u hu
    rw [hω] at hu
    exact ((mem_sylowCenter.1 hu).2 x hx)

theorem goldExcl_transitive {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hK : goldschmidtSimpleType K) (T : Sylow 2 K)
    (hΩ : IsMulCommutative (Omega1 (T : Subgroup K))) :
    ∀ x ∈ Omega1 (T : Subgroup K), ∀ y ∈ Omega1 (T : Subgroup K), x ≠ 1 → y ≠ 1 →
      ∃ n ∈ normalizer ((Omega1 (T : Subgroup K) : Subgroup K) : Set K), n⁻¹ * x * n = y :=
  (N11b K hK T hΩ).2

theorem goldExcl_odd {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hK : goldschmidtSimpleType K) (T : Sylow 2 K)
    (hΩ : IsMulCommutative (Omega1 (T : Subgroup K))) :
    Odd ((centralizer ((Omega1 (T : Subgroup K) : Subgroup K) : Set K)).relIndex
      (normalizer ((Omega1 (T : Subgroup K) : Subgroup K) : Set K))) := by
  set Ω : Subgroup K := Omega1 (T : Subgroup K) with hΩdef
  have hTC : (T : Subgroup K) ≤ centralizer (Ω : Set K) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (goldExcl_centralizes hK T hΩ x hx u hu).symm
  have hCN : centralizer (Ω : Set K) ≤ normalizer (Ω : Set K) := Subgroup.centralizer_le_normalizer _
  have hTN : (T : Subgroup K) ≤ normalizer (Ω : Set K) := hTC.trans hCN
  have h1 : (T : Subgroup K).relIndex (centralizer (Ω : Set K)) *
      (centralizer (Ω : Set K)).relIndex (normalizer (Ω : Set K)) =
      (T : Subgroup K).relIndex (normalizer (Ω : Set K)) :=
    Subgroup.relIndex_mul_relIndex _ _ _ hTC hCN
  have h2 : (T : Subgroup K).relIndex (normalizer (Ω : Set K)) * (normalizer (Ω : Set K)).index =
      (T : Subgroup K).index := Subgroup.relIndex_mul_index hTN
  have hodd : ¬ 2 ∣ (T : Subgroup K).index := Sylow.not_dvd_index T
  have h3 : (centralizer (Ω : Set K)).relIndex (normalizer (Ω : Set K)) ∣ (T : Subgroup K).index := by
    rw [← h2, ← h1]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_refl _) _) _
  rw [Nat.odd_iff]
  by_contra hne
  have h2d : 2 ∣ (centralizer (Ω : Set K)).relIndex (normalizer (Ω : Set K)) := by omega
  exact hodd (h2d.trans h3)

end

end CFSG.LocalAnalysis.EvenBN.Tits.N.P4
