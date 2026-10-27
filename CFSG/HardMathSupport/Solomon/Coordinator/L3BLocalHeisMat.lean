module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
  Matrix

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem l3b_not_commute {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {g : GL (Fin 3) K}
    (hcomm : g * cycThree * g⁻¹ * (g * diagTau hτ * g⁻¹) =
      (g * diagTau hτ * g⁻¹) * (g * cycThree * g⁻¹)) : False := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  set d' := g * diagTau hτ * g⁻¹ with hd'
  set c' := g * cycThree * g⁻¹ with hc'
  have hc'd : c' * d' * c'⁻¹ = d' := by
    rw [hcomm]; group
  have hcd : c' * d' * c'⁻¹ = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2) * d' := by
    have h1 := cycThree_pow_conj_diagTau hτ hτ0 1
    rw [pow_one, mul_one] at h1
    rw [hc', hd']
    calc g * cycThree * g⁻¹ * (g * diagTau hτ * g⁻¹) * (g * cycThree * g⁻¹)⁻¹ =
        g * (cycThree * diagTau hτ * cycThree⁻¹) * g⁻¹ := by group
      _ = g * (GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2) * diagTau hτ) * g⁻¹ := by
        rw [h1]
      _ = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2) * (g * diagTau hτ * g⁻¹) := by
        have := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar (Units.mk0 τ hτ0 ^ 2) g).eq
        calc g * (GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2) * diagTau hτ) * g⁻¹ =
            (g * GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2)) * diagTau hτ * g⁻¹ := by
              group
          _ = (GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2) * g) * diagTau hτ * g⁻¹ := by
              rw [← this]
          _ = _ := by group
  rw [hcd] at hc'd
  have h2 : GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0 ^ 2) = 1 := by
    have := congrArg (fun z => z * d'⁻¹) hc'd
    simpa using this
  have h3 : Units.mk0 τ hτ0 ^ 2 = 1 := by
    apply scalar_injective_three
    rw [h2, map_one]
  have h4 : τ ^ 2 = 1 := by
    have := congrArg Units.val h3
    simpa using this
  apply hτ1
  calc τ = τ ^ 3 / τ ^ 2 := by field_simp
    _ = 1 := by rw [hτ, h4, div_one]

theorem l3b_heis_pair {M : Type*} [Group M] (ι : M →* ProjGenLinGroup (Fin 3) K)
    (hι : Function.Injective ι)
    (hsurj : ∀ s ∈ slPi π 3 (p ^ f) K, ∃ m : M, ι m = ProjGenLinGroup.mk s)
    (hK : PiField π p f K) (hq : ModThree π (p ^ f)) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {g : GL (Fin 3) K} (hg : g ∈ glPi π 3 (p ^ f) K) {x₁ x₂ : M}
    (h₁ : ι x₁ = ProjGenLinGroup.mk (g * diagTau hτ * g⁻¹))
    (h₂ : ι x₂ = ProjGenLinGroup.mk (g * cycThree * g⁻¹)) :
    ∃ n₁ n₂ : M, x₁ * x₂ = x₂ * x₁ ∧ x₁ ^ 3 = 1 ∧ x₂ ^ 3 = 1 ∧ x₁ ≠ 1 ∧
      x₂ ∉ Subgroup.zpowers x₁ ∧ n₁ * x₁ * n₁⁻¹ = x₂⁻¹ ∧ n₁ * x₂ * n₁⁻¹ = x₁ ∧
      n₂ * x₁ * n₂⁻¹ = x₂⁻¹ * x₁⁻¹ ∧ n₂ * x₂ * n₂⁻¹ = x₁ * x₂ * x₁ := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have h3 := hK.three_ne_zero hq
  have hs := one_add_tau_add_sq hτ hτ1
  have hFS : fourierGL h3 hs ∈ slPi π 3 (p ^ f) K := fourierGL_mem_slPi hK hq hτ h3 hs
  have hTH : phaseGL hτ ∈ glPi π 3 (p ^ f) K := phaseGL_mem_glPi hK hq hτ
  have hgF : g * fourierGL h3 hs * g⁻¹ ∈ slPi π 3 (p ^ f) K := conj_mem_slPi hπ hg hFS
  have hgN : g * (phaseGL hτ * fourierGL h3 hs * (phaseGL hτ)⁻¹) * g⁻¹ ∈ slPi π 3 (p ^ f) K :=
    conj_mem_slPi hπ hg (conj_mem_slPi hπ hTH hFS)
  obtain ⟨n₁, hn₁⟩ := hsurj _ hgF
  obtain ⟨n₂, hn₂⟩ := hsurj _ hgN
  set mg := ProjGenLinGroup.mk g
  set md := ProjGenLinGroup.mk (diagTau hτ)
  set mc := ProjGenLinGroup.mk (cycThree : GL (Fin 3) K)
  set mF := ProjGenLinGroup.mk (fourierGL h3 hs)
  set mN := ProjGenLinGroup.mk (phaseGL hτ * fourierGL h3 hs * (phaseGL hτ)⁻¹)
  have hφ₁ : ι x₁ = mg * md * mg⁻¹ := by rw [h₁, map_mul, map_mul, map_inv]
  have hφ₂ : ι x₂ = mg * mc * mg⁻¹ := by rw [h₂, map_mul, map_mul, map_inv]
  have hφN₁ : ι n₁ = mg * mF * mg⁻¹ := by rw [hn₁, map_mul, map_mul, map_inv]
  have hφN₂ : ι n₂ = mg * mN * mg⁻¹ := by rw [hn₂, map_mul, map_mul, map_inv]
  have R1 : mF * md * mF⁻¹ = mc⁻¹ := mk_fourier_diagTau hτ h3 hs
  have R2 : mF * mc * mF⁻¹ = md := mk_fourier_cycThree hτ h3 hs
  have R5 : md * mc = mc * md := mk_diagTau_cycThree hτ
  have R6 : mN * md * mN⁻¹ = mc⁻¹ * md⁻¹ := mk_conjFourier_diagTau hτ h3 hs
  have R7 : mN * mc * mN⁻¹ = md * mc * md := mk_conjFourier_cycThree hτ h3 hs
  have hd3 : md ^ 3 = 1 := by rw [← map_pow, diagTau_pow_three hτ, map_one]
  have hc3 : mc ^ 3 = 1 := by rw [← map_pow, cycThree_pow_three, map_one]
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  refine ⟨n₁, n₂, hι (by
    rw [map_mul, map_mul, hφ₁, hφ₂]
    calc mg * md * mg⁻¹ * (mg * mc * mg⁻¹) = mg * (md * mc) * mg⁻¹ := by group
      _ = mg * (mc * md) * mg⁻¹ := by rw [R5]
      _ = mg * mc * mg⁻¹ * (mg * md * mg⁻¹) := by group),
    hι (by rw [map_pow, hφ₁, conj_pow, hd3, map_one]; group),
    hι (by rw [map_pow, hφ₂, conj_pow, hc3, map_one]; group), ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro h
    rw [h, map_one, eq_comm, mk_eq_one_iff_mem_statedScalars] at h₁
    refine l3b_not_commute hτ hτ1 (g := g) ?_
    exact (commute_of_mem_statedScalars h₁ _)
  ·
    intro h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
    have h4 : ProjGenLinGroup.mk (g * cycThree * g⁻¹) =
        ProjGenLinGroup.mk ((g * diagTau hτ * g⁻¹) ^ k) := by
      rw [← h₂, map_zpow, h₁, map_zpow]
    have h5 : (g * cycThree * g⁻¹)⁻¹ * (g * diagTau hτ * g⁻¹) ^ k ∈ StatedScalars (Fin 3) K := by
      rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_inv, h4, inv_mul_cancel]
    obtain ⟨s, hs⟩ := h5
    refine l3b_not_commute hτ hτ1 (g := g) ?_
    have hsc : (g * cycThree * g⁻¹) = (g * diagTau hτ * g⁻¹) ^ k *
        (GeneralLinearGroup.scalar (Fin 3) s)⁻¹ := by
      rw [hs]; group
    rw [hsc]
    have hs' : (GeneralLinearGroup.scalar (Fin 3) s)⁻¹ ∈ StatedScalars (Fin 3) K :=
      inv_mem ⟨s, rfl⟩
    have e1 := commute_of_mem_statedScalars hs' (g * diagTau hτ * g⁻¹)
    have e2 : (g * diagTau hτ * g⁻¹) ^ k * (g * diagTau hτ * g⁻¹) =
        (g * diagTau hτ * g⁻¹) * (g * diagTau hτ * g⁻¹) ^ k :=
      (Commute.zpow_left (Commute.refl _) k).eq
    calc (g * diagTau hτ * g⁻¹) ^ k * (GeneralLinearGroup.scalar (Fin 3) s)⁻¹ *
        (g * diagTau hτ * g⁻¹) =
        (g * diagTau hτ * g⁻¹) ^ k * ((GeneralLinearGroup.scalar (Fin 3) s)⁻¹ *
        (g * diagTau hτ * g⁻¹)) := by group
      _ = (g * diagTau hτ * g⁻¹) ^ k * ((g * diagTau hτ * g⁻¹) *
        (GeneralLinearGroup.scalar (Fin 3) s)⁻¹) := by rw [← e1]
      _ = (g * diagTau hτ * g⁻¹) * ((g * diagTau hτ * g⁻¹) ^ k *
        (GeneralLinearGroup.scalar (Fin 3) s)⁻¹) := by
        rw [← mul_assoc, e2, mul_assoc]
  · exact hι (by
      rw [map_mul, map_mul, map_inv, map_inv, hφN₁, hφ₁, hφ₂]
      calc mg * mF * mg⁻¹ * (mg * md * mg⁻¹) * (mg * mF * mg⁻¹)⁻¹ =
          mg * (mF * md * mF⁻¹) * mg⁻¹ := by group
        _ = (mg * mc * mg⁻¹)⁻¹ := by rw [R1]; group)
  · exact hι (by
      rw [map_mul, map_mul, map_inv, hφN₁, hφ₁, hφ₂]
      calc mg * mF * mg⁻¹ * (mg * mc * mg⁻¹) * (mg * mF * mg⁻¹)⁻¹ =
          mg * (mF * mc * mF⁻¹) * mg⁻¹ := by group
        _ = mg * md * mg⁻¹ := by rw [R2])
  · exact hι (by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_inv, hφN₂, hφ₁, hφ₂]
      calc mg * mN * mg⁻¹ * (mg * md * mg⁻¹) * (mg * mN * mg⁻¹)⁻¹ =
          mg * (mN * md * mN⁻¹) * mg⁻¹ := by group
        _ = (mg * mc * mg⁻¹)⁻¹ * (mg * md * mg⁻¹)⁻¹ := by rw [R6]; group)
  · exact hι (by
      rw [map_mul, map_mul, map_mul, map_mul, map_inv, hφN₂, hφ₁, hφ₂]
      calc mg * mN * mg⁻¹ * (mg * mc * mg⁻¹) * (mg * mN * mg⁻¹)⁻¹ =
          mg * (mN * mc * mN⁻¹) * mg⁻¹ := by group
        _ = mg * md * mg⁻¹ * (mg * mc * mg⁻¹) * (mg * md * mg⁻¹) := by rw [R7]; group)

end CFSG.HardMathSupport.Solomon.Coordinator
