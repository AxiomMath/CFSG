module

public import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeTrialityDefs
import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeOrthModel
import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeOrthFlagLink
import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeOrthZ

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit QuadraticMap

theorem trialityFlagInput : TrialityFlagInput := by
  intro G _ _ hm J T hNJ hJ E₀ hEJ hE3 x hx y hy
  have hm' : CFSG.Assembly.LowTwoRank.StatedClassicalModel G .POmegaPlus 4 2 1 := hm
  obtain ⟨-, K, hKf, hKfin, hcard, ⟨e⟩⟩ := hm'
  have hK : Nat.card K = 2 := by simpa using hcard
  have : Fintype K := Fintype.ofFinite K
  have hchar : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
  have hn3 : 3 ≤ 4 := by norm_num
  have hK2 := eq_zero_or_one_of_card_two' hK
  obtain ⟨xP, hxP⟩ := exists_conj_borel_le hn3 e T J hNJ
  let Q : QuadraticForm K (Fin 4 ⊕ Fin 4 → K) := quadPlus 4 K
  let Θ := projEquivElementary K hK hn3
  let Ψ : G ≃* ↥(elementaryGroup Q) := e.trans Θ
  let Jl : Subgroup ((Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :=
    (J.map Ψ.toMonoidHom).map (elementaryGroup Q).subtype
  have hJlE : Jl ≤ elementaryGroup Q := by
    rintro _ ⟨g, -, rfl⟩
    exact g.2
  have hJlO : Jl ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    hJlE.trans (elementaryGroup_le_orthogonalGroup Q)
  have hJltop : ¬ elementaryGroup Q ≤ Jl := by
    intro hle
    apply hJ
    rw [eq_top_iff]
    intro g _
    obtain ⟨_, ⟨j, hj, rfl⟩, hjg⟩ := hle (Ψ g).2
    have : j = g := Ψ.injective (Subtype.ext hjg)
    rwa [← this]
  let e₀ : Fin 4 ⊕ Fin 4 → K := Pi.single (Sum.inl (0 : Fin 4)) 1
  have he₀mem : ∀ i : Fin 3, e₀ ∈ stdFlag 4 K i := fun i =>
    Submodule.subset_span ⟨(0 : Fin 4), by simp, rfl⟩
  have he₀Q : Q e₀ = 0 := flag_singular (r := 4) (K := K) 1 e₀ (he₀mem 0)
  have he₀0 : e₀ ≠ 0 := by
    intro h
    have := congrFun h (Sum.inl 0)
    simp [e₀] at this
  let ε₁ : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K) := (Θ xP : ↥(elementaryGroup Q))
  have hε₁O : ε₁ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q (Θ xP).2
  have hH1 : ∀ y, eichler Q (ε₁ e₀) y ∈ Jl := by
    intro y
    set y' := ε₁⁻¹ y with hy'
    have hηE : eichler Q e₀ y' ∈ elementaryGroup Q := eichler_mem_elementaryGroup Q e₀ y'
    have hstab : ∀ i, (stdFlag 4 K i).map (eichler Q e₀ y').toLinearMap = stdFlag 4 K i :=
      fun i => map_eichler_eq_of_totSingular (Q := Q)
        (flag_singular (r := 4) (K := K) (i + 1)) (he₀mem i) y'
    have hb := mem_borel_of_stab hK hn3 ⟨eichler Q e₀ y', hηE⟩ hstab
    have hconj := hxP _ hb
    have h1 : Θ (xP * Θ.symm ⟨eichler Q e₀ y', hηE⟩ * xP⁻¹) ∈
        (J.map e.toMonoidHom).map Θ.toMonoidHom := ⟨_, hconj, rfl⟩
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, map_inv] at h1
    have hJΨ : (J.map e.toMonoidHom).map Θ.toMonoidHom = J.map Ψ.toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    rw [hJΨ] at h1
    have h2 : ε₁ * eichler Q e₀ y' * ε₁⁻¹ ∈ Jl := ⟨_, h1, rfl⟩
    rwa [eichler_conj hε₁O, hy', LinearEquiv.apply_inv_apply'] at h2
  have he₁0 : ε₁ e₀ ≠ 0 := fun h => he₀0 (ε₁.injective (by rw [h, map_zero]))
  have he₁Q : Q (ε₁ e₀) = 0 := by rw [map_of_mem hε₁O, he₀Q]
  have hQnd := nondegenerate_polarBilin_quadPlus 4 K
  obtain ⟨W, hW0, hWQ, hWJ⟩ := exists_invariant_totSingular (Q := Q) hQnd hK2 hJlO hJltop he₁0
    he₁Q hH1
  let El : Subgroup ((Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :=
    (E₀.map Ψ.toMonoidHom).map (elementaryGroup Q).subtype
  have hElJ : El ≤ Jl := Subgroup.map_mono (Subgroup.map_mono hEJ)
  have hElO : El ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨g, -, rfl⟩
    exact elementaryGroup_le_orthogonalGroup Q g.2
  have hEl3 : IsPGroup 3 El := (hE3.map Ψ.toMonoidHom).map (elementaryGroup Q).subtype
  have hdim : Module.finrank K (Fin 4 ⊕ Fin 4 → K) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have hcount : Nat.card {v : Fin 4 ⊕ Fin 4 → K // Q v = 0} % 3 = 1 := by
    change Nat.card {v : Fin 4 ⊕ Fin 4 → K // quadPlus 4 K v = 0} % 3 = 1
    rw [card_singular_quadPlus_four hK]
  have hcomm := commutative_of_three_subgroup hK hQnd hdim hcount hElO hEl3 hW0 hWQ
    (fun g hg w hw => hWJ g (hElJ hg) w hw)
  have hxl : ((Ψ x : ↥(elementaryGroup Q)) : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) ∈ El :=
    ⟨Ψ x, ⟨x, hx, rfl⟩, rfl⟩
  have hyl : ((Ψ y : ↥(elementaryGroup Q)) : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) ∈ El :=
    ⟨Ψ y, ⟨y, hy, rfl⟩, rfl⟩
  have h := hcomm _ hxl _ hyl
  apply Ψ.injective
  rw [map_mul, map_mul]
  exact Subtype.ext h

end CFSG.HardMathSupport.Curtis.Coordinator
