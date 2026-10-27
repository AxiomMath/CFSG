module

public import CFSG.RankThree.PartOne.KC.UnitaryInnerPlaneKernel

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.PSUTwo

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryPlane

variable {ℓ f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem not_all_fixed_dim (hq : ℓ ^ f = 2) (hn : 3 ≤ n)
    (Ahat : Subgroup (gramSU h (idGram K n))) (hAel : IsElementaryAbelian 3 Ahat)
    (hAcard : Nat.card Ahat = 3 ^ 2) :
    ¬ ∀ x ∈ Ahat, x ≠ 1 → Module.finrank K (LinearMap.ker (Matrix.toLin'
      (((x : gramSU h (idGram K n)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1)) = n - 2 := by
  classical
  intro hfix
  have hfin := h.finite
  have : Finite ↥Ahat := inferInstance
  have : Fintype ↥Ahat := Fintype.ofFinite _
  have hP : IsPlane 3 ↥Ahat := isPlane_of_elementaryAbelian Nat.prime_three hAel hAcard
  have hℓ : ℓ = 2 := by
    have : ℓ ∣ 2 := hq ▸ dvd_pow_self ℓ (by have := h.one_le; omega)
    exact (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 this
  have hpK : ((3 : ℕ) : K) ≠ 0 := by
    have : CharP K ℓ := h.charP
    intro h0
    have := (CharP.cast_eq_zero_iff K ℓ 3).mp h0
    rw [hℓ] at this
    omega
  set ρ := planeRep h n Ahat with hρ
  have hρm : ∀ x : ↥Ahat, ρ x ∈ sesqUnitaryGroup (idForm h n) := planeRep_mem Ahat
  have hB := idForm_isSymm h n
  have hBl := idForm_separatingLeft h n
  have hsum := finrank_eq_sum ρ hP hpK hρm hB hBl
  rw [Module.finrank_fin_fun] at hsum
  have hline : ∀ L ∈ lines 3 ↥Ahat, Module.finrank K (lineSpace ρ (idForm h n) L) +
      Module.finrank K (fixedSpace ρ ⊤) = n - 2 := by
    intro L hL
    obtain ⟨x, hxL, hx1⟩ := exists_ne_one_mem hP.prime (mem_lines.mp hL)
    have h1 := ker_act_sub_one_eq ρ hP hpK hρm hB hBl (mem_lines.mp hL) hxL hx1
    have h2 := hfix (x : gramSU h (idGram K n)) x.2 (fun h' => hx1 (Subtype.ext h'))
    have h3 : LinearMap.ker (act ρ x - 1) = LinearMap.ker (Matrix.toLin'
        (((x : gramSU h (idGram K n)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) - 1) := rfl
    rw [← h3, h1] at h2
    have h4 := Submodule.finrank_sup_add_finrank_inf_eq (fixedSpace ρ ⊤)
      (lineSpace ρ (idForm h n) L)
    rw [fixedTop_inf_lineSpace ρ hP hpK hρm hB hBl L, finrank_bot, add_zero] at h4
    omega
  have hcard : (lines 3 ↥Ahat).card = 4 := hP.card_lines
  obtain ⟨L0, hL0⟩ : (lines 3 ↥Ahat).Nonempty := Finset.card_pos.1 (by omega)
  have hL0d := hline L0 hL0
  have hsum' : ∑ L ∈ lines 3 ↥Ahat, Module.finrank K (lineSpace ρ (idForm h n) L) =
      ∑ _L ∈ lines 3 ↥Ahat, (n - 2 - Module.finrank K (fixedSpace ρ ⊤)) :=
    Finset.sum_congr rfl fun L hL => by have := hline L hL; omega
  rw [hsum', Finset.sum_const, hcard, smul_eq_mul] at hsum
  omega

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.PSUTwo
