module

public import CFSG.ClassicalInvolution.Phan.PhanD5Mat
public import CFSG.ClassicalInvolution.Phan.PhanD4Tor

public section

namespace CFSG.ClassicalInvolution.PhanD4

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary
open CFSG.Timmesfeld (edgeD)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {G : Type} [Group G]

structure GoodFamily (S : PhanFamilyD4 K p f G) : Prop where
  inj : ∀ i, Function.Injective (S.ι i)
  disj : ∀ i j, i ≠ j → (S.ι i).range ⊓ (S.ι j).range = ⊥
  ker : ∀ e, (S.θ e).ker ≤ Subgroup.center (Su K p f 3)

section Rho

theorem rho_zero (t : Fin 4 → normOne (unitaryInvolution K p f)) :
    rho 0 t = t 0 * t 0 * (t 1)⁻¹ := by
  have e01 : edgeD 4 0 1 := by decide
  rw [rho, chi_self, chi_edge' e01,
    chi_far (i := 2) (j := 0) (by decide) (by decide) (by decide),
    chi_far (i := 3) (j := 0) (by decide) (by decide) (by decide)]
  simp

theorem rho_one (t : Fin 4 → normOne (unitaryInvolution K p f)) :
    rho 1 t = (t 0)⁻¹ * (t 1 * t 1) * (t 2)⁻¹ * (t 3)⁻¹ := by
  have e01 : edgeD 4 0 1 := by decide
  have e12 : edgeD 4 1 2 := by decide
  have e13 : edgeD 4 1 3 := by decide
  rw [rho, chi_edge e01, chi_self, chi_edge' e12, chi_edge' e13]

theorem rho_two (t : Fin 4 → normOne (unitaryInvolution K p f)) :
    rho 2 t = (t 1)⁻¹ * (t 2 * t 2) := by
  have e12 : edgeD 4 1 2 := by decide
  rw [rho, chi_far (i := 0) (j := 2) (by decide) (by decide) (by decide), chi_edge e12, chi_self,
    chi_far (i := 3) (j := 2) (by decide) (by decide) (by decide)]
  simp

theorem rho_three (t : Fin 4 → normOne (unitaryInvolution K p f)) :
    rho 3 t = (t 1)⁻¹ * (t 3 * t 3) := by
  have e13 : edgeD 4 1 3 := by decide
  rw [rho, chi_far (i := 0) (j := 3) (by decide) (by decide) (by decide), chi_edge e13,
    chi_far (i := 2) (j := 3) (by decide) (by decide) (by decide), chi_self]
  simp

end Rho

section Good

variable {S : PhanFamilyD4 K p f G}

theorem edgeD_edge (e : Fin 3) : edgeD 4 (edgeSrc e) (edgeTgt e) :=
  (edgeD_iff _ _).2 ⟨e, rfl, rfl⟩

theorem GoodFamily.θ_injective (hK : Nat.card K = (p ^ f) ^ 2) (hg : GoodFamily S) (e : Fin 3) :
    Function.Injective (S.θ e) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  obtain ⟨u, rfl⟩ := exists_scalar_decomp hK (hg.ker e hz)
  rw [map_mul, ← ι_src, ← ι_tgt] at hz
  have h1 : S.ι (edgeSrc e) (torusTwo (unitaryInvolution K p f) u) =
      S.ι (edgeTgt e) (torusTwo (unitaryInvolution K p f) u) := by
    have := mul_eq_one_iff_eq_inv.mp hz
    rw [this, ← map_inv, ← map_inv, inv_inv]
  have hmem : S.ι (edgeSrc e) (torusTwo (unitaryInvolution K p f) u) ∈
      (S.ι (edgeSrc e)).range ⊓ (S.ι (edgeTgt e)).range :=
    ⟨⟨_, rfl⟩, h1 ▸ ⟨_, rfl⟩⟩
  rw [hg.disj _ _ (edgeD_ne (edgeD_edge e)), Subgroup.mem_bot] at hmem
  have hu : u = 1 := torusTwo_injective _ (by
    rw [map_one]
    exact hg.inj _ (by rw [hmem, map_one]))
  subst hu
  simp

theorem GoodFamily.tor_negOne_mul_ne_one (hg : GoodFamily S) (h2 : (2 : K) ≠ 0) {i j : Fin 4}
    (hij : i ≠ j) :
    tor S i (negOne (unitaryInvolution K p f)) *
      tor S j (negOne (unitaryInvolution K p f)) ≠ 1 := by
  intro h
  have h1 : tor S i (negOne (unitaryInvolution K p f)) =
      tor S j (negOne (unitaryInvolution K p f)) := by
    rw [mul_eq_one_iff_eq_inv.mp h, ← map_inv, negOne_inv]
  have hmem : tor S i (negOne (unitaryInvolution K p f)) ∈ (S.ι i).range ⊓ (S.ι j).range :=
    ⟨⟨_, rfl⟩, h1 ▸ ⟨_, rfl⟩⟩
  rw [hg.disj i j hij, Subgroup.mem_bot] at hmem
  exact negOne_ne_one _ h2 (torusTwo_injective _ (by
    rw [map_one]
    exact hg.inj i (by rw [map_one]; exact hmem)))

theorem GoodFamily.mTor_injective (hK : Nat.card K = (p ^ f) ^ 2) (hg : GoodFamily S)
    (h2 : (2 : K) ≠ 0) : Function.Injective (mTor S) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  have hrho : ∀ j, rho j t = 1 := by
    intro j
    refine eq_one_of_conjDiag_weyl hK (hg.inj j ?_)
    rw [← mTor_conj_ι hK S t j, ht, one_mul, inv_one, mul_one]
  have r0 := hrho 0
  have r1 := hrho 1
  have r2 := hrho 2
  have r3 := hrho 3
  rw [rho_zero] at r0
  rw [rho_one] at r1
  rw [rho_two] at r2
  rw [rho_three] at r3
  have h0 : t 0 * t 0 = t 1 := mul_inv_eq_one.mp r0
  have h2' : t 2 * t 2 = t 1 := (inv_mul_eq_one.mp r2).symm
  have h3 : t 3 * t 3 = t 1 := (inv_mul_eq_one.mp r3).symm
  have h1 : t 1 * t 1 = t 0 * t 2 * t 3 := by
    have a1 := mul_inv_eq_one.mp r1
    have a2 := mul_inv_eq_iff_eq_mul.mp a1
    have a3 := inv_mul_eq_iff_eq_mul.mp a2
    rw [a3, mul_comm (t 3) (t 2), mul_assoc]
  obtain ⟨ht1, hcase⟩ := cartan_solutions h0 h2' h3 h1
  have hsplit := mTor_apply S t
  rw [ht] at hsplit
  have ne := fun {i j : Fin 4} (hij : i ≠ j) => hg.tor_negOne_mul_ne_one h2 hij
  rcases hcase with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
  · funext i
    fin_cases i
    · exact a
    · exact ht1
    · exact b
    · exact c
  · rw [a, ht1, b, c] at hsplit
    simp only [map_one, mul_one] at hsplit
    exact absurd hsplit.symm (ne (by decide : (0 : Fin 4) ≠ 3))
  · rw [a, ht1, b, c] at hsplit
    simp only [map_one, mul_one] at hsplit
    exact absurd hsplit.symm (ne (by decide : (0 : Fin 4) ≠ 2))
  · rw [a, ht1, b, c] at hsplit
    simp only [map_one, mul_one, one_mul] at hsplit
    exact absurd hsplit.symm (ne (by decide : (2 : Fin 4) ≠ 3))

end Good

end CFSG.ClassicalInvolution.PhanD4
