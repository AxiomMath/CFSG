module

public import CFSG.RankThree.PartTwo.KFacts.L34SL

public section

namespace CFSG.AGLEmbedding.KFactProofs.CoverThree.SL3FourGen

open scoped Pointwise

theorem exists_conj_of_card {G : Type*} [Group G] [Finite G] {p n m : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p ^ n * m) (hm : ¬ p ∣ m) {P Q : Subgroup G} (hP : Nat.card P = p ^ n)
    (hQ : Nat.card Q = p ^ n) : ∃ g : G, ∀ x, x ∈ Q ↔ g⁻¹ * x * g ∈ P := by
  have : Fact p.Prime := ⟨hp⟩
  have hidx : ∀ H : Subgroup G, Nat.card H = p ^ n → H.index = m := fun H hH => by
    have := H.card_mul_index
    rw [hH, hG] at this
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos n) this
  let P' : Sylow p G := (IsPGroup.of_card hP).toSylow (by rw [hidx P hP]; exact hm)
  let Q' : Sylow p G := (IsPGroup.of_card hQ).toSylow (by rw [hidx Q hQ]; exact hm)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P' Q'
  refine ⟨g, fun x => ?_⟩
  have h1 : ((g • P' : Sylow p G) : Subgroup G) = (Q' : Subgroup G) := by rw [hg]
  rw [Sylow.coe_subgroup_smul] at h1
  have h2 : x ∈ (Q' : Subgroup G) ↔ x ∈ MulAut.conj g • (P' : Subgroup G) := by rw [← h1]
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h2
  have h3 : x ∈ (Q' : Subgroup G) ↔ g⁻¹ * x * g ∈ (P' : Subgroup G) := by simpa using h2
  exact h3

open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine in
open CFSG.RankThree.PartTwo.KFacts.L34 in
theorem exists_noncomm_of_card_27 {k : Type} [Field k] (hk : Nat.card k = 4) {K : Type} [Group K]
    (ψ : Matrix.SpecialLinearGroup (Fin 3) k ≃* K) {P : Subgroup K} (hP : Nat.card P = 27) :
    ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x := by
  have hK : Nat.card K = 60480 := by
    rw [← Nat.card_congr ψ.toEquiv]
    exact card_specialLinearGroup hk
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  have hQ : Nat.card ((qSub : Subgroup (Matrix.SpecialLinearGroup (Fin 3) k)).map
      ψ.toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective ψ.injective, card_qSub hk]
  obtain ⟨g, hg⟩ := exists_conj_of_card (p := 3) (n := 3) (m := 2240) Nat.prime_three
    (by rw [hK]; norm_num) (by norm_num) (by simpa using hP) hQ
  have hne : hSL u * rSL ≠ rSL * hSL u := by
    intro h
    have hc : hSL u * rSL * (hSL u)⁻¹ * rSL⁻¹ = 1 := by rw [h]; group
    rw [hSL_commutator hk, inv_eq_one] at hc
    have h0 := congrFun (congrFun (congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) k =>
      (g : Matrix (Fin 3) (Fin 3) k)) hc) 0) 0
    simp only [zSL, coe_dHom, Matrix.SpecialLinearGroup.coe_one] at h0
    simp at h0
    exact hu h0
  have hx : ψ (hSL u) ∈ (qSub : Subgroup (Matrix.SpecialLinearGroup (Fin 3) k)).map
      ψ.toMonoidHom := ⟨hSL u, hSL_mem_qSub, rfl⟩
  have hy : ψ rSL ∈ (qSub : Subgroup (Matrix.SpecialLinearGroup (Fin 3) k)).map
      ψ.toMonoidHom := ⟨rSL, rSL_mem_qSub, rfl⟩
  refine ⟨g⁻¹ * ψ (hSL u) * g, (hg _).1 hx, g⁻¹ * ψ rSL * g, (hg _).1 hy, fun h => hne ?_⟩
  apply ψ.injective
  have h1 : g * (g⁻¹ * ψ (hSL u) * g * (g⁻¹ * ψ rSL * g)) * g⁻¹ =
      g * (g⁻¹ * ψ rSL * g * (g⁻¹ * ψ (hSL u) * g)) * g⁻¹ := by rw [h]
  simpa [mul_assoc] using h1

end CFSG.AGLEmbedding.KFactProofs.CoverThree.SL3FourGen
