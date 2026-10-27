module

public import CFSG.HardMathSupport.Seitz.G2Noninner.Coordinator.FixedPair
public import CFSG.HardMathSupport.Seitz.G2Noninner.Coordinator.A1A1Pair
public import CFSG.LieType.SeitzGeneration.ExcOuterG2
public import CFSG.LieType.SeitzGeneration.ExcPlaneBridge

public section

namespace CFSG.HardMathSupport.Seitz.G2Noninner.Coordinator

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.RankThree.PartOne.SEITZ3 CFSG.RankThree.PartTwo.KFacts
  CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField CFSG.TauCetiBridge TauCeti

theorem exists_conj_mul_pow {P : Type*} [Group P] (g : P) (f : MulAut P) :
    ∀ n : ℕ, ∃ h : P, (MulAut.conj g * f) ^ n = MulAut.conj h * f ^ n
  | 0 => ⟨1, by simp⟩
  | n + 1 => by
    obtain ⟨h, hh⟩ := exists_conj_mul_pow g f n
    refine ⟨h * (f ^ n) g, ?_⟩
    have hc : f ^ n * MulAut.conj g = MulAut.conj ((f ^ n) g) * f ^ n := by
      rw [← CFSG.LieType.SeitzGeneration.mulAut_mul_conj_mul_inv (f ^ n) g, inv_mul_cancel_right]
    rw [pow_succ, hh, pow_succ, map_mul, mul_assoc, ← mul_assoc (f ^ n), hc]
    group

section Core


variable {K : Type} [Field K] [Finite K]

theorem exists_fieldAut_of_noninner (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K) {p : ℕ}
    (hp : p.Prime) {ψ : MulAut (adjointGroup .G2 K)}
    (hψ : ψ ∉ (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range)
    (hψp : ψ ^ p = 1) :
    ∃ (g : adjointGroup .G2 K) (σ : K ≃+* K), ψ = MulAut.conj g * g2FieldHom K σ ∧
      orderOf σ = p ∧ ∀ x, g2FieldHom K σ ≠ MulAut.conj x := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hNF, hInn⟩ := g2_automorphism_normal_form hK3 hK4
  obtain ⟨g, σ, hψeq⟩ := hNF ψ
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    apply hψ
    rw [hψeq, map_one, mul_one]
    exact ⟨g, rfl⟩
  have hσp : σ ^ p = 1 := by
    obtain ⟨h, hh⟩ := exists_conj_mul_pow g (g2FieldHom K σ) p
    rw [← hψeq, hψp] at hh
    apply hInn
    refine ⟨h⁻¹, ?_⟩
    rw [map_inv, map_pow, eq_inv_of_mul_eq_one_right hh.symm]
  refine ⟨g, σ, hψeq, orderOf_eq_prime hσp hσ1, fun x hx => hσ1 (hInn σ ⟨x, hx.symm⟩)⟩

theorem false_of_noninner_narrowScope (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hSL : ∀ (k : Type) [Field k] [Finite k], p ∣ Nat.card k ^ 2 - 1 →
      ∃ x : Matrix.SpecialLinearGroup (Fin 2) k, orderOf x = p)
    {E : Subgroup (MulAut (adjointGroup .G2 K))} (hE : ∀ x ∈ E, x ^ p = 1)
    (hout : ¬ E ≤ (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range)
    (hs : NarrowScope p E)
    (hk : ∀ σ : K ≃+* K, orderOf σ = p → p ∣ Nat.card (fixedField σ) ^ 2 - 1) : False := by
  obtain ⟨ψ, hψE, hψ⟩ := IsConcreteLE.not_le_iff_exists.1 hout
  obtain ⟨g, σ, hψeq, hσ, hfout⟩ := exists_fieldAut_of_noninner hK3 hK4 hp hψ (hE ψ hψE)
  obtain ⟨x₀, hx₀⟩ := hSL (fixedField σ) (hk σ hσ)
  set x : Matrix.SpecialLinearGroup (Fin 2) K :=
    Matrix.SpecialLinearGroup.map (fixedField σ).subtype x₀ with hxdef
  have hinjmap : Function.Injective
      (Matrix.SpecialLinearGroup.map (n := Fin 2) (fixedField σ).subtype) := by
    intro A B h
    apply Subtype.ext
    ext i j
    have := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) K =>
      (X : Matrix (Fin 2) (Fin 2) K) i j) h
    simpa using this
  have hx : orderOf x = p := by rw [hxdef, orderOf_injective _ hinjmap, hx₀]
  have hxσ : Matrix.SpecialLinearGroup.map σ.toRingHom x = x := by
    apply Subtype.ext
    ext i j
    simp only [hxdef, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply]
    exact (mem_fixedField_iff σ _).1 (x₀ i j).2
  have := finite_modGL (τ := .G2) (K := K)
  have hinj : Function.Injective
      (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)) :=
    conj_injective_of_center_eq_bot center_adjointGroup_eq_bot
  have hfX : g2FieldHom K σ ∈
      (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range ⊔ E := by
    have h1 : g2FieldHom K σ = (MulAut.conj g)⁻¹ * ψ := by rw [hψeq, inv_mul_cancel_left]
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.inv_mem _ ⟨g, rfl⟩))
      (Subgroup.mem_sup_right hψE)
  have hfp : g2FieldHom K σ ^ p = 1 := by rw [← map_pow, ← hσ, pow_orderOf_eq_one, map_one]
  obtain ⟨hαp, hβp⟩ := a1a1Hom_pow_eq_one (K := K) (n := p)
    (by rw [← hx]; exact pow_orderOf_eq_one x)
  exact false_of_fixed_pair_sup hp hinj hs hfX hfp hfout (commute_a1a1Hom x x) hαp hβp
    (a1a1Hom_indep hp hp2 hx) (g2FieldHom_a1a1Hom_inl σ hxσ) (g2FieldHom_a1a1Hom_inr σ hxσ)

end Core

section Regime


theorem seitzExcOuterNarrowG2Three_of_SL2
    (hSL : ∀ (k : Type) [Field k] [Finite k], 3 ∣ Nat.card k ^ 2 - 1 →
      ∃ x : Matrix.SpecialLinearGroup (Fin 2) k, orderOf x = 3) :
    SeitzExcOuterNarrowG2Three := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hcard ⟨hout, hs, ⟨q, rfl⟩, rfl⟩
  exfalso
  obtain ⟨K, _, _, hK, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.g2 q hv
  have h3q : 3 ≠ q.p := by simpa using hpd
  have h3K : ¬ 3 ∣ Nat.card K := by
    rw [hK]
    exact not_dvd_card_of_ne Nat.prime_three h3q
  have hK3 : ringChar K ≠ 3 := by
    rw [ringChar.eq K q.p]
    exact h3q.symm
  have hK4 : 4 ≤ Nat.card K := by
    have h3 : 3 ≤ Nat.card K := by
      rw [hK]
      exact (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
    have h3' : Nat.card K ≠ 3 := fun h => h3K (h ▸ dvd_rfl)
    omega
  refine false_of_noninner_narrowScope hK3 hK4 Nat.prime_three (by norm_num) hSL
    (E := E.map (MulAut.congr e).toMonoidHom) ?_ ?_ (hs.map_congr e) ?_
  · rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hE.2 y hy, map_one]
  · intro hle
    apply hout
    intro φ hφ
    obtain ⟨g, hg⟩ := hle ⟨φ, hφ, rfl⟩
    exact ⟨e.symm g, (CFSG.RankThree.PartOne.CTP.eq_conj_of_congr_eq_conj e hg.symm).symm⟩
  · intro σ hσ
    have hcard := fixedField_card_pow_order σ
    rw [hσ] at hcard
    have h3k : ¬ 3 ∣ Nat.card (fixedField σ) := fun h =>
      h3K (hcard ▸ dvd_pow h (by norm_num))
    refine Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq ?_)
    have h12 : Nat.card (fixedField σ) % 3 = 1 ∨ Nat.card (fixedField σ) % 3 = 2 := by omega
    rw [Nat.pow_mod]
    rcases h12 with h | h <;> rw [h]

end Regime

end CFSG.HardMathSupport.Seitz.G2Noninner.Coordinator
