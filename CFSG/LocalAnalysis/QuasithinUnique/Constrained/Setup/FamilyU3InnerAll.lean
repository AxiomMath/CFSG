module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyU3Inner
public import CFSG.RankThree.Classical.SteinbergBJUnitaryThreeInvolutions
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyL3Inner

public section

namespace CFSG.QuasithinUnique.Setup.Family

open Matrix Module CFSG.LieType.Universal.Unitary CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] [CharP K p]

theorem inner_rank_ge_four_unitary (hp5 : 5 ≤ p) (hK : Nat.card K = (p ^ 1) ^ 2) {E : Type*}
    [AddCommGroup E] [Module (ZMod 2) E] [Module.Finite (ZMod 2) E]
    (ρ₀ : ↥(StatedSU 3 (p ^ 1) K) →* (E ≃ₗ[ZMod 2] E))
    (hρ₀ : ∀ g, ρ₀ g = 1 →
      ∃ r : Kˣ, (g : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) r)
    {g : ↥(StatedSU 3 (p ^ 1) K)} (hg2 : g * g = 1) (hg1 : g ≠ 1) :
    4 ≤ finrank (ZMod 2) (LinearMap.range (sub1 (ρ₀ g))) := by
  classical
  have hp := (Fact.out : p.Prime)
  have hp2 : p ≠ 2 := by omega
  have h : UnitaryFieldData p 1 K := ⟨hp, le_rfl, by rw [hK]; ring⟩
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  let σ : K ≃+* K := CFSG.LieType.BorelTits.unitaryInvolution K p 1
  have hσ : ∀ x, σ (σ x) = x := CFSG.LieType.BorelTits.unitaryInvolution_involutive hK
  have hσbar : ∀ x, σ x = h.bar x := fun x => by
    show CFSG.LieType.BorelTits.unitaryInvolution K p 1 x = _
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, h.bar_apply]
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  have hω : σ (c - h.bar c) = -(c - h.bar c) := by
    rw [map_sub, hσbar c, hσbar (h.bar c), h.bar_bar]
    ring
  have hω0 : c - h.bar c ≠ 0 := fun h0 => hc (sub_eq_zero.1 h0).symm
  obtain ⟨P, hP⟩ := exists_wittMatrix hK 3
  let Ξ : SU σ 3 ≃* StatedSU 3 (p ^ 1) K :=
    (conjEquiv P hP).trans (MulEquiv.subgroupCongr (SUid_eq_statedSU hK 3))
  let ρ : SU σ 3 →* (E ≃ₗ[ZMod 2] E) := ρ₀.comp Ξ.toMonoidHom
  have hΞ : ∀ g' : SU σ 3, ((Ξ g' : ↥(StatedSU 3 (p ^ 1) K)) : GL (Fin 3) K) =
      P * g' * P⁻¹ := fun g' => rfl
  have hρ : ∀ g' : SU σ 3, ρ g' = 1 →
      ∃ r : Kˣ, (g' : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) r := by
    intro g' hg'
    obtain ⟨r, hr⟩ := hρ₀ (Ξ g') hg'
    refine ⟨r, ?_⟩
    rw [hΞ] at hr
    calc (g' : GL (Fin 3) K) = P⁻¹ * (P * g' * P⁻¹) * P := by group
      _ = P⁻¹ * GeneralLinearGroup.scalar (Fin 3) r * P := by rw [hr]
      _ = GeneralLinearGroup.scalar (Fin 3) r := by
        rw [mul_assoc, ← (commute_scalar r P).eq, inv_mul_cancel_left]
  let ι : ZMod p →+* K := ZMod.castHom (dvd_refl p) K
  have hFK : ∀ k : ZMod p, ∃ n : ℕ, (n : ZMod p) = k := fun k => ⟨k.val, ZMod.natCast_zmod_val k⟩
  have hι : ∀ x : ZMod p, σ (ι x) = ι x := by
    intro x
    obtain ⟨n, rfl⟩ := hFK x
    simp [ι, map_natCast]
  have hrk : 4 ≤ finrank (ZMod 2) (LinearMap.range (sub1 (ρ (negT σ)))) :=
    negT_rank_ge_four hp5 (ZMod.card p) hFK ι hι hσ hω hω0 ρ hρ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hneg2 : Ξ (negT σ) * Ξ (negT σ) = 1 := by rw [← map_mul, negT_mul_self, map_one]
  have hneg1 : Ξ (negT σ) ≠ 1 := by
    intro h1
    have h3 : negT σ = 1 := Ξ.injective (by rw [h1, map_one])
    have e := congrArg (fun M : SU σ 3 => ((M : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) h3
    simp [negT, coe_torGL, torMat] at e
    apply h2
    linear_combination -e
  have hog : orderOf g = 2 := orderOf_eq_prime (by rw [pow_two]; exact hg2) hg1
  have hon : orderOf (Ξ (negT σ)) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hneg2) hneg1
  have c1 := CFSG.RankThree.Classical.isConj_unitaryInvT_of_orderOf h hp2 hog
  have c2 := CFSG.RankThree.Classical.isConj_unitaryInvT_of_orderOf h hp2 hon
  obtain ⟨u, hu⟩ := isConj_iff.1 (c2.symm.trans c1)
  have hgu : ρ₀ g = ρ₀ u * ρ₀ (Ξ (negT σ)) * (ρ₀ u)⁻¹ := by
    rw [← hu]
    simp [map_mul, map_inv]
  rw [hgu, finrank_range_sub1_conj]
  exact hrk

end CFSG.QuasithinUnique.Setup.Family
