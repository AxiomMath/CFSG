module


public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TwE6Aux.Diag

public section

namespace CFSG.LieType.Chevalley

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.Blueprint.Chevalley
open CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.LocalAnalysis.ComponentInitial

theorem card_outer_twistedE6RootGroup_dvd
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    Nat.card (Outer (twistedE6RootGroup K σ)) ∣ 2 * Nat.gcd 3 (p ^ f + 1) * f := by
  classical
  set C := twistedE6RootGroup K σ
  set I : Subgroup (MulAut C) := inner C
  obtain ⟨-, -, -, -, -, -, -, -,
    ⟨Θ, -, hΘsurj, hΘker, -, -, -⟩, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hp hf K hK σ hσ
  have hinner : I ≤ Θ.ker := by
    rw [hΘker]
    exact le_sup_left
  let Φ : Outer C →* RingAut K := QuotientGroup.lift I Θ hinner
  have hΦsurj : Function.Surjective Φ := fun y => by
    obtain ⟨α, rfl⟩ := hΘsurj y
    exact ⟨α, QuotientGroup.lift_mk _ hinner α⟩
  let ψ : TwM σ →* Outer C :=
    (QuotientGroup.mk' I).comp (compatDiagAutHom TwistTag.E6 K σ.toRingHom)
  have hΦker : Φ.ker = ψ.range := by
    rw [show Φ = QuotientGroup.lift I Θ hinner from rfl, QuotientGroup.ker_lift, hΘker,
      Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    rw [show ψ = (QuotientGroup.mk' I).comp
      (compatDiagAutHom TwistTag.E6 K σ.toRingHom) from rfl, MonoidHom.range_comp]
  have hψker : twIm σ ≤ ψ.ker := by
    intro u hu
    exact (QuotientGroup.eq_one_iff _).2
      (compatDiagAutHom_mem_inner_of_mem_twIm σ hu)
  have hΦdvd : Nat.card Φ.ker ∣ Nat.gcd 3 (p ^ f + 1) := by
    rw [hΦker, ← Subgroup.index_ker]
    refine (Subgroup.index_dvd_of_le hψker).trans ?_
    rw [twIm_index σ hK hσ]
  have hK2 : Nat.card K = p ^ (2 * f) := by
    rw [hK, ← pow_mul, mul_comm f 2]
  have hcardAut : Nat.card (RingAut K) = 2 * f :=
    (card_ringAut_and_isCyclic hp K hK2).1
  have hOutEq : Nat.card (Outer C) = Nat.card Φ.ker * (2 * f) := by
    rw [← Subgroup.card_mul_index Φ.ker, Subgroup.index_ker,
      MonoidHom.range_eq_top.2 hΦsurj, Subgroup.card_top, hcardAut]
  rw [hOutEq]
  rw [show 2 * Nat.gcd 3 (p ^ f + 1) * f = Nat.gcd 3 (p ^ f + 1) * (2 * f) by ring]
  exact Nat.mul_dvd_mul_right hΦdvd (2 * f)

end CFSG.LieType.Chevalley

end
