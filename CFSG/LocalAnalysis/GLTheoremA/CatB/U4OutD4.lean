module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XFNorm
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4Tab1

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_map_congr)

theorem u4Out_three_dvd_d4two {K : Type} [Group K] [Finite K] (h : catalogIs K S9.isD4two) :
    3 ∣ Nat.card (MulAut K ⧸ innerAut K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (MulAut K) :=
    Finite.of_injective (fun α : MulAut K => (α : K → K)) DFunLike.coe_injective
  obtain ⟨-, K₀, _, _, hK₀, ⟨e⟩⟩ := D4XF.statedModel_of_d4two h
  have hK₀' : Nat.card K₀ = 2 := by rw [hK₀]; norm_num
  haveI : Finite K₀ := Nat.finite_of_card_ne_zero (by omega)
  haveI : Fintype K₀ := Fintype.ofFinite K₀
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K₀ 2 := charP_of_card_eq_prime_pow (f := 1)
    (by rw [← Nat.card_eq_fintype_card, hK₀']; norm_num)
  have hunits : Nat.card K₀ˣ = 1 := by rw [Nat.card_units, hK₀']
  have hu : Subsingleton K₀ˣ := (Nat.card_eq_one_iff_unique.1 hunits).1
  obtain ⟨Φ⟩ := D4XF.equiv_triality_of_statedProj hu e
  obtain ⟨θK, hθK⟩ : ∃ θK : MulAut K,
      θK = (MulAut.congr Φ).symm (CFSG.StandardType.Triality.theta (K := K₀)) := ⟨_, rfl⟩
  have hθ3 : θK ^ 3 = 1 := by
    rw [hθK, ← map_pow, CFSG.StandardType.Triality.theta_cube, map_one]
  have hθout : θK ∉ inner K := by
    intro hmem
    apply D4XF.theta_not_mem_inner_om8 K₀
    have hm : (CFSG.StandardType.Triality.theta (K := K₀)) ∈
        (inner K).map (MulAut.congr Φ).toMonoidHom := by
      refine Subgroup.mem_map.2 ⟨θK, hmem, ?_⟩
      rw [hθK]
      exact (MulAut.congr Φ).apply_symm_apply _
    rwa [inner_map_congr Φ] at hm
  have hmk3 : QuotientGroup.mk' (innerAut K) θK ^ 3 = 1 := by
    rw [← map_pow, hθ3, map_one]
  have hmk1 : QuotientGroup.mk' (innerAut K) θK ≠ 1 := fun h1 =>
    hθout ((QuotientGroup.eq_one_iff θK).1 h1)
  have hord := orderOf_eq_prime hmk3 hmk1
  have hdvd := orderOf_dvd_natCard (QuotientGroup.mk' (innerAut K) θK)
  rwa [hord] at hdvd

theorem u4Out_index_d4two {P : Type} [Group P] [Finite P] (h : catalogIs P S9.isD4two) :
    (innerAut P).index = 3 ∨ (innerAut P).index = 6 := by
  haveI : Finite (MulAut P) :=
    Finite.of_injective (fun α : MulAut P => (α : P → P)) DFunLike.coe_injective
  have hle : Nat.card (MulAut P ⧸ innerAut P) ≤ 6 :=
    CFSG.EvenSmallLie.OmegaEight.card_outer_le_six (D4XF.statedModel_of_d4two h)
  have h3 := u4Out_three_dvd_d4two h
  have hpos : 0 < Nat.card (MulAut P ⧸ innerAut P) := Nat.card_pos
  obtain ⟨k, hk⟩ := h3
  change Nat.card (MulAut P ⧸ innerAut P) = 3 ∨ Nat.card (MulAut P ⧸ innerAut P) = 6
  omega

end CFSG.LocalAnalysis.GLTheoremA.CatB

end
