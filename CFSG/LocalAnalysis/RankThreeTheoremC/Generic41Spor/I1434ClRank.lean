module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434General
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
import all CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossPSU
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294OuterDiagRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

section Transfer

variable {K M : Type} [Group K] [Finite K] [Group M] [Finite M]

theorem false_of_four_le_pRank_top (e : K ≃* M) {Q : Sylow 5 K}
    (hQ : CFSG.Open.pRank 5 (Q : Subgroup K) = 3)
    (h : 4 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup M)) : False := by
  obtain ⟨E, -, hE, hc⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 5) (⊤ : Subgroup M)
  have hE' : IsElemAbelian 5 (E.map e.symm.toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hE _
  have hcard := card_le_of_isElemAbelian hQ hE'
  rw [Subgroup.card_map_of_injective e.symm.injective, hc] at hcard
  have h45 : 5 ^ 4 ≤ 5 ^ CFSG.Open.pRank 5 (⊤ : Subgroup M) :=
    Nat.pow_le_pow_right (by norm_num) h
  have := h45.trans hcard
  norm_num at this

theorem false_of_not_cyclic_derived (e : K ≃* M) {Q : Sylow 5 K}
    (hQ : IsMulCommutative (Q : Subgroup K)) {U : Subgroup M} (hU : IsPGroup 5 U)
    (hUd : ¬ IsCyclic ↥⁅U, U⁆) : False := by
  have hU' : IsPGroup 5 (U.map e.symm.toMonoidHom) := hU.map _
  haveI := isMulCommutative_of_isPGroup hQ hU'
  have hcomm : ∀ a b : U, a * b = b * a := fun a b => by
    have h1 := mul_comm' (⟨e.symm (a : M), Subgroup.mem_map_of_mem _ a.2⟩ :
      U.map e.symm.toMonoidHom) ⟨e.symm (b : M), Subgroup.mem_map_of_mem _ b.2⟩
    have h2 : e.symm (a : M) * e.symm (b : M) = e.symm (b : M) * e.symm (a : M) :=
      congrArg Subtype.val h1
    apply Subtype.ext
    apply e.symm.injective
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact h2
  have hbot : ⁅U, U⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    have := hcomm ⟨a, ha⟩ ⟨b, hb⟩
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact congrArg Subtype.val this
  rw [hbot] at hUd
  exact hUd (isCyclic_of_subsingleton)

end Transfer

section PSU

variable {K : Type} [Group K] [Finite K] {F : Type} [Field F] [Finite F] {ℓ f n : ℕ}

theorem false_of_psu_five_le (h : UnitaryFieldData ℓ f F) (hn : 5 ≤ n) (h5 : 5 ∣ ℓ ^ f + 1)
    (e : K ≃* StatedProj (StatedSU n (ℓ ^ f) F)) {Q : Sylow 5 K}
    (hQ : CFSG.Open.pRank 5 (Q : Subgroup K) = 3) (hab : IsMulCommutative (Q : Subgroup K)) :
    False := by
  rcases Nat.lt_or_ge n 6 with hn6 | hn6
  · have hn5 : n = 5 := by omega
    subst hn5
    obtain ⟨ζ, hζ⟩ := psu_exists_zeta Nat.prime_five h.card_eq_sq h5
    have hzp := psu_zeta_pow h5 hζ
    have hq0 : ℓ ^ f ≠ 0 := pow_ne_zero _ h.prime.ne_zero
    have hd : diagGL 5 ![ζ, ζ⁻¹, 1, 1, 1] ∈ StatedSU 5 (ℓ ^ f) F := by
      refine diagGL_mem_statedSU hq0 _ (fun i => hzp _ ?_) ?_
      · fin_cases i
        · exact Subgroup.mem_zpowers ζ
        · exact Subgroup.inv_mem _ (Subgroup.mem_zpowers ζ)
        · exact Subgroup.one_mem _
        · exact Subgroup.one_mem _
        · exact Subgroup.one_mem _
      · simp [Fin.prod_univ_five]
    have hc : permGL 5 (finRotate 5) ∈ StatedSU 5 (ℓ ^ f) F :=
      permGL_mem_statedSU hq0 _ (by rw [sign_finRotate]; decide)
    obtain ⟨U, hU, hUd⟩ := exists_not_cyclic_derived_projFive hζ (StatedSU 5 (ℓ ^ f) F) hd hc
    exact false_of_not_cyclic_derived e hab hU hUd
  · exact false_of_four_le_pRank_top e hQ
      (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.odFour_le_pRank_psu h
        Nat.prime_five hn6 h5)

end PSU

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434.Cl
