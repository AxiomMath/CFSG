module

public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsL2Eight
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsL2Glue
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsNN
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D61

public noncomputable section

open Equiv Equiv.Perm MulAction CFSG.Open CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  GL83 GL83.CompFam CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG CFSG.GorensteinWalter CFSG.ComponentClassification.AutL2Facts
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups

namespace CFSG.HardMathSupport.Solomon.Coordinator

namespace L2Plane

variable {F : Type} [Field F] [Finite F]

theorem card_le_three_of_cube_psl2_even {n : ℕ} (hn : 3 ≤ n) (hF : Nat.card F = 2 ^ n)
    (E : Subgroup (PSL2 F)) (hE3 : ∀ x ∈ E, x ^ 3 = 1) : Nat.card E ≤ 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpg : IsPGroup 3 E := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hE3 x x.2)⟩
  obtain ⟨R, hR⟩ := hpg.exists_le_sylow
  have h7 : 7 ≤ Nat.card F := by
    rw [hF]
    calc 7 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hcop : Nat.Coprime 3 (Nat.card F) := by
    rw [hF]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hcyc : IsCyclic (R : Subgroup (PSL2 F)) :=
    psl2_sylow_isCyclic_of_coprime_field_card F hF h7 3 (by norm_num) hcop R
  classical
  haveI := Fintype.ofFinite (R : Subgroup (PSL2 F))
  have hbound : Nat.card {x : (R : Subgroup (PSL2 F)) // x ^ 3 = 1} ≤ 3 := by
    have := IsCyclic.card_pow_eq_one_le (α := (R : Subgroup (PSL2 F))) (n := 3) (by norm_num)
    simpa [Nat.card_eq_fintype_card, Fintype.card_subtype] using this
  refine le_trans (Nat.card_le_card_of_injective
    (fun x : E => (⟨⟨x.1, hR x.2⟩, Subtype.ext (hE3 x.1 x.2)⟩ :
      {y : (R : Subgroup (PSL2 F)) // y ^ 3 = 1})) ?_) hbound
  intro x y hxy
  apply Subtype.ext
  have := congrArg (fun z : {y : (R : Subgroup (PSL2 F)) // y ^ 3 = 1} => ((z : _) : PSL2 F)) hxy
  exact this

end L2Plane

theorem card_le_three_of_inner_even {S : Type} [Group S] [Finite S]
    (hS : IsLTwoOddPow S) (A : Subgroup (MulAut S)) (hA : IsElemAbelian 3 A)
    (hAi : A ≤ innerAut S) : Nat.card A ≤ 3 := by
  obtain ⟨K, hK, hfin, n, hn, hn1, hcard, ⟨e0⟩⟩ := hS
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by rw [← Nat.card_eq_fintype_card, hcard])
  let e : S ≃* PSL2 K := e0.trans
    ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm.trans
      (L2Plane.slEquivPsl2 K))
  let φ : MulAut S ≃* PGammaL2 K := autEquiv e
  let Ab : Subgroup (PGammaL2 K) := A.map φ.toMonoidHom
  have hAb : Ab ≤ (incl K).range := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 : φ a ∈ (MulAut.conj : S →* MulAut S).range.map φ.toMonoidHom := ⟨a, hAi ha, rfl⟩
    rw [map_autEquiv_innAut e] at h1
    exact h1
  let E : Subgroup (PSL2 K) := Ab.comap (incl K)
  have hEmap : E.map (incl K) = Ab := Subgroup.map_comap_eq_self hAb
  have hEcard : Nat.card E = Nat.card A := by
    calc Nat.card E = Nat.card (E.map (incl K)) :=
          (Subgroup.card_map_of_injective (incl_injective K)).symm
      _ = Nat.card Ab := by rw [hEmap]
      _ = Nat.card A := Subgroup.card_map_of_injective φ.injective
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := (hx : incl K x ∈ Ab)
    apply incl_injective K
    rw [map_pow, map_one, ← hax]
    show φ a ^ 3 = 1
    rw [← map_pow]
    have : a ^ 3 = 1 := hA.2 a ha
    rw [this, map_one]
  rw [← hEcard]
  exact L2Plane.card_le_three_of_cube_psl2_even (n := n) (by omega) hcard E hE3

section NNL2

variable {X : Type} [Group X] [Finite X]

theorem inner_autOrderIn_le_three {K B : Subgroup X}
    (hBel : IsElemAbelian 3 B) (hK : IsLTwoOddPow ↥K) (hinn : InducesInnerIn B K) :
    autOrderIn B K ≤ 3 := by
  classical
  set N : Subgroup X := Subgroup.normalizer (K : Set X) with hN
  set A : Subgroup X := B ⊓ N with hA
  have hAB : A ≤ B := inf_le_left
  have hAN : A ≤ N := inf_le_right
  have hAel : IsElemAbelian 3 A := elem_mono hBel hAB
  let θ : ↥N →* MulAut ↥K := K.normalizerMonoidHom
  let Ā : Subgroup (MulAut ↥K) := (A.subgroupOf N).map θ
  have hĀel : IsElemAbelian 3 Ā :=
    CFSG.SectionRank.isElemAbelian_map (i271_isElemAbelian_subgroupOf N hAel) θ
  have hker : θ.ker = (Subgroup.centralizer (K : Set X)).subgroupOf N :=
    Subgroup.normalizerMonoidHom_ker (H := K)
  have hcardĀ : Nat.card Ā = autOrderIn B K := by
    show Nat.card ((A.subgroupOf N).map θ) = _
    rw [← Subgroup.relIndex_ker, hker, Subgroup.relIndex_subgroupOf hAN]
    rfl
  have hĀi : Ā ≤ innerAut ↥K := by
    rintro _ ⟨b', hb', rfl⟩
    obtain ⟨k, hk, hkc⟩ := hinn b' (Subgroup.mem_subgroupOf.1 hb')
    refine ⟨⟨k, hk⟩, ?_⟩
    ext y
    show (k : X) * y * (k : X)⁻¹ = (b' : X) * y * (b' : X)⁻¹
    have hc : (y : X) * ((k : X)⁻¹ * b') = ((k : X)⁻¹ * b') * y :=
      Subgroup.mem_centralizer_iff.1 hkc y y.2
    calc (k : X) * y * (k : X)⁻¹
        = (k : X) * ((y : X) * ((k : X)⁻¹ * b')) * ((k : X)⁻¹ * b')⁻¹ * (k : X)⁻¹ := by group
      _ = (k : X) * (((k : X)⁻¹ * b') * y) * ((k : X)⁻¹ * b')⁻¹ * (k : X)⁻¹ := by rw [hc]
      _ = (b' : X) * y * (b' : X)⁻¹ := by group
  rw [← hcardĀ]
  exact card_le_three_of_inner_even hK Ā hĀel hĀi

theorem nnExc_lTwoOddPow :
    NNExc (fun _ _ K => IsLTwoOddPow ↥K) := by
  intro X _ _ hXK K B hH hNN hidx h4 h9 hP
  have hBel : IsElemAbelian 3 B := hH.scp.2.1
  have hq : CFSG.Open.IsQuasisimple ↥K := i116e_isQuasisimple hH.core hH.comp
  by_cases h8 : IsLTwoEight ↥K
  · right; left
    have hZ : Subgroup.center ↥K = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      rw [Subgroup.mem_bot]
      by_contra hz1
      exact not_isLTwoOddPow_of_central ⟨z, hz, hz1⟩ hP
    obtain ⟨F, hF, hfin, hcard, ⟨e8⟩⟩ := h8
    let eQ : ↥K ⧸ Subgroup.center ↥K ≃* ↥K :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    have hS8 : IsLTwoEight (↥K ⧸ Subgroup.center ↥K) := ⟨F, hF, hfin, hcard, ⟨eQ.trans e8⟩⟩
    exact isStronglyBalancedIn_of_autBalanced hBel hq.1 (MulEquiv.refl _) (by rw [h9]; all_goals norm_num)
      (fun A hA hn T hT hAT => autLTwoEightBalance_holds _ hS8 A hA hn T hT hAT)
  · left
    by_cases hinn : InducesInnerIn B K
    · exfalso
      have := inner_autOrderIn_le_three hBel hP hinn
      omega
    · have hK' := hyperplane_gen_of_plane l2FieldPlane_holds hBel (Or.inr ⟨hP, h8⟩) hinn
        (by rw [h9]; norm_num)
      exact nn_caseA_of_hyperplane hH.comp hBel hH.rank_four (one_le_pRank_inf_normalizer hH) hK'

end NNL2

end CFSG.HardMathSupport.Solomon.Coordinator
