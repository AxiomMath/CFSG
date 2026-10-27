module

public import CFSG.ClassicalInvolution.Asc77.AscIHSectKC
public import CFSG.ClassicalInvolution.Asc77.AscIHSectKB
public import CFSG.ClassicalInvolution.Asc77.AscIHSectD
public import CFSG.ClassicalInvolution.ModelFacts.D4RigidFrame

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Steinberg CFSG.LieType.BorelTits QuadraticMap
open CFSG.ClassicalInvolution.ModelFacts (spinCtx_pOmegaPlus exists_spin_conj
  finrank_perp_add_four map_longSL2_range map_conj_map La_range_eq_map_conj longestFundamental
  fundamentalSubgroups_subset_longest)
open CFSG.ClassicalInvolution.ModelFacts.D4Rigid (longSL2_range_mem_fund)
open CFSG.ClassicalInvolution.Models.OrthogonalPairs (IsFundamental)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)
open CFSG.ClassicalInvolution.Asc77.Hub (hubFrame hub_unitaryPair hub_ne_std)
open CFSG.LieType.CurtisTits (rankOne)
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]

theorem exists_hub (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hq3 : p ^ f % 4 = 3) :
    ∃ H : Subgroup (spinGroup (quadPlus 4 (GaloisField p f))),
      H ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p f) (by norm_num)) ∧
      ∀ {i j : Fin 4} (hij : i ≠ j) (s t : Bool),
        H ≠ ((plusFrame 4 (GaloisField p f) (by norm_num)).longSL2 hij s t).range ∧
        ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W H
          ((plusFrame 4 (GaloisField p f) (by norm_num)).longSL2 hij s t).range := by
  classical
  have hn3 : 3 ≤ 4 := by norm_num
  have S := spinCtx_pOmegaPlus (p := p) (n := 4) (e := f) le_rfl hp2 hq
  have hodd : Odd (Nat.card (GaloisField p f)) := S.odd_card
  have h2 : (2 : GaloisField p f) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  have hcard : Nat.card (GaloisField p f) = p ^ f := S.card_eq
  have hneg : ¬ IsSquare (-1 : GaloisField p f) := by
    have : Fintype (GaloisField p f) := Fintype.ofFinite _
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hcard]
    omega
  obtain ⟨a₀, b₀, hab₀⟩ := CharP.sq_add_sq (GaloisField p f) p (-1)
  have hab : (a₀ : GaloisField p f) * a₀ + (b₀ : GaloisField p f) * b₀ = -1 := by
    have := hab₀
    push_cast at this
    linear_combination this
  have h4 : (4 : GaloisField p f) ≠ 0 := by
    have : (4 : GaloisField p f) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  have hw : 4 * (4 : GaloisField p f)⁻¹ = 1 := mul_inv_cancel₀ h4
  set a : GaloisField p f := (a₀ : GaloisField p f) with ha
  set b : GaloisField p f := (b₀ : GaloisField p f) with hb
  set w : GaloisField p f := 4⁻¹ with hwdef
  have hij₀ : (0 : Fin 4) ≠ 1 := by decide
  set fr₀ := (plusFrame 4 (GaloisField p f) hn3).toFrame hij₀ true false with hfr₀
  have hperp : 2 ≤ Module.finrank (GaloisField p f) fr₀.perp := by
    have := finrank_perp_add_four fr₀
    have hdim : Module.finrank (GaloisField p f) (Fin 4 ⊕ Fin 4 → GaloisField p f) = 8 := by
      simp
    omega
  obtain ⟨x, hx⟩ := exists_spin_conj hodd (nondegenerate_polarBilin_quadPlus 4 (GaloisField p f))
    fr₀ (hubFrame a b w hab hw) hperp
  set R₀ := ((plusFrame 4 (GaloisField p f) hn3).longSL2 hij₀ true false).range with hR₀
  have hR₀fund : R₀ ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 4 (GaloisField p f) hn3) := longSL2_range_mem_fund hp2 hq hij₀ true false
  have hHfund : conjSub x R₀ ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 4 (GaloisField p f) hn3) :=
    CFSG.ClassicalInvolution.RouteD.conjSub_mem_fundamentalSubgroups hR₀fund x
  have hHmap : (conjSub x R₀).map (spinAction (quadPlus 4 (GaloisField p f))) =
      (hubFrame a b w hab hw).La.range := by
    unfold conjSub
    rw [map_conj_map, hR₀, map_longSL2_range]
    exact (La_range_eq_map_conj hx).symm
  refine ⟨conjSub x R₀, hHfund, ?_⟩
  intro i j hij s t
  have hRmap := map_longSL2_range (plusFrame 4 (GaloisField p f) hn3) hij s t
  have hRfund : ((plusFrame 4 (GaloisField p f) hn3).longSL2 hij s t).range ∈
      fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p f) hn3) :=
    longSL2_range_mem_fund hp2 hq hij s t
  have hHlong := fundamentalSubgroups_subset_longest (by decide) (by decide) _ hHfund
  have hRlong := fundamentalSubgroups_subset_longest (by decide) (by decide) _ hRfund
  have hpair := hub_unitaryPair (K' := GaloisField p (2 * f)) hcard S.card_eq' hodd hneg hn3 a b w
    hab hw hij s t
  have hpair' : UnitaryBlockStandardPair (GaloisField p (2 * f)) p f
      ((hubFrame a b w hab hw).La.range ⊔
        ((plusFrame 4 (GaloisField p f) hn3).toFrame hij s t).La.range)
      ((conjSub x R₀).map (spinAction (quadPlus 4 (GaloisField p f))))
      (((plusFrame 4 (GaloisField p f) hn3).longSL2 hij s t).range.map
        (spinAction (quadPlus 4 (GaloisField p f)))) := by
    rw [hHmap, hRmap]
    exact hpair
  refine ⟨?_, S.unitary_of_map hHlong hRlong ⟨_, hpair'⟩⟩
  intro hHR
  refine hub_ne_std hn3 a b w hab hw hij s t
    (IsFundamental.involution_unique hodd (L := (hubFrame a b w hab hw).La.range)
      ⟨_, rfl, rfl⟩ ?_)
  rw [← hHmap, hHR, hRmap]
  exact ⟨_, rfl, rfl⟩

theorem exists_hub_node (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hq3 : p ^ f % 4 = 3) :
    ∃ H : Subgroup (spinGroup (quadPlus 4 (GaloisField p f))),
      H ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField p f) (by norm_num)) ∧
      ∀ k : Fin 4,
        H ≠ rankOne (plusDatum 4 (GaloisField p f) (by norm_num)).rootGroup k ∧
        ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W H
          (rankOne (plusDatum 4 (GaloisField p f) (by norm_num)).rootGroup k) := by
  obtain ⟨H, hH, hall⟩ := exists_hub hp2 hq hq3
  refine ⟨H, hH, fun k => ?_⟩
  have hk : rankOne (plusDatum 4 (GaloisField p f) (by norm_num)).rootGroup k =
      ((plusFrame 4 (GaloisField p f) (by norm_num)).longSL2 (rootIdxD_ne 4 (by omega) k) true
        (rootSignD 4 k)).range := PlusCT.rankOne_plusRootGroup (by norm_num) k
  have key : ∀ R : Subgroup (spinGroup (quadPlus 4 (GaloisField p f))),
      R = ((plusFrame 4 (GaloisField p f) (by norm_num)).longSL2 (rootIdxD_ne 4 (by omega) k) true
        (rootSignD 4 k)).range →
      (H ≠ R ∧ ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W H R) := by
    rintro R rfl
    exact hall _ _ _
  exact key _ hk

theorem exists_hub_of_eq (M₀ : LieUniversal)
    (hM₀ : M₀ = ⟨spinGroup (quadPlus 4 (GaloisField p f)),
      plusDatum 4 (GaloisField p f) (by norm_num)⟩) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hq3 : p ^ f % 4 = 3) :
    ∃ H : Subgroup M₀.K, H ∈ fundamentalSubgroups .POmegaPlus M₀.D ∧
      ∀ k : Fin M₀.D.rank, H ≠ rankOne M₀.D.rootGroup k ∧
        ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W H
          (rankOne M₀.D.rootGroup k) := by
  subst hM₀
  exact exists_hub_node hp2 hq hq3

section Model

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem Ih8Model.dstarAdj_hub_node [Finite G] (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hq3 : p ^ f % 4 = 3) (M : Ih8Model p f Ω .POmegaPlus 4 f)
    {H : Subgroup (modelUniv .POmegaPlus 4 p f Fact.out).K} (hH : H ∈ M.cls) {k : Fin 4}
    (hne : H ≠ nodeSub p f k) (hmem : nodeSub p f k ∈ M.cls)
    (hW : ∃ W, UnitaryBlockStandardPair (GaloisField p (2 * f)) p f W H (nodeSub p f k)) :
    dstarAdj Ω (H.map M.ψ) ((nodeSub p f k).map M.ψ) := by
  have hD4 : (StatedLieTag.POmegaPlus) ≠ .trialityD4 := by decide
  have hnpsl : ¬ (StatedLieTag.POmegaPlus = .PSL ∧ (4 : ℕ) = 2) := by simp
  have hf1 : 1 ≤ f := M.admissible.2.1
  have hcardF : Nat.card (GaloisField p f) = p ^ f := natCard_galoisField_eq hf1
  have hK' : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := card_galoisField_two_mul p f hf1
  obtain ⟨W, hW⟩ := hW
  obtain ⟨u, hu⟩ := exists_orderOf_eq_two_part
    (normOne (unitaryInvolution (GaloisField p (2 * f)) p f))
  obtain ⟨v, hvV, hvN, hvo⟩ := UnitaryBlockStandardPair.exists_torus_elt hK' hW u
  refine M.dstarAdj_of_torus hΩ hp2 hq hD4 hnpsl hH hmem hne hvV hvN
    (a := (Nat.card (normOne (unitaryInvolution (GaloisField p (2 * f)) p f))).factorization 2)
    (hvo.trans hu) ?_
  rw [two_pow_sl2_of_three_mod_four (GaloisField p f) (by rw [hcardF]; exact hq3), hcardF,
    CFSG.ClassicalInvolution.Phan.card_normOne hK']

theorem ih8_dstarConnected_of_three_mod_four [Finite G] (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hq3 : p ^ f % 4 = 3) (M : Ih8Model p f Ω .POmegaPlus 4 f) :
    T3.DStarConnected Ω := by
  by_cases hne : Ω.Nonempty
  swap
  · intro K hK
    exact absurd ⟨K, hK⟩ hne
  have hD4 : (StatedLieTag.POmegaPlus) ≠ .trialityD4 := by decide
  have hG2 : (StatedLieTag.POmegaPlus) ≠ .G2 := by decide
  obtain ⟨H, hHfund, hall⟩ := exists_hub_of_eq (modelUniv .POmegaPlus 4 p f Fact.out)
    (modelUniv_pOmegaPlus_four p f (by norm_num)) hp2 hq hq3
  have hHcls : H ∈ M.cls := M.fund_subset_cls hne hG2 hD4 hHfund
  have hmem : ∀ i, nodeSub p f i ∈ M.cls := fun i =>
    M.fund_subset_cls hne hG2 hD4 (nodeSub_mem_fund p f i)
  refine M.dstarConnected_of_gens hΩ hG2 hD4 (fun o : Option (Fin 4) => o.elim H (nodeSub p f))
    none (fun o => ?_) ?_ (fun o => ?_)
  · cases o
    · exact hHcls
    · exact hmem _
  · rw [eq_top_iff, ← iSup_nodeSub p f]
    exact iSup_le fun k => le_iSup (fun o : Option (Fin 4) => o.elim H (nodeSub p f)) (some k)
  · cases o
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single (Ih8Model.dstarAdj_hub_node hΩ hp2 hq hq3 M hHcls
        (hall _).1 (hmem _) (hall _).2)

theorem ih8_dstarConnected [Finite G] (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (M : Ih8Model p f Ω .POmegaPlus 4 f) : T3.DStarConnected Ω := by
  have hodd : p ^ f % 2 = 1 := Nat.odd_iff.mp (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  rcases (by omega : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3) with h | h
  · exact ih8_dstarConnected_of_one_mod_four hΩ hp2 hq h M
  · exact ih8_dstarConnected_of_three_mod_four hΩ hp2 hq h M

end Model

theorem ih8D4Star : Ih8D4Star p f := by
  intro hp2 hq G _ _ Ω e hΩ ⟨M⟩
  have hD4 : (StatedLieTag.POmegaPlus) ≠ .trialityD4 := by decide
  have he : e = f := M.exp_eq_f hD4
  subst he
  exact ih8_dstarConnected hΩ hp2 hq M

end CFSG.ClassicalInvolution.Asc77
