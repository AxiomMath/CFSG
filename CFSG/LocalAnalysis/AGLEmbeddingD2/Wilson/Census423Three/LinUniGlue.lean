module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census423Three.Sp4Glue
public import CFSG.RankThree.PartTwo.Sec21.Item228Census5ProofL4
public import CFSG.RankThree.PartTwo.Sec21.Item228Census3ProofMain
public import CFSG.RankThree.PartTwo.Sec4.Item417Res4ProofLieP
public import CFSG.LieType.SeitzGeneration.LinearPlaneFixed
public import CFSG.LieType.SeitzGeneration.UnitarySplit
public import CFSG.RankThree.PartOne.CTP.SeitzUIndex
public import CFSG.RankThree.PartOne.CTP.SeitzUToral
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census423Three

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (Census423)
open CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.Assembly.LowTwoRank (StatedSU StatedProj)
open Matrix

theorem seitz_of_equiv {G H : Type} [Group G] [Group H] (φ : G ≃* H)
    (h : ∀ E : Subgroup H, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ 3 = 1) →
      Nat.card E = 9 → Subgroup.closure {k : H | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤)
    (D : Subgroup G) (hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (hDexp : ∀ x ∈ D, x ^ 3 = 1)
    (hD9 : Nat.card D = 9) :
    (⊤ : Subgroup G) ≤ Subgroup.closure
      {x : G | ∃ d ∈ D, d ≠ 1 ∧ x ∈ Subgroup.centralizer ({d} : Set G)} := by
  have hE : ∀ x ∈ D.map φ.toMonoidHom, ∀ y ∈ D.map φ.toMonoidHom, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hDc a ha b hb]
  have hX : ∀ x ∈ D.map φ.toMonoidHom, x ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_pow, hDexp a ha, map_one]
  have hC : Nat.card (D.map φ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective φ.injective, hD9]
  exact closure_centralizers_of_map φ D (h _ hE hX hC)

theorem goodQ_of_sl2_or_psl2 (p : ℕ) [Fact p.Prime] (hp : 3 < p) {Q : Type} [Group Q]
    (h : Nonempty (Q ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField p 1)) ∨
      Nonempty (Q ≃* projSL 2 (GaloisField p 2))) :
    ∃ (S : Type) (_ : Group S), GoodGroup S ∧ Nonempty (Q ≃* S) := by
  rcases h with h | h
  · obtain ⟨e⟩ := h
    obtain ⟨hodd, h3, h5, hσ⟩ := fieldData_galoisField p 1 hp (Or.inl rfl)
    exact ⟨_, inferInstance, GoodGroup.sl2 hodd h3 h5 hσ, ⟨e⟩⟩
  · obtain ⟨e⟩ := h
    obtain ⟨hodd, h3, h5, hσ⟩ := fieldData_galoisField p 2 hp (Or.inr rfl)
    exact ⟨_, inferInstance, GoodGroup.psl2 h3 h5 hσ,
      ⟨e.trans (CFSG.RankThree.PartTwo.Sec4.projSLEquivPSL (GaloisField p 2))⟩⟩

theorem census423_of_projSL_four {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hp3 : p % 3 = 2)
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (hZ : Subgroup.center X = ⊥)
    (e : X ≃* projSL 4 (GaloisField p 1)) : Census423 X := by
  have : IsSimpleGroup (projSL 4 (GaloisField p 1)) := MulEquiv.isSimpleGroup e.symm
  have : Finite (projSL 4 (GaloisField p 1)) := inferInstance
  have hZM := Sec4.Res423Two.center_eq_bot_of_mulEquiv hZ e
  have hq : p ^ 1 % 3 = 2 := by rwa [pow_one]
  refine census423_of_data e hZM
    (rank2_of_pRank (Sec4.Res417Four.pRank_projSL_four_le_two (p := p) (f := 1) le_rfl hq))
    (fun d hd => goodQ_of_sl2_or_psl2 p hp (l4OddCentThree_holds p hp hp3 d hd)) ?_
  intro D hDc hDexp hD9
  have hp' : p.Prime := Fact.out
  set F := GaloisField p 1
  have hFc : Nat.card F = p ^ 1 := GaloisField.card p 1 one_ne_zero
  have h3 : (3 : F) ≠ 0 := Sec4.three_ne_zero_of_card hp' (by omega) hFc
  have hZc : ¬ 3 ∣ Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) F)) := by
    intro h
    have h1 := h.trans (CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd (by omega) F)
    have h2 : 3 ∣ 4 := h1.trans (Nat.gcd_dvd_left _ _)
    omega
  exact seitz_of_equiv (Sec4.projSLEquivPSLn 4 F)
    (fun E hc hx h9 => CFSG.LieType.SeitzGeneration.closure_centralizers_psl_three_ab (by omega) h3
      hZc E hc hx h9) D hDc hDexp hD9

theorem isElementaryAbelian_three {G : Type} [Group G] (E : Subgroup G)
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1) :
    CFSG.IsElementaryAbelian 3 E := CFSG.IsElementaryAbelian.of_forall hc hexp

theorem census423_of_projSU_four {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hp3 : p % 3 = 1)
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (hZ : Subgroup.center X = ⊥)
    (e : X ≃* projSU 4 p 1) : Census423 X := by
  have : IsSimpleGroup (projSU 4 p 1) := MulEquiv.isSimpleGroup e.symm
  have : Finite (projSU 4 p 1) := inferInstance
  have hZM := Sec4.Res423Two.center_eq_bot_of_mulEquiv hZ e
  have hq : p ^ 1 % 3 = 1 := by rwa [pow_one]
  refine census423_of_data e hZM
    (rank2_of_pRank (Sec4.Res417Four.pRank_projSU_four_le_two (p := p) (f := 1) (by omega)
      le_rfl hq))
    (fun d hd => goodQ_of_sl2_or_psl2 p hp (u4OddCentThree_holds p hp hp3 d hd)) ?_
  refine seitz_of_equiv (Sec4.projSUEquivStatedProj 4 p 1) ?_
  intro E hc hx h9
  have hp' : p.Prime := Fact.out
  have hU := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField p 1 le_rfl
  have : CFSG.IsElementaryAbelian 3 E := isElementaryAbelian_three E hc hx
  refine CFSG.RankThree.PartOne.CTP.closure_centralizers_statedProj_unitary_of_lift hU
    Nat.prime_three (by norm_num) ?_ E (by rw [h9]; norm_num) ?_
  · intro h
    have h1 := h.trans (Nat.gcd_dvd_left 4 (p ^ 1 + 1))
    omega
  · intro E' hc' he' hcd
    exact CFSG.LieType.SeitzGeneration.unitarySU_planeGen_split hU Nat.prime_three (by norm_num)
      (by omega) (by norm_num) E' hc' he' hcd

end CFSG.AGLEmbeddingD2.Wilson.Census423Three
