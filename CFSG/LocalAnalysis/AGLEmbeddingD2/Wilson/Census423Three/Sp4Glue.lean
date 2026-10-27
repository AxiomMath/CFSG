module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census423Three.GoodGroupPSL2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census423Three.DataGlue
public import CFSG.RankThree.PartTwo.Sec21.Item228Census5ProofSp4
public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofLieP
public import CFSG.LieType.SeitzGeneration.SpFourThree
public import CFSG.LieType.SeitzGeneration.SpFourScope
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.Quasithin.Background.C1PackNat
public import CFSG.Quasithin.Background.C1PackSolvBasic
public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofAlt

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census423Three

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 (Census423)
open CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.Item228Census3Proof
  CFSG.RankThree.PartTwo.Sec21.Item228Census5Proof
open CFSG.Assembly.RankThreeEven (projSL projSp)
open CFSG.Assembly.LowTwoRank (StatedSp StatedProj)
open Matrix

theorem noOrderThree_of_card {K : Type} [Field K] [Finite K]
    (h : Nat.card (K ≃+* K) ≤ 2) : ∀ σ : K ≃+* K, σ ^ 3 = 1 → σ = 1 := by
  intro σ hσ
  have hpos : 0 < Nat.card (K ≃+* K) := Nat.card_pos
  have h1 : orderOf σ ∣ Nat.card (K ≃+* K) := orderOf_dvd_natCard σ
  have h2 : orderOf σ ∣ 3 := orderOf_dvd_of_pow_eq_one hσ
  have h3 : orderOf σ = 1 ∨ orderOf σ = 3 := (Nat.dvd_prime Nat.prime_three).mp h2
  rcases h3 with h3 | h3
  · exact orderOf_eq_one_iff.mp h3
  · exfalso
    rw [h3] at h1
    have := Nat.le_of_dvd hpos h1
    omega

theorem pSp4CentThree_all (p : ℕ) [Fact p.Prime] (hp : 3 < p)
    (y : projSp 2 (GaloisField p 1)) (hy : orderOf y = 3) :
    Nonempty (inSubgroup perfectResidual (Subgroup.centralizer ({y} : Set (projSp 2
        (GaloisField p 1)))) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField p 1)) ∨
      Nonempty (inSubgroup perfectResidual (Subgroup.centralizer ({y} : Set (projSp 2
        (GaloisField p 1)))) ≃* projSL 2 (GaloisField p 1)) := by
  have hp' : p.Prime := Fact.out
  set K := GaloisField p 1
  have hKc : Nat.card K = p := by rw [GaloisField.card p 1 one_ne_zero, pow_one]
  have h2 : (2 : K) ≠ 0 := Item228Census2Proof.two_ne_zero_galoisField (by omega)
  have h3 : (3 : K) ≠ 0 := three_ne_zero_galoisField (by omega)
  set G := StatedSp 2 K with hG
  have hZ4 : ∀ u : Kˣ, GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) u ∈ G → u ^ 4 = 1 := by
    intro u hu
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_eq_one_of_scalar_mem_statedSp hu, one_pow]
  have hZ3 : ∀ u : Kˣ, GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) u ∈ G → u ^ 3 = 1 → u = 1 :=
    fun u hu h3' => by
      calc u = u ^ 4 * (u ^ 3)⁻¹ := by group
        _ = 1 := by rw [hZ4 u hu, h3', inv_one, one_mul]
  obtain ⟨A, hAy, hA3, hA1⟩ := exists_lift_cube G hZ4 y hy
  have hA3' : (A : GL (Fin 2 ⊕ Fin 2) K) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hA3, Subgroup.coe_one]
  have hA1' : (A : GL (Fin 2 ⊕ Fin 2) K) ≠ 1 := fun h => hA1 (Subtype.ext h)
  rcases centData_statedSp h2 h3 A.2 hA3' hA1' with ⟨φ, hφ, hker⟩ | ⟨φ, hφ, hker⟩
  · left
    have : Group.IsPerfect (SpecialLinearGroup (Fin 2) K) :=
      CFSG.ClassicalInvolution.sl2_isPerfect (by rw [hKc]; omega)
    obtain ⟨e⟩ := nonempty_perfectResidual_equiv_of_ker_bot G A hA3 hZ3 φ hφ hker
    rw [hAy] at e
    exact ⟨e⟩
  · right
    have : Group.IsPerfect (SpecialLinearGroup (Fin 2) K) :=
      CFSG.ClassicalInvolution.sl2_isPerfect (by rw [hKc]; omega)
    obtain ⟨e⟩ := nonempty_perfectResidual_equiv_projSL G A hA3 hZ3 φ hφ hker (MulEquiv.refl _)
    rw [hAy] at e
    exact ⟨e⟩

theorem fieldData_galoisField (p e : ℕ) [Fact p.Prime] (hp : 3 < p) (he : e = 1 ∨ e = 2) :
    Odd (Nat.card (GaloisField p e)) ∧ ringChar (GaloisField p e) ≠ 3 ∧
      5 ≤ Nat.card (GaloisField p e) ∧
      ∀ σ : GaloisField p e ≃+* GaloisField p e, σ ^ 3 = 1 → σ = 1 := by
  have hp' : p.Prime := Fact.out
  have he0 : e ≠ 0 := by rcases he with rfl | rfl <;> norm_num
  have hcard : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e he0
  have hp5 : 5 ≤ p := by
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp' (by norm_num)
    omega
  have hpodd : Odd p := hp'.odd_of_ne_two (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcard]; exact hpodd.pow
  · have : ringChar (GaloisField p e) = p := ringChar.eq (GaloisField p e) p
    omega
  · rw [hcard]
    calc 5 ≤ p := hp5
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right hp'.pos (by omega)
  · refine noOrderThree_of_card ?_
    have := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp'
      (GaloisField p e) hcard).1
    change Nat.card (RingAut (GaloisField p e)) ≤ 2
    rw [this]
    omega

theorem rank2_projSp (p : ℕ) [Fact p.Prime] (hp : 3 < p)
    (hs : IsSimpleGroup (projSp 2 (GaloisField p 1)))
    (hZ : Subgroup.center (projSp 2 (GaloisField p 1)) = ⊥) :
    Rank2 (projSp 2 (GaloisField p 1)) := by
  have : Finite (projSp 2 (GaloisField p 1)) := finite_projImage _
  have h := Sec4.Res417Three.pRank_projSp_two_le (p := p) (f := 1) (by omega) le_rfl hs
  have e' : projSp 2 (GaloisField p 1) ≃* projSp 2 (GaloisField p 1) ⧸
      Subgroup.center (projSp 2 (GaloisField p 1)) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
  exact rank2_of_mulEquiv e'.symm (rank2_of_pRank h)

theorem goodQ_projSp (p : ℕ) [Fact p.Prime] (hp : 3 < p) (d : projSp 2 (GaloisField p 1))
    (hd : orderOf d = 3) :
    ∃ (S : Type) (_ : Group S), GoodGroup S ∧ Nonempty (↥(qRes d) ≃* S) := by
  obtain ⟨hodd, h3, h5, hσ⟩ := fieldData_galoisField p 1 hp (Or.inl rfl)
  rcases pSp4CentThree_all p hp d hd with h | h
  · obtain ⟨e⟩ := h
    exact ⟨_, inferInstance, GoodGroup.sl2 hodd h3 h5 hσ, ⟨e⟩⟩
  · obtain ⟨e⟩ := h
    exact ⟨_, inferInstance, GoodGroup.psl2 h3 h5 hσ,
      ⟨e.trans (CFSG.RankThree.PartTwo.Sec4.projSLEquivPSL (GaloisField p 1))⟩⟩

theorem seitz_projSp (p : ℕ) [Fact p.Prime] (hp : 3 < p) (D : Subgroup (projSp 2 (GaloisField p 1)))
    (hDc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (hDexp : ∀ x ∈ D, x ^ 3 = 1)
    (hD9 : Nat.card D = 9) :
    (⊤ : Subgroup (projSp 2 (GaloisField p 1))) ≤ Subgroup.closure
      {x : projSp 2 (GaloisField p 1) |
        ∃ d ∈ D, d ≠ 1 ∧ x ∈ Subgroup.centralizer ({d} : Set (projSp 2 (GaloisField p 1)))} := by
  have hp' : p.Prime := Fact.out
  set K := GaloisField p 1
  have hKc : Nat.card K = p := by rw [GaloisField.card p 1 one_ne_zero, pow_one]
  have h3 : (3 : K) ≠ 0 := three_ne_zero_galoisField (by omega)
  have hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
    exact CFSG.LieType.SeitzGeneration.exists_ne_zero_one (by rw [hKc]; omega)
  let φ : projSp 2 K ≃* StatedProj (StatedSp 2 K) :=
    (CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage (StatedSp 2 K)).symm
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
  exact closure_centralizers_of_map φ D
    (CFSG.LieType.SeitzGeneration.closure_centralizers_psp_four_three h3 hK _ hE hX hC)

theorem census423_of_projSp {p : ℕ} [Fact p.Prime] (hp : 3 < p) {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] (hZ : Subgroup.center X = ⊥)
    (e : X ≃* projSp 2 (GaloisField p 1)) : Census423 X := by
  have : IsSimpleGroup (projSp 2 (GaloisField p 1)) := MulEquiv.isSimpleGroup e.symm
  have : Finite (projSp 2 (GaloisField p 1)) := finite_projImage _
  have hZM := Sec4.Res423Two.center_eq_bot_of_mulEquiv hZ e
  exact census423_of_data e hZM (rank2_projSp p hp inferInstance hZM) (goodQ_projSp p hp)
    (seitz_projSp p hp)

end CFSG.AGLEmbeddingD2.Wilson.Census423Three
