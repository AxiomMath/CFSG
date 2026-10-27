module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDOrthOrder
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDFam
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamBCDOrthLevi

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup Matrix CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.LocalAnalysis.ComponentInitial

section Dot

variable {m : Type} [Fintype m] {K : Type} [Field K]

theorem dot_mulVec_transpose_mulVec [DecidableEq m] (A B : Matrix m m K) (h : B * A = 1)
    (x y : m → K) : (A *ᵥ x) ⬝ᵥ (Bᵀ *ᵥ y) = x ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec, h,
    Matrix.one_mulVec]

end Dot

section LeviD

variable (r : ℕ) (K : Type) [Field K]

theorem leviGL_injective : Function.Injective (leviGL r K) := fun a b h =>
  leviSp_injective r K (Subtype.ext h)

theorem quadPlus_leviGL (g : GL (Fin r) K) (v : Fin r ⊕ Fin r → K) :
    StatedQuadPlus r K ((leviGL r K g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v) =
      StatedQuadPlus r K v := by
  have hM : ((leviGL r K g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      fromBlocks (g : Matrix (Fin r) (Fin r) K) 0 0
        (((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ) := rfl
  rw [hM, fromBlocks_mulVec]
  simp only [StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, Sum.elim_inl, Sum.elim_inr,
    Matrix.zero_mulVec, add_zero, zero_add]
  exact dot_mulVec_transpose_mulVec _ _ (Units.inv_mul g) _ _

theorem quadPlus_smul (c : K) (w : Fin r ⊕ Fin r → K) :
    StatedQuadPlus r K (c • w) = c ^ 2 * StatedQuadPlus r K w := by
  simp only [StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem quadPlus_exists_one (hr : 1 ≤ r) : ∃ w : Fin r ⊕ Fin r → K, StatedQuadPlus r K w = 1 :=
  ⟨Sum.elim (Pi.single ⟨0, hr⟩ 1) (Pi.single ⟨0, hr⟩ 1), by
    simp [StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, Pi.single_apply]⟩

end LeviD

section D

variable {K : Type} [Field K] [Finite K] {p : ℕ} [hp : Fact p.Prime]

theorem crossAt_statedProj_D_odd (hp5 : 5 ≤ p) {r : ℕ} (hr : 1 ≤ r) (hpK : ¬ p ∣ Nat.card K)
    {e : ℕ} (he : 0 < e) (heo : Odd e) (hpe : ∀ j : ℕ, p ∣ Nat.card K ^ j - 1 ↔ e ∣ j)
    (hab : CFSG.IsElementaryAbelian 2
      (Abelianization (TauCeti.QuadraticMap.orthogonalGroup (quadPlus r K))))
    (hord : Nat.card (StatedProj (StatedOmega (StatedQuadPlus r K))) = ordD r (Nat.card K)) :
    (CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadPlus r K)))) = 2 →
      ∀ R : Sylow p (StatedProj (StatedOmega (StatedQuadPlus r K))),
        IsMulCommutative (R : Subgroup (StatedProj (StatedOmega (StatedQuadPlus r K))))) ∧
    (3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedOmega (StatedQuadPlus r K)))) →
      ∀ y : StatedProj (StatedOmega (StatedQuadPlus r K)), y ^ p = 1 →
        3 ≤ CFSG.Open.pRank p
          (centralizer ({y} : Set (StatedProj (StatedOmega (StatedQuadPlus r K)))))) := by
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  obtain ⟨w₀, hw₀⟩ := quadPlus_exists_one r K hr
  refine crossAt_statedProj_omega_levi (s := r) (e := e) hp5 hpK he hpe (coe_quadPlus r K) hab
    (quadPlus_smul r K) hw₀ (leviGL r K) (leviGL_injective r K) (quadPlus_leviGL r K) ?_
  rw [hord, padicValNat_card_GL_eq_sum hpK]
  exact padicValNat_ordD hp5 heo hpe (fun h => hpK h) hq1 hr

end D

section Family

theorem crossAtOn_of_core {d : TauCeti.ValidLieTypeIndex} {S : ℕ → Prop}
    (core : ∀ (L : Type) [Group L] [Finite L] (p : ℕ), p.Prime → 5 ≤ p → S p →
      d.1.characteristic ≠ p → Nonempty (L ≃* (TauCeti.CFSGIndex.lie d).Group) →
      (CFSG.Open.pRank p (⊤ : Subgroup L) = 2 →
        ∀ P : Sylow p L, IsMulCommutative (P : Subgroup L)) ∧
      (3 ≤ CFSG.Open.pRank p (⊤ : Subgroup L) → ∀ y : L, y ^ p = 1 →
        3 ≤ CFSG.Open.pRank p (centralizer ({y} : Set L)))) :
    CrossAtOn d S :=
  ⟨fun p hp hp5 hS hdp L _ _ _ hiso _ h2 P => (core L p hp hp5 hS hdp hiso).1 h2 P,
    fun p hp hp5 hS hdp L _ _ _ hiso _ h3 y hy =>
      (core L p hp hp5 hS hdp hiso).2 h3 y (hy ▸ pow_orderOf_eq_one y)⟩

theorem crossAtOn_D_odd {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.D r q).Valid) :
    CrossAtOn ⟨.D r q, hv⟩ (fun p => OddOrderAt (q.p ^ q.exponent) p) := by
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hr1 : 1 ≤ r := by omega
  refine crossAtOn_of_core fun L _ _ p hp hp5 hS hdp ⟨e⟩ => ?_
  haveI : Fact p.Prime := ⟨hp⟩
  have hdp' : q.p ≠ p := by simpa [TauCeti.LieTypeIndex.characteristic_D] using hdp
  have hmod : StatedClassicalModel L .POmegaPlus r q.p q.exponent :=
    statedClassicalModel_of_lieModel_of_ne_zero (by omega) (CFSG.Models.lieModel_D r q hv e)
  have hW := orthogonal_model_isometry_abelianization_order_bound
    L .POmegaPlus (Or.inr (Or.inl rfl)) r q.p q.exponent hmod
  have hcardL := CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical hmod
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hmod
  have hab := (hW K hK (quadPlus r K) (coe_quadPlus r K) e').1
  have hcard : Nat.card (StatedProj (StatedOmega (StatedQuadPlus r K))) =
      ordD r (Nat.card K) := by
    rw [← Nat.card_congr e'.toEquiv, hcardL, hK]
    rfl
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro h
    exact hdp' ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).1 (hp.dvd_of_dvd_pow h)).symm
  obtain ⟨e₀, he₀, heo, hpe⟩ := hS
  rw [← hK] at hpe
  exact cross_transport e' (crossAt_statedProj_D_odd hp5 hr1 hpK he₀ heo hpe hab hcard)

end Family

end CFSG.LocalAnalysis.RankFourTheoremC
