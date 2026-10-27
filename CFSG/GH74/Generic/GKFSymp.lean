module

public import CFSG.GH74.Generic.Front.SpFld
public import CFSG.Assembly.GL83LieDefs
public import CFSG.GH74.Generic.Context
public import CFSG.GH74.Generic.GKFTables
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Generic

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PerfectCover CFSG.Blueprint
  CFSG.Blueprint.Multiplier
open scoped Matrix

@[expose] noncomputable def pSp (n : ℕ) (F : Type) [Field F] :
    ↥(StatedSp n F) →* StatedProj (StatedSp n F) :=
  QuotientGroup.mk' ((StatedScalars (Fin n ⊕ Fin n) F).subgroupOf (StatedSp n F))

theorem pSp_surjective (n : ℕ) (F : Type) [Field F] : Function.Surjective (pSp n F) :=
  QuotientGroup.mk'_surjective _

theorem pSp_ker (n : ℕ) (F : Type) [Field F] : (pSp n F).ker = center ↥(StatedSp n F) := by
  rw [pSp, QuotientGroup.ker_mk']
  exact (CFSG.LieType.Universal.Symplectic.center_eq n F).symm

theorem negOneSp_mem_ker (F : Type) [Field F] : negOneSp F ∈ (pSp 2 F).ker := by
  rw [pSp_ker, CFSG.LieType.Universal.Symplectic.center_eq, Subgroup.mem_subgroupOf,
    StatedScalars, MonoidHom.mem_range]
  refine ⟨-1, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_scalar, coe_negOneSp, Units.val_neg, Units.val_one, map_neg,
    map_one]

theorem negOneSp_ne_one (F : Type) [Field F] (h : (-1 : F) ≠ 1) : negOneSp F ≠ 1 := by
  intro h1
  have h2 := congrArg (fun x : ↥(StatedSp 2 F) =>
    ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
      (Sum.inl 0) (Sum.inl 0)) h1
  simp [coe_negOneSp] at h2
  exact h h2

theorem classical_psp_of_lieModel {G : Type} [Group G] {n p f : ℕ} (hn : n ≠ 0)
    (h : CFSG.Models.LieModel G .PSp n p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      Nonempty (G ≃* StatedProj (StatedSp n F)) := by
  rcases h with ⟨-, ⟨-, hc⟩ | ⟨h0, -⟩⟩
  · exact hc
  · exact absurd h0 hn

open CFSG.ComponentClassification.TBLit in
theorem psp4_cover_of_griess (hGA : GriessMultipliersAllModels) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {K : Type} [Group K] [Finite K] (hK : IsQuasisimple K)
    (h2 : IsPGroup 2 ↥(center K)) (hm : CFSG.Models.LieModel (K ⧸ center K) .PSp 2 p f) :
    center K = ⊥ ∨ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      Nonempty (K ≃* StatedSp 2 F) := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := classical_psp_of_lieModel (by norm_num) hm
  have hoddp : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hodd : Odd (Nat.card F) := hcard ▸ hoddp
  have hmJ : CFSG.Models.LieModel (StatedProj (StatedSp 2 F)) .PSp 2 p f :=
    ⟨hm.1, Or.inl ⟨hm.1, F, inferInstance, inferInstance, hcard, ⟨MulEquiv.refl _⟩⟩⟩
  have hexc : exceptionalOrders .PSp 2 p f = (1, 1) := by
    unfold exceptionalOrders
    split <;> simp_all
  have h2gcd : Nat.gcd 2 (p ^ f - 1) = 2 := by
    obtain ⟨k, hk⟩ := hoddp
    exact Nat.gcd_eq_left ⟨k, by omega⟩
  have hcardM : Nat.card (hopfMultiplier (StatedProj (StatedSp 2 F))) = 2 := by
    rw [card_hopfMultiplier_of_griess hGA hmJ, hexc]
    have : genericOrders .PSp 2 p f = (2, 1) := Prod.ext h2gcd rfl
    rw [this]
    norm_num
  have hdvd := card_center_dvd_hopfMultiplier hK e
  rw [hcardM] at hdvd
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2'
  · exact Or.inl (Subgroup.eq_bot_of_card_eq _ h1)
  · refine Or.inr ⟨F, inferInstance, inferInstance, hcard, ?_⟩
    have hS₀ : Group.IsPerfect ↥(StatedSp 2 F) :=
      (CFSG.LieType.Universal.Symplectic.isQuasisimple_of_admissible 2 F hm.1 hcard).1
    have hpk : Nat.card (pSp 2 F).ker = 2 := by
      have hd := card_ker_dvd_hopfMultiplier hS₀ (pSp 2 F) (pSp_surjective 2 F)
        (pSp_ker 2 F).le
      rw [hcardM] at hd
      rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h2''
      · exfalso
        have hbot := Subgroup.eq_bot_of_card_eq _ h1
        have hmem := negOneSp_mem_ker F
        rw [hbot, Subgroup.mem_bot] at hmem
        have hne1 : (-1 : F) ≠ 1 :=
          Ring.neg_one_ne_one_of_char_ne_two (ringChar_ne_two_of_card_eq hp hp2 hcard)
        exact negOneSp_ne_one F hne1 hmem
      · exact h2''
    obtain ⟨α, hαs, hαc⟩ := exists_lift_of_odd_index hS₀ hK.1 (pSp 2 F) (pSp_surjective 2 F)
      (pSp_ker 2 F).le (centralQuotientMap e) (centralQuotientMap_surjective e)
      (centralQuotientMap_ker e).le (by rw [centralQuotientMap_ker e]; exact h2) 1 odd_one
      (by rw [hcardM, hpk, mul_one])
    have hcardS : Nat.card ↥(StatedSp 2 F) = Nat.card (StatedProj (StatedSp 2 F)) * 2 := by
      rw [card_eq_card_mul_card_ker (pSp 2 F) (pSp_surjective 2 F), hpk]
    have hcardK : Nat.card K = Nat.card (StatedProj (StatedSp 2 F)) * 2 := by
      rw [card_eq_card_mul_card_ker (centralQuotientMap e) (centralQuotientMap_surjective e),
        centralQuotientMap_ker e, h2']
    have hb : Function.Bijective α := hαs.bijective_of_nat_card_le (by rw [hcardS, hcardK])
    exact ⟨(MulEquiv.ofBijective α hb).symm⟩

end CFSG.GH74.Generic
