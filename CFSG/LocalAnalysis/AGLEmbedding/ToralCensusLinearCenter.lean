module

public import CFSG.Open.GriessAllModelsStatement
public import CFSG.GH74.Generic.GKFCover
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial

@[expose] def OddCenterLinear : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), IsComponentOf L ⊤ →
    Odd (Nat.card (Subgroup.center ↥L)) →
    ∀ (n : ℕ) (K : Type) [Field K] [Fintype K] [CharP K 2],
    Nonempty (↥L ⧸ Subgroup.center ↥L ≃* LinearFlag.projectiveSL n K) →
    Nat.card (Subgroup.center ↥L) ∣ Nat.gcd n (Fintype.card K - 1)

namespace ToralCensus

open LinearFlag

theorem subsingleton_projectiveSL {n : ℕ} (hn : n ≤ 1) (K : Type*) [Field K] :
    Subsingleton (projectiveSL n K) := by
  have : Subsingleton (Matrix.SpecialLinearGroup (Fin n) K) := by
    rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl <;> infer_instance
  exact (QuotientGroup.mk'_surjective (scalars n K)).subsingleton

theorem isSolvable_projectiveSL_two (K : Type) [Field K] [CharP K 2] (hK : Nat.card K = 2) :
    Group.IsSolvable (projectiveSL 2 K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) K) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable K
      (Or.inl hK)
  have : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) K) :=
    Group.isSolvable_of_isSolvable_injective Matrix.SpecialLinearGroup.toGL_injective
  exact Group.isSolvable_of_isSolvable_injective
    (f := (LinearCover.projectiveSLTwoEquivSL K).toMonoidHom)
    (LinearCover.projectiveSLTwoEquivSL K).injective

theorem two_le_of_mulEquiv_projectiveSL {X : Type*} [Group X] [Nontrivial X]
    [Group.IsPerfect X] {n : ℕ} {K : Type} [Field K] [CharP K 2] (e : X ≃* projectiveSL n K) :
    2 ≤ n ∧ ¬ (n = 2 ∧ Nat.card K = 2) := by
  constructor
  · by_contra hn
    have := subsingleton_projectiveSL (n := n) (by omega) K
    exact not_subsingleton X e.toEquiv.subsingleton
  · rintro ⟨rfl, hK⟩
    have := isSolvable_projectiveSL_two K hK
    have : Group.IsSolvable X :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact Group.IsPerfect.not_isSolvable X this

theorem statedClassicalModel_of_projectiveSL_evenChar {X : Type} [Group X] {n f : ℕ} {K : Type}
    [Field K] [Finite K] (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 2 ≤ n)
    (h22 : ¬ (n = 2 ∧ Nat.card K = 2)) (e : X ≃* projectiveSL n K) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL n 2 f := by
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL n 2 f := by
    refine ⟨Nat.prime_two, hf, hn, fun h => h22 ?_, fun h => ?_⟩
    · simp only [Prod.mk.injEq] at h
      exact ⟨h.1, hK.trans h.2⟩
    · simp only [Prod.mk.injEq] at h
      have h3 : 2 ^ f % 2 = 1 := by rw [h.2]
      rw [Nat.pow_mod, Nat.mod_self, zero_pow (by omega)] at h3
      exact absurd h3 (by norm_num)
  refine ⟨hadm, K, inferInstance, inferInstance, hK, ⟨?_⟩⟩
  exact e.trans ((LinearCover.projectiveSpecialLinearEquivProjectiveSL n K).symm.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K))

theorem lieModel_of_projectiveSL_evenChar {X : Type} [Group X] {n f : ℕ} {K : Type} [Field K]
    [Finite K]
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 2 ≤ n) (h22 : ¬ (n = 2 ∧ Nat.card K = 2))
    (e : X ≃* projectiveSL n K) :
    CFSG.Models.LieModel X .PSL n 2 f :=
  have hc := statedClassicalModel_of_projectiveSL_evenChar hf hK hn h22 e
  ⟨hc.1, Or.inl hc⟩

theorem exceptionalOrders_psl_two_dvd (n f : ℕ) :
    (CFSG.Blueprint.Multiplier.exceptionalOrders .PSL n 2 f).1 *
      (CFSG.Blueprint.Multiplier.exceptionalOrders .PSL n 2 f).2 ∣ 16 := by
  unfold CFSG.Blueprint.Multiplier.exceptionalOrders
  split <;> first | omega | norm_num

theorem card_multiplicative_zmod_eq (k : ℕ) : Nat.card (Multiplicative (ZMod k)) = k := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem exists_mul_ne_mul_of_perfect_nontrivial (X : Type*) [Group X] [Nontrivial X]
    [Group.IsPerfect X] :
    ∃ a b : X, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  exact Group.IsPerfect.not_isSolvable X (Group.isSolvable_of_comm hcon)

end ToralCensus

open ToralCensus in
theorem oddCenterLinear_of_griess (hGA : CFSG.Open.GriessAllModelsStatement) :
    OddCenterLinear := by
  intro Y _ _ L hL hodd n K _ _ _ ⟨e⟩
  have hq := hL.2.2
  have : Group.IsPerfect ↥L := ⟨hq.1⟩
  have hnt : Nontrivial (↥L ⧸ Subgroup.center ↥L) := hq.2.toNontrivial
  have : Group.IsPerfect (↥L ⧸ Subgroup.center ↥L) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center ↥L))
      (QuotientGroup.mk'_surjective _)
  obtain ⟨hn, h22⟩ := two_le_of_mulEquiv_projectiveSL e
  obtain ⟨f, -, hcard⟩ := FiniteField.card K 2
  have hKf : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hm := lieModel_of_projectiveSL_evenChar f.pos hKf hn h22 e
  obtain ⟨-, ⟨g⟩⟩ := hGA _ _ _ _ _ hm
  have hdvd := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier (K := ↥L)
    ⟨inferInstance, hq.2, exists_mul_ne_mul_of_perfect_nontrivial _⟩
    (MulEquiv.refl (↥L ⧸ Subgroup.center ↥L))
  rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
    Nat.card_congr g.toEquiv, Nat.card_prod, Nat.card_prod, Nat.card_prod,
    card_multiplicative_zmod_eq, card_multiplicative_zmod_eq, card_multiplicative_zmod_eq,
    card_multiplicative_zmod_eq] at hdvd
  have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSL n 2 f =
      (Nat.gcd n (2 ^ (f : ℕ) - 1), 1) := rfl
  rw [hgen, mul_one] at hdvd
  have hcop : (Nat.card (Subgroup.center ↥L)).Coprime
      ((CFSG.Blueprint.Multiplier.exceptionalOrders .PSL n 2 f).1 *
        (CFSG.Blueprint.Multiplier.exceptionalOrders .PSL n 2 f).2) :=
    Nat.Coprime.coprime_dvd_right (exceptionalOrders_psl_two_dvd n f)
      (by simpa using (Odd.coprime_two_right hodd).pow_right 4)
  rw [hcard]
  exact hcop.dvd_of_dvd_mul_right hdvd

end CFSG.AGLEmbedding
