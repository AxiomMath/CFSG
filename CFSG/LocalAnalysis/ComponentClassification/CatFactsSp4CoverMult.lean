module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4CoverCore
public import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup

theorem models_lieModel_of_lieModel_psp {X : Type} [Group X] {p f : ℕ}
    (hm : Blueprint.LieModel X .PSp 2 p f) : Models.LieModel X .PSp 2 p f := by
  rcases hm with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact ⟨hc.1, .inl hc⟩
  all_goals exact absurd h0 (by decide)

theorem card_multiplier_table_psp_two {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Nat.card (Blueprint.Multiplier.generic .PSp 2 p f ×
      Blueprint.Multiplier.exceptional .PSp 2 p f) = 2 := by
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hgcd : Nat.gcd 2 (p ^ f - 1) = 2 := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk, Nat.add_sub_cancel]
    exact Nat.gcd_eq_left (dvd_mul_right 2 k)
  have hgen : Blueprint.Multiplier.genericOrders .PSp 2 p f = (2, 1) := by
    change (Nat.gcd 2 (p ^ f - 1), 1) = (2, 1)
    rw [hgcd]
  have hexc : Blueprint.Multiplier.exceptionalOrders .PSp 2 p f = (1, 1) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp

theorem card_griessHopfMultiplier_psp_two
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {X : Type} [Group X] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : Models.LieModel X .PSp 2 p f) :
    Nat.card (Open.griessHopfMultiplier X) = 2 := by
  obtain ⟨e⟩ := (hGA X .PSp 2 p f hm).2
  rw [Nat.card_congr e.toEquiv, card_multiplier_table_psp_two hp hp2]

theorem card_center_dvd_hopfMultiplier {S : Type} [Group S] {Q : Type} [Group Q]
    [Group.IsPerfect Q] (e : Q ⧸ center Q ≃* S) :
    Nat.card (center Q) ∣ Nat.card (RankThree.PerfectCover.hopfMultiplier S) := by
  let q : Q →* S := e.toMonoidHom.comp (QuotientGroup.mk' (center Q))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = center Q := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (center Q) x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hmap := RankThree.PerfectCover.map_hopfMultiplier_hopfLift q hq hker.le
  rw [← hker, ← hmap]
  exact Subgroup.card_map_dvd (H := RankThree.PerfectCover.hopfMultiplier S)
    (RankThree.PerfectCover.hopfLift q hq hker.le)

theorem card_center_statedSp (K : Type) [Field K] (h2 : (2 : K) ≠ 0) :
    Nat.card (center (StatedSp 2 K)) = 2 := by
  rw [LieType.Universal.Symplectic.center_eq]
  exact card_spScalars h2

theorem exists_mulEquiv_statedSp
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hGC : type_of% @Milestones.cl_lit_griess_schur_multipliers_central_covers)
    {Y : Type} [Group Y] [Finite Y] (hY : CFSG.IsQuasisimple Y) (hZ : center Y ≠ ⊥)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : Blueprint.LieModel (Y ⧸ center Y) .PSp 2 p f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = p ^ f ∧
      Nonempty (Y ≃* StatedSp 2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm' := models_lieModel_of_lieModel_psp hm
  have hcardM := card_griessHopfMultiplier_psp_two hGA hp hp2 hm'
  have : Finite (Open.griessHopfMultiplier (Y ⧸ center Y)) :=
    Nat.finite_of_card_ne_zero (by rw [hcardM]; exact two_ne_zero)
  have hS2 : ∀ S : Sylow 2 (Open.griessHopfMultiplier (Y ⧸ center Y)), Nat.card S = 2 := by
    intro S
    rw [Sylow.card_eq_multiplicity, hcardM, Nat.Prime.factorization_self Nat.prime_two, pow_one]
  obtain ⟨-, hcov2⟩ := hGC (Y ⧸ center Y) .PSp 2 p f hm'
  have : Group.IsPerfect Y := hY.1
  have hcardZ : Nat.card (center Y) = 2 := by
    have hdvd := card_center_dvd_hopfMultiplier (MulEquiv.refl (Y ⧸ center Y))
    rw [Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess _).symm.toEquiv,
      hcardM] at hdvd
    have h1 : 1 < Nat.card (center Y) := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      exact hZ
    have h2 := Nat.le_of_dvd two_pos hdvd
    omega
  obtain ⟨-, hadm, K, _, _, hK, ⟨eK⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ := hm
  rotate_left
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  · exact absurd h0 (by decide)
  have hKodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hKodd
  obtain ⟨eY⟩ := hcov2 hS2 Y (StatedSp 2 K) hY
    (LieType.Universal.Symplectic.isQuasisimple_of_admissible 2 K hadm hK) hcardZ
    (card_center_statedSp K h2K)
    ⟨MulEquiv.refl _⟩ ⟨(LieType.Universal.Symplectic.centerQuotientEquiv 2 K).trans eK.symm⟩
  exact ⟨K, inferInstance, inferInstance, hK, ⟨eY⟩⟩

theorem center_quotient_ne_bot_of_le {G : Type} [Group G] [Finite G] {Y : Subgroup G}
    {K : Type} [Field K] (h2 : (2 : K) ≠ 0) (eY : Y ≃* StatedSp 2 K) {C M : Subgroup G}
    (hMC : M ≤ C) (hMY : M ≤ Y) (hM : CFSG.IsPComponent 2 (M.subgroupOf C)) :
    center (M ⧸ pPrimeCore 2 M) ≠ ⊥ := by
  have e : M.subgroupOf C ≃* M := subgroupOfEquivOfLe hMC
  set ι : M →* StatedSp 2 K := eY.toMonoidHom.comp (Subgroup.inclusion hMY) with hιdef
  have hι : Function.Injective ι := eY.injective.comp (Subgroup.inclusion_injective hMY)
  have hneg : negS K ∈ center (StatedSp 2 K) :=
    mem_center_of_mem_spScalars ((mem_spScalars_iff _).mpr (Or.inr rfl))
  have hcent : ∀ w : M, ι w = negS K → w ∈ center M := by
    intro w hw
    rw [mem_center_iff]
    intro m
    apply hι
    rw [map_mul, map_mul, hw]
    exact mem_center_iff.mp hneg (ι m)
  have hsq : ∀ x : M, orderOf x = 2 → ι x * ι x = 1 := by
    intro x hx
    have hx2 : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
    rw [← map_mul, hx2, map_one]
  have hne1 : ∀ x : M, orderOf x = 2 → ι x ≠ 1 := by
    intro x hx h
    rw [← map_one ι] at h
    rw [hι h, orderOf_one] at hx
    norm_num at hx
  apply center_quotient_ne_bot
  · have := CatalogueBAlternating.pComponent_perfect hM
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  · have := even_card_of_isPComponent hM
    rwa [Nat.card_congr e.toEquiv] at this
  · intro x y hx hy hxy hne
    have hxy' : ι x * ι y = ι y * ι x := by rw [← map_mul, ← map_mul, hxy]
    rcases neg_one_mem_of_four_group h2 (hsq x hx) (hsq y hy) hxy' (hne1 x hx) (hne1 y hy)
      (fun h => hne (hι h)) with h | h | h
    · exact ⟨x, hcent x h, hx⟩
    · exact ⟨y, hcent y h, hy⟩
    · refine ⟨x * y, hcent _ (by rw [map_mul]; exact h), orderOf_eq_prime ?_ ?_⟩
      · have hx2 : x ^ 2 = 1 := by rw [← hx, pow_orderOf_eq_one]
        have hy2 : y ^ 2 = 1 := by rw [← hy, pow_orderOf_eq_one]
        calc (x * y) ^ 2 = x * (y * x) * y := by rw [pow_two]; simp only [mul_assoc]
          _ = x * (x * y) * y := by rw [hxy]
          _ = x ^ 2 * y ^ 2 := by rw [pow_two, pow_two]; simp only [mul_assoc]
          _ = 1 := by rw [hx2, hy2, one_mul]
      · intro h1
        apply hne
        have hy2 : y * y = 1 := by rw [← pow_two, ← hy, pow_orderOf_eq_one]
        calc x = x * y * y := by rw [mul_assoc, hy2, mul_one]
          _ = y := by rw [h1, one_mul]

end CFSG.ComponentClassification.CatFactsSp4
