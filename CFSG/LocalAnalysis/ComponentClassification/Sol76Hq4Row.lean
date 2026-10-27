module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4Gen
public import CFSG.LocalAnalysis.ComponentClassification.Sol76Hq4Omega
public import CFSG.LieType.Steinberg.CentralExt.GriessAllModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ComponentClassification.Sol76T13.Hq4

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier
open CFSG.LieType.Steinberg.CentralExt

@[expose] def IsCentralFourRow (t : StatedLieTag) (n p f : ℕ) : Prop :=
  (t = .PSL ∧ n = 3 ∧ p = 2 ∧ f = 2) ∨ (t = .PSU ∧ n = 6 ∧ p = 2 ∧ f = 1) ∨
    (t = .POmegaPlus ∧ n = 4 ∧ p = 2 ∧ f = 1) ∨ (t = .twistedB2 ∧ n = 0 ∧ p = 2 ∧ f = 3) ∨
    (t = .twistedE6 ∧ n = 0 ∧ p = 2 ∧ f = 1) ∨ (t = .POmegaPlus ∧ p ≠ 2 ∧ Even n)

theorem not_two_dvd_generic_fst {t : StatedLieTag} {n f : ℕ}
    (hadm : StatedLieAdmissible t n 2 f) : ¬ 2 ∣ (genericOrders t n 2 f).1 := by
  have hf : 1 ≤ f := hadm.2.1
  have hev : Even (2 ^ f) := (Nat.even_pow' (by omega)).2 even_two
  have h4 : ∀ k, 1 ≤ k → ¬ 2 ∣ (2 ^ f) ^ k - 1 := by
    intro k hk
    rw [← even_iff_two_dvd, Nat.even_sub' (Nat.one_le_pow _ _ (by positivity))]
    simp [(Nat.even_pow' (by omega : k ≠ 0)).2 hev]
  have h3 : ∀ k, 1 ≤ k → ¬ 2 ∣ (2 ^ f) ^ k + 1 := by
    intro k hk
    rw [← even_iff_two_dvd, Nat.even_add_one, not_not]
    exact (Nat.even_pow' (by omega)).2 hev
  have h1 : ¬ 2 ∣ 2 ^ f - 1 := by simpa using h4 1 le_rfl
  have h2 : ¬ 2 ∣ 2 ^ f + 1 := by simpa using h3 1 le_rfl
  have g3 : ∀ a, ¬ 2 ∣ Nat.gcd 3 a := fun a h => by
    have := h.trans (Nat.gcd_dvd_left 3 a)
    omega
  cases t
  · exact fun h => h1 (h.trans (Nat.gcd_dvd_right _ _))
  · exact fun h => h2 (h.trans (Nat.gcd_dvd_right _ _))
  · exact fun h => h1 (h.trans (Nat.gcd_dvd_right _ _))
  · exact absurd rfl hadm.2.2.2
  · have : genericOrders .POmegaPlus n 2 f = (1, 1) := by
      simp only [genericOrders, hev, ↓reduceIte]
    rw [this]
    norm_num
  · exact fun h => h3 n (by have := hadm.2.2; omega) (h.trans (Nat.gcd_dvd_right _ _))
  all_goals first
    | (show ¬ 2 ∣ 1; norm_num)
    | (show ¬ 2 ∣ Nat.gcd 3 (2 ^ f - 1); exact g3 _)
    | (show ¬ 2 ∣ Nat.gcd 3 (2 ^ f + 1); exact g3 _)
    | (show ¬ 2 ∣ Nat.gcd 2 (2 ^ f - 1); exact fun h => h1 (h.trans (Nat.gcd_dvd_right _ _)))

theorem table_odd_of_not_row {t : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible t n p f)
    (h : ¬ IsCentralFourRow t n p f) :
    ¬ 2 ∣ (genericOrders t n p f).2 ∧ ¬ 2 ∣ (exceptionalOrders t n p f).2 ∧
      (¬ 2 ∣ (genericOrders t n p f).1 ∨ ¬ 2 ∣ (exceptionalOrders t n p f).1) := by
  have hf : 1 ≤ f := hadm.2.1
  refine ⟨?_, ?_, ?_⟩
  · cases t
    all_goals first
      | (show ¬ 2 ∣ 1; norm_num)
      | skip
    simp only [genericOrders]
    split_ifs with hq hn
    · norm_num
    · exfalso
      refine h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, ?_, hn⟩)))))
      rintro rfl
      exact hq ((Nat.even_pow' (by omega)).2 even_two)
    · norm_num
  · unfold IsCentralFourRow at h
    unfold exceptionalOrders
    split <;> simp_all
  · by_cases he : 2 ∣ (exceptionalOrders t n p f).1
    · left
      have hp : p = 2 := by
        revert he
        unfold exceptionalOrders
        split <;> simp_all
      subst hp
      exact not_two_dvd_generic_fst hadm
    · exact Or.inr he

theorem table_odd_pair_of_row {t : StatedLieTag} {n p f : ℕ} (h : IsCentralFourRow t n p f) :
    (¬ 2 ∣ (genericOrders t n p f).1 ∧ ¬ 2 ∣ (genericOrders t n p f).2) ∨
      (¬ 2 ∣ (exceptionalOrders t n p f).1 ∧ ¬ 2 ∣ (exceptionalOrders t n p f).2) := by
  rcases h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, hp, hn⟩
  · left; decide
  · left; decide
  · left; decide
  · left; decide
  · left; decide
  · right
    unfold exceptionalOrders
    split <;> simp_all

theorem exists_hom_range_eq_center {Q : Type} [Group Q] [Finite Q] (hQ : IsQuasisimple Q)
    {t : StatedLieTag} {n p f : ℕ} (hrow : GriessAll.GriessRow (Q ⧸ center Q) t n p f) :
    ∃ (_ : Finite (generic t n p f × exceptional t n p f))
      (φ : generic t n p f × exceptional t n p f →* Q), φ.range = center Q := by
  have : Group.IsPerfect Q := hQ.1
  have hS : Group.IsPerfect (Q ⧸ center Q) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (center Q))
      (QuotientGroup.mk'_surjective _)
  obtain ⟨-, ⟨e⟩⟩ := hrow
  obtain ⟨-, h, -, -, -, hmap, -⟩ :=
    RankThree.PerfectCover.perfect_central_kernel_quotient_of_hopf_multiplier
      (S := Q ⧸ center Q) (QuotientGroup.mk' (center Q)) (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk'])
  rw [QuotientGroup.ker_mk'] at hmap
  let E' := e.symm.trans (RankThree.PerfectCover.hopfMultiplierEquivGriess (Q ⧸ center Q))
  have : Finite (RankThree.PerfectCover.hopfMultiplier (Q ⧸ center Q)) :=
    RankThree.PerfectCover.finite_hopfMultiplier hS
  refine ⟨Finite.of_equiv _ E'.symm.toEquiv,
    h.comp ((RankThree.PerfectCover.hopfMultiplier _).subtype.comp E'.toMonoidHom), ?_⟩
  rw [MonoidHom.range_comp, MonoidHom.range_comp,
    MonoidHom.range_eq_top_of_surjective _ E'.surjective, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]
  exact hmap

theorem eq_of_center_involution_of_griessRow {Q : Type} [Group Q] [Finite Q]
    (hQ : IsQuasisimple Q) {t : StatedLieTag} {n p f : ℕ}
    (hrow : GriessAll.GriessRow (Q ⧸ center Q) t n p f) (hb : ¬ 2 ∣ (genericOrders t n p f).2)
    (hd : ¬ 2 ∣ (exceptionalOrders t n p f).2)
    (hac : ¬ 2 ∣ (genericOrders t n p f).1 ∨ ¬ 2 ∣ (exceptionalOrders t n p f).1) {u v : Q}
    (hu : u ∈ center Q) (hv : v ∈ center Q) (hu2 : u * u = 1) (hv2 : v * v = 1) (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) : u = v := by
  obtain ⟨_, φ, hφ⟩ := exists_hom_range_eq_center hQ hrow
  exact eq_of_involution_of_table φ hb hd hac (hφ ▸ hu) (hφ ▸ hv) hu2 hv2 hu1 hv1

theorem card_omegaCenter_le_four_of_griessRow {Q : Type} [Group Q] [Finite Q]
    (hQ : IsQuasisimple Q) {t : StatedLieTag} {n p f : ℕ}
    (hrow : GriessAll.GriessRow (Q ⧸ center Q) t n p f)
    (hodd : (¬ 2 ∣ (genericOrders t n p f).1 ∧ ¬ 2 ∣ (genericOrders t n p f).2) ∨
      (¬ 2 ∣ (exceptionalOrders t n p f).1 ∧ ¬ 2 ∣ (exceptionalOrders t n p f).2)) :
    Nat.card (omegaCenter Q) ≤ 4 := by
  obtain ⟨_, φ, hφ⟩ := exists_hom_range_eq_center hQ hrow
  have key : ∀ {A : Type} [Group A] (ι : A →* generic t n p f × exceptional t n p f),
      (∀ m, (∃ k : ℕ, m ^ (2 ^ k) = 1) → m ∈ ι.range) →
      Nat.card (omegaCenter Q) ≤ Nat.card {z : Q // z ∈ (φ.comp ι).range ∧ z * z = 1} := by
    intro A _ ι h2
    refine Nat.card_le_card_of_injective (fun z => ⟨z.1, ?_, z.2.2⟩) ?_
    · rw [MonoidHom.range_comp]
      exact mem_map_of_involution φ h2 (hφ ▸ z.2.1) z.2.2
    · intro a b hab
      apply Subtype.ext
      have h := congrArg Subtype.val hab
      exact h
  rcases hodd with ⟨ha, hb⟩ | ⟨hc, hd⟩
  · exact (key _ (mem_range_inr_of_odd ha hb)).trans (card_sq_eq_one_le_four _)
  · exact (key _ (mem_range_inl_of_odd hc hd)).trans (card_sq_eq_one_le_four _)

theorem four_le_card_omegaCenter {Q : Type} [Group Q] [Finite Q] {u v : Q} (hu : u ∈ center Q)
    (hv : v ∈ center Q) (hu2 : u * u = 1) (hv2 : v * v = 1) (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (huv : u ≠ v) : 4 ≤ Nat.card (omegaCenter Q) := by
  classical
  have := Fintype.ofFinite (omegaCenter Q)
  have huΩ : u ∈ omegaCenter Q := ⟨hu, hu2⟩
  have hvΩ : v ∈ omegaCenter Q := ⟨hv, hv2⟩
  have huvΩ : u * v ∈ omegaCenter Q := mul_mem huΩ hvΩ
  have h1 : u * v ≠ 1 := by
    intro h
    apply huv
    calc u = u * (v * v) := by rw [hv2, mul_one]
      _ = u * v * v := by group
      _ = v := by rw [h, one_mul]
  have h2 : u * v ≠ u := fun h => hv1 (by
    calc v = u⁻¹ * (u * v) := by group
      _ = 1 := by rw [h, inv_mul_cancel])
  have h3 : u * v ≠ v := fun h => hu1 (by
    calc u = u * v * v⁻¹ := by group
      _ = 1 := by rw [h, mul_inv_cancel])
  have hcard : ({⟨1, one_mem _⟩, ⟨u, huΩ⟩, ⟨v, hvΩ⟩, ⟨u * v, huvΩ⟩} :
      Finset (omegaCenter Q)).card = 4 := by
    rw [Finset.card_eq_succ]
    refine ⟨⟨1, one_mem _⟩, {⟨u, huΩ⟩, ⟨v, hvΩ⟩, ⟨u * v, huvΩ⟩}, ?_, rfl, ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq, not_or]
      exact ⟨Ne.symm hu1, Ne.symm hv1, Ne.symm h1⟩
    · rw [Finset.card_eq_three]
      exact ⟨_, _, _, fun h => huv (congrArg Subtype.val h),
        fun h => h2 (congrArg Subtype.val h).symm, fun h => h3 (congrArg Subtype.val h).symm, rfl⟩
  rw [Nat.card_eq_fintype_card, ← hcard]
  exact Finset.card_le_univ _

theorem card_omegaCenter_eq_four {Q : Type} [Group Q] [Finite Q]
    (h4 : Nat.card (omegaCenter Q) ≤ 4) {u v : Q} (hu : u ∈ center Q) (hv : v ∈ center Q)
    (hu2 : u * u = 1) (hv2 : v * v = 1) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v) :
    Nat.card (omegaCenter Q) = 4 :=
  le_antisymm h4 (four_le_card_omegaCenter hu hv hu2 hv2 hu1 hv1 huv)

theorem clause_two_of_griessRow {Q : Type} [Group Q] [Finite Q] (hQ : IsQuasisimple Q)
    {t : StatedLieTag} {n p f : ℕ} (hrow : GriessAll.GriessRow (Q ⧸ center Q) t n p f)
    (hodd : (¬ 2 ∣ (genericOrders t n p f).1 ∧ ¬ 2 ∣ (genericOrders t n p f).2) ∨
      (¬ 2 ∣ (exceptionalOrders t n p f).1 ∧ ¬ 2 ∣ (exceptionalOrders t n p f).2))
    {u v : Q} (hu : u ∈ center Q) (hv : v ∈ center Q) (hu2 : u * u = 1) (hv2 : v * v = 1)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v) {x : Q} (hx : x * x = 1)
    (h16 : 4 ≤
      (Nat.card ↥(centralizer ({(x : Q ⧸ center Q)} : Set (Q ⧸ center Q)))).factorization 2) :
    (Nat.card ↥(center Q)).factorization 2 + 2 ≤
      (Nat.card ↥(centralizer ({x} : Set Q))).factorization 2 :=
  two_add_le_of_sixteen (card_omegaCenter_eq_four
    (card_omegaCenter_le_four_of_griessRow hQ hrow hodd) hu hv hu2 hv2 hu1 hv1 huv) hx h16

theorem exists_noncentral_involution_of_pRank {Q : Type} [Group Q] [Finite Q]
    (h4 : Nat.card (omegaCenter Q) ≤ 4) (h3 : 3 ≤ CFSG.pRank 2 Q) :
    ∃ x : Q, orderOf x = 2 ∧ x ∉ center Q := by
  rw [SectionRank.pRank_eq_open_pRank_top] at h3
  obtain ⟨E, -, hE, hEcard⟩ := SectionRank.exists_pRank one_lt_two (⊤ : Subgroup Q)
  have hE8 : 8 ≤ Nat.card E := by
    rw [hEcard]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 (⊤ : Subgroup Q) := Nat.pow_le_pow_right (by norm_num) h3
  by_contra hcon
  push Not at hcon
  have hle : E ≤ omegaCenter Q := by
    intro x hx
    have hx2 : x * x = 1 := by rw [← pow_two]; exact hE.2 x hx
    by_cases hx1 : x = 1
    · rw [hx1]; exact one_mem _
    · exact ⟨hcon x (orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1), hx2⟩
  have := Subgroup.card_le_of_le hle
  omega

end CFSG.ComponentClassification.Sol76T13.Hq4
