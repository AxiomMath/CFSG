module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreUnits
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreMonEmb
public import CFSG.GroupTheory.WeirSylow.Unitary
public import CFSG.Sporadic.J4.QT2LocHGen

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.ACore

open CFSG.SectionRank.OddCover CFSG.Quasithin CFSG.GroupTheory.WeirSylow

theorem exists_conj_mem_of_factorization_eq {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (K : Subgroup G) [Finite K] (P₀ H : Subgroup G) (hP₀K : P₀ ≤ K) (hHK : H ≤ K)
    (hP₀ : (Nat.card P₀).factorization p = (Nat.card K).factorization p) (hH : IsPGroup p H) :
    ∃ g ∈ K, ∀ x ∈ H, g * x * g⁻¹ ∈ P₀ := by
  obtain ⟨S₁⟩ := (inferInstance : Nonempty (Sylow p (P₀.subgroupOf K)))
  have hcard : Nat.card ((S₁ : Subgroup (P₀.subgroupOf K)).map (P₀.subgroupOf K).subtype) =
      p ^ (Nat.card K).factorization p := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), S₁.card_eq_multiplicity,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₀K).toEquiv, hP₀]
  have hH' : IsPGroup p (H.subgroupOf K) := by
    rw [← Subgroup.comap_subtype]
    exact hH.comap_subtype
  obtain ⟨g, hg⟩ := CFSG.Sporadic.J4.QT2.exists_conj_le_of_card _ (H.subgroupOf K) hcard hH'
  refine ⟨g, g.2, fun x hx => ?_⟩
  obtain ⟨y, -, hy⟩ := Subgroup.mem_map.1 (hg ⟨x, hHK hx⟩ (Subgroup.mem_subgroupOf.2 hx))
  have hy' : ((y : K) : G) = (g : G) * x * (g : G)⁻¹ := by
    simpa using congrArg Subtype.val hy
  rw [← hy']
  exact Subgroup.mem_subgroupOf.1 y.2

theorem factorization_card_range_monEmb {F : Type} [Field F] {r : ℕ} [Fact r.Prime] {a : ℕ}
    (ha : Nat.card (unitsPPart F r) = r ^ a) (m : ℕ) :
    (Nat.card (monEmb (unitsPPart F r).subtype m).range).factorization r =
      a * m + padicValNat r m.factorial := by
  have hinj := monEmb_injective (F := F) (unitsPPart F r).subtype_injective m
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, card_mon, ha, ← pow_mul,
    Nat.factorization_def _ Fact.out,
    padicValNat.mul (pow_ne_zero _ (Fact.out : r.Prime).ne_zero) (Nat.factorial_ne_zero m),
    padicValNat.prime_pow]

theorem exists_conj_monomial_GL {F : Type} [Field F] [Fintype F] {r m : ℕ} [Fact r.Prime]
    (hr : r ≠ 2) (hrF : r ∣ Fintype.card F - 1) (hm : 1 ≤ m)
    (H : Subgroup (GL (Fin m) F)) (hH : IsPGroup r H) :
    ∃ g : GL (Fin m) F, ∀ x ∈ H,
      g * x * g⁻¹ ∈ (monEmb (unitsPPart F r).subtype m).range := by
  have hp : r.Prime := Fact.out
  have hcF : ¬ r ∣ Fintype.card F := fun h => by
    have h1 : r ∣ Fintype.card F - (Fintype.card F - 1) := Nat.dvd_sub h hrF
    rw [Nat.sub_sub_self Fintype.card_pos] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have h1 : ((Fintype.card F - 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hrF
  have hF1 : ((Fintype.card F : ℕ) : ZMod r) = 1 := by
    have : Fintype.card F = (Fintype.card F - 1) + 1 := (Nat.sub_add_cancel Fintype.card_pos).symm
    rw [this, Nat.cast_add, h1, Nat.cast_one, zero_add]
  have hfac : (Nat.card (monEmb (unitsPPart F r).subtype m).range).factorization r =
      (Nat.card (⊤ : Subgroup (GL (Fin m) F))).factorization r := by
    rw [Subgroup.card_top, factorization_card_GL (hp.odd_of_ne_two hr) F hcF m, hF1,
      orderOf_one, pow_one, Nat.div_one, factorization_card_range_monEmb (card_unitsPPart F r)]
  obtain ⟨g, -, hg⟩ := exists_conj_mem_of_factorization_eq ⊤ _ H le_top le_top hfac hH
  exact ⟨g, hg⟩

theorem range_monEmb_le_statedGU {F : Type} [Field F] [Fintype F] {q r m : ℕ} [Fact r.Prime]
    (hr : r ≠ 2) (hF : Fintype.card F = q ^ 2) (hrq : r ∣ q + 1) :
    (monEmb (unitsPPart F r).subtype m).range ≤ StatedGU m q F := by
  rintro _ ⟨x, rfl⟩
  refine monEmb_mem_statedGU _ (by have := two_le_of_card_eq_sq hF; omega) (fun z => ?_) x
  rw [Subgroup.subtype_apply, ← Units.val_pow_eq_pow_val,
    pow_add_one_eq_one_of_mem_unitsPPart hr hF hrq z.2, Units.val_one]

theorem exists_conj_monomial_GU {F : Type} [Field F] [Fintype F] {q r m : ℕ} [Fact r.Prime]
    (hr : r ≠ 2) (hF : Fintype.card F = q ^ 2) (hrq : r ∣ q + 1) (hm : 1 ≤ m)
    (H : Subgroup (GL (Fin m) F)) (hHU : H ≤ StatedGU m q F) (hH : IsPGroup r H) :
    ∃ g ∈ StatedGU m q F, ∀ x ∈ H,
      g * x * g⁻¹ ∈ (monEmb (unitsPPart F r).subtype m).range := by
  have hp : r.Prime := Fact.out
  have hcq : ¬ r ∣ q := fun h => by
    have h1 : r ∣ q + 1 - q := Nat.dvd_sub hrq h
    rw [Nat.add_sub_cancel_left] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hq1 : (q : ZMod r) + 1 = 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff _ _).2 hrq
  have hneg : -(q : ZMod r) = 1 := neg_eq_of_add_eq_zero_right hq1
  have hval : padicValInt r ((-(q : ℤ)) ^ 1 - 1) = padicValNat r (q + 1) := by
    rw [pow_one, show -(q : ℤ) - 1 = -((q + 1 : ℕ) : ℤ) by push_cast; ring, padicValInt,
      Int.natAbs_neg, Int.natAbs_natCast]
  have hfac : (Nat.card (monEmb (unitsPPart F r).subtype m).range).factorization r =
      (Nat.card (StatedGU m q F)).factorization r := by
    rw [factorization_card_statedGU (hp.odd_of_ne_two hr) F hF hcq hm, hneg, orderOf_one, hval,
      Nat.div_one, factorization_card_range_monEmb (card_unitsPPart_of_dvd_add_one hr hF hrq)]
  exact exists_conj_mem_of_factorization_eq _ _ H (range_monEmb_le_statedGU hr hF hrq) hHU hfac hH

end CFSG.LocalAnalysis.RankThreeUC.S15.ACore
