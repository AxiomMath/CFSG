module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LpEpsLin

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance Matrix
open CFSG.HardMathSupport.Timmesfeld.Coordinator
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCLinearSubfield
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.HardMathSupport.Lang.UnitaryAutomorphisms (higher_linear_prime_semilinear_field_descent')
open CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL (mem_semilinearAutGroup_of_odd)
open CFSG.HardMathSupport.Timmesfeld.CrossChar

section Orders

theorem exists_dvd_pow_sub_one_of_dvd_card_GL {n p : ℕ} (hp : p.Prime) {F : Type} [Field F]
    [Finite F] (hpF : ¬ p ∣ Nat.card F) (h : p ∣ Nat.card (GL (Fin n) F)) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ n ∧ p ∣ Nat.card F ^ j - 1 := by
  have : Fintype F := Fintype.ofFinite F
  rw [Matrix.card_GL_field] at h
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 h
  have hq : Fintype.card F ^ n - Fintype.card F ^ (i : ℕ) =
      Fintype.card F ^ (i : ℕ) * (Fintype.card F ^ (n - i) - 1) := by
    have hpow : Fintype.card F ^ n = Fintype.card F ^ (i : ℕ) * Fintype.card F ^ (n - i) := by
      rw [← pow_add]; congr 1; have := i.2; omega
    rw [Nat.mul_sub, mul_one, ← hpow]
  rw [hq] at hi
  refine ⟨n - i, by have := i.2; omega, by omega, ?_⟩
  rcases (Nat.Prime.dvd_mul hp).1 hi with h1 | h1
  · exact absurd ((Nat.Prime.dvd_of_dvd_pow hp h1).trans (by rw [Nat.card_eq_fintype_card])) hpF
  · rwa [Nat.card_eq_fintype_card]

theorem dvd_card_projectiveSL_of_dvd_pow_sub_one {n p j : ℕ} (hp : p.Prime) (hn : 3 ≤ n)
    {E : Type} [Field E] [Finite E] (hj1 : 1 ≤ j) (hjn : j ≤ n)
    (h : p ∣ Nat.card E ^ j - 1) : p ∣ Nat.card (projectiveSL n E) := by
  by_cases hpq : p ∣ Nat.card E - 1
  · exact dvd_card_projectiveSL_of_dvd_card_sub_one hp hn hpq
  · have hSL := dvd_card_SL_of_dvd_pow_sub_one (m := n) hp hpq hj1 hjn h
    have hcard : Nat.card (SpecialLinearGroup (Fin n) E) =
        Nat.card (projectiveSL n E) * Nat.card (scalars n E) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (scalars n E)
    have hZ : ¬ p ∣ Nat.card (scalars n E) := fun hd => hpq (by
      rw [scalars_eq_center] at hd
      exact hd.trans ((CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd (by omega) E).trans
        (Nat.gcd_dvd_right _ _)))
    rw [hcard] at hSL
    exact (Nat.Prime.dvd_mul hp).1 hSL |>.resolve_right hZ

theorem dvd_card_projectiveSL_of_dvd_card_GL {n p : ℕ} (hp : p.Prime) (hn : 3 ≤ n) {F : Type}
    [Field F] [Finite F] {E : Type} [Field E] [Finite E]
    (hcard : Nat.card F = Nat.card E ^ p) (hpE : ¬ p ∣ Nat.card E)
    (h : p ∣ Nat.card (GL (Fin n) F)) : p ∣ Nat.card (projectiveSL n E) := by
  have hpF : ¬ p ∣ Nat.card F := fun hd => hpE (hp.dvd_of_dvd_pow (hcard ▸ hd))
  obtain ⟨j, hj1, hjn, hj⟩ := exists_dvd_pow_sub_one_of_dvd_card_GL hp hpF h
  refine dvd_card_projectiveSL_of_dvd_pow_sub_one hp hn hj1 hjn ?_
  have : Fact p.Prime := ⟨hp⟩
  have hq1 : 1 ≤ Nat.card E := Finite.card_pos
  rw [hcard] at hj
  rw [← ZMod.natCast_eq_zero_iff] at hj ⊢
  have hpos1 : 1 ≤ (Nat.card E ^ p) ^ j := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hq1)
  have hpos2 : 1 ≤ Nat.card E ^ j := Nat.one_le_pow _ _ hq1
  rw [Nat.cast_sub hpos1, Nat.cast_pow, Nat.cast_pow, Nat.cast_one] at hj
  rw [Nat.cast_sub hpos2, Nat.cast_pow, Nat.cast_one]
  have h2 : ((Nat.card E : ZMod p) ^ p) ^ j = ((Nat.card E : ZMod p) ^ j) ^ p := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  rw [h2, ZMod.pow_card] at hj
  exact hj

end Orders

section Outer

variable {n : ℕ} {F : Type} [Field F] [Finite F]

theorem localDeltaIn_eq_bot_of_conj_fieldAut' (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime)
    {σ : F ≃+* F} (hσ : orderOf σ = p)
    (hpT : p ∣ Nat.card (projectiveSL n (semilinearFixedSubfield σ)))
    {H D : Subgroup (MulAut (projectiveSL n F))} (hH : innerAut (projectiveSL n F) ≤ H)
    {x : MulAut (projectiveSL n F)} (hx : x ∈ D) (h : MulAut (projectiveSL n F))
    (hxh : x = h * fieldAut n F σ * h⁻¹) : localDeltaIn p H D = ⊥ := by
  set k := semilinearFixedSubfield σ with hkdef
  have hk : ∀ c, c ∈ k ↔ σ c = c := fun c => RingHom.mem_eqLocusField
  have hinj := CFSG.RankThree.RegularUnipotent.conj_injective_projectiveSL (k := F) hn
  have hx1 : x ≠ 1 := by
    rintro rfl
    have h1 : fieldAut n F σ = 1 := by
      calc fieldAut n F σ = h⁻¹ * (h * fieldAut n F σ * h⁻¹) * h := by group
        _ = 1 := by rw [← hxh, mul_one, inv_mul_cancel]
    have h2 : σ = 1 := fieldAut_injective hn (by rw [h1, map_one])
    rw [h2, orderOf_one] at hσ
    exact hp.one_lt.ne hσ
  refine localDeltaIn_eq_bot_of_conj_normal_quasisimple_fixSub hp hinj hH hx hx1 h
    (fieldAut n F σ) hxh (linearSubfieldInclusion n k).range ?_ ?_
    (isQuasisimple_range_linearSubfieldInclusion hn k) ?_ ?_
  · rintro _ ⟨y, rfl⟩
    exact fieldAut_linearSubfieldInclusion (fun c hc => (hk c).1 hc) y
  · intro a ha t ht
    exact conj_mem_range_linearSubfieldInclusion σ ha ht
  · rw [← Nat.card_congr (MonoidHom.ofInjective (linearSubfieldInclusion_injective
      (by omega) k)).toEquiv]
    exact hpT
  · intro g hg hfix
    have hmem : g ∈ fixingSubgroup (MulAut (projectiveSL n F))
        ((linearSubfieldInclusion n k).range : Set (projectiveSL n F)) :=
      (mem_fixingSubgroup_iff _).2 fun y hy => hfix y hy
    rw [fixingSubgroup_range_linearSubfieldInclusion hk hn] at hmem
    have hdvd : orderOf g ∣ p := by
      rw [← hσ, ← orderOf_fieldAut hn σ]
      exact orderOf_dvd_of_mem_zpowers hmem
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hg.symm hdvd)

theorem localDeltaIn_eq_bot_of_not_le_linearAutGroup_two (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpF : ¬ p ∣ Nat.card F) {D : Subgroup (MulAut (projectiveSL n F))}
    (hD : IsElemAbelian p D) (hcard : Nat.card D = p ^ 2) (hDl : ¬ D ≤ linearAutGroup n F)
    {H : Subgroup (MulAut (projectiveSL n F))} (hH : innerAut (projectiveSL n F) ≤ H) :
    localDeltaIn p H D = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨x, hx, hxl⟩ := IsConcreteLE.not_le_iff_exists.1 hDl
  have hxp := hD.2 x hx
  have hxE : x ∈ semilinearAutGroup n F := by
    refine mem_semilinearAutGroup_of_odd hn ?_
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hxp) with h | h
    · rw [h]; exact odd_one
    · rw [h]; exact hp.odd_of_ne_two hp2
  have hx1 : x ≠ 1 := fun h => hxl (h ▸ (linearAutGroup n F).one_mem)
  obtain ⟨C, _, hC, α, hα⟩ := exists_cyclic_quotient_linear hn hp hp2 D hD
  have hDfin : Finite D :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)
  have hle := card_le_mul_card_ker' hp (fun h : D => Subtype.ext (hD.2 h h.2)) α
  obtain ⟨y, hyker, hy1⟩ : ∃ y ∈ α.ker, y ≠ 1 := by
    by_contra hno
    push Not at hno
    have hbot : α.ker = ⊥ := eq_bot_iff.2 fun z hz => (Subgroup.mem_bot).2 (hno z hz)
    rw [hbot, Subgroup.card_bot] at hle
    rw [hcard] at hle
    have : p ^ 2 = p * p := by ring
    have := hp.two_le
    nlinarith
  obtain ⟨M, hM⟩ := hα y (MonoidHom.mem_ker.1 hyker)
  have hyord : orderOf (conjAut n F M) = p := by
    rw [hM]
    have : (y : MulAut (projectiveSL n F)) ^ p = 1 := hD.2 y y.2
    refine orderOf_eq_prime this ?_
    intro h1
    exact hy1 (Subtype.ext h1)
  have hGL : p ∣ Nat.card (GL (Fin n) F) :=
    (hyord ▸ orderOf_map_dvd (conjAut n F) M).trans (orderOf_dvd_natCard M)
  obtain ⟨f, hℓ, hcard'⟩ := FiniteField.card F (ringChar F)
  have hFc : Nat.card F = ringChar F ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hcard']
  obtain ⟨hpf, σ, hσ, ⟨h, -, hxh⟩, hk⟩ := higher_linear_prime_semilinear_field_descent' hℓ
    f.pos hn hFc hp x hxE hxl (orderOf_eq_prime hxp hx1)
  have hFE : Nat.card F = Nat.card (semilinearFixedSubfield σ) ^ p := by
    rw [hk, ← pow_mul, Nat.div_mul_cancel hpf, hFc]
  have hpE : ¬ p ∣ Nat.card (semilinearFixedSubfield σ) := fun hd =>
    hpF (hFE ▸ dvd_pow hd hp.ne_zero)
  exact localDeltaIn_eq_bot_of_conj_fieldAut' hn hp hσ
    (dvd_card_projectiveSL_of_dvd_card_GL hp hn hFE hpE hGL) hH hx h hxh

end Outer

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
