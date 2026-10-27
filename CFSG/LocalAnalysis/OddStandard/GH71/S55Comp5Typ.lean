module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Gen

public section

namespace CFSG.OddStandard.GH71.S55

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Signalizer.Ivk8 Matrix CFSG.Assembly.LowTwoRank
  CFSG.Blueprint

namespace C5

theorem pow_ne_two {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) : r ^ f ≠ 2 := by
  intro h
  rcases Nat.eq_zero_or_pos f with rfl | hf
  · simp at h
  have : r ∣ 2 := h ▸ dvd_pow_self r hf.ne'
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp this)

theorem three_le_pow {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hf : 1 ≤ f) : 3 ≤ r ^ f := by
  have h3 : 3 ≤ r := by have := hr.two_le; omega
  calc 3 ≤ r := h3
    _ = r ^ 1 := (pow_one r).symm
    _ ≤ r ^ f := Nat.pow_le_pow_right hr.pos hf

theorem dvd_pow_of_one_le {r f : ℕ} (hf : 1 ≤ f) : r ∣ r ^ f := dvd_pow_self r (by omega)

theorem isQuasisimple_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (hn : ∃ a b : G, a * b ≠ b * a) : IsQuasisimple G ∧ center G = ⊥ := by
  obtain ⟨a, b, hab⟩ := hn
  have hZ : center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
    · exact h
    · exact absurd (mem_center_iff.mp (h ▸ mem_top b) a) hab
  have hperf : Group.IsPerfect G := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
    · have := Subgroup.commutator_mem_commutator (mem_top a) (mem_top b)
      rw [← commutator_def, h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact absurd this hab
    · exact ⟨h⟩
  let e : G ⧸ center G ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have : IsSimpleGroup (G ⧸ center G) := e.isSimpleGroup
  refine ⟨⟨hperf, this, e.symm a, e.symm b, fun h => hab ?_⟩, hZ⟩
  have := congrArg e h
  simpa only [map_mul, MulEquiv.apply_symm_apply] using this

theorem scalar_injective {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {K : Type}
    [Field K] : Function.Injective (GeneralLinearGroup.scalar ι : Kˣ →* GL ι K) := by
  intro a b h
  obtain ⟨i⟩ := ‹Nonempty ι›
  have := congrArg (fun g : GL ι K => (g : Matrix ι ι K) i i) h
  simp only [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq] at this
  exact Units.ext this

end C5

open C5

theorem dvd_card_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {K : Type}
    [Field K] [Finite K] {r : ℕ} (hr : r.Prime) (hrK : r ∣ Nat.card K) {H : Subgroup (GL ι K)}
    (h : r ∣ Nat.card H) : r ∣ Nat.card (StatedProj H) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ((StatedScalars ι K).subgroupOf H)
  have h2 : Nat.card ↥((StatedScalars ι K).subgroupOf H) ∣ Nat.card K - 1 := by
    have e1 : Nat.card ↥((StatedScalars ι K).subgroupOf H) =
        Nat.card ↥(StatedScalars ι K ⊓ H) := by
      rw [← subgroupOf_map_subtype, card_map_of_injective H.subtype_injective]
    rw [e1]
    refine (card_dvd_of_le inf_le_left).trans ?_
    rw [StatedScalars, ← Nat.card_congr (MonoidHom.ofInjective scalar_injective).toEquiv,
      Nat.card_units]
  have hK1 : 1 ≤ Nat.card K := Nat.card_pos
  have h3 : Nat.Coprime r (Nat.card K - 1) := by
    rw [hr.coprime_iff_not_dvd]
    intro hd
    have h4 : r ∣ Nat.card K - (Nat.card K - 1) := Nat.dvd_sub hrK hd
    rw [show Nat.card K - (Nat.card K - 1) = 1 by omega] at h4
    exact hr.one_lt.ne' (Nat.dvd_one.mp h4)
  rw [h1] at h
  exact (Nat.Coprime.coprime_dvd_right h2 h3).dvd_of_dvd_mul_right h

variable {Y : Type} [Group Y]

theorem typ_sl {r f n : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hf : 1 ≤ f) (hn : n = 2 ∨ n = 3)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = r ^ f) (h3 : n = 3 ∨ r ^ f ≠ 3)
    {L : Subgroup Y} (e : SpecialLinearGroup (Fin n) K ≃* ↥L) :
    IsQuasisimple ↥L ∧ OddChev r (↥L ⧸ center ↥L) ∧ r ∣ Nat.card L := by
  have hq2 := pow_ne_two (f := f) hr hr2
  have hn2 : 2 ≤ n := by omega
  have h22 : n ≠ 2 ∨ Nat.card K ≠ 2 := Or.inr (by rw [hK]; exact hq2)
  have h23 : n ≠ 2 ∨ Nat.card K ≠ 3 := by
    rcases h3 with h3 | h3
    · exact Or.inl (by omega)
    · exact Or.inr (by rw [hK]; exact h3)
  refine ⟨LocalCores.isQuasisimple_of_mulEquiv e
    (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple n K hn2 h22
      h23), ⟨hr, hr2, ?_⟩, ?_⟩
  · have e' : ↥L ⧸ center ↥L ≃* StatedProj (StatedSL n K) :=
      (centerQuotCongr e.symm).trans (projectiveSpecialLinearGroupEquivStatedProj n K)
    have hM : LieModel (↥L ⧸ center ↥L) .PSL n r f := by
      refine Or.inl ⟨by decide, ⟨⟨hr, hf, hn2, ?_, ?_⟩, K, inferInstance, inferInstance, hK,
        ⟨e'⟩⟩⟩
      · intro h
        simp only [Prod.mk.injEq] at h
        exact hq2 h.2
      · intro h
        simp only [Prod.mk.injEq] at h
        rcases h3 with h3 | h3
        · omega
        · exact h3 h.2
    rcases hn with rfl | rfl
    · exact Or.inl ⟨f, hf, hM⟩
    · exact Or.inr (Or.inl ⟨f, hf, hM⟩)
  · rw [← Nat.card_congr e.toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by omega), hK]
    refine Dvd.dvd.mul_right (Dvd.dvd.trans (dvd_pow_of_one_le hf) (dvd_pow_self _ ?_)) _
    rcases hn with rfl | rfl <;> norm_num

theorem typ_su3 {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (r ^ f) ^ 2) {L : Subgroup Y}
    (e : ↥(StatedSU 3 (r ^ f) K) ≃* ↥L) :
    IsQuasisimple ↥L ∧ OddChev r (↥L ⧸ center ↥L) ∧ r ∣ Nat.card L := by
  have : Fact r.Prime := ⟨hr⟩
  have hq : ((3 : ℕ), r ^ f) ≠ (3, 2) := by
    intro h
    simp only [Prod.mk.injEq, true_and] at h
    exact pow_ne_two hr hr2 h
  obtain ⟨hQ, hZ⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (F := K) (p := r) (f := f) hK (n := 3) le_rfl hq
  refine ⟨LocalCores.isQuasisimple_of_mulEquiv e hQ,
    ⟨hr, hr2, Or.inr (Or.inr (Or.inl ⟨f, hf, ?_⟩))⟩, ?_⟩
  · have e' : ↥L ⧸ center ↥L ≃* StatedProj (StatedSU 3 (r ^ f) K) :=
      (centerQuotCongr e.symm).trans (QuotientGroup.quotientMulEquivOfEq hZ)
    exact Or.inl ⟨by decide, ⟨⟨hr, hf, le_rfl, hq⟩, K, inferInstance, inferInstance, hK, ⟨e'⟩⟩⟩
  · rw [← Nat.card_congr e.toEquiv]
    have h := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int (p := r) (f := f) (F := K)
      ⟨hr, hf, by rw [hK, ← pow_mul, mul_comm]⟩ (n := 3) (by norm_num)
    have h' : (r : ℤ) ∣ (Nat.card ↥(StatedSU 3 (r ^ f) K) : ℤ) := by
      rw [h]
      refine Dvd.dvd.mul_right (Dvd.dvd.trans ?_ (dvd_pow_self _ (by norm_num))) _
      exact_mod_cast dvd_pow_of_one_le hf
    exact_mod_cast h'

theorem typ_simple {r : ℕ} {L : Subgroup Y} [IsSimpleGroup ↥L] (hn : ∃ a b : ↥L, a * b ≠ b * a)
    (hc : OddChev r ↥L) : IsQuasisimple ↥L ∧ OddChev r (↥L ⧸ center ↥L) := by
  obtain ⟨hq, hZ⟩ := isQuasisimple_of_simple hn
  exact ⟨hq, oddChev_congr
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm hc⟩

theorem typ_psp4 {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = r ^ f) {L : Subgroup Y}
    (e : StatedProj (StatedSp 2 K) ≃* ↥L) :
    IsQuasisimple ↥L ∧ OddChev r (↥L ⧸ center ↥L) ∧ r ∣ Nat.card L := by
  have h3 : 3 ≤ Nat.card K := hK ▸ three_le_pow (f := f) hr hr2 hf
  have hK3 : (Infinite K ∨ 4 ≤ Nat.card K) ∨ (Nat.card K = 3 ∧ 2 ≤ 2) ∨
      (Nat.card K = 2 ∧ 3 ≤ 2) := by
    rcases eq_or_lt_of_le h3 with h | h
    · exact Or.inr (Or.inl ⟨h.symm, le_rfl⟩)
    · exact Or.inl (Or.inr h)
  have hS : IsSimpleGroup (StatedProj (StatedSp 2 K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2 (by norm_num) hK3
  have hP : Group.IsPerfect (StatedProj (StatedSp 2 K)) := by
    refine CFSG.ClassicalGroups.Symplectic.symplectic_projective_perfect 2 K ?_
    rcases hK3 with (h | h) | h | h
    · exact (@not_finite K h _).elim
    · have : Fintype K := Fintype.ofFinite K
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
        (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h)
      exact Or.inl ⟨s, hs⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have : IsSimpleGroup ↥L := e.symm.isSimpleGroup
  have hn : ∃ a b : ↥L, a * b ≠ b * a := by
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    exact Group.IsPerfect.not_isMulCommutative (StatedProj (StatedSp 2 K))
      ⟨⟨fun a b => e.injective (by rw [map_mul, map_mul, hcon])⟩⟩
  have hc : OddChev r ↥L := by
    refine ⟨hr, hr2, Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hf, ?_⟩)))⟩
    refine Or.inl ⟨by decide, ⟨⟨hr, hf, le_rfl, ?_⟩, K, inferInstance, inferInstance, hK,
      ⟨e.symm⟩⟩⟩
    intro h
    simp only [Prod.mk.injEq, true_and] at h
    exact pow_ne_two hr hr2 h
  obtain ⟨hq, hc'⟩ := typ_simple hn hc
  refine ⟨hq, hc', ?_⟩
  rw [← Nat.card_congr e.toEquiv]
  refine dvd_card_statedProj hr (hK ▸ dvd_pow_of_one_le hf) ?_
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp (K := K) 2, hK]
  exact Dvd.dvd.mul_right (Dvd.dvd.trans (dvd_pow_of_one_le hf) (dvd_pow_self _ (by norm_num))) _

end CFSG.OddStandard.GH71.S55
