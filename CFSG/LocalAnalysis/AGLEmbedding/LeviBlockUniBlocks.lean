module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups
public import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
import CFSG.Timmesfeld.Orders.ClassicalLinear
import CFSG.CharacterTheory.Burnside
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGenArith

public section

namespace CFSG.AGLEmbedding.LeviBlock

open Matrix CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

theorem not_isQuasisimple_of_isSolvable {G : Type*} [Group G] (hG : Group.IsSolvable G) :
    ¬ CFSG.Open.IsQuasisimple G := by
  intro hq
  have htop : ∀ n, derivedSeries G n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih, ← commutator_def, hq.1]
  obtain ⟨n, hn⟩ := hG.solvable
  have hsub : Subsingleton G := by
    refine ⟨fun a b => ?_⟩
    have ha : a ∈ derivedSeries G n := (htop n).symm ▸ Subgroup.mem_top a
    have hb : b ∈ derivedSeries G n := (htop n).symm ▸ Subgroup.mem_top b
    rw [hn, Subgroup.mem_bot] at ha hb
    rw [ha, hb]
  have : IsSimpleGroup (G ⧸ Subgroup.center G) := hq.2
  obtain ⟨x, y, hxy⟩ := (IsSimpleGroup.toNontrivial (G := G ⧸ Subgroup.center G)).exists_pair_ne
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  exact hxy (by rw [Subsingleton.elim a b])

theorem card_centerQuotient_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (A ⧸ Subgroup.center A) = Nat.card (B ⧸ Subgroup.center B) :=
  Nat.card_congr (QuotientGroup.congr _ _ e (map_center_mulEquiv e)).toEquiv

theorem card_centerQuotient_SL [Finite K] {m : ℕ} (hm : 1 ≤ m) :
    Nat.card (SpecialLinearGroup (Fin m) K ⧸ Subgroup.center (SpecialLinearGroup (Fin m) K)) =
      ordA (m - 1) (Nat.card K) := by
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := K) hm
  rw [← Nat.card_congr (projectiveSpecialLinearGroupEquivStatedProj m K).toEquiv] at h
  rw [show (SpecialLinearGroup (Fin m) K ⧸ Subgroup.center (SpecialLinearGroup (Fin m) K)) =
    ProjectiveSpecialLinearGroup (Fin m) K from rfl, h, ordA, Nat.sub_add_cancel hm,
    mul_comm (m - 1) m]

theorem isQuasisimple_SL_of_four_le [Finite K] (hK : 4 ≤ Nat.card K) {m : ℕ} (hm : 2 ≤ m) :
    CFSG.Open.IsQuasisimple (SpecialLinearGroup (Fin m) K) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hK)
  have hq := CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_SL (F := K) hm (Or.inr ⟨s, hs⟩)
  exact ⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩

theorem blockSL_facts [Finite K] (hK : 4 ≤ Nat.card K) {m : ℕ} (hm : 1 ≤ m) :
    let S := (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range
    (CFSG.Open.IsQuasisimple S ∨ Group.IsSolvable S) ∧
      (CFSG.Open.IsQuasisimple S → Nat.card (S ⧸ Subgroup.center S) = ordA (m - 1) (Nat.card K))
    := by
  intro S
  let e : SpecialLinearGroup (Fin m) K ≃* S :=
    MonoidHom.ofInjective (SpecialLinearGroup.toGL_injective)
  refine ⟨?_, fun _ => (card_centerQuotient_congr e).symm.trans (card_centerQuotient_SL hm)⟩
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · right
    obtain rfl : m = 1 := by omega
    have : Subsingleton (SpecialLinearGroup (Fin 1) K) := by
      refine ⟨fun A B => Subtype.ext (Matrix.ext fun i j => ?_)⟩
      rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
      have hA := A.2
      have hB := B.2
      rw [det_unique] at hA hB
      exact hA.trans hB.symm
    have : Subsingleton S := e.symm.injective.subsingleton
    infer_instance
  · exact Or.inl (isQuasisimple_of_mulEquiv e (isQuasisimple_SL_of_four_le hK hm2))

variable {p f s ε : ℕ}

theorem subsingleton_hypSU_zero (h : UnitaryFieldData p f K) (hε : ε ≤ 1) :
    Subsingleton (hypSU h 0 ε) := by
  have hsub : Subsingleton (HypIndex 0 ε) := by
    refine ⟨fun a b => ?_⟩
    rcases a with ⟨i, hi⟩ | ⟨i, hi⟩ | ⟨i, hi⟩ <;> rcases b with ⟨j, hj⟩ | ⟨j, hj⟩ | ⟨j, hj⟩ <;>
      first | omega | (congr 2; ext; simp only; omega)
  refine ⟨fun g g' => Subtype.ext (Units.ext (Matrix.ext fun a b => ?_))⟩
  rw [Subsingleton.elim b a]
  have : Unique (HypIndex 0 ε) := uniqueOfSubsingleton a
  have hg := (mem_hypSU.mp g.2).2
  have hg' := (mem_hypSU.mp g'.2).2
  rw [det_unique, Subsingleton.elim (default : HypIndex 0 ε) a] at hg hg'
  exact hg.trans hg'.symm

theorem hypSU_facts_of_three_le (h : UnitaryFieldData p f K) (hm : 3 ≤ 2 * s + ε)
    (hmq : (2 * s + ε, p ^ f) ≠ (3, 2)) :
    CFSG.Open.IsQuasisimple (hypSU h s ε) ∧
      Nat.card (hypSU h s ε ⧸ Subgroup.center (hypSU h s ε)) =
        ordTwistedA (2 * s + ε - 1) (p ^ f) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite K := h.finite
  have hF : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  obtain ⟨R, hR⟩ := exists_isHypTransport h (r := s) (ε := ε)
  set e := hypTransport h hR
  have hq := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hF hm hmq
  refine ⟨isQuasisimple_of_mulEquiv e.symm ⟨Group.isPerfect_def.mp hq.1.1, hq.1.2.1⟩, ?_⟩
  rw [card_centerQuotient_congr e]
  change Nat.card (StatedSU (2 * s + ε) (p ^ f) K ⧸
    Subgroup.center (StatedSU (2 * s + ε) (p ^ f) K)) = _
  rw [hq.2]
  change Nat.card (StatedProj (StatedSU (2 * s + ε) (p ^ f) K)) = _
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU h.prime h.one_le hF (by omega),
    ordTwistedA, Nat.sub_add_cancel (by omega : 1 ≤ 2 * s + ε),
    mul_comm (2 * s + ε - 1) (2 * s + ε)]

theorem ordA_one_eq_ordTwistedA_one {q : ℕ} (hq : Even q) (hq1 : 1 ≤ q) :
    ordA 1 q = ordTwistedA 1 q := by
  obtain ⟨k, rfl⟩ := hq
  have h1 : Nat.gcd 2 (k + k - 1) = 1 := by
    rw [Nat.Coprime.gcd_eq_one]
    exact (Nat.coprime_two_left).mpr (by rw [Nat.odd_iff]; omega)
  have h2 : Nat.gcd 2 (k + k + 1) = 1 := by
    rw [Nat.Coprime.gcd_eq_one]
    exact (Nat.coprime_two_left).mpr (by rw [Nat.odd_iff]; omega)
  simp only [ordA, ordTwistedA, Finset.Icc_self, Finset.prod_singleton, h1, h2, Nat.div_one]
  congr 1
  have : (((k + k : ℕ) : ℤ) ^ 2 - (-1) ^ 2) = (((k + k) ^ 2 - 1 : ℕ) : ℤ) := by
    have : 1 ≤ (k + k) ^ 2 := Nat.one_le_pow _ _ (by omega)
    push_cast [this]
    ring
  rw [this, Int.toNat_natCast]

theorem exists_hypSU_one_zero_mulEquiv [Fact p.Prime] [CharP K p] (h : UnitaryFieldData p f K) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      Nonempty (hypSU h 1 0 ≃* SpecialLinearGroup (Fin 2) F) := by
  have : Finite K := h.finite
  have hF : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  obtain ⟨R, hR⟩ := exists_isHypTransport h (r := 1) (ε := 0)
  obtain ⟨ζ, hζ0, hζ⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_eq_neg hF
  exact ⟨_, inferInstance, inferInstance, CFSG.LieType.Steinberg.card_fixedSubfield hF,
    ⟨(hypTransport h hR).trans ((CFSG.LieType.Universal.Unitary.equivStatedSU hF 2).symm.trans
      (CFSG.LieType.Steinberg.hypEquiv hζ0 hζ).symm)⟩⟩

theorem hypSU_facts_two (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f) :
    CFSG.Open.IsQuasisimple (hypSU h 1 0) ∧
      Nat.card (hypSU h 1 0 ⧸ Subgroup.center (hypSU h 1 0)) = ordTwistedA 1 (2 ^ f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := h.charP
  obtain ⟨F, _, _, hq, ⟨e⟩⟩ := exists_hypSU_one_zero_mulEquiv h
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  refine ⟨isQuasisimple_of_mulEquiv e.symm (isQuasisimple_SL_of_four_le (hq ▸ h4) le_rfl), ?_⟩
  rw [card_centerQuotient_congr e, card_centerQuotient_SL (by norm_num), hq]
  exact ordA_one_eq_ordTwistedA_one (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    (Nat.one_le_two_pow)

theorem isSolvable_hypSU_one (h : UnitaryFieldData 2 1 K) (hε : ε ≤ 1) :
    Group.IsSolvable (hypSU h 1 ε) := by
  have : Finite K := h.finite
  have hcard := (unitary_order_and_Sylow h le_rfl hε).2.2.2.2.2.1
  have : Fintype (hypSU h 1 ε) := Fintype.ofFinite _
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · have h6 : Nat.card (hypSU h 1 0) = 2 ^ 1 * 3 ^ 1 := by
      have : ((Nat.card (hypSU h 1 0) : ℕ) : ℤ) = ((2 ^ 1 * 3 ^ 1 : ℕ) : ℤ) := by
        rw [hcard]
        decide
      exact_mod_cast this
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      Nat.prime_two Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, h6])
  · have h216 : Nat.card (hypSU h 1 1) = 2 ^ 3 * 3 ^ 3 := by
      have : ((Nat.card (hypSU h 1 1) : ℕ) : ℤ) = ((2 ^ 3 * 3 ^ 3 : ℕ) : ℤ) := by
        rw [hcard]
        decide
      exact_mod_cast this
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      Nat.prime_two Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, h216])

theorem card_hypSU_one_zero_four (h : UnitaryFieldData 2 2 K) : Nat.card (hypSU h 1 0) = 60 := by
  have hcard := (unitary_order_and_Sylow h le_rfl (Nat.zero_le 1)).2.2.2.2.2.1
  have : ((Nat.card (hypSU h 1 0) : ℕ) : ℤ) = ((60 : ℕ) : ℤ) := by
    rw [hcard]
    decide
  exact_mod_cast this

theorem card_toGL_range_of_ordA_eq_sixty [Finite K] {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2)
    {m : ℕ} (hm : 1 ≤ m) (h60 : ordA (m - 1) (Nat.card K) = 60) :
    Nat.card (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range =
      60 := by
  obtain ⟨hm1, hK4⟩ := (ordA_eq_sixty_iff (f := 2 * f) (by rw [hK, pow_mul'])).mp h60
  obtain rfl : m = 2 := by omega
  rw [Nat.card_congr (MonoidHom.ofInjective SpecialLinearGroup.toGL_injective).toEquiv.symm,
    CFSG.LieType.Steinberg.card_specialLinearGroup_fin_two, hK4]
  norm_num

theorem hypSU_facts (h : UnitaryFieldData 2 f K) (hε : ε ≤ 1) (s : ℕ) :
    (CFSG.Open.IsQuasisimple (hypSU h s ε) ∨ Group.IsSolvable (hypSU h s ε)) ∧
      (CFSG.Open.IsQuasisimple (hypSU h s ε) →
        Nat.card (hypSU h s ε ⧸ Subgroup.center (hypSU h s ε)) =
          ordTwistedA (2 * s + ε - 1) (2 ^ f)) := by
  have hsolv : ∀ {s' : ℕ}, Group.IsSolvable (hypSU h s' ε) →
      (CFSG.Open.IsQuasisimple (hypSU h s' ε) ∨ Group.IsSolvable (hypSU h s' ε)) ∧
        (CFSG.Open.IsQuasisimple (hypSU h s' ε) →
          Nat.card (hypSU h s' ε ⧸ Subgroup.center (hypSU h s' ε)) =
            ordTwistedA (2 * s' + ε - 1) (2 ^ f)) :=
    fun hs => ⟨Or.inr hs, fun hq => absurd hq (not_isQuasisimple_of_isSolvable hs)⟩
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · have := subsingleton_hypSU_zero h hε
    exact hsolv inferInstance
  by_cases hm3 : 3 ≤ 2 * s + ε
  · by_cases hmq : (2 * s + ε, 2 ^ f) = (3, 2)
    · rw [Prod.mk.injEq] at hmq
      obtain ⟨rfl, rfl⟩ : s = 1 ∧ ε = 1 := by omega
      obtain rfl : f = 1 := Nat.pow_right_injective le_rfl (hmq.2.trans (pow_one 2).symm)
      exact hsolv (isSolvable_hypSU_one h le_rfl)
    · obtain ⟨hq, hc⟩ := hypSU_facts_of_three_le h hm3 hmq
      exact ⟨Or.inl hq, fun _ => hc⟩
  · obtain ⟨rfl, rfl⟩ : s = 1 ∧ ε = 0 := by omega
    rcases Nat.lt_or_ge f 2 with hf2 | hf2
    · obtain rfl : f = 1 := by have := h.one_le; omega
      exact hsolv (isSolvable_hypSU_one h (Nat.zero_le 1))
    · obtain ⟨hq, hc⟩ := hypSU_facts_two h hf2
      exact ⟨Or.inl hq, fun _ => hc⟩

end CFSG.AGLEmbedding.LeviBlock
