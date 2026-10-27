module

public import CFSG.GF2Type.Smith1980Orth.Order
public import CFSG.GF2Type.Smith1980Orth.IdentArith
public import CFSG.LargeExtraspecial.S14C12THyp
public import CFSG.LargeExtraspecial.DWRtMain
public import CFSG.Timmesfeld.Assembly

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open CFSG.LargeExtraspecial CFSG.Open CFSG.Blueprint Module

theorem ordA_two {n : ℕ} (hn : 1 ≤ n) :
    ordA (n - 1) (2 ^ 1) = 2 ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 2 n, (2 ^ j - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  unfold ordA
  rw [pow_one, show (2 : ℕ) - 1 = 1 from rfl, Nat.gcd_one_right, Nat.div_one, Nat.add_sub_cancel,
    mul_comm k (k + 1)]

theorem ordD_two {n : ℕ} (hn : 1 ≤ n) : ordD n (2 ^ 1) = 2 ^ (n * (n - 1)) * omegaOdd true n := by
  have hg : Nat.gcd 4 (2 ^ n - 1) = 1 := by
    have := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr (odd_two_pow_sub_one_of_pos hn))
    simpa using this
  unfold ordD omegaOdd sqProd
  rw [pow_one, hg, Nat.div_one, if_pos rfl, mul_assoc]

theorem ordTwistedD_two {n : ℕ} (hn : 1 ≤ n) :
    ordTwistedD n (2 ^ 1) = 2 ^ (n * (n - 1)) * omegaOdd false n := by
  have hg : Nat.gcd 4 (2 ^ n + 1) = 1 := by
    have := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr (odd_two_pow_add_one_of_pos hn))
    simpa using this
  unfold ordTwistedD omegaOdd sqProd
  rw [pow_one, hg, Nat.div_one, if_neg (by simp), mul_assoc]

theorem timmesfeldPlusType_iff {d : ℕ} (q : QuadraticForm (ZMod 2) (Fin d → ZMod 2)) :
    timmesfeldPlusType q ↔ CFSG.GroupTheory.WeirSylow.IsPlusType q := by
  unfold timmesfeldPlusType CFSG.GroupTheory.WeirSylow.IsPlusType
  simp only [Module.finrank_fin_fun]

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem OrthData.card_omega_exact (O : OrthData S) (b : Bool)
    (hb : b = true ↔ timmesfeldPlusType O.q) :
    Nat.card (timmesfeldOmega O.q) =
      2 ^ (S.width / 2 * (S.width / 2 - 1)) * omegaOdd b (S.width / 2) := by
  have hdim := O.finrank_eq
  have h4 := O.four_le
  obtain ⟨m, hm⟩ : ∃ m, S.width / 2 = m + 1 := ⟨S.width / 2 - 1, by omega⟩
  have hdim' : finrank (ZMod 2) (Fin S.width → ZMod 2) = 2 * (m + 1) := by rw [hdim, hm]
  have hcard := O.card_isometries
  rw [S7.timmesfeldIsometries_eq] at hcard
  rw [hm]
  obtain ⟨ε, hε, hεp⟩ : ∃ ε : ℤ, ((b = true ∧ ε = 1) ∨ (b = false ∧ ε = -1)) ∧
      ((ε = 1 ∧ CFSG.GroupTheory.WeirSylow.IsPlusType O.q) ∨
        (ε = -1 ∧ ¬ CFSG.GroupTheory.WeirSylow.IsPlusType O.q)) := by
    rw [← timmesfeldPlusType_iff] at *
    cases b
    · exact ⟨-1, Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, fun h => by simpa using hb.2 h⟩⟩
    · exact ⟨1, Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, hb.1 rfl⟩⟩
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type
    O.polarBilin_nondegenerate hdim' hεp
  rw [hcard, Nat.card_zmod] at h
  have hU := cast_omegaOdd b (m + 1) hε
  rw [Nat.add_sub_cancel] at hU ⊢
  have hΩ : ((Nat.card (timmesfeldOmega O.q) : ℕ) : ℤ) =
      2 ^ (m * (m + 1)) *
        (((2 : ℤ) ^ (m + 1) - ε) * ∏ i ∈ Finset.Icc 1 m, ((2 : ℤ) ^ (2 * i) - 1)) := by
    push_cast at h
    have h4' : ∀ x : ℕ, (4 : ℤ) ^ x = 2 ^ (2 * x) := fun x => by rw [pow_mul]; norm_num
    simp_rw [h4'] at h
    have h2 : (2 : ℤ) ≠ 0 := by norm_num
    apply mul_left_cancel₀ h2
    rw [h]
    ring
  have : (m + 1) * m = m * (m + 1) := mul_comm _ _
  rw [this]
  apply Nat.cast_injective (R := ℤ)
  rw [hΩ, Nat.cast_mul, hU]
  push_cast
  ring

theorem OrthData.card_G_eq (O : OrthData S) (hidx : S.M.index % 4 = 3) (b : Bool)
    (hb : b = true ↔ timmesfeldPlusType O.q) :
    ∃ e i : ℕ, e ≤ 1 ∧ i % 4 = 3 ∧
      Nat.card G = 2 ^ ((S.width / 2 + 1) * (S.width / 2 + 2) + e) *
        (3 * omegaOdd b (S.width / 2) * i) := by
  have hΩ := O.card_omega_exact b hb
  have hM := O.card_M
  have hG : Nat.card S.M * S.M.index = Nat.card G := S.M.card_mul_index
  have hw := O.width_eq_two_mul
  have h4 := O.four_le
  generalize S.width / 2 = m at hw hΩ ⊢
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hk : k + 2 - 1 = k + 1 := by omega
  rw [hk] at hΩ
  rcases O.iso with h | h
  · refine ⟨0, S.M.index, by omega, hidx, ?_⟩
    rw [← hG, hM.1 h, hΩ, hw, show (6 : ℕ) = 2 * 3 by norm_num]
    ring
  · refine ⟨1, S.M.index, le_rfl, hidx, ?_⟩
    rw [← hG, hM.2 h, hΩ, hw, show (12 : ℕ) = 2 * 2 * 3 by norm_num]
    ring

theorem isTransClass34_of_threeFourPlusClass {H : Type} [Group H] {D : Set H}
    (hD : ThreeFourPlusClass H D) : DW.IsTransClass34 D := by
  obtain ⟨⟨d₀, hD₀⟩, hord, hgen, hprod, hcomm⟩ := hD
  have hDeq : D = {g | IsConj d₀ g} := hD₀.trans (S14.setOf_isConj_eq_range d₀).symm
  refine ⟨hgen, ⟨d₀, ?_, fun d => ?_⟩, fun d hd => ⟨?_, ?_⟩, fun d hd e he => ?_,
    fun d hd e he h4 => ?_⟩
  · rw [hDeq]
    exact IsConj.refl d₀
  · rw [hDeq]
    rfl
  · intro h1
    have := hord d hd
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  · rw [← sq, ← hord d hd, pow_orderOf_eq_one]
  · have := hprod d hd e he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    omega
  · rw [← S14.commutator_eq_sq_of_orderOf (hord d hd) (hord e he)]
    exact hcomm d hd e he h4

theorem outcome_orthogonal {G : Type} [Group G] [Finite G] (hFI : DW.DW2FieldInput) {D : Set G}
    (hD : DW.IsTransClass34 D) (hOut : Timmesfeld.Outcome G) {m e i : ℕ} (b : Bool)
    (hm : 3 ≤ m) (he : e ≤ 1) (hi : i % 4 = 3)
    (hcard : Nat.card G = 2 ^ ((m + 1) * (m + 2) + e) * (3 * omegaOdd b m * i)) :
    (b = true → LieModel G .POmegaPlus (m + 2) 2 1) ∧
      (b = false → LieModel G .POmegaMinus (m + 2) 2 1) := by
  have hodd : Odd (3 * omegaOdd b m * i) := odd_three_mul_omegaOdd_mul b (by omega) hi
  have hpos : 0 < 3 * omegaOdd b m * i := hodd.pos
  rcases hOut with ⟨n, f, hn, hf, h⟩ | ⟨n, f, hn, hf, h⟩ | ⟨n, f, hn, hf, h | h⟩ | ⟨f, hf, h⟩ |
      ⟨f, hf, t, ht, h⟩ | h | h | h
  ·
    exfalso
    obtain rfl : f = 1 := by
      by_contra hne
      exact hFI G .PSL n f (by omega) (Or.inl ⟨rfl, hn⟩) h D hD
    have hc := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    rw [(Timmesfeld.card_statedClassicalModel_two hc).1 rfl, ordA_two (by omega)] at hcard
    exact psl_numeric hn hm he hi hcard
  ·
    exfalso
    obtain rfl : f = 1 := by
      by_contra hne
      exact hFI G .PSp n f (by omega) (Or.inr (Or.inl ⟨rfl, hn⟩)) h D hD
    have hc := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    rw [(Timmesfeld.card_statedClassicalModel_two hc).2.2.1 rfl] at hcard
    obtain ⟨r, hr, hr'⟩ := (Timmesfeld.Orders.profile_ordBC (n := n) (le_refl 1)).two
    rw [hr'] at hcard
    have := (two_pow_mul_odd_inj hr hodd hcard).1
    exact psp_numeric (m := m) (n := n) he (by omega)
  ·
    obtain rfl : f = 1 := by
      by_contra hne
      exact (hFI G .POmegaPlus n f (by omega) (Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, hn⟩))) h D
        hD).elim
    have hc := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    rw [(Timmesfeld.card_statedClassicalModel_two hc).2.2.2.1 rfl, ordD_two (by omega)] at hcard
    obtain ⟨rfl, rfl, rfl⟩ := pomega_numeric (by omega) hm he hi hcard
    exact ⟨fun _ => h, fun hb => by simp at hb⟩
  ·
    obtain rfl : f = 1 := by
      by_contra hne
      exact (hFI G .POmegaMinus n f (by omega) (Or.inr (Or.inr (Or.inl ⟨Or.inr rfl, hn⟩))) h D
        hD).elim
    have hc := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    rw [(Timmesfeld.card_statedClassicalModel_two hc).2.2.2.2 rfl,
      ordTwistedD_two (by omega)] at hcard
    obtain ⟨rfl, rfl, rfl⟩ := pomega_numeric (by omega) hm he hi hcard
    exact ⟨fun hb => by simp at hb, fun _ => h⟩
  ·
    exact (hFI G .G2 0 f hf (Or.inr (Or.inr (Or.inr ⟨rfl, by simp⟩))) h D hD).elim
  ·
    exfalso
    have hct : t ∈ chevalleyExceptionalTags := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    obtain rfl : f = 1 := by
      by_contra hne
      refine hFI G t 0 f (by omega) (Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩))) h D hD
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht ⊢
      tauto
    have hc := Timmesfeld.Final.chevalleyExceptionalModel_of_lieModel hct h
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · have hm' : Nat.card G = ordTrialityD4 (2 ^ 1) :=
        Timmesfeld.card_chevalleyExceptionalModel_two hc
      obtain ⟨r, hr, hr'⟩ := (Timmesfeld.Orders.profile_ordTrialityD4 (f := 1) le_rfl).two
      rw [hm', hr'] at hcard
      have h1 := (two_pow_mul_odd_inj hr hodd hcard).1
      exact exceptional_numeric hm he (v := 12) (by omega) (by omega)
    · have hm' : Nat.card G = ordF4 (2 ^ 1) := Timmesfeld.card_chevalleyExceptionalModel_two hc
      obtain ⟨r, hr, hr'⟩ := (Timmesfeld.Orders.profile_ordF4 (f := 1) le_rfl).two
      rw [hm', hr'] at hcard
      have h1 := (two_pow_mul_odd_inj hr hodd hcard).1
      exact exceptional_numeric hm he (v := 24) (by omega) (by omega)
    · have hm' : Nat.card G = ordE6 (2 ^ 1) := Timmesfeld.card_chevalleyExceptionalModel_two hc
      obtain ⟨r, hr, hr'⟩ := (Timmesfeld.Orders.profile_ordE6 (f := 1) le_rfl).two
      rw [hm', hr'] at hcard
      have h1 := (two_pow_mul_odd_inj hr hodd hcard).1
      exact exceptional_numeric hm he (v := 36) (by omega) (by omega)
    · have hm' : Nat.card G = ordTwistedE6 (2 ^ 1) :=
        Timmesfeld.card_chevalleyExceptionalModel_two hc
      obtain ⟨r, hr, hr'⟩ := (Timmesfeld.Orders.profile_ordTwistedE6 (f := 1) le_rfl).two
      rw [hm', hr'] at hcard
      have h1 := (two_pow_mul_odd_inj hr hodd hcard).1
      exact exceptional_numeric hm he (v := 36) (by omega) (by omega)
    · have hm' : Nat.card G = ordE7 (2 ^ 1) := Timmesfeld.card_chevalleyExceptionalModel_two hc
      obtain ⟨r, hr, hr'⟩ := (Timmesfeld.Orders.profile_ordE7 (f := 1) le_rfl).two
      rw [hm', hr'] at hcard
      have h1 := (two_pow_mul_odd_inj hr hodd hcard).1
      exact exceptional_numeric hm he (v := 63) (by omega) (by omega)
    · have hm' : Nat.card G = ordE8 (2 ^ 1) := Timmesfeld.card_chevalleyExceptionalModel_two hc
      obtain ⟨r, hr, hr'⟩ := (Timmesfeld.Orders.profile_ordE8 (f := 1) le_rfl).two
      rw [hm', hr'] at hcard
      have h1 := (two_pow_mul_odd_inj hr hodd hcard).1
      exact exceptional_numeric hm he (v := 120) (by omega) (by omega)
  ·
    exfalso
    obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ :=
      LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
    have h6048 : Nat.card G = 6048 := by
      rw [Nat.card_congr e'.toEquiv, Timmesfeld.ClassicalOrders.card_statedProj_statedSU
        Nat.prime_three le_rfl hK (by norm_num)]
      decide
    exact small_numeric hm hpos (by omega) (h6048.symm.trans hcard)
  ·
    exfalso
    obtain ⟨e'⟩ := h
    have h360 : Nat.card G = 360 := by
      rw [Nat.card_congr e'.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
    exact small_numeric hm hpos (by omega) (h360.symm.trans hcard)
  ·
    exfalso
    obtain ⟨e'⟩ := h
    have hJ : Nat.card G = 604800 := (Nat.card_congr e'.toEquiv).trans Sporadic.J2.card_J2
    exact small_numeric hm hpos (by omega) (hJ.symm.trans hcard)

theorem identInput : IdentInput := by
  intro G _ _ _ S O hw6 hD hnd hidx
  obtain ⟨a, b, ha, hb, h4⟩ := hnd
  have hOut := Timmesfeld.outcome (S14.hyp_of_threeFourPlusClass hD ⟨a, ha, b, hb, h4⟩)
  have hD34 := isTransClass34_of_threeFourPlusClass hD
  have hm : 3 ≤ S.width / 2 := by omega
  rw [show (S.width + 4) / 2 = S.width / 2 + 2 by omega]
  by_cases hp : timmesfeldPlusType O.q
  · obtain ⟨e, i, he, hi, hcard⟩ := O.card_G_eq hidx true (iff_of_true rfl hp)
    exact ⟨fun _ => (outcome_orthogonal DW.dw2FieldInput hD34 hOut true hm he hi hcard).1 rfl,
      fun h => absurd hp h⟩
  · obtain ⟨e, i, he, hi, hcard⟩ := O.card_G_eq hidx false (iff_of_false (by simp) hp)
    exact ⟨fun h => absurd h hp,
      fun _ => (outcome_orthogonal DW.dw2FieldInput hD34 hOut false hm he hi hcard).2 rfl⟩

end CFSG.GF2Type.Smith1980Orth
