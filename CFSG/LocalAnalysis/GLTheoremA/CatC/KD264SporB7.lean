module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockFiveA5
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SevenSq
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporAll
public import CFSG.HardMathSupport.Dickson.BMRows.RowsB

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen.B7

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem not_modEq_seven {n m : ℕ} (hn : n ≤ 2) (hm : m < n) : ¬ 7 ^ n ≡ 7 ^ m [MOD 5] := by
  interval_cases n <;> interval_cases m <;> decide

theorem glaPLayer_ne_bot_of_five {X : Type} [Group X] [Finite X] {y : X} (hy : orderOf y = 5)
    (hyc : y ∉ CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := X) 7)
    (h343 : ¬ 7 ^ 3 ∣ Nat.card X) : GLAPLayer 7 (⊤ : Subgroup X) ≠ ⊥ := by
  intro hl
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P, hPn, hPp, hCP⟩ := GL83.hasPrimeConstraint_of_glaPLayer_eq_bot (by norm_num) hl
  set N := CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := X) 7 with hN
  set yb : X ⧸ N := (y : X ⧸ N) with hyb
  have hy5 : yb ^ 5 = 1 := by
    rw [hyb, ← QuotientGroup.mk_pow, ← hy, pow_orderOf_eq_one, QuotientGroup.mk_one]
  have hy1 : yb ≠ 1 := fun h => hyc ((QuotientGroup.eq_one_iff y).1 h)
  have hynorm : yb ∈ Subgroup.normalizer (P : Set (X ⧸ N)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh; exact hPn.conj_mem h hh yb
    · intro hh
      have := hPn.conj_mem _ hh yb⁻¹
      simpa [mul_assoc] using this
  have hmod := CFSG.AGLEmbedding.BlockCyc.card_inf_centralizer_modEq_of_pow (p := 5) (a := 1)
    hynorm (by rw [pow_one]; exact hy5)
  obtain ⟨n, hn⟩ := hPp.exists_card_eq
  have hPdvd : Nat.card P ∣ Nat.card X :=
    (Subgroup.card_subgroup_dvd_card P).trans (Subgroup.card_quotient_dvd_card N)
  have hn2 : n ≤ 2 := by
    by_contra h
    apply h343
    rw [hn] at hPdvd
    exact (Nat.pow_dvd_pow 7 (by omega)).trans hPdvd
  have hPC : IsPGroup 7 ↥(P ⊓ Subgroup.centralizer ({yb} : Set (X ⧸ N))) := hPp.to_le inf_le_left
  obtain ⟨m, hm⟩ := hPC.exists_card_eq
  have hmn : m < n := by
    have hdvd : 7 ^ m ∣ 7 ^ n := by
      rw [← hm, ← hn]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hle : m ≤ n := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 hdvd
    rcases Nat.lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      have heq : P ⊓ Subgroup.centralizer ({yb} : Set (X ⧸ N)) = P :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hm, hn, h])
      have hyC : yb ∈ Subgroup.centralizer (P : Set (X ⧸ N)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h' hh'
        have := (heq.symm ▸ hh' : h' ∈ P ⊓ Subgroup.centralizer ({yb} : Set (X ⧸ N)))
        exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 this).2
      have hyP : yb ∈ P := hCP hyC
      obtain ⟨k, hk⟩ := hPp ⟨yb, hyP⟩
      have hk' : yb ^ 7 ^ k = 1 := congrArg Subtype.val hk
      have h1 : orderOf yb ∣ 5 := orderOf_dvd_of_pow_eq_one hy5
      have h2 : orderOf yb ∣ 7 ^ k := orderOf_dvd_of_pow_eq_one hk'
      have hcop : Nat.Coprime 5 (7 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
      have h3 : orderOf yb = 1 := Nat.dvd_one.1 (by
        have := Nat.dvd_gcd h1 h2
        rwa [hcop] at this)
      exact hy1 (orderOf_eq_one_iff.1 h3)
  rw [hn, hm] at hmod
  exact not_modEq_seven hn2 hmn hmod

theorem exists_glaPComponent_of_top {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (C : Subgroup G) (h : GLAPLayer p (⊤ : Subgroup ↥C) ≠ ⊥) :
    ∃ J : Subgroup G, GLAPComponent p C J := by
  obtain ⟨J, hJ⟩ := CFSG.LocalAnalysis.GLTheoremA.exists_glaPComponent_of_layer_ne_bot h
  have hker : Nat.Coprime p (Nat.card ↥((⊤ : Subgroup C) ⊓ C.subtype.ker)) := by
    have : (⊤ : Subgroup C) ⊓ C.subtype.ker = ⊥ := by simp
    rw [this, Subgroup.card_bot]
    exact Nat.coprime_one_right p
  have h1 := glaPComponent_map hp C.subtype hker hJ
  have htop : (⊤ : Subgroup C).map C.subtype = C :=
    le_antisymm (by rintro _ ⟨y, -, rfl⟩; exact y.2) fun y hy => ⟨⟨y, hy⟩, Subgroup.mem_top _, rfl⟩
  rw [htop] at h1
  exact ⟨_, h1⟩


theorem card_carrier_B
    : Nat.card (Carrier .B) = 4154781481226426191177580544000000 := by
  obtain ⟨-, -, ⟨b⟩, -⟩ := CFSG.HardMathSupport.Dickson.BMRows.model_B
  rw [Nat.card_congr b.toEquiv,
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds .B]
  rfl

theorem factorization_card_B_seven
    : (Nat.card (Carrier .B)).factorization 7 = 2 := by
  rw [card_carrier_B, show (4154781481226426191177580544000000 : ℕ) =
      7 ^ 2 * 84791458800539310024032256000000 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem exists_component_B_seven
    :
    ∃ x : Carrier .B, orderOf x = 7 ∧
      ∃ J : Subgroup (Carrier .B),
        GLAPComponent 7 (Subgroup.centralizer ({x} : Set (Carrier .B))) J := by
  obtain ⟨hfin, -, -, -⟩ := CFSG.HardMathSupport.Dickson.BMRows.model_B
  obtain ⟨x, -, y, -, -, -, hx, -, -, -, -, -, -, -, -, -, -, -, hy, hyx, -⟩ :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.bSeven_elements
  refine ⟨x, hx, ?_⟩
  set C := Subgroup.centralizer ({x} : Set (Carrier .B)) with hC
  have hyC : y ∈ C := Subgroup.mem_centralizer_singleton_iff.2 hyx
  obtain ⟨yC, hyC'⟩ : ∃ yC : ↥C, (yC : Carrier .B) = y := ⟨⟨y, hyC⟩, rfl⟩
  have hyo : orderOf yC = 5 := by rw [← Subgroup.orderOf_coe, hyC']; exact hy
  have hcore :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.oPrimeCoreLeTwoAt_B_seven x hx
  have hcard :
      Nat.card (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥C) 7) ≤ 2 := by
    have e : Nat.card (GLAPPrimeCoreOf 7 C) =
        Nat.card (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥C) 7) :=
      Subgroup.card_map_of_injective C.subtype_injective
    rw [← e]
    exact hcore
  have hyc : yC ∉ CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥C) 7 := by
    intro hmem
    have hle : Subgroup.zpowers yC ≤
        CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥C) 7 :=
      Subgroup.zpowers_le.2 hmem
    have := (Subgroup.card_le_of_le hle).trans hcard
    rw [Nat.card_zpowers, hyo] at this
    omega
  have h343 : ¬ 7 ^ 3 ∣ Nat.card ↥C := by
    intro h
    have h2 := h.trans (Subgroup.card_subgroup_dvd_card C)
    rw [card_carrier_B] at h2
    norm_num at h2
  exact exists_glaPComponent_of_top (by norm_num) C (glaPLayer_ne_bot_of_five hyo hyc h343)

theorem kd264RowData_B_seven
    : KD264RowData 7 (Carrier .B) := by
  obtain ⟨hfin, -, -, -⟩ := CFSG.HardMathSupport.Dickson.BMRows.model_B
  obtain ⟨x, hx, J, hJ⟩ := exists_component_B_seven
  exact Seven.kd264RowData_of_sq (by norm_num) factorization_card_B_seven hx hJ

set_option maxRecDepth 100000 in
theorem kd264SporAt_B_seven
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) :
    KD264SporAt 7 .B := by
  obtain ⟨hfin, hs, ⟨b⟩, hnc⟩ := CFSG.HardMathSupport.Dickson.BMRows.model_B
  have hrd : KD264RowData 7 (Carrier .B) := kd264RowData_B_seven
  refine @kd264SporAt_of_model hOut 7 (by norm_num) (by decide) .B (Carrier .B) _ hfin hs hnc b ?_
  intro _ _ _
  exact hrd

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen.B7
