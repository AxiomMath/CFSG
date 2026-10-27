module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdArith
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdRows

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7Std

open CFSG Subgroup CFSG.Assembly.LowTwoRank

theorem ordL2sq_dvd_L216 {Q : ℕ} (h5 : 5 ≤ Q) (h : ordL2sq Q ∣ 4080) : False := by
  have hQ := lt_of_ordL2sq_dvd (B := 5) (by norm_num) (by decide) h
  omega

theorem ordL2sq_dvd_L34 {Q : ℕ} (h5 : 5 ≤ Q) (h : ordL2sq Q ∣ 20160) : False := by
  have hQ := lt_of_ordL2sq_dvd (B := 7) (by norm_num) (by decide) h
  interval_cases Q <;> revert h <;> decide

theorem ordL2sq_dvd_S44 {Q : ℕ} (h5 : 5 ≤ Q) (h : ordL2sq Q ∣ 979200) : False := by
  have hQ := lt_of_ordL2sq_dvd (B := 13) (by norm_num) (by decide) h
  interval_cases Q <;> revert h <;> decide

theorem ordL2sq_dvd_L52 {Q : ℕ} (h5 : 5 ≤ Q) (h : ordL2sq Q ∣ 9999360) : False := by
  have hQ := lt_of_ordL2sq_dvd (B := 19) (by norm_num) (by decide) h
  interval_cases Q <;> revert h <;> decide

theorem ordL2sq_dvd_U52 {Q : ℕ} (h5 : 5 ≤ Q) (h : ordL2sq Q ∣ 13685760) : False := by
  have hQ := lt_of_ordL2sq_dvd (B := 20) (by norm_num) (by decide) h
  interval_cases Q <;> revert h <;> decide

theorem ordL2sq_dvd_U34 {Q : ℕ} (h5 : 5 ≤ Q) (h : ordL2sq Q ∣ 62400) : Q = 5 := by
  have hQ := lt_of_ordL2sq_dvd (B := 8) (by norm_num) (by decide) h
  interval_cases Q <;> first | rfl | (revert h; decide)

theorem ordL2sq_dvd_L316 {Q : ℕ} (h5 : 5 ≤ Q) (hQo : Odd Q) (h : ordL2sq Q ∣ 1425715200) :
    Q = 5 := by
  have hQ := lt_of_ordL2sq_dvd (B := 43) (by norm_num) (by decide) h
  interval_cases Q <;> first | rfl | (revert h hQo; decide)

theorem card_of_lieModel_PSL {G : Type} [Group G] {n e : ℕ} (hn : 1 ≤ n)
    (h : Blueprint.LieModel G .PSL n 2 e) :
    Nat.card G = (2 ^ e) ^ (n * (n - 1) / 2) * (∏ j ∈ Finset.Icc 2 n, ((2 ^ e) ^ j - 1)) /
      Nat.gcd n (2 ^ e - 1) := by
  have h' := OddClassSelector.statedClassicalModel_of_lieModel h
    (by simp [Blueprint.chevalleyExceptionalTags]) (by simp [Blueprint.reeTitsTags]) (by decide)
  obtain ⟨-, F, _, _, hF, ⟨φ⟩⟩ := h'
  rw [Nat.card_congr φ.toEquiv, CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL hn, hF]

theorem card_of_lieModel_PSU {G : Type} [Group G] {n e : ℕ} (hn : 2 ≤ n) (he : 1 ≤ e)
    (h : Blueprint.LieModel G .PSU n 2 e) :
    Nat.card G = (2 ^ e) ^ (n * (n - 1) / 2) *
      (∏ i ∈ Finset.Icc 2 n, (((2 ^ e : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) /
        Nat.gcd n (2 ^ e + 1) := by
  have h' := OddClassSelector.statedClassicalModel_of_lieModel h
    (by simp [Blueprint.chevalleyExceptionalTags]) (by simp [Blueprint.reeTitsTags]) (by decide)
  obtain ⟨-, F, _, _, hF, ⟨φ⟩⟩ := h'
  rw [Nat.card_congr φ.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two he hF hn]

theorem card_of_lieModel_PSp {G : Type} [Group G] {n e : ℕ} (he : 1 ≤ e)
    (h : Blueprint.LieModel G .PSp n 2 e) :
    Nat.card G = (2 ^ e) ^ (n ^ 2) * ∏ j ∈ Finset.Icc 1 n, ((2 ^ e) ^ (2 * j) - 1) := by
  have h' := OddClassSelector.statedClassicalModel_of_lieModel h
    (by simp [Blueprint.chevalleyExceptionalTags]) (by simp [Blueprint.reeTitsTags]) (by decide)
  obtain ⟨-, F, _, _, hF, ⟨φ⟩⟩ := h'
  have : CharP F 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two he hF
  rw [Nat.card_congr φ.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo, hF]

variable {H : Type} [Group H] [Finite H]

theorem StdConf.false_of_U34 (c : StdConf H) (hG : Nat.card ↥(generalizedFitting H) = 62400) :
    False := by
  classical
  have h := c.ordL2sq_dvd
  rw [hG] at h
  have hq := ordL2sq_dvd_U34 c.five_le h
  set G := generalizedFitting H with hGdef
  set M : Subgroup G := (centralizer ({c.b} : Set H)).subgroupOf G with hM
  have hMtop : M ≠ ⊤ := by
    intro htop
    apply c.b_ne_one
    have hbC : c.b ∈ centralizer (G : Set H) := by
      rw [mem_centralizer_iff]
      intro g hg
      have : (⟨g, hg⟩ : G) ∈ M := htop ▸ mem_top _
      rw [hM, mem_subgroupOf, mem_centralizer_singleton_iff] at this
      exact this
    rw [c.centralizer_eq_bot, mem_bot] at hbC
    exact hbC
  have hKM : c.K.subgroupOf G ≤ M := fun x hx => by
    rw [hM, mem_subgroupOf]
    exact c.K_le (mem_subgroupOf.mp hx)
  have hKcard : Nat.card (c.K.subgroupOf G) = Nat.card c.K :=
    Nat.card_congr (subgroupOfEquivOfLe c.K_le_G).toEquiv
  have hK7800 : 7800 ≤ Nat.card c.K := by
    have h1 := c.card_K_bar
    rw [hq] at h1
    have h2 : Nat.card (c.K ⧸ pPrimeCore 2 c.K) ≤ Nat.card c.K :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)
    rw [h1] at h2
    exact le_trans (by decide) h2
  have hM7800 : 7800 ≤ Nat.card M :=
    hK7800.trans (hKcard ▸ Subgroup.card_le_of_le hKM)
  have hidx := M.card_mul_index
  rw [hG] at hidx
  have hi8 : M.index ≤ 8 := by
    by_contra hlt
    push Not at hlt
    have : 7800 * 9 ≤ Nat.card M * M.index := Nat.mul_le_mul hM7800 hlt
    omega
  have hsimple := c.simple
  have hnc : M.normalCore = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal M.normalCore with h | h
    · exact h
    · exfalso
      apply hMtop
      rw [eq_top_iff, ← h]
      exact M.normalCore_le
  have hdvd := M.index_normalCore_dvd_factorial_index
  rw [hnc, Subgroup.index_bot, hG] at hdvd
  have hfac : (M.index).factorial ≤ 40320 := by
    calc (M.index).factorial ≤ (8 : ℕ).factorial := Nat.factorial_le hi8
      _ = 40320 := by decide
  have := Nat.le_of_dvd (Nat.factorial_pos _) hdvd
  omega

@[expose] def L316Row : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (_ : StdConf H),
    Blueprint.LieModel ↥(generalizedFitting H) .PSL 3 2 4 → False

theorem rowEven (hL316 : L316Row) : RowEven := by
  intro H _ _ c hG
  have h5 := c.five_le
  rcases hG with hG | hG | hG | hG | hG | hG | hG
  · have hc : Nat.card ↥(generalizedFitting H) = 4080 := by
      rw [card_of_lieModel_PSL (by norm_num) hG]; decide
    exact ordL2sq_dvd_L216 h5 (hc ▸ c.ordL2sq_dvd)
  · have hc : Nat.card ↥(generalizedFitting H) = 20160 := by
      rw [card_of_lieModel_PSL (by norm_num) hG]; decide
    exact ordL2sq_dvd_L34 h5 (hc ▸ c.ordL2sq_dvd)
  · exact c.false_of_U34 (by rw [card_of_lieModel_PSU (by norm_num) (by norm_num) hG]; decide)
  · have hc : Nat.card ↥(generalizedFitting H) = 979200 := by
      rw [card_of_lieModel_PSp (by norm_num) hG]; decide
    exact ordL2sq_dvd_S44 h5 (hc ▸ c.ordL2sq_dvd)
  · have hc : Nat.card ↥(generalizedFitting H) = 9999360 := by
      rw [card_of_lieModel_PSL (by norm_num) hG]; decide
    exact ordL2sq_dvd_L52 h5 (hc ▸ c.ordL2sq_dvd)
  · have hc : Nat.card ↥(generalizedFitting H) = 13685760 := by
      rw [card_of_lieModel_PSU (by norm_num) (by norm_num) hG]; decide
    exact ordL2sq_dvd_U52 h5 (hc ▸ c.ordL2sq_dvd)
  · exact hL316 H c hG

end Catalog7Std

end CFSG.ComponentClassification.GSThmB
