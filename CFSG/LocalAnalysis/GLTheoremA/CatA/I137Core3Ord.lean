module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Core3List
public import CFSG.Milestones.CL_LIT_Borel_Tits_local_parabolic
import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel
import CFSG.LieType.Catalog.Realization

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I137C3

open CFSG.Yardstones.Md0ec50421ce4 TauCeti CFSG.Open
  CFSG.HardMathSupport.Solomon.Coordinator.I1420

theorem exists_odd_index_of_sylow_le {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    {P A : Subgroup S} (hP : P ≠ ⊤) (Syl : Sylow 2 S) (hSyl : (Syl : Subgroup S) ≤ P)
    (hA : A ≤ P) :
    ∃ m : ℕ, Odd m ∧ 1 < m ∧ Nat.card A * m ∣ Nat.card S ∧ Nat.card S ∣ m.factorial := by
  refine ⟨P.index, ?_, Subgroup.one_lt_index_of_ne_top hP, ?_, ?_⟩
  · have h1 : ¬ 2 ∣ P.index := fun h2 =>
      Syl.not_dvd_index (h2.trans (Subgroup.index_dvd_of_le hSyl))
    exact Nat.odd_iff.2 (by omega)
  · calc Nat.card A * P.index ∣ Nat.card P * P.index :=
          Nat.mul_dvd_mul_right (Subgroup.card_dvd_of_le hA) _
      _ = Nat.card S := Subgroup.card_mul_index P
  · have hcore : P.normalCore = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P.normalCore with h | h
      · exact h
      · exact absurd (top_le_iff.1 (h ▸ P.normalCore_le)) hP
    have hinj : Function.Injective (MulAction.toPermHom S (S ⧸ P)) := by
      rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker]
      exact hcore
    have := Subgroup.card_dvd_of_injective _ hinj
    rwa [Nat.card_perm] at this

section BorelTits


theorem exists_proper_sylow_le {S : Type} [Group S] {t : CFSG.Assembly.LowTwoRank.StatedLieTag}
    {n f : ℕ} (hmodel : CFSG.Blueprint.LieModel S t n 2 f) {T : Subgroup S} (hT2 : IsPGroup 2 T)
    (hT : T ≠ ⊥) :
    ∃ P : Subgroup S, P ≠ ⊤ ∧ Subgroup.normalizer (T : Set S) ≤ P ∧
      ∃ Syl : Sylow 2 S, (Syl : Subgroup S) ≤ P := by
  obtain ⟨Syl, P, hP, hN, -, -, hSN, hST⟩ :=
    CFSG.Milestones.cl_lit_borel_tits_local_parabolic_all_models S t n 2 f hmodel T hT hT2
  refine ⟨P, hP, hN, Syl, ?_⟩
  by_cases ht : t = .Tits
  · exact hST ht
  · exact Subgroup.le_normalizer.trans (hSN ht)

theorem exists_odd_index {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n f : ℕ}
    (hmodel : CFSG.Blueprint.LieModel S t n 2 f) {T A : Subgroup S} (hT2 : IsPGroup 2 T)
    (hT : T ≠ ⊥) (hA : A ≤ Subgroup.normalizer (T : Set S)) :
    ∃ m : ℕ, Odd m ∧ 1 < m ∧ Nat.card A * m ∣ Nat.card S ∧ Nat.card S ∣ m.factorial := by
  obtain ⟨P, hP, hN, Syl, hSyl⟩ := exists_proper_sylow_le hmodel hT2 hT
  exact exists_odd_index_of_sylow_le hS hP Syl hSyl (hA.trans hN)

end BorelTits

@[expose] def ordFamOrders : List ℕ :=
  [1056706560, 1451520, 174182400, 13685760, 9196830720, 211341312, 17971200]

namespace Core3Arith

theorem fixed_order_dvd {Q N : ℕ} (hQ : Q ∈ list93FixedOrders) (hN : N ∈ ordFamOrders)
    (hd : Q ∣ N) : Q = N ∨ (Q = 211341312 ∧ N = 1056706560) := by
  have key : ∀ Q ∈ list93FixedOrders, ∀ N ∈ ordFamOrders,
      Q ∣ N → Q = N ∨ (Q = 211341312 ∧ N = 1056706560) := by decide +kernel
  exact key Q hQ N hN hd

theorem fixed_order_false {Q N m : ℕ} (hQ : Q ∈ list93FixedOrders) (hN : N ∈ ordFamOrders)
    (hm : 1 < m) (hd : Q * m ∣ N) (hf : N ∣ m.factorial) : False := by
  have hNpos : 0 < N := by
    have key : ∀ N ∈ ordFamOrders, 0 < N := by decide +kernel
    exact key N hN
  rcases fixed_order_dvd hQ hN (Dvd.dvd.trans (Dvd.intro _ rfl) hd) with rfl | ⟨rfl, rfl⟩
  · have := Nat.le_of_dvd hNpos hd
    nlinarith
  · have h5 : m ∣ 5 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 211341312)
      (by simpa using hd)
    have hm5 : m = 5 := ((Nat.dvd_prime Nat.prime_five).1 h5).resolve_left (by omega)
    subst hm5
    have := Nat.le_of_dvd (by norm_num) hf
    norm_num [Nat.factorial] at this

theorem l3_order_dvd {e N : ℕ} (hN : N ∈ ordFamOrders) (he : 2 ≤ e) (hev : Even e)
    (hd : orderA 2 (2 ^ e) ∣ N) : e = 2 := by
  by_contra hne
  have h4 : 4 ≤ e := by
    obtain ⟨k, hk⟩ := hev
    omega
  have h2 : (2 : ℕ) ^ (3 * e) ∣ N := by
    have : (2 : ℕ) ^ (3 * e) = (2 ^ e) ^ 3 := by rw [mul_comm, pow_mul]
    rw [this]
    exact (pow_three_dvd_orderA_two _).trans hd
  have he5 : e ≤ 5 := by
    by_contra h6
    have h16 : (2 : ℕ) ^ 16 ∣ N := (pow_dvd_pow 2 (by omega : 16 ≤ 3 * e)).trans h2
    have key : ∀ N ∈ ordFamOrders, ¬ (2 : ℕ) ^ 16 ∣ N := by decide +kernel
    exact key N hN h16
  have he4 : e = 4 := by
    obtain ⟨k, hk⟩ := hev
    omega
  subst he4
  have key : ∀ N ∈ ordFamOrders, ¬ orderA 2 (2 ^ 4) ∣ N := by decide +kernel
  exact key N hN hd

theorem u3_order_not_dvd {e N : ℕ} (hN : N ∈ ordFamOrders) (he : 3 ≤ e) (hodd : Odd e) :
    ¬ orderTwistedA 2 (2 ^ e) ∣ N := by
  intro hd
  have h2 : (2 : ℕ) ^ (3 * e) ∣ N := by
    have : (2 : ℕ) ^ (3 * e) = (2 ^ e) ^ 3 := by rw [mul_comm, pow_mul]
    rw [this]
    exact (pow_three_dvd_orderTwistedA_two Nat.one_le_two_pow).trans hd
  have he5 : e ≤ 5 := by
    by_contra h6
    have h16 : (2 : ℕ) ^ 16 ∣ N := (pow_dvd_pow 2 (by omega : 16 ≤ 3 * e)).trans h2
    have key : ∀ N ∈ ordFamOrders, ¬ (2 : ℕ) ^ 16 ∣ N := by decide +kernel
    exact key N hN h16
  have key : ∀ N ∈ ordFamOrders,
      ¬ orderTwistedA 2 (2 ^ 3) ∣ N ∧ ¬ orderTwistedA 2 (2 ^ 5) ∣ N := by decide +kernel
  obtain ⟨k, hk⟩ := hodd
  have he35 : e = 3 ∨ e = 5 := by omega
  rcases he35 with rfl | rfl
  · exact (key N hN).1 hd
  · exact (key N hN).2 hd

theorem primePower_p_eq_two_of_card {q : PrimePower} {k : ℕ} (h : q.card = 2 ^ k) : q.p = 2 := by
  rw [PrimePower.card_def] at h
  have h1 : q.p ∣ 2 ^ k := h ▸ dvd_pow_self q.p (Nat.pos_iff_ne_zero.1 q.exponent_pos)
  exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 (q.prime_p.dvd_of_dvd_pow h1)

end Core3Arith

open Core3Arith

@[expose] def OrdFam (d : LieTypeIndex) : Prop :=
  (∃ q : PrimePower, d = .B 2 q ∧ q.card = 8) ∨ (∃ q : PrimePower, d = .B 3 q ∧ q.card = 2) ∨
    (∃ q : PrimePower, d = .D 4 q ∧ q.card = 2) ∨
    (∃ q : PrimePower, d = .twistedA 4 q ∧ q.card = 2) ∨
    (∃ q : PrimePower, d = .twistedA 5 q ∧ q.card = 2) ∨
    (∃ q : PrimePower, d = .trialityD4 q ∧ q.card = 2) ∨ d = .tits

theorem OrdFam.characteristic_eq {d : LieTypeIndex} (h : OrdFam d) : d.characteristic = 2 := by
  rcases h with ⟨q, rfl, hq⟩ | ⟨q, rfl, hq⟩ | ⟨q, rfl, hq⟩ | ⟨q, rfl, hq⟩ | ⟨q, rfl, hq⟩ |
    ⟨q, rfl, hq⟩ | rfl
  · rw [LieTypeIndex.characteristic_B]
    exact primePower_p_eq_two_of_card (k := 3) (by rw [hq]; norm_num)
  · rw [LieTypeIndex.characteristic_B]
    exact primePower_p_eq_two_of_card (k := 1) (by rw [hq]; norm_num)
  · rw [LieTypeIndex.characteristic_D]
    exact primePower_p_eq_two_of_card (k := 1) (by rw [hq]; norm_num)
  · rw [LieTypeIndex.characteristic_twistedA]
    exact primePower_p_eq_two_of_card (k := 1) (by rw [hq]; norm_num)
  · rw [LieTypeIndex.characteristic_twistedA]
    exact primePower_p_eq_two_of_card (k := 1) (by rw [hq]; norm_num)
  · rw [LieTypeIndex.characteristic_trialityD4]
    exact primePower_p_eq_two_of_card (k := 1) (by rw [hq]; norm_num)
  · exact LieTypeIndex.characteristic_tits

theorem OrdFam.lieOrderFormula_mem {d : LieTypeIndex} (h : OrdFam d) :
    lieOrderFormula d ∈ ordFamOrders := by
  rcases h with ⟨q, rfl, hq⟩ | ⟨q, rfl, hq⟩ | ⟨q, rfl, hq⟩ | ⟨q, rfl, hq⟩ | ⟨q, rfl, hq⟩ |
    ⟨q, rfl, hq⟩ | rfl
  · simp only [lieOrderFormula, hq]
    decide +kernel
  · simp only [lieOrderFormula, hq]
    decide +kernel
  · simp only [lieOrderFormula, hq]
    decide +kernel
  · simp only [lieOrderFormula, hq]
    decide +kernel
  · simp only [lieOrderFormula, hq]
    decide +kernel
  · simp only [lieOrderFormula, hq]
    decide +kernel
  · simp only [lieOrderFormula]
    decide +kernel

section OrderFilter


theorem core3At_ord : Core3At OrdFam := by
  intro d hd S _ _ ⟨e⟩ T A hT2 hT0 hA Q₀ _ ⟨f, hf⟩ hQ
  obtain ⟨t, n, r, hmodel⟩ :=
    CFSG.StandardType.ChevTwo.exists_lieModel_two_of_valid d hd.characteristic_eq e
  obtain ⟨-, -, hsimp⟩ := CFSG.LieType.Catalog.lieModel_finite_simple S t n 2 r hmodel
  obtain ⟨m, -, hm1, hAm, hSm⟩ := exists_odd_index hsimp hmodel hT2 hT0 hA
  have : Finite Q₀ := Finite.of_surjective f hf
  have hSord : Nat.card S ∈ ordFamOrders := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds d S ⟨e⟩]
    exact hd.lieOrderFormula_mem
  have hQmS : Nat.card Q₀ * m ∣ Nat.card S :=
    (Nat.mul_dvd_mul_right (card_dvd_of_surjective f hf) m).trans hAm
  rcases card_list93three hQ with hfix | ⟨e', he', hev, hcard, hcat⟩ | ⟨e', he', hodd, hcard⟩
  · exact (fixed_order_false hfix hSord hm1 hQmS hSm).elim
  · refine hcat (l3_order_dvd hSord he' hev ?_)
    rw [← hcard]
    exact (Dvd.intro _ rfl).trans hQmS
  · refine (u3_order_not_dvd hSord he' hodd ?_).elim
    rw [← hcard]
    exact (Dvd.intro _ rfl).trans hQmS

end OrderFilter

end CFSG.LocalAnalysis.GLTheoremA.I137C3

end
