module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveWeyl
public import CFSG.RankThree.PartOne.KE8F.MultiStab

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSE8Five

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootSpace CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.Lattice
  CFSG.LieType.SeitzGeneration.ExcHigh.E8FiveSq
open CFSG.RankThree.E6 (charVal charVal_single charVal_neg)

set_option linter.unusedSectionVars false

theorem exists_rel3 (u : Fin 3 → Fin 2 → ZMod 5) : ∃ a b c : ZMod 5,
    (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧ ∀ k : Fin 2, a * u 0 k + b * u 1 k + c * u 2 k = 0 := by
  let f : (Fin 3 → ZMod 5) → (Fin 2 → ZMod 5) :=
    fun t k => t 0 * u 0 k + t 1 * u 1 k + t 2 * u 2 k
  have hcard : Fintype.card (Fin 2 → ZMod 5) < Fintype.card (Fin 3 → ZMod 5) := by
    simp [Fintype.card_fun, ZMod.card]
  obtain ⟨x, y, hxy, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  refine ⟨x 0 - y 0, x 1 - y 1, x 2 - y 2, ?_, fun k => ?_⟩
  · by_contra hcon
    push Not at hcon
    obtain ⟨h0, h1, h2⟩ := hcon
    apply hxy
    funext s
    fin_cases s
    · exact sub_eq_zero.1 h0
    · exact sub_eq_zero.1 h1
    · exact sub_eq_zero.1 h2
  · have := congrFun hf k
    simp only [f] at this
    linear_combination this


theorem fixH_eq_zero {m : ℕ} (hm1 : 1 ≤ m) (hm4 : m ≤ 4) {z : Fin Tag.E8.rank → ZMod 5}
    (hz : z ∈ fixSet (e8FiveH m)) (h4 : z 4 = 0) (h7 : z 7 = 0) : z = 0 := by
  interval_cases m
  · have h := fixSet_h1_param hz
    rw [h4, h7] at h
    exact h.trans (by decide)
  · have h := fixSet_h2_param hz
    rw [h4, h7] at h
    exact h.trans (by decide)
  · have h := fixSet_h3_param hz
    rw [h4, h7] at h
    exact h.trans (by decide)
  · have h := fixSet_h4_param hz
    rw [h4, h7] at h
    exact h.trans (by decide)

theorem no_order_five_fixes_regular_triple {z₀ z₁ z₂ : Fin Tag.E8.rank → ZMod 5}
    (hind : ∀ a b c : ZMod 5, a • z₀ + b • z₁ + c • z₂ = 0 → a = 0 ∧ b = 0 ∧ c = 0)
    (hreg : ∀ α, IsRoot Tag.E8 α → charVal z₀ α = 0 → charVal z₁ α = 0 →
      charVal z₂ α = 0 → False)
    {y : WeylGroup Tag.E8} (hy : orderOf y = 5) (hy₀ : y ∈ dualWeylStabilizer z₀)
    (hy₁ : y ∈ dualWeylStabilizer z₁) (hy₂ : y ∈ dualWeylStabilizer z₂) : False := by
  obtain ⟨x, i, j, hxy, hij⟩ := exists_conj_into_P hy
  have hzs : ∀ z, y ∈ dualWeylStabilizer z →
      trCol x z ∈ fixSet (e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ)) := fun z hz => by
    rw [← hxy]
    exact (mem_fixSet_trCol x y z).1 hz
  have hreg' : ∀ α, IsRoot Tag.E8 α → charVal (trCol x z₀) α = 0 → charVal (trCol x z₁) α = 0 →
      charVal (trCol x z₂) α = 0 → False := fun α hα h₀ h₁ h₂ =>
    hreg (x⁻¹ • α) (IsRoot.smul hα x⁻¹) (by rwa [charVal_trCol] at h₀)
      (by rwa [charVal_trCol] at h₁) (by rwa [charVal_trCol] at h₂)
  by_cases hi : (i : ℕ) = 0
  · exfalso
    have hj : (j : ℕ) ≠ 0 := by
      rcases hij with h | h
      · exact absurd (Fin.ext hi) h
      · exact fun h0 => h (Fin.ext h0)
    have hw : e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ) = e8FiveG2 ^ (j : ℕ) := by
      rw [hi, pow_zero, one_mul]
    have hjd : ¬ 5 ∣ (j : ℕ) := fun h => hj (Nat.eq_zero_of_dvd_of_lt h j.2)
    have h7 : ∀ z ∈ fixSet (e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ)), z 7 = 0 := fun z hz => by
      rw [congrFun (fixSet_g2_param (fixSet_subset_of_pow e8FiveG2_pow hjd hw hz)) 7]
      rfl
    exact hreg' (Pi.single 7 1) (isRoot_single _ 7) (by rw [charVal_single]; exact h7 _ (hzs _ hy₀))
      (by rw [charVal_single]; exact h7 _ (hzs _ hy₁))
      (by rw [charVal_single]; exact h7 _ (hzs _ hy₂))
  have hid : ¬ 5 ∣ (i : ℕ) := fun h => hi (Nat.eq_zero_of_dvd_of_lt h i.2)
  by_cases hj : (j : ℕ) = 0
  · exfalso
    have hw : e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ) = (e8FiveH 0) ^ (i : ℕ) := by
      rw [hj, pow_zero, mul_one, e8FiveH, pow_zero, mul_one]
    have h0 : ∀ z ∈ fixSet (e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ)), z 0 = 0 := fun z hz => by
      rw [congrFun (fixSet_h0_param (fixSet_subset_of_pow (e8FiveH_pow_five 0) hid hw hz)) 0]
      rfl
    exact hreg' (Pi.single 0 1) (isRoot_single _ 0) (by rw [charVal_single]; exact h0 _ (hzs _ hy₀))
      (by rw [charVal_single]; exact h0 _ (hzs _ hy₁))
      (by rw [charVal_single]; exact h0 _ (hzs _ hy₂))
  · have hex : ∀ i j : Fin 5, (i : ℕ) ≠ 0 → ∃ m : Fin 5, ((m : ℕ) * i) % 5 = j := by decide
    obtain ⟨m, hm⟩ := hex i j hi
    have hw : e8FiveG1 ^ (i : ℕ) * e8FiveG2 ^ (j : ℕ) = (e8FiveH m) ^ (i : ℕ) := by
      have hc : Commute e8FiveG1 (e8FiveG2 ^ (m : ℕ)) := Commute.pow_right e8Five_comm _
      rw [e8FiveH, hc.mul_pow, ← pow_mul, pow_eq_pow_mod ((m : ℕ) * (i : ℕ)) e8FiveG2_pow, hm]
    have hm0 : (m : ℕ) ≠ 0 := by
      intro h0
      rw [h0, zero_mul, Nat.zero_mod] at hm
      exact hj hm.symm
    have hm4 : (m : ℕ) ≤ 4 := by have := m.2; omega
    have hZ : ∀ z, y ∈ dualWeylStabilizer z → trCol x z ∈ fixSet (e8FiveH m) := fun z hz =>
      fixSet_subset_of_pow (e8FiveH_pow_five m) hid hw (hzs z hz)
    set Z₀ := trCol x z₀ with hZ₀
    set Z₁ := trCol x z₁ with hZ₁
    set Z₂ := trCol x z₂ with hZ₂
    obtain ⟨a, b, c, habc, hrel⟩ := exists_rel3
      ![![Z₀ 4, Z₀ 7], ![Z₁ 4, Z₁ 7], ![Z₂ 4, Z₂ 7]]
    have hmem : a • Z₀ + b • Z₁ + c • Z₂ ∈ fixSet (e8FiveH m) := by
      have h1 := mem_fixSet_add (mem_fixSet_add (hZ _ hy₀) (hZ _ hy₁) a b) (hZ _ hy₂) 1 c
      rwa [one_smul] at h1
    have hr0 := hrel 0
    have hr1 := hrel 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hr0 hr1
    have hz0 : a • Z₀ + b • Z₁ + c • Z₂ = 0 :=
      fixH_eq_zero (Nat.one_le_iff_ne_zero.2 hm0) hm4 hmem
        (by simpa [Pi.add_apply, Pi.smul_apply] using hr0)
        (by simpa [Pi.add_apply, Pi.smul_apply] using hr1)
    have hz1 : a • z₀ + b • z₁ + c • z₂ = 0 := by
      apply trCol_eq_zero (x := x)
      rw [trCol_add, trCol_add, trCol_smul, trCol_smul, trCol_smul]
      exact hz0
    obtain ⟨ha, hb, hc⟩ := hind a b c hz1
    rcases habc with h | h | h
    · exact h ha
    · exact h hb
    · exact h hc

theorem triple_stab_eq_bot (z : Fin 3 → Fin Tag.E8.rank → ZMod 5)
    (hind : ∀ a b c : ZMod 5, a • z 0 + b • z 1 + c • z 2 = 0 → a = 0 ∧ b = 0 ∧ c = 0)
    (hreg : ∀ α, IsRoot Tag.E8 α → (∀ i, charVal (z i) α = 0) → False) :
    (⨅ i, dualWeylStabilizer (z i) : Subgroup (WeylGroup Tag.E8)) = ⊥ := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set U : Subgroup (WeylGroup Tag.E8) := ⨅ i, dualWeylStabilizer (z i) with hU
  haveI : Fintype U := Fintype.ofFinite _
  by_cases h5 : 5 ∣ Nat.card U
  · exfalso
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := U) 5
      (by rwa [← Nat.card_eq_fintype_card])
    have hy : orderOf (x : WeylGroup Tag.E8) = 5 := by rw [Subgroup.orderOf_coe]; exact hx
    have hmem : ∀ i, (x : WeylGroup Tag.E8) ∈ dualWeylStabilizer (z i) := fun i =>
      (Subgroup.mem_iInf.1 x.2) i
    exact no_order_five_fixes_regular_triple (z₀ := z 0) (z₁ := z 1) (z₂ := z 2) hind
      (fun α hα h0 h1 h2 => hreg α hα fun i => by fin_cases i <;> assumption) hy
      (hmem 0) (hmem 1) (hmem 2)
  · refine eq_bot_iff.2 ((iInf_dualWeylStabilizer_le_of_card z h5).trans ?_)
    rw [Subgroup.closure_le]
    rintro _ ⟨α, hα, hz, rfl⟩
    exact (hreg α hα hz).elim

structure EigenTriple (w : WeylGroup Tag.E8) (r : ZMod 5)
    (z : Fin 3 → Fin Tag.E8.rank → ZMod 5) : Prop where
  ind : ∀ a b c : ZMod 5, a • z 0 + b • z 1 + c • z 2 = 0 → a = 0 ∧ b = 0 ∧ c = 0
  eig : ∀ (i : Fin 3) (v : Fin Tag.E8.rank → ℤ), charVal (z i) (w • v) = r * charVal (z i) v
  reg : ∀ α, IsRoot Tag.E8 α → (∀ i, charVal (z i) α = 0) → False

theorem EigenTriple.eq_one {w : WeylGroup Tag.E8} {z : Fin 3 → Fin Tag.E8.rank → ZMod 5}
    (h : EigenTriple w 1 z) : w = 1 := by
  have hw : w ∈ (⨅ i, dualWeylStabilizer (z i) : Subgroup (WeylGroup Tag.E8)) :=
    Subgroup.mem_iInf.2 fun i => mem_dualWeylStabilizer.2 fun v => by rw [h.eig, one_mul]
  rw [triple_stab_eq_bot z h.ind h.reg] at hw
  exact Subgroup.mem_bot.1 hw

theorem EigenTriple.eq_neg {w w₀ : WeylGroup Tag.E8} {z : Fin 3 → Fin Tag.E8.rank → ZMod 5}
    (h : EigenTriple w (-1) z) (hw₀ : ∀ v : Fin Tag.E8.rank → ℤ, w₀ • v = -v) :
    ∀ u : Fin Tag.E8.rank → ℤ, w • u = -u := by
  have hmem : w₀ * w ∈ (⨅ i, dualWeylStabilizer (z i) : Subgroup (WeylGroup Tag.E8)) :=
    Subgroup.mem_iInf.2 fun i => mem_dualWeylStabilizer.2 fun v => by
      rw [mul_smul, hw₀, charVal_neg, h.eig, neg_mul, one_mul, neg_neg]
  rw [triple_stab_eq_bot z h.ind h.reg] at hmem
  have h1 : w₀ * w = 1 := Subgroup.mem_bot.1 hmem
  intro u
  have h2 := congrArg (fun g => g • u) h1
  simp only [mul_smul, one_smul, hw₀] at h2
  exact (neg_eq_iff_eq_neg.1 h2)

end KSE8Five

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
