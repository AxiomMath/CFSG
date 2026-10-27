module

public import Mathlib.GroupTheory.PGroup
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith.Frontend

open MulAction

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {G : Type*} [Group G] {V K B : Subgroup G}

theorem natCard_mul_relIndex (h : V ≤ K) : Nat.card V * V.relIndex K = Nat.card K := by
  have h1 := natCard_eq_natCard_range_leftCoset_mul_natCard (V.subgroupOf K)
  rw [natCard_range_leftCoset] at h1
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv.symm, Subgroup.relIndex, mul_comm]
  exact h1.symm

section FreeAction

variable {W : Subgroup G} {B' : Subgroup (Subgroup.normalizer (W : Set G))}

theorem stabilizer_eq_bot_of_centralizer_inf_eq_bot
    (hfree : ∀ b ∈ B', (b : G) ≠ 1 → Subgroup.centralizer {(b : G)} ⊓ W = ⊥)
    {x : W} (hx : x ≠ 1) : stabilizer B' x = ⊥ := by
  refine le_antisymm (fun b hb => ?_) bot_le
  rw [mem_stabilizer_iff] at hb
  by_contra hb1
  have hb1' : ((b : Subgroup.normalizer (W : Set G)) : G) ≠ 1 := fun h =>
    hb1 (Subtype.ext (Subtype.ext h))
  have hc : ((b • x : W) : G) = ((b : Subgroup.normalizer (W : Set G)) : G) * (x : G) *
      ((b : Subgroup.normalizer (W : Set G)) : G)⁻¹ := Subgroup.smul_coe W _ x
  rw [hb] at hc
  have hmem : (x : G) ∈ Subgroup.centralizer {((b : Subgroup.normalizer (W : Set G)) : G)} ⊓ W :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hc.symm).symm, x.2⟩
  rw [hfree _ b.2 hb1'] at hmem
  exact hx (Subtype.ext (by simpa using hmem))

theorem fixedPoints_eq_singleton_one_of_centralizer_inf_eq_bot {p : ℕ} (hp : p.Prime)
    (hBcard : Nat.card B' = p)
    (hfree : ∀ b ∈ B', (b : G) ≠ 1 → Subgroup.centralizer {(b : G)} ⊓ W = ⊥) :
    fixedPoints B' W = {1} := by
  obtain ⟨b, hbB, hb1⟩ : ∃ b : Subgroup.normalizer (W : Set G), b ∈ B' ∧ b ≠ 1 := by
    have hne : B' ≠ ⊥ := by
      intro hb
      rw [hb, Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1, rfl⟩⟩] at hBcard
      exact hp.one_lt.ne hBcard
    rw [ne_eq, Subgroup.eq_bot_iff_forall] at hne
    by_contra hcon
    refine hne fun b hb => ?_
    by_contra hb1
    exact hcon ⟨b, hb, hb1⟩
  ext x
  simp only [Set.mem_singleton_iff]
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · by_contra hx1
    have hmem : (⟨b, hbB⟩ : B') ∈ stabilizer B' x := mem_stabilizer_iff.mpr (hx ⟨b, hbB⟩)
    rw [stabilizer_eq_bot_of_centralizer_inf_eq_bot hfree hx1] at hmem
    exact hb1 (congrArg Subtype.val (Subgroup.mem_bot.mp hmem))
  · subst hx
    exact fun b' => Subtype.ext (by simp)

end FreeAction

theorem natCard_modEq_one_of_centralizer_inf_eq_bot [Finite G] {p : ℕ} (hp : p.Prime)
    {W : Subgroup G} (hBW : B ≤ Subgroup.normalizer (W : Set G)) (hBcard : Nat.card B = p)
    (hfree : ∀ b ∈ B, b ≠ 1 → Subgroup.centralizer {b} ⊓ W = ⊥) :
    Nat.card W ≡ 1 [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  set B' := B.subgroupOf (Subgroup.normalizer (W : Set G)) with hB'
  have hcard' : Nat.card B' = p := by
    rw [hB', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBW).toEquiv, hBcard]
  have hfree' : ∀ b ∈ B', (b : G) ≠ 1 → Subgroup.centralizer {(b : G)} ⊓ W = ⊥ :=
    fun b hb => hfree _ (Subgroup.mem_subgroupOf.mp hb)
  have hpg : IsPGroup p B' := IsPGroup.of_card (n := 1) (by simpa using hcard')
  have h := hpg.card_modEq_card_fixedPoints (α := W)
  rw [fixedPoints_eq_singleton_one_of_centralizer_inf_eq_bot hp hcard' hfree'] at h
  simpa using h

theorem succ_two_mul_mul_natCard_le_natCard [Finite G] (hGodd : Odd (Nat.card G))
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (hVK : V < K)
    (hBK : B ≤ Subgroup.normalizer (K : Set G)) (hBV : B ≤ Subgroup.normalizer (V : Set G))
    (hBcard : Nat.card B = p)
    (hfree : ∀ b ∈ B, b ≠ 1 → Subgroup.centralizer {b} ⊓ K = ⊥) :
    (2 * p + 1) * Nat.card V ≤ Nat.card K := by
  have hVKle : V ≤ K := hVK.le
  set x := V.relIndex K with hxdef
  have hx : Nat.card V * x = Nat.card K := natCard_mul_relIndex hVKle
  have hV1 : Nat.card V ≡ 1 [MOD p] := by
    refine natCard_modEq_one_of_centralizer_inf_eq_bot hp hBV hBcard fun b hb hb1 => ?_
    refine le_antisymm ?_ bot_le
    calc Subgroup.centralizer {b} ⊓ V ≤ Subgroup.centralizer {b} ⊓ K := inf_le_inf_left _ hVKle
      _ = ⊥ := hfree b hb hb1
  have hK1 : Nat.card K ≡ 1 [MOD p] :=
    natCard_modEq_one_of_centralizer_inf_eq_bot hp hBK hBcard hfree
  have hx1 : x ≡ 1 [MOD p] :=
    calc x = 1 * x := (one_mul x).symm
      _ ≡ Nat.card V * x [MOD p] := (Nat.ModEq.mul_right x hV1).symm
      _ = Nat.card K := hx
      _ ≡ 1 [MOD p] := hK1
  have hxodd : Odd x := Odd.of_dvd_nat hGodd
    ((Subgroup.relIndex_dvd_card V K).trans (Subgroup.card_subgroup_dvd_card K))
  have hxpos : 0 < x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · rw [h, mul_zero] at hx
      exact absurd hx.symm Nat.card_pos.ne'
    · exact h
  have hxne1 : x ≠ 1 := fun h => by
    rw [h, mul_one] at hx
    exact hVK.ne (Subgroup.eq_of_le_of_card_ge hVKle hx.ge)
  have hpdvd : p ∣ x - 1 := (Nat.modEq_iff_dvd' hxpos).mp hx1.symm
  have h2dvd : 2 ∣ x - 1 := by
    obtain ⟨m, hm⟩ := hxodd
    exact ⟨m, by omega⟩
  have h2p : 2 * p ∣ x - 1 :=
    (Nat.coprime_two_left.mpr hpodd).mul_dvd_of_dvd_of_dvd h2dvd hpdvd
  have hxge : 2 * p + 1 ≤ x := by
    have := Nat.le_of_dvd (by omega) h2p
    omega
  calc (2 * p + 1) * Nat.card V = Nat.card V * (2 * p + 1) := by ring
    _ ≤ Nat.card V * x := Nat.mul_le_mul_left _ hxge
    _ = Nat.card K := hx

theorem two_mul_mul_natCard_lt_natCard [Finite G] (hGodd : Odd (Nat.card G))
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (hVK : V < K)
    (hBK : B ≤ Subgroup.normalizer (K : Set G)) (hBV : B ≤ Subgroup.normalizer (V : Set G))
    (hBcard : Nat.card B = p)
    (hfree : ∀ b ∈ B, b ≠ 1 → Subgroup.centralizer {b} ⊓ K = ⊥) :
    2 * p * Nat.card V < Nat.card K :=
  lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le (Nat.lt_succ_self _) le_rfl Nat.card_pos)
    (succ_two_mul_mul_natCard_le_natCard hGodd hp hpodd hVK hBK hBV hBcard hfree)

theorem sub_one_div_lt_sub_one_div [Finite G] (hGodd : Odd (Nat.card G))
    {p q : ℕ} (hp : p.Prime) (hpodd : Odd p) (hq : q.Prime) (_hqodd : Odd q) (hqp : q < p)
    (hVK : V < K) (hBK : B ≤ Subgroup.normalizer (K : Set G))
    (hBV : B ≤ Subgroup.normalizer (V : Set G)) (hBcard : Nat.card B = p)
    (hfree : ∀ b ∈ B, b ≠ 1 → Subgroup.centralizer {b} ⊓ K = ⊥)
    {e : ℕ} (he : 0 < e) (hepq : e ≤ p * q) :
    ((Nat.card V : ℝ) - 1) / p < ((Nat.card K : ℝ) - 1) / e := by
  have hkey := succ_two_mul_mul_natCard_le_natCard hGodd hp hpodd hVK hBK hBV hBcard hfree
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have he0 : (0 : ℝ) < e := by exact_mod_cast he
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hv1 : (1 : ℝ) ≤ Nat.card V := by exact_mod_cast Nat.card_pos (α := V)
  have hqp' : (q : ℝ) + 1 ≤ p := by exact_mod_cast hqp
  have hepq' : (e : ℝ) ≤ (p : ℝ) * q := by exact_mod_cast hepq
  have hkey' : (2 * (p : ℝ) + 1) * Nat.card V ≤ Nat.card K := by exact_mod_cast hkey
  rw [div_lt_div_iff₀ hp0 he0]
  nlinarith [mul_pos hp0 hq0, sq_nonneg ((Nat.card V : ℝ) - 1)]

end

end CFSG.FeitThompson
