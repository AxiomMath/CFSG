module

public import CFSG.FeitThompson.Local.SmallRankLineInMaximalPlane
import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.NormalSylowDirectProduct
import CFSG.FeitThompson.Foundations.NilpotentSylowNormalCharacteristic
public import Mathlib.GroupTheory.Nilpotent
import CFSG.FeitThompson.Local.FreeActionKernelGrowthProperInvariant
import CFSG.FeitThompson.Definitions.AlphaPrimesOfAFiniteGroup
import CFSG.FeitThompson.Foundations.PGroupNontrivialCenter
import CFSG.FeitThompson.Local.CentralSylowFixedFreeCycle

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup MulAction

variable {G : Type*} [Group G] {R : Subgroup G} {n : ℕ} {z : G}

def omega1Center (n : ℕ) (R : Subgroup G) : Subgroup G where
  carrier := {z | z ∈ R ∧ (∀ y ∈ R, y * z = z * y) ∧ z ^ n = 1}
  one_mem' := ⟨one_mem R, fun y _ => by rw [mul_one, one_mul], one_pow n⟩
  mul_mem' := by
    rintro a b ⟨haR, hac, han⟩ ⟨hbR, hbc, hbn⟩
    refine ⟨mul_mem haR hbR, fun y hy => ?_, ?_⟩
    · rw [← mul_assoc, hac y hy, mul_assoc, hbc y hy, ← mul_assoc]
    · have hab : Commute a b := (hac b hbR).symm
      rw [hab.mul_pow, han, hbn, mul_one]
  inv_mem' := by
    rintro a ⟨haR, hac, han⟩
    refine ⟨inv_mem haR, fun y hy => ?_, ?_⟩
    · exact (Commute.inv_right (hac y hy : Commute y a)).eq
    · rw [inv_pow, han, inv_one]

@[simp]
theorem mem_omega1Center :
    z ∈ omega1Center n R ↔ z ∈ R ∧ (∀ y ∈ R, y * z = z * y) ∧ z ^ n = 1 := Iff.rfl

theorem omega1Center_le : omega1Center n R ≤ R := fun _ hz => hz.1

theorem omega1Center_le_centralizer :
    omega1Center n R ≤ centralizer (R : Set G) := fun _ hz => mem_centralizer_iff.2 hz.2.1

theorem pow_eq_one_of_mem_omega1Center (hz : z ∈ omega1Center n R) : z ^ n = 1 := hz.2.2

theorem isElementaryAbelian_omega1Center : IsElementaryAbelian n (omega1Center n R) :=
  isElementaryAbelian_iff.2
    ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (by simpa using b.2.2.1 a.1 a.2.1),
      fun _ hz => hz.2.2⟩

theorem mem_omega1Center_of_mem_center {y : R} (hy : y ∈ center R) (hyn : (y : G) ^ n = 1) :
    (y : G) ∈ omega1Center n R :=
  ⟨y.2, fun w hw => congrArg Subtype.val (mem_center_iff.1 hy ⟨w, hw⟩), hyn⟩

theorem map_omega1Center (f : G ≃* G) (hf : R.map f.toMonoidHom = R) :
    (omega1Center n R).map f.toMonoidHom = omega1Center n R := by
  have key : ∀ g : G ≃* G, R.map g.toMonoidHom = R →
      (omega1Center n R).map g.toMonoidHom ≤ omega1Center n R := by
    rintro g hg _ ⟨a, ⟨haR, hac, han⟩, rfl⟩
    refine ⟨hg ▸ mem_map_of_mem _ haR, fun y hy => ?_, by rw [← map_pow, han, map_one]⟩
    have hy' : g.symm y ∈ R := by
      rw [← hg] at hy
      obtain ⟨b, hb, rfl⟩ := hy
      simpa using hb
    have h := hac _ hy'
    calc y * g a = g (g.symm y * a) := by simp
      _ = g (a * g.symm y) := by rw [h]
      _ = g a * y := by simp
  have hf' : R.map f.symm.toMonoidHom = R := by
    apply_fun (fun K => Subgroup.map f.symm.toMonoidHom K) at hf
    rw [Subgroup.map_map] at hf
    simpa using hf.symm
  refine le_antisymm (key f hf) fun w hw => ⟨f.symm w, key f.symm hf' (mem_map_of_mem _ hw), ?_⟩
  simp

theorem normalizer_le_normalizer_omega1Center :
    normalizer (R : Set G) ≤ normalizer (omega1Center n R : Set G) := fun _ hg =>
  mem_normalizer_iff_map_conj_eq.2
    (map_omega1Center _ (mem_normalizer_iff_map_conj_eq.1 hg))

theorem le_succ_of_dvd_pow_sub_one {p r m : ℕ} (hp : p.Prime) (hr : 2 ≤ r) (hm1 : 1 ≤ m)
    (hm2 : m ≤ 2) (hdvd : p ∣ r ^ m - 1) : p ≤ r + 1 := by
  interval_cases m
  · rw [pow_one] at hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  · have hfac : r ^ 2 - 1 = (r - 1) * (r + 1) := by
      cases r with
      | zero => omega
      | succ k => simp [pow_two]; ring_nf; omega
    rw [hfac] at hdvd
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · have := Nat.le_of_dvd (by omega) h
      omega
    · have := Nat.le_of_dvd (by omega) h
      omega

variable {S H R0 B : Subgroup G} {p r : ℕ} {x : G}

theorem prime_le_succ_of_centralizer_le_of_free_action [Finite G] (hp : p.Prime) (hr : r.Prime)
    (hH : Group.IsNilpotent ↥H) (hR0 : R0 ≤ S ⊓ H) (hR0bot : R0 ≠ ⊥)
    (hR0comm : IsMulCommutative R0)
    (hR0syl : Nat.card R0 = r ^ (Nat.card S).factorization r)
    (hrank : 3 ∉ elementaryAbelianRanks r R0)
    (hxR0 : x ∈ R0) (hxS : centralizer {x} ≤ S)
    (hBN : B ≤ normalizer (H : Set G)) (hBcard : Nat.card B = p)
    (hfree : ∀ b ∈ B, b ≠ 1 → centralizer {b} ⊓ H = ⊥) :
    p ≤ r + 1 := by
  have := Fact.mk hr
  have := hH
  have hR0H : R0 ≤ H := le_trans hR0 inf_le_right
  have hR0p : IsPGroup r (R0.subgroupOf H) :=
    (IsPGroup.of_card hR0syl).of_equiv (subgroupOfEquivOfLe hR0H).symm
  obtain ⟨T, hT⟩ := hR0p.exists_le_sylow
  set R : Subgroup G := (T : Subgroup ↥H).map H.subtype with hRdef
  have hR0R : R0 ≤ R := by
    rw [hRdef, ← map_subgroupOf_eq_of_le hR0H]
    exact map_mono hT
  have hRp : IsPGroup r R :=
    T.isPGroup'.of_equiv (Subgroup.equivMapOfInjective _ _ H.subtype_injective)
  have hCR : R ⊓ centralizer {x} = R0 := by
    refine (eq_of_le_of_card_ge (le_inf hR0R fun y hy => ?_) ?_).symm
    · exact mem_centralizer_singleton_iff.2
        (by simpa using congrArg Subtype.val (hR0comm.is_comm.comm (⟨y, hy⟩ : R0) ⟨x, hxR0⟩))
    · obtain ⟨k, hk⟩ := (hRp.to_le (inf_le_left : R ⊓ centralizer {x} ≤ R)).exists_card_eq
      have hdvdS : Nat.card (R ⊓ centralizer {x} : Subgroup G) ∣ Nat.card S :=
        card_dvd_of_le (le_trans inf_le_right hxS)
      rw [hk] at hdvdS ⊢
      rw [hR0syl]
      exact Nat.pow_le_pow_right hr.pos
        ((hr.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hdvdS)
  set A : Subgroup G := omega1Center r R with hAdef
  have hAR0 : A ≤ R0 := by
    rw [← hCR]
    exact le_inf omega1Center_le
      (le_trans omega1Center_le_centralizer (centralizer_le (by simpa using hR0R hxR0)))
  have hRnontrivial : Nontrivial R := by
    rw [nontrivial_iff_ne_bot]
    intro hRbot
    exact hR0bot (le_bot_iff.1 (hRbot ▸ hR0R))
  have hAbot : A ≠ ⊥ := by
    obtain ⟨k, hk⟩ := hRp.exists_card_eq
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h, pow_zero, Nat.card_eq_one_iff_unique] at hk
        exact absurd hk.1 (not_subsingleton _)
      · exact h
    obtain ⟨w, hw, hworder⟩ := exists_mem_center_orderOf_eq hr hk hk1
    have hwr : (w : G) ^ r = 1 := by
      exact_mod_cast congrArg Subtype.val (hworder ▸ pow_orderOf_eq_one w)
    have hwG : (w : G) ∈ A := mem_omega1Center_of_mem_center hw hwr
    intro hcon
    rw [hcon, mem_bot] at hwG
    rw [show w = 1 from Subtype.ext hwG, orderOf_one] at hworder
    exact hr.one_lt.ne hworder
  obtain ⟨m, hm⟩ := (isElementaryAbelian_omega1Center (n := r) (R := R)).exists_natCard_eq_pow hr
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, pow_zero, Subgroup.card_eq_one] at hm
      exact absurd hm hAbot
    · exact h
  have hm2 : m ≤ 2 := by
    by_contra hcon
    exact hrank (mem_elementaryAbelianRanks_of_le (by omega)
      (IsElementaryAbelian.mem_elementaryAbelianRanks_of_le hr
        isElementaryAbelian_omega1Center hm hAR0))
  have hTchar : (T : Subgroup ↥H).Characteristic := sylow_characteristic_of_isNilpotent T
  have hBA : B ≤ normalizer (A : Set G) :=
    le_trans hBN (le_trans (normalizer_le_normalizer_map_subtype H (T : Subgroup ↥H))
      normalizer_le_normalizer_omega1Center)
  have hcong : Nat.card A ≡ 1 [MOD p] :=
    natCard_modEq_one_of_centralizer_inf_eq_bot hp hBA hBcard fun b hb hb1 =>
      le_antisymm (le_trans (inf_le_inf_left _ (le_trans hAR0 hR0H))
        (le_of_eq (hfree b hb hb1))) bot_le
  rw [hm] at hcong
  exact le_succ_of_dvd_pow_sub_one hp hr.two_le hm1 hm2
    ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hr.pos)).1 hcong.symm)

theorem prime_le_succ_of_centralizer_le_of_free_action_of_sylow_family [Finite G] (hp : p.Prime)
    (hr : r.Prime)
    (hH : ∃ (P : (Nat.card ↥H).primeFactors → Subgroup ↥H)
      (hcard : ∀ q, Nat.card (P q) = (q : ℕ) ^ (Nat.card ↥H).factorization (q : ℕ))
      (hn : ∀ q, (P q).Normal), Function.Bijective (normalSylowPiHom P hcard hn))
    (hR0 : R0 ≤ S ⊓ H) (hR0bot : R0 ≠ ⊥) (hR0comm : IsMulCommutative R0)
    (hR0syl : Nat.card R0 = r ^ (Nat.card S).factorization r)
    (hrank : 3 ∉ elementaryAbelianRanks r R0)
    (hxR0 : x ∈ R0) (hxS : centralizer {x} ≤ S)
    (hBN : B ≤ normalizer (H : Set G)) (hBcard : Nat.card B = p)
    (hfree : ∀ b ∈ B, b ≠ 1 → centralizer {b} ⊓ H = ⊥) :
    p ≤ r + 1 :=
  prime_le_succ_of_centralizer_le_of_free_action hp hr
    ((isNilpotent_iff_exists_normal_sylow_family ↥H).2 hH) hR0 hR0bot hR0comm hR0syl hrank hxR0
    hxS hBN hBcard hfree

end

end CFSG.FeitThompson
