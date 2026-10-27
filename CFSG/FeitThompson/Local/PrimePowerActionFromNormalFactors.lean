module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Local.QuadraticActionsDescendSections
import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
import Mathlib.GroupTheory.Nilpotent

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {A P : Type*} [Group A] [Group P] {ρ : A →* MulAut P} {N : Subgroup P}

def sectionStabilizer (N : Subgroup P) : Subgroup (MulAut P) where
  carrier := {e | (∀ v ∈ N, e v = v) ∧ ∀ v : P, v⁻¹ * e v ∈ N}
  one_mem' := by simp
  mul_mem' := by
    rintro e f ⟨he₁, he₂⟩ ⟨hf₁, hf₂⟩
    refine ⟨fun v hv => ?_, fun v => ?_⟩
    · rw [MulAut.mul_apply, hf₁ v hv, he₁ v hv]
    · rw [MulAut.mul_apply, show v⁻¹ * e (f v) = (v⁻¹ * f v) * ((f v)⁻¹ * e (f v)) by group]
      exact mul_mem (hf₂ v) (he₂ _)
  inv_mem' := by
    rintro e ⟨he₁, he₂⟩
    refine ⟨fun v hv => ?_, fun v => ?_⟩
    · conv_lhs => rw [← he₁ v hv]
      simp
    · rw [show v⁻¹ * e⁻¹ v = ((e⁻¹ v)⁻¹ * e (e⁻¹ v))⁻¹ by
        simp only [MulAut.apply_inv_self]; group]
      exact inv_mem (he₂ _)

theorem mem_sectionStabilizer_iff {e : MulAut P} :
    e ∈ sectionStabilizer N ↔ (∀ v ∈ N, e v = v) ∧ ∀ v : P, v⁻¹ * e v ∈ N := Iff.rfl

theorem apply_eq_self_of_mem_sectionStabilizer {e : MulAut P} (he : e ∈ sectionStabilizer N)
    {v : P} (hv : v ∈ N) : e v = v := (mem_sectionStabilizer_iff.1 he).1 v hv

theorem inv_mul_apply_mem_of_mem_sectionStabilizer {e : MulAut P}
    (he : e ∈ sectionStabilizer N) (v : P) : v⁻¹ * e v ∈ N :=
  (mem_sectionStabilizer_iff.1 he).2 v

theorem isInvariantSubgroup_subtype_of_le_sectionStabilizer {Q : Subgroup (MulAut P)}
    (hQ : Q ≤ sectionStabilizer N) : IsInvariantSubgroup Q.subtype N := by
  rw [isInvariantSubgroup_iff_forall_map_eq]
  intro b
  refine le_antisymm ?_ fun v hv => ⟨v, hv, ?_⟩
  · rintro x ⟨w, hw, rfl⟩
    rwa [show ((Q.subtype b : MulAut P) : P →* P) w = w from
      apply_eq_self_of_mem_sectionStabilizer (hQ b.2) hw]
  · exact apply_eq_self_of_mem_sectionStabilizer (hQ b.2) hv

private theorem isSolvable_zpowers (c : MulAut P) : Group.IsSolvable (Subgroup.zpowers c) := by
  refine Group.isSolvable_of_comm fun a b => ?_
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 a.2
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 b.2
  refine Subtype.ext ?_
  push_cast
  rw [← hm, ← hn]
  group

theorem eq_one_of_pointwise_fixing_of_trivial_on_quotient [Finite P] [N.Normal]
    [Group.IsSolvable ↥N] {c : MulAut P} (hcop : (orderOf c).Coprime (Nat.card P))
    (hfix : ∀ v ∈ N, c v = v) (hquot : ∀ v : P, v⁻¹ * c v ∈ N) : c = 1 := by
  set Q : Subgroup (MulAut P) := Subgroup.zpowers c with hQdef
  have hQsolv : Group.IsSolvable ↥Q := isSolvable_zpowers c
  have hle : Q ≤ sectionStabilizer N :=
    Subgroup.zpowers_le.2 (mem_sectionStabilizer_iff.2 ⟨hfix, hquot⟩)
  have hinv : IsInvariantSubgroup Q.subtype N :=
    isInvariantSubgroup_subtype_of_le_sectionStabilizer hle
  have hcop' : (Nat.card ↥Q).Coprime (Nat.card P) := by rwa [hQdef, Nat.card_zpowers]
  ext v
  obtain ⟨n, hnN, hn⟩ := exists_mem_forall_apply_mul_eq (ρ := Q.subtype) hinv hcop'
    (v := v) fun b => inv_mul_apply_mem_of_mem_sectionStabilizer (hle b.2) v
  have hc : c (v * n) = v * n := hn ⟨c, Subgroup.mem_zpowers c⟩
  rw [map_mul, hfix n hnN] at hc
  simpa using mul_right_cancel hc

private theorem eq_one_of_isPGroup_of_pow_eq_one {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    {H : Subgroup G} (hH : IsPGroup p H) {x : G} (hx : x ∈ H) {m : ℕ} (hm : ¬ p ∣ m)
    (hxm : x ^ m = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hH ⟨x, hx⟩
  have hk' : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcop : (p ^ k).Coprime m := Nat.Coprime.pow_left _ (hp.coprime_iff_not_dvd.2 hm)
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one hxm))

theorem isPGroup_range_of_isPGroup_factor_ranges {p : ℕ} (hp : p.Prime) [Finite P]
    (hP : IsPGroup p P) [N.Normal] (hN : IsInvariantSubgroup ρ N)
    (hres : IsPGroup p hN.restrictAut.range) (hquo : IsPGroup p hN.quotientAut.range) :
    IsPGroup p ρ.range := by
  have hpf : Fact p.Prime := ⟨hp⟩
  have hnil : Group.IsNilpotent P := hP.isNilpotent
  have hNsolv : Group.IsSolvable ↥N := inferInstance
  obtain ⟨s, hs⟩ := hP.exists_card_eq
  intro g
  obtain ⟨a, ha⟩ := g.2
  refine ⟨(orderOf (ρ a)).factorization p, ?_⟩
  have hne : orderOf (ρ a) ≠ 0 := (orderOf_pos (ρ a)).ne'
  set d : ℕ := p ^ (orderOf (ρ a)).factorization p with hd
  set m : ℕ := orderOf (ρ a) / d with hm
  have hdvd : d ∣ orderOf (ρ a) := Nat.ordProj_dvd _ _
  have hmp : ¬ p ∣ m := Nat.not_dvd_ordCompl hp hne
  set c : MulAut P := ρ (a ^ d) with hc
  have hcpow : c = ρ a ^ d := by rw [hc, map_pow]
  have hordc : orderOf c = m := by
    rw [hcpow, orderOf_pow_of_dvd (pow_pos hp.pos _).ne' hdvd]
  have hbm : ρ ((a ^ d) ^ m) = 1 := by
    rw [map_pow, ← hc, ← hordc]; exact pow_orderOf_eq_one c
  have hr : hN.restrictAut (a ^ d) = 1 := by
    refine eq_one_of_isPGroup_of_pow_eq_one hp hres ⟨a ^ d, rfl⟩ hmp ?_
    rw [← map_pow]
    ext x
    rw [hN.coe_restrictAut_apply, hbm]
    simp
  have hq : hN.quotientAut (a ^ d) = 1 := by
    refine eq_one_of_isPGroup_of_pow_eq_one hp hquo ⟨a ^ d, rfl⟩ hmp ?_
    rw [← map_pow]
    ext x
    induction x using QuotientGroup.induction_on with
    | H v => rw [hN.quotientAut_mk, hbm]; simp
  have hfix : ∀ v ∈ N, c v = v := by
    intro v hv
    have h := hN.coe_restrictAut_apply (a ^ d) ⟨v, hv⟩
    rw [hr] at h
    simpa [hc] using h.symm
  have hquot : ∀ v : P, v⁻¹ * c v ∈ N := by
    intro v
    have h := hN.quotientAut_mk (a ^ d) v
    rw [hq] at h
    exact QuotientGroup.eq.1 (by simpa [hc] using h)
  have hcop : (orderOf c).Coprime (Nat.card P) := by
    rw [hordc, hs]
    exact Nat.Coprime.pow_right _ (hp.coprime_iff_not_dvd.2 hmp).symm
  have hc1 : ρ a ^ d = 1 := by
    rw [← hcpow]
    exact eq_one_of_pointwise_fixing_of_trivial_on_quotient hcop hfix hquot
  exact Subtype.ext (by push_cast; rw [← ha]; exact hc1)

theorem exists_natCard_range_eq_pow_of_isPGroup_factor_ranges {p : ℕ} (hp : p.Prime) [Finite A]
    [Finite P] (hP : IsPGroup p P) [N.Normal] (hN : IsInvariantSubgroup ρ N)
    (hres : IsPGroup p hN.restrictAut.range) (hquo : IsPGroup p hN.quotientAut.range) :
    ∃ n : ℕ, Nat.card ρ.range = p ^ n :=
  haveI : Fact p.Prime := ⟨hp⟩
  (isPGroup_range_of_isPGroup_factor_ranges hp hP hN hres hquo).exists_card_eq

end CFSG.FeitThompson
