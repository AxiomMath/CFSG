module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.Sylow
import CFSG.FeitThompson.Representations.InvariantLineAbelianNormalSylowKernel
import CFSG.FeitThompson.Representations.NormalPSubgroupInvariantLine
import CFSG.FeitThompson.Representations.OddSpecialLinearPrimeCore
import CFSG.FeitThompson.Representations.NormalPrimeKernelCommutative
import CFSG.FeitThompson.Representations.TrivialDeterminantKernelAbelianOrder

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Matrix Subgroup

variable {k : Type*} [Field k] [Finite k] {p f q : ℕ}

private theorem exists_sylow_of_isMulCommutative (hp : p.Prime) {G : Subgroup (GL (Fin 2) k)}
    (hab : IsMulCommutative G) (hnd : ¬ p ∣ Nat.card G) :
    ∃ P : Sylow p G, (P : Subgroup G).Normal ∧ IsMulCommutative (P : Subgroup G) ∧
      _root_.commutator G ≤ (P : Subgroup G) ∧ Nat.card (P : Subgroup G) ∣ Nat.card k ∧
      ∀ x ∈ (P : Subgroup G), x ^ p = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨IsPGroup.toSylow (P := (⊥ : Subgroup G)) (IsPGroup.of_card (n := 0) (by simp))
    (by rwa [Subgroup.index_bot]), ?_⟩
  rw [IsPGroup.toSylow_coe]
  refine ⟨inferInstance, inferInstance, ?_, ?_, fun x hx => ?_⟩
  · rw [(commutator_eq_bot_iff _).2 hab]
  · simp
  · rw [Subgroup.mem_bot] at hx
    simp [hx]

private theorem exists_sylow_of_normal_pGroup [CharP k p] (hp : p.Prime)
    {G R : Subgroup (GL (Fin 2) k)} (hRG : R ≤ G) (hRnorm : (R.subgroupOf G).Normal)
    (hR1 : R ≠ ⊥) (hRp : IsPGroup p R) :
    ∃ P : Sylow p G, (P : Subgroup G).Normal ∧ IsMulCommutative (P : Subgroup G) ∧
      _root_.commutator G ≤ (P : Subgroup G) ∧ Nat.card (P : Subgroup G) ∣ Nat.card k ∧
      ∀ x ∈ (P : Subgroup G), x ^ p = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := hRp.exists_card_eq
  obtain ⟨w, hw0, hWeq⟩ := exists_eq_span_singleton_of_finrank_eq_one
    (finrank_glFixedSubmodule_eq_one (char_dvd_natCard (k := k) (p := p)) hR1 ha)
  have hG : ∀ g ∈ G, g • w ∈ Submodule.span k {w} := by
    intro g hg
    rw [← hWeq]
    exact smul_mem_glFixedSubmodule hRG hRnorm hg (hWeq ▸ Submodule.mem_span_singleton_self w)
  have hchar : ringChar k = p := (ringChar.eq_iff (R := k) (p := p)).2 inferInstance
  refine ⟨lineUnipotentSylow (p := p) hw0 hG, ?_⟩
  rw [coe_lineUnipotentSylow]
  refine ⟨lineUnipotentCore_span_singleton_normal hG,
    lineUnipotentCore_isMulCommutative hw0,
    commutator_le_lineUnipotentCore hw0 hG,
    card_lineUnipotentCore_dvd hw0, fun x hx => ?_⟩
  have h := pow_ringChar_eq_one_of_mem_lineUnipotentCore (G := G) hw0 ⟨x, hx⟩
  rw [hchar] at h
  exact congrArg Subtype.val h

theorem exists_normal_abelian_sylow_of_odd [CharP k p] (hp : p.Prime)
    {G : Subgroup (GL (Fin 2) k)} (hGodd : Odd (Nat.card G)) :
    ∃ P : Sylow p G, (P : Subgroup G).Normal ∧ IsMulCommutative (P : Subgroup G) ∧
      _root_.commutator G ≤ (P : Subgroup G) ∧ Nat.card (P : Subgroup G) ∣ Nat.card k ∧
      ∀ x ∈ (P : Subgroup G), x ^ p = 1 := by
  set S := (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := k)).range with hS
  set D := G ⊓ S with hD
  have hDG : D ≤ G := inf_le_left
  have hDS : D ≤ S := inf_le_right
  have hDnorm : (D.subgroupOf G).Normal := by
    rw [hD, Subgroup.inf_subgroupOf_left, hS, range_toGL_eq_ker_det]
    exact (MonoidHom.normal_ker _).subgroupOf G
  by_cases hD1 : D = ⊥
  ·
    exact exists_sylow_of_isMulCommutative hp (isMulCommutative_of_inf_specialLinear_eq_bot hD1)
      (not_dvd_natCard_of_inf_specialLinear_eq_bot hp hD1)
  ·
    have hDodd : Odd (Nat.card D) := hGodd.of_dvd_nat (natCard_dvd_natCard_of_le hDG)
    obtain ⟨r, hr, hR1⟩ := exists_prime_pCoreIn_ne_bot hp hD1 hDodd hDS
    have hRD : pCoreIn r D ≤ D := pCoreIn_le r D
    have hRG : pCoreIn r D ≤ G := hRD.trans hDG
    have hRnorm : ((pCoreIn r D).subgroupOf G).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hRG).mpr (le_normalizer_pCoreIn r
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hDG).mp hDnorm))
    have hRp : IsPGroup r (pCoreIn r D) := isPGroup_pCoreIn hr D
    by_cases hrp : r = p
    ·
      subst hrp
      exact exists_sylow_of_normal_pGroup hp hRG hRnorm hR1 hRp
    ·
      obtain ⟨hab, hnd⟩ := isMulCommutative_and_not_dvd_of_normal_prime_kernel_isPGroup hp hr hrp
        hGodd hRG hRnorm hR1 hRp (hRD.trans hDS)
      exact exists_sylow_of_isMulCommutative hp hab hnd

theorem isMulCommutative_of_odd_of_not_dvd [CharP k p] (hp : p.Prime)
    {G : Subgroup (GL (Fin 2) k)} (hGodd : Odd (Nat.card G)) (hnd : ¬ p ∣ Nat.card G) :
    IsMulCommutative G := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, -, -, hcomm, -, -⟩ := exists_normal_abelian_sylow_of_odd hp hGodd
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  have hn0 : n = 0 := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact h
    · exact absurd ((dvd_pow_self p h.ne').trans
        (hn ▸ Subgroup.card_subgroup_dvd_card (P : Subgroup G))) hnd
  rw [hn0, pow_zero] at hn
  rw [← commutator_eq_bot_iff, ← le_bot_iff]
  exact hcomm.trans (le_of_eq (Subgroup.card_eq_one.mp hn))

theorem exists_normal_abelian_sylow_of_odd_card {k : Type*} [Field k] (hp : p.Prime) (_hf : 1 ≤ f)
    (hq : q = p ^ f) (hcard : Nat.card k = q) {G : Subgroup (GL (Fin 2) k)}
    (hGodd : Odd (Nat.card G)) :
    (∃ P : Sylow p G, (P : Subgroup G).Normal ∧ IsMulCommutative (P : Subgroup G) ∧
        _root_.commutator G ≤ (P : Subgroup G) ∧ Nat.card (P : Subgroup G) ∣ q ∧
        ∀ x ∈ (P : Subgroup G), x ^ p = 1) ∧
      (¬ p ∣ Nat.card G → IsMulCommutative G) :=
  have : Finite k :=
    Nat.finite_of_card_ne_zero (by rw [hcard, hq]; exact pow_ne_zero _ hp.pos.ne')
  have : CharP k p := charP_of_natCard_eq_prime_pow hp (by rw [hcard, hq])
  ⟨by simpa only [hcard] using exists_normal_abelian_sylow_of_odd (p := p) hp hGodd,
    isMulCommutative_of_odd_of_not_dvd hp hGodd⟩

end

end CFSG.FeitThompson
