module

public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Family
public import CFSG.LocalAnalysis.GL83PartI.I_6_10
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.Open.GLADefs

public section

namespace GL83.CompFam

open CFSG.Open

section Subnormal

theorem coprime_iff_isPiSubgroup {p : ℕ} (hp : p.Prime) {Y : Type*} [Group Y] (N : Subgroup Y) :
    Nat.Coprime p (Nat.card N) ↔ CFSG.IsPiSubgroup {q : Nat.Primes | q.val ≠ p} N := by
  rw [hp.coprime_iff_not_dvd]
  constructor
  · intro hN q hq hqp
    exact hN (hqp ▸ hq)
  · intro hN hdvd
    exact hN ⟨p, hp⟩ hdvd rfl

theorem glaPPrimeCore_eq_piCore {p : ℕ} (hp : p.Prime) (Y : Type*) [Group Y] :
    GLAPPrimeCore p Y = CFSG.piCore {q : Nat.Primes | q.val ≠ p} Y := by
  unfold GLAPPrimeCore CFSG.pPrimeCore CFSG.piCore
  congr 1
  ext N
  exact and_congr_right fun _ => coprime_iff_isPiSubgroup hp N

theorem eq_bot_of_isSubnormal_of_coprime {p : ℕ} (hp : p.Prime) {X : Type*} [Group X] [Finite X]
    (hcore : GLAPPrimeCore p X = ⊥) {V : Subgroup X} (hsn : IsSubnormal V ⊤)
    (hV : Nat.Coprime p (Nat.card V)) : V = ⊥ := by
  have hmsn : V.IsSubnormal :=
    CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain hsn
      Subgroup.IsSubnormal.top
  have h1 := CFSG.LocalCores.prime_set_core_subnormal_intersection
    {q : Nat.Primes | q.val ≠ p} hmsn
  have h2 : CFSG.piCore {q : Nat.Primes | q.val ≠ p} V = ⊤ :=
    eq_top_iff.2 (CFSG.LocalCores.le_piCore_of_normal inferInstance
      ((coprime_iff_isPiSubgroup hp _).1 (by rwa [Subgroup.card_top])))
  rw [h2, ← glaPPrimeCore_eq_piCore hp X, hcore, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    inf_bot_eq] at h1
  exact h1

end Subnormal

theorem one_le_pRank_aut {p : ℕ} (hp : p.Prime) {X : Type*} [Group X] [Finite X]
    (hcore : GLAPPrimeCore p X = ⊥) {K : Subgroup X} (hK : IsComponentOf K ⊤) :
    1 ≤ pRank p (⊤ : Subgroup (MulAut ↥K)) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hsn, hq⟩ := hK
  let f : ↥K →* MulAut ↥K := MulAut.conj
  have hker : f.ker = Subgroup.center ↥K := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro h x
      have hx := congrArg (fun φ : MulAut ↥K => φ x) h
      simp only [f, MulAut.conj_apply, MulAut.one_apply] at hx
      calc x * g = (g * x * g⁻¹) * g := by rw [hx]
        _ = g * x := by group
    · intro h
      refine MulEquiv.ext fun x => ?_
      simp only [f, MulAut.conj_apply, MulAut.one_apply]
      rw [mul_inv_eq_iff_eq_mul]
      exact (h x).symm
  have hdvd : p ∣ Nat.card f.range := by
    by_contra hnd
    obtain ⟨Q⟩ : Nonempty (Sylow p ↥K) := inferInstance
    have hQz : (Q : Subgroup ↥K) ≤ Subgroup.center ↥K := by
      rw [← hker, ← Subgroup.map_eq_bot_iff]
      have hmap : IsPGroup p ↥((Q : Subgroup ↥K).map f) := Q.isPGroup'.map f
      rcases hmap.card_eq_or_dvd with h1 | h1
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exact absurd (h1.trans (Subgroup.card_dvd_of_le (Subgroup.map_le_range f _))) hnd
    have hcomm : IsMulCommutative (Q : Subgroup ↥K) :=
      ⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.1 (hQz b.2) a)⟩⟩
    by_cases hpK : p ∣ Nat.card ↥K
    · have hZ : p ∣ Nat.card (Subgroup.center ↥K) := by
        have h1 := Subgroup.card_ker_mul_card_range f
        rw [hker] at h1
        rw [← h1] at hpK
        exact (hp.dvd_mul.1 hpK).resolve_right hnd
      exact not_isMulCommutative_sylow_of_perfect hq.1 hZ Q hcomm
    · have hbot : K = ⊥ :=
        eq_bot_of_isSubnormal_of_coprime hp hcore hsn (hp.coprime_iff_not_dvd.2 hpK)
      have hnt := CFSG.ComponentClassification.Quasisimple.nontrivial hq
      exact (K.nontrivial_iff_ne_bot.mp hnt) hbot
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := MulAut ↥K) p
    (hdvd.trans (Subgroup.card_subgroup_dvd_card f.range))
  have hxp : x ^ p = 1 := by simpa [hx] using pow_orderOf_eq_one x
  have hE : IsElemAbelian p (Subgroup.zpowers x) := by
    refine ⟨inferInstance, fun y hy => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  have hcard : Nat.card (Subgroup.zpowers x) = p ^ 1 := by
    rw [Nat.card_zpowers, hx, pow_one]
  exact CFSG.SectionRank.le_pRank hp.one_lt le_top hE hcard

section Stab

variable {X : Type*} [Group X] [Finite X]

theorem card_stab_le {p : ℕ} [Fact p.Prime] {B : Subgroup X} (hB : IsElemAbelian p B)
    (K : Subgroup X) :
    Nat.card (stab B K) ≤ p ^ pRank p (⊤ : Subgroup (MulAut ↥K)) * Nat.card (cen B K) := by
  have hA : stab B K ≤ Subgroup.normalizer (K : Set X) := inf_le_right
  let ψ : ↥(stab B K) →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hA)
  have hAe : IsElemAbelian p (stab B K) := elem_mono hB inf_le_left
  have hker : ψ.ker.map (stab B K).subtype ≤ cen B K := by
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_cen]
    refine ⟨(mem_stab.1 a.2).1, fun x hx => ?_⟩
    have h1 : ψ a = 1 := ha
    have h2 := congrArg (fun φ : MulAut ↥K => ((φ ⟨x, hx⟩ : ↥K) : X)) h1
    simp only [ψ, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
    have h3 : (a : X) * x * (a : X)⁻¹ = x := h2
    change (a : X) * x = x * (a : X)
    calc (a : X) * x = (a : X) * x * (a : X)⁻¹ * (a : X) := by group
      _ = x * (a : X) := by rw [h3]
  have hrange : IsElemAbelian p ψ.range := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, a, rfl⟩ ⟨_, a', rfl⟩
      apply Subtype.ext
      show ψ a * ψ a' = ψ a' * ψ a
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (elem_comm hAe a.2 a'.2)
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have : a ^ p = 1 := Subtype.ext (hAe.2 a a.2)
      rw [this, map_one]
  obtain ⟨j, hj⟩ := exists_card_eq_pow hrange
  have hjr : j ≤ pRank p (⊤ : Subgroup (MulAut ↥K)) :=
    CFSG.SectionRank.le_pRank (Fact.out : p.Prime).one_lt le_top hrange hj
  have hkc : Nat.card ψ.ker ≤ Nat.card (cen B K) := by
    rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective (stab B K))]
    exact Subgroup.card_le_of_le hker
  calc Nat.card (stab B K) = Nat.card ψ.ker * Nat.card ψ.range :=
        (Subgroup.card_ker_mul_card_range ψ).symm
    _ ≤ Nat.card (cen B K) * p ^ pRank p (⊤ : Subgroup (MulAut ↥K)) := by
        rw [hj]
        exact Nat.mul_le_mul hkc (Nat.pow_le_pow_right (Fact.out : p.Prime).pos hjr)
    _ = p ^ pRank p (⊤ : Subgroup (MulAut ↥K)) * Nat.card (cen B K) := mul_comm _ _

end Stab

section Conj

variable {X : Type*} [Group X]

@[expose] def conjSet (B K : Subgroup X) : Set (Subgroup X) := {K' | ∃ b ∈ B, K' = cj b K}

theorem mem_conjSet_self (B K : Subgroup X) : K ∈ conjSet B K :=
  ⟨1, B.one_mem, (cj_one K).symm⟩

theorem isComponentOf_cj {K : Subgroup X} (hK : IsComponentOf K ⊤) (b : X) :
    IsComponentOf (cj b K) ⊤ :=
  (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj b) K).2 hK

variable [Finite X]

theorem isFam_conjSet {p : ℕ} {B K : Subgroup X} (hB : IsElemAbelian p B)
    (hK : IsComponentOf K ⊤) : IsFam p B (conjSet B K) where
  elem := hB
  nonempty := ⟨K, mem_conjSet_self B K⟩
  quasi := by
    rintro _ ⟨b, -, rfl⟩
    exact (isComponentOf_cj hK b).2.2
  comm := by
    rintro _ ⟨b, -, rfl⟩ _ ⟨c, -, rfl⟩ hne x hx y hy
    have h := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _
      (isComponentOf_cj hK b) (isComponentOf_cj hK c) hne
    have hxc : x ∈ Subgroup.centralizer (cj c K : Set X) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 h hx
    exact (Subgroup.mem_centralizer_iff.1 hxc y hy).symm
  smul_mem := by
    rintro _ ⟨b, hb, rfl⟩ c hc
    exact ⟨c * b, B.mul_mem hc hb, (cj_mul c b K).symm⟩
  trans := by
    rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩
    exact ⟨c * b⁻¹, B.mul_mem hc (B.inv_mem hb), by rw [← cj_mul, inv_mul_cancel_right]⟩

end Conj

end GL83.CompFam
