module

import CFSG.FeitThompson.Representations.CharacterValuesAlgebraicIntegers
import CFSG.FeitThompson.Representations.SymmetricAlternatingSquareCharacters
import CFSG.FeitThompson.Representations.RationalAlgebraicIntegerIsInteger
public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem isIntegral_trace_of_isOfFinOrder [FiniteDimensional ℂ V] {T : Module.End ℂ V}
    (hT : IsOfFinOrder T) : IsIntegral ℤ (LinearMap.trace ℂ V T) := by
  obtain ⟨m, hm, hTm⟩ := isOfFinOrder_iff_pow_eq_one.1 hT
  have hcoe : (hT.isUnit.unit : Module.End ℂ V) = T := hT.isUnit.unit_spec
  have hu : IsOfFinOrder hT.isUnit.unit := by
    refine isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, Units.val_inj.1 ?_⟩
    push_cast
    rw [hcoe, hTm]
  have h := Representation.isIntegral_character_of_isOfFinOrder
    ((Units.coeHom (Module.End ℂ V) : (Module.End ℂ V)ˣ →* Module.End ℂ V) :
      Representation ℂ (Module.End ℂ V)ˣ V) hu
  simpa [Representation.character, hcoe] using h

theorem isIntegral_trace_mul_of_commute [FiniteDimensional ℂ V] {E P : Module.End ℂ V}
    (hE : IsOfFinOrder E) (hP : IsIdempotentElem P) (hEP : Commute E P) :
    IsIntegral ℤ (LinearMap.trace ℂ V (E * P)) := by
  obtain ⟨m, hm, hEm⟩ := isOfFinOrder_iff_pow_eq_one.1 hE
  have hcompl : IsCompl (LinearMap.range P) (LinearMap.ker P) :=
    LinearMap.IsIdempotentElem.isCompl hP
  have hcomm : ∀ v : V, E (P v) = P (E v) := fun v => by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, hEP.eq]
  have hPid : ∀ v ∈ LinearMap.range P, P v = v := by
    rintro v ⟨w, rfl⟩
    calc P (P w) = (P * P) w := rfl
      _ = P w := by rw [hP]
  have hEW : ∀ v ∈ LinearMap.range P, E v ∈ LinearMap.range P := by
    rintro v ⟨w, rfl⟩
    exact ⟨E w, (hcomm w).symm⟩
  have hEPW : ∀ v ∈ LinearMap.range P, (E * P) v ∈ LinearMap.range P := by
    intro v hv
    rw [Module.End.mul_apply, hPid v hv]
    exact hEW v hv
  have hEPK : ∀ v ∈ LinearMap.ker P, (E * P) v ∈ LinearMap.ker P := by
    intro v hv
    rw [Module.End.mul_apply, LinearMap.mem_ker.1 hv, map_zero]
    exact Submodule.zero_mem _
  rw [trace_eq_add_of_isCompl hcompl (E * P) hEPW hEPK]
  have hzero : (E * P).restrict hEPK = 0 := by
    ext v
    simp [LinearMap.restrict_apply, LinearMap.mem_ker.1 v.2]
  have hrestr : (E * P).restrict hEPW = E.restrict hEW :=
    restrict_congr hEPW hEW fun v hv => by rw [Module.End.mul_apply, hPid v hv]
  rw [hzero, hrestr, map_zero, add_zero]
  refine isIntegral_trace_of_isOfFinOrder (isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, ?_⟩)
  rw [Module.End.pow_restrict m hEW]
  ext v
  simp [LinearMap.restrict_apply, hEm]

theorem isIntegral_inv_mul_sum_character [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    {x g : G} {n : ℕ} (hn : 0 < n) (hxn : x ^ n = 1) (hxg : Commute x g) (hg : IsOfFinOrder g) :
    IsIntegral ℤ ((n : ℂ)⁻¹ * ∑ a ∈ Finset.range n, ρ.character (x ^ a * g)) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  set T : Module.End ℂ V := ρ x with hTdef
  set E : Module.End ℂ V := ρ g with hEdef
  set S : Module.End ℂ V := ∑ a ∈ Finset.range n, T ^ a with hSdef
  have hTn : T ^ n = 1 := by rw [hTdef, ← map_pow, hxn, map_one]
  have hSTeq : S * T = S := by
    have h := geom_sum_mul T n
    rw [hTn, sub_self] at h
    rw [← hSdef, mul_sub, mul_one, sub_eq_zero] at h
    exact h
  have hpow : ∀ a : ℕ, S * T ^ a = S := by
    intro a
    induction a with
    | zero => simp
    | succ k ih => rw [pow_succ, ← mul_assoc, ih, hSTeq]
  have hSS : S * S = (n : ℂ) • S := by
    calc S * S = ∑ _a ∈ Finset.range n, S := by
          rw [hSdef, Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => hpow a
      _ = (n : ℂ) • S := by
          rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℂ]
  set P : Module.End ℂ V := (n : ℂ)⁻¹ • S with hPdef
  have hPP : IsIdempotentElem P := by
    have h1 : P * P = ((n : ℂ)⁻¹ * (n : ℂ)⁻¹ * (n : ℂ)) • S := by
      rw [hPdef, smul_mul_smul_comm, hSS, smul_smul]
    have h2 : ((n : ℂ)⁻¹ * (n : ℂ)⁻¹ * (n : ℂ)) = (n : ℂ)⁻¹ := by field_simp
    exact h1.trans (by rw [h2, hPdef])
  have hET : Commute E T := by
    rw [hEdef, hTdef, Commute, SemiconjBy, ← map_mul, ← map_mul, hxg.symm.eq]
  have hES : Commute E S := by
    rw [hSdef]
    exact Commute.sum_right _ _ _ fun a _ => hET.pow_right a
  have hEP : Commute E P := by
    rw [hPdef]
    exact hES.smul_right _
  have hchar : ∀ a : ℕ, ρ.character (x ^ a * g) = LinearMap.trace ℂ V (T ^ a * E) := by
    intro a
    rw [Representation.character, map_mul, map_pow, hTdef, hEdef]
  have key : (n : ℂ)⁻¹ * ∑ a ∈ Finset.range n, ρ.character (x ^ a * g)
      = LinearMap.trace ℂ V (E * P) := by
    rw [Finset.sum_congr rfl fun a _ => hchar a, ← map_sum, ← Finset.sum_mul, ← hSdef,
      hEP.eq, hPdef, smul_mul_assoc, map_smul, smul_eq_mul]
  rw [key]
  obtain ⟨k, hk, hgk⟩ := isOfFinOrder_iff_pow_eq_one.1 hg
  have hEfin : IsOfFinOrder E :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, by rw [hEdef, ← map_pow, hgk, map_one]⟩
  exact isIntegral_trace_mul_of_commute hEfin hPP hEP

theorem isIntegral_inv_mul_sum_apply_of_mem_span_Irr {x g : G} {n : ℕ} (hn : 0 < n)
    (hxn : x ^ n = 1) (hxg : Commute x g) (hg : IsOfFinOrder g) {Ψ : G → ℂ}
    (hΨ : Ψ ∈ Submodule.span ℤ (Irr G)) :
    IsIntegral ℤ ((n : ℂ)⁻¹ * ∑ a ∈ Finset.range n, Ψ (x ^ a * g)) := by
  induction hΨ using Submodule.span_induction with
  | mem χ hχ =>
      obtain ⟨W, -, rfl⟩ := mem_Irr.1 hχ
      exact isIntegral_inv_mul_sum_character W.ρ hn hxn hxg hg
  | zero => simpa using isIntegral_zero
  | add f h _ _ ihf ihh =>
      have : (n : ℂ)⁻¹ * ∑ a ∈ Finset.range n, (f + h) (x ^ a * g)
          = ((n : ℂ)⁻¹ * ∑ a ∈ Finset.range n, f (x ^ a * g))
            + (n : ℂ)⁻¹ * ∑ a ∈ Finset.range n, h (x ^ a * g) := by
        simp only [Pi.add_apply, Finset.sum_add_distrib, mul_add]
      rw [this]
      exact ihf.add ihh
  | smul a f _ ih =>
      have : (n : ℂ)⁻¹ * ∑ b ∈ Finset.range n, (a • f) (x ^ b * g)
          = a • ((n : ℂ)⁻¹ * ∑ b ∈ Finset.range n, f (x ^ b * g)) := by
        simp only [Pi.smul_apply, zsmul_eq_mul, ← Finset.mul_sum]
        ring
      rw [this]
      exact ih.zsmul a

theorem exists_int_inv_card_mul_sum_of_mem_span_Irr {C : Type*} [Group C] [Fintype C]
    {Θ : C → ℂ} (hΘ : Θ ∈ Submodule.span ℤ (Irr C)) :
    ∃ m : ℤ, (Nat.card C : ℂ)⁻¹ * ∑ y : C, Θ y = (m : ℂ) := by
  have hcard : (Nat.card C : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  haveI : Invertible ((Nat.card C : ℂ)) := invertibleOfNonzero hcard
  induction hΘ using Submodule.span_induction with
  | mem χ hχ =>
      obtain ⟨W, -, rfl⟩ := mem_Irr.1 hχ
      refine ⟨(finrank ℂ (Representation.invariants W.ρ) : ℤ), ?_⟩
      rw [show (FDRep.character W) = Representation.character W.ρ from rfl,
        Representation.card_inv_mul_sum_char_eq_finrank]
      push_cast
      ring
  | zero => exact ⟨0, by simp⟩
  | add f h _ _ ihf ihh =>
      obtain ⟨m₁, h₁⟩ := ihf
      obtain ⟨m₂, h₂⟩ := ihh
      refine ⟨m₁ + m₂, ?_⟩
      rw [show ∑ y : C, (f + h) y = (∑ y : C, f y) + ∑ y : C, h y by
        simp [Pi.add_apply, Finset.sum_add_distrib], mul_add, h₁, h₂]
      push_cast
      ring
  | smul a f _ ih =>
      obtain ⟨m, hm⟩ := ih
      refine ⟨a * m, ?_⟩
      rw [show ∑ y : C, (a • f) y = (a : ℂ) * ∑ y : C, f y by
        simp [Pi.smul_apply, zsmul_eq_mul, Finset.mul_sum]]
      rw [show (Nat.card C : ℂ)⁻¹ * ((a : ℂ) * ∑ y : C, f y)
          = (a : ℂ) * ((Nat.card C : ℂ)⁻¹ * ∑ y : C, f y) by ring, hm]
      push_cast
      ring

theorem cfInner_principalClassFun_right {C : Type*} [Fintype C] (Θ : C → ℂ) :
    cfInner Θ (1 : C → ℂ) = (Nat.card C : ℂ)⁻¹ * ∑ y : C, Θ y := by
  rw [cfInner_def]
  simp

theorem exists_int_cfInner_one_of_mem_span_Irr {C : Type*} [Group C] [Fintype C]
    {Θ : C → ℂ} (hΘ : Θ ∈ Submodule.span ℤ (Irr C)) :
    ∃ m : ℤ, cfInner Θ (1 : C → ℂ) = (m : ℂ) := by
  rw [cfInner_principalClassFun_right]
  exact exists_int_inv_card_mul_sum_of_mem_span_Irr hΘ

theorem prime_dvd_sub_of_forall_apply_eq [Finite G] {p : ℕ} (hp : p.Prime) {x g : G}
    (hx : orderOf x = p) (hxg : Commute x g)
    {Ψ : G → ℂ} (hΨ : Ψ ∈ Submodule.span ℤ (Irr G))
    {Θ : Subgroup.zpowers x → ℂ} (hΘ : Θ ∈ Submodule.span ℤ (Irr (Subgroup.zpowers x)))
    {c e : ℤ} (hc : Ψ g = (c : ℂ)) (he : Θ 1 = (e : ℂ))
    (hmatch : ∀ a : ℕ, 1 ≤ a → a ≤ p - 1 →
      Ψ (x ^ a * g) = Θ (⟨x, Subgroup.mem_zpowers x⟩ ^ a)) :
    (p : ℤ) ∣ c - e := by
  classical
  have hp0 : 0 < p := hp.pos
  have hp' : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp0.ne'
  have hxfin : IsOfFinOrder x := isOfFinOrder_of_finite x
  have hxn : x ^ p = 1 := by rw [← hx, pow_orderOf_eq_one]
  set xC : Subgroup.zpowers x := ⟨x, Subgroup.mem_zpowers x⟩ with hxC
  haveI : Fintype (Subgroup.zpowers x) := Fintype.ofFinite _
  have hcard : (Nat.card (Subgroup.zpowers x) : ℂ) = (p : ℂ) := by
    rw [Nat.card_zpowers, hx]
  have hA : IsIntegral ℤ ((p : ℂ)⁻¹ * ∑ a ∈ Finset.range p, Ψ (x ^ a * g)) :=
    isIntegral_inv_mul_sum_apply_of_mem_span_Irr hp0 hxn hxg (isOfFinOrder_of_finite g) hΨ
  obtain ⟨m, hm⟩ := exists_int_inv_card_mul_sum_of_mem_span_Irr hΘ
  have hsum : ∑ y : Subgroup.zpowers x, Θ y = ∑ a ∈ Finset.range p, Θ (xC ^ a) := by
    rw [← hx, ← Fin.sum_univ_eq_sum_range (fun a => Θ (xC ^ a)) (orderOf x)]
    refine (Fintype.sum_equiv (finEquivZPowers hxfin) _ _ ?_).symm
    intro a
    congr 1
  have hB : (p : ℂ)⁻¹ * ∑ a ∈ Finset.range p, Θ (xC ^ a) = (m : ℂ) := by
    rw [← hsum, ← hcard]
    exact hm
  have hBint : IsIntegral ℤ ((p : ℂ)⁻¹ * ∑ a ∈ Finset.range p, Θ (xC ^ a)) := by
    rw [hB]
    exact isIntegral_intCast m
  have hdiff : ((p : ℂ)⁻¹ * ∑ a ∈ Finset.range p, Ψ (x ^ a * g))
      - ((p : ℂ)⁻¹ * ∑ a ∈ Finset.range p, Θ (xC ^ a))
      = (p : ℂ)⁻¹ * ((c : ℂ) - (e : ℂ)) := by
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 hp0) ?_]
    · simp [hc, he]
    · intro b hb hb0
      have h1 : 1 ≤ b := Nat.one_le_iff_ne_zero.2 hb0
      have h2 : b ≤ p - 1 := Nat.le_sub_one_of_lt (Finset.mem_range.1 hb)
      rw [hmatch b h1 h2, hxC, sub_self]
  have hint : IsIntegral ℤ ((p : ℂ)⁻¹ * ((c : ℂ) - (e : ℂ))) := by
    rw [← hdiff]
    exact hA.sub hBint
  have hrat : ∃ q : ℚ, (p : ℂ)⁻¹ * ((c : ℂ) - (e : ℂ)) = (q : ℂ) :=
    ⟨((c - e : ℤ) : ℚ) / (p : ℚ), by push_cast; ring⟩
  obtain ⟨n, hn⟩ := (Complex.isIntegral_int_iff_exists_int_of_exists_rat hrat).1 hint
  refine ⟨n, ?_⟩
  have h2 : (c : ℂ) - (e : ℂ) = (p : ℂ) * (n : ℂ) := by
    rw [← hn, mul_inv_cancel_left₀ hp']
  exact_mod_cast h2

end CFSG.FeitThompson
