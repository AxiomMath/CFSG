module

public import CFSG.FeitThompson.OddOrder.PrimeDimAbelianImageTwoModels
import CFSG.FeitThompson.Representations.SymplecticBasesAlternatingForms

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Module Submodule
open LinearMap (BilinForm)

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {q : ℕ}

theorem mem_ker_of_mem_ker_of_invariant {A : Subgroup (V ≃ₗ[k] V)} {β : BilinForm k V}
    (hinv : ∀ a ∈ A, ∀ v w : V, β (a v) (a w) = β v w) {a : V ≃ₗ[k] V} (ha : a ∈ A)
    {v : V} (hv : v ∈ LinearMap.ker β) : a v ∈ LinearMap.ker β := by
  rw [LinearMap.mem_ker] at hv ⊢
  refine LinearMap.ext fun w => ?_
  have h := hinv a ha v (a.symm w)
  rw [LinearEquiv.apply_symm_apply] at h
  rw [h, hv]
  simp

theorem eq_zero_of_isAlt_of_invariant_of_not_actsReducibly [FiniteDimensional k V]
    {A : Subgroup (V ≃ₗ[k] V)} (hred : ¬ ActsReducibly A) (hodd : Odd (finrank k V))
    {β : BilinForm k V} (halt : β.IsAlt)
    (hinv : ∀ a ∈ A, ∀ v w : V, β (a v) (a w) = β v w) : β = 0 := by
  have hker : ∀ a ∈ A, ∀ v ∈ LinearMap.ker β, a v ∈ LinearMap.ker β := fun a ha _ hv =>
    mem_ker_of_mem_ker_of_invariant hinv ha hv
  by_cases htop : LinearMap.ker β = ⊤
  · refine LinearMap.ext fun v => ?_
    have hv : v ∈ LinearMap.ker β := htop ▸ Submodule.mem_top
    simpa using hv
  · exfalso
    have hbot : LinearMap.ker β = ⊥ := by
      by_contra hb
      exact hred (actsReducibly_of_invariant hker hb htop)
    have hsep : β.SeparatingLeft := by
      intro x hx
      have hxk : x ∈ LinearMap.ker β :=
        LinearMap.mem_ker.2 (LinearMap.ext fun y => by simpa using hx y)
      rw [hbot] at hxk
      simpa using hxk
    obtain ⟨n, hn⟩ := even_finrank_of_isAlt_of_separatingLeft β halt hsep
    obtain ⟨t, ht⟩ := hodd
    omega

namespace ScalarLineSystem

variable (S : ScalarLineSystem k V q)

def conjInvB (a : S.A) : S.A := ⟨S.b⁻¹ * a * S.b, S.conj_inv_mem a.2⟩

theorem coe_conjInvB (a : S.A) : (S.conjInvB a : V ≃ₗ[k] V) = S.b⁻¹ * a * S.b := (rfl)

theorem coe_conjInvB_iterate (n : ℕ) (a : S.A) :
    ((S.conjInvB^[n] a : S.A) : V ≃ₗ[k] V) = (S.b ^ n)⁻¹ * a * S.b ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', coe_conjInvB, ih]; group

theorem pow_index_eq_one : S.b ^ q = 1 := by
  have h := pow_orderOf_eq_one S.b
  rwa [S.orderOf_b] at h

theorem conjInvB_iterate_index_mul (n : ℕ) (a : S.A) : S.conjInvB^[q * n] a = a := by
  apply Subtype.ext
  rw [coe_conjInvB_iterate, pow_mul, S.pow_index_eq_one]
  simp

theorem lineScalar_add_one_eq (l : ZMod q) (a : S.A) :
    S.lineScalar (l + 1) a = S.lineScalar l (S.conjInvB a) := by
  have h := S.lineScalar_conj l (S.conjInvB a)
  rw [← h]
  congr 1
  refine Subtype.ext ?_
  simp only [coe_conjInvB]
  group

theorem lineScalar_add_natCast (n : ℕ) (l : ZMod q) (a : S.A) :
    S.lineScalar (l + (n : ZMod q)) a = S.lineScalar l (S.conjInvB^[n] a) := by
  induction n generalizing l with
  | zero => simp
  | succ n ih =>
    have h1 : l + ((n + 1 : ℕ) : ZMod q) = (l + 1) + (n : ZMod q) := by push_cast; ring
    rw [h1, ih (l + 1), S.lineScalar_add_one_eq, Function.iterate_succ_apply']

theorem lineScalar_pow_card_eq_one (i : ZMod q) (a : S.A) :
    S.lineScalar i a ^ Nat.card S.A = 1 := by
  have h := map_pow (S.lineScalarHom i) a (Nat.card S.A)
  rw [pow_card_eq_one', map_one] at h
  simpa using h.symm

theorem lineScalar_sq_eq_one (hq : Odd q) {i j : ZMod q}
    (h : ∀ a : S.A, S.lineScalar i a * S.lineScalar j a = 1) (a : S.A) :
    S.lineScalar i a ^ 2 = 1 := by
  have := S.neZero_index
  set m : ℕ := (j - i).val with hm
  have hjm : i + (m : ZMod q) = j := by
    rw [hm, ZMod.natCast_val, ZMod.cast_id]; ring
  have hkey : ∀ a : S.A, S.lineScalar i (S.conjInvB^[m] a) = (S.lineScalar i a)⁻¹ := by
    intro a
    rw [← S.lineScalar_add_natCast m i a, hjm]
    exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h a)
  have hiter : ∀ n : ℕ, ∀ a : S.A,
      S.lineScalar i (S.conjInvB^[n * m] a) = S.lineScalar i a ^ ((-1 : ℤ) ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro a
      have hadd : (n + 1) * m = n * m + m := by ring
      rw [hadd, Function.iterate_add_apply, ih, hkey a, pow_succ, inv_zpow, ← zpow_neg]
      congr 1
      ring
  have hq' := hiter q a
  rw [S.conjInvB_iterate_index_mul, hq.neg_one_pow, zpow_neg_one] at hq'
  rw [pow_two]
  nth_rewrite 1 [hq']
  rw [inv_mul_cancel]

theorem lineScalar_eq_one_of_odd (hq : Odd q) (hA : Odd (Nat.card S.A)) {i j : ZMod q}
    (h : ∀ a : S.A, S.lineScalar i a * S.lineScalar j a = 1) (a : S.A) :
    S.lineScalar i a = 1 := by
  obtain ⟨s, hs⟩ := hA
  have hsq := S.lineScalar_sq_eq_one hq h a
  have hcard := S.lineScalar_pow_card_eq_one i a
  rwa [hs, pow_succ, pow_mul, hsq, one_pow, one_mul] at hcard

theorem lineScalar_eq_one_of_lineScalar_eq_one {i : ZMod q}
    (h : ∀ a : S.A, S.lineScalar i a = 1) (l : ZMod q) (a : S.A) : S.lineScalar l a = 1 := by
  have := S.neZero_index
  have hli : i + ((l - i).val : ZMod q) = l := by rw [ZMod.natCast_val, ZMod.cast_id]; ring
  rw [← hli, S.lineScalar_add_natCast]
  exact h _

theorem eq_zero_of_isAlt_of_invariant (hq : Odd q) (hA : Odd (Nat.card S.A))
    {β : BilinForm k V} (hinv : ∀ a ∈ S.A, ∀ v w : V, β (a v) (a w) = β v w) : β = 0 := by
  have hlines : ∀ (i j : ZMod q), ∀ v ∈ S.L i, ∀ w ∈ S.L j, β v w = 0 := by
    intro i j v hv w hw
    by_contra hne
    have hchar : ∀ a : S.A, S.lineScalar i a * S.lineScalar j a = 1 := by
      intro a
      have h := hinv a a.2 v w
      rw [S.apply_eq_lineScalar_smul i a hv, S.apply_eq_lineScalar_smul j a hw] at h
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
      refine Units.ext ?_
      push_cast
      refine mul_right_cancel₀ hne ?_
      rw [one_mul]
      linear_combination h
    have h1 : ∀ (l : ZMod q) (a : S.A), S.lineScalar l a = 1 :=
      S.lineScalar_eq_one_of_lineScalar_eq_one (S.lineScalar_eq_one_of_odd hq hA hchar)
    refine S.A_ne_bot (S.A.eq_bot_iff_forall.2 fun a ha => ?_)
    simpa using S.eq_one_of_forall_lineScalar_eq (a := ⟨a, ha⟩) (c := 1) fun l => h1 l _
  have hspan : span k (⋃ i, (S.L i : Set V)) = ⊤ := by
    rw [← Submodule.iSup_eq_span, S.iSup_L]
  refine LinearMap.ext_on hspan fun v hv => ?_
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hv
  refine LinearMap.ext_on hspan fun w hw => ?_
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hw
  simpa using hlines i j v hi w hj

end ScalarLineSystem

variable {p : ℕ} [Fact p.Prime] [Fact q.Prime] {W : Type*} [AddCommGroup W] [Module (ZMod p) W]

namespace PrimeDimLinearSetup

variable (D : PrimeDimLinearSetup p q W)

include D

theorem bilinForm_eq_zero_of_isAlt_of_invariant (hq : Odd q) (hA : Odd (Nat.card D.A))
    {β : BilinForm (ZMod p) W} (halt : ∀ v, β v v = 0)
    (hinv : ∀ a ∈ D.A, ∀ v w : W, β (a v) (a w) = β v w) : β = 0 := by
  have hfd := D.finiteDimensional
  rcases em (ActsReducibly D.A) with hred | hirr
  · obtain ⟨S, hSA, _⟩ := D.exists_scalarLineSystem hred
    refine S.eq_zero_of_isAlt_of_invariant hq (by rw [hSA]; exact hA) ?_
    rw [hSA]
    exact hinv
  · exact eq_zero_of_isAlt_of_invariant_of_not_actsReducibly hirr
      (by rw [D.finrank_eq]; exact hq) halt hinv

end PrimeDimLinearSetup

theorem invariants_zpowers_eq_eqLocus (b : W ≃ₗ[ZMod p] W) :
    Representation.invariants (linearGroupRep (Subgroup.zpowers b))
      = LinearMap.eqLocus (b : W →ₗ[ZMod p] W) LinearMap.id := by
  ext v
  rw [mem_invariants_zpowers_iff, LinearMap.mem_eqLocus]
  simp

theorem bilinForm_eq_zero_of_odd_of_isAlt_of_invariant (hqp : q ≠ p) (hq : Odd q)
    (hW : finrank (ZMod p) W = q) {D : Subgroup (W ≃ₗ[ZMod p] W)} (hDne : D ≠ ⊥)
    (hDab : IsMulCommutative D) (hDodd : Odd (Nat.card D)) {b : W ≃ₗ[ZMod p] W}
    (hb : orderOf b = q) (hbn : b ∈ Subgroup.normalizer (D : Set (W ≃ₗ[ZMod p] W)))
    (hirr : ∀ U : Submodule (ZMod p) W,
      (∀ g ∈ D ⊔ Subgroup.zpowers b, ∀ v ∈ U, g v ∈ U) → U = ⊥ ∨ U = ⊤)
    (hCD : ∀ d ∈ D, d * b = b * d → d = 1)
    (hfix : finrank (ZMod p) ↥(LinearMap.eqLocus (b : W →ₗ[ZMod p] W) LinearMap.id) = 1)
    {β : BilinForm (ZMod p) W} (halt : ∀ v, β v v = 0)
    (hinv : ∀ d ∈ D, ∀ v w : W, β (d v) (d w) = β v w) : β = 0 := by
  have hq0 : 0 < q := (Fact.out : q.Prime).pos
  have hfd : FiniteDimensional (ZMod p) W := FiniteDimensional.of_finrank_pos (by omega)
  have hnt : Nontrivial W := Module.nontrivial_of_finrank_pos (R := ZMod p) (by omega)
  let S : PrimeDimLinearSetup p q W :=
    { ne_char := hqp, finrank_eq := hW, A := D, b := b, A_ne_bot := hDne,
      isMulCommutative_A := hDab, orderOf_b := hb, b_mem_normalizer := hbn,
      isIrreducible_sup := isIrreducible_linearGroupRep_iff.2 ⟨hnt, hirr⟩
      inf_centralizer_b := by
        refine le_antisymm (fun d hd => ?_) bot_le
        have h2 := Subgroup.mem_centralizer_singleton_iff.1 hd.2
        simpa using hCD d hd.1 h2
      finrank_invariants := by rw [invariants_zpowers_eq_eqLocus]; exact hfix }
  exact S.bilinForm_eq_zero_of_isAlt_of_invariant hq hDodd halt hinv

end

end CFSG.FeitThompson
