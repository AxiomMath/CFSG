module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.QuasithinUnique.Setup.Family

open Module

section Char2

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

theorem e_add_self (x : E) : x + x = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [← two_smul (ZMod 2) x, h2, zero_smul]

theorem e_neg (x : E) : -x = x := neg_eq_of_add_eq_zero_right (e_add_self x)

theorem e_sub (x y : E) : x - y = x + y := by rw [sub_eq_add_neg, e_neg]

theorem e_eq_of_add_eq_zero {x y : E} (h : x + y = 0) : x = y := by
  have : x = -y := eq_neg_of_add_eq_zero_left h
  rw [this, e_neg]

theorem end_add_self (a : Module.End (ZMod 2) E) : a + a = 0 := by
  ext x
  simp only [LinearMap.add_apply, LinearMap.zero_apply]
  exact e_add_self _

theorem end_odd_nsmul (a : Module.End (ZMod 2) E) {n : ℕ} (hn : Odd n) : n • a = a := by
  obtain ⟨k, rfl⟩ := hn
  rw [add_nsmul, mul_nsmul, two_nsmul, end_add_self, nsmul_zero, zero_add, one_nsmul]

@[expose] def sub1 (s : E ≃ₗ[ZMod 2] E) : E →ₗ[ZMod 2] E :=
  (s : E →ₗ[ZMod 2] E) - LinearMap.id

theorem sub1_apply (s : E ≃ₗ[ZMod 2] E) (x : E) : sub1 s x = s x - x := rfl

theorem sub1_apply' (s : E ≃ₗ[ZMod 2] E) (x : E) : sub1 s x = s x + x := by
  rw [sub1_apply, e_sub]

theorem mul_self_apply {s : E ≃ₗ[ZMod 2] E} (hs : s * s = 1) (x : E) : s (s x) = x := by
  have := congrArg (fun f : E ≃ₗ[ZMod 2] E => f x) hs
  simpa using this

theorem sub1_sub1 {s : E ≃ₗ[ZMod 2] E} (hs : s * s = 1) (x : E) : sub1 s (sub1 s x) = 0 := by
  rw [sub1_apply', sub1_apply', map_add, mul_self_apply hs]
  calc x + s x + (s x + x) = (x + x) + (s x + s x) := by abel
    _ = 0 := by rw [e_add_self, e_add_self, add_zero]

theorem pow_apply_mem {v : E ≃ₗ[ZMod 2] E} (M : Submodule (ZMod 2) E)
    (hvM : ∀ x ∈ M, v x ∈ M) (n : ℕ) : ∀ x ∈ M, (v ^ n) x ∈ M := by
  induction n with
  | zero => intro x hx; simpa using hx
  | succ n ih =>
    intro x hx
    rw [pow_succ', LinearEquiv.mul_apply]
    exact hvM _ (ih x hx)


theorem end_even_nsmul (a : Module.End (ZMod 2) E) {n : ℕ} (hn : Even n) : n • a = 0 := by
  obtain ⟨k, rfl⟩ := hn
  rw [← two_mul, mul_nsmul, two_nsmul, end_add_self, nsmul_zero]

theorem end_eq_of_add_eq_zero {a b : Module.End (ZMod 2) E} (h : a + b = 0) : a = b := by
  have : a = -b := eq_neg_of_add_eq_zero_left h
  rw [this]
  exact neg_eq_of_add_eq_zero_right (end_add_self b)

theorem e_odd_nsmul (x : E) {n : ℕ} (hn : Odd n) : n • x = x := by
  obtain ⟨k, rfl⟩ := hn
  rw [add_nsmul, mul_nsmul, two_nsmul, e_add_self, nsmul_zero, zero_add, one_nsmul]

end Char2

section Half

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

theorem finrank_half [Module.Finite (ZMod 2) E] {s v : E ≃ₗ[ZMod 2] E}
    (M : Submodule (ZMod 2) E) (hs : s * s = 1) (hsv : s * v * s = v⁻¹) {m : ℕ} (hm : Odd m)
    (hvm : v ^ m = 1) (hsM : ∀ x ∈ M, s x ∈ M) (hvM : ∀ x ∈ M, v x ∈ M)
    (hfpf : ∀ x ∈ M, v x = x → x = 0) :
    finrank (ZMod 2) M = 2 * finrank (ZMod 2) (M.map (sub1 s)) := by
  obtain ⟨k, rfl⟩ := hm
  set w : E ≃ₗ[ZMod 2] E := v ^ (k + 1) with hw
  have hww : w * w = v := by
    rw [hw, ← pow_add]
    have : k + 1 + (k + 1) = (2 * k + 1) + 1 := by ring
    rw [this, pow_succ, hvm, one_mul]
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have hsw : s * w * s = w⁻¹ := by
    have h1 : s * w * s⁻¹ = (s * v * s⁻¹) ^ (k + 1) := by
      rw [hw]; exact (conj_pow).symm
    rw [hsinv, hsv, inv_pow] at h1
    exact h1
  have hsw' : ∀ x, s (w x) = w⁻¹ (s x) := by
    intro x
    have := congrArg (fun f : E ≃ₗ[ZMod 2] E => f (s x)) hsw
    simp only [LinearEquiv.mul_apply] at this
    rw [mul_self_apply hs] at this
    exact this
  have hwM : ∀ x ∈ M, w x ∈ M := pow_apply_mem M hvM (k + 1)
  have hwfpf : ∀ x ∈ M, w x = x → x = 0 := fun x hx hwx =>
    hfpf x hx (by rw [← hww, LinearEquiv.mul_apply, hwx, hwx])
  have hTM : ∀ x ∈ M, sub1 w x ∈ M := fun x hx => by
    rw [sub1_apply]; exact M.sub_mem (hwM x hx) hx
  have hinj : Function.Injective ((sub1 w).restrict hTM) := by
    intro a b hab
    have h0 : sub1 w ((a : E) - b) = 0 := by
      have := congrArg Subtype.val hab
      simp only [LinearMap.coe_restrict_apply] at this
      rw [map_sub, this, sub_self]
    have h1 : w ((a : E) - b) = (a : E) - b := by
      rw [sub1_apply, sub_eq_zero] at h0; exact h0
    have h2 : (a : E) - b = 0 := hwfpf _ (M.sub_mem a.2 b.2) h1
    exact Subtype.ext (sub_eq_zero.1 h2)
  have hsurj : Function.Surjective ((sub1 w).restrict hTM) :=
    LinearMap.injective_iff_surjective.1 hinj
  have key : ∀ m ∈ M, s m = m → ∃ x ∈ M, sub1 s x = m := by
    intro m hmM hsm
    obtain ⟨x, hx⟩ := hsurj ⟨m, hmM⟩
    have h1 : w x + x = m := by
      have := congrArg Subtype.val hx
      simp only [LinearMap.coe_restrict_apply, sub1_apply'] at this
      exact this
    have h2 : w⁻¹ (s x) + s x = m := by
      have := congrArg s h1
      rw [map_add, hsw', hsm] at this
      exact this
    have h3 : s x + w (s x) = w m := by
      have := congrArg w h2
      have hww' : ∀ y, w (w⁻¹ y) = y := fun y => by
        rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl
      rw [map_add, hww'] at this
      exact this
    have hu : w ((s x : E) + x + m) = (s x : E) + x + m := by
      have h4 : w ((s x : E) + x + m) + ((s x : E) + x + m) = 0 := by
        rw [map_add, map_add]
        calc w (s x) + w x + w m + (s x + x + m)
            = (s x + w (s x)) + (w x + x) + (w m + m) := by abel
          _ = w m + m + (w m + m) := by rw [h3, h1]
          _ = 0 := by rw [e_add_self]
      exact e_eq_of_add_eq_zero h4
    have hu0 : (s x : E) + x + m = 0 :=
      hwfpf _ (M.add_mem (M.add_mem (hsM x x.2) x.2) hmM) hu
    refine ⟨x, x.2, ?_⟩
    rw [sub1_apply']
    exact e_eq_of_add_eq_zero (show ((s x : E) + x) + m = 0 from hu0)
  have heq : M ⊓ LinearMap.ker (sub1 s) = M.map (sub1 s) := by
    apply le_antisymm
    · rintro m ⟨hmM, hmk⟩
      have hsm : s m = m := by
        have hmk' : sub1 s m = 0 := LinearMap.mem_ker.1 hmk
        rw [sub1_apply'] at hmk'
        exact e_eq_of_add_eq_zero hmk'
      obtain ⟨x, hxM, hx⟩ := key m hmM hsm
      exact ⟨x, hxM, hx⟩
    · rintro _ ⟨x, hxM, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [sub1_apply]; exact M.sub_mem (hsM x hxM) hxM
      · exact LinearMap.mem_ker.2 (sub1_sub1 hs x)
  have hrk := LinearMap.finrank_range_add_finrank_ker ((sub1 s).domRestrict M)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at hrk
  have hker : finrank (ZMod 2) (Submodule.comap M.subtype (LinearMap.ker (sub1 s))) =
      finrank (ZMod 2) (M.map (sub1 s)) := by
    rw [← Submodule.finrank_map_subtype_eq M, Submodule.map_comap_subtype, heq]
  rw [hker] at hrk
  omega

end Half


section Blocks

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

theorem finrank_biSup_eq_sum {ι : Type*} [DecidableEq ι] [Module.Finite (ZMod 2) E]
    (S : Finset ι) (π : ι → Module.End (ZMod 2) E) (hπ : ∀ i ∈ S, π i * π i = π i)
    (horth : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → π i * π j = 0)
    (Y : ι → Submodule (ZMod 2) E) (hY : ∀ i ∈ S, Y i ≤ LinearMap.range (π i)) :
    finrank (ZMod 2) (⨆ i ∈ S, Y i : Submodule (ZMod 2) E) = ∑ i ∈ S, finrank (ZMod 2) (Y i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have hS : ∀ i ∈ S, i ∈ insert a S := fun i hi => Finset.mem_insert_of_mem hi
    have ih' := ih (fun i hi => hπ i (hS i hi))
      (fun i hi j hj hij => horth i (hS i hi) j (hS j hj) hij) (fun i hi => hY i (hS i hi))
    rw [Finset.iSup_insert, Finset.sum_insert ha, ← ih']
    have hdisj : Y a ⊓ (⨆ i ∈ S, Y i) = ⊥ := by
      rw [eq_bot_iff]
      intro x ⟨hxa, hxS⟩
      have hπa : π a * π a = π a := hπ a (Finset.mem_insert_self a S)
      have hfix : π a x = x := by
        obtain ⟨y, rfl⟩ := hY a (Finset.mem_insert_self a S) hxa
        rw [← Module.End.mul_apply, hπa]
      have hker : (⨆ i ∈ S, Y i) ≤ LinearMap.ker (π a) := by
        refine iSup₂_le fun i hi => ?_
        intro z hz
        obtain ⟨y, rfl⟩ := hY i (hS i hi) hz
        rw [LinearMap.mem_ker, ← Module.End.mul_apply,
          horth a (Finset.mem_insert_self a S) i (hS i hi) (fun h => ha (h ▸ hi))]
        rfl
      have h0 : π a x = 0 := LinearMap.mem_ker.1 (hker hxS)
      rw [hfix] at h0
      exact (Submodule.mem_bot _).2 h0
    have := Submodule.finrank_sup_add_finrank_inf_eq (Y a) (⨆ i ∈ S, Y i)
    rw [hdisj, finrank_bot] at this
    omega

theorem sum_le_finrank_range_sub1 [Module.Finite (ZMod 2) E] (s : E ≃ₗ[ZMod 2] E) {ι : Type*}
    [DecidableEq ι] (S : Finset ι) (π : ι → Module.End (ZMod 2) E)
    (hπ : ∀ i ∈ S, π i * π i = π i) (horth : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → π i * π j = 0)
    (hcomm : ∀ i ∈ S, (s : E →ₗ[ZMod 2] E) * π i = π i * (s : E →ₗ[ZMod 2] E)) (c : ι → ℕ)
    (hc : ∀ i ∈ S, c i ≤ finrank (ZMod 2) ((LinearMap.range (π i)).map (sub1 s))) :
    ∑ i ∈ S, c i ≤ finrank (ZMod 2) (LinearMap.range (sub1 s)) := by
  set Y : ι → Submodule (ZMod 2) E := fun i => (LinearMap.range (π i)).map (sub1 s) with hYdef
  have hY : ∀ i ∈ S, Y i ≤ LinearMap.range (π i) := by
    intro i hi
    rintro _ ⟨x, ⟨y, rfl⟩, rfl⟩
    refine ⟨s y - y, ?_⟩
    have := congrArg (fun f : Module.End (ZMod 2) E => f y) (hcomm i hi)
    simp only [Module.End.mul_apply, LinearEquiv.coe_coe] at this
    rw [sub1_apply, map_sub, ← this]
  have h1 := finrank_biSup_eq_sum S π hπ horth Y hY
  have h2 : (⨆ i ∈ S, Y i : Submodule (ZMod 2) E) ≤ LinearMap.range (sub1 s) := by
    refine iSup₂_le fun i hi => ?_
    rintro _ ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  calc ∑ i ∈ S, c i ≤ ∑ i ∈ S, finrank (ZMod 2) (Y i) := Finset.sum_le_sum hc
    _ = finrank (ZMod 2) (⨆ i ∈ S, Y i : Submodule (ZMod 2) E) := h1.symm
    _ ≤ finrank (ZMod 2) (LinearMap.range (sub1 s)) := Submodule.finrank_mono h2

end Blocks

section Lines

variable {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

structure IsVAct (ρ : K × K → (E ≃ₗ[ZMod 2] E)) : Prop where
  map_zero : ρ 0 = 1
  map_add : ∀ x y, ρ (x + y) = ρ x * ρ y

@[expose] def opE (ρ : K × K → (E ≃ₗ[ZMod 2] E)) (x : K × K) : Module.End (ZMod 2) E :=
  (ρ x : E →ₗ[ZMod 2] E)

section Basic

variable {ρ : K × K → (E ≃ₗ[ZMod 2] E)} (h : IsVAct ρ)
include h

theorem opE_mul (x y : K × K) : opE ρ x * opE ρ y = opE ρ (x + y) := by
  unfold opE; rw [h.map_add]; rfl

theorem opE_zero : opE ρ 0 = 1 := by
  unfold opE; rw [h.map_zero]; rfl

theorem opE_comm (x y : K × K) : opE ρ x * opE ρ y = opE ρ y * opE ρ x := by
  rw [opE_mul h, opE_mul h, add_comm]

theorem map_neg_eq_inv (x : K × K) : ρ (-x) = (ρ x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← h.map_add, neg_add_cancel, h.map_zero]

theorem map_nsmul_eq_pow (n : ℕ) (x : K × K) : ρ (n • x) = ρ x ^ n := by
  induction n with
  | zero => simp [h.map_zero]
  | succ n ih => rw [succ_nsmul, h.map_add, ih, pow_succ]

end Basic

section Sums

variable [Fintype K]
variable {ρ : K × K → (E ≃ₗ[ZMod 2] E)} (h : IsVAct ρ)

@[expose] def lineSum (ρ : K × K → (E ≃ₗ[ZMod 2] E)) (u : K × K) : Module.End (ZMod 2) E :=
  ∑ k : K, opE ρ (k • u)

@[expose] def fullSum (ρ : K × K → (E ≃ₗ[ZMod 2] E)) : Module.End (ZMod 2) E :=
  ∑ x : K × K, opE ρ x

@[expose] def lineProj (ρ : K × K → (E ≃ₗ[ZMod 2] E)) (u : K × K) : Module.End (ZMod 2) E :=
  lineSum ρ u + fullSum ρ

include h

theorem opE_mul_lineSum (a : K) (u : K × K) : opE ρ (a • u) * lineSum ρ u = lineSum ρ u := by
  unfold lineSum
  rw [Finset.mul_sum]
  simp_rw [opE_mul h, ← add_smul]
  exact Equiv.sum_comp (Equiv.addLeft a) (fun k => opE ρ (k • u))

theorem opE_mul_fullSum (x : K × K) : opE ρ x * fullSum ρ = fullSum ρ := by
  unfold fullSum
  rw [Finset.mul_sum]
  simp_rw [opE_mul h]
  exact Equiv.sum_comp (Equiv.addLeft x) (fun y => opE ρ y)

theorem fullSum_mul_opE (x : K × K) : fullSum ρ * opE ρ x = fullSum ρ := by
  unfold fullSum
  rw [Finset.sum_mul]
  simp_rw [opE_mul h]
  exact Equiv.sum_comp (Equiv.addRight x) (fun y => opE ρ y)

variable (hodd : Odd (Fintype.card K))
include hodd

theorem lineSum_mul_self (u : K × K) : lineSum ρ u * lineSum ρ u = lineSum ρ u := by
  calc lineSum ρ u * lineSum ρ u = ∑ k : K, opE ρ (k • u) * lineSum ρ u :=
        Finset.sum_mul _ _ _
    _ = ∑ _k : K, lineSum ρ u := Finset.sum_congr rfl fun k _ => opE_mul_lineSum h k u
    _ = lineSum ρ u := by
      rw [Finset.sum_const, Finset.card_univ]
      exact end_odd_nsmul _ hodd

theorem fullSum_mul_self : fullSum ρ * fullSum ρ = fullSum ρ := by
  calc fullSum ρ * fullSum ρ = ∑ x : K × K, opE ρ x * fullSum ρ := Finset.sum_mul _ _ _
    _ = ∑ _x : K × K, fullSum ρ := Finset.sum_congr rfl fun x _ => opE_mul_fullSum h x
    _ = fullSum ρ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod]
      exact end_odd_nsmul _ (hodd.mul hodd)

theorem lineSum_mul_fullSum (u : K × K) : lineSum ρ u * fullSum ρ = fullSum ρ := by
  calc lineSum ρ u * fullSum ρ = ∑ k : K, opE ρ (k • u) * fullSum ρ := Finset.sum_mul _ _ _
    _ = ∑ _k : K, fullSum ρ := Finset.sum_congr rfl fun k _ => opE_mul_fullSum h _
    _ = fullSum ρ := by
      rw [Finset.sum_const, Finset.card_univ]
      exact end_odd_nsmul _ hodd

theorem fullSum_mul_lineSum (u : K × K) : fullSum ρ * lineSum ρ u = fullSum ρ := by
  calc fullSum ρ * lineSum ρ u = ∑ k : K, fullSum ρ * opE ρ (k • u) := Finset.mul_sum _ _ _
    _ = ∑ _k : K, fullSum ρ := Finset.sum_congr rfl fun k _ => fullSum_mul_opE h _
    _ = fullSum ρ := by
      rw [Finset.sum_const, Finset.card_univ]
      exact end_odd_nsmul _ hodd

end Sums


section Indep

variable [Fintype K]
variable {ρ : K × K → (E ≃ₗ[ZMod 2] E)} (h : IsVAct ρ) (hodd : Odd (Fintype.card K))

@[expose] def det2 (u v : K × K) : K := u.1 * v.2 - u.2 * v.1

omit [Fintype K] in
theorem lineMap_injective {u v : K × K} (hd : det2 u v ≠ 0) :
    Function.Injective (fun kl : K × K => kl.1 • u + kl.2 • v) := by
  rintro ⟨k, l⟩ ⟨k', l'⟩ hkl
  have e1 := congrArg Prod.fst hkl
  have e2 := congrArg Prod.snd hkl
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at e1 e2
  have h1 : (k - k') * det2 u v = 0 := by unfold det2; linear_combination v.2 * e1 - v.1 * e2
  have h2 : (l - l') * det2 u v = 0 := by unfold det2; linear_combination u.1 * e2 - u.2 * e1
  have hk : k = k' := sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_right hd)
  have hl : l = l' := sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hd)
  rw [hk, hl]

include h

theorem lineSum_mul_lineSum {u v : K × K} (hd : det2 u v ≠ 0) :
    lineSum ρ u * lineSum ρ v = fullSum ρ := by
  have hbij := Finite.injective_iff_bijective.1 (lineMap_injective hd)
  calc lineSum ρ u * lineSum ρ v
      = (∑ k : K, opE ρ (k • u)) * (∑ l : K, opE ρ (l • v)) := rfl
    _ = ∑ k : K, ∑ l : K, opE ρ (k • u + l • v) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => opE_mul h _ _
    _ = ∑ kl : K × K, opE ρ (kl.1 • u + kl.2 • v) :=
        (Fintype.sum_prod_type' (fun k l => opE ρ (k • u + l • v))).symm
    _ = fullSum ρ := Equiv.sum_comp (Equiv.ofBijective _ hbij) (fun x => opE ρ x)

include hodd

theorem lineProj_mul_self (u : K × K) : lineProj ρ u * lineProj ρ u = lineProj ρ u := by
  unfold lineProj
  rw [add_mul, mul_add, mul_add, lineSum_mul_self h hodd, lineSum_mul_fullSum h hodd,
    fullSum_mul_lineSum h hodd, fullSum_mul_self h hodd]
  simp only [end_add_self, add_zero]

theorem lineProj_mul_of_indep {u v : K × K} (hd : det2 u v ≠ 0) :
    lineProj ρ u * lineProj ρ v = 0 := by
  unfold lineProj
  rw [add_mul, mul_add, mul_add, lineSum_mul_lineSum h hd, lineSum_mul_fullSum h hodd,
    fullSum_mul_lineSum h hodd, fullSum_mul_self h hodd]
  simp only [end_add_self, add_zero]

theorem fullSum_mul_lineProj (u : K × K) : fullSum ρ * lineProj ρ u = 0 := by
  unfold lineProj
  rw [mul_add, fullSum_mul_lineSum h hodd, fullSum_mul_self h hodd, end_add_self]

omit hodd in
theorem opE_mul_lineProj (k : K) (u : K × K) : opE ρ (k • u) * lineProj ρ u = lineProj ρ u := by
  unfold lineProj
  rw [mul_add, opE_mul_lineSum h, opE_mul_fullSum h]

omit hodd in
theorem opE_mul_lineProj_comm (x u : K × K) :
    opE ρ x * lineProj ρ u = lineProj ρ u * opE ρ x := by
  unfold lineProj lineSum fullSum
  rw [mul_add, add_mul, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  simp_rw [opE_comm h x]

end Indep


section Complete

@[expose] def lineRep : Option K → K × K
  | none => (0, 1)
  | some m => (1, m)

theorem lineRep_ne_zero (o : Option K) : lineRep o ≠ 0 := by
  cases o <;> simp [lineRep, Prod.ext_iff]

theorem det2_lineRep {o o' : Option K} (hne : o ≠ o') : det2 (lineRep o) (lineRep o') ≠ 0 := by
  cases o with
  | none =>
    cases o' with
    | none => exact absurd rfl hne
    | some m => simp [det2, lineRep]
  | some m =>
    cases o' with
    | none => simp [det2, lineRep]
    | some m' =>
      have : m ≠ m' := fun h => hne (by rw [h])
      simp [det2, lineRep, sub_eq_zero, eq_comm, this]

variable [Fintype K] {ρ : K × K → (E ≃ₗ[ZMod 2] E)} (h : IsVAct ρ)
  (hodd : Odd (Fintype.card K))

include h

theorem sum_lineSum_rep :
    ∑ o : Option K, lineSum ρ (lineRep o) =
      fullSum ρ + (Fintype.card K) • (1 : Module.End (ZMod 2) E) := by
  classical
  have h1 : lineSum ρ (0, 1) = ∑ y : K, opE ρ (0, y) := by
    unfold lineSum
    refine Finset.sum_congr rfl fun k _ => ?_
    simp
  have h2 : ∑ m : K, lineSum ρ (1, m) = (Fintype.card K) • (1 : Module.End (ZMod 2) E) +
      ∑ a ∈ ({0}ᶜ : Finset K), ∑ y : K, opE ρ (a, y) := by
    unfold lineSum
    simp only [Prod.smul_mk, smul_eq_mul, mul_one]
    rw [Finset.sum_comm, Fintype.sum_eq_add_sum_compl (0 : K)]
    congr 1
    · simp only [zero_mul, Finset.sum_const, Finset.card_univ,
        show opE ρ ((0 : K), (0 : K)) = 1 from opE_zero h]
    · refine Finset.sum_congr rfl fun a ha => ?_
      have ha0 : a ≠ 0 := by simpa using ha
      exact Equiv.sum_comp (Equiv.mulLeft₀ a ha0) (fun y => opE ρ (a, y))
  have h3 : fullSum ρ = ∑ y : K, opE ρ (0, y) +
      ∑ a ∈ ({0}ᶜ : Finset K), ∑ y : K, opE ρ (a, y) := by
    unfold fullSum
    rw [Fintype.sum_prod_type, Fintype.sum_eq_add_sum_compl (0 : K)]
  rw [Fintype.sum_option]
  show lineSum ρ (0, 1) + ∑ m : K, lineSum ρ (1, m) = _
  rw [h1, h2, h3]
  abel

include hodd

theorem sum_lineProj_rep : ∑ o : Option K, lineProj ρ (lineRep o) = fullSum ρ + 1 := by
  unfold lineProj
  rw [Finset.sum_add_distrib, sum_lineSum_rep h, Finset.sum_const, Finset.card_univ,
    Fintype.card_option, end_odd_nsmul _ hodd,
    end_even_nsmul _ (by obtain ⟨k, hk⟩ := hodd; exact ⟨k + 1, by omega⟩), add_zero]

theorem exists_lineProj_ne (hfaith : ∀ x, ρ x = 1 → x = 0) :
    ∃ o : Option K, lineProj ρ (lineRep o) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hsum := sum_lineProj_rep h hodd
  rw [Finset.sum_eq_zero fun o _ => hcon o] at hsum
  have h1 : fullSum ρ = 1 := (end_eq_of_add_eq_zero hsum.symm)
  have h2 : opE ρ (1, 0) = 1 := by
    calc opE ρ (1, 0) = opE ρ (1, 0) * fullSum ρ := by rw [h1, mul_one]
      _ = fullSum ρ := opE_mul_fullSum h _
      _ = 1 := h1
  have h3 : ρ (1, 0) = 1 := by
    ext x
    have := LinearMap.congr_fun h2 x
    simpa [opE] using this
  have := hfaith _ h3
  exact one_ne_zero (congrArg Prod.fst this)

end Complete

end Lines

section Rank

variable {K : Type*} [Field K] [Fintype K] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  {ρ : K × K → (E ≃ₗ[ZMod 2] E)} (h : IsVAct ρ) (hodd : Odd (Fintype.card K))

include h hodd

theorem exists_two_lines (hfaith : ∀ x, ρ x = 1 → x = 0) :
    ∃ o o' : Option K, o ≠ o' ∧ lineProj ρ (lineRep o) ≠ 0 ∧ lineProj ρ (lineRep o') ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨o₁, ho₁⟩ := exists_lineProj_ne h hodd hfaith
  have hsum := sum_lineProj_rep h hodd
  rw [Finset.sum_eq_single o₁ (fun o _ hne => hcon o₁ o (Ne.symm hne) ho₁)
    (fun h' => absurd (Finset.mem_univ o₁) h')] at hsum
  have e1 : opE ρ (lineRep o₁) * lineProj ρ (lineRep o₁) = lineProj ρ (lineRep o₁) := by
    simpa using opE_mul_lineProj h (1 : K) (lineRep o₁)
  rw [hsum, mul_add, opE_mul_fullSum h, mul_one] at e1
  have e2 : opE ρ (lineRep o₁) = 1 := add_left_cancel e1
  have e3 : ρ (lineRep o₁) = 1 := by
    ext x
    have := LinearMap.congr_fun e2 x
    simpa [opE] using this
  exact lineRep_ne_zero o₁ (hfaith _ e3)

omit h hodd in
theorem lineProj_conj {g : E ≃ₗ[ZMod 2] E} {γ : K × K → K × K} (hγ : Function.Bijective γ)
    (hγk : ∀ (k : K) (x : K × K), γ (k • x) = k • γ x)
    (hg : ∀ x, g * ρ x * g⁻¹ = ρ (γ x)) (u : K × K) :
    (g : E →ₗ[ZMod 2] E) * lineProj ρ u * ((g⁻¹ : E ≃ₗ[ZMod 2] E) : E →ₗ[ZMod 2] E) =
      lineProj ρ (γ u) := by
  have hop : ∀ x, (g : E →ₗ[ZMod 2] E) * opE ρ x * ((g⁻¹ : E ≃ₗ[ZMod 2] E) : E →ₗ[ZMod 2] E) =
      opE ρ (γ x) := fun x => congrArg (fun f : E ≃ₗ[ZMod 2] E => (f : E →ₗ[ZMod 2] E)) (hg x)
  unfold lineProj lineSum fullSum
  rw [mul_add, add_mul, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  congr 1
  · simp_rw [hop, hγk]
  · simp_rw [hop]
    exact Equiv.sum_comp (Equiv.ofBijective γ hγ) (fun x => opE ρ x)

theorem fpf_of_mem_range {u w : K × K} (hd : det2 u w ≠ 0) (hK : ∀ k : K, ∃ n : ℕ, (n : K) = k)
    {x : E} (hx : x ∈ LinearMap.range (lineProj ρ u)) (hw : ρ w x = x) : x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  set x := lineProj ρ u y with hxdef
  have hfull : fullSum ρ x = 0 := by
    have := LinearMap.congr_fun (fullSum_mul_lineProj h hodd u) y
    simpa [Module.End.mul_apply] using this
  have hu : ∀ k : K, opE ρ (k • u) x = x := by
    intro k
    have := LinearMap.congr_fun (opE_mul_lineProj h k u) y
    simpa [Module.End.mul_apply] using this
  have hw' : ∀ k : K, opE ρ (k • w) x = x := by
    intro k
    obtain ⟨n, rfl⟩ := hK k
    have hpow : ∀ n : ℕ, (ρ w ^ n) x = x := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ', LinearEquiv.mul_apply, ih, hw]
    rw [Nat.cast_smul_eq_nsmul, opE, map_nsmul_eq_pow h]
    exact hpow n
  have hlu : lineSum ρ u x = x := by
    unfold lineSum
    rw [LinearMap.sum_apply]
    simp_rw [hu]
    rw [Finset.sum_const, Finset.card_univ]
    exact e_odd_nsmul _ hodd
  have hlw : lineSum ρ w x = x := by
    unfold lineSum
    rw [LinearMap.sum_apply]
    simp_rw [hw']
    rw [Finset.sum_const, Finset.card_univ]
    exact e_odd_nsmul _ hodd
  have hfx : fullSum ρ x = x := by
    rw [← lineSum_mul_lineSum h hd, Module.End.mul_apply, hlw, hlu]
  rw [← hfx, hfull]

end Rank

section RankMain

variable {K : Type*} [Field K] [Fintype K] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  {ρ : K × K → (E ≃ₗ[ZMod 2] E)} (h : IsVAct ρ) (hodd : Odd (Fintype.card K))

omit [Fintype K] in
theorem exists_det_ne (u : K × K) (hu : u ≠ 0) : ∃ w : K × K, det2 u w ≠ 0 := by
  by_cases h1 : u.1 = 0
  · refine ⟨(1, 0), ?_⟩
    have h2 : u.2 ≠ 0 := fun h2 => hu (Prod.ext h1 h2)
    simp [det2, h1, h2]
  · exact ⟨(0, 1), by simp [det2, h1]⟩

theorem conj_ne_zero {g : E ≃ₗ[ZMod 2] E} {P : Module.End (ZMod 2) E} (hP : P ≠ 0) :
    (g : E →ₗ[ZMod 2] E) * P * ((g⁻¹ : E ≃ₗ[ZMod 2] E) : E →ₗ[ZMod 2] E) ≠ 0 := by
  intro h0
  apply hP
  ext x
  have := LinearMap.congr_fun h0 (g x)
  simp only [Module.End.mul_apply, LinearEquiv.coe_coe, LinearMap.zero_apply] at this
  have h1 : g⁻¹ (g x) = x := by
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
  rw [h1] at this
  simpa using this

include h hodd

theorem card_le_finrank_range_sub1 [Module.Finite (ZMod 2) E]
    (hK : ∀ k : K, ∃ n : ℕ, (n : K) = k) {s : E ≃ₗ[ZMod 2] E} (hs : s * s = 1)
    (hsρ : ∀ x, s * ρ x * s = ρ (-x)) (U : Finset (K × K)) (hU0 : ∀ u ∈ U, u ≠ 0)
    (hUind : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → det2 u v ≠ 0)
    (hUne : ∀ u ∈ U, lineProj ρ u ≠ 0) :
    U.card ≤ finrank (ZMod 2) (LinearMap.range (sub1 s)) := by
  classical
  have hs' : (s : Module.End (ZMod 2) E) * (s : Module.End (ZMod 2) E) = 1 :=
    congrArg (fun f : E ≃ₗ[ZMod 2] E => (f : E →ₗ[ZMod 2] E)) hs
  have hsop : ∀ x, (s : Module.End (ZMod 2) E) * opE ρ x =
      opE ρ (-x) * (s : Module.End (ZMod 2) E) := by
    intro x
    have e : (s : Module.End (ZMod 2) E) * opE ρ x * (s : Module.End (ZMod 2) E) = opE ρ (-x) :=
      congrArg (fun f : E ≃ₗ[ZMod 2] E => (f : E →ₗ[ZMod 2] E)) (hsρ x)
    calc (s : Module.End (ZMod 2) E) * opE ρ x
        = (s : Module.End (ZMod 2) E) * opE ρ x * ((s : Module.End (ZMod 2) E) *
            (s : Module.End (ZMod 2) E)) := by rw [hs', mul_one]
      _ = ((s : Module.End (ZMod 2) E) * opE ρ x * (s : Module.End (ZMod 2) E)) *
            (s : Module.End (ZMod 2) E) := by simp only [mul_assoc]
      _ = opE ρ (-x) * (s : Module.End (ZMod 2) E) := by rw [e]
  have hcomm : ∀ u : K × K, (s : Module.End (ZMod 2) E) * lineProj ρ u =
      lineProj ρ u * (s : Module.End (ZMod 2) E) := by
    intro u
    unfold lineProj lineSum fullSum
    rw [mul_add, add_mul, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    congr 1
    · simp_rw [hsop]
      calc ∑ k : K, opE ρ (-(k • u)) * (s : Module.End (ZMod 2) E)
          = ∑ k : K, (fun k : K => opE ρ (k • u) * (s : Module.End (ZMod 2) E)) (-k) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            simp only [neg_smul]
        _ = ∑ k : K, opE ρ (k • u) * (s : Module.End (ZMod 2) E) :=
            Equiv.sum_comp (Equiv.neg K)
              (fun k : K => opE ρ (k • u) * (s : Module.End (ZMod 2) E))
    · simp_rw [hsop]
      exact Equiv.sum_comp (Equiv.neg (K × K))
        (fun x : K × K => opE ρ x * (s : Module.End (ZMod 2) E))
  have hc : ∀ u ∈ U, 1 ≤
      finrank (ZMod 2) ((LinearMap.range (lineProj ρ u)).map (sub1 s)) := by
    intro u hu
    obtain ⟨w, hw⟩ := exists_det_ne u (hU0 u hu)
    set M := LinearMap.range (lineProj ρ u) with hM
    have hMne : M ≠ ⊥ := fun h0 => hUne u hu (LinearMap.range_eq_bot.1 h0)
    have hMpos : 1 ≤ finrank (ZMod 2) M := Submodule.one_le_finrank_iff.2 hMne
    have hm : Odd (Fintype.card (K × K)) := by
      rw [Fintype.card_prod]; exact hodd.mul hodd
    have hvm : (ρ w) ^ (Fintype.card (K × K)) = 1 := by
      rw [← map_nsmul_eq_pow h, card_nsmul_eq_zero, h.map_zero]
    have hsv : s * ρ w * s = (ρ w)⁻¹ := by rw [hsρ, map_neg_eq_inv h]
    have hsM : ∀ x ∈ M, s x ∈ M := by
      rintro _ ⟨y, rfl⟩
      refine ⟨s y, ?_⟩
      have := LinearMap.congr_fun (hcomm u) y
      simpa [Module.End.mul_apply] using this.symm
    have hvM : ∀ x ∈ M, (ρ w) x ∈ M := by
      rintro _ ⟨y, rfl⟩
      refine ⟨ρ w y, ?_⟩
      have := LinearMap.congr_fun (opE_mul_lineProj_comm h w u) y
      simpa [Module.End.mul_apply, opE] using this.symm
    have hfpf : ∀ x ∈ M, (ρ w) x = x → x = 0 := fun x hx hwx =>
      fpf_of_mem_range h hodd hw hK hx hwx
    have := finrank_half M hs hsv hm hvm hsM hvM hfpf
    omega
  have := sum_le_finrank_range_sub1 s U (fun u => lineProj ρ u)
    (fun u _ => lineProj_mul_self h hodd u)
    (fun u hu v hv huv => lineProj_mul_of_indep h hodd (hUind u hu v hv huv))
    (fun u _ => by simpa using hcomm u) (fun _ => 1) hc
  simpa using this

theorem lineProj_ne_zero_of_trans (hfaith : ∀ x, ρ x = 1 → x = 0)
    (htrans : ∀ u : K × K, u ≠ 0 → ∃ (γ : K × K → K × K) (g : E ≃ₗ[ZMod 2] E),
      Function.Bijective γ ∧ (∀ (k : K) (x : K × K), γ (k • x) = k • γ x) ∧ γ (1, 0) = u ∧
        ∀ x, g * ρ x * g⁻¹ = ρ (γ x)) :
    ∀ u : K × K, u ≠ 0 → lineProj ρ u ≠ 0 := by
  obtain ⟨o, ho⟩ := exists_lineProj_ne h hodd hfaith
  obtain ⟨γ₀, g₀, hb₀, hk₀, hγ₀, hg₀⟩ := htrans (lineRep o) (lineRep_ne_zero o)
  have h10 : lineProj ρ (1, 0) ≠ 0 := by
    intro h0
    apply ho
    rw [← hγ₀, ← lineProj_conj hb₀ hk₀ hg₀, h0]
    simp
  intro u hu
  obtain ⟨γ, g, hb, hk, hγ, hg⟩ := htrans u hu
  rw [← hγ, ← lineProj_conj hb hk hg]
  exact conj_ne_zero h10

end RankMain
end CFSG.QuasithinUnique.Setup.Family
