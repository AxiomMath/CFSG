module

public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms
public import CFSG.FeitThompson.Definitions.PowerOperationOnClassFunctions
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Representations.NormOneVirtualCharacters
import CFSG.FeitThompson.Representations.PowerOperationsPreserveVirtualChars

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

section Arith

variable {N k b : ℕ}

theorem natCast_dvd_mul_sub_one_iff_modEq (N k b : ℕ) :
    ((N : ℤ) ∣ (k : ℤ) * b - 1) ↔ k * b ≡ 1 [MOD N] := by
  rw [Nat.modEq_iff_dvd, dvd_sub_comm]
  push_cast
  rfl

theorem coprime_right_of_mul_modEq_one (h : k * b ≡ 1 [MOD N]) : b.Coprime N :=
  Nat.Coprime.coprime_dvd_left (dvd_mul_left b k)
    (by simpa [Nat.Coprime] using Nat.ModEq.gcd_eq h)

end Arith

section Monoid

variable {G : Type*} [Monoid G] {M : Type*} {k : ℕ}

@[simp]
theorem powOp_apply_one (n : ℕ) (f : G → M) : powOp n f 1 = f 1 := by simp

theorem powOp_eq_self_of_pow_eq_self (h : ∀ y : G, y ^ k = y) (f : G → M) : powOp k f = f := by
  ext g; simp [h g]

theorem powOp_injective (h : Function.Surjective fun y : G => y ^ k) :
    Function.Injective (powOp k : (G → M) → G → M) := by
  intro f₁ f₂ hf
  funext g
  obtain ⟨y, rfl⟩ := h g
  simpa using congrFun hf y

end Monoid

section Coprime

variable {G : Type*} [Group G] {M : Type*} {k b : ℕ}

theorem pow_eq_self_of_modEq_one [Finite G] {n : ℕ} (hn : n ≡ 1 [MOD Nat.card G]) (g : G) :
    g ^ n = g := by
  simpa using pow_eq_pow_iff_modEq.2 (hn.of_dvd (orderOf_dvd_natCard g))

theorem exists_one_le_mul_modEq_one [Finite G] (hk1 : 1 ≤ k) (hk : k.Coprime (Nat.card G)) :
    ∃ b : ℕ, 1 ≤ b ∧ k * b ≡ 1 [MOD Nat.card G] := by
  have hφ : 1 ≤ (Nat.card G).totient := Nat.totient_pos.2 Nat.card_pos
  refine ⟨k ^ ((Nat.card G).totient - 1), Nat.one_le_pow _ _ hk1, ?_⟩
  have hmul : k * k ^ ((Nat.card G).totient - 1) = k ^ (Nat.card G).totient := by
    rw [← pow_succ', Nat.sub_add_cancel hφ]
  rw [hmul]
  exact Nat.ModEq.pow_totient hk

theorem powOp_powOp_eq_self [Finite G] (hkb : k * b ≡ 1 [MOD Nat.card G]) (f : G → M) :
    powOp b (powOp k f) = f := by
  rw [powOp_powOp, mul_comm b k]
  exact powOp_eq_self_of_pow_eq_self (pow_eq_self_of_modEq_one hkb) f

theorem powOp_powOp_eq_self' [Finite G] (hkb : k * b ≡ 1 [MOD Nat.card G]) (f : G → M) :
    powOp k (powOp b f) = f :=
  powOp_powOp_eq_self (mul_comm k b ▸ hkb) f

end Coprime

variable {G : Type*} [Group G] {k b : ℕ}

def classFun.powOpₗ (G : Type*) [Group G] (k : ℕ) : classFun G →ₗ[ℂ] classFun G where
  toFun f := ⟨powOp k (f : G → ℂ), powOp_mem_classFun k f.2⟩
  map_add' _ _ := by ext x; simp
  map_smul' _ _ := by ext x; simp

@[simp] theorem classFun.coe_powOpₗ_apply (k : ℕ) (f : classFun G) :
    ((classFun.powOpₗ G k f : classFun G) : G → ℂ) = powOp k (f : G → ℂ) := (rfl)

theorem cfInner_powOp_powOp [Fintype G] (hk : k.Coprime (Nat.card G)) (f h : G → ℂ) :
    cfInner (powOp k f) (powOp k h) = cfInner f h := by
  rw [cfInner_def, cfInner_def]
  congr 1
  refine Fintype.sum_bijective (fun g : G => g ^ k) (Nat.Coprime.pow_left_bijective hk.symm)
    _ _ fun g => ?_
  simp

theorem cfInner_powOpₗ_powOpₗ [Fintype G] (hk : k.Coprime (Nat.card G)) (f h : classFun G) :
    cfInner (classFun.powOpₗ G k f : G → ℂ) (classFun.powOpₗ G k h : G → ℂ) =
      cfInner (f : G → ℂ) (h : G → ℂ) := by
  rw [classFun.coe_powOpₗ_apply, classFun.coe_powOpₗ_apply, cfInner_powOp_powOp hk]

def classFun.powOpEquiv [Finite G] (hkb : k * b ≡ 1 [MOD Nat.card G]) :
    classFun G ≃ₗ[ℂ] classFun G :=
  LinearEquiv.ofLinear (classFun.powOpₗ G k) (classFun.powOpₗ G b)
    (by ext f x; simpa using congrFun (powOp_powOp_eq_self' (M := ℂ) hkb (f : G → ℂ)) x)
    (by ext f x; simpa using congrFun (powOp_powOp_eq_self (M := ℂ) hkb (f : G → ℂ)) x)

@[simp] theorem classFun.coe_powOpEquiv_apply [Finite G] (hkb : k * b ≡ 1 [MOD Nat.card G])
    (f : classFun G) :
    ((classFun.powOpEquiv hkb f : classFun G) : G → ℂ) = powOp k (f : G → ℂ) := (rfl)

theorem powOp_bijOn_span_Irr [Finite G] (hk1 : 1 ≤ k) (hk : k.Coprime (Nat.card G)) :
    Set.BijOn (powOp k) (Submodule.span ℤ (Irr G) : Set (G → ℂ))
      (Submodule.span ℤ (Irr G) : Set (G → ℂ)) := by
  obtain ⟨b, hb1, hb⟩ := exists_one_le_mul_modEq_one (G := G) hk1 hk
  exact ⟨fun _ hf => powOp_mem_span_Irr hk1 hf,
    fun _ _ _ _ h => powOp_injective (Nat.Coprime.pow_left_bijective hk.symm).surjective h,
    fun f hf => ⟨powOp b f, powOp_mem_span_Irr hb1 hf, powOp_powOp_eq_self' hb f⟩⟩

theorem powOp_mem_Irr [Finite G] (hk1 : 1 ≤ k) (hk : k.Coprime (Nat.card G)) {χ : G → ℂ}
    (hχ : χ ∈ Irr G) : powOp k χ ∈ Irr G := by
  have : Fintype G := Fintype.ofFinite G
  have hspan : powOp k χ ∈ Submodule.span ℤ (Irr G) :=
    powOp_mem_span_Irr hk1 (Submodule.subset_span hχ)
  have hnorm : cfInner (powOp k χ) (powOp k χ) = 1 := by
    rw [cfInner_powOp_powOp hk, cfInner_self_of_mem_Irr hχ]
  rcases mem_Irr_or_neg_mem_Irr_of_mem_span_Irr_of_cfInner_self_eq_one hspan hnorm with h | h
  · exact h
  ·
    obtain ⟨d, hd, hd1⟩ := NormalInducedFamily.exists_apply_one_eq_of_mem_Irr h
    obtain ⟨e, he, he1⟩ := NormalInducedFamily.exists_apply_one_eq_of_mem_Irr hχ
    rw [Pi.neg_apply, powOp_apply_one, he1] at hd1
    have hsum : ((d + e : ℕ) : ℂ) = 0 := by push_cast; linear_combination -hd1
    have : d + e = 0 := by exact_mod_cast hsum
    omega

theorem powOp_bijOn_Irr [Finite G] (hk1 : 1 ≤ k) (hk : k.Coprime (Nat.card G)) :
    Set.BijOn (powOp k) (Irr G) (Irr G) := by
  obtain ⟨b, hb1, hb⟩ := exists_one_le_mul_modEq_one (G := G) hk1 hk
  exact ⟨fun _ hχ => powOp_mem_Irr hk1 hk hχ,
    fun _ _ _ _ h => powOp_injective (Nat.Coprime.pow_left_bijective hk.symm).surjective h,
    fun χ hχ => ⟨powOp b χ, powOp_mem_Irr hb1 (coprime_right_of_mul_modEq_one hb) hχ,
      powOp_powOp_eq_self' hb χ⟩⟩

noncomputable def irrPowPerm [Finite G] (hk1 : 1 ≤ k) (hk : k.Coprime (Nat.card G)) :
    Equiv.Perm (Irr G) :=
  (powOp_bijOn_Irr hk1 hk).equiv _

@[simp] theorem coe_irrPowPerm_apply [Finite G] (hk1 : 1 ≤ k) (hk : k.Coprime (Nat.card G))
    (χ : Irr G) : ((irrPowPerm hk1 hk χ : Irr G) : G → ℂ) = powOp k (χ : G → ℂ) := (rfl)

theorem irrPowPerm_apply_one [Finite G] (hk1 : 1 ≤ k) (hk : k.Coprime (Nat.card G)) (χ : Irr G) :
    ((irrPowPerm hk1 hk χ : Irr G) : G → ℂ) 1 = (χ : G → ℂ) 1 := by
  rw [coe_irrPowPerm_apply, powOp_apply_one]

theorem irrPowPerm_irrPowPerm [Finite G] (hk1 : 1 ≤ k) (hk : k.Coprime (Nat.card G))
    (hb1 : 1 ≤ b) (hb : b.Coprime (Nat.card G)) (hkb : k * b ≡ 1 [MOD Nat.card G]) (χ : Irr G) :
    irrPowPerm hb1 hb (irrPowPerm hk1 hk χ) = χ := by
  ext x
  rw [coe_irrPowPerm_apply, coe_irrPowPerm_apply, powOp_powOp_eq_self hkb]

end CFSG.FeitThompson
