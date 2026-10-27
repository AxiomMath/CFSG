module

public import CFSG.FeitThompson.Representations.CoherentFamilyCommonSignDegreeRatio
public import CFSG.FeitThompson.Definitions.PowerOperationOnClassFunctions
import CFSG.FeitThompson.Representations.CoprimePowerPermutesIrreducibles
import CFSG.FeitThompson.Representations.IrreducibleCharacterOrthogonality
import CFSG.FeitThompson.Representations.IrreducibleDegreeDividesOrder
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.RingTheory.SimpleRing.Principal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {L G : Type*} [Group L] [Group G] {k : ℕ} {S : Set (L → ℂ)}

theorem powOp_add {M : Type*} [Add M] (n : ℕ) (f h : L → M) :
    powOp n (f + h) = powOp n f + powOp n h := by ext g; simp

theorem powOp_sub {M : Type*} [Sub M] (n : ℕ) (f h : L → M) :
    powOp n (f - h) = powOp n f - powOp n h := by ext g; simp

theorem powOp_zsmul (n : ℕ) (c : ℤ) (f : L → ℂ) :
    powOp n (c • f) = c • powOp n f := by ext g; simp

theorem powOp_smul (n : ℕ) (c : ℂ) (f : L → ℂ) :
    powOp n (c • f) = c • powOp n f := by ext g; simp

theorem powOp_mem_span_of_mapsTo (h : Set.MapsTo (powOp k) S S) {f : L → ℂ}
    (hf : f ∈ Submodule.span ℤ S) : powOp k f ∈ Submodule.span ℤ S := by
  induction hf using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (h hx)
  | zero => simp [show powOp k (0 : L → ℂ) = 0 from by ext g; simp]
  | add x y _ _ hx hy => rw [powOp_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [powOp_zsmul]; exact Submodule.smul_mem _ _ hx

theorem powOp_mem_charSpanZero (h : Set.MapsTo (powOp k) S S) {f : L → ℂ}
    (hf : f ∈ charSpanZero S) : powOp k f ∈ charSpanZero S :=
  mem_charSpanZero.2 ⟨powOp_mem_span_of_mapsTo h (mem_charSpanZero.1 hf).1, by
    simpa using (mem_charSpanZero.1 hf).2⟩

def charSpanZeroPowOp (h : Set.MapsTo (powOp k) S S) :
    charSpanZero S →ₗ[ℤ] charSpanZero S where
  toFun f := ⟨powOp k (f : L → ℂ), powOp_mem_charSpanZero h f.2⟩
  map_add' _ _ := Subtype.ext (powOp_add k _ _)
  map_smul' c _ := Subtype.ext (powOp_zsmul k c _)

@[simp] theorem coe_charSpanZeroPowOp_apply (h : Set.MapsTo (powOp k) S S) (f : charSpanZero S) :
    (charSpanZeroPowOp h f : L → ℂ) = powOp k (f : L → ℂ) := (rfl)

theorem charSpanZeroPowOp_apply_apply (h : Set.MapsTo (powOp k) S S) (f : charSpanZero S) (x : L) :
    (charSpanZeroPowOp h f : L → ℂ) x = (f : L → ℂ) (x ^ k) := by simp

variable [Fintype L] [Fintype G] {τ : charSpanZero S →+ virtualChars G}
  {ν : Submodule.span ℤ S →+ virtualChars G}

theorem coherentVal_powOp_of_mem_Irr (hk1 : 1 ≤ k) (hk : k.Coprime (Nat.card G * Nat.card L))
    (hSpow : Set.BijOn (powOp k) S S) (hI2 : 2 ≤ (S ∩ Irr L).ncard)
    (hτ1 : ∀ f : charSpanZero S, (τ f : G → ℂ) 1 = 0)
    (hτpow : ∀ f : charSpanZero S,
      (τ (charSpanZeroPowOp hSpow.mapsTo f) : G → ℂ) = powOp k (τ f : G → ℂ))
    (hν : IsCoherentWith S τ ν) {χ : L → ℂ} (hχ : χ ∈ S ∩ Irr L) :
    coherentVal ν ⟨powOp k χ, hSpow.mapsTo hχ.1⟩ = powOp k (coherentVal ν ⟨χ, hχ.1⟩) := by
  classical
  have hmaps := hSpow.mapsTo
  have hkG : k.Coprime (Nat.card G) := Nat.Coprime.coprime_dvd_right (dvd_mul_right _ _) hk
  have hkL : k.Coprime (Nat.card L) := Nat.Coprime.coprime_dvd_right (dvd_mul_left _ _) hk
  have hPinjL : Function.Injective (powOp k : (L → ℂ) → L → ℂ) :=
    powOp_injective (Nat.Coprime.pow_left_bijective hkL.symm).surjective
  have hIIrr : S ∩ Irr L ⊆ Irr L := Set.inter_subset_right
  have hIS : Submodule.span ℤ (S ∩ Irr L) ≤ Submodule.span ℤ S :=
    Submodule.span_mono Set.inter_subset_left
  have hIS0 : charSpanZero (S ∩ Irr L) ≤ charSpanZero S := fun f hf =>
    mem_charSpanZero.2 ⟨hIS (mem_charSpanZero.1 hf).1, (mem_charSpanZero.1 hf).2⟩
  set τ' : charSpanZero (S ∩ Irr L) →+ virtualChars G :=
    τ.comp (Submodule.inclusion hIS0).toAddMonoidHom with hτ'def
  set ν' : Submodule.span ℤ (S ∩ Irr L) →+ virtualChars G :=
    ν.comp (Submodule.inclusion hIS).toAddMonoidHom with hν'def
  have hν'apply : ∀ z : Submodule.span ℤ (S ∩ Irr L), ν' z = ν (Submodule.inclusion hIS z) :=
    fun _ => rfl
  have hτ'apply : ∀ z : charSpanZero (S ∩ Irr L), τ' z = τ (Submodule.inclusion hIS0 z) :=
    fun _ => rfl
  have hνI : IsCoherentWith (S ∩ Irr L) τ' ν' := by
    constructor
    · intro f g
      rw [hν'apply, hν'apply, hν.inner_eq]
      rfl
    · intro f
      have h1 : Submodule.inclusion hIS (Submodule.inclusion (charSpanZero_le (S ∩ Irr L)) f)
          = Submodule.inclusion (charSpanZero_le S) (Submodule.inclusion hIS0 f) := Subtype.ext rfl
      rw [hν'apply, hτ'apply, h1, hν.eq_on_zero]
  obtain ⟨ε, hε, c, hc, η, hηinj, hηIrr, hηval, -⟩ :=
    exists_sign_and_degree_ratio_of_isCoherentWith hIIrr hI2
      (fun f => by rw [hτ'apply]; exact hτ1 _) hνI
  have hε0 : ε ≠ 0 := by rcases hε with h | h <;> simp [h]
  have hvalN : ∀ (u : L → ℂ) (hu : u ∈ S ∩ Irr L) (hz : u ∈ Submodule.span ℤ S),
      ((ν ⟨u, hz⟩ : virtualChars G) : G → ℂ) = ε • η ⟨u, hu⟩ := by
    intro u hu hz
    have h1 : (⟨u, hz⟩ : Submodule.span ℤ S)
        = Submodule.inclusion hIS ⟨u, Submodule.subset_span hu⟩ := Subtype.ext rfl
    rw [h1, ← hν'apply, ← hηval ⟨u, hu⟩, coherentVal_apply]
  obtain ⟨y, hy, hyx⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < (S ∩ Irr L).ncard) χ
  obtain ⟨a, ha, ha1, -⟩ := Irr.exists_degree hχ.2
  obtain ⟨b, hb, hb1, -⟩ := Irr.exists_degree (hIIrr hy)
  have hPx : powOp k χ ∈ S ∩ Irr L := ⟨hmaps hχ.1, powOp_mem_Irr hk1 hkL hχ.2⟩
  have hPy : powOp k y ∈ S ∩ Irr L := ⟨hmaps hy.1, powOp_mem_Irr hk1 hkL (hIIrr hy)⟩
  set A := η ⟨powOp k χ, hPx⟩ with hAdef
  set B := η ⟨powOp k y, hPy⟩ with hBdef
  set C := η ⟨χ, hχ⟩ with hCdef
  set D := η ⟨y, hy⟩ with hDdef
  set sx : χ ∈ Submodule.span ℤ S := Submodule.subset_span hχ.1 with hsx
  set sy : y ∈ Submodule.span ℤ S := Submodule.subset_span hy.1 with hsy
  set sPx : powOp k χ ∈ Submodule.span ℤ S := Submodule.subset_span (hmaps hχ.1) with hsPx
  set sPy : powOp k y ∈ Submodule.span ℤ S := Submodule.subset_span (hmaps hy.1) with hsPy
  have hFmem : ((b : ℤ) • χ - (a : ℤ) • y) ∈ charSpanZero S := by
    refine mem_charSpanZero.2 ⟨Submodule.sub_mem _ (Submodule.smul_mem _ _ sx)
      (Submodule.smul_mem _ _ sy), ?_⟩
    rw [Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, ha1, hb1, zsmul_eq_mul, zsmul_eq_mul]
    push_cast
    ring
  have hFdec : Submodule.inclusion (charSpanZero_le S) (⟨_, hFmem⟩ : charSpanZero S)
      = (b : ℤ) • (⟨χ, sx⟩ : Submodule.span ℤ S)
        - (a : ℤ) • (⟨y, sy⟩ : Submodule.span ℤ S) := Subtype.ext rfl
  have hPFdec : Submodule.inclusion (charSpanZero_le S)
        (charSpanZeroPowOp hmaps (⟨_, hFmem⟩ : charSpanZero S))
      = (b : ℤ) • (⟨powOp k χ, sPx⟩ : Submodule.span ℤ S)
        - (a : ℤ) • (⟨powOp k y, sPy⟩ : Submodule.span ℤ S) := by
    refine Subtype.ext ?_
    ext g
    simp
  have heval : ∀ (u v : L → ℂ) (P Q : G → ℂ) (hu : u ∈ Submodule.span ℤ S)
      (hv : v ∈ Submodule.span ℤ S),
      ((ν ⟨u, hu⟩ : virtualChars G) : G → ℂ) = ε • P →
      ((ν ⟨v, hv⟩ : virtualChars G) : G → ℂ) = ε • Q →
      ((ν ((b : ℤ) • (⟨u, hu⟩ : Submodule.span ℤ S)
          - (a : ℤ) • (⟨v, hv⟩ : Submodule.span ℤ S)) : virtualChars G) : G → ℂ)
        = fun g => ε * ((b : ℂ) * P g - (a : ℂ) * Q g) := by
    intro u v P Q hu hv hP hQ
    rw [map_sub, map_zsmul, map_zsmul]
    funext g
    have h1 : ((((b : ℤ) • ν ⟨u, hu⟩ - (a : ℤ) • ν ⟨v, hv⟩ : virtualChars G)) : G → ℂ) g
        = (b : ℤ) • ((ν ⟨u, hu⟩ : virtualChars G) : G → ℂ) g
          - (a : ℤ) • ((ν ⟨v, hv⟩ : virtualChars G) : G → ℂ) g := by simp
    rw [h1, hP, hQ]
    simp only [Pi.smul_apply, smul_eq_mul, zsmul_eq_mul]
    push_cast
    ring
  have hL := heval (powOp k χ) (powOp k y) A B sPx sPy (hvalN _ hPx _) (hvalN _ hPy _)
  have hR := heval χ y C D sx sy (hvalN _ hχ _) (hvalN _ hy _)
  have hkey : (fun g => ε * ((b : ℂ) * A g - (a : ℂ) * B g))
      = powOp k (fun g => ε * ((b : ℂ) * C g - (a : ℂ) * D g)) := by
    rw [← hL, ← hR, ← hPFdec, ← hFdec, hν.eq_on_zero, hν.eq_on_zero, hτpow]
  have hcancel : (b : ℂ) • A - (a : ℂ) • B = (b : ℂ) • powOp k C - (a : ℂ) • powOp k D := by
    funext g
    have h := congrFun hkey g
    simp only [powOp_apply] at h
    have h3 := mul_left_cancel₀ hε0 h
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, powOp_apply]
    linear_combination h3
  have hAIrr : A ∈ Irr G := hηIrr _
  have hBIrr : B ∈ Irr G := hηIrr _
  have hCk : powOp k C ∈ Irr G := powOp_mem_Irr hk1 hkG (hηIrr _)
  have hDk : powOp k D ∈ Irr G := powOp_mem_Irr hk1 hkG (hηIrr _)
  have hBA : B ≠ A := by
    intro h
    have h1 := hηinj h
    exact hyx (hPinjL (congrArg (fun z : (S ∩ Irr L : Set (L → ℂ)) => (z : L → ℂ)) h1))
  have hCA : powOp k C = A := by
    by_contra hCA
    have hinner : cfInner ((b : ℂ) • A - (a : ℂ) • B) A = (b : ℂ) := by
      rw [cfInner_sub_left, cfInner_smul_left, cfInner_smul_left,
        cfInner_self_of_mem_Irr hAIrr, cfInner_eq_zero_of_mem_Irr hBIrr hAIrr hBA]
      ring
    rw [hcancel, cfInner_sub_left, cfInner_smul_left, cfInner_smul_left,
      cfInner_eq_zero_of_mem_Irr hCk hAIrr hCA] at hinner
    by_cases hDA : powOp k D = A
    · rw [hDA, cfInner_self_of_mem_Irr hAIrr] at hinner
      have hz : ((b + a : ℕ) : ℂ) = 0 := by push_cast; linear_combination -hinner
      have := Nat.cast_eq_zero.1 hz
      omega
    · rw [cfInner_eq_zero_of_mem_Irr hDk hAIrr hDA] at hinner
      have hz : (b : ℂ) = 0 := by linear_combination -hinner
      have := Nat.cast_eq_zero.1 hz
      omega
  rw [coherentVal_apply, coherentVal_apply, hvalN _ hPx _, hvalN _ hχ _, powOp_smul, ← hAdef,
    ← hCdef, hCA]

theorem apply_powOp_eq_powOp_apply (hk1 : 1 ≤ k) (hk : k.Coprime (Nat.card G * Nat.card L))
    (hSpow : Set.BijOn (powOp k) S S) (hI2 : 2 ≤ (S ∩ Irr L).ncard)
    (hτ1 : ∀ f : charSpanZero S, (τ f : G → ℂ) 1 = 0)
    (hτpow : ∀ f : charSpanZero S,
      (τ (charSpanZeroPowOp hSpow.mapsTo f) : G → ℂ) = powOp k (τ f : G → ℂ))
    (hν : IsCoherentWith S τ ν) {χ : L → ℂ} (hχ : χ ∈ S ∩ Irr L)
    (hPχ : powOp k χ ∈ Submodule.span ℤ S) (hχ' : χ ∈ Submodule.span ℤ S) :
    ((ν ⟨powOp k χ, hPχ⟩ : virtualChars G) : G → ℂ)
      = powOp k ((ν ⟨χ, hχ'⟩ : virtualChars G) : G → ℂ) := by
  have h := coherentVal_powOp_of_mem_Irr hk1 hk hSpow hI2 hτ1 hτpow hν hχ
  rw [coherentVal_apply, coherentVal_apply] at h
  convert h using 3

end CFSG.FeitThompson
