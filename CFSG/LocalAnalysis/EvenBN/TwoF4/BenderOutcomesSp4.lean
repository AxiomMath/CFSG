module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.BenderOutcomesBasic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpOuter
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup Matrix
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

namespace Sp4

variable {K : Type} [Field K] [CharP K 2]

theorem add_pow_two_pow (k : ℕ) (x y : K) : (x + y) ^ 2 ^ k = x ^ 2 ^ k + y ^ 2 ^ k :=
  add_pow_char_pow x y 2 k

omit [CharP K 2] in
theorem pow_card_eq [Finite K] {q : ℕ} (hK : Nat.card K = q) (x : K) : x ^ q = x := by
  have : Fintype K := Fintype.ofFinite K
  rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]

omit [CharP K 2] in
theorem pow_e_pow_θ [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ (2 * m + 1)) (x : K) :
    (x ^ 2 ^ m) ^ 2 ^ (m + 1) = x := by
  rw [← pow_mul, ← pow_add, show m + (m + 1) = 2 * m + 1 by ring, pow_card_eq hK]

omit [CharP K 2] in
theorem pow_θ_pow_e [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ (2 * m + 1)) (x : K) :
    (x ^ 2 ^ (m + 1)) ^ 2 ^ m = x := by
  rw [← pow_mul, ← pow_add, show m + 1 + m = 2 * m + 1 by ring, pow_card_eq hK]

omit [CharP K 2] in
theorem pow_e_sq (m : ℕ) (x : K) : (x ^ 2 ^ m) ^ 2 = x ^ 2 ^ (m + 1) := by
  rw [← pow_mul, ← pow_succ]

variable (K) in
theorem two_eq_zero : (2 : K) = 0 := CharTwo.two_eq_zero

theorem add_self (x : K) : x + x = 0 := CharTwo.add_self_eq_zero x

variable [Finite K]

theorem eta_uElt (m : ℕ) (a b c d : K) :
    (minorAut K ^ (2 * m + 1)) (uElt a b c d) =
      uElt (d ^ 2 ^ m) (c ^ 2 ^ m + a ^ 2 ^ m * b ^ 2 ^ m + (a ^ 2 ^ m) ^ 2 * d ^ 2 ^ m)
        ((b ^ 2 ^ m) ^ 2 + a ^ 2 ^ m * b ^ 2 ^ m * d ^ 2 ^ m + c ^ 2 ^ m * d ^ 2 ^ m)
        ((a ^ 2 ^ m) ^ 2) :=
  antiSp_ext (glMat_eta_uElt m a b c d)

omit [Finite K] in
theorem uElt_mul_self (a b c d : K) :
    uElt a b c d * uElt a b c d = uElt 0 (a * d) (a ^ 2 * d) 0 := by
  rw [uElt_mul]
  congr 1
  · exact add_self a
  · rw [add_self, zero_add]
  · linear_combination (c + a * b) * two_eq_zero K
  · exact add_self d

variable {m : ℕ} {α : K}

omit [CharP K 2] [Finite K] in
theorem zero_pow_two_pow (k : ℕ) : (0 : K) ^ 2 ^ k = 0 := zero_pow (pow_ne_zero _ two_ne_zero)

variable (m) in
@[expose] def vElt (α : K) : antiSp K := uElt α 0 (α ^ 2 * α ^ 2 ^ (m + 1)) (α ^ 2 ^ (m + 1))

variable (m) in
@[expose] def zElt (β : K) : antiSp K := uElt 0 β (β ^ 2 ^ (m + 1)) 0

theorem eta_vElt (hK : Nat.card K = 2 ^ (2 * m + 1)) (α : K) :
    (minorAut K ^ (2 * m + 1)) (vElt m α) = vElt m α := by
  rw [vElt, eta_uElt]
  have h1 : (α ^ 2 * α ^ 2 ^ (m + 1)) ^ 2 ^ m = (α ^ 2 ^ m) ^ 2 * α := by
    rw [mul_pow, pow_θ_pow_e hK, ← pow_mul, ← pow_mul, mul_comm 2]
  congr 1
  · exact pow_θ_pow_e hK α
  · rw [h1, zero_pow_two_pow, mul_zero, add_zero, pow_θ_pow_e hK]
    exact add_self _
  · rw [h1, zero_pow_two_pow, pow_θ_pow_e hK, pow_e_sq]
    ring_nf
  · exact pow_e_sq m α

theorem eta_zElt (hK : Nat.card K = 2 ^ (2 * m + 1)) (β : K) :
    (minorAut K ^ (2 * m + 1)) (zElt m β) = zElt m β := by
  rw [zElt, eta_uElt, zero_pow_two_pow, pow_θ_pow_e hK, pow_e_sq]
  congr 1 <;> ring

omit [Finite K] in
theorem vElt_mem : vElt m α ∈ antiUnipotent K := uElt_mem_antiUnipotent _ _ _ _

omit [Finite K] in
theorem zElt_mem_center (β : K) : zElt m β ∈ antiUnipotentCenter K := ⟨_, _, rfl⟩

omit [Finite K] in
theorem inv_mul_mem_center (a b c d B C : K) :
    (uElt a b c d)⁻¹ * uElt a B C d ∈ antiUnipotentCenter K := by
  rw [uElt_inv, uElt_mul, add_self, add_self]
  exact ⟨_, _, rfl⟩

omit [Finite K] in
theorem zIn_antiUnipotent : zIn (antiUnipotent K) = antiUnipotentCenter K := by
  apply le_antisymm
  · intro z hz
    obtain ⟨hc, hzU⟩ := mem_zIn.mp hz
    obtain ⟨a, b, c, d, rfl⟩ := hzU
    have h1 := hc _ (uElt_mem_antiUnipotent 1 0 0 0)
    have h2 := hc _ (uElt_mem_antiUnipotent 0 0 0 1)
    rw [uElt_mul, uElt_mul] at h1 h2
    obtain ⟨-, h1b, -, -⟩ := uMat_inj (congrArg (fun x : antiSp K => glMat (x : GL (Fin 4) K)) h1)
    obtain ⟨-, h2b, -, -⟩ := uMat_inj (congrArg (fun x : antiSp K => glMat (x : GL (Fin 4) K)) h2)
    have hd : d = 0 := by linear_combination h1b
    have ha : a = 0 := by linear_combination -h2b
    subst hd ha
    exact ⟨b, c, rfl⟩
  · intro z hz
    exact mem_zIn.mpr ⟨fun w hw => (antiUnipotentCenter_comm hz hw).symm,
      antiUnipotentCenter_le hz⟩

variable (K m) in
@[expose] def etaFix : Subgroup (antiSp K) :=
  (minorAut K ^ (2 * m + 1)).toMonoidHom.eqLocus (MonoidHom.id _)

theorem mem_etaFix {g : antiSp K} : g ∈ etaFix K m ↔ (minorAut K ^ (2 * m + 1)) g = g :=
  Iff.rfl

variable (K m) in
@[expose] def szSylow : Subgroup (antiSp K) := antiUnipotent K ⊓ etaFix K m

theorem vElt_mem_szSylow (hK : Nat.card K = 2 ^ (2 * m + 1)) (α : K) : vElt m α ∈ szSylow K m :=
  mem_inf.mpr ⟨vElt_mem, eta_vElt hK α⟩

theorem zElt_mem_szSylow (hK : Nat.card K = 2 ^ (2 * m + 1)) (β : K) : zElt m β ∈ szSylow K m :=
  mem_inf.mpr ⟨antiUnipotentCenter_le (zElt_mem_center β), eta_zElt hK β⟩

theorem eq_of_eta_uElt {a b c d : K}
    (h : (minorAut K ^ (2 * m + 1)) (uElt a b c d) = uElt a b c d) :
    d = a ^ 2 ^ (m + 1) := by
  rw [eta_uElt] at h
  obtain ⟨-, -, -, h4⟩ := uMat_inj (congrArg (fun x : antiSp K => glMat (x : GL (Fin 4) K)) h)
  rw [← h4, pow_e_sq]

omit [Finite K] in
theorem vElt_mul_zElt (α β : K) :
    vElt m α * zElt m β =
      uElt α β (α ^ 2 * α ^ 2 ^ (m + 1) + β ^ 2 ^ (m + 1) + α * β) (α ^ 2 ^ (m + 1)) := by
  rw [vElt, zElt, uElt_mul]
  congr 1 <;> ring

theorem exists_eq_vElt_mul_zElt (hK : Nat.card K = 2 ^ (2 * m + 1)) {w : antiSp K}
    (hw : w ∈ szSylow K m) : ∃ α β : K, w = vElt m α * zElt m β := by
  obtain ⟨hwU, hwη⟩ := mem_inf.mp hw
  obtain ⟨a, b, c, d, rfl⟩ := hwU
  have hd := eq_of_eta_uElt (mem_etaFix.mp hwη)
  subst hd
  have hz : (vElt m a)⁻¹ * uElt a b c (a ^ 2 ^ (m + 1)) ∈ antiUnipotentCenter K :=
    inv_mul_mem_center _ _ _ _ _ _
  obtain ⟨β, γ, hβγ⟩ := hz
  have hzη : (minorAut K ^ (2 * m + 1)) (uElt 0 β γ 0) = uElt 0 β γ 0 := by
    rw [← hβγ, map_mul, map_inv, eta_vElt hK, mem_etaFix.mp hwη]
  have hγ : γ = β ^ 2 ^ (m + 1) := by
    rw [eta_uElt] at hzη
    obtain ⟨-, -, h3, -⟩ :=
      uMat_inj (congrArg (fun x : antiSp K => glMat (x : GL (Fin 4) K)) hzη)
    rw [← h3, zero_pow_two_pow, pow_e_sq]
    ring
  refine ⟨a, β, ?_⟩
  rw [zElt, ← hγ, ← hβγ, mul_inv_cancel_left]

theorem card_szSylow (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    Nat.card (szSylow K m) = (2 ^ (2 * m + 1)) ^ 2 := by
  let f : K × K → szSylow K m := fun p =>
    ⟨vElt m p.1 * zElt m p.2, mul_mem (vElt_mem_szSylow hK p.1) (zElt_mem_szSylow hK p.2)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p q hpq => ?_, fun w => ?_⟩
    · have h1 := congrArg (fun x : szSylow K m => glMat ((x : antiSp K) : GL (Fin 4) K)) hpq
      simp only [f, vElt_mul_zElt, glMat_uElt] at h1
      obtain ⟨h1a, h1b, -, -⟩ := uMat_inj h1
      exact Prod.ext h1a h1b
    · obtain ⟨α, β, hw⟩ := exists_eq_vElt_mul_zElt hK w.2
      exact ⟨(α, β), Subtype.ext hw.symm⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_prod, hK, sq]

omit [CharP K 2] [Finite K] in
theorem frob_pow_apply {φ : K ≃+* K} (hφ : ∀ x, φ x = x ^ 2) (k : ℕ) (x : K) :
    (φ ^ k) x = x ^ 2 ^ k := by
  induction k with
  | zero => rw [pow_zero, RingAut.one_apply, pow_zero, pow_one]
  | succ k ih => rw [pow_succ', RingAut.mul_apply, ih, hφ, ← pow_mul, ← pow_succ]

omit [CharP K 2] [Finite K] in
theorem exists_pow_θ_ne (hK : Nat.card K = 2 ^ (2 * m + 1)) (hm : 1 ≤ m) :
    ∃ s : K, s ^ 2 ^ (m + 1) ≠ s := by
  obtain ⟨Fr, hFr, hord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega) hK
  by_contra h
  push Not at h
  have h1 : Fr ^ (m + 1) = 1 := RingEquiv.ext fun s => by
    rw [frob_pow_apply hFr, h s, RingAut.one_apply]
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [hord] at h2
  have := Nat.le_of_dvd (by omega) h2
  omega

theorem zIn_szSylow_le (hK : Nat.card K = 2 ^ (2 * m + 1)) (hm : 1 ≤ m) :
    zIn (szSylow K m) ≤ antiUnipotentCenter K := by
  intro v hv
  obtain ⟨hc, hvV⟩ := mem_zIn.mp hv
  obtain ⟨α, β, rfl⟩ := exists_eq_vElt_mul_zElt hK hvV
  have key : ∀ s : K, α * s ^ 2 ^ (m + 1) = s * α ^ 2 ^ (m + 1) := by
    intro s
    have h1 := hc _ (vElt_mem_szSylow hK s)
    rw [vElt_mul_zElt, vElt, uElt_mul, uElt_mul] at h1
    obtain ⟨-, h1b, -, -⟩ := uMat_inj (congrArg (fun x : antiSp K => glMat (x : GL (Fin 4) K)) h1)
    linear_combination -h1b
  have hα : α = 0 := by
    have h1 := key 1
    rw [one_pow, mul_one, one_mul] at h1
    obtain ⟨s, hs⟩ := exists_pow_θ_ne hK hm
    have h2 := key s
    rw [← h1] at h2
    by_contra hα0
    apply hs
    have : α * (s ^ 2 ^ (m + 1) - s) = 0 := by linear_combination h2
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hα0)
  subst hα
  have h0 : vElt m (0 : K) = 1 := by
    rw [vElt, zero_pow_two_pow, zero_pow two_ne_zero, mul_zero]
    exact antiSp_ext uMat_zero
  rw [h0, one_mul]
  exact zElt_mem_center β

omit [Finite K] in
theorem commutator_le_center : ⁅antiUnipotent K, antiUnipotent K⁆ ≤ antiUnipotentCenter K := by
  rw [commutator_le]
  rintro _ ⟨a, b, c, d, rfl⟩ _ ⟨A, B, C, D, rfl⟩
  rw [commutatorElement_def, uElt_inv, uElt_inv, uElt_mul, uElt_mul, uElt_mul]
  have h0 : ∀ X Y Z W : K, X = 0 → W = 0 → uElt X Y Z W ∈ antiUnipotentCenter K := by
    rintro X Y Z W rfl rfl
    exact ⟨Y, Z, rfl⟩
  apply h0
  · linear_combination (a + A) * two_eq_zero K
  · linear_combination (d + D) * two_eq_zero K

omit [Finite K] in
theorem commutatorElement_uElt (x s : K) :
    ⁅uElt x 0 0 0, uElt 0 0 0 s⁆ = uElt 0 (x * s) (x ^ 2 * s) 0 := by
  rw [commutatorElement_def, uElt_inv, uElt_inv, uElt_mul, uElt_mul, uElt_mul]
  congr 1
  · linear_combination x * two_eq_zero K
  · linear_combination (x * s) * two_eq_zero K
  · ring
  · linear_combination s * two_eq_zero K

omit [Finite K] in
theorem center_le_of_forall_mem {C : Subgroup (antiSp K)} {x₀ : K} (hx₀ : x₀ ^ 2 ≠ x₀)
    (hC : ∀ x s : K, uElt 0 (x * s) (x ^ 2 * s) 0 ∈ C) : antiUnipotentCenter K ≤ C := by
  rintro _ ⟨β, γ, rfl⟩
  have hden : x₀ + x₀ ^ 2 ≠ 0 := by
    intro h0
    apply hx₀
    linear_combination h0 - x₀ * two_eq_zero K
  obtain ⟨s₂, hs⟩ : ∃ s₂ : K, (x₀ + x₀ ^ 2) * s₂ = β + γ :=
    ⟨(β + γ) / (x₀ + x₀ ^ 2), mul_div_cancel₀ _ hden⟩
  have h : uElt 0 β γ 0 = uElt 0 (1 * (β + x₀ * s₂)) (1 ^ 2 * (β + x₀ * s₂)) 0 *
      uElt 0 (x₀ * s₂) (x₀ ^ 2 * s₂) 0 := by
    rw [uElt_mul]
    congr 1
    · ring
    · linear_combination (-(x₀ * s₂)) * two_eq_zero K
    · linear_combination -hs - β * two_eq_zero K
    · ring
  rw [h]
  exact mul_mem (hC 1 _) (hC x₀ s₂)

omit [CharP K 2] [Finite K] in
theorem exists_sq_ne (hK : 2 < Nat.card K) : ∃ x₀ : K, x₀ ^ 2 ≠ x₀ := by
  by_contra h
  push Not at h
  let f : Bool → K := fun b => if b then 1 else 0
  have hf : Function.Surjective f := by
    intro x
    have h1 : x * (x - 1) = 0 := by linear_combination h x
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact ⟨false, by simp [f, h2]⟩
    · exact ⟨true, by simp [f, sub_eq_zero.mp h2]⟩
  have := Nat.card_le_card_of_surjective f hf
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
  omega

theorem gElt_eq (α : K) :
    (uElt α 0 0 0)⁻¹ * (minorAut K ^ (2 * m + 1)) (uElt α 0 0 0) =
      uElt α (α * α ^ 2 ^ (m + 1)) 0 (α ^ 2 ^ (m + 1)) := by
  rw [eta_uElt, uElt_inv, uElt_mul, zero_pow_two_pow, pow_e_sq]
  congr 1 <;> ring

omit [Finite K] in
theorem gElt_relation (a a' : K) :
    (uElt (a + a') ((a + a') * (a + a') ^ 2 ^ (m + 1)) 0 ((a + a') ^ 2 ^ (m + 1)))⁻¹ *
        uElt a (a * a ^ 2 ^ (m + 1)) 0 (a ^ 2 ^ (m + 1)) *
        uElt a' (a' * a' ^ 2 ^ (m + 1)) 0 (a' ^ 2 ^ (m + 1)) =
      uElt 0 (a' * a ^ 2 ^ (m + 1)) (a' ^ 2 * a ^ 2 ^ (m + 1)) 0 := by
  rw [add_pow_two_pow]
  generalize a ^ 2 ^ (m + 1) = A
  generalize a' ^ 2 ^ (m + 1) = A'
  rw [uElt_inv, uElt_mul, uElt_mul]
  congr 1
  · linear_combination (a + a') * two_eq_zero K
  · linear_combination (2 * a * A + 2 * a * A' + 2 * a' * A' + a' * A) * two_eq_zero K
  · linear_combination (2 * a ^ 2 * A + a ^ 2 * A' + 4 * a * a' * A' + 4 * a * a' * A +
      a' ^ 2 * A + 2 * a' ^ 2 * A') * two_eq_zero K
  · linear_combination (A + A') * two_eq_zero K

theorem center_le_closure (hK : Nat.card K = 2 ^ (2 * m + 1)) (h2K : 2 < Nat.card K) :
    antiUnipotentCenter K ≤ closure {x | ∃ w ∈ antiUnipotent K,
      x = w⁻¹ * (minorAut K ^ (2 * m + 1)) w} := by
  set C := closure {x | ∃ w ∈ antiUnipotent K, x = w⁻¹ * (minorAut K ^ (2 * m + 1)) w}
  have hg : ∀ α : K, uElt α (α * α ^ 2 ^ (m + 1)) 0 (α ^ 2 ^ (m + 1)) ∈ C := fun α =>
    subset_closure ⟨uElt α 0 0 0, uElt_mem_antiUnipotent _ _ _ _, (gElt_eq α).symm⟩
  obtain ⟨x₀, hx₀⟩ := exists_sq_ne h2K
  refine center_le_of_forall_mem hx₀ fun x s => ?_
  have h : uElt 0 (x * s) (x ^ 2 * s) 0 =
      (uElt (s ^ 2 ^ m + x) ((s ^ 2 ^ m + x) * (s ^ 2 ^ m + x) ^ 2 ^ (m + 1)) 0
        ((s ^ 2 ^ m + x) ^ 2 ^ (m + 1)))⁻¹ *
        uElt (s ^ 2 ^ m) (s ^ 2 ^ m * (s ^ 2 ^ m) ^ 2 ^ (m + 1)) 0 ((s ^ 2 ^ m) ^ 2 ^ (m + 1)) *
        uElt x (x * x ^ 2 ^ (m + 1)) 0 (x ^ 2 ^ (m + 1)) := by
    rw [gElt_relation, pow_e_pow_θ hK]
  rw [h]
  exact mul_mem (mul_mem (inv_mem (hg _)) (hg _)) (hg _)

omit [Finite K] in
theorem center_le_commutator (h2K : 2 < Nat.card K) :
    antiUnipotentCenter K ≤ ⁅antiUnipotent K, antiUnipotent K⁆ := by
  obtain ⟨x₀, hx₀⟩ := exists_sq_ne h2K
  refine center_le_of_forall_mem hx₀ fun x s => ?_
  rw [← commutatorElement_uElt]
  exact commutator_mem_commutator (uElt_mem_antiUnipotent _ _ _ _) (uElt_mem_antiUnipotent _ _ _ _)

variable (K) in
@[expose] def vecRep : antiSp K →* Module.End K (Fin 4 → K) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin 4) (Fin 4) K ≃ₐ[K] Module.End K (Fin 4 → K)).toRingEquiv
    |>.toMonoidHom.comp ((Units.coeHom (Matrix (Fin 4) (Fin 4) K)).comp (antiSp K).subtype)

omit [CharP K 2] [Finite K] in
theorem vecRep_apply (g : antiSp K) (v : Fin 4 → K) :
    vecRep K g v = glMat (g : GL (Fin 4) K) *ᵥ v :=
  rfl

omit [Finite K] [CharP K 2] in
theorem fixed_uMat_one {v : Fin 4 → K} (hv : uMat (1 : K) 1 1 1 *ᵥ v = v) :
    v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0 := by
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  have h2 := congrFun hv 2
  simp [uMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four] at h0 h1 h2
  have hv2 : v 2 = 0 := by linear_combination h1 - 2 * h2
  have hv1 : v 1 = 0 := by linear_combination h0 - hv2 - h2
  exact ⟨hv1, hv2, h2⟩

theorem col_zero_of_mem {S : Subgroup (antiSp K)} (hS : IsPGroup 2 S)
    (h1 : uElt (1 : K) 1 1 1 ∈ S) {s : antiSp K} (hs : s ∈ S) :
    glMat (s : GL (Fin 4) K) 0 0 = 1 ∧ glMat (s : GL (Fin 4) K) 1 0 = 0 ∧
      glMat (s : GL (Fin 4) K) 2 0 = 0 ∧ glMat (s : GL (Fin 4) K) 3 0 = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, hv0, hv⟩ := CFSG.LieType.BorelTits.exists_fixed_ne_zero (vecRep K) 2 S hS
  have hx₀ := hv _ h1
  rw [vecRep_apply, glMat_uElt] at hx₀
  obtain ⟨hv1, hv2, hv3⟩ := fixed_uMat_one hx₀
  have hv00 : v 0 ≠ 0 := by
    intro h
    apply hv0
    funext i
    fin_cases i <;> simp [h, hv1, hv2, hv3]
  have hsv := hv s hs
  rw [vecRep_apply] at hsv
  have key : ∀ i, glMat (s : GL (Fin 4) K) i 0 * v 0 = v i := by
    intro i
    have := congrFun hsv i
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_four, hv1, hv2, hv3] using this
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact mul_right_cancel₀ hv00 ((key 0).trans (one_mul _).symm)
  · exact (mul_eq_zero.mp ((key 1).trans hv1)).resolve_right hv00
  · exact (mul_eq_zero.mp ((key 2).trans hv2)).resolve_right hv00
  · exact (mul_eq_zero.mp ((key 3).trans hv3)).resolve_right hv00

theorem minorAut_uElt_one : minorAut K (uElt 1 1 1 1) = uElt 1 1 1 1 := by
  refine antiSp_ext ?_
  rw [glMat_minorAut, glMat_uElt, minorMap_uMat]
  congr 1 <;> first | ring1 | linear_combination two_eq_zero K

theorem le_antiUnipotent {S : Subgroup (antiSp K)} (hS : IsPGroup 2 S)
    (h1 : uElt (1 : K) 1 1 1 ∈ S) : S ≤ antiUnipotent K := by
  have hS' : IsPGroup 2 (S.map (minorAut K).toMonoidHom) := hS.map _
  have h1' : uElt (1 : K) 1 1 1 ∈ S.map (minorAut K).toMonoidHom := ⟨_, h1, minorAut_uElt_one⟩
  intro s hs
  obtain ⟨e00, e10, e20, e30⟩ := col_zero_of_mem hS h1 hs
  obtain ⟨f00, f10, -, -⟩ := col_zero_of_mem hS' h1' ⟨s, hs, rfl⟩
  change glMat (minorAut K s : GL (Fin 4) K) 0 0 = 1 at f00
  change glMat (minorAut K s : GL (Fin 4) K) 1 0 = 0 at f10
  rw [glMat_minorAut, minorMap_apply, minorIdx_zero] at f00 f10
  rw [minorIdx_one] at f10
  simp only at f00 f10
  have hJ := mem_antiSp.mp s.2
  have j01 := congrFun (congrFun hJ 0) 1
  have j02 := congrFun (congrFun hJ 0) 2
  have j03 := congrFun (congrFun hJ 0) 3
  have j12 := congrFun (congrFun hJ 1) 2
  rw [transpose_mul_minorJ_mul_apply, minorJ_apply] at j01 j02 j03 j12
  set M := glMat (s : GL (Fin 4) K) with hM
  rw [e00, e10, e20, e30] at j01 j02 j03
  rw [e00, e10] at f00
  rw [e00, e20] at f10
  norm_num at j01 j02 j03 f00 f10
  rw [j01, j02, f00, f10] at j12
  norm_num at j12
  rw [mem_antiUnipotent_iff_upper]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all
  · fin_cases i <;> simp_all

theorem uElt_one_mem_szSylow : uElt (1 : K) 1 1 1 ∈ szSylow K m := by
  refine mem_inf.mpr ⟨uElt_mem_antiUnipotent _ _ _ _, ?_⟩
  rw [mem_etaFix, eta_uElt]
  simp only [one_pow, mul_one]
  congr 1 <;> first | ring1 | linear_combination two_eq_zero K

theorem benderSylowAut_eta (hK : Nat.card K = 2 ^ (2 * m + 1)) (hm : 1 ≤ m) :
    BenderSylowAut (minorAut K ^ (2 * m + 1)) (szSylow K m) (antiUnipotent K) := by
  have h2K : 2 < Nat.card K := by
    rw [hK]
    calc 2 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hZ := zIn_antiUnipotent (K := K)
  have hcomm : ∀ a b c d : K, ∃ B C : K,
      (uElt a b c d)⁻¹ * (minorAut K ^ (2 * m + 1)) (uElt a b c d) =
        uElt (a + d ^ 2 ^ m) B C ((a + d ^ 2 ^ m) ^ 2 ^ (m + 1)) := by
    intro a b c d
    rw [eta_uElt, uElt_inv, uElt_mul, add_pow_two_pow, pow_e_pow_θ hK, pow_e_sq]
    exact ⟨_, _, by congr 1; ring⟩
  refine
    { isPGroup := ?_
      le := inf_le_left
      unique := fun S hS hVS => le_antiUnipotent hS (hVS uElt_one_mem_szSylow)
      mem := ?_
      fixed := ?_
      center_mul_self := ?_
      mul_self_mem := ?_
      center_comm_mem := ?_
      exists_center_comm := ?_
      comm_mem := ?_
      le_closure := ?_
      exists_comm_mod := ?_
      mem_of_comm := ?_
      mem_center := ?_ }
  · refine IsPGroup.of_card (n := (2 * m + 1) * 4) ?_
    rw [card_antiUnipotent hK, ← pow_mul]
  · rintro _ ⟨a, b, c, d, rfl⟩
    rw [eta_uElt]
    exact uElt_mem_antiUnipotent _ _ _ _
  · intro w hw
    exact ⟨fun h => mem_inf.mpr ⟨hw, h⟩, fun h => (mem_inf.mp h).2⟩
  · intro z hz
    rw [hZ] at hz
    obtain ⟨b, c, rfl⟩ := hz
    rw [uElt_mul]
    simp only [add_self, mul_zero, zero_mul]
    exact antiSp_ext uMat_zero
  · rintro _ ⟨a, b, c, d, rfl⟩
    rw [hZ, uElt_mul_self]
    exact ⟨_, _, rfl⟩
  · intro z hz
    rw [hZ] at hz
    obtain ⟨b, c, rfl⟩ := hz
    have h : (uElt 0 b c 0)⁻¹ * (minorAut K ^ (2 * m + 1)) (uElt 0 b c 0) =
        zElt m (b + c ^ 2 ^ m) := by
      rw [eta_uElt, uElt_inv, uElt_mul, zElt, add_pow_two_pow, pow_e_pow_θ hK, pow_e_sq,
        zero_pow_two_pow]
      congr 1 <;> ring
    rw [h]
    refine mem_zIn.mpr ⟨fun v hv => ?_, zElt_mem_szSylow hK _⟩
    exact (antiUnipotentCenter_comm (zElt_mem_center _) (mem_inf.mp hv).1).symm
  · intro v hv
    have hvc := zIn_szSylow_le hK hm hv
    obtain ⟨α, β, hvαβ⟩ := exists_eq_vElt_mul_zElt hK (mem_zIn.mp hv).2
    obtain ⟨b, c, hbc⟩ := hvc
    rw [hbc, vElt_mul_zElt] at hvαβ
    obtain ⟨hα, hβ, hc, -⟩ :=
      uMat_inj (congrArg (fun x : antiSp K => glMat (x : GL (Fin 4) K)) hvαβ)
    subst hα hβ
    refine ⟨uElt 0 b 0 0, hZ ▸ ⟨b, 0, rfl⟩, ?_⟩
    rw [hbc, eta_uElt, uElt_inv, uElt_mul, hc, zero_pow_two_pow, pow_e_sq]
    congr 1 <;> ring
  · rintro _ ⟨a, b, c, d, rfl⟩
    obtain ⟨B, C, hBC⟩ := hcomm a b c d
    rw [hBC]
    set s := a + d ^ 2 ^ m
    have h1 : uElt s B C (s ^ 2 ^ (m + 1)) =
        vElt m s * ((vElt m s)⁻¹ * uElt s B C (s ^ 2 ^ (m + 1))) := by
      rw [mul_inv_cancel_left]
    rw [h1]
    exact mul_mem (mem_sup_right (vElt_mem_szSylow hK s))
      (mem_sup_left (center_le_commutator h2K (inv_mul_mem_center _ _ _ _ _ _)))
  · refine sup_le ((commutator_le_center).trans (center_le_closure hK h2K)) ?_
    intro v hv
    obtain ⟨α, β, rfl⟩ := exists_eq_vElt_mul_zElt hK hv
    have h1 : vElt m α * zElt m β = uElt α (α * α ^ 2 ^ (m + 1)) 0 (α ^ 2 ^ (m + 1)) *
        ((uElt α (α * α ^ 2 ^ (m + 1)) 0 (α ^ 2 ^ (m + 1)))⁻¹ * (vElt m α * zElt m β)) := by
      rw [mul_inv_cancel_left]
    rw [h1]
    refine mul_mem (subset_closure ⟨uElt α 0 0 0, uElt_mem_antiUnipotent _ _ _ _,
      (gElt_eq α).symm⟩) (center_le_closure hK h2K ?_)
    rw [vElt_mul_zElt]
    exact inv_mul_mem_center _ _ _ _ _ _
  · intro v hv
    obtain ⟨α, β, rfl⟩ := exists_eq_vElt_mul_zElt hK hv
    refine ⟨uElt α 0 0 0, uElt_mem_antiUnipotent _ _ _ _, ?_⟩
    rw [gElt_eq, hZ, vElt_mul_zElt]
    exact inv_mul_mem_center _ _ _ _ _ _
  · rintro _ ⟨a, b, c, d, rfl⟩ hw
    obtain ⟨B, C, hBC⟩ := hcomm a b c d
    rw [hBC, hZ] at hw
    obtain ⟨b', c', hb'c'⟩ := hw
    obtain ⟨h1, -, -, h4⟩ :=
      uMat_inj (congrArg (fun x : antiSp K => glMat (x : GL (Fin 4) K)) hb'c')
    have hd : d = a ^ 2 ^ (m + 1) := by
      have : a = d ^ 2 ^ m := by linear_combination h1 - (d ^ 2 ^ m) * two_eq_zero K
      rw [this, pow_e_pow_θ hK]
    have h2 : uElt a b c d = vElt m a * ((vElt m a)⁻¹ * uElt a b c d) := by
      rw [mul_inv_cancel_left]
    rw [h2, hZ]
    refine mul_mem (mem_sup_left (vElt_mem_szSylow hK a)) (mem_sup_right ?_)
    rw [vElt, hd]
    exact inv_mul_mem_center _ _ _ _ _ _
  · intro v hv hvv
    obtain ⟨α, β, rfl⟩ := exists_eq_vElt_mul_zElt hK hv
    rw [vElt_mul_zElt, uElt_mul_self] at hvv
    have h1 : (1 : antiSp K) = uElt 0 0 0 0 := antiSp_ext uMat_zero.symm
    rw [h1] at hvv
    have hvv' := uMat_inj (congrArg (fun x : antiSp K => glMat (x : GL (Fin 4) K)) hvv)
    obtain ⟨-, h2, -, -⟩ := hvv'
    have hα : α = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact h
      · exact pow_eq_zero_iff (pow_ne_zero _ two_ne_zero) |>.mp h
    subst hα
    rw [hZ]
    have h0 : vElt m (0 : K) = 1 := by
      rw [vElt, zero_pow_two_pow, zero_pow two_ne_zero, mul_zero]
      exact antiSp_ext uMat_zero
    rw [h0, one_mul]
    exact zElt_mem_center β

theorem exists_conj_eq_of_outer (hK : Nat.card K = 2 ^ (2 * m + 1))
    {α : MulAut (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 K))}
    (hα : orderOf α = 2)
    (hαI : α ∉ inner (CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSp 2 K))) :
    ∃ h : antiSp K, α = (spInner 2 K (antiSpEquiv K h))⁻¹ * exceptionalAut K ^ (2 * m + 1) *
      spInner 2 K (antiSpEquiv K h) := by
  obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega) hK
  obtain ⟨hγord, -, -, -, -, -, -, -, -, hinvol⟩ := exceptionalAut_structure (by omega) hFr hord hzp
  obtain ⟨s, j, hj, hsj⟩ := hinvol α hα
  have hjf : j = 2 * m + 1 := hj.resolve_left fun h => hαI (by
    rw [hsj, h, pow_zero, mul_one]
    exact spInner_mem_inner s)
  subst hjf
  set ηG : Subgroup.zpowers (minorAut K ^ (2 * m + 1)) :=
    ⟨minorAut K ^ (2 * m + 1), Subgroup.mem_zpowers _⟩ with hηG
  set u := (antiSpEquiv K).symm s with hu
  set x : etaProduct K m := SemidirectProduct.inl u * SemidirectProduct.inr ηG with hx
  have hΘx : etaProductHom K m x = α := by
    rw [hx, map_mul, etaProductHom_inl, hηG, etaProductHom_inr_eta, hu,
      MulEquiv.apply_symm_apply, hsj]
  have hxr : x.right = ηG := by
    rw [hx, SemidirectProduct.mul_right, SemidirectProduct.right_inl, SemidirectProduct.right_inr,
      one_mul]
  have hγ2f : exceptionalAut K ^ (2 * (2 * m + 1)) = 1 := by rw [← hγord, pow_orderOf_eq_one]
  have hu1 : u * (minorAut K ^ (2 * m + 1)) u = 1 := by
    have hsq := pow_orderOf_eq_one α
    rw [hα] at hsq
    have hγ2 : exceptionalAut K ^ (2 * m + 1) * exceptionalAut K ^ (2 * m + 1) = 1 := by
      rw [← pow_add, ← two_mul, hγ2f]
    have key : α * α = spInner 2 K (s * (exceptionalSpAut K ^ (2 * m + 1)) s) :=
      calc α * α = spInner 2 K s * (exceptionalAut K ^ (2 * m + 1) * spInner 2 K s) *
            exceptionalAut K ^ (2 * m + 1) := by rw [hsj]; simp only [mul_assoc]
        _ = spInner 2 K s * spInner 2 K ((exceptionalSpAut K ^ (2 * m + 1)) s) *
            (exceptionalAut K ^ (2 * m + 1) * exceptionalAut K ^ (2 * m + 1)) := by
          rw [exceptionalAut_pow_mul_spInner]
          simp only [mul_assoc]
        _ = spInner 2 K (s * (exceptionalSpAut K ^ (2 * m + 1)) s) := by
          rw [hγ2, mul_one, map_mul]
    have h1 : s * (exceptionalSpAut K ^ (2 * m + 1)) s = 1 :=
      spInner_injective (by rw [← key, ← sq, hsq, map_one])
    have hs : s = antiSpEquiv K u := by rw [hu, MulEquiv.apply_symm_apply]
    rw [hs, exceptionalSpAut_pow_apply, ← map_mul] at h1
    exact (antiSpEquiv K).injective (h1.trans (map_one _).symm)
  have hxl : x.left = u := by
    simp only [hx, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.left_inr, SemidirectProduct.right_inl, map_one, mul_one]
  have hx2 : x ^ 2 = 1 := by
    refine SemidirectProduct.ext ?_ ?_
    · rw [sq, SemidirectProduct.mul_left, hxr, hxl, SemidirectProduct.one_left]
      exact hu1
    · rw [sq, SemidirectProduct.mul_right, hxr, SemidirectProduct.one_right]
      have h := pow_orderOf_eq_one (minorAut K ^ (2 * m + 1))
      rw [orderOf_eta m hK] at h
      exact Subtype.ext (by rw [Subgroup.coe_mul, ← sq, h]; rfl)
  obtain ⟨h, hh⟩ := eta_involution_conj m hK x hxr hx2
  have hconj := congrArg (etaProductHom K m) hh
  rw [map_mul, map_mul, map_inv, hΘx, etaProductHom_inl, etaProductHom_inr_eta] at hconj
  refine ⟨h, ?_⟩
  rw [← hconj]
  group

theorem le_szSylow (hK : Nat.card K = 2 ^ (2 * m + 1)) (hm : 1 ≤ m) {Q : Subgroup (antiSp K)}
    (hQ : IsPGroup 2 Q) (hQη : Q ≤ etaFix K m) (hVQ : szSylow K m ≤ Q) : Q ≤ szSylow K m :=
  le_inf ((benderSylowAut_eta hK hm).unique Q hQ hVQ) hQη

theorem exists_eq_map_conj (hK : Nat.card K = 2 ^ (2 * m + 1)) (hm : 1 ≤ m)
    {Q : Subgroup (antiSp K)} (hQ : IsPGroup 2 Q) (hQη : Q ≤ etaFix K m)
    (hQc : Nat.card Q = (2 ^ (2 * m + 1)) ^ 2) :
    ∃ s ∈ etaFix K m, Q = (szSylow K m).map (MulAut.conj s).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E := etaFix K m with hE
  have hV : IsPGroup 2 (szSylow K m) := (benderSylowAut_eta hK hm).isPGroup.to_le inf_le_left
  have hVE : szSylow K m ≤ E := inf_le_right
  let P : Sylow 2 E :=
    { toSubgroup := (szSylow K m).subgroupOf E
      isPGroup' := hV.comap_subtype
      is_maximal' := by
        intro Q' hQ' hPQ'
        refine le_antisymm (fun x hx => ?_) hPQ'
        have h1 : Q'.map E.subtype ≤ szSylow K m :=
          le_szSylow hK hm (hQ'.map E.subtype) (map_subtype_le Q') (fun y hy =>
            ⟨⟨y, hVE hy⟩, hPQ' hy, rfl⟩)
        exact h1 ⟨x, hx, rfl⟩ }
  obtain ⟨T, hQT⟩ := (hQ.comap_subtype (K := E)).exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq E P T
  refine ⟨g, g.2, ?_⟩
  have hle : Q ≤ (szSylow K m).map (MulAut.conj (g : antiSp K)).toMonoidHom := by
    intro x hx
    have hx' : (⟨x, hQη hx⟩ : E) ∈ ((g • P : Sylow 2 E) : Subgroup E) := hQT hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx'
    obtain ⟨p, hpP, hpx⟩ := hx'
    rw [MulAut.smul_def, MulAut.conj_apply] at hpx
    refine ⟨p, hpP, ?_⟩
    have := congrArg Subtype.val hpx
    simpa using this
  refine (eq_of_le_of_card_ge hle ?_)
  rw [hQc, card_map_of_injective (MulAut.conj (g : antiSp K)).injective, card_szSylow hK]

theorem symm_apply_conj_eta (h y : antiSp K) :
    ((antiSpEquiv K).trans (projSpEquiv K)).symm
      (((spInner 2 K (antiSpEquiv K h))⁻¹ * exceptionalAut K ^ (2 * m + 1) *
        spInner 2 K (antiSpEquiv K h)) (((antiSpEquiv K).trans (projSpEquiv K)) y)) =
      h⁻¹ * (minorAut K ^ (2 * m + 1)) (h * y * h⁻¹) * h := by
  set Φ := (antiSpEquiv K).trans (projSpEquiv K) with hΦ
  have hb : spInner 2 K (antiSpEquiv K h) = MulAut.conj (Φ h) := by
    rw [spInner_eq_conj]
    rfl
  have hγ : exceptionalAut K ^ (2 * m + 1) = MulAut.congr Φ (minorAut K ^ (2 * m + 1)) := by
    rw [exceptionalAut_eq_congr, map_pow]
  have hc : MulAut.congr Φ (MulAut.conj h) = MulAut.conj (Φ h) := by
    ext z
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have e1 : (spInner 2 K (antiSpEquiv K h))⁻¹ * exceptionalAut K ^ (2 * m + 1) *
      spInner 2 K (antiSpEquiv K h) =
        MulAut.congr Φ ((MulAut.conj h)⁻¹ * minorAut K ^ (2 * m + 1) * MulAut.conj h) := by
    rw [hb, hγ, map_mul, map_mul, map_inv, hc]
  rw [e1, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  change (MulAut.conj h)⁻¹ ((minorAut K ^ (2 * m + 1)) (MulAut.conj h y)) = _
  rw [MulAut.conj_apply, MulAut.conj_inv_apply]

end Sp4

open Sp4 in
theorem benderSylow_of_symplectic {H : Type} [Group H] [Finite H] {D : Subgroup H} [D.Normal]
    {a : H} (haa : a * a = 1) {n : ℕ} (hn : CFSG.Blueprint.LieModel D .PSp 2 2 n) (hodd : Odd n)
    (h3 : 3 ≤ n)
    (hout : (MulAut.conjNormal a : MulAut D) ∉ (MulAut.conj : D →* MulAut D).range)
    {V : Subgroup H} (hVD : V ≤ D ⊓ centralizer ({a} : Set H)) (hV : IsPGroup 2 V)
    (hcard : Nat.card V = 2 ^ (2 * n)) :
    ∃ W : Subgroup H, BenderSylow D a V W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, rfl⟩ := hodd
  have hm : 1 ≤ m := by omega
  obtain ⟨K, hF, hfin, hK, e₁⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = 2 ^ (2 * m + 1) ∧
        Nonempty (D ≃* CFSG.Assembly.LowTwoRank.StatedProj
          (CFSG.Assembly.LowTwoRank.StatedSp 2 K)) := by
    rcases hn with ⟨-, -, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h
    all_goals exact absurd h0 (by norm_num)
  obtain ⟨e₁⟩ := e₁
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK
  set Φ := (antiSpEquiv K).trans (projSpEquiv K) with hΦ
  set e : D ≃* antiSp K := e₁.trans Φ.symm with he
  obtain ⟨αD, hαD⟩ : ∃ f : MulAut D, f = MulAut.conjNormal a := ⟨_, rfl⟩
  rw [← hαD] at hout
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have haD : a ∉ D := by
    intro ha
    apply hout
    refine ⟨⟨a, ha⟩, ?_⟩
    ext d
    rw [hαD, MulAut.conjNormal_apply, MulAut.conj_apply]
    rfl
  set αP := MulAut.congr e₁ αD with hαP
  have hαD2 : αD * αD = 1 := by
    rw [hαD, ← map_mul, haa, map_one]
  have hαD1 : αD ≠ 1 := fun h1 => hout ⟨1, (map_one _).trans h1.symm⟩
  have hαPord : orderOf αP = 2 := by
    rw [hαP, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [sq, hαD2]) hαD1
  have hαPI : αP ∉ inner (CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSp 2 K)) := by
    rintro ⟨y, hy⟩
    apply hout
    refine ⟨e₁.symm y, ?_⟩
    apply (MulAut.congr e₁).injective
    rw [← hαP, ← hy]
    ext z
    simp [MulAut.congr_apply, MulAut.conj_apply]
  obtain ⟨h, hh⟩ := exists_conj_eq_of_outer hK hαPord hαPI
  have hβ : ∀ d : D, e (αD d) = h⁻¹ * (minorAut K ^ (2 * m + 1)) (h * e d * h⁻¹) * h := by
    intro d
    rw [← symm_apply_conj_eta, ← hh]
    have h1 : Φ (e d) = e₁ d := by
      rw [he]
      exact Φ.apply_symm_apply (e₁ d)
    rw [h1, hαP, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
    rfl
  set V₁ : Subgroup (antiSp K) := (V.subgroupOf D).map e.toMonoidHom with hV₁
  set Q : Subgroup (antiSp K) := V₁.map (MulAut.conj h).toMonoidHom with hQ
  have hVsub : Nat.card (V.subgroupOf D) = Nat.card V :=
    Nat.card_congr (subgroupOfEquivOfLe (hVD.trans inf_le_left)).toEquiv
  have hQcard : Nat.card Q = (2 ^ (2 * m + 1)) ^ 2 := by
    rw [hQ, card_map_of_injective (MulAut.conj h).injective, hV₁,
      card_map_of_injective e.injective, hVsub, hcard, ← pow_mul, mul_comm]
  have hQp : IsPGroup 2 Q :=
    ((hV.comap_subtype (K := D)).map e.toMonoidHom).map (MulAut.conj h).toMonoidHom
  have hQη : Q ≤ etaFix K m := by
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    have hva : αD v = v := by
      apply Subtype.ext
      rw [hαD, MulAut.conjNormal_apply]
      have hv' : (v : H) ∈ V := hv
      have hva' : (v : H) * a = a * v := mem_centralizer_singleton_iff.mp (hVD hv').2
      calc a * (v : H) * a⁻¹ = (v : H) * a * a⁻¹ := by rw [hva']
        _ = v := by group
    have h1 := hβ v
    rw [hva] at h1
    rw [mem_etaFix]
    change (minorAut K ^ (2 * m + 1)) (h * e v * h⁻¹) = h * e v * h⁻¹
    calc (minorAut K ^ (2 * m + 1)) (h * e v * h⁻¹) =
          h * (h⁻¹ * (minorAut K ^ (2 * m + 1)) (h * e v * h⁻¹) * h) * h⁻¹ := by group
      _ = h * e v * h⁻¹ := by rw [← h1]
  obtain ⟨s, hs, hQs⟩ := exists_eq_map_conj hK hm hQp hQη hQcard
  set c := h⁻¹ * s with hc
  set φ : antiSp K →* H := D.subtype.comp (e.symm.toMonoidHom.comp (MulAut.conj c).toMonoidHom)
    with hφdef
  have hφ : Function.Injective φ :=
    (subtype_injective D).comp (e.symm.injective.comp (MulAut.conj c).injective)
  have hφD : φ.range = D := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (e.symm _).2
    · intro hx
      refine ⟨c⁻¹ * e ⟨x, hx⟩ * c, ?_⟩
      change ((e.symm (c * (c⁻¹ * e ⟨x, hx⟩ * c) * c⁻¹) : D) : H) = x
      rw [show c * (c⁻¹ * e ⟨x, hx⟩ * c) * c⁻¹ = e ⟨x, hx⟩ by group, MulEquiv.symm_apply_apply]
  have hτ : ∀ x, a⁻¹ * φ x * a = φ ((minorAut K ^ (2 * m + 1)) x) := by
    intro x
    have hsη : (minorAut K ^ (2 * m + 1)) s = s := hs
    have h1 : c * (minorAut K ^ (2 * m + 1)) x * c⁻¹ =
        h⁻¹ * (minorAut K ^ (2 * m + 1)) (h * (c * x * c⁻¹) * h⁻¹) * h := by
      rw [hc, show h * (h⁻¹ * s * x * (h⁻¹ * s)⁻¹) * h⁻¹ = s * x * s⁻¹ by group, map_mul,
        map_mul, map_inv, hsη]
      group
    have h2 := hβ (e.symm (c * x * c⁻¹))
    rw [MulEquiv.apply_symm_apply, ← h1] at h2
    have h3 : αD (e.symm (c * x * c⁻¹)) = e.symm (c * (minorAut K ^ (2 * m + 1)) x * c⁻¹) := by
      rw [← h2, MulEquiv.symm_apply_apply]
    have h4 := congrArg Subtype.val h3
    rw [hαD, MulAut.conjNormal_apply] at h4
    simp only [hφdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, coe_subtype,
      MulAut.conj_apply] at h4 ⊢
    rw [← h4, hainv]
  have hmap := (benderSylowAut_eta hK hm).map haa haD φ hφ hφD hτ
  refine ⟨(antiUnipotent K).map φ, ?_⟩
  have hVφ : (szSylow K m).map φ = V := by
    have h1 : (szSylow K m).map (MulAut.conj c).toMonoidHom = V₁ := by
      have h2 : V₁ = Q.map (MulAut.conj h⁻¹).toMonoidHom := by
        rw [hQ, Subgroup.map_map]
        have : (MulAut.conj h⁻¹).toMonoidHom.comp (MulAut.conj h).toMonoidHom =
            MonoidHom.id (antiSp K) := MonoidHom.ext fun y => by
          change h⁻¹ * (h * y * h⁻¹) * h⁻¹⁻¹ = y
          group
        rw [this, Subgroup.map_id]
      rw [h2, hQs, Subgroup.map_map]
      congr 1
      exact MonoidHom.ext fun y => by
        change c * y * c⁻¹ = h⁻¹ * (s * y * s⁻¹) * h⁻¹⁻¹
        rw [hc]
        group
    have h3 : (szSylow K m).map φ =
        ((((szSylow K m).map (MulAut.conj c).toMonoidHom).map e.symm.toMonoidHom).map
          D.subtype) := by
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
    have h4 : (e.symm.toMonoidHom.comp e.toMonoidHom) = MonoidHom.id D := by
      ext y
      simp
    rw [h3, h1, hV₁, Subgroup.map_map (V.subgroupOf D) e.symm.toMonoidHom e.toMonoidHom]
    rw [h4, Subgroup.map_id, subgroupOf_map_subtype, inf_eq_left.mpr (hVD.trans inf_le_left)]
  rwa [hVφ] at hmap

namespace Sp4

end Sp4

end CFSG.LocalAnalysis.EvenBN.TwoF4
