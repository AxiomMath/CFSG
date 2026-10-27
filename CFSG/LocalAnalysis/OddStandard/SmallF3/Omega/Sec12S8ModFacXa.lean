module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import Certificates.Data.A5

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open scoped CharTwo

variable {G : Type} [Group G]

private instance s8FacX_isEvenVecDecidable {n : ℕ} (v : Fin n → ZMod 2) :
    Decidable (IsEvenVec v) :=
  inferInstanceAs (Decidable (∑ i, v i = 0))

theorem s8FacX_isEvenVec_permVec :
    ∀ (σ : Equiv.Perm (Fin 5)) (v : Fin 5 → ZMod 2), IsEvenVec v → IsEvenVec (permVec σ v) := by
  unfold IsEvenVec permVec
  decide +kernel

private theorem s8FacX_isEvenVec_add {n : ℕ} {v w : Fin n → ZMod 2} (hv : IsEvenVec v)
    (hw : IsEvenVec w) : IsEvenVec (v + w) := by
  have hv' : ∑ i, v i = 0 := hv
  have hw' : ∑ i, w i = 0 := hw
  show ∑ i, (v + w) i = 0
  simp only [Pi.add_apply, Finset.sum_add_distrib, hv', hw', add_zero]

theorem s8FacX_permVec_mul (σ τ : Equiv.Perm (Fin 5)) (v : Fin 5 → ZMod 2) :
    permVec (σ * τ) v = permVec σ (permVec τ v) := rfl

theorem s8FacX_permVec_one (v : Fin 5 → ZMod 2) :
    permVec (1 : Equiv.Perm (Fin 5)) v = v := rfl

theorem s8FacX_permVec_injective {σ σ' : Equiv.Perm (Fin 5)}
    (h : ∀ v : Fin 5 → ZMod 2, IsEvenVec v → permVec σ v = permVec σ' v) : σ = σ' := by
  let ev : Fin 5 → Fin 5 → Fin 5 → ZMod 2 := fun a b x => if x = a ∨ x = b then 1 else 0
  have hev : ∀ a b : Fin 5, a ≠ b → IsEvenVec (ev a b) := by
    unfold IsEvenVec
    decide
  have key : ∀ a b : Fin 5, a ≠ b → ∀ x : Fin 5,
      (σ'.symm (σ x) = a ∨ σ'.symm (σ x) = b) ↔ (x = a ∨ x = b) := by
    intro a b hab x
    have h1 := congrFun (h _ (hev a b hab)) (σ x)
    simp only [permVec, Function.comp_apply, Equiv.symm_apply_apply, ev] at h1
    by_cases hx : x = a ∨ x = b
    · simp only [hx, if_true] at h1
      by_cases hy : σ'.symm (σ x) = a ∨ σ'.symm (σ x) = b
      · simp [hx, hy]
      · simp [hy] at h1
    · simp only [hx, if_false] at h1
      by_cases hy : σ'.symm (σ x) = a ∨ σ'.symm (σ x) = b
      · simp [hy] at h1
      · simp [hx, hy]
  refine Equiv.ext fun i => ?_
  have hne : ∀ i : Fin 5, i ≠ i + 1 ∧ i ≠ i + 2 ∧ i + 1 ≠ i + 2 := by decide
  obtain ⟨h1, h2, h3⟩ := hne i
  have e1 := (key i (i + 1) h1 i).2 (Or.inl rfl)
  have e2 := (key i (i + 2) h2 i).2 (Or.inl rfl)
  have : σ'.symm (σ i) = i := by
    rcases e1 with e1 | e1
    · exact e1
    · rcases e2 with e2 | e2
      · exact e2
      · exact absurd (e1.symm.trans e2) h3
  have := congrArg σ' this
  simpa using this

theorem s8FacX_five :
    ∀ (σ : Equiv.Perm (Fin 5)), σ ^ 5 = 1 → σ ≠ 1 →
      ∀ v : Fin 5 → ZMod 2, IsEvenVec v → permVec σ v = v → v = 0 := by
  decide +kernel

private theorem s8FacX_three_card :
    ∀ (σ : Equiv.Perm (Fin 5)), σ ^ 3 = 1 → σ ≠ 1 →
      Fintype.card {v : Fin 5 → ZMod 2 // IsEvenVec v ∧ permVec σ v = v} = 4 := by
  decide +kernel

theorem s8FacX_three (σ : Equiv.Perm (Fin 5)) (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1) :
    Nat.card {v : Fin 5 → ZMod 2 // IsEvenVec v ∧ permVec σ v = v} = 4 := by
  rw [Nat.card_eq_fintype_card]
  exact s8FacX_three_card σ h3 h1

def s8FacX_v0 : Fin 5 → ZMod 2 := fun i => if i = 0 ∨ i = 1 then 1 else 0

theorem s8FacX_isEvenVec_v0 : IsEvenVec s8FacX_v0 := by
  unfold s8FacX_v0 IsEvenVec
  decide

theorem s8FacX_exists_alt_moves :
    ∃ σ : Equiv.Perm (Fin 5), σ ∈ alternatingGroup (Fin 5) ∧ permVec σ s8FacX_v0 ≠ s8FacX_v0 := by
  decide +kernel

private theorem s8FacX_isEvenVec_zero : IsEvenVec (0 : Fin 5 → ZMod 2) := by
  simp [IsEvenVec]

theorem s8FacX_phi_zero {φ : (Fin 5 → ZMod 2) → G}
    (hφhom : ∀ v w, IsEvenVec v → IsEvenVec w → φ (v + w) = φ v * φ w) : φ 0 = 1 := by
  have h : φ 0 = φ 0 * φ 0 := by simpa using hφhom 0 0 s8FacX_isEvenVec_zero s8FacX_isEvenVec_zero
  exact mul_eq_left.mp h.symm

theorem s8FacX_phi_injective {φ : (Fin 5 → ZMod 2) → G}
    (hφhom : ∀ v w, IsEvenVec v → IsEvenVec w → φ (v + w) = φ v * φ w)
    (hφker : ∀ v, IsEvenVec v → φ v = 1 → v = 0) (hφ0 : φ 0 = 1)
    {v w : Fin 5 → ZMod 2} (hv : IsEvenVec v) (hw : IsEvenVec w) (h : φ v = φ w) : v = w := by
  have hsum : v + w = 0 := by
    apply hφker (v + w) (s8FacX_isEvenVec_add hv hw)
    calc φ (v + w) = φ v * φ w := hφhom v w hv hw
      _ = φ v * φ v := by rw [h]
      _ = φ (v + v) := (hφhom v v hv hv).symm
      _ = φ (0 : Fin 5 → ZMod 2) := by rw [CharTwo.add_self_eq_zero v]
      _ = 1 := hφ0
  have hvv : v + v = 0 := CharTwo.add_self_eq_zero v
  exact (add_left_cancel (by rw [hsum, hvv])).symm

theorem s8FacX_conj_pow_phi {φ : (Fin 5 → ZMod 2) → G} {σ : Equiv.Perm (Fin 5)} {x : G}
    (hact : ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec σ v)) :
    ∀ (k : ℕ) (v : Fin 5 → ZMod 2), IsEvenVec v →
      x ^ k * φ v * (x ^ k)⁻¹ = φ (permVec (σ ^ k) v) := by
  intro k
  induction k with
  | zero => intro v _; simp [s8FacX_permVec_one]
  | succ k ih =>
      intro v hv
      have hv' : IsEvenVec (permVec (σ ^ k) v) := s8FacX_isEvenVec_permVec (σ ^ k) v hv
      calc x ^ (k + 1) * φ v * (x ^ (k + 1))⁻¹
          = x * (x ^ k * φ v * (x ^ k)⁻¹) * x⁻¹ := by group
        _ = x * φ (permVec (σ ^ k) v) * x⁻¹ := by rw [ih v hv]
        _ = φ (permVec σ (permVec (σ ^ k) v)) := hact _ hv'
        _ = φ (permVec (σ ^ (k + 1)) v) := by rw [pow_succ', s8FacX_permVec_mul]

theorem s8FacX_prod_decomp_unique {V1 V2 : Subgroup G} (hinf : V1 ⊓ V2 = ⊥)
    {a1 a2 : G} (ha1 : a1 ∈ V1) (ha2 : a2 ∈ V1) {b1 b2 : G} (hb1 : b1 ∈ V2) (hb2 : b2 ∈ V2)
    (h : a1 * b1 = a2 * b2) : a1 = a2 ∧ b1 = b2 := by
  have h1 : a2⁻¹ * a1 ∈ V1 := V1.mul_mem (V1.inv_mem ha2) ha1
  have h2 : b2 * b1⁻¹ ∈ V2 := V2.mul_mem hb2 (V2.inv_mem hb1)
  have heq : a2⁻¹ * a1 = b2 * b1⁻¹ := by
    calc a2⁻¹ * a1 = a2⁻¹ * (a1 * b1) * b1⁻¹ := by group
      _ = a2⁻¹ * (a2 * b2) * b1⁻¹ := by rw [h]
      _ = b2 * b1⁻¹ := by group
  have hmem : a2⁻¹ * a1 ∈ V1 ⊓ V2 := Subgroup.mem_inf.mpr ⟨h1, heq ▸ h2⟩
  rw [hinf] at hmem
  have ha : a2⁻¹ * a1 = 1 := Subgroup.mem_bot.mp hmem
  have hb : b2 * b1⁻¹ = 1 := by rw [← heq]; exact ha
  exact ⟨(inv_mul_eq_one.mp ha).symm, (mul_inv_eq_one.mp hb).symm⟩

end CFSG.OddStandard.SmallF3.Omega
