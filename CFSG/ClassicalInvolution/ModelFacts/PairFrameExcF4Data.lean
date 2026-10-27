module

public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Data
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcConn

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem RootSpace

def thetaF4 : Fin (Tag.rank .F4) → ℤ := ![2, 3, 4, 2]

theorem mem_rootFinset_thetaF4 : thetaF4 ∈ rootFinset .F4 := by decide +kernel

theorem isRoot_thetaF4 : IsRoot .F4 thetaF4 := mem_rootFinset.1 mem_rootFinset_thetaF4

theorem iform_thetaF4_single (i : Fin (Tag.rank .F4)) :
    iform thetaF4 (Pi.single i 1) = if i.val = 0 then 2 else 0 := by
  revert i; decide +kernel

theorem iform_thetaF4_self : iform thetaF4 thetaF4 = 4 := by decide +kernel

theorem abs_iform_thetaF4_le : ∀ σ ∈ rootFinset .F4, |iform thetaF4 σ| ≤ 4 := by
  decide +kernel

theorem iform_thetaF4_eq_zero_iff : ∀ σ ∈ rootFinset .F4,
    (iform thetaF4 σ = 0 ↔ σ ⟨0, by decide⟩ = 0) := by
  decide +kernel

theorem iform_self_cases_F4 : ∀ σ ∈ rootFinset .F4, iform σ σ = 2 ∨ iform σ σ = 4 := by
  decide +kernel

theorem even_iform_single_of_long_F4 : ∀ σ ∈ rootFinset .F4, iform σ σ = 4 →
    ∀ j : Fin (Tag.rank .F4), Even (iform σ (Pi.single j 1)) := by
  decide +kernel

theorem even_iform_of_long_F4 {σ : Fin (Tag.rank .F4) → ℤ} (hσ : IsRoot .F4 σ)
    (hl : iform σ σ = 4) (v : Fin (Tag.rank .F4) → ℤ) : Even (iform σ v) := by
  rw [iform_eq_sum_single]
  refine Finset.even_sum _ fun j _ => ?_
  exact (even_iform_single_of_long_F4 σ (mem_rootFinset.2 hσ) hl j).mul_left _

theorem iform_self_isRoot_F4 {σ : Fin (Tag.rank .F4) → ℤ} (hσ : IsRoot .F4 σ) :
    iform σ σ = 2 ∨ iform σ σ = 4 :=
  iform_self_cases_F4 σ (mem_rootFinset.2 hσ)

theorem abs_iform_le_four_F4 {ρ σ : Fin (Tag.rank .F4) → ℤ} (hρ : IsRoot .F4 ρ)
    (hσ : IsRoot .F4 σ) : |iform ρ σ| ≤ 4 := by
  have h := iform_sq_le ρ σ
  rw [abs_le]
  rcases iform_self_isRoot_F4 hρ with h1 | h1 <;> rcases iform_self_isRoot_F4 hσ with h2 | h2 <;>
    rw [h1, h2] at h <;> constructor <;> nlinarith

theorem iform_single_right_sum {τ : Tag} (x : Fin τ.rank → ℤ) (j : Fin τ.rank) :
    iform x (Pi.single j 1) = ∑ i, x i * τ.symmetrizedCartan i j := by
  simp only [iform, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem exists_eq_two_smul_F4 (x : Fin (Tag.rank .F4) → ℤ)
    (hx : ∀ j, (4 : ℤ) ∣ iform x (Pi.single j 1)) :
    ∃ y : Fin (Tag.rank .F4) → ℤ, x = (2 : ℤ) • y ∧ (4 : ℤ) ∣ iform y y := by
  have h1 : ∀ z : Fin (Tag.rank .F4) → ZMod 4,
      (∀ j, ∑ i, z i * ((Tag.symmetrizedCartan .F4 i j : ℤ) : ZMod 4) = 0) →
        ∀ i, z i = 0 ∨ z i = 2 := by decide +kernel
  have h2 : ∀ z : Fin (Tag.rank .F4) → ZMod 4,
      (∀ j, ∑ i, z i * ((Tag.symmetrizedCartan .F4 i j : ℤ) : ZMod 4) = 0 ∨
        ∑ i, z i * ((Tag.symmetrizedCartan .F4 i j : ℤ) : ZMod 4) = 2) →
        ∑ i, ∑ j, z i * ((Tag.symmetrizedCartan .F4 i j : ℤ) : ZMod 4) * z j = 0 := by
    decide +kernel
  have hxev : ∀ i, (2 : ℤ) ∣ x i := by
    have h3 := h1 (fun i => (x i : ZMod 4)) (fun j => by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).2 (hx j)
      rw [iform_single_right_sum] at this
      push_cast at this
      exact this)
    intro i
    rcases h3 i with h | h
    · have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).1 h
      omega
    · have h' : ((x i - 2 : ℤ) : ZMod 4) = 0 := by push_cast; rw [h]; ring
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).1 h'
      omega
  choose y hy using hxev
  have hxy : x = (2 : ℤ) • y := funext fun i => by simp [hy i]
  refine ⟨y, hxy, ?_⟩
  have hy2 : ∀ j, (2 : ℤ) ∣ iform y (Pi.single j 1) := by
    intro j
    have := hx j
    rw [hxy, iform_smul_left] at this
    omega
  have h44 : (4 : ZMod 4) = 0 := by decide
  have hsum : ∀ j, ((iform y (Pi.single j 1) : ℤ) : ZMod 4) = 0 ∨
      ((iform y (Pi.single j 1) : ℤ) : ZMod 4) = 2 := by
    intro j
    obtain ⟨m, hm⟩ := hy2 j
    rw [hm]
    rcases Int.even_or_odd m with ⟨t, ht⟩ | ⟨t, ht⟩
    · left
      rw [ht]
      push_cast
      calc 2 * ((t : ZMod 4) + t) = 4 * (t : ZMod 4) := by ring
        _ = 0 := by rw [h44, zero_mul]
    · right
      rw [ht]
      push_cast
      calc 2 * (2 * (t : ZMod 4) + 1) = 4 * (t : ZMod 4) + 2 := by ring
        _ = 2 := by rw [h44, zero_mul, zero_add]
  have h4 := h2 (fun i => (y i : ZMod 4)) (fun j => by
    have := hsum j
    rw [iform_single_right_sum] at this
    push_cast at this
    exact this)
  have h5 : ((iform y y : ℤ) : ZMod 4) = 0 := by
    simp only [iform]
    push_cast
    exact h4
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).1 h5


end CFSG.ClassicalInvolution.ModelFacts.Levi
