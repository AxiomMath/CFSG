module

public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Data
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem RootSpace

def thetaE6 : Fin (Tag.rank .E6) → ℤ := ![1, 2, 2, 3, 2, 1]

theorem mem_rootFinset_thetaE6 : thetaE6 ∈ rootFinset .E6 := by decide +kernel

theorem isRoot_thetaE6 : IsRoot .E6 thetaE6 := mem_rootFinset.1 mem_rootFinset_thetaE6

theorem iform_thetaE6_single (i : Fin (Tag.rank .E6)) :
    iform thetaE6 (Pi.single i 1) = if i.val = 1 then 1 else 0 := by
  revert i; decide +kernel

theorem abs_iform_thetaE6_le : ∀ σ ∈ rootFinset .E6, |iform thetaE6 σ| ≤ 2 := by
  decide +kernel

theorem iform_thetaE6_eq_zero_iff : ∀ σ ∈ rootFinset .E6,
    (iform thetaE6 σ = 0 ↔ σ ⟨1, by decide⟩ = 0) := by
  decide +kernel

theorem iform_self_isRoot_E6 {σ : Fin (Tag.rank .E6) → ℤ} (hσ : IsRoot .E6 σ) : iform σ σ = 2 := by
  have h : ∀ σ ∈ rootFinset .E6, iform σ σ = 2 := by decide +kernel
  exact h σ (mem_rootFinset.2 hσ)

theorem abs_iform_le_two_E6 {ρ σ : Fin (Tag.rank .E6) → ℤ} (hρ : IsRoot .E6 ρ)
    (hσ : IsRoot .E6 σ) : |iform ρ σ| ≤ 2 := by
  have h := iform_sq_le ρ σ
  rw [iform_self_isRoot_E6 hρ, iform_self_isRoot_E6 hσ] at h
  rw [abs_le]
  constructor <;> nlinarith

theorem even_iform_self_E6 (y : Fin (Tag.rank .E6) → ℤ) : Even (iform y y) := by
  have h : ∀ z : Fin (Tag.rank .E6) → ZMod 2,
      ∑ i, ∑ j, z i * ((Tag.symmetrizedCartan .E6 i j : ℤ) : ZMod 2) * z j = 0 := by
    decide +kernel
  have h2 := h fun i => (y i : ZMod 2)
  rw [even_iff_two_dvd]
  have h3 : ((iform y y : ℤ) : ZMod 2) = 0 := by
    simp only [iform]
    push_cast
    exact h2
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (iform y y) 2).1 h3

theorem exists_eq_two_smul_of_even_iform_single_E6 (x : Fin (Tag.rank .E6) → ℤ)
    (hx : ∀ j, Even (iform x (Pi.single j 1))) : ∃ y : Fin (Tag.rank .E6) → ℤ, x = 2 • y := by
  have h1 : ∀ z : Fin (Tag.rank .E6) → ZMod 2,
      (∀ j, ∑ i, z i * ((Tag.symmetrizedCartan .E6 i j : ℤ) : ZMod 2) = 0) → ∀ i, z i = 0 := by
    decide +kernel
  have hxev : ∀ i, (2 : ℤ) ∣ x i := by
    have h3 := h1 (fun i => (x i : ZMod 2)) (fun j => by
      have h4 : ((iform x (Pi.single j 1) : ℤ) : ZMod 2) = 0 := by
        have h6 := even_iff_two_dvd.1 (hx j)
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).2 (by exact_mod_cast h6)
      have h5 : iform x (Pi.single j 1) = ∑ i, x i * Tag.symmetrizedCartan .E6 i j := by
        simp only [iform, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, ite_true]
      rw [h5] at h4
      push_cast at h4
      exact h4)
    intro i
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1 (h3 i)
  choose y hy using hxev
  exact ⟨y, funext fun i => by simp [hy i]⟩

end CFSG.ClassicalInvolution.ModelFacts.Levi
