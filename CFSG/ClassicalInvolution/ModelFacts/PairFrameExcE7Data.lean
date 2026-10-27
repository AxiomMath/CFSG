module

public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Data
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcConn

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem RootSpace

def thetaE7 : Fin (Tag.rank .E7) → ℤ := ![2, 2, 3, 4, 3, 2, 1]

theorem mem_rootFinset_thetaE7 : thetaE7 ∈ rootFinset .E7 := by decide +kernel

theorem isRoot_thetaE7 : IsRoot .E7 thetaE7 := mem_rootFinset.1 mem_rootFinset_thetaE7

theorem iform_thetaE7_single (i : Fin (Tag.rank .E7)) :
    iform thetaE7 (Pi.single i 1) = if i.val = 0 then 1 else 0 := by
  revert i; decide +kernel

theorem abs_iform_thetaE7_le : ∀ σ ∈ rootFinset .E7, |iform thetaE7 σ| ≤ 2 := by
  decide +kernel

theorem iform_thetaE7_eq_zero_iff : ∀ σ ∈ rootFinset .E7,
    (iform thetaE7 σ = 0 ↔ σ ⟨0, by decide⟩ = 0) := by
  decide +kernel

theorem iform_self_isRoot_E7 {σ : Fin (Tag.rank .E7) → ℤ} (hσ : IsRoot .E7 σ) : iform σ σ = 2 := by
  have h : ∀ σ ∈ rootFinset .E7, iform σ σ = 2 := by decide +kernel
  exact h σ (mem_rootFinset.2 hσ)

theorem abs_iform_le_two_E7 {ρ σ : Fin (Tag.rank .E7) → ℤ} (hρ : IsRoot .E7 ρ)
    (hσ : IsRoot .E7 σ) : |iform ρ σ| ≤ 2 := by
  have h := iform_sq_le ρ σ
  rw [iform_self_isRoot_E7 hρ, iform_self_isRoot_E7 hσ] at h
  rw [abs_le]
  constructor <;> nlinarith

theorem even_iform_self_E7 (y : Fin (Tag.rank .E7) → ℤ) : Even (iform y y) := by
  have h : ∀ z : Fin (Tag.rank .E7) → ZMod 2,
      ∑ i, ∑ j, z i * ((Tag.symmetrizedCartan .E7 i j : ℤ) : ZMod 2) * z j = 0 := by
    decide +kernel
  have h2 := h fun i => (y i : ZMod 2)
  rw [even_iff_two_dvd]
  have h3 : ((iform y y : ℤ) : ZMod 2) = 0 := by
    simp only [iform]
    push_cast
    exact h2
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (iform y y) 2).1 h3

@[expose] def glueE7 : Fin (Tag.rank .E7) → ℤ := ![0, 1, 0, 0, 1, 0, 1]

theorem eq_zero_or_glue_of_even_E7 (x : Fin (Tag.rank .E7) → ℤ)
    (hx : ∀ j, Even (iform x (Pi.single j 1))) :
    ∃ y : Fin (Tag.rank .E7) → ℤ, x = (2 : ℤ) • y ∨ x = glueE7 + (2 : ℤ) • y := by
  have h1 : ∀ z : Fin (Tag.rank .E7) → ZMod 2,
      (∀ j, ∑ i, z i * ((Tag.symmetrizedCartan .E7 i j : ℤ) : ZMod 2) = 0) →
        z = 0 ∨ z = fun i => ((glueE7 i : ℤ) : ZMod 2) := by
    decide +kernel
  have h3 := h1 (fun i => (x i : ZMod 2)) (fun j => by
    have h4 : ((iform x (Pi.single j 1) : ℤ) : ZMod 2) = 0 := by
      have h6 := even_iff_two_dvd.1 (hx j)
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).2 (by exact_mod_cast h6)
    have h5 : iform x (Pi.single j 1) = ∑ i, x i * Tag.symmetrizedCartan .E7 i j := by
      simp only [iform, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
    rw [h5] at h4
    push_cast at h4
    exact h4)
  rcases h3 with h | h
  · have hev : ∀ i, (2 : ℤ) ∣ x i := fun i => by
      have h2 : ((x i : ℤ) : ZMod 2) = 0 := congrFun h i
      exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1 h2
    choose y hy using hev
    exact ⟨y, Or.inl (funext fun i => by simp [hy i])⟩
  · have hev : ∀ i, (2 : ℤ) ∣ x i - glueE7 i := fun i => by
      have h2 : (((x i - glueE7 i : ℤ)) : ZMod 2) = 0 := by
        have := congrFun h i
        push_cast
        rw [this, sub_self]
      exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1 h2
    choose y hy using hev
    exact ⟨y, Or.inr (funext fun i => by
      have := hy i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith)⟩

theorem twinFree_E7 {ρ δ : Fin (Tag.rank .E7) → ℤ} (hρ : IsRoot .E7 ρ) (hδ : IsRoot .E7 δ)
    (h : ∀ j : Fin (Tag.rank .E7), Even (iform (ρ - δ) (Pi.single j 1))) :
    ρ = δ ∨ ρ = -δ := by
  set x := ρ - δ with hxdef
  set g : Fin (Tag.rank .E7) → ℤ := glueE7 with hg
  have hρρ := iform_self_isRoot_E7 hρ
  have hδδ := iform_self_isRoot_E7 hδ
  have ht := abs_iform_le_two_E7 hρ hδ
  rw [abs_le] at ht
  have hnorm : iform x x = 4 - 2 * iform ρ δ := by
    rw [hxdef, iform_sub_left, iform_sub_right, iform_sub_right, hρρ, hδδ, iform_comm δ ρ]
    ring
  have key : ∀ u : Fin (Tag.rank .E7) → ℤ, iform u u = 0 → u = 0 := fun u hu => by
    by_contra hne
    have := iform_self_pos hne
    omega
  have hg0 : ∀ j, iform g (Pi.single j 1) % 2 = 0 := by
    rw [hg]; unfold glueE7; decide +kernel
  have hgg : iform g g = 6 := by rw [hg]; unfold glueE7; decide +kernel
  have hgy : ∀ y : Fin (Tag.rank .E7) → ℤ, Even (iform g y) := fun y => by
    rw [iform_eq_sum_single]
    refine Finset.even_sum _ fun j _ => ?_
    exact (Int.even_iff.2 (hg0 j)).mul_left _
  have hmod : (iform x x) % 8 = 0 ∨ (iform x x) % 8 = 6 := by
    obtain ⟨y, hy | hy⟩ := eq_zero_or_glue_of_even_E7 x h
    · left
      rw [hy, iform_smul_left, iform_smul_right]
      obtain ⟨m, hm⟩ := even_iform_self_E7 y
      omega
    · right
      have e : iform x x = 6 + 4 * iform g y + 4 * iform y y := by
        rw [hy, iform_add_left, iform_add_right, iform_add_right]
        simp only [iform_smul_left, iform_smul_right]
        rw [iform_comm y g, hgg]
        ring
      obtain ⟨m₁, hm₁⟩ := hgy y
      obtain ⟨m₂, hm₂⟩ := even_iform_self_E7 y
      omega
  have hxρ : Even (iform x ρ) := by
    rw [iform_eq_sum_single]
    exact Finset.even_sum _ fun j _ => (h j).mul_left _
  have hxρ' : iform x ρ = 2 - iform δ ρ := by
    rw [hxdef, iform_sub_left, hρρ]
  rw [iform_comm δ ρ] at hxρ'
  obtain ⟨m, hm⟩ := hxρ
  have h4 : iform ρ δ = 2 ∨ iform ρ δ = -2 := by omega
  rcases h4 with h4 | h4
  · left
    have : iform x x = 0 := by rw [hnorm, h4]; norm_num
    exact sub_eq_zero.1 (key _ this)
  · right
    have : iform (ρ + δ) (ρ + δ) = 0 := by
      rw [iform_add_left, iform_add_right, iform_add_right, hρρ, hδδ, iform_comm δ ρ, h4]
      norm_num
    exact eq_neg_of_add_eq_zero_left (key _ this)

end CFSG.ClassicalInvolution.ModelFacts.Levi
