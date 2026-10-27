module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BSwSetup
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BSwKer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private theorem sec5b_map_conjugate {G N : Type*} [Group G] [Group N] (f : G →* N)
    (A : Subgroup G) (c : G) :
    (CFSG.conjugate A c).map f = CFSG.conjugate (A.map f) (f c) := by
  rw [CFSG.conjugate, CFSG.conjugate, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [MulAut.conj_apply, MulAut.conj_apply]
  simp only [map_mul, map_inv]

private theorem sec5b_conj_gen {G : Type*} [Group G] {A : Subgroup G} {c : G}
    (hA : A ≤ Subgroup.closure {a : G | a ∈ A ∧ Odd (orderOf a)}) :
    CFSG.conjugate A c ≤
      Subgroup.closure {b : G | b ∈ CFSG.conjugate A c ∧ Odd (orderOf b)} := by
  have h1 : A.map (MulAut.conj c⁻¹).toMonoidHom ≤
      (Subgroup.closure {a : G | a ∈ A ∧ Odd (orderOf a)}).map
        (MulAut.conj c⁻¹).toMonoidHom :=
    Subgroup.map_mono hA
  rw [MonoidHom.map_closure] at h1
  refine le_trans h1 (Subgroup.closure_mono ?_)
  rintro b ⟨a, ⟨haA, haodd⟩, rfl⟩
  refine ⟨Subgroup.mem_map_of_mem _ haA, ?_⟩
  have hof : orderOf ((MulAut.conj c⁻¹).toMonoidHom a) = orderOf a := by
    rw [show (MulAut.conj c⁻¹).toMonoidHom a = (MulAut.conj c⁻¹) a from rfl,
      MulEquiv.orderOf_eq]
  rw [hof]
  exact haodd

theorem sw_conj_of_img {Λ X : Type} [Group Λ] [Group X] [Finite Λ] {τ : Λ →* X}
    (hτ : SwCentralTwo τ) {A₁ A₂ : Subgroup Λ} {z : Λ} (S : SwSetup A₁ A₂ z) {c : Λ}
    (h : CFSG.conjugate (A₁.map τ) (τ c) = A₂.map τ) : CFSG.conjugate A₁ c = A₂ := by
  have hmap : (CFSG.conjugate A₁ c).map τ = A₂.map τ := by
    rw [sec5b_map_conjugate, h]
  refine le_antisymm ?_ ?_
  · refine le_trans (sec5b_conj_gen S.pocket₁.gen)
      ((Subgroup.closure_le A₂).2 ?_)
    rintro b ⟨hbB, hbodd⟩
    have hbmap : τ b ∈ A₂.map τ := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem τ hbB
    obtain ⟨k, hkA₂, hk⟩ := Subgroup.mem_map.mp hbmap
    exact hτ.odd_mem hbodd hkA₂ hk.symm
  · refine le_trans S.pocket₂.gen
      ((Subgroup.closure_le (CFSG.conjugate A₁ c)).2 ?_)
    rintro a ⟨haA₂, haodd⟩
    have hamap : τ a ∈ (CFSG.conjugate A₁ c).map τ := by
      rw [hmap]
      exact Subgroup.mem_map_of_mem τ haA₂
    obtain ⟨k, hk, hkτ⟩ := Subgroup.mem_map.mp hamap
    exact hτ.odd_mem haodd hk hkτ.symm

theorem sw_cent_of_conj {Λ : Type} [Group Λ] {A₁ A₂ : Subgroup Λ} {z : Λ}
    (S : SwSetup A₁ A₂ z) (hz : orderOf z = 2) {c : Λ} (h : CFSG.conjugate A₁ c = A₂) :
    c ∈ centralizer ({z} : Set Λ) := by
  set w : Λ := c⁻¹ * z * c with hw
  have hwA₂ : w ∈ A₂ := by
    rw [← h]
    refine Subgroup.mem_map.mpr ⟨z, S.pocket₁.mem, ?_⟩
    simp [hw, MulAut.conj_apply]
  have hw2 : orderOf w = 2 := by
    have hweq : w = (MulAut.conj c⁻¹) z := by
      simp [hw, MulAut.conj_apply]
    rw [hweq, MulEquiv.orderOf_eq, hz]
  have hwcent : ∀ a ∈ A₂, a * w = w * a := by
    intro a ha
    rw [← h] at ha
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    have hxa : (MulAut.conj c⁻¹).toMonoidHom x = c⁻¹ * x * c := by
      simp [MulAut.conj_apply]
    have hxz : x * z = z * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (S.pocket₁.le_cent hx)
    rw [hxa, hw]
    calc c⁻¹ * x * c * (c⁻¹ * z * c)
        = c⁻¹ * (x * z) * c := by group
      _ = c⁻¹ * (z * x) * c := by rw [hxz]
      _ = c⁻¹ * z * c * (c⁻¹ * x * c) := by group
  have hzcent : ∀ a ∈ A₂, a * z = z * a :=
    fun a ha => Subgroup.mem_centralizer_singleton_iff.mp (S.pocket₂.le_cent ha)
  have hz2 : ∃ k : ℕ, orderOf z = 2 ^ k := ⟨1, by rw [hz, pow_one]⟩
  have hw2' : ∃ k : ℕ, orderOf w = 2 ^ k := ⟨1, by rw [hw2, pow_one]⟩
  rcases S.pocket₂.two_center w hwA₂ hwcent hw2' z S.pocket₂.mem hzcent hz2 with
    h1 | h1 | h1
  · exfalso
    have h' : c⁻¹ * z * c = 1 := hw ▸ h1
    have hz1 : z = 1 := by
      calc z = c * (c⁻¹ * z * c) * c⁻¹ := by group
        _ = c * 1 * c⁻¹ := by rw [h']
        _ = 1 := by group
    rw [hz1, orderOf_one] at hz
    exact absurd hz (by decide)
  · exfalso
    rw [h1, orderOf_one] at hz
    exact absurd hz (by decide)
  · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have h' : c⁻¹ * z * c = z := hw ▸ h1
    have hzc : z * c = c * z := by
      calc z * c = c * (c⁻¹ * z * c) := by group
        _ = c * z := by rw [h']
    exact hzc.symm

end CFSG.OddStandard.SmallF3.Omega
