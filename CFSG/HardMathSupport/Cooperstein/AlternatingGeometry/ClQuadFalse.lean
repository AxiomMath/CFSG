module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClClassify

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

namespace Classif

variable {Ω : Type*} [DecidableEq Ω] {W : Subgroup (Perm Ω)}

theorem false_of_threeCycle_mem_normalizer (hW : IsPGroup 2 W)
    (hmatch : ∀ z, partner hW z ≠ z) {Sstar : Subgroup (Perm Ω)} (hWS : W ≤ Sstar)
    (hSN : Sstar ≤ Subgroup.normalizer (W : Set (Perm Ω))) {a c : Ω} (hc1 : c ≠ a)
    (hc2 : c ≠ partner hW a)
    (hσ : swap a (partner hW a) * swap a c ∈ Subgroup.normalizer (Sstar : Set (Perm Ω))) :
    False := by
  have hsw : ∀ z, swap z (partner hW z) ∈ W := fun z => swap_partner_mem hW (hmatch z)
  have hωω := partner_partner hW
  have hωinj : ∀ {x y}, partner hW x = partner hW y → x = y := fun {x y} h => by
    have := congrArg (partner hW) h
    rwa [hωω, hωω] at this
  have h1 : swap a (partner hW a) ∈ Sstar := hWS (hsw a)
  have h2 := (Subgroup.mem_normalizer_iff.1 hσ _).1 h1
  have hca : partner hW a ≠ a := hmatch a
  have hca' : partner hW a ≠ c := fun h => hc2 h.symm
  have hσa : (swap a (partner hW a) * swap a c) a = c := by
    rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hc1 hc2]
  have hσa' : (swap a (partner hW a) * swap a c) (partner hW a) = a := by
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hca hca', swap_apply_right]
  have hcomp : (swap a (partner hW a) * swap a c) * swap a (partner hW a) *
      (swap a (partner hW a) * swap a c)⁻¹ = swap c a := by
    rw [← swap_apply_apply, hσa, hσa']
  have h3 : swap c a ∈ Sstar := by rw [← hcomp]; exact h2
  have hN := hSN h3
  have hcc : swap c (partner hW c) ∈ W := hsw c
  have h4 := (Subgroup.mem_normalizer_iff.1 hN _).1 hcc
  have hne1 : partner hW c ≠ c := hmatch c
  have hne2 : partner hW c ≠ a := fun h => hc2 (by rw [← h, hωω])
  have h5 : swap c a * swap c (partner hW c) * (swap c a)⁻¹ = swap a (partner hW c) := by
    rw [← swap_apply_apply, swap_apply_left, swap_apply_of_ne_of_ne hne1 hne2]
  rw [h5] at h4
  have h6 := partner_eq_of_swap_mem hW (x := a) (y := partner hW c) (Ne.symm hne2) h4
  exact hc1 (hωinj h6).symm

namespace Setup

open MulAction

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] {W : Subgroup (Perm Ω)}
  {E : ι → Subgroup (Perm Ω)} (S : Setup W E)

include S in
theorem exists_quad {z : Ω} (hz : Nat.card (orbit W z) = 4) :
    ∃ a c : Ω, c ≠ a ∧ c ≠ S.ω a ∧
      (orbit W a : Set Ω) = ↑({a, S.ω a, c, S.ω c} : Finset Ω) := by
  classical
  have hfin : (orbit W z : Set Ω).Finite := Set.toFinite _
  have hncard : (orbit W z : Set Ω).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact hz
  obtain ⟨c, hcorb, hc1, hc2⟩ : ∃ c ∈ (orbit W z : Set Ω), c ≠ z ∧ c ≠ S.ω z := by
    by_contra hcon
    push Not at hcon
    have hsub : (orbit W z : Set Ω) ⊆ {z, S.ω z} := by
      intro y hy
      by_cases h1 : y = z
      · exact Or.inl h1
      · exact Or.inr (hcon y hy h1)
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({z, S.ω z} : Set Ω).ncard ≤ 2 := by
      calc ({z, S.ω z} : Set Ω).ncard ≤ ({S.ω z} : Set Ω).ncard + 1 := Set.ncard_insert_le z _
        _ = 2 := by simp
    omega
  refine ⟨z, c, hc1, hc2, ?_⟩
  have hcorb' : (orbit W c : Set Ω) = orbit W z := orbit_eq_iff.2 hcorb
  have hωc : S.ω c ∈ (orbit W z : Set Ω) := by
    rw [← hcorb']; exact S.partner_mem_orbit c
  have hsub : (↑({z, S.ω z, c, S.ω c} : Finset Ω) : Set Ω) ⊆ orbit W z := by
    intro y hy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact mem_orbit_self _
    · exact S.partner_mem_orbit _
    · exact hcorb
    · exact hωc
  have hc3 : S.ω c ≠ z := fun h => hc2 (by rw [← h, S.ωω])
  have hc4 : S.ω c ≠ S.ω z := fun h => hc1 (S.ωinj h)
  have hcard : (↑({z, S.ω z, c, S.ω c} : Finset Ω) : Set Ω).ncard = 4 := by
    rw [Set.ncard_coe_finset]
    exact card_four (S.hmatch z).symm (Ne.symm hc1) (Ne.symm hc3) (Ne.symm hc2) (Ne.symm hc4)
      (S.hmatch c).symm
  exact (Set.eq_of_subset_of_ncard_le hsub (by omega) hfin).symm

include S in
theorem exists_quad_group {z : Ω} (hz : Nat.card (orbit W z) = 4) :
    ∃ (a c : Ω) (P : Subgroup (Perm Ω)), c ≠ a ∧ c ≠ S.ω a ∧
      (∀ p ∈ P, p ∈ W ∧ p ∈ alternatingGroup Ω ∧
        ∀ i, i ∉ ({a, S.ω a, c, S.ω c} : Finset Ω) → p i = i) ∧
      ∀ i ∈ ({a, S.ω a, c, S.ω c} : Finset Ω), ∀ j ∈ ({a, S.ω a, c, S.ω c} : Finset Ω),
        ∃ p ∈ P, p i = j := by
  classical
  obtain ⟨a, c, hc1, hc2, horb⟩ := S.exists_quad hz
  refine ⟨a, c, ?_⟩
  obtain ⟨a', ha'⟩ : ∃ a', S.ω a = a' := ⟨_, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c', S.ω c = c' := ⟨_, rfl⟩
  rw [ha'] at hc2 horb ⊢
  rw [hc'] at horb ⊢
  have haa' : a' ≠ a := ha' ▸ S.hmatch a
  have hcc' : c' ≠ c := hc' ▸ S.hmatch c
  have ha'c : a' ≠ c := fun h => hc2 h.symm
  have hωa' : S.ω a' = a := by rw [← ha', S.ωω]
  have hωc' : S.ω c' = c := by rw [← hc', S.ωω]
  have hc'a : c' ≠ a := fun h => hc2 (by rw [← hωc', h, ha'])
  have hc'a' : c' ≠ a' := fun h => hc1 (S.ωinj (by rw [hc', h, ha']))
  have hΔω : ∀ y ∈ ({a, a', c, c'} : Finset Ω), S.ω y ∈ ({a, a', c, c'} : Finset Ω) := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
    rcases hy with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl ha')
    · exact Or.inl hωa'
    · exact Or.inr (Or.inr (Or.inr hc'))
    · exact Or.inr (Or.inr (Or.inl hωc'))
  let x1 : Perm Ω := swap a a' * swap c c'
  let x2 : Perm Ω := swap a c * swap a' c'
  have hx1W : x1 ∈ W := by
    refine W.mul_mem ?_ ?_
    · have := S.swap_mem a; rwa [ha'] at this
    · have := S.swap_mem c; rwa [hc'] at this
  have hx1fix : ∀ i, i ∉ ({a, a', c, c'} : Finset Ω) → x1 i = i := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    simp only [x1, Perm.mul_apply]
    rw [swap_apply_of_ne_of_ne hi.2.2.1 hi.2.2.2, swap_apply_of_ne_of_ne hi.1 hi.2.1]
  have hx2fix : ∀ i, i ∉ ({a, a', c, c'} : Finset Ω) → x2 i = i := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    simp only [x2, Perm.mul_apply]
    rw [swap_apply_of_ne_of_ne hi.2.1 hi.2.2.2, swap_apply_of_ne_of_ne hi.1 hi.2.2.1]
  have hx1sign : x1 ∈ alternatingGroup Ω := by
    rw [mem_alternatingGroup, map_mul, sign_swap (Ne.symm haa'), sign_swap (Ne.symm hcc')]; rfl
  have hx2sign : x2 ∈ alternatingGroup Ω := by
    rw [mem_alternatingGroup, map_mul, sign_swap (Ne.symm hc1), sign_swap hc'a'.symm]; rfl
  have hx2a : x2 a = c := by
    simp only [x2, Perm.mul_apply]
    rw [swap_apply_of_ne_of_ne (Ne.symm haa') (Ne.symm hc'a), swap_apply_left]
  have hx2a' : x2 a' = c' := by
    simp only [x2, Perm.mul_apply]
    rw [swap_apply_left, swap_apply_of_ne_of_ne hc'a hcc']
  have hx2c : x2 c = a := by
    simp only [x2, Perm.mul_apply]
    rw [swap_apply_of_ne_of_ne hc2 (Ne.symm hcc'), swap_apply_right]
  have hx2c' : x2 c' = a' := by
    simp only [x2, Perm.mul_apply]
    rw [swap_apply_right, swap_apply_of_ne_of_ne haa' ha'c]
  have hx2W : x2 ∈ W := by
    have hWeq := S.classification.2.2
    rw [hWeq]
    refine ⟨?_, ?_⟩
    · intro y
      by_cases hy : y ∈ ({a, a', c, c'} : Finset Ω)
      · have hx2y : x2 y ∈ ({a, a', c, c'} : Finset Ω) := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
          rcases hy with rfl | rfl | rfl | rfl
          · rw [hx2a]; exact Or.inr (Or.inr (Or.inl rfl))
          · rw [hx2a']; exact Or.inr (Or.inr (Or.inr rfl))
          · rw [hx2c]; exact Or.inl rfl
          · rw [hx2c']; exact Or.inr (Or.inl rfl)
        have hyorb : y ∈ orbit W a := by
          have : y ∈ (orbit W a : Set Ω) := by rw [horb]; exact hy
          exact this
        have h1 : orbit W y = orbit W a := orbit_eq_iff.2 hyorb
        have : x2 y ∈ (orbit W a : Set Ω) := by rw [horb]; exact hx2y
        rw [h1]; exact this
      · rw [hx2fix y hy]; exact mem_orbit_self y
    · intro y
      by_cases hy : y ∈ ({a, a', c, c'} : Finset Ω)
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl | rfl
        · rw [hx2a, ha', hx2a', hc']
        · rw [hx2a', hωc', hωa', hx2a]
        · rw [hx2c, hc', ha', hx2c']
        · rw [hx2c', hωa', hωc', hx2c]
      · have hy' : S.ω y ∉ ({a, a', c, c'} : Finset Ω) := fun h => hy (by simpa [S.ωω] using hΔω _ h)
        rw [hx2fix y hy, hx2fix _ hy']
  let F : Subgroup (Perm Ω) :=
    { carrier := {p | ∀ i, i ∉ ({a, a', c, c'} : Finset Ω) → p i = i}
      mul_mem' := by
        intro p q hp hq i hi
        simp only [Perm.mul_apply]
        rw [hq i hi, hp i hi]
      one_mem' := fun i _ => rfl
      inv_mem' := by
        intro p hp i hi
        exact Perm.inv_eq_iff_eq.2 (hp i hi).symm }
  have hx1F : x1 ∈ F := hx1fix
  have hx2F : x2 ∈ F := hx2fix
  refine ⟨W ⊓ alternatingGroup Ω ⊓ F, hc1, hc2, ?_, ?_⟩
  · intro p hp
    exact ⟨hp.1.1, hp.1.2, hp.2⟩
  · have hx1P : x1 ∈ W ⊓ alternatingGroup Ω ⊓ F := ⟨⟨hx1W, hx1sign⟩, hx1F⟩
    have hx2P : x2 ∈ W ⊓ alternatingGroup Ω ⊓ F := ⟨⟨hx2W, hx2sign⟩, hx2F⟩
    have hx1a : x1 a = a' := by
      simp only [x1, Perm.mul_apply]
      rw [swap_apply_of_ne_of_ne (Ne.symm hc1) (Ne.symm hc'a), swap_apply_left]
    have hx12a : (x1 * x2) a = c' := by
      rw [Perm.mul_apply, hx2a]
      simp only [x1, Perm.mul_apply]
      rw [swap_apply_left, swap_apply_of_ne_of_ne hc'a hc'a']
    have hfrom : ∀ t ∈ ({a, a', c, c'} : Finset Ω),
        ∃ p ∈ W ⊓ alternatingGroup Ω ⊓ F, p a = t := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact ⟨1, one_mem _, rfl⟩
      · exact ⟨x1, hx1P, hx1a⟩
      · exact ⟨x2, hx2P, hx2a⟩
      · exact ⟨x1 * x2, mul_mem hx1P hx2P, hx12a⟩
    intro i hi j hj
    obtain ⟨p, hp, hpa⟩ := hfrom i hi
    obtain ⟨q, hq, hqa⟩ := hfrom j hj
    refine ⟨q * p⁻¹, mul_mem hq (inv_mem hp), ?_⟩
    rw [Perm.mul_apply, ← hpa]
    simp [hqa]

end Setup

end Classif

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
