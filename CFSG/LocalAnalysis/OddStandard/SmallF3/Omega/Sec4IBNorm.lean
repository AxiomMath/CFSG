module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBMono

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma exists_third (k k' : Fin 7) (h : k ≠ k') : ∃ m : Fin 7, m ≠ k ∧ m ≠ k' := by
  revert k k'
  decide

private theorem sec4IT_smul_of_normalizes (fr : Sec4IFrame Q) (g : OGroup Q)
    (hg : ∀ s : Fin 7 → ZMod 2, IsEvenVec s →
      ∃ s' : Fin 7 → ZMod 2, IsEvenVec s' ∧ g⁻¹ * sec4IT fr s * g = sec4IT fr s')
    (s : Fin 7 → ZMod 2) (hs : IsEvenVec s) (j : Fin 7) :
    ∃ eps : (ZMod 3)ˣ,
      (sec4IT fr s : V ≃ₗ[ZMod 3] V) ((g : V ≃ₗ[ZMod 3] V) (fr.b j)) =
        (eps : ZMod 3) • ((g : V ≃ₗ[ZMod 3] V) (fr.b j)) := by
  obtain ⟨s', _hs'even, hs'eq⟩ := hg s hs
  refine ⟨sec4ISgn (s' j), ?_⟩
  have h1 := congrArg (fun e : OGroup Q => (e : V ≃ₗ[ZMod 3] V) (fr.b j)) hs'eq
  change (g : V ≃ₗ[ZMod 3] V)⁻¹ ((sec4IT fr s : V ≃ₗ[ZMod 3] V)
    ((g : V ≃ₗ[ZMod 3] V) (fr.b j))) = (sec4IT fr s' : V ≃ₗ[ZMod 3] V) (fr.b j) at h1
  rw [sec4IT_apply_basis] at h1
  have h2 := congrArg (fun y => (g : V ≃ₗ[ZMod 3] V) y) h1
  simp only [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply, map_smul] at h2
  simpa using h2

private theorem sec4I_exists_smul_basis (fr : Sec4IFrame Q) (g : OGroup Q)
    (hg : ∀ s : Fin 7 → ZMod 2, IsEvenVec s →
      ∃ s' : Fin 7 → ZMod 2, IsEvenVec s' ∧ g⁻¹ * sec4IT fr s * g = sec4IT fr s')
    (j : Fin 7) :
    ∃ (k : Fin 7) (c : (ZMod 3)ˣ),
      (g : V ≃ₗ[ZMod 3] V) (fr.b j) = (c : ZMod 3) • fr.b k := by
  set v : V := (g : V ≃ₗ[ZMod 3] V) (fr.b j) with hv
  have hvne : v ≠ 0 := by
    intro hv0
    have hgj : (g : V ≃ₗ[ZMod 3] V) (fr.b j) = 0 := hv.symm.trans hv0
    have hbj : fr.b j = 0 := by
      have := congrArg (fun y => (g : V ≃ₗ[ZMod 3] V).symm y) hgj
      simpa using this
    exact fr.b.ne_zero j hbj
  have hatmost : ∀ k k' : Fin 7, k ≠ k' →
      fr.b.repr v k = 0 ∨ fr.b.repr v k' = 0 := by
    intro k k' hkk'
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hkne, hk'ne⟩ := hcon
    obtain ⟨m, hmk, hmk'⟩ := exists_third k k' hkk'
    have hs_even : IsEvenVec (Pi.single k 1 + Pi.single m 1 : Fin 7 → ZMod 2) := by
      show (∑ i, (Pi.single k 1 + Pi.single m 1 : Fin 7 → ZMod 2) i) = 0
      simp only [Pi.add_apply]
      rw [Finset.sum_add_distrib, Finset.sum_pi_single', Finset.sum_pi_single']
      simp only [Finset.mem_univ, if_true]
      decide
    obtain ⟨eps, heps⟩ :=
      sec4IT_smul_of_normalizes fr g hg (Pi.single k 1 + Pi.single m 1) hs_even j
    have hcoord : ∀ i : Fin 7, fr.b.repr v i ≠ 0 →
        ((sec4ISgn ((Pi.single k 1 + Pi.single m 1 : Fin 7 → ZMod 2) i) : (ZMod 3)ˣ) :
          ZMod 3) = (eps : ZMod 3) := by
      intro i hi
      have h := congrArg (fun y => fr.b.repr y i) heps
      rw [sec4IT_repr] at h
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at h
      exact mul_right_cancel₀ hi h
    have hval : ((sec4ISgn ((Pi.single k 1 + Pi.single m 1 : Fin 7 → ZMod 2) k) :
          (ZMod 3)ˣ) : ZMod 3) =
        ((sec4ISgn ((Pi.single k 1 + Pi.single m 1 : Fin 7 → ZMod 2) k') :
          (ZMod 3)ˣ) : ZMod 3) := by
      rw [hcoord k hkne, hcoord k' hk'ne]
    have hunits := Units.ext hval
    have hsk : (Pi.single k 1 + Pi.single m 1 : Fin 7 → ZMod 2) k = 1 := by
      simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hmk), add_zero]
    have hsk' : (Pi.single k 1 + Pi.single m 1 : Fin 7 → ZMod 2) k' = 0 := by
      have hk'k : k' ≠ k := fun h => hkk' h.symm
      have hk'm : k' ≠ m := fun h => hmk' h.symm
      simp only [Pi.add_apply, Pi.single_eq_of_ne hk'k, Pi.single_eq_of_ne hk'm, add_zero]
    have hcontra : (1 : ZMod 2) = 0 := by
      have := sec4ISgn_injective hunits
      rwa [hsk, hsk'] at this
    exact one_ne_zero hcontra
  have hrepr_ne : fr.b.repr v ≠ 0 := by
    intro hzero
    have : v = 0 := by
      have := congrArg (fun w => fr.b.repr.symm w) hzero
      simpa using this
    exact hvne this
  obtain ⟨k0, hk0ne⟩ := Finsupp.ne_iff.mp hrepr_ne
  simp only [Finsupp.zero_apply] at hk0ne
  refine ⟨k0, Units.mk0 (fr.b.repr v k0) hk0ne, ?_⟩
  rw [Units.val_mk0]
  have hother : ∀ i : Fin 7, i ≠ k0 → fr.b.repr v i = 0 := by
    intro i hi
    rcases hatmost k0 i (Ne.symm hi) with h | h
    · exact absurd h hk0ne
    · exact h
  have hsum : (∑ i, fr.b.repr v i • fr.b i) = fr.b.repr v k0 • fr.b k0 := by
    refine Finset.sum_eq_single k0 ?_ ?_
    · intro i _ hi
      rw [hother i hi, zero_smul]
    · intro hk0
      exact absurd (Finset.mem_univ k0) hk0
  rw [← hsum, fr.b.sum_repr]

private theorem sec4I_sigma_injective (fr : Sec4IFrame Q) (g : OGroup Q)
    (sigma0 : Fin 7 → Fin 7) (c : Fin 7 → (ZMod 3)ˣ)
    (hc : ∀ j, (g : V ≃ₗ[ZMod 3] V) (fr.b j) = (c j : ZMod 3) • fr.b (sigma0 j)) :
    Function.Injective sigma0 := by
  intro j j' hjj
  by_contra hne
  have h1 := hc j
  have h2 := hc j'
  rw [hjj] at h1
  have hzero : (g : V ≃ₗ[ZMod 3] V)
      ((c j' : ZMod 3) • fr.b j - (c j : ZMod 3) • fr.b j') = 0 := by
    rw [map_sub, map_smul, map_smul, h1, h2]
    rw [smul_smul, smul_smul, mul_comm (c j' : ZMod 3) (c j : ZMod 3), sub_self]
  have hvec : (c j' : ZMod 3) • fr.b j - (c j : ZMod 3) • fr.b j' = 0 := by
    have := congrArg (fun y => (g : V ≃ₗ[ZMod 3] V).symm y) hzero
    simpa using this
  have hcoord := congrArg (fun y => fr.b.repr y j) hvec
  simp only [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, map_zero,
    Finsupp.zero_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne hne, smul_eq_mul, mul_one, mul_zero, sub_zero] at hcoord
  exact (c j').ne_zero hcoord

theorem sec4I_eq_mono_of_normalizes (fr : Sec4IFrame Q) (g : OGroup Q)
    (hg : ∀ s : Fin 7 → ZMod 2, IsEvenVec s →
      ∃ s' : Fin 7 → ZMod 2, IsEvenVec s' ∧ g⁻¹ * sec4IT fr s * g = sec4IT fr s') :
    ∃ (σ : Equiv.Perm (Fin 7)) (u : Fin 7 → ZMod 2), g = sec4IMono fr σ u := by
  have hex : ∀ j : Fin 7, ∃ (k : Fin 7) (c : (ZMod 3)ˣ),
      (g : V ≃ₗ[ZMod 3] V) (fr.b j) = (c : ZMod 3) • fr.b k :=
    fun j => sec4I_exists_smul_basis fr g hg j
  choose sigma0 c hc using hex
  have hinj : Function.Injective sigma0 := sec4I_sigma_injective fr g sigma0 c hc
  have hbij : Function.Bijective sigma0 := Finite.injective_iff_bijective.mp hinj
  have hcard : Fintype.card (ZMod 2) = Fintype.card (ZMod 3)ˣ := by
    rw [ZMod.card, ZMod.card_units]
  have hsurj : Function.Surjective sec4ISgn :=
    (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hcard)).mp
      sec4ISgn_injective
  choose u hu using fun j => hsurj (c j)
  refine ⟨Equiv.ofBijective sigma0 hbij, u, ?_⟩
  apply sec4I_ogroup_ext fr
  intro i
  rw [hc i, sec4IMono_apply, hu i]
  rfl

end CFSG.OddStandard.SmallF3.Omega
