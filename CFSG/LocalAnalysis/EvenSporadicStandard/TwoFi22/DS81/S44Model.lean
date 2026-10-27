module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44Frame
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44ModelOrb

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup CFSG.Sporadic.Fi23 FrameJ Gen FrameCd CFSG.EvenSporadicStandard.Wong77.Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option linter.unusedSectionVars false

section Aut



theorem frameAut_Cd (R : Fi22CoverRest)
    (hAut : Nat.card ↥(permStab golayCode ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 23)) (0 : Fin 23)) ≤ 443520)
    (α : E0 ≃* E0) (hz : ∀ e : E0, (e : ↥Cd) = dCd → (α e : ↥Cd) = dCd)
    (hO : ∀ e : E0, (e : ↥Cd) ∈ orbSet 0 → (α e : ↥Cd) ∈ orbSet 0) :
    ∃ n ∈ normalizer (E0 : Set ↥Cd), ∀ e : E0, (α e : ↥Cd) = n * e * n⁻¹ := by
  let a : Fin 23 → E0 := fun j => ⟨fjQ j, fjQ_mem j⟩
  have h0 : (α (a 0) : ↥Cd) = fjQ 0 := (hz (a 0) fjQ_zero).trans fjQ_zero.symm
  have hex : ∀ j : Fin 23, ∃ i : Fin 23, (α (a j) : ↥Cd) = fjQ i := by
    intro j
    by_cases hj : j = 0
    · exact ⟨0, hj ▸ h0⟩
    · have hmem : (a j : ↥Cd) ∈ orbSet 0 := by
        rw [orbSet_zero_eq]
        exact ⟨j, hj, rfl⟩
      have := hO _ hmem
      rw [orbSet_zero_eq] at this
      obtain ⟨i, -, hi⟩ := this
      exact ⟨i, hi⟩
  choose f hf using hex
  have hf0 : f 0 = 0 := fjQ_injective ((hf 0).symm.trans h0)
  have hinj : Function.Injective f := by
    intro i j hij
    have h1 : α (a i) = α (a j) :=
      Subtype.ext ((hf i).trans ((congrArg fjQ hij).trans (hf j).symm))
    exact fjQ_injective (congrArg Subtype.val (α.injective h1))
  let π : Equiv.Perm (Fin 23) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj)
  have hπ : ∀ j, (α (a j) : ↥Cd) = fjQ (π j) := hf
  have hA : ∀ s : Finset (Fin 23), (α ⟨evC s, evC_mem s⟩ : ↥Cd) = evC (s.image π) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have h1 : (⟨evC ∅, evC_mem ∅⟩ : E0) = 1 := Subtype.ext evC_empty
      rw [h1, map_one, Finset.image_empty, evC_empty]
      rfl
    | insert b s hb ih =>
      have hnot : π b ∉ s.image π := by
        rw [Finset.mem_image]
        rintro ⟨x, hx, hxb⟩
        exact hb (π.injective hxb ▸ hx)
      have h1 : (⟨evC (insert b s), evC_mem _⟩ : E0) = a b * ⟨evC s, evC_mem s⟩ :=
        Subtype.ext (evC_insert hb)
      rw [h1, map_mul, Subgroup.coe_mul, hπ, ih, Finset.image_insert, evC_insert hnot]
  have hperm : π ∈ permStab golayCode := by
    refine mem_permStab_of_evC fun s => ?_
    rw [← hA s]
    constructor
    · intro h
      have h1 : α ⟨evC s, evC_mem s⟩ = 1 := Subtype.ext h
      have h2 : (⟨evC s, evC_mem s⟩ : E0) = 1 := α.injective (h1.trans (map_one α).symm)
      have h3 := congrArg (fun x : E0 => (x : ↥Cd)) h2
      simpa using h3
    · intro h
      have h1 : (⟨evC s, evC_mem s⟩ : E0) = 1 := Subtype.ext h
      rw [h1, map_one]
      rfl
  have hπmem : π ∈ (permHom : normalizer (E0 : Set ↥Cd) →* Equiv.Perm (Fin 23)).range := by
    rw [range_permHom_eq R hAut]
    refine Subgroup.mem_inf.2 ⟨hperm, ?_⟩
    rw [MulAction.mem_stabilizer_iff]
    exact hf0
  obtain ⟨n, hn⟩ := hπmem
  have hnπ : IsPerm (n : ↥Cd) π := by
    rw [← hn]
    exact isPerm_permOf n
  refine ⟨(n : ↥Cd), n.2, fun e => ?_⟩
  obtain ⟨s, -, hs⟩ := exists_evC e.2
  have he : e = ⟨evC s, evC_mem s⟩ := Subtype.ext hs.symm
  rw [he, hA s]
  exact (hnπ.conj_evC s).symm

end Aut

section Main



theorem frameModel_Cd (R : Fi22CoverRest)
    (hAut : Nat.card ↥(permStab golayCode ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 23)) (0 : Fin 23)) ≤ 443520) :
    ∃ O : Fin 5 → Set ↥Cd, FrameModel ↥Cd E0 dCd O := by
  refine ⟨orbSet, ⟨?_, ?_, E0_card_normalizer, isOrbit_orbSet, ncard_orbSet,
    fun i j h => disjoint_orbSet h, one_notMem_orbSet, dCd_notMem_orbSet,
    fun v hv hv1 => cover_orbSet hv hv1, swap_orbSet,
    fun u hu u' hu' hne => prod_orbSet hu hu' hne, ?_, frameAut_Cd R hAut⟩⟩
  · rw [← fjQ_zero]
    exact fjQ_mem 0
  · intro h
    have h2 : orderOf (dCd : ↥Cd) = 2 := orderOf_dCd
    rw [h, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  · rw [insert_orbSet_zero]
    exact closure_range_fjQ

end Main

end CFSG.EvenSporadicStandard.TwoFi22.DS81
