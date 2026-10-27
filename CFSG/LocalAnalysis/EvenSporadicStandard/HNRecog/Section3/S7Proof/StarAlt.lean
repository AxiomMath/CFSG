module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem s7_alt_equiv {G : Type} [Group G] {S A : Subgroup G} (hAS : A ≤ S) (ψ : ↥S ≃* Sym 8)
    (hA : Nat.card ↥A = 20160) :
    ∃ φ₀ : alternatingGroup (Fin 8) ≃* ↥A,
      ∀ s : alternatingGroup (Fin 8), ((φ₀ s : ↥A) : G) = ((ψ.symm (s : Sym 8) : ↥S) : G) := by
  let A' : Subgroup ↥S := A.subgroupOf S
  let B : Subgroup (Sym 8) := A'.map ψ.toMonoidHom
  have hA' : Nat.card ↥A' = 20160 := by
    rw [← hA]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAS).toEquiv
  have hB : Nat.card ↥B = 20160 := by
    rw [← hA']
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective A' ψ.toMonoidHom ψ.injective).toEquiv).symm
  have hcard8 : Nat.card (Sym 8) = 40320 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    norm_num
  have hindex : B.index = 2 := by
    have hcard := B.card_mul_index
    rw [hB, hcard8] at hcard
    omega
  have hB_eq : B = alternatingGroup (Fin 8) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hindex
  have hmem : ∀ s : alternatingGroup (Fin 8), ((ψ.symm (s : Sym 8) : ↥S) : G) ∈ A := by
    intro s
    have hsB : (s : Sym 8) ∈ B := by rw [hB_eq]; exact s.2
    rw [Subgroup.mem_map] at hsB
    obtain ⟨a, ha, hpsi⟩ := hsB
    have hsymm : (ψ.symm (s : Sym 8) : ↥S) = a := by
      rw [← hpsi]
      exact MulEquiv.symm_apply_apply ψ a
    rw [hsymm]
    exact Subgroup.mem_subgroupOf.mp ha
  let f : ↥(alternatingGroup (Fin 8)) →* ↥A :=
    { toFun := fun s => ⟨((ψ.symm (s : Sym 8) : ↥S) : G), hmem s⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro s t
        apply Subtype.ext
        simp [Subgroup.coe_mul] }
  have hfinj : Function.Injective f := by
    intro s t hst
    have h1 : (ψ.symm (s : Sym 8) : ↥S) = (ψ.symm (t : Sym 8) : ↥S) := by
      apply Subtype.ext
      exact congrArg (fun x : ↥A => (x : G)) hst
    have h2 : (s : Sym 8) = (t : Sym 8) := by
      simpa using congrArg ψ h1
    exact Subtype.ext h2
  have hcard_alt : Nat.card ↥(alternatingGroup (Fin 8)) = Nat.card ↥A := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin, hA]
    norm_num
  haveI : Finite ↥A := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  have hf : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).mpr ⟨hfinj, hcard_alt⟩
  exact ⟨MulEquiv.ofBijective f hf, fun s => rfl⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
