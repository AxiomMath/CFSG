module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Toolbox
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso

public section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup
open scoped commutatorElement

theorem s8_A6_simple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem s8_A6_nonab : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
  by_contra hno
  push Not at hno
  have hs := s8_A6_simple
  let _ : CommGroup (alternatingGroup (Fin 6)) :=
    { (inferInstance : Group (alternatingGroup (Fin 6))) with mul_comm := fun a b => hno a b }
  have hp := hs.prime_card
  rw [Nat.card_eq_fintype_card, card_alternatingGroup] at hp
  simp [Nat.factorial] at hp
  norm_num at hp

theorem s8_comm_mulAut :
    commutator (MulAut (alternatingGroup (Fin 6))) =
      (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range := by
  apply le_antisymm
  · have hN : (MulAut.conj : alternatingGroup (Fin 6) →*
        MulAut (alternatingGroup (Fin 6))).range.Normal :=
      ⟨by
        rintro _ ⟨b, rfl⟩ g
        exact ⟨g b, (mul_conj_mul_inv g b).symm⟩⟩
    have hcard : Nat.card (MulAut (alternatingGroup (Fin 6)) ⧸ (MulAut.conj :
        alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range) = 2 ^ 2 := by
      rw [← Subgroup.index_eq_card, CFSG.QuasithinUnique.Setup.X3Aut.index_inner_alt6]
      norm_num
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard
    exact (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := (MulAut.conj :
      alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range)).1 hcomm
  · have hperf : commutator (alternatingGroup (Fin 6)) = ⊤ := by
      have := s8_A6_simple
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (alternatingGroup (Fin 6)))
        with h | h
      · exfalso
        obtain ⟨a, b, hab⟩ := s8_A6_nonab
        apply hab
        have hmem : ⁅a, b⁆ ∈ commutator (alternatingGroup (Fin 6)) :=
          Subgroup.commutator_mem_commutator (mem_top a) (mem_top b)
        rw [h, Subgroup.mem_bot, commutatorElement_def] at hmem
        calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
          _ = b * a := by rw [hmem, one_mul]
      · exact h
    rw [MonoidHom.range_eq_map, ← hperf, _root_.commutator_def, Subgroup.map_commutator,
      _root_.commutator_def]
    exact Subgroup.commutator_mono le_top le_top

theorem s8_conj_injective :
    Function.Injective (MulAut.conj :
      alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))) :=
  have := s8_A6_simple
  conj_injective_of_simple s8_A6_nonab

section J

variable {G : Type*} [Group G]

theorem s8_J_equiv (Abar : Subgroup G) (e : ↥Abar ≃* MulAut (alternatingGroup (Fin 6))) :
    Nonempty (↥(derivedIn Abar) ≃* alternatingGroup (Fin 6)) := by
  have hmap : (commutator ↥Abar).map e.toMonoidHom =
      commutator (MulAut (alternatingGroup (Fin 6))) := by
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective, ← _root_.commutator_def]
  have e1 : ↥(derivedIn Abar) ≃* ↥(commutator ↥Abar) :=
    (Subgroup.equivMapOfInjective _ Abar.subtype Abar.subtype_injective).symm
  have e2 : ↥(commutator ↥Abar) ≃*
      ↥((commutator ↥Abar).map e.toMonoidHom) :=
    Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective
  have e3 : ↥((commutator ↥Abar).map e.toMonoidHom) ≃*
      ↥(MulAut.conj : alternatingGroup (Fin 6) →*
        MulAut (alternatingGroup (Fin 6))).range :=
    MulEquiv.subgroupCongr (hmap.trans s8_comm_mulAut)
  have e4 : ↥(MulAut.conj : alternatingGroup (Fin 6) →*
        MulAut (alternatingGroup (Fin 6))).range ≃* alternatingGroup (Fin 6) :=
    (MonoidHom.ofInjective s8_conj_injective).symm
  exact ⟨e1.trans (e2.trans (e3.trans e4))⟩

theorem s8_J_simple (Abar : Subgroup G) (e : ↥Abar ≃* MulAut (alternatingGroup (Fin 6))) :
    IsSimpleGroup ↥(derivedIn Abar) := by
  obtain ⟨eJ⟩ := s8_J_equiv Abar e
  exact (MulEquiv.isSimpleGroup_congr eJ).2 s8_A6_simple

theorem s8_J_nonab (Abar : Subgroup G) (e : ↥Abar ≃* MulAut (alternatingGroup (Fin 6))) :
    ∃ a b : ↥(derivedIn Abar), a * b ≠ b * a := by
  obtain ⟨eJ⟩ := s8_J_equiv Abar e
  obtain ⟨a, b, hab⟩ := s8_A6_nonab
  exact ⟨eJ.symm a, eJ.symm b, fun h => hab (eJ.symm.injective (by simpa using h))⟩

theorem s8_J_card (Abar : Subgroup G) (e : ↥Abar ≃* MulAut (alternatingGroup (Fin 6))) :
    Nat.card ↥(derivedIn Abar) = 360 := by
  obtain ⟨eJ⟩ := s8_J_equiv Abar e
  rw [Nat.card_congr eJ.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem commutator_eq_self_of_simple {J : Subgroup G} (hJs : IsSimpleGroup ↥J)
    (hna : ∃ a b : ↥J, a * b ≠ b * a) : ⁅J, J⁆ = J := by
  have h1 : commutator ↥J = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥J) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      apply hab
      have hmem : ⁅a, b⁆ ∈ commutator ↥J :=
        Subgroup.commutator_mem_commutator (mem_top a) (mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_def] at hmem
      calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
        _ = b * a := by rw [hmem, one_mul]
    · exact h
  have h2 := Subgroup.map_commutator (⊤ : Subgroup ↥J) ⊤ J.subtype
  have hm : (⊤ : Subgroup ↥J).map J.subtype = J := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← _root_.commutator_def, h1, hm] at h2
  exact h2.symm

end J

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
