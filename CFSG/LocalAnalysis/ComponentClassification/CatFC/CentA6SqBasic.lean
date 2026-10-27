module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.PumpBridge
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.FoursInputs

public section

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.EvenSporadicStandard.HSStd (autCentralizer)

theorem a6sq_simple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem a6sq_nonab : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
  by_contra hno
  push Not at hno
  have hs := a6sq_simple
  let _ : CommGroup (alternatingGroup (Fin 6)) :=
    { (inferInstance : Group (alternatingGroup (Fin 6))) with mul_comm := fun a b => hno a b }
  have hp := hs.prime_card
  rw [Nat.card_eq_fintype_card, card_alternatingGroup] at hp
  simp [Nat.factorial] at hp
  norm_num at hp

theorem a6sq_card : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem a6sq_center : center (alternatingGroup (Fin 6)) = ⊥ := by
  haveI := a6sq_simple
  exact CFSG.ComponentClassification.CatLeaf.center_eq_bot_of_simple a6sq_nonab

section Pair

variable {S : Type} [Group S] (τ : MulAut S) {A : Subgroup S}

theorem a6sq_ne_one (hq : CFSG.IsQuasisimple ↥A)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * τ b = τ b * a) : τ ≠ 1 := by
  rintro rfl
  obtain ⟨-, -, a, b, hab⟩ := hq
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (by simpa using hcomm a' a'.2 b' b'.2)

theorem a6sq_card_A [Finite S] (hA6 : Nonempty (↥A ⧸ center ↥A ≃* alternatingGroup (Fin 6))) :
    Nat.card A = 360 * Nat.card (center ↥A) := by
  obtain ⟨e⟩ := hA6
  have h1 : Nat.card (↥A ⧸ center ↥A) = 360 := by
    rw [Nat.card_congr e.toEquiv, a6sq_card]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥A), h1]

theorem a6sq_card_dvd [Finite S]
    (hA6 : Nonempty (↥A ⧸ center ↥A ≃* alternatingGroup (Fin 6)))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * τ b = τ b * a) : 129600 ∣ Nat.card S := by
  classical
  set B : Subgroup S := A.map τ.toMonoidHom with hB
  have hc : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x := by
    rintro x hx _ ⟨b, hb, rfl⟩
    exact hcomm x hx b hb
  obtain ⟨hmul, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hc
  have hBcard : Nat.card B = Nat.card A := Subgroup.card_map_of_injective τ.injective
  have hA360 : Nat.card A = 360 * Nat.card (center ↥A) := a6sq_card_A hA6
  have hinf : A ⊓ B ≤ (center ↥A).map A.subtype := by
    intro x hx
    obtain ⟨hxA, hxB⟩ := Subgroup.mem_inf.1 hx
    exact ⟨⟨x, hxA⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext (hc g g.2 x hxB), rfl⟩
  have hdvd : Nat.card ↥(A ⊓ B) ∣ Nat.card (center ↥A) := by
    have := Subgroup.card_dvd_of_le hinf
    rwa [Subgroup.card_map_of_injective A.subtype_injective] at this
  obtain ⟨m, hm⟩ := hdvd
  have hk : 0 < Nat.card ↥(A ⊓ B) := Nat.card_pos
  have hE : Nat.card ↥(A ⊔ B) = 129600 * Nat.card ↥(A ⊓ B) * m ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_right hk
    rw [hmul, hBcard, hA360, hm]
    ring
  have hS : Nat.card ↥(A ⊔ B) ∣ Nat.card S := Subgroup.card_subgroup_dvd_card _
  exact Dvd.dvd.trans ⟨Nat.card ↥(A ⊓ B) * m ^ 2, by rw [hE]; ring⟩ hS

end Pair

section Derived

variable {S : Type} [Group S] (τ : MulAut S)

theorem a6sq_commutator_component
    (e : ↥(commutator ↥(autCentralizer τ)) ≃* alternatingGroup (Fin 6)) :
    ∃ D : Subgroup ↥(fixedSubgroup τ), IsComponent D ∧ D.Normal ∧
      Nonempty (↥D ≃* alternatingGroup (Fin 6)) ∧
      Nonempty (↥D ⧸ center ↥D ≃* alternatingGroup (Fin 6)) := by
  classical
  have hqC : CFSG.IsQuasisimple ↥(commutator ↥(autCentralizer τ)) := by
    haveI := a6sq_simple
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup a6sq_nonab).1
  let φ : ↥(autCentralizer τ) ≃* ↥(fixedSubgroup τ) :=
    MulEquiv.subgroupCongr (autCentralizer_eq_fixedSubgroup τ)
  let K : Subgroup ↥(autCentralizer τ) := commutator ↥(autCentralizer τ)
  have hKsub : K.IsSubnormal := Subgroup.Normal.isSubnormal inferInstance
  have eD : ↥(K.map φ.toMonoidHom) ≃* alternatingGroup (Fin 6) :=
    (K.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans e
  refine ⟨K.map φ.toMonoidHom, CFSG.LocalCores.isComponent_map_mulEquiv φ ⟨hqC, hKsub⟩,
    Subgroup.Normal.map inferInstance φ.toMonoidHom φ.surjective, ⟨eD⟩, ⟨?_⟩⟩
  exact (quotientCenterEquiv eD).trans
    ((QuotientGroup.quotientMulEquivOfEq a6sq_center).trans QuotientGroup.quotientBot)

theorem a6sq_dvd_card_fixed [Finite S]
    (e : ↥(commutator ↥(autCentralizer τ)) ≃* alternatingGroup (Fin 6)) :
    360 ∣ Nat.card (fixedSubgroup τ) := by
  have h1 : Nat.card ↥(commutator ↥(autCentralizer τ)) = 360 := by
    rw [Nat.card_congr e.toEquiv, a6sq_card]
  have h2 := Subgroup.card_subgroup_dvd_card (commutator ↥(autCentralizer τ))
  rw [h1] at h2
  have h3 : Nat.card ↥(autCentralizer τ) = Nat.card (fixedSubgroup τ) := by
    rw [autCentralizer_eq_fixedSubgroup]
  rwa [h3] at h2

end Derived

end CFSG.ComponentClassification.CatFC
