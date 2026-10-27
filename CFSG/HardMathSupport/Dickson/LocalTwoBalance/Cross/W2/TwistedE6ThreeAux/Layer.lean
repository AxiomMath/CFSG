module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.F4FourAux.Layer

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open Subgroup CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped commutatorElement

variable {C : Type*} [Group C]

theorem map_perfectResidual_mulEquiv' {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (CFSG.perfectResidual A).map e.toMonoidHom = CFSG.perfectResidual B := by
  rw [CFSG.perfectResidual, CFSG.perfectResidual, Subgroup.map_iInf _ e.injective]
  exact iInf_congr fun n => map_derivedSeries_eq e.surjective n

theorem map_inSubgroup_perfectResidual_of_injective {M : Type*} [Group M] (ψ : C →* M)
    (hψ : Function.Injective ψ) (X : Subgroup C) :
    ((CFSG.perfectResidual X).map X.subtype).map ψ =
      (CFSG.perfectResidual (X.map ψ)).map (X.map ψ).subtype := by
  rw [Subgroup.map_map]
  have h : ψ.comp X.subtype = (X.map ψ).subtype.comp (X.equivMapOfInjective ψ hψ).toMonoidHom := by
    ext
    rfl
  rw [h, ← Subgroup.map_map, map_perfectResidual_mulEquiv']

theorem apply_mem_perfectResidual_centralizer {η : MulAut C} {b : C} (hη : η b = b) {r : C}
    (hr : r ∈ (CFSG.perfectResidual (centralizer ({b} : Set C))).map
      (centralizer ({b} : Set C)).subtype) :
    η r ∈ (CFSG.perfectResidual (centralizer ({b} : Set C))).map
      (centralizer ({b} : Set C)).subtype := by
  have hY : (centralizer ({b} : Set C)).map η.toMonoidHom = centralizer ({b} : Set C) := by
    rw [map_centralizer_singleton_apply, hη]
  have h1 := Subgroup.mem_map_of_mem η.toMonoidHom hr
  rw [map_inSubgroup_perfectResidual_of_injective η.toMonoidHom η.injective, hY] at h1
  exact h1

theorem map_perfectResidual_le_self (X : Subgroup C) :
    (CFSG.perfectResidual X).map X.subtype ≤ X := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem isComponent_image_of_stable
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) {H : Subgroup (MulAut C)}
    (hH : innerAut C ≤ H) (b : C) (R : Subgroup C) (hRD : R ≤ centralizer ({b} : Set C))
    (hRst : ∀ η : MulAut C, η b = b → ∀ r ∈ R, η r ∈ R) (hq : CFSG.IsQuasisimple R) :
    (R.map (MulAut.conj : C →* MulAut C)) ≤
        H ⊓ centralizer ({MulAut.conj b} : Set (MulAut C)) ∧
      CFSG.IsComponent
        ((R.map (MulAut.conj : C →* MulAut C)).subgroupOf
            (H ⊓ centralizer ({MulAut.conj b} : Set (MulAut C)))) := by
  set M : Subgroup (MulAut C) := H ⊓ centralizer ({MulAut.conj b} : Set (MulAut C)) with hM
  have hRM : R.map (MulAut.conj : C →* MulAut C) ≤ M := by
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨hH ⟨r, rfl⟩, mem_centralizer_singleton_iff.2 ?_⟩
    have := mem_centralizer_singleton_iff.1 (hRD hr)
    rw [← map_mul, ← map_mul, this]
  refine ⟨hRM, CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((Subgroup.equivMapOfInjective R (MulAut.conj : C →* MulAut C) hinj).trans
      (Subgroup.subgroupOfEquivOfLe hRM).symm) hq, ?_⟩
  have hN : ((R.map (MulAut.conj : C →* MulAut C)).subgroupOf M).Normal := by
    refine ⟨fun n hn m => ?_⟩
    obtain ⟨r, hr, hrn⟩ := hn
    have hmx : (m : MulAut C) b = b := by
      apply hinj
      have h1 := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 m.2).2
      rw [← mul_conj_mul_inv, h1, mul_assoc, mul_inv_cancel, mul_one]
    refine ⟨(m : MulAut C) r, hRst _ hmx r hr, ?_⟩
    change MulAut.conj ((m : MulAut C) r) = (m : MulAut C) * ((n : M) : MulAut C) * (m : MulAut C)⁻¹
    rw [← mul_conj_mul_inv, hrn]
    rfl
  exact hN.isSubnormal

theorem fixes_of_mem_localDeltaIn_of_stable [Finite C] {p : ℕ} (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) {H E : Subgroup (MulAut C)}
    (hH : innerAut C ≤ H) {z : MulAut C} (hz : z ∈ localDeltaIn p H E) {b : C}
    (hbE : MulAut.conj b ∈ E) (hb1 : b ≠ 1) (R : Subgroup C)
    (hRD : R ≤ centralizer ({b} : Set C))
    (hRst : ∀ η : MulAut C, η b = b → ∀ r ∈ R, η r ∈ R) (hq : CFSG.IsQuasisimple R)
    (hpR : ¬ Nat.Coprime p (Nat.card R)) :
    z b = b ∧ ∀ r ∈ R, z r = r := by
  have hb1' : MulAut.conj b ≠ 1 := fun h => hb1 (hinj (by rw [h, map_one]))
  obtain ⟨hTC, hcomp⟩ := isComponent_image_of_stable hinj hH b R hRD hRst hq
  have hpR' : ¬ Nat.Coprime p (Nat.card
      ((R.map (MulAut.conj : C →* MulAut C)).subgroupOf
        (H ⊓ centralizer ({MulAut.conj b} : Set (MulAut C))))) := by
    rwa [Nat.card_congr ((Subgroup.subgroupOfEquivOfLe hTC).toEquiv.trans
      (Subgroup.equivMapOfInjective R (MulAut.conj : C →* MulAut C) hinj).toEquiv.symm)]
  have hle := le_fixSub_of_component hp hinj hz hbE hb1' hTC hcomp hpR
  refine ⟨mem_fixSub_of_commute hinj (commute_of_mem_localDeltaIn hz hbE), fun r hr => ?_⟩
  exact hle hr

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
