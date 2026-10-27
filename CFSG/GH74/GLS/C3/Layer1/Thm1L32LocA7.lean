module

public import CFSG.GH74.GLS.C3.Layer1.Thm1L32LocBase
public import CFSG.GH74.GLS.IVK.A7.Core
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndSix

public section

open Subgroup Equiv Equiv.Perm CFSG.GH74.GLS.C3.Layer1.Thm1L32.Loc
open scoped commutatorElement

namespace CFSG.GH74.GLS.C3.Layer1.Thm1L32

theorem a7_fixed_classification {Z : Type} [Group Z] [Finite Z] (L : Subgroup Z)
    (e7 : ↥L ≃* alternatingGroup (Fin 7)) (s : Z) (hs2 : s * s = 1)
    (hsL : ∀ l ∈ L, s * l * s⁻¹ ∈ L) (hmove : ∃ l ∈ L, s * l * s⁻¹ ≠ l)
    (P : Subgroup Z) (hPL : P ≤ L) (hP : ⁅P, P⁆ = P) (hP1 : P ≠ ⊥)
    (hPs : ∀ x ∈ P, s * x * s⁻¹ = x)
    (hsub : (P.subgroupOf (centralizer ({s} : Set Z))).IsSubnormal) :
    Nonempty (↥P ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨σ, P', -, hσ2, hσ1, ⟨eP⟩, hP'1, hP', hfix, -⟩ :=
    local_data L s hs2 hsL hmove P hPL hP hP1 hPs hsub
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)
  obtain ⟨τ, hτ⟩ := hbij.2 (MulAut.congr e7 σ)
  have hτfun : ∀ k : ↥L, τ * ((e7 k : alternatingGroup (Fin 7)) : Perm (Fin 7)) * τ⁻¹ =
      ((e7 (σ k) : alternatingGroup (Fin 7)) : Perm (Fin 7)) := by
    intro k
    have h1 := MulAut.conjNormal_apply (H := alternatingGroup (Fin 7)) τ (e7 k)
    have h2 : (MulAut.conjNormal (H := alternatingGroup (Fin 7)) τ) (e7 k) = e7 (σ k) := by
      have : (MulAut.conjNormal (H := alternatingGroup (Fin 7)) τ) (e7 k) =
          (MulAut.congr e7 σ) (e7 k) := by rw [hτ]
      rw [this]
      simp [MulAut.congr_apply]
    rw [h2] at h1
    exact h1.symm
  have hττ : τ * τ = 1 := by
    apply hbij.1
    rw [map_mul, hτ, map_one, ← map_mul, hσ2, map_one]
  have hτ1 : τ ≠ 1 := by
    intro h
    apply hσ1
    apply (MulAut.congr e7).injective
    rw [← hτ, h, map_one, map_one]
  have hτ2 : τ ^ 2 = 1 := by rw [pow_two]; exact hττ
  let α : ↥P' →* Perm (Fin 7) :=
    (alternatingGroup (Fin 7)).subtype.comp (e7.toMonoidHom.comp P'.subtype)
  have hαinj : Function.Injective α := by
    intro a b hab
    apply Subtype.ext
    apply e7.injective
    exact Subtype.ext hab
  have hαc : ∀ x : ↥P', α x * τ = τ * α x := by
    intro x
    have h1 := hτfun (x : ↥L)
    rw [hfix x x.2] at h1
    show ((e7 (x : ↥L) : alternatingGroup (Fin 7)) : Perm (Fin 7)) * τ =
      τ * ((e7 (x : ↥L) : alternatingGroup (Fin 7)) : Perm (Fin 7))
    calc ((e7 (x : ↥L) : alternatingGroup (Fin 7)) : Perm (Fin 7)) * τ
        = (τ * ((e7 (x : ↥L) : alternatingGroup (Fin 7)) : Perm (Fin 7)) * τ⁻¹) * τ := by
          rw [h1]
      _ = τ * ((e7 (x : ↥L) : alternatingGroup (Fin 7)) : Perm (Fin 7)) := by group
  let C : Subgroup (Perm (Fin 7)) :=
    centralizer ({τ} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7)
  let αC : ↥P' →* ↥C := α.codRestrict C (fun x =>
    ⟨mem_centralizer_singleton_iff.2 (hαc x), (e7 (x : ↥L)).2⟩)
  have hαCinj : Function.Injective αC :=
    Function.Injective.of_comp (f := C.subtype) (show Function.Injective (C.subtype ∘ αC) from hαinj)
  have : Group.IsPerfect ↥P' := Subgroup.isPerfect_iff.2 hP'
  have : Nontrivial ↥P' := (Subgroup.nontrivial_iff_ne_bot P').2 hP'1
  rcases IVK.A7.involution_cycleType τ hτ2 hτ1 with hct | hct | hct
  ·
    obtain ⟨e5⟩ := IVK.A7.centralizer_A7_swap_equiv (Equiv.Perm.isSwap_iff_cycleType.mpr hct)
    let β : ↥P' →* Perm (Fin 5) := e5.toMonoidHom.comp αC
    have hβ : Function.Injective β := e5.injective.comp hαCinj
    have : Group.IsPerfect ↥β.range := Group.IsPerfect.range β
    have hne : β.range ≠ ⊥ := by
      intro h
      obtain ⟨x, hx⟩ := exists_ne (1 : ↥P')
      apply hx
      apply hβ
      have : β x ∈ β.range := ⟨x, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      rw [this, map_one]
    have hR := CFSG.RankThree.PartTwo.Sec4.Census.perfect_perm_five
      (L := β.range) inferInstance hne
    exact ⟨eP.trans ((MonoidHom.ofInjective hβ).trans (MulEquiv.subgroupCongr hR))⟩
  · exfalso
    have hcard := IVK.A7.card_centralizer_A7_two_two hct hτ2 hτ1
    have hsolv : Group.IsSolvable ↥C := isSolvable_of_card_two_pow_mul_three_pow
      (a := 3) (b := 1) (by rw [show C = _ from rfl, hcard]; norm_num)
    have : Group.IsSolvable ↥P' := Group.isSolvable_of_isSolvable_injective (f := αC) hαCinj
    exact Group.IsPerfect.not_isSolvable ↥P' inferInstance
  · exfalso
    have hcard := IVK.A7.card_centralizer_A7_two_two_two hct hτ2 hτ1
    have hsolv : Group.IsSolvable ↥C := isSolvable_of_card_two_pow_mul_three_pow
      (a := 3) (b := 1) (by rw [show C = _ from rfl, hcard]; norm_num)
    have : Group.IsSolvable ↥P' := Group.isSolvable_of_isSolvable_injective (f := αC) hαCinj
    exact Group.IsPerfect.not_isSolvable ↥P' inferInstance

end CFSG.GH74.GLS.C3.Layer1.Thm1L32
