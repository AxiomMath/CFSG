module

import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Equiv Equiv.Perm Subgroup

@[expose] def toPerm {K : Type*} [Group K] {m : ℕ}
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin m)) : K →* Perm (Fin m) :=
  (alternatingGroup (Fin m)).subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' (center K)))

theorem toPerm_apply {K : Type*} [Group K] {m : ℕ}
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin m)) (k : K) :
    toPerm e k = (e (QuotientGroup.mk k) : Perm (Fin m)) := rfl

theorem ker_toPerm {K : Type*} [Group K] {m : ℕ}
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin m)) :
    (toPerm e).ker = center K := by
  rw [toPerm,
    MonoidHom.ker_comp_of_injective _ _ (alternatingGroup (Fin m)).subtype_injective,
    MonoidHom.ker_comp_of_injective _ _ e.injective]
  exact QuotientGroup.ker_mk' (Subgroup.center K)

theorem range_toPerm {K : Type*} [Group K] {m : ℕ}
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin m)) :
    (toPerm e).range = alternatingGroup (Fin m) := by
  rw [toPerm, MonoidHom.range_comp, MonoidHom.range_comp,
    MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _),
    Subgroup.map_top, MonoidHom.range_eq_top_of_surjective _ e.surjective,
    Subgroup.map_top, Subgroup.range_subtype]

theorem exists_perm_intertwining {X : Type*} [Group X] {K : Subgroup X} [K.Normal] {t : X}
    (ht : t * t = 1) {m : ℕ} (hm5 : 5 ≤ m) (hm6 : m ≠ 6)
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin m)) :
    ∃ π : Perm (Fin m), π * π = 1 ∧
      ∀ k : K, toPerm e (MulAut.conjNormal t k) = π * toPerm e k * π⁻¹ := by
  classical
  let τ : MulAut K := MulAut.conjNormal t
  let τbar : MulAut (K ⧸ Subgroup.center K) :=
    QuotientGroup.congr (Subgroup.center K) (Subgroup.center K) (τ : K ≃* K)
      (Subgroup.map_center_eq (τ : K ≃* K))
  let τbarA : MulAut (alternatingGroup (Fin m)) := MulAut.congr e τbar
  have hτ2 : τ * τ = 1 := by
    change MulAut.conjNormal t * MulAut.conjNormal t = 1
    rw [← map_mul, ht, map_one]
  have hτbar2 : τbar * τbar = 1 := by
    ext x
    refine QuotientGroup.induction_on x (fun k => ?_)
    have h1 : τbar (QuotientGroup.mk k) = QuotientGroup.mk (τ k) := by
      dsimp only [τbar]
      rw [QuotientGroup.congr_apply]
      rfl
    have h2 : τbar (QuotientGroup.mk (τ k)) = QuotientGroup.mk (τ (τ k)) := by
      dsimp only [τbar]
      rw [QuotientGroup.congr_apply]
      rfl
    have h3 : τ (τ k) = k := by
      have h := congrArg (fun f : MulAut K => f k) hτ2
      simpa only [MulAut.mul_apply, MulAut.one_apply] using h
    simp only [MulAut.mul_apply, MulAut.one_apply, h1, h2, h3]
  have hτbarA2 : τbarA * τbarA = 1 := by
    dsimp only [τbarA]
    rw [← map_mul, hτbar2, map_one]
  obtain ⟨π, hπ⟩ :=
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj m hm5 hm6).2 τbarA
  have hπ2 : π * π = 1 := by
    apply (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj m hm5 hm6).1
    calc MulAut.conjNormal (H := alternatingGroup (Fin m)) (π * π)
        = MulAut.conjNormal (H := alternatingGroup (Fin m)) π *
          MulAut.conjNormal (H := alternatingGroup (Fin m)) π := map_mul _ _ _
      _ = τbarA * τbarA := by rw [hπ]
      _ = 1 := hτbarA2
      _ = MulAut.conjNormal (H := alternatingGroup (Fin m)) 1 := (map_one _).symm
  refine ⟨π, hπ2, fun k => ?_⟩
  have hkey : τbarA (e (QuotientGroup.mk k)) = e (QuotientGroup.mk (τ k)) := by
    have hcongr : MulAut.congr e τbar (e (QuotientGroup.mk k)) =
        e (τbar (QuotientGroup.mk k)) := by
      change (e.symm.trans (τbar.trans e)) (e (QuotientGroup.mk k)) =
        e (τbar (QuotientGroup.mk k))
      simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    dsimp only [τbarA]
    rw [hcongr]
    congr 1
  rw [toPerm_apply, toPerm_apply, ← MulAut.conjNormal_apply, hπ, hkey]

end CFSG.OddStandard.AltStdSec.SwapPartner
