module

public import CFSG.LocalAnalysis.GL83PartI.I_27_9.Lift
public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace GL83.PiGen

open Equiv Equiv.Perm
open CFSG.ComponentClassification.PerfectAutomorphisms

variable {X : Type*} [Group X] {K A : Subgroup X}

@[expose] noncomputable def actHom (hA : A ≤ Subgroup.normalizer (K : Set X)) :
    A →* MulAut (K ⧸ Subgroup.center K) :=
  (centerQuotientHom K).comp (K.normalizerMonoidHom.comp (Subgroup.inclusion hA))

theorem actHom_mk (hA : A ≤ Subgroup.normalizer (K : Set X)) (a : A) (x : K) :
    ∃ y : K, (y : X) = (a : X) * x * (a : X)⁻¹ ∧
      actHom hA a (QuotientGroup.mk x) = (QuotientGroup.mk y : K ⧸ Subgroup.center K) := by
  refine ⟨K.normalizerMonoidHom (Subgroup.inclusion hA a) x, ?_, ?_⟩
  · rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  · exact onCenterQuotient_apply_mk _ x

@[expose] noncomputable def permHom (hA : A ≤ Subgroup.normalizer (K : Set X)) {n : ℕ} (hn : 5 ≤ n)
    (hn6 : n ≠ 6) (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) :
    A →* Perm (Fin n) :=
  (MulEquiv.ofBijective
    (MulAut.conjNormal : Perm (Fin n) →* MulAut (alternatingGroup (Fin n)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn
      hn6)).symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp (actHom hA))

theorem conjNormal_permHom (hA : A ≤ Subgroup.normalizer (K : Set X)) {n : ℕ} (hn : 5 ≤ n)
    (hn6 : n ≠ 6) (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) (a : A) :
    (MulAut.conjNormal (permHom hA hn hn6 e a) : MulAut (alternatingGroup (Fin n))) =
      MulAut.congr e (actHom hA a) := by
  have := (MulEquiv.ofBijective
    (MulAut.conjNormal : Perm (Fin n) →* MulAut (alternatingGroup (Fin n)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6)).apply_symm_apply
    (MulAut.congr e (actHom hA a))
  exact this

theorem permHom_spec (hA : A ≤ Subgroup.normalizer (K : Set X)) {n : ℕ} (hn : 5 ≤ n)
    (hn6 : n ≠ 6) (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) (a : A) (x : K) :
    ∃ y : K, (y : X) = (a : X) * x * (a : X)⁻¹ ∧
      permHom hA hn hn6 e a * (e (QuotientGroup.mk x) : Perm (Fin n)) *
          (permHom hA hn hn6 e a)⁻¹ = (e (QuotientGroup.mk y) : Perm (Fin n)) := by
  obtain ⟨y, hy, hy'⟩ := actHom_mk hA a x
  refine ⟨y, hy, ?_⟩
  have h := congrArg (fun φ : MulAut (alternatingGroup (Fin n)) =>
    ((φ (e (QuotientGroup.mk x)) : alternatingGroup (Fin n)) : Perm (Fin n)))
    (conjNormal_permHom hA hn hn6 e a)
  simp only [MulAut.conjNormal_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at h
  rw [h, hy']

theorem permHom_eq_one_iff_actHom (hA : A ≤ Subgroup.normalizer (K : Set X)) {n : ℕ}
    (hn : 5 ≤ n) (hn6 : n ≠ 6) (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) (a : A) :
    permHom hA hn hn6 e a = 1 ↔ actHom hA a = 1 := by
  constructor
  · intro h
    have h1 := conjNormal_permHom hA hn hn6 e a
    rw [h, map_one] at h1
    exact (MulAut.congr e).injective (by rw [← h1, map_one])
  · intro h
    show (MulEquiv.ofBijective
      (MulAut.conjNormal : Perm (Fin n) →* MulAut (alternatingGroup (Fin n)))
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6)).symm
      (MulAut.congr e (actHom hA a)) = 1
    rw [h, map_one]
    exact map_one _

theorem actHom_eq_one_iff [Group.IsPerfect K] (hA : A ≤ Subgroup.normalizer (K : Set X))
    (a : A) : actHom hA a = 1 ↔ ∀ x : K, (a : X) * x = x * a := by
  constructor
  · intro h x
    have h1 : K.normalizerMonoidHom (Subgroup.inclusion hA a) = 1 :=
      centerQuotientHom_injective K (by rw [map_one]; exact h)
    have h2 := congrArg (fun φ : MulAut K => ((φ x : K) : X)) h1
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
    have h3 : (a : X) * x * (a : X)⁻¹ = x := h2
    calc (a : X) * x = (a : X) * x * (a : X)⁻¹ * a := by group
      _ = x * a := by rw [h3]
  · intro h
    have h1 : K.normalizerMonoidHom (Subgroup.inclusion hA a) = 1 := by
      refine MulEquiv.ext fun x => Subtype.ext ?_
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      have : (a : X) * x * (a : X)⁻¹ = x := by
        calc (a : X) * x * (a : X)⁻¹ = x * a * (a : X)⁻¹ := by rw [h x]
          _ = x := by group
      exact this
    show centerQuotientHom K (K.normalizerMonoidHom (Subgroup.inclusion hA a)) = 1
    rw [h1, map_one]

theorem permHom_eq_one_iff [Group.IsPerfect K] (hA : A ≤ Subgroup.normalizer (K : Set X)) {n : ℕ}
    (hn : 5 ≤ n) (hn6 : n ≠ 6) (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n)) (a : A) :
    permHom hA hn hn6 e a = 1 ↔ ∀ x : K, (a : X) * x = x * a :=
  (permHom_eq_one_iff_actHom hA hn hn6 e a).trans (actHom_eq_one_iff hA a)

end GL83.PiGen
