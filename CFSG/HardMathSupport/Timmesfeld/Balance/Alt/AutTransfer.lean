module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.HardMathSupport.Timmesfeld.Balance.Alt

open Equiv
open scoped commutatorElement

theorem mulAut_eq_one_of_central {P : Type*} [Group P] [Group.IsPerfect P] (φ : MulAut P)
    (h : ∀ x, x⁻¹ * φ x ∈ Subgroup.center P) : φ = 1 := by
  let f : P →* P :=
    { toFun := fun x => x⁻¹ * φ x
      map_one' := by simp
      map_mul' := by
        intro x y
        have hx := Subgroup.mem_center_iff.1 (h x) y⁻¹
        have : (x * y)⁻¹ * φ (x * y) = y⁻¹ * (x⁻¹ * φ x) * φ y := by
          simp [mul_assoc]
        rw [this, hx]
        simp [mul_assoc] }
  have hker : ∀ a b : P, ⁅a, b⁆ ∈ f.ker := by
    intro a b
    have hb : f a * f b = f b * f a := (Subgroup.mem_center_iff.1 (h b)) (f a)
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact hb
  have htop : f.ker = ⊤ := by
    refine eq_top_iff.2 ?_
    have h1 : (commutator P) = ⊤ := Group.IsPerfect.commutator_eq_top
    rw [← h1, commutator_def]
    exact Subgroup.commutator_le.2 fun a _ b _ => hker a b
  ext x
  show φ x = x
  have hx : f x = 1 := by
    have : x ∈ f.ker := htop ▸ Subgroup.mem_top x
    exact this
  have : x⁻¹ * φ x = 1 := hx
  exact (inv_mul_eq_one.1 this).symm

@[expose] noncomputable def autCenterQuot (P : Type*) [Group P] :
    MulAut P →* MulAut (P ⧸ Subgroup.center P) where
  toFun φ := QuotientGroup.congr (Subgroup.center P) (Subgroup.center P) φ
    (Subgroup.map_center_eq φ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with | _ x => ?_
    simp [QuotientGroup.congr_mk]
  map_mul' := by
    intro φ ψ
    ext x
    induction x using QuotientGroup.induction_on with | _ x => ?_
    simp [QuotientGroup.congr_mk]

theorem autCenterQuot_mk {P : Type*} [Group P] (φ : MulAut P) (x : P) :
    autCenterQuot P φ (QuotientGroup.mk x) = QuotientGroup.mk (φ x) :=
  QuotientGroup.congr_mk _ _ φ (Subgroup.map_center_eq φ) x

theorem autCenterQuot_injective (P : Type*) [Group P] [Group.IsPerfect P] :
    Function.Injective (autCenterQuot P) := by
  rw [injective_iff_map_eq_one]
  intro φ hφ
  refine mulAut_eq_one_of_central φ fun x => ?_
  have h1 : autCenterQuot P φ (QuotientGroup.mk x) = QuotientGroup.mk x := by
    rw [hφ]; rfl
  rw [autCenterQuot_mk] at h1
  exact QuotientGroup.eq.1 h1.symm

theorem exists_embedding_perm {P : Type*} [Group P] [Group.IsPerfect P] {n : ℕ}
    (e : (P ⧸ Subgroup.center P) ≃* alternatingGroup (Fin n))
    (hbij : Function.Bijective
      (MulAut.conjNormal (H := alternatingGroup (Fin n)) :
        Perm (Fin n) →* MulAut (alternatingGroup (Fin n)))) :
    ∃ ι : MulAut P →* Perm (Fin n), Function.Injective ι ∧
      ∀ σ ∈ alternatingGroup (Fin n),
        σ ∈ ((MulAut.conj : P →* MulAut P).range).map ι := by
  let c := MulEquiv.ofBijective _ hbij
  let ι : MulAut P →* Perm (Fin n) :=
    c.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp (autCenterQuot P))
  refine ⟨ι, ?_, ?_⟩
  · intro φ ψ h
    apply autCenterQuot_injective P
    have h2 := c.symm.injective h
    exact (MulAut.congr e).injective h2
  · intro σ hσ
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e.symm ⟨σ, hσ⟩)
    have hxe : e (QuotientGroup.mk x) = ⟨σ, hσ⟩ := by rw [hx]; simp
    have key : (MulAut.congr e) (autCenterQuot P (MulAut.conj x)) = c σ := by
      refine MulEquiv.ext fun y => ?_
      obtain ⟨z, hz⟩ := QuotientGroup.mk_surjective (e.symm y)
      have h1 : (MulAut.congr e) (autCenterQuot P (MulAut.conj x)) y =
          ⟨σ, hσ⟩ * y * ⟨σ, hσ⟩⁻¹ := by
        simp only [MulAut.congr_apply, MulEquiv.trans_apply]
        rw [← hz, autCenterQuot_mk]
        have : (QuotientGroup.mk (MulAut.conj x z) : P ⧸ Subgroup.center P) =
            QuotientGroup.mk x * QuotientGroup.mk z * (QuotientGroup.mk x)⁻¹ := by
          simp [MulAut.conj_apply]
        rw [this, map_mul, map_mul, map_inv, hxe, hz]
        simp
      rw [h1]
      show _ = (MulAut.conjNormal σ) y
      apply Subtype.ext
      simp [MulAut.conjNormal_apply]
    refine ⟨MulAut.conj x, ⟨x, rfl⟩, ?_⟩
    show c.symm ((MulAut.congr e) (autCenterQuot P (MulAut.conj x))) = σ
    rw [key]
    exact c.symm_apply_apply σ

end CFSG.HardMathSupport.Timmesfeld.Balance.Alt
