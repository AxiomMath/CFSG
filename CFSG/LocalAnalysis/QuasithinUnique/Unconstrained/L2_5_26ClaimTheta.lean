module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.QuasithinUnique.Claim2526

open Equiv

theorem conjNormal_bijective8 :
    Function.Bijective (MulAut.conjNormal :
      Equiv.Perm (Fin 8) →* MulAut (alternatingGroup (Fin 8))) :=
  CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8 (by norm_num) (by norm_num)

@[expose] noncomputable def conjEquiv8 :
    Equiv.Perm (Fin 8) ≃* MulAut (alternatingGroup (Fin 8)) :=
  MulEquiv.ofBijective _ conjNormal_bijective8

variable {G : Type*} [Group G]

@[expose] noncomputable def thetaHom (L : Subgroup G) (φ : ↥L ≃* alternatingGroup (Fin 8)) :
    ↥(Subgroup.normalizer (L : Set G)) →* Equiv.Perm (Fin 8) :=
  (conjEquiv8.symm : MulAut (alternatingGroup (Fin 8)) ≃* Equiv.Perm (Fin 8)).toMonoidHom.comp
    ((MulAut.congr φ).toMonoidHom.comp L.normalizerMonoidHom)

theorem conjNormal_thetaHom (L : Subgroup G) (φ : ↥L ≃* alternatingGroup (Fin 8))
    (n : ↥(Subgroup.normalizer (L : Set G))) :
    MulAut.conjNormal (thetaHom L φ n) = MulAut.congr φ (L.normalizerMonoidHom n) := by
  have h : conjEquiv8 (conjEquiv8.symm (MulAut.congr φ (L.normalizerMonoidHom n))) =
      MulAut.congr φ (L.normalizerMonoidHom n) := conjEquiv8.apply_symm_apply _
  exact h

theorem theta_spec (L : Subgroup G) (φ : ↥L ≃* alternatingGroup (Fin 8))
    (n : ↥(Subgroup.normalizer (L : Set G))) (k : ↥L) :
    ((φ (L.normalizerMonoidHom n k) : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) =
      thetaHom L φ n * (φ k : Equiv.Perm (Fin 8)) * (thetaHom L φ n)⁻¹ := by
  have h := congrArg (fun α : MulAut (alternatingGroup (Fin 8)) => ((α (φ k) :
    alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8))) (conjNormal_thetaHom L φ n)
  simp only [MulAut.conjNormal_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at h
  exact h.symm

theorem theta_unique (L : Subgroup G) (φ : ↥L ≃* alternatingGroup (Fin 8))
    (n : ↥(Subgroup.normalizer (L : Set G))) {σ : Equiv.Perm (Fin 8)}
    (h : ∀ k : ↥L, ((φ (L.normalizerMonoidHom n k) : alternatingGroup (Fin 8)) :
      Equiv.Perm (Fin 8)) = σ * (φ k : Equiv.Perm (Fin 8)) * σ⁻¹) :
    σ = thetaHom L φ n := by
  apply conjNormal_bijective8.1
  rw [conjNormal_thetaHom]
  apply MulEquiv.ext
  intro a
  obtain ⟨k, rfl⟩ := φ.surjective a
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply]
  exact (h k).symm

theorem theta_apply_of_mem (L : Subgroup G) (φ : ↥L ≃* alternatingGroup (Fin 8)) (k : ↥L) :
    thetaHom L φ ⟨(k : G), Subgroup.le_normalizer k.2⟩ = (φ k : Equiv.Perm (Fin 8)) := by
  symm
  apply theta_unique
  intro k'
  have : (L.normalizerMonoidHom ⟨(k : G), Subgroup.le_normalizer k.2⟩ k') = k * k' * k⁻¹ := by
    apply Subtype.ext
    simp
  rw [this, map_mul, map_mul, map_inv]
  rfl

theorem theta_eq_one_iff (L : Subgroup G) (φ : ↥L ≃* alternatingGroup (Fin 8))
    (n : ↥(Subgroup.normalizer (L : Set G))) :
    thetaHom L φ n = 1 ↔ ∀ k ∈ L, (n : G) * k = k * (n : G) := by
  constructor
  · intro h k hk
    have h1 := theta_spec L φ n ⟨k, hk⟩
    rw [h] at h1
    simp only [inv_one, mul_one, one_mul] at h1
    have h2 : φ (L.normalizerMonoidHom n ⟨k, hk⟩) = φ ⟨k, hk⟩ := Subtype.ext h1
    have h3 := φ.injective h2
    have h4 : ((L.normalizerMonoidHom n ⟨k, hk⟩ : ↥L) : G) = k := congrArg Subtype.val h3
    have h5 : ((L.normalizerMonoidHom n ⟨k, hk⟩ : ↥L) : G) = (n : G) * k * (n : G)⁻¹ := by simp
    rw [h5] at h4
    calc (n : G) * k = (n : G) * k * (n : G)⁻¹ * n := by group
      _ = k * n := by rw [h4]
  · intro h
    symm
    apply theta_unique
    intro k
    have h1 : ((L.normalizerMonoidHom n k : ↥L) : G) = (k : G) := by
      have h5 : ((L.normalizerMonoidHom n k : ↥L) : G) = (n : G) * k * (n : G)⁻¹ := by simp
      rw [h5, h k k.2]
      group
    have h2 : L.normalizerMonoidHom n k = k := Subtype.ext h1
    rw [h2]
    simp

theorem theta_swap (L : Subgroup G) (φ : ↥L ≃* alternatingGroup (Fin 8)) {a b : Fin 8}
    (t : ↥(Subgroup.normalizer (L : Set G))) (ht : (t : G) * t = 1)
    (hind : ∀ y y' : ↥L, (y' : G) = (t : G)⁻¹ * y * t →
      φ y' = (MulAut.conjNormal (Equiv.swap a b) : MulAut (alternatingGroup (Fin 8))) (φ y)) :
    thetaHom L φ t = Equiv.swap a b := by
  symm
  apply theta_unique
  intro k
  have ht' : (t : G)⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hk : ((L.normalizerMonoidHom t k : ↥L) : G) = (t : G)⁻¹ * k * t := by
    have h5 : ((L.normalizerMonoidHom t k : ↥L) : G) = (t : G) * k * (t : G)⁻¹ := by simp
    rw [h5, ht']
  have := hind k (L.normalizerMonoidHom t k) hk
  rw [this, MulAut.conjNormal_apply]

end CFSG.QuasithinUnique.Claim2526
