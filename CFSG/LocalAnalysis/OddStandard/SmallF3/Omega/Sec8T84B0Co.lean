module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FPConj

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace T84Co

open Matrix

variable {G : Type} [Group G] {B : Subgroup G}

@[expose] def ActsAs (e : ↥B ≃* Multiplicative (Fin 4 → ZMod 2)) (h : MulAut ↥B)
    (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Prop :=
  ∀ b : ↥B, Multiplicative.toAdd (e (h b)) = M *ᵥ Multiplicative.toAdd (e b)

theorem ActsAs.ext {e : ↥B ≃* Multiplicative (Fin 4 → ZMod 2)} {h h' : MulAut ↥B}
    {M : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hh : ActsAs e h M) (hh' : ActsAs e h' M) : h = h' := by
  refine MulEquiv.ext fun b => ?_
  apply e.injective
  apply Multiplicative.toAdd.injective
  rw [hh b, hh' b]

theorem ActsAs.congr {e : ↥B ≃* Multiplicative (Fin 4 → ZMod 2)} {h : MulAut ↥B}
    {M M' : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hh : ActsAs e h M) (hM : M = M') :
    ActsAs e h M' := hM ▸ hh

theorem ActsAs.matrix_eq {e : ↥B ≃* Multiplicative (Fin 4 → ZMod 2)} {h : MulAut ↥B}
    {M M' : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hh : ActsAs e h M) (hh' : ActsAs e h M') :
    M = M' := by
  have hv : ∀ v : Fin 4 → ZMod 2, M *ᵥ v = M' *ᵥ v := by
    intro v
    obtain ⟨b, hb⟩ := e.surjective (Multiplicative.ofAdd v)
    have hb' : Multiplicative.toAdd (e b) = v := by rw [hb]; rfl
    rw [← hb', ← hh b, ← hh' b]
  exact Matrix.toLin'.injective (LinearMap.ext fun v => by simpa using hv v)

theorem ActsAs.mul {e : ↥B ≃* Multiplicative (Fin 4 → ZMod 2)} {h h' : MulAut ↥B}
    {M M' : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hh : ActsAs e h M) (hh' : ActsAs e h' M') :
    ActsAs e (h * h') (M * M') := by
  intro b
  rw [MulAut.mul_apply, hh, hh', Matrix.mulVec_mulVec]

theorem actsAs_theta (e : ↥B ≃* Multiplicative (Fin 4 → ZMod 2)) (h : MulAut ↥B) :
    ActsAs e h ((CFSG.SectionRank.Ccomm.elemAutEquivGL e h : GL (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) :=
  fun b => (CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec e h b).symm

theorem exists_actsAs_rho
    (e : ↥B ≃* Multiplicative (Fin 4 → ZMod 2)) (p : Equiv.Perm (Fin 6)) :
    ∃ g : MulAut ↥B, ActsAs e g (Certificates.Asc82NormA6.rho p) := by
  refine ⟨(CFSG.SectionRank.Ccomm.elemAutEquivGL e).symm
    (sec8t84RhoGL Certificates.certificate442267 p), (actsAs_theta e _).congr ?_⟩
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem actsAs_one (e : ↥B ≃* Multiplicative (Fin 4 → ZMod 2)) :
    ActsAs e (1 : MulAut ↥B) 1 := by
  intro b
  simp

theorem card_fix_eq {e : ↥B ≃* Multiplicative (Fin 4 → ZMod 2)} {h : MulAut ↥B}
    {M : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hh : ActsAs e h M) :
    Nat.card {b : ↥B // h b = b} =
      (Finset.univ.filter fun v : Fin 4 → ZMod 2 => M *ᵥ v = v).card := by
  have hequiv : {b : ↥B // h b = b} ≃ {v : Fin 4 → ZMod 2 // M *ᵥ v = v} :=
    Equiv.subtypeEquiv (e.toEquiv.trans Multiplicative.toAdd) fun b => by
      change h b = b ↔ M *ᵥ Multiplicative.toAdd (e b) = Multiplicative.toAdd (e b)
      rw [← hh b, Multiplicative.toAdd.injective.eq_iff, e.injective.eq_iff]
  rw [Nat.card_congr hequiv, Nat.card_eq_fintype_card, Fintype.card_subtype]

end T84Co

end CFSG.OddStandard.SmallF3.Omega
