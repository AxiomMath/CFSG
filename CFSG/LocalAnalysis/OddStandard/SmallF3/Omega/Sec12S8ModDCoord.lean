module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModDBase
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128CentPsi
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private theorem s8d_permVec_add (σ : Equiv.Perm (Fin 5)) (v w : Fin 5 → ZMod 2) :
    permVec σ (v + w) = permVec σ v + permVec σ w := rfl

private theorem s8d_permVec_zero (σ : Equiv.Perm (Fin 5)) :
    permVec σ (0 : Fin 5 → ZMod 2) = 0 := rfl

private theorem s8d_permVec_conj (π σ : Equiv.Perm (Fin 5)) (v : Fin 5 → ZMod 2) :
    permVec (π * σ * π⁻¹) (permVec π v) = permVec π (permVec σ v) := by
  rw [permVec_mul]
  rw [← permVec_mul (π⁻¹) π v, inv_mul_cancel, permVec_one]
  rw [permVec_mul]

private theorem s8d_permVec_conj' (π σ : Equiv.Perm (Fin 5)) (v : Fin 5 → ZMod 2) :
    permVec σ (permVec π v) = permVec π (permVec (π⁻¹ * σ * π) v) := by
  have h := s8d_permVec_conj π (π⁻¹ * σ * π) v
  rwa [show π * (π⁻¹ * σ * π) * π⁻¹ = σ from by group] at h

private theorem s8d_act_unique {V1 X : Subgroup G} {φ : (Fin 5 → ZMod 2) → G}
    (hc : Sec127NatCoord V1 X φ) (h : G)
    {σ τ : ↥(alternatingGroup (Fin 5))}
    (hσ : ∀ v, IsEvenVec v → h * φ v * h⁻¹ = φ (permVec (σ : Equiv.Perm (Fin 5)) v))
    (hτ : ∀ v, IsEvenVec v → h * φ v * h⁻¹ = φ (permVec (τ : Equiv.Perm (Fin 5)) v)) :
    σ = τ := by
  apply Subtype.ext
  refine permVec_injective_five fun v hv => ?_
  exact (hc.eq_iff (sec127_isEvenVec_permVec _ hv) (sec127_isEvenVec_permVec _ hv)).mp
    ((hσ v hv).symm.trans (hτ v hv))

theorem s8d_natIso {V1 X : Subgroup G} {φ : (Fin 5 → ZMod 2) → G} (hc : Sec127NatCoord V1 X φ)
    (hA5 : Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5)))) :
    ∃ σ : ↥X ≃* ↥(alternatingGroup (Fin 5)), ∀ (h : ↥X) (v : Fin 5 → ZMod 2), IsEvenVec v →
      (h : G) * φ v * (h : G)⁻¹ = φ (permVec (σ h : Equiv.Perm (Fin 5)) v) := by
  classical
  choose σ0 hσ0mem hσ0 using fun h : ↥X => hc.act (h : G) h.2
  let s : ↥X → ↥(alternatingGroup (Fin 5)) := fun h => ⟨σ0 h, hσ0mem h⟩
  have hs : ∀ (h : ↥X) (v : Fin 5 → ZMod 2), IsEvenVec v →
      (h : G) * φ v * (h : G)⁻¹ = φ (permVec (s h : Equiv.Perm (Fin 5)) v) :=
    fun h v hv => hσ0 h v hv
  let f : ↥X →* ↥(alternatingGroup (Fin 5)) :=
    { toFun := s
      map_one' := by
        refine s8d_act_unique hc 1 ?_ ?_
        · intro v hv
          exact hs 1 v hv
        · intro v hv
          rw [show ((1 : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) = 1 from rfl,
            permVec_one]
          group
      map_mul' := fun a b => by
        refine s8d_act_unique hc ((a : G) * (b : G)) ?_ ?_
        · intro v hv
          exact hs (a * b) v hv
        · intro v hv
          have hv' : IsEvenVec (permVec (s b : Equiv.Perm (Fin 5)) v) :=
            sec127_isEvenVec_permVec _ hv
          rw [show ((s a * s b : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) =
            (s a : Equiv.Perm (Fin 5)) * (s b : Equiv.Perm (Fin 5)) from rfl, permVec_mul]
          calc (a : G) * (b : G) * φ v * ((a : G) * (b : G))⁻¹
              = (a : G) * ((b : G) * φ v * (b : G)⁻¹) * (a : G)⁻¹ := by group
            _ = (a : G) * φ (permVec (s b : Equiv.Perm (Fin 5)) v) * (a : G)⁻¹ := by
                  rw [hs b v hv]
            _ = φ (permVec (s a : Equiv.Perm (Fin 5))
                  (permVec (s b : Equiv.Perm (Fin 5)) v)) := hs a _ hv' }
  have hsurj : Function.Surjective f := by
    intro σ
    obtain ⟨h, hh, hhσ⟩ := hc.onto (σ : Equiv.Perm (Fin 5)) σ.2
    refine ⟨⟨h, hh⟩, ?_⟩
    refine s8d_act_unique hc h ?_ ?_
    · intro v hv
      exact hs ⟨h, hh⟩ v hv
    · intro v hv
      exact hhσ v hv
  obtain ⟨e⟩ := hA5
  haveI : Finite ↥X :=
    Finite.of_injective (e.toEquiv : ↥X → ↥(alternatingGroup (Fin 5))) e.toEquiv.injective
  have hbij : Function.Bijective f :=
    hsurj.bijective_of_nat_card_le (le_of_eq (Nat.card_congr e.toEquiv))
  exact ⟨MulEquiv.ofBijective f hbij, fun h v hv => hs h v hv⟩

theorem s8d_natCoord_twist {V1 X : Subgroup G} {φ : (Fin 5 → ZMod 2) → G}
    (hc : Sec127NatCoord V1 X φ) (π : Equiv.Perm (Fin 5)) :
    Sec127NatCoord V1 X (fun v => φ (permVec π v)) := by
  refine ⟨hc.normalizes, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact hc.mem _ (sec127_isEvenVec_permVec π hv)
  · intro v w hv hw
    rw [s8d_permVec_add]
    exact hc.mul _ _ (sec127_isEvenVec_permVec π hv) (sec127_isEvenVec_permVec π hw)
  · intro v hv h1
    have h0 : permVec π v = 0 := hc.inj _ (sec127_isEvenVec_permVec π hv) h1
    have h2 := congrArg (permVec π⁻¹) h0
    rw [s8d_permVec_zero, ← permVec_mul, inv_mul_cancel, permVec_one] at h2
    exact h2
  · intro x hx
    obtain ⟨v, hv, hφv⟩ := hc.surj x hx
    refine ⟨permVec π⁻¹ v, sec127_isEvenVec_permVec π⁻¹ hv, ?_⟩
    rw [show permVec π (permVec π⁻¹ v) = v from by
      rw [← permVec_mul, mul_inv_cancel, permVec_one], hφv]
  · intro h hh
    obtain ⟨σ, hσ, hσh⟩ := hc.act h hh
    refine ⟨π⁻¹ * σ * π,
      (inferInstance : (alternatingGroup (Fin 5)).Normal).conj_mem σ hσ π⁻¹, fun v hv => ?_⟩
    have hv' := sec127_isEvenVec_permVec π hv
    have h1 := hσh (permVec π v) hv'
    rw [s8d_permVec_conj' π σ v] at h1
    exact h1
  · intro σ hσ
    obtain ⟨h, hh, hhσ⟩ :=
      hc.onto (π * σ * π⁻¹)
        ((inferInstance : (alternatingGroup (Fin 5)).Normal).conj_mem σ hσ π)
    refine ⟨h, hh, fun v hv => ?_⟩
    have hv' := sec127_isEvenVec_permVec π hv
    have h1 := hhσ (permVec π v) hv'
    rw [s8d_permVec_conj π σ v] at h1
    exact h1

theorem s8d_coord {V X V1 V2 : Subgroup G} (hV : IsElemAb2 V 8) (hsup : V1 ⊔ V2 = V)
    (hinf : V1 ⊓ V2 = ⊥) (hA5 : Nonempty (↥X ≃* ↥(alternatingGroup (Fin 5))))
    (h1 : IsNatModA5 V1 ⊥ X) (h2 : IsNatModA5 V2 ⊥ X) :
    ∃ (K : AddCoord V) (σ : ↥X ≃* ↥(alternatingGroup (Fin 5))), ∀ (x : ↥X) (p : EvW × EvW),
      ((K.Ψ (s8dAp (s8dDiag (σ x : Equiv.Perm (Fin 5))) p) : ↥V) : G) =
        (x : G) * (K.Ψ p : G) * (x : G)⁻¹ := by
  classical
  obtain ⟨φ₁, hc1⟩ := sec127_natCoord_of h1
  obtain ⟨φ₂, hc2⟩ := sec127_natCoord_of h2
  obtain ⟨σ₁, hσ₁⟩ := s8d_natIso hc1 hA5
  obtain ⟨σ₂, hσ₂⟩ := s8d_natIso hc2 hA5
  obtain ⟨π, hπ⟩ :=
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl (by decide)).2
      (σ₁.symm.trans σ₂ : MulAut ↥(alternatingGroup (Fin 5)))
  have hc2' : Sec127NatCoord V2 X (fun v => φ₂ (permVec π v)) := s8d_natCoord_twist hc2 π
  have hcommV : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val
      (hV.1.1.is_comm.comm (⟨x, hx⟩ : ↥V) (⟨y, hy⟩ : ↥V))
  let hd : Sec128Two V V1 V2 X φ₁ (fun v => φ₂ (permVec π v)) :=
    { comm := hcommV, sup := hsup, inf := hinf, c1 := hc1, c2 := hc2' }
  have hσ₂x : ∀ x : ↥X,
      ((σ₂ x : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) =
        π * ((σ₁ x : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) * π⁻¹ := by
    intro x
    have h1 := congrArg (fun f : MulAut ↥(alternatingGroup (Fin 5)) => f (σ₁ x)) hπ
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
    have h2 := congrArg (fun y : ↥(alternatingGroup (Fin 5)) => (y : Equiv.Perm (Fin 5))) h1
    rw [MulAut.conjNormal_apply] at h2
    exact h2.symm
  have hΦ1 : ∀ (x : ↥X) (v : Fin 5 → ZMod 2), IsEvenVec v →
      φ₁ (permVec (σ₁ x : Equiv.Perm (Fin 5)) v) = (x : G) * φ₁ v * (x : G)⁻¹ :=
    fun x v hv => (hσ₁ x v hv).symm
  have hΦ2 : ∀ (x : ↥X) (v : Fin 5 → ZMod 2), IsEvenVec v →
      φ₂ (permVec π (permVec (σ₁ x : Equiv.Perm (Fin 5)) v)) =
        (x : G) * φ₂ (permVec π v) * (x : G)⁻¹ := by
    intro x v hv
    have hv' : IsEvenVec (permVec π v) := sec127_isEvenVec_permVec π hv
    have hb := hσ₂ x (permVec π v) hv'
    have h2 : permVec (σ₂ x : Equiv.Perm (Fin 5)) (permVec π v) =
        permVec π (permVec (σ₁ x : Equiv.Perm (Fin 5)) v) := by
      rw [hσ₂x x]
      exact s8d_permVec_conj π (σ₁ x) v
    rw [h2] at hb
    exact hb.symm
  refine ⟨hd.coord, σ₁, fun x p => ?_⟩
  have hΨ : ∀ q : EvW × EvW,
      ((hd.coord.Ψ q : ↥V) : G) = φ₁ q.1.1 * φ₂ (permVec π q.2.1) := by
    intro q
    rw [Sec128Two.coord_Ψ, Sec128Two.psiE_val]
  have hL : ((hd.coord.Ψ (s8dAp (s8dDiag (σ₁ x : Equiv.Perm (Fin 5))) p) : ↥V) : G) =
      φ₁ (permVec (σ₁ x : Equiv.Perm (Fin 5)) p.1.1) *
        φ₂ (permVec π (permVec (σ₁ x : Equiv.Perm (Fin 5)) p.2.1)) := by
    rw [hΨ (s8dAp (s8dDiag (σ₁ x : Equiv.Perm (Fin 5))) p)]
    simp only [s8dAp_diag, permW_val]
  rw [hL, hΨ p, hΦ1 x p.1.1 p.1.2, hΦ2 x p.2.1 p.2.2]
  group

end CFSG.OddStandard.SmallF3.Omega
