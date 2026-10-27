module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModDBase
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128CentPsi

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] {V : Subgroup G}

namespace AddCoord

@[expose] noncomputable def s8dPsiM (K : AddCoord V) : S8P ≃* ↥V where
  toEquiv := Multiplicative.toAdd.trans K.Ψ
  map_mul' a b := K.add (Multiplicative.toAdd a) (Multiplicative.toAdd b)

@[expose] noncomputable def s8dKap (K : AddCoord V) : MulAut ↥V ≃* S8A where
  toFun c := K.s8dPsiM.trans (c.trans K.s8dPsiM.symm)
  invFun f := K.s8dPsiM.symm.trans (f.trans K.s8dPsiM)
  left_inv c := MulEquiv.ext fun v => by simp
  right_inv f := MulEquiv.ext fun p => by simp
  map_mul' c c' := MulEquiv.ext fun p => by simp

theorem s8dAp_kap (K : AddCoord V) (c : MulAut ↥V) (p : EvW × EvW) :
    s8dAp (K.s8dKap c) p = K.Ψ.symm (c (K.Ψ p)) := rfl

theorem s8dKap_spec (K : AddCoord V) (c : MulAut ↥V) (p : EvW × EvW) :
    K.Ψ (s8dAp (K.s8dKap c) p) = c (K.Ψ p) := by
  rw [s8dAp_kap]
  exact K.Ψ.apply_symm_apply _

theorem s8dKap_eq (K : AddCoord V) {c : MulAut ↥V} {f : S8A}
    (h : ∀ p : EvW × EvW, c (K.Ψ p) = K.Ψ (s8dAp f p)) : K.s8dKap c = f :=
  s8d_ext fun p => K.Ψ.injective (by rw [K.s8dKap_spec, h])

end AddCoord

theorem s8d_kap_autIn {X : Subgroup G} (K : AddCoord V)
    (σ : ↥X ≃* ↥(alternatingGroup (Fin 5)))
    (hK : ∀ (x : ↥X) (p : EvW × EvW),
      ((K.Ψ (s8dAp (s8dDiag (σ x : Equiv.Perm (Fin 5))) p) : ↥V) : G) =
        (x : G) * (K.Ψ p : G) * (x : G)⁻¹)
    {Z : Subgroup (MulAut ↥V)} (hZ : autIn X V ≤ Z) (a : ↥(alternatingGroup (Fin 5))) :
    s8dDiag a ∈ Z.map K.s8dKap.toMonoidHom := by
  have hmapV : ∀ x : ↥X, ∀ v ∈ V, (x : G) * v * (x : G)⁻¹ ∈ V := by
    intro x v hv
    obtain ⟨q, hq⟩ := K.Ψ.surjective ⟨v, hv⟩
    have h := hK x q
    rw [hq] at h
    rw [← h]
    exact (K.Ψ (s8dAp (s8dDiag (σ x : Equiv.Perm (Fin 5))) q)).2
  set x : ↥X := σ.symm a with hx
  have hN : (x : G) ∈ normalizer (V : Set G) := by
    rw [mem_normalizer_iff]
    intro v
    refine ⟨fun hv => hmapV x v hv, fun hv => ?_⟩
    have := hmapV x⁻¹ _ hv
    simpa [mul_assoc] using this
  set y : MulAut ↥V := V.normalizerMonoidHom ⟨(x : G), hN⟩ with hy
  have hyZ : y ∈ Z :=
    hZ (Subgroup.mem_map.mpr ⟨⟨(x : G), hN⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩)
  have hσx : σ x = a := by rw [hx, MulEquiv.apply_symm_apply]
  refine Subgroup.mem_map.mpr ⟨y, hyZ, K.s8dKap_eq fun p => Subtype.ext ?_⟩
  show (x : G) * (K.Ψ p : G) * (x : G)⁻¹ = _
  rw [← hK x p, hσx]

end CFSG.OddStandard.SmallF3.Omega
