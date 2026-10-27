module

public import CFSG.HardMathSupport.Foote.E27.LieThree.SylowQuot
public import CFSG.HardMathSupport.Foote.E27.LieThree.SpModelP
public import CFSG.ClassicalInvolution.Q3.Q3ZAdjSp
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.HardMathSupport.Foote.E27

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)

theorem statedSp_scalar_sq {n : ℕ} (hn : 0 < n) {F : Type} [Field F] (y : StatedSp n F)
    (hy : (y : GL (Fin n ⊕ Fin n) F) ∈ StatedScalars (Fin n ⊕ Fin n) F) : y ^ 2 = 1 := by
  obtain ⟨u, hu⟩ := hy
  have hM : mat n F y = Matrix.diagonal (fun _ => (u : F)) := by
    have : ((y : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
        Matrix.diagonal (fun _ => (u : F)) := by
      rw [← hu]
      ext i j
      simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply, Matrix.one_apply]
    exact this
  have h := congrFun (congrFun (mat_transpose_mul_gram_mul y) (Sum.inl ⟨0, hn⟩))
    (Sum.inr ⟨0, hn⟩)
  rw [hM] at h
  simp [Matrix.mul_diagonal, Matrix.diagonal_mul, gram_apply, par, sgn] at h
  have hu2 : u * u = 1 := Units.ext (by simpa [mul_comm] using h)
  have hy2 : (y : GL (Fin n ⊕ Fin n) F) ^ 2 = 1 := by
    rw [← hu, ← map_pow, pow_two, hu2, map_one]
  exact Subtype.ext hy2

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

theorem E27Config.false_of_psp_three (h : E27Config X K R T z) (hz : z ∈ K) {r : ℕ} (hr : 0 < r)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3)
    (eK : ↥K ≃* StatedProj (StatedSp r F)) (P : Subgroup (SpJP 3 r))
    (hP : Nat.card P = 3 ^ (Nat.card (SpJP 3 r)).factorization 3)
    (hprop : ∀ s ∈ P, orderOf s = 3 → 81 ∣ Nat.card ↥(P ⊓ Subgroup.centralizer ({s} : Set (SpJP 3 r)))) :
    False := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 3 := by rw [← Nat.card_eq_fintype_card]; exact hF
  let e : ZMod 3 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_three hF'
  let ψ : SpJP 3 r →* StatedSp r F :=
    (CFSG.ClassicalInvolution.Q3.Q3Z.spMap (n := r) e.toRingHom).comp
      (CFSG.LieType.Universal.Symplectic.equivStatedSp r (ZMod 3)).toMonoidHom
  have hψinj : Function.Injective ψ :=
    (CFSG.ClassicalInvolution.Q3.Q3Z.spMap_injective _).comp
      (CFSG.LieType.Universal.Symplectic.equivStatedSp r (ZMod 3)).injective
  have hψsurj : Function.Surjective ψ :=
    (CFSG.ClassicalInvolution.Q3.Q3Z.spMap_surjective e).comp
      (CFSG.LieType.Universal.Symplectic.equivStatedSp r (ZMod 3)).surjective
  let π : SpJP 3 r →* ↥K :=
    eK.symm.toMonoidHom.comp ((QuotientGroup.mk' ((StatedScalars _ F).subgroupOf (StatedSp r F))).comp ψ)
  have hπ : Function.Surjective π :=
    eK.symm.surjective.comp ((QuotientGroup.mk'_surjective _).comp hψsurj)
  refine h.false_of_sylow_table_quot hz π hπ ?_ P hP hprop
  intro x hx
  have h1 : QuotientGroup.mk' ((StatedScalars _ F).subgroupOf (StatedSp r F)) (ψ x) = 1 := by
    have : eK.symm (QuotientGroup.mk' ((StatedScalars _ F).subgroupOf (StatedSp r F)) (ψ x)) = 1 := hx
    simpa using this
  have h2 : ψ x ∈ (StatedScalars _ F).subgroupOf (StatedSp r F) := (QuotientGroup.eq_one_iff _).1 h1
  apply hψinj
  rw [map_pow, map_one]
  exact statedSp_scalar_sq hr _ h2

end CFSG.HardMathSupport.Foote.E27
