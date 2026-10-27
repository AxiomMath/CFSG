module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U6Model
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U6FixedT
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.U6FixedLift

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Open CFSG.HardMathSupport.Dickson.I271 Bal209F4Aux OuterFourInAux
  CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.Burgoyne.U

section Transport

theorem glaPComponent_map_mulEquiv_three {Q Q' : Type} [Group Q] [Group Q'] [Finite Q] (e : Q ≃* Q')
    {X L : Subgroup Q} (hL : GLAPComponent 3 X L) :
    GLAPComponent 3 (X.map e.toMonoidHom) (L.map e.toMonoidHom) := by
  refine glaPComponent_map Nat.prime_three e.toMonoidHom ?_ hL
  rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective, inf_bot_eq, Subgroup.card_bot]
  exact Nat.coprime_one_right 3

theorem uniqComp_of_congr {S P : Type} [Group S] [Group P] [Finite S] (ε : S ≃* P) (φ : MulAut S)
    {T : Subgroup P} (hT : GLAPComponent 3 (fixSubgroup (MulAut.congr ε φ)) T)
    (hu : ∀ L : Subgroup P, GLAPComponent 3 (fixSubgroup (MulAut.congr ε φ)) L → L = T) :
    ∃ T' : Subgroup S, GLAPComponent 3 (fixSubgroup φ) T' ∧
      (∀ L : Subgroup S, GLAPComponent 3 (fixSubgroup φ) L → L = T') ∧ Nonempty (↥T' ≃* ↥T) := by
  haveI : Finite P := Finite.of_equiv S ε.toEquiv
  have hfix : (fixSubgroup φ).map ε.toMonoidHom = fixSubgroup (MulAut.congr ε φ) :=
    (CFSG.HardMathSupport.Dickson.I271.fixSubgroup_congr ε φ).symm
  have hback : ∀ M : Subgroup S, (M.map ε.toMonoidHom).map ε.symm.toMonoidHom = M := fun M => by
    rw [Subgroup.map_map]
    convert Subgroup.map_id M
    ext x
    simp
  refine ⟨T.map ε.symm.toMonoidHom, ?_, ?_,
    ⟨(T.equivMapOfInjective ε.symm.toMonoidHom ε.symm.injective).symm⟩⟩
  · have h := glaPComponent_map_mulEquiv_three ε.symm hT
    rwa [← hfix, hback] at h
  · intro L hL
    have h := glaPComponent_map_mulEquiv_three ε hL
    rw [hfix] at h
    rw [← hu _ h, hback]

end Transport

section FieldOrder

variable {K0 : Type} [Field K0]

theorem orderOf_eq_three_of_uFieldAut_cube (h : UnitaryFieldData 2 3 K0) {σ : K0 ≃+* K0}
    (hσ1 : σ ≠ 1) (h3 : (uFieldAut (n := 6) h (by norm_num) σ) ^ 3 = 1) : orderOf σ = 3 := by
  have hn3 : 3 ≤ 6 := by norm_num
  have hq : ¬((6 : ℕ) = 3 ∧ 2 ^ 3 = 2) := by norm_num
  have h2 := congrArg (uFactor h hn3 hq) h3
  have h4 := uFactor_apply h (n := 6) hn3 hq 1 σ
  rw [map_one, one_mul] at h4
  rw [map_pow, h4, map_one] at h2
  exact orderOf_eq_prime h2 hσ1

end FieldOrder

theorem u6Fixed : FourUFixed IsU6EightIndex (FieldAutU 6) IsU6TwoIndex := by
  intro X _ _ K a hK hLie ha ha3 hF
  obtain ⟨K0, fK0, h, e, σ, γ, hσ1, -, hγ⟩ := U6Bridge.exists_uFieldAut_of_fieldAutU6 hF
  haveI := h.finite
  set φ : MulAut (↥K ⧸ Subgroup.center ↥K) := actHom K ⟨a, ha⟩ with hφ
  have hcube : φ ^ 3 = 1 := by
    rw [hφ, ← map_pow]
    have : (⟨a, ha⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ 3 = 1 := Subtype.ext ha3
    rw [this, map_one]
  have hσord : orderOf σ = 3 := by
    refine orderOf_eq_three_of_uFieldAut_cube h hσ1 ?_
    rw [← hγ, conj_pow, ← map_pow, hcube, map_one, mul_one, mul_inv_cancel]
  obtain ⟨T, hT, hTu, hTq, hTL⟩ := u6_fix_unique_component h hσord
  let ε : (↥K ⧸ Subgroup.center ↥K) ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ 3) K0) :=
    e.trans γ
  have hε : MulAut.congr ε φ = uFieldAut h (by norm_num) σ := by
    rw [← hγ]
    exact MulEquiv.ext fun x => rfl
  rw [← hε] at hT hTu
  obtain ⟨T', hT', hT'u, ⟨eT⟩⟩ := uniqComp_of_congr ε φ hT hTu
  have hT'q : CFSG.Open.IsQuasisimple ↥T' :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eT.symm hTq
  obtain ⟨J₀, hJ₀, hJ₀u, hJ₀q, ⟨eJ⟩⟩ := uniqComp_lift hK.2.2 ha hT' hT'u hT'q
  refine ⟨J₀, hJ₀, hJ₀u, hJ₀q, ?_⟩
  obtain ⟨d, hd, ⟨ψ⟩⟩ := hTL
  exact ⟨d, hd, ⟨(eJ.trans (QuotientGroup.congr _ _ eT (Subgroup.map_center_eq eT))).trans ψ⟩⟩

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
