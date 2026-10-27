module

public import CFSG.Adapters.TauCetiExceptional.MinusculeScalar
public import CFSG.Adapters.TauCetiExceptional.TwistedEndgame

public noncomputable section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule MinData

variable {τ : Tag} {D : MinData τ} {n : ℕ} (lab : Fin n ≃ Fin D.d) (L : Type) [Field L]

@[expose] def labMat : Module.End L (Fin D.d →₀ L) ≃ₐ[L] Matrix (Fin n) (Fin n) L :=
  (natMat L).trans (Matrix.reindexAlgEquiv L L lab.symm)

theorem labMat_apply (X : Module.End L (Fin D.d →₀ L)) (r s : Fin n) :
    labMat lab L X r s = X (Finsupp.single (lab s) 1) (lab r) := by
  simp [labMat, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, natMat_apply]

theorem coe_toMat (g : (Module.End L (Fin D.d →₀ L))ˣ) :
    ((toMat lab L g : Matrix.GeneralLinearGroup (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      labMat lab L (g : Module.End L (Fin D.d →₀ L)) := by
  ext r s
  rw [toMat_apply, labMat_apply]

theorem labMat_cartanOp (i : Fin τ.rank) :
    labMat lab L (cartanOp L D i) = Matrix.diagonal fun a => ((D.wt (lab a) i : ℤ) : L) := by
  ext r s
  rw [labMat_apply, cartanOp_single, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply,
    Matrix.diagonal_apply]
  by_cases h : r = s
  · subst h
    simp
  · simp [h, lab.injective.ne (Ne.symm h)]

variable (hV : D.Valid) (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef) {S : AdjSigns τ}
  (hS : S.check D = true) (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) L))
  (hH : ∀ z ∈ H, IsZeroOfIdentities hV lab (z : Matrix (Fin n) (Fin n) L))
  (hu : ∀ i c, toMat lab L (rootUnit hV L (Pi.single i 1) c) ∈ H)
  (hv : ∀ i c, toMat lab L (rootUnit hV L (-Pi.single i 1) c) ∈ H)
  (hhw : ∀ a : Fin D.d, (a : ℕ) ≠ 0 → ∃ i, D.wt a i = -1) (hord : DegOrdered D) (hd : 0 < D.d)
  (hexcl : ∀ π' : Equiv.Perm (Fin τ.rank),
    (∀ ij : Fin τ.rank × Fin τ.rank, τ.cartan (π' ij.1) (π' ij.2) = τ.cartan ij.1 ij.2) →
      (∀ a : Fin D.d, ∃ b : Fin D.d, ∀ j, D.wt b (π' j) = D.wt a j) → π' = 1)

@[expose] def blockCarrier : Twisted.BlockCarrier τ L n 1 where
  C := H
  π := adCarrier hV hpd hS lab L H hH
  u i c := ⟨_, hu i c⟩
  v i c := ⟨_, hv i c⟩
  E i := labMat lab L (D.rootOp L (Pi.single i 1))
  F i := labMat lab L (D.rootOp L (-Pi.single i 1))
  coe_u i c := by
    change ((toMat lab L (rootUnit hV L (Pi.single i 1) c) : Matrix.GeneralLinearGroup (Fin n) L) :
      Matrix (Fin n) (Fin n) L) = _
    rw [coe_toMat, coe_rootUnit, map_add, map_one, map_smul]
  coe_v i c := by
    change ((toMat lab L (rootUnit hV L (-Pi.single i 1) c) :
      Matrix.GeneralLinearGroup (Fin n) L) : Matrix (Fin n) (Fin n) L) = _
    rw [coe_toMat, coe_rootUnit, map_add, map_one, map_smul]
  u_add i c d := Subtype.ext (by
    change toMat lab L (rootUnit hV L (Pi.single i 1) (c + d)) =
      toMat lab L (rootUnit hV L (Pi.single i 1) c) * toMat lab L (rootUnit hV L (Pi.single i 1) d)
    rw [rootUnit_add, map_mul])
  v_add i c d := Subtype.ext (by
    change toMat lab L (rootUnit hV L (-Pi.single i 1) (c + d)) =
      toMat lab L (rootUnit hV L (-Pi.single i 1) c) *
        toMat lab L (rootUnit hV L (-Pi.single i 1) d)
    rw [rootUnit_add, map_mul])
  π_u i c := adCarrier_rootUnit_single hV hpd hS lab L H hH i c (hu i c)
  π_v i c := adCarrier_rootUnit_neg_single hV hpd hS lab L H hH i c (hv i c)
  blk _ := 0
  block _ a b h := absurd (Subsingleton.elim _ _) h
  ker_diag z hz a b hab := by
    obtain ⟨c, hc⟩ := exists_eq_smul_one_of_adCarrier_eq_one hV hhw hord hd hz
    rw [hc, Matrix.smul_apply, Matrix.one_apply_ne hab, smul_zero]
  ker_center z hz := by
    obtain ⟨c, hc⟩ := exists_eq_smul_one_of_adCarrier_eq_one hV hhw hord hd hz
    refine Subgroup.mem_center_iff.2 fun w => Subtype.ext (Units.ext ?_)
    simp only [Subgroup.coe_mul, Units.val_mul, hc, Matrix.mul_smul, Matrix.smul_mul, mul_one,
      one_mul]
  wt a := D.wt (lab a)
  wt_mem a i := hV.wt_mem (lab a) i
  comm i := by
    rw [← map_mul, ← map_mul, ← map_sub, rootOp_single_comm_neg_single hV L i, labMat_cartanOp]
  comm_HE i j := by
    rw [← labMat_cartanOp, ← map_mul, ← map_mul, ← map_sub,
      cartanOp_comm_rootOp hV L (IsRoot.basis j) i, map_smul, toWeight_single]
  E_ne j h := hV.rootOp_ne_zero (R := L) (IsRoot.basis j)
    ((labMat lab L).injective (by rw [h, map_zero]))
  cartan_off i j hij := by
    rcases AdjSigns.cartan_cases hS i j with h | h | ⟨h, -⟩
    · exact absurd h hij
    · exact Or.inl h
    · exact Or.inr h
  excl π' hc h := hexcl π' hc fun a => by
    obtain ⟨b, -, hb⟩ := h (lab.symm a)
    exact ⟨lab b, fun j => by simpa using hb j⟩

include hu hv hhw hord hd hexcl in
theorem adCarrier_mem_adjointGroup
    {p : ℕ} [Fact p.Prime] [CharP L p] [IsAlgClosed L]
    [Algebra (ZMod p) L] [Algebra.IsAlgebraic (ZMod p) L] (hτ : τ ≠ .G2) (hp2 : p ≠ 2) (z : H) :
    adCarrier hV hpd hS lab L H hH z ∈ adjointGroup τ L :=
  (blockCarrier lab L hV hpd hS H hH hu hv hhw hord hd hexcl).π_mem_adjointGroup hτ hp2
    (fun z P hP => vanishes_adCarrier hV hpd hS lab L H hH z P hP) z

end CFSG.TauCetiBridge.Minuscule
