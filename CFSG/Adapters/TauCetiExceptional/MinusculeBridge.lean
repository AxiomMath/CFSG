module

public import CFSG.Adapters.TauCetiExceptional.MinusculeBlock
public import CFSG.Adapters.TauCetiExceptional.MinusculeTransfer
public import CFSG.Adapters.TauCetiExceptional.BridgeTransport

public noncomputable section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  TauCeti MinData

variable {τ : Tag} {D : MinData τ} {n : ℕ} (lab : Fin n ≃ Fin D.d) (L : Type) [Field L]
  (hV : D.Valid) (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef) {S : AdjSigns τ}
  (hS : S.check D = true) (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) L))
  (hH : ∀ z ∈ H, IsZeroOfIdentities hV lab (z : Matrix (Fin n) (Fin n) L))
  (hu : ∀ i c, toMat lab L (rootUnit hV L (Pi.single i 1) c) ∈ H)
  (hv : ∀ i c, toMat lab L (rootUnit hV L (-Pi.single i 1) c) ∈ H)
  (hhw : ∀ a : Fin D.d, (a : ℕ) ≠ 0 → ∃ i, D.wt a i = -1) (hord : DegOrdered D) (hd : 0 < D.d)
  (hexcl : ∀ π' : Equiv.Perm (Fin τ.rank),
    (∀ ij : Fin τ.rank × Fin τ.rank, τ.cartan (π' ij.1) (π' ij.2) = τ.cartan ij.1 ij.2) →
      (∀ a : Fin D.d, ∃ b : Fin D.d, ∀ j, D.wt b (π' j) = D.wt a j) → π' = 1)
  {p : ℕ} [Fact p.Prime] [CharP L p] [IsAlgClosed L] [Algebra (ZMod p) L]
  [Algebra.IsAlgebraic (ZMod p) L] (hτ : τ ≠ .G2) (hp2 : p ≠ 2)
  (σ : H →* H) (Fr : L →+* L)
  (hσ : ∀ (z : H) (r s : Fin n), (((σ z : H) : Matrix.GeneralLinearGroup (Fin n) L) :
    Matrix (Fin n) (Fin n) L) r s = Fr (((z : Matrix.GeneralLinearGroup (Fin n) L) :
      Matrix (Fin n) (Fin n) L) r s))

include hu hv hhw hord hd hexcl hτ hp2 hσ in
theorem isIsogeny_adCarrier :
    IsIsogeny τ L Fr σ (adCarrier hV hpd hS lab L H hH) where
  mem z := adCarrier_mem_adjointGroup lab L hV hpd hS H hH hu hv hhw hord hd hexcl hτ hp2 z
  surj x hx := by
    obtain ⟨g, hg⟩ :=
      (blockCarrier lab L hV hpd hS H hH hu hv hhw hord hd hexcl).adjointGroup_le_range hx
    exact ⟨g, hg⟩
  ker z hz := (blockCarrier lab L hV hpd hS H hH hu hv hhw hord hd hexcl).ker_center z hz
  comm z := by
    have hnat : ((((σ z : H) : Matrix.GeneralLinearGroup (Fin n) L) :
        Matrix (Fin n) (Fin n) L)).submatrix lab.symm lab.symm =
          Fr.mapMatrix (((z : Matrix.GeneralLinearGroup (Fin n) L) :
            Matrix (Fin n) (Fin n) L).submatrix lab.symm lab.symm) := by
      ext r s
      simp only [Matrix.submatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, hσ]
    refine Units.ext ((BigCell.natMat τ L).injective (Matrix.ext fun i j => ?_))
    change BigCell.natMat τ L ((adCarrier hV hpd hS lab L H hH (σ z) : ModGL τ L) :
      Module.End L (RootModule τ L)) i j = BigCell.natMat τ L (entrywise Fr
        ((adCarrier hV hpd hS lab L H hH z : ModGL τ L) : Module.End L (RootModule τ L))) i j
    rw [natMat_entrywise, natMat_adCarrier, natMat_adCarrier, hnat, ← mapMatrix_adMat S Fr]
    rfl

include hpd hS hH hu hv hhw hord hd hexcl hτ hp2 hσ in
theorem nonempty_fixedPointCandidate_equiv
    (E : Type) [Field E] [Finite E] [Algebra E L]
    [IsAlgClosure E L] (hodd : Odd (Nat.card E)) (hFr : ∀ c, Fr c = c ^ Nat.card E)
    (hperfE : ⁅adjointGroup τ E, adjointGroup τ E⁆ = adjointGroup τ E) :
    Nonempty (FixedPointCandidate σ ≃* AdjointQuotient τ E) := by
  have hI := isIsogeny_adCarrier lab L hV hpd hS H hH hu hv hhw hord hd hexcl hτ hp2 σ Fr hσ
  obtain ⟨-, -, -, hder⟩ := exceptional_Lang_Frobenius_fixed_derived_root_group τ E hodd L Fr hFr
  change ⁅frobFixedGroup τ L Fr, frobFixedGroup τ L Fr⁆ = _ at hder
  have hperf : ⁅⁅frobFixedGroup τ L Fr, frobFixedGroup τ L Fr⁆,
      ⁅frobFixedGroup τ L Fr, frobFixedGroup τ L Fr⁆⁆ =
        ⁅frobFixedGroup τ L Fr, frobFixedGroup τ L Fr⁆ := by
    rw [hder, ← Subgroup.map_commutator, hperfE]
  let e₂ : ↥⁅frobFixedGroup τ L Fr, frobFixedGroup τ L Fr⁆ ≃* ↥(adjointGroup τ E) :=
    (MulEquiv.subgroupCongr hder).trans ((adjointGroup τ E).equivMapOfInjective _
      (baseChangeGL_injective (algebraMap E L))).symm
  have hZ : Subgroup.center ↥⁅frobFixedGroup τ L Fr, frobFixedGroup τ L Fr⁆ = ⊥ := by
    have h1 := Subgroup.map_center_eq e₂
    rw [center_adjointGroup_eq_bot] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e₂.injective).1 h1
  exact ⟨(hI.derivedCentralQuotientEquiv hperf hZ).trans (e₂.trans
    (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot (τ := τ) (K := E)).symm)))⟩

omit [Field L] in
include hpd hS in
theorem commutator_adjointGroup_eq
    (K : Type*) [Field K]
    (hperf : Group.IsPerfect (hV.minGroup K)) :
    ⁅adjointGroup τ K, adjointGroup τ K⁆ = adjointGroup τ K := by
  have h := Group.isPerfect_def.1 hperf
  rw [commutator_def] at h
  rw [← range_adMin hV hpd hS K, MonoidHom.range_eq_map, ← Subgroup.map_commutator, h]

end CFSG.TauCetiBridge.Minuscule
