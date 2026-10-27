module

public import CFSG.Adapters.TauCetiExceptional.EvenBlockEndgame
public import CFSG.Adapters.TauCetiExceptional.EvenMono
public import CFSG.Adapters.TauCetiExceptional.BridgeTransport
public import CFSG.Adapters.TauCetiExceptional.MinusculeBlock
public import CFSG.Adapters.TauCetiExceptional.MinusculeTransfer

public noncomputable section

namespace CFSG.TauCetiBridge.Even

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  TauCeti MinData Minuscule

variable {τ : Tag} {D : MinData τ} {n : ℕ}

@[expose] def minMono
    (hV : D.Valid) (lab : Fin n ≃ Fin D.d) (L : Type) [Field L] :
    MonoRoots L n τ.rank where
  E i := labMat lab L (D.rootOp L (Pi.single i 1))
  F i := labMat lab L (D.rootOp L (-Pi.single i 1))
  wt a := D.wt (lab a)
  refl i a := lab.symm (hV.sRefl i (lab a))
  E_apply i a b := by
    rw [labMat_apply, hV.rootOp_single_apply]
    by_cases h : D.wt (lab b) i = -1
    · rw [ite_eq_left h, Finsupp.single_apply]
      simp only [h, true_and, Equiv.eq_symm_apply, eq_comm]
    · simp [h]
  F_apply i a b := by
    rw [labMat_apply, hV.rootOp_neg_single_apply]
    by_cases h : D.wt (lab b) i = 1
    · rw [ite_eq_left h, Finsupp.single_apply]
      simp only [h, true_and, Equiv.eq_symm_apply, eq_comm]
    · simp [h]
  refl_refl i b := by simp [hV.sRefl_sRefl]
  wt_refl i b := by simp [hV.wt_sRefl_self]

variable (lab : Fin n ≃ Fin D.d) (L : Type) [Field L]
  (hV : D.Valid) (hpd : (τ.cartan.map (Int.cast : ℤ → ℚ)).PosDef) {S : AdjSigns τ}
  (hS : S.check D = true) (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) L))
  (hH : ∀ z ∈ H, IsZeroOfIdentities hV lab (z : Matrix (Fin n) (Fin n) L))
  (hu : ∀ i c, toMat lab L (rootUnit hV L (Pi.single i 1) c) ∈ H)
  (hv : ∀ i c, toMat lab L (rootUnit hV L (-Pi.single i 1) c) ∈ H)
  (hhw : ∀ a : Fin D.d, (a : ℕ) ≠ 0 → ∃ i, D.wt a i = -1) (hord : DegOrdered D) (hd : 0 < D.d)
  (hexcl : ∀ π' : Equiv.Perm (Fin τ.rank),
    (∀ ij : Fin τ.rank × Fin τ.rank, τ.cartan (π' ij.1) (π' ij.2) = τ.cartan ij.1 ij.2) →
      (∀ a : Fin D.d, ∃ b : Fin D.d, ∀ j, D.wt b (π' j) = D.wt a j) → π' = 1)
  (h0 : ∀ i, D.wt 0 i ≠ -1)
  (hexcl2 : ∀ π' : Equiv.Perm (Fin τ.rank),
    (∀ ij : Fin τ.rank × Fin τ.rank, τ.cartan (π' ij.1) (π' ij.2) = τ.cartan ij.1 ij.2) →
      (∀ j, D.wt 0 j = 1 ↔ D.wt 0 (π' j) = 1) → π' = 1)

include h0 hexcl2 in
theorem exclTwo_minuscule :
    ExclTwo (blockCarrier lab L hV hpd hS H hH hu hv hhw hord hd hexcl) := by
  intro z π' c hc hcart hE hF
  refine hexcl2 π' (fun ij => hcart ij.1 ij.2) fun j => ?_
  have hw : ∀ j, (minMono hV lab L).wt (lab.symm ⟨0, hd⟩) j = D.wt 0 j := fun j => by
    simp [minMono]
  have key := (minMono hV lab L).wt_eq_one_iff_of_conj (fun _ => (0 : Fin 1))
    ((blockCarrier lab L hV hpd hS H hH hu hv hhw hord hd hexcl).mat_inv_mul z)
    (fun _ _ h => absurd rfl h) π' hc hE hF (h := lab.symm ⟨0, hd⟩)
    (fun i => by rw [hw]; exact h0 i)
    (fun b _ hb => hhw (lab b) fun h => hb (by
      rw [Equiv.eq_symm_apply]
      exact Fin.ext h)) j
  rwa [hw, hw] at key

variable {p : ℕ} [Fact p.Prime] [CharP L p] [IsAlgClosed L] [Algebra (ZMod p) L]
  [Algebra.IsAlgebraic (ZMod p) L] (hτ : τ ≠ .G2) (hp : p = 2)
  (σ : H →* H) (Fr : L →+* L)
  (hσ : ∀ (z : H) (r s : Fin n), (((σ z : H) : Matrix.GeneralLinearGroup (Fin n) L) :
    Matrix (Fin n) (Fin n) L) r s = Fr (((z : Matrix.GeneralLinearGroup (Fin n) L) :
      Matrix (Fin n) (Fin n) L) r s))

include hu hv hhw hord hd hexcl h0 hexcl2 hτ hp in
theorem adCarrier_mem_adjointGroup_two
    (z : H) :
    adCarrier hV hpd hS lab L H hH z ∈ adjointGroup τ L :=
  π_mem_adjointGroup_two (blockCarrier lab L hV hpd hS H hH hu hv hhw hord hd hexcl) hp hτ
    (exclTwo_minuscule lab L hV hpd hS H hH hu hv hhw hord hd hexcl h0 hexcl2)
    (fun z P hP => vanishes_adCarrier hV hpd hS lab L H hH z P hP) z

include hu hv hhw hord hd hexcl h0 hexcl2 hτ hp hσ in
theorem isIsogeny_adCarrier_two :
    IsIsogeny τ L Fr σ (adCarrier hV hpd hS lab L H hH) where
  mem z := adCarrier_mem_adjointGroup_two lab L hV hpd hS H hH hu hv hhw hord hd hexcl h0 hexcl2
    hτ hp z
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

include hpd hS hH hu hv hhw hord hd hexcl h0 hexcl2 hτ hp hσ in
theorem nonempty_fixedPointCandidate_equiv_two
    (E : Type) [Field E] [Finite E] [Algebra E L]
    [IsAlgClosure E L] (hFr : ∀ c, Fr c = c ^ Nat.card E)
    (hperfE : ⁅adjointGroup τ E, adjointGroup τ E⁆ = adjointGroup τ E) :
    Nonempty (FixedPointCandidate σ ≃* AdjointQuotient τ E) := by
  have hI := isIsogeny_adCarrier_two lab L hV hpd hS H hH hu hv hhw hord hd hexcl h0 hexcl2 hτ hp
    σ Fr hσ
  obtain ⟨-, -, -, hder⟩ := Lang_Frobenius_fixed_derived_of_perfect τ E hperfE L Fr hFr
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

end CFSG.TauCetiBridge.Even
