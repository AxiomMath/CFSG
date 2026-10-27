module

public import CFSG.LieType.SemisimpleCentralizers.HeldUCDKBlock
public import CFSG.LieType.SemisimpleCentralizers.HeldUCDTransfer
public import CFSG.LieType.SemisimpleCentralizers.HeldUCDField

public section

open CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.LieType.SemisimpleCentralizers.HeldUCD

open Matrix Polynomial

open scoped _root_.Classical

variable {L : Type} [Field L] [Finite L] {n : ℕ}

section SelfDual

variable {τ : L ≃+* L} {m : ℕ} {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]}
  {a b : L[X] → L[X]}

theorem dvd_starP_of_self_dual (H : PrimaryHyp τ s m F a b) {f : L[X]} (hf : f ∈ F)
    (hPf : Pmat s b F f ≠ 0) (hself : adjM τ (Pmat s b F f) = Pmat s b F f) :
    f ∣ starP τ m f := by
  rw [← aeval_mul_Pmat_iff H.hirr H.hmon H.hprod H.hsm H.hab hf hPf]
  have h1 : adjM τ (aeval s f * Pmat s b F f) = 0 := by
    rw [aeval_mul_Pmat_self H.hirr H.hmon H.hprod H.hsm H.hab hf, adjM_zero' τ]
  rw [adjM_mul, hself, adjM_aeval_eq_aeval_starP τ H.hτ H.hm s H.hsm H.hs f] at h1
  have hc : aeval s (starP τ m f) * Pmat s b F f = Pmat s b F f * aeval s (starP τ m f) := by
    rw [Pmat, ← map_mul, ← map_mul, mul_comm]
  rw [hc, h1]

@[expose] noncomputable def hW (τ : L ≃+* L) (s : Matrix (Fin n) (Fin n) L) (b : L[X] → L[X])
    (F : Finset L[X]) (f : L[X]) : Vf s b F f →ₛₗ[(τ : L →+* L)] Vf s b F f →ₗ[L] L :=
  LinearMap.mk₂'ₛₗ (τ : L →+* L) (RingHom.id L)
    (fun x y => hfm τ (x : Fin n → L) (y : Fin n → L))
    (fun x x' y => by
      rw [Submodule.coe_add, hfm_add_left])
    (fun c x y => by
      rw [Submodule.coe_smul, hfm_smul_left, smul_eq_mul]; rfl)
    (fun x y y' => by
      rw [Submodule.coe_add, hfm_add_right])
    (fun c x y => by
      rw [Submodule.coe_smul, hfm_smul_right, RingHom.id_apply, smul_eq_mul])

theorem hW_apply (τ : L ≃+* L) (s : Matrix (Fin n) (Fin n) L) (b : L[X] → L[X])
    (F : Finset L[X]) (f : L[X]) (x y : Vf s b F f) :
    hW τ s b F f x y = hfm τ (x : Fin n → L) (y : Fin n → L) := rfl

variable {f : L[X]}

theorem hW_smul_adj (H : PrimaryHyp τ s m F a b) [Fact (∀ x ∈ Vf s b F f, aeval s f *ᵥ x = 0)]
    (hdiv : f ∣ starP τ m f) (c : AdjoinRoot f) (x y : Vf s b F f) :
    hfm τ (((c • x : Vf s b F f)) : Fin n → L) (y : Fin n → L) =
      hfm τ (x : Fin n → L) (((sigmaK τ m hdiv c • y : Vf s b F f)) : Fin n → L) := by
  induction c using AdjoinRoot.induction_on with
  | ih q =>
    rw [coe_smul_mk, sigmaK_mk, coe_smul_mk, hfm_mulVec, adjM_aeval_eq_aeval_starP τ H.hτ H.hm s
      H.hsm H.hs q]

theorem hW_nondeg (H : PrimaryHyp τ s m F a b) {f : L[X]} (hf : f ∈ F)
    (hself : adjM τ (Pmat s b F f) = Pmat s b F f) :
    ∀ x : Vf s b F f, (∀ y : Vf s b F f, hW τ s b F f x y = 0) → x = 0 := by
  intro x hx
  apply Subtype.ext
  refine eq_zero_of_hfm_block (π := fun g => g) H hf hself hf (mem_Vf.mp x.2) (fun y => ?_)
  have hy : Pmat s b F f *ᵥ (Pmat s b F f *ᵥ y) = Pmat s b F f *ᵥ y := by
    rw [Matrix.mulVec_mulVec, H.Pmat_idem hf]
  have := hx ⟨Pmat s b F f *ᵥ y, mem_Vf.mpr hy⟩
  rw [hW_apply] at this
  exact this

@[expose] def invEquiv {K : Type} [Field K] (σ : K →+* K) (h : ∀ x, σ (σ x) = x) : K ≃+* K :=
  { σ with toFun := σ, invFun := σ, left_inv := h, right_inv := h }

@[expose] noncomputable def unitaryBlock (τ : L ≃+* L) (s : Matrix (Fin n) (Fin n) L)
    (b : L[X] → L[X]) (F : Finset L[X]) (f : L[X])
    [Fact (∀ x ∈ Vf s b F f, aeval s f *ᵥ x = 0)] :
    Subgroup (LinearMap.GeneralLinearGroup (AdjoinRoot f) (Vf s b F f)) where
  carrier := {g | ∀ x y : Vf s b F f,
    hfm τ ((g.1 x : Vf s b F f) : Fin n → L) ((g.1 y : Vf s b F f) : Fin n → L) =
      hfm τ (x : Fin n → L) (y : Fin n → L)}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro g g' hg hg' x y
    show hfm τ ((g.1 (g'.1 x) : Vf s b F f) : Fin n → L) ((g.1 (g'.1 y) : Vf s b F f) : Fin n → L) = _
    rw [hg, hg']
  inv_mem' := by
    intro g hg x y
    have e1 : ∀ z : Vf s b F f, g.1 (g⁻¹.1 z) = z := fun z => by
      rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Module.End.one_apply]
    have h := hg (g⁻¹.1 x) (g⁻¹.1 y)
    rw [e1, e1] at h
    exact h.symm

theorem selfDual_unitaryOrLinear (H : PrimaryHyp τ s m F a b) {f : L[X]} [Fact (Irreducible f)]
    [Fact (∀ x ∈ Vf s b F f, aeval s f *ᵥ x = 0)] (hf : f ∈ F) (hPf : Pmat s b F f ≠ 0)
    (hself : adjM τ (Pmat s b F f) = Pmat s b F f) (Q : ℕ) (hQ : Nat.card L = Q ^ 2)
    (hτQ : ∀ x, τ x = x ^ Q) :
    Held.UnitaryOrLinearBlock Q ↥(unitaryBlock τ s b F f) := by
  classical
  have hdiv : f ∣ starP τ m f := dvd_starP_of_self_dual H hf hPf hself
  have hdvd : f ∣ (X ^ m - 1 : L[X]) := by
    rw [← H.hprod]
    exact Finset.dvd_prod_of_mem _ hf
  have hσσ : ∀ x, sigmaK τ m hdiv (sigmaK τ m hdiv x) = x :=
    sigmaK_sigmaK τ H.hτ H.hm hdiv hdvd
  have hσL : ∀ l : L, sigmaK τ m hdiv (algebraMap L (AdjoinRoot f) l) =
      algebraMap L (AdjoinRoot f) (τ l) := fun l => sigmaK_of τ m hdiv l
  haveI : Module.Finite L (AdjoinRoot f) := (H.hmon f hf).finite_adjoinRoot
  haveI : Finite (AdjoinRoot f) :=
    Finite.of_equiv (Fin (Module.finrank L (AdjoinRoot f)) → L)
      (Module.finBasis L (AdjoinRoot f)).equivFun.toEquiv.symm
  let σE : AdjoinRoot f ≃+* AdjoinRoot f := invEquiv (sigmaK τ m hdiv) hσσ
  obtain ⟨p, e, hp, he1, hQe, hodd, hcard, hsig⟩ :=
    sigma_eq_frobenius_pow hQ τ hτQ σE hσL hσσ
  set k := Module.finrank L (AdjoinRoot f) with hk
  have hbar_card : Nat.card (AdjoinRoot f) = p ^ (2 * (e * k)) := by
    rw [hcard, hQe, ← pow_mul]
    congr 1
    ring
  have hUFD : UnitaryFieldData p (e * k) (AdjoinRoot f) :=
    ⟨hp, Nat.mul_pos he1 hodd.pos, hbar_card⟩
  have hbar : ∀ x, hUFD.bar x = sigmaK τ m hdiv x := by
    intro x
    rw [UnitaryFieldData.bar_apply]
    have h1 := hsig x
    rw [hQe, ← pow_mul] at h1
    exact h1.symm
  have hρE : ∀ x, hUFD.bar (hUFD.bar x) = x := hUFD.bar_bar
  have hρL : ∀ l : L, hUFD.bar (algebraMap L (AdjoinRoot f) l) =
      algebraMap L (AdjoinRoot f) (τ l) := fun l => by
    rw [hbar]
    exact hσL l
  have hherm : ∀ x y : Vf s b F f, τ (hW τ s b F f x y) = hW τ s b F f y x := by
    intro x y
    rw [hW_apply, hW_apply]
    exact hfm_symm τ H.hτ _ _
  have hadj : ∀ (c : AdjoinRoot f) (x y : Vf s b F f),
      hW τ s b F f (c • x) y = hW τ s b F f x (hUFD.bar c • y) := by
    intro c x y
    rw [hbar]
    exact hW_smul_adj H hdiv c x y
  obtain ⟨B, hsymm, hsep, hrep⟩ :=
    exists_trace_form hUFD.bar (τ : L →+* L) hρE hρL (hW τ s b F f) hherm hadj
      (hW_nondeg H hf hself)
  haveI : Module.Finite L (Vf s b F f) := inferInstance
  haveI : FiniteDimensional (AdjoinRoot f) (Vf s b F f) :=
    Module.Finite.of_restrictScalars_finite L (AdjoinRoot f) (Vf s b F f)
  obtain ⟨e0, he0⟩ :=
    UnitaryFieldData.exists_orthonormal_basis hUFD (B := B) (LinearMap.isSymm_def.mpr hsymm) hsep
  let ρE : AdjoinRoot f ≃+* AdjoinRoot f := invEquiv hUFD.bar hρE
  obtain ⟨φ⟩ := nonempty_mulEquiv_heldGU ρE hρE B e0 he0
  have hsub : unitaryBlock τ s b F f = sesqUnitaryGroup B := by
    ext g
    rw [mem_sesqUnitaryGroup]
    exact unitary_trace_iff (hW τ s b F f) B hrep g.1
  refine Or.inl ⟨Module.finrank (AdjoinRoot f) (Vf s b F f), k, AdjoinRoot f, inferInstance,
    inferInstance, ρE, hρE, hodd, ?_, ?_, ⟨(MulEquiv.subgroupCongr hsub).trans φ⟩⟩
  · intro x
    show hUFD.bar x = _
    rw [UnitaryFieldData.bar_apply, hQe, ← pow_mul]
  · rw [hcard, ← pow_mul, mul_comm]

end SelfDual


end CFSG.LieType.SemisimpleCentralizers.HeldUCD

end
