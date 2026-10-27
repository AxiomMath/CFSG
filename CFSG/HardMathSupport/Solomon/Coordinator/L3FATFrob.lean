module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3AField
public import CFSG.HardMathSupport.Solomon.Coordinator.L3AGap

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns

section Frob

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def frobHom (hK : PiField π p f K) :
    (K ≃+* K) →* MulAut ↥(slPi π 3 (p ^ f) K) where
  toFun := frobSL hK
  map_one' := MulEquiv.ext fun _ => Subtype.ext (frobGL_one_apply _)
  map_mul' σ τ := MulEquiv.ext fun _ => Subtype.ext (frobGL_mul_apply σ τ _)

theorem frobHom_apply (hK : PiField π p f K) (σ : K ≃+* K) : frobHom hK σ = frobSL hK σ := rfl

theorem frobSL_pow (hK : PiField π p f K) (σ : K ≃+* K) (j : ℕ) :
    frobSL hK (σ ^ j) = frobSL hK σ ^ j := by
  rw [← frobHom_apply, map_pow, frobHom_apply]

theorem frobSL_mul (hK : PiField π p f K) (σ τ : K ≃+* K) :
    frobSL hK (σ * τ) = frobSL hK σ * frobSL hK τ := by
  rw [← frobHom_apply, map_mul, frobHom_apply, frobHom_apply]

theorem frobSL_descend_eq_one {hK : PiField π p f K} (hq2 : π = false → 2 < p ^ f)
    {σ : K ≃+* K} (h : centerDescend ↥(slPi π 3 (p ^ f) K) (frobSL hK σ) = 1) : σ = 1 := by
  have := hK.finite
  cases π
  · have h1 := congr_eta_false_frob hK (hq2 rfl) σ
    rw [h, map_one] at h1
    have h2 : psuField hK.unitary σ ∈ (psuConj hK.unitary).range := by
      rw [← h1]; exact one_mem _
    exact (psuField_mem_range_psuConj_iff (h := hK.unitary)).1 h2
  · have h1 := congr_etaTrue_frob hK σ
    rw [h, map_one] at h1
    have h2 : fieldAut 3 K σ ∈ linearAutGroup 3 K := by
      rw [← h1]; exact one_mem _
    exact (fieldAut_mem_linearAutGroup_iff (le_refl 3)).1 h2

theorem exists_restrict {S : Subfield K} {ψ : K ≃+* K} (h : ∀ c, c ∈ S ↔ ψ c ∈ S) :
    ∃ ψ₀ : S ≃+* S, ∀ c : S, ((ψ₀ c : S) : K) = ψ (c : K) := by
  refine ⟨{ toFun := fun c => ⟨ψ c, (h c).1 c.2⟩
            invFun := fun c => ⟨ψ.symm c, ?_⟩
            left_inv := fun c => Subtype.ext (ψ.symm_apply_apply _)
            right_inv := fun c => Subtype.ext (ψ.apply_symm_apply _)
            map_mul' := fun a b => Subtype.ext (map_mul ψ _ _)
            map_add' := fun a b => Subtype.ext (map_add ψ _ _) }, fun c => rfl⟩
  exact (h (ψ.symm c)).2 (by rw [ψ.apply_symm_apply]; exact c.2)

theorem orderOf_restrict_dvd {S : Subfield K} {ψ : K ≃+* K} {ψ₀ : S ≃+* S}
    (h : ∀ c : S, ((ψ₀ c : S) : K) = ψ (c : K)) : orderOf ψ₀ ∣ orderOf ψ := by
  have hpow : ∀ (n : ℕ) (c : S), (((ψ₀ ^ n) c : S) : K) = (ψ ^ n) (c : K) := by
    intro n
    induction n with
    | zero => intro c; rfl
    | succ n ih =>
      intro c
      rw [pow_succ, pow_succ, RingAut.mul_apply, RingAut.mul_apply, ih, h]
  refine orderOf_dvd_of_pow_eq_one (RingEquiv.ext fun c => Subtype.ext ?_)
  rw [hpow, pow_orderOf_eq_one]
  rfl

theorem frobSL_incl {σ : K ≃+* K} {hK : PiField π p f K} (d : FrobData hK σ) {ψ : K ≃+* K}
    {ψ₀ : d.K₀ ≃+* d.K₀} (h : ∀ c : d.K₀, ((ψ₀ c : d.K₀) : K) = ψ (c : K))
    (t : ↥(slPi π 3 (p ^ d.f₀) d.K₀)) :
    frobSL hK ψ (d.incl t) = d.incl (frobSL d.hP ψ₀ t) := by
  apply Subtype.ext
  rw [coe_frobSL, FrobData.coe_incl, FrobData.coe_incl, coe_frobSL]
  apply Units.ext
  rw [coe_frobGL, coe_subGL, coe_subGL, coe_frobGL]
  ext i j
  simp only [Matrix.map_apply]
  exact (h _).symm

end Frob

section Field

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

theorem isFieldAutThree_of_frob' {Y : Type} [Group Y] (hK : PiField π p f K)
    (hq2 : π = false → 2 < p ^ f)
    (e : (Y ⧸ Subgroup.center Y) ≃*
      (↥(slPi π 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 3 (p ^ f) K)))
    {α : MulAut Y} {σ : K ≃+* K} (hσ : π = false → Odd (orderOf σ))
    (h : MulAut.congr e (centerDescend Y α) = centerDescend _ (frobSL hK σ)) :
    IsFieldAutThree α := by
  have := hK.finite
  right
  cases π
  · right
    refine isFieldAutPSU3_of_data hK.unitary (e.trans (etaFalse hK (hq2 rfl))) σ (hσ rfl) 1 ?_
    rw [congr_trans', h, congr_eta_false_frob, inv_one, mul_one, one_mul]
  · left
    refine isFieldAutPSL3_of_data (e.trans (etaTrue (p ^ f) K)) σ 1 ?_
    rw [congr_trans', h, congr_etaTrue_frob, inv_one, mul_one, one_mul]

end Field

end CFSG.HardMathSupport.Solomon.Coordinator
