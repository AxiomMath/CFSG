module

public import CFSG.HardMathSupport.Dickson.KD.CharPAux.Frame
public import CFSG.HardMathSupport.Timmesfeld.DefChar.CoreDFour
public import CFSG.HardMathSupport.Dickson.KD.CharPAux.FlagGroup

public section

namespace CFSG.HardMathSupport.Dickson.KD

open CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.HardMathSupport.Timmesfeld.DefChar.Orth
  QuadraticMap Matrix CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

section Cayley

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Z : Module.End K V} {n : ℕ}

theorem inFlag_cay [Nontrivial V] (hn : Z ^ n = 0) (t : K) : InFlag Z (cay Z n t) := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact one_ne_zero hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hker : ∀ x ∈ LinearMap.ker Z, cay Z (m + 1) t x = x := by
    intro x hx
    have hZx : Z x = 0 := LinearMap.mem_ker.1 hx
    have hpow : ∀ i : ℕ, ((t • Z) ^ (i + 1)) x = 0 := by
      intro i
      rw [pow_succ, Module.End.mul_apply, LinearMap.smul_apply, hZx, smul_zero, map_zero]
    have hsum : (∑ i ∈ Finset.range (m + 1), (t • Z) ^ i) x = x := by
      rw [Finset.sum_range_succ', LinearMap.add_apply, pow_zero, Module.End.one_apply]
      have : (∑ i ∈ Finset.range m, (t • Z) ^ (i + 1)) x = 0 := by
        rw [LinearMap.sum_apply]
        exact Finset.sum_eq_zero fun i _ => hpow i
      rw [this, zero_add]
    rw [cay, Module.End.mul_apply, hsum, LinearMap.add_apply, Module.End.one_apply,
      LinearMap.smul_apply, hZx, smul_zero, add_zero]
  refine ⟨fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · have := cay_comm (Z := Z) (n := m + 1) (s := Z) rfl t
    exact (LinearMap.congr_fun this x).symm
  · rw [hker x hx, sub_self]
    exact Submodule.zero_mem _
  · exact hker x hx.1

end Cayley

section Orth

variable {K : Type} [Field K] {d : ℕ}

@[expose] noncomputable def omegaRep (Q : QuadraticForm K (Fin d → K)) :
    matrixDerived Q →* Module.End K (Fin d → K) :=
  (glRep (Fin d) K).comp (matrixDerived Q).subtype

theorem omegaRep_apply (Q : QuadraticForm K (Fin d → K)) (f : matrixDerived Q) :
    omegaRep Q f = toE f.val := by
  refine LinearMap.ext fun v => ?_
  rw [toE_apply]
  rfl

theorem omegaRep_injective (Q : QuadraticForm K (Fin d → K)) : Function.Injective (omegaRep Q) :=
  glRep_injective.comp Subtype.val_injective

variable [NeZero d] {Q : QuadraticForm K (Fin d → K)} {p : ℕ} [Fact p.Prime] [CharP K p]

theorem frame_orth (hp2 : p ≠ 2) (hd : 5 ≤ d) (hnd : (polarBilin Q).Nondegenerate)
    (hQ : ∃ v, Q v ≠ 0)
    (hab : ∃ m : ℕ, Nat.card (Abelianization (matrixIsometries Q)) = 2 ^ m)
    (y : matrixProjectiveDerived Q) (hy : orderOf y = p) : Frame p y := by
  have hp : p.Prime := Fact.out
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨s0, c, hcc, hg0, hG, hG1⟩ := exists_lift hQ hp2 y hy
  have hZ := zEnd_skew s0 h2 hodd hG hcc
  have hn := zEnd_pow s0 hG
  have hyT : y ∈ tSet Q p s0 c := by
    obtain ⟨f1, hf1⟩ := exists_cay_mem hp2 h2 hab hZ hn 1
    refine ⟨f1, 1, hf1, ?_⟩
    rw [hg0]
    have hc0 : c ≠ 0 := fun h => by rw [h, mul_zero] at hcc; exact zero_ne_one hcc
    have hE : toE f1.val = c • toE s0.val := by
      rw [hf1, cay_zEnd_one s0 h2 hodd hG]
      rfl
    symm
    rw [proj_eq_iff]
    refine ⟨Units.mk0 c hc0, ?_⟩
    apply toE_injective
    rw [toE_mul, toE_scalar, hE, Units.val_mk0, smul_mul_assoc, mul_smul_comm, mul_one, smul_smul,
      hcc, one_smul]
  have hy' : matrixProjectiveProjection Q s0 = y := hg0.symm
  refine ⟨genSet Q p s0 c, tSet Q p s0 c, ?_, ?_, ?_, ?_, ?_⟩
  · rintro q (hq | hq)
    · rw [← hy']
      exact genSet_commute h2 hodd hcc hG hq
    · rw [← hy']
      exact tSet_commute hcc hG hq
  · intro s q hs hq
    rw [← hy'] at hs
    exact tSet_central hcc hG hs hq
  · intro s q hs hq
    rw [← hy'] at hs
    exact genSet_conj hcc hG hs hq
  · intro t hcop hfix
    refine uniq_orth hnd hd h2 hp2 hab hcc hG hG1 (inner_mem_matrixProjectiveImage Q t)
      (Nat.Coprime.coprime_dvd_left (orderOf_map_dvd MulAut.conj t) hcop) ?_
      (fun q hq => hfix q (Or.inl hq)) (fun q hq => hfix q (Or.inr hq))
    rw [hy']
    exact hfix y (Or.inr hyT)
  · haveI : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_neZero d⟩⟩
    have hZn : IsNilpotent (zEnd p s0 c) := ⟨p, hn⟩
    refine isPGroup_closure_of_subset_map (omegaRep_injective Q) hZn
      (matrixProjectiveProjection Q) ?_
    rintro q (⟨f, hf, rfl⟩ | ⟨f, t, hf, rfl⟩)
    · refine ⟨f, mem_flagSub.2 ?_, rfl⟩
      rw [omegaRep_apply]
      exact hf
    · refine ⟨f, mem_flagSub.2 ?_, rfl⟩
      rw [omegaRep_apply, hf]
      exact inFlag_cay hn t

theorem kdCharPAt_of_orthEquiv {T : Type} [Group T] [Finite K] (hp2 : p ≠ 2) (hd : 5 ≤ d)
    (hnd : (polarBilin Q).Nondegenerate) (hQ : ∃ v, Q v ≠ 0)
    (hab : ∃ m : ℕ, Nat.card (Abelianization (matrixIsometries Q)) = 2 ^ m)
    (e : T ≃* matrixProjectiveDerived Q) (hT : IsSimpleGroup T) : KDCharPAt p T := by
  haveI : IsSimpleGroup T := hT
  haveI : IsSimpleGroup (matrixProjectiveDerived Q) := e.symm.isSimpleGroup
  exact kdCharPAt_of_frame_simple e inferInstance fun y hy => frame_orth hp2 hd hnd hQ hab y hy

end Orth

section Families

open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag StatedProj StatedOmega
  StatedQuadOdd StatedQuadPlus StatedQuadMinus)
open Subgroup CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
  CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal

theorem kdCharPAt_of_model_POmegaOdd {T : Type} [Group T] {n ℓ f : ℕ}
    (hm : StatedClassicalModel T .POmegaOdd n ℓ f) : KDCharPAt ℓ T := by
  have h0 := hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  have hn : 3 ≤ n := hm.1.2.2.1
  have hℓ2 : ℓ ≠ 2 := hm.1.2.2.2
  have : Fact ℓ.Prime := ⟨hm.1.1⟩
  have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaOdd (.inl rfl)
    n ℓ f hm K hK (quadOdd n K) (coe_quadOdd n K) e
  obtain ⟨hchar, hnd, -⟩ := coordinate_model_witness_odd hm K hK e
  have : CharP K ℓ := by
    have := ringChar.charP K
    rw [hchar] at this
    exact this
  have hS := (isSimpleGroup_of_statedClassicalModel_POmegaOdd T n ℓ f hm).2
  haveI : NeZero (2 * n + 1) := ⟨by omega⟩
  exact kdCharPAt_of_orthEquiv hℓ2 (d := 2 * n + 1) (by omega) hnd
    (exists_nonzero_value _ (coordinate_model_intrinsic_odd hm K hK e).1)
    (exists_two_pow_card_abelianization (oddIndexEquiv n) (quadOdd n K) hab)
    (coordinateOddWitnessEquiv K e) hS

theorem kdCharPAt_of_model_POmegaPlus {T : Type} [Group T] {n ℓ f : ℕ}
    (hm : StatedClassicalModel T .POmegaPlus n ℓ f) (hℓ2 : ℓ ≠ 2) : KDCharPAt ℓ T := by
  have h0 := hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  have hn : 4 ≤ n := hm.1.2.2
  have : Fact ℓ.Prime := ⟨hm.1.1⟩
  have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaPlus
    (.inr (.inl rfl)) n ℓ f hm K hK (quadPlus n K) (coe_quadPlus n K) e
  obtain ⟨hchar, hnd, -⟩ := coordinate_model_witness_plus hm K hK e
  have : CharP K ℓ := by
    have := ringChar.charP K
    rw [hchar] at this
    exact this
  have hS := (isSimpleGroup_of_statedClassicalModel_POmegaPlus T n ℓ f hm).2
  haveI : NeZero (2 * n) := ⟨by omega⟩
  exact kdCharPAt_of_orthEquiv hℓ2 (d := 2 * n) (by omega) hnd
    (exists_nonzero_value _ (coordinate_model_intrinsic_plus hm K hK e).1)
    (exists_two_pow_card_abelianization (plusIndexEquiv n) (quadPlus n K) hab)
    (coordinatePlusWitnessEquiv K e) hS

theorem kdCharPAt_of_model_POmegaMinus {T : Type} [Group T] {n ℓ f : ℕ}
    (hm : StatedClassicalModel T .POmegaMinus n ℓ f) (hℓ2 : ℓ ≠ 2) : KDCharPAt ℓ T := by
  have hn4 : 4 ≤ n := hm.1.2.2
  have hn1 : 1 ≤ n := by omega
  have h0 := hm
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h0
  have : Fact ℓ.Prime := ⟨hm.1.1⟩
  have hab := orthogonal_model_isometry_abelianization_order_bound T .POmegaMinus
    (.inr (.inr rfl)) n ℓ f hm K hK b c hirr (quadMinus n K b c) (coe_quadMinus n K b c) e
  obtain ⟨hchar, hnd, -⟩ := coordinate_model_witness_minus hm K hK b c hirr e
  have : CharP K ℓ := by
    have := ringChar.charP K
    rw [hchar] at this
    exact this
  have hS := (isSimpleGroup_of_statedClassicalModel_POmegaMinus T n ℓ f hm).2
  haveI : NeZero (2 * n) := ⟨by omega⟩
  exact kdCharPAt_of_orthEquiv hℓ2 (d := 2 * n) (by omega) hnd
    (exists_nonzero_value _ (coordinate_model_intrinsic_minus hm K hK b c hirr e).1)
    (exists_two_pow_card_abelianization (minusIndexEquiv n hn1) (quadMinus n K b c) hab)
    (coordinateMinusWitnessEquiv K hn1 b c e) hS

theorem kdCharPAt_B (q : TauCeti.PrimePower) (r : ℕ) (hv : (TauCeti.LieTypeIndex.B r q).Valid)
    (hr3 : 3 ≤ r) {p : ℕ} (hp2 : p ≠ 2) (hpq : p = q.p) :
    KDCharPAt p (TauCeti.CFSGIndex.lie ⟨.B r q, hv⟩).Group := by
  have hqp2 : q.p ≠ 2 := hpq ▸ hp2
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hqp2 hr3
    (MulEquiv.refl (TauCeti.ValidLieTypeIndex.Group ⟨.B r q, hv⟩))
  subst hpq
  exact kdCharPAt_of_model_POmegaOdd hm

theorem kdCharPAt_D (q : TauCeti.PrimePower) (r : ℕ) (hv : (TauCeti.LieTypeIndex.D r q).Valid)
    {p : ℕ} (hp2 : p ≠ 2) (hpq : p = q.p) :
    KDCharPAt p (TauCeti.CFSGIndex.lie ⟨.D r q, hv⟩).Group := by
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv
    (MulEquiv.refl (TauCeti.ValidLieTypeIndex.Group ⟨.D r q, hv⟩))
  subst hpq
  exact kdCharPAt_of_model_POmegaPlus hm hp2

theorem kdCharPAt_twistedD (q : TauCeti.PrimePower) (r : ℕ)
    (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid) {p : ℕ} (hp2 : p ≠ 2) (hpq : p = q.p) :
    KDCharPAt p (TauCeti.CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group := by
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv
    (MulEquiv.refl (TauCeti.ValidLieTypeIndex.Group ⟨.twistedD r q, hv⟩))
  subst hpq
  exact kdCharPAt_of_model_POmegaMinus hm hp2

end Families

end CFSG.HardMathSupport.Dickson.KD
