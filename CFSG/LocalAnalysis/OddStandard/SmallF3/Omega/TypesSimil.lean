module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesInvol

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] def IsSimilitude (Q : QuadraticForm (ZMod 3) V) (σ : V ≃ₗ[ZMod 3] V)
    (c : (ZMod 3)ˣ) : Prop :=
  ∀ v : V, Q (σ v) = (c : ZMod 3) * Q v

theorem aux_isSimilitude_one :
    IsSimilitude Q (1 : V ≃ₗ[ZMod 3] V) 1 := by
  intro v
  simp

theorem aux_isSimilitude_mul {σ τ : V ≃ₗ[ZMod 3] V} {c d : (ZMod 3)ˣ}
    (hσ : IsSimilitude Q σ c) (hτ : IsSimilitude Q τ d) :
    IsSimilitude Q (σ * τ) (c * d) := by
  intro v
  rw [LinearEquiv.mul_apply, hσ (τ v), hτ v, Units.val_mul, mul_assoc]

theorem aux_isSimilitude_inv {σ : V ≃ₗ[ZMod 3] V} {c : (ZMod 3)ˣ}
    (hσ : IsSimilitude Q σ c) : IsSimilitude Q σ⁻¹ c⁻¹ := by
  intro v
  have h := hσ (σ.symm v)
  rw [LinearEquiv.apply_symm_apply] at h
  simp only [LinearEquiv.coe_inv]
  rw [h, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

theorem aux_conj_mul {G : Type*} [Group G] (a b c : G) :
    a * (b * c) * a⁻¹ = (a * b * a⁻¹) * (a * c * a⁻¹) := by
  group

theorem aux_unit_eq_one_or_neg_one (c : (ZMod 3)ˣ) : c = 1 ∨ c = -1 := by
  revert c
  decide

theorem aux_toSign_neg_one : toSign (-1 : (ZMod 3)ˣ) = -1 := by decide

theorem aux_quadSign_map_of_similitude {σ : V ≃ₗ[ZMod 3] V} {c : (ZMod 3)ˣ}
    (hσ : IsSimilitude Q σ c) {N : Submodule (ZMod 3) V}
    (hN : (Q.restrict N).Nondegenerate) :
    quadSign (Q.restrict (N.map (σ : V →ₗ[ZMod 3] V))) =
      toSign c ^ Module.finrank (ZMod 3) N * quadSign (Q.restrict N) := by
  let M : Submodule (ZMod 3) V := N.map (σ : V →ₗ[ZMod 3] V)
  rcases aux_unit_eq_one_or_neg_one c with hc | hc
  · have hiso : (Q.restrict N).Equivalent (Q.restrict M) :=
      ⟨{ toLinearEquiv := (σ : V ≃ₗ[ZMod 3] V).ofSubmodules N M rfl
         map_app' := by
           intro x
           change Q (σ (x : V)) = Q (x : V)
           rw [hσ (x : V), hc]
           simp }⟩
    rw [hc, map_one, one_pow, one_mul]
    exact (quadSign_congr hN hiso).symm
  · have hnegnd : (-(Q.restrict N)).Nondegenerate := by
      have hneg : -(Q.restrict N) =
          ((-1 : (ZMod 3)ˣ) : ZMod 3) • (Q.restrict N) := by
        ext x
        simp
      rw [hneg]
      exact (QuadraticMap.nondegenerate_smul_iff ((-1 : (ZMod 3)ˣ).isUnit)
        (Q.restrict N)).mpr hN
    have hiso : (-(Q.restrict N)).Equivalent (Q.restrict M) :=
      ⟨{ toLinearEquiv := (σ : V ≃ₗ[ZMod 3] V).ofSubmodules N M rfl
         map_app' := by
           intro x
           change Q (σ (x : V)) = -(Q.restrict N) x
           rw [hσ (x : V), hc]
           simp }⟩
    rw [hc, aux_toSign_neg_one]
    rw [← quadSign_congr hnegnd hiso, quadSign_neg hN]

@[expose] def simGroup (Q : QuadraticForm (ZMod 3) V) : Subgroup (V ≃ₗ[ZMod 3] V) where
  carrier := {σ | ∃ c : (ZMod 3)ˣ, IsSimilitude Q σ c}
  mul_mem' := by
    rintro σ τ ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c * d, aux_isSimilitude_mul hc hd⟩
  one_mem' := ⟨1, aux_isSimilitude_one⟩
  inv_mem' := by
    rintro σ ⟨c, hc⟩
    exact ⟨c⁻¹, aux_isSimilitude_inv hc⟩

theorem isSimilitude_one_iff {σ : V ≃ₗ[ZMod 3] V} :
    IsSimilitude Q σ 1 ↔ σ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  constructor
  · intro h
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    simpa using h v
  · intro h
    intro v
    simpa using TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup h v

theorem orthogonalGroup_le_simGroup : TauCeti.QuadraticMap.orthogonalGroup Q ≤ simGroup Q := by
  intro σ h
  exact ⟨1, isSimilitude_one_iff.mpr h⟩

theorem eq_of_isSimilitude (hQ : Q.Nondegenerate) (h0 : 0 < Module.finrank (ZMod 3) V)
    {σ : V ≃ₗ[ZMod 3] V} {c c' : (ZMod 3)ˣ} (h : IsSimilitude Q σ c) (h' : IsSimilitude Q σ c') :
    c = c' := by
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos h0
  obtain ⟨v, hv⟩ := hQ.exists_isUnit
  have hv' : Q v ≠ 0 := hv.ne_zero
  have heq : (c : ZMod 3) * Q v = (c' : ZMod 3) * Q v := (h v).symm.trans (h' v)
  exact Units.ext (mul_right_cancel₀ hv' heq)

theorem aux_mem_subgroupOf_iff {σ : simGroup Q} {c : (ZMod 3)ˣ}
    (hQ : Q.Nondegenerate) (h0 : 0 < Module.finrank (ZMod 3) V)
    (hσ : IsSimilitude Q (σ : V ≃ₗ[ZMod 3] V) c) :
    σ ∈ (TauCeti.QuadraticMap.orthogonalGroup Q).subgroupOf (simGroup Q) ↔ c = 1 := by
  rw [Subgroup.mem_subgroupOf, ← isSimilitude_one_iff]
  constructor
  · intro hmem
    exact eq_of_isSimilitude hQ h0 hσ hmem
  · intro hc
    rw [← hc]
    exact hσ

@[expose] noncomputable def simConj {σ : V ≃ₗ[ZMod 3] V} {c : (ZMod 3)ˣ}
    (hσ : IsSimilitude Q σ c) (t : OGroup Q) : OGroup Q :=
  ⟨σ * (t : V ≃ₗ[ZMod 3] V) * σ⁻¹, by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    change Q ((σ * (t : V ≃ₗ[ZMod 3] V) * σ⁻¹) v) = Q v
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    simp only [LinearEquiv.coe_inv]
    rw [hσ ((t : V ≃ₗ[ZMod 3] V) (σ.symm v)),
      TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup t.2 (σ.symm v)]
    rw [← hσ (σ.symm v), LinearEquiv.apply_symm_apply]⟩

theorem coe_simConj {σ : V ≃ₗ[ZMod 3] V} {c : (ZMod 3)ˣ} (hσ : IsSimilitude Q σ c)
    (t : OGroup Q) :
    ((simConj hσ t : OGroup Q) : V ≃ₗ[ZMod 3] V) = σ * (t : V ≃ₗ[ZMod 3] V) * σ⁻¹ :=
  rfl

theorem simConj_mul {σ : V ≃ₗ[ZMod 3] V} {c : (ZMod 3)ˣ} (hσ : IsSimilitude Q σ c)
    (s t : OGroup Q) : simConj hσ (s * t) = simConj hσ s * simConj hσ t := by
  apply Subtype.ext
  simp only [coe_simConj, Subgroup.coe_mul]
  exact aux_conj_mul σ (s : V ≃ₗ[ZMod 3] V) (t : V ≃ₗ[ZMod 3] V)

theorem commSp_simConj {σ : V ≃ₗ[ZMod 3] V} {c : (ZMod 3)ˣ} (hσ : IsSimilitude Q σ c)
    (t : OGroup Q) : commSp (simConj hσ t) = (commSp t).map (σ : V →ₗ[ZMod 3] V) := by
  rw [commSp, coe_simConj]
  exact CFSG.RankThree.OrthogonalInvolutions.commSpace_conj σ (t : V ≃ₗ[ZMod 3] V)

theorem invType_simConj (hQ : Q.Nondegenerate) {σ : V ≃ₗ[ZMod 3] V} {c : (ZMod 3)ˣ}
    (hσ : IsSimilitude Q σ c) {t : OGroup Q} (htt : t * t = 1) :
    simConj hσ t * simConj hσ t = 1 ∧
      invType (simConj hσ t) = (invDim t, toSign c ^ invDim t * invSign t) := by
  have hsq : simConj hσ t * simConj hσ t = 1 := by
    have h1 : simConj hσ (t * t) = simConj hσ t * simConj hσ t := simConj_mul hσ t t
    rw [htt] at h1
    rw [← h1]
    apply Subtype.ext
    rw [coe_simConj, Subgroup.coe_one, mul_one, mul_inv_cancel]
  refine ⟨hsq, ?_⟩
  have hdim : invDim (simConj hσ t) = invDim t := by
    rw [invDim, invDim, commSp_simConj, LinearEquiv.finrank_map_eq]
  have hsign : invSign (simConj hσ t) = toSign c ^ invDim t * invSign t := by
    have hcomm := commSp_simConj hσ t
    rw [invSign, invSign]
    rw [show quadSign (Q.restrict (commSp (simConj hσ t))) =
        quadSign (Q.restrict ((commSp t).map (σ : V →ₗ[ZMod 3] V))) from
      congrArg (fun N : Submodule (ZMod 3) V => quadSign (Q.restrict N)) hcomm]
    exact aux_quadSign_map_of_similitude hσ (nondegenerate_restrict_commSp hQ htt)
  change (invDim (simConj hσ t), invSign (simConj hσ t)) =
    (invDim t, toSign c ^ invDim t * invSign t)
  rw [hdim, hsign]

theorem invType_simConj_neg_one_of_odd (hQ : Q.Nondegenerate) {σ : V ≃ₗ[ZMod 3] V}
    (hσ : IsSimilitude Q σ (-1)) {t : OGroup Q} (htt : t * t = 1) (hr : Odd (invDim t)) :
    invType (simConj hσ t) = (invDim t, -invSign t) := by
  have h := (invType_simConj hQ hσ htt).2
  rw [h]
  exact Prod.ext rfl (by rw [aux_toSign_neg_one, Odd.neg_one_pow hr, neg_one_mul])

theorem exists_isSimilitude_neg_one_iff (hQ : Q.Nondegenerate) :
    (∃ σ : V ≃ₗ[ZMod 3] V, IsSimilitude Q σ (-1)) ↔ Even (Module.finrank (ZMod 3) V) := by
  have hnegnd : (-Q).Nondegenerate := by
    have hneg : -Q = ((-1 : (ZMod 3)ˣ) : ZMod 3) • Q := by
      ext x
      simp
    rw [hneg]
    exact (QuadraticMap.nondegenerate_smul_iff ((-1 : (ZMod 3)ˣ).isUnit) Q).mpr hQ
  constructor
  · rintro ⟨σ, hσ⟩
    have hiso : (-Q).Equivalent Q :=
      ⟨{ toLinearEquiv := σ, map_app' := fun v => by
            change Q (σ v) = (-Q) v
            rw [hσ v]
            simp }⟩
    have hsign : quadSign (-Q) = quadSign Q := quadSign_congr hnegnd hiso
    have h1 : (-1 : ℤˣ) ^ Module.finrank (ZMod 3) V * quadSign Q = quadSign Q := by
      calc (-1 : ℤˣ) ^ Module.finrank (ZMod 3) V * quadSign Q
          = quadSign (-Q) := (quadSign_neg hQ).symm
        _ = quadSign Q := hsign
    have h2 : (-1 : ℤˣ) ^ Module.finrank (ZMod 3) V = 1 := by
      have h1' : (-1 : ℤˣ) ^ Module.finrank (ZMod 3) V * quadSign Q = 1 * quadSign Q := by
        rw [one_mul]
        exact h1
      exact mul_right_cancel h1'
    exact (neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤˣ) ≠ 1)).mp h2
  · intro hn
    have hsign : quadSign (-Q) = quadSign Q := by
      rw [quadSign_neg hQ, hn.neg_one_pow, one_mul]
    obtain ⟨e⟩ := equivalent_of_quadSign_eq hnegnd hQ rfl hsign
    refine ⟨e.toLinearEquiv, fun v => ?_⟩
    simpa using e.map_app v

theorem index_orthogonalGroup_subgroupOf_simGroup (hQ : Q.Nondegenerate)
    (h0 : 0 < Module.finrank (ZMod 3) V) :
    ((TauCeti.QuadraticMap.orthogonalGroup Q).subgroupOf (simGroup Q)).index =
      if Even (Module.finrank (ZMod 3) V) then 2 else 1 := by
  by_cases hn : Even (Module.finrank (ZMod 3) V)
  · rw [if_pos hn, Subgroup.index_eq_two_iff]
    obtain ⟨σ₀, hσ₀⟩ := (exists_isSimilitude_neg_one_iff hQ).mpr hn
    let a : simGroup Q := ⟨σ₀, ⟨-1, hσ₀⟩⟩
    refine ⟨a, fun b => ?_⟩
    obtain ⟨c, hc⟩ := b.2
    have hb : b ∈ (TauCeti.QuadraticMap.orthogonalGroup Q).subgroupOf (simGroup Q) ↔ c = 1 :=
      aux_mem_subgroupOf_iff hQ h0 hc
    have hba : b * a ∈ (TauCeti.QuadraticMap.orthogonalGroup Q).subgroupOf (simGroup Q) ↔
        c * (-1) = 1 := by
      apply aux_mem_subgroupOf_iff hQ h0
      rw [Subgroup.coe_mul]
      exact aux_isSimilitude_mul hc hσ₀
    rw [xor_iff_iff_not, hba, hb]
    rcases aux_unit_eq_one_or_neg_one c with hc1 | hc1 <;> rw [hc1] <;> decide
  · rw [if_neg hn]
    rw [Subgroup.index_eq_one]
    rw [eq_top_iff]
    intro σ _
    rw [Subgroup.mem_subgroupOf, ← isSimilitude_one_iff]
    obtain ⟨c, hc⟩ := σ.2
    rcases aux_unit_eq_one_or_neg_one c with hc1 | hc1
    · rw [← hc1]
      exact hc
    · exfalso
      exact hn ((exists_isSimilitude_neg_one_iff hQ).mp ⟨_, hc1 ▸ hc⟩)

end CFSG.OddStandard.SmallF3.Omega
