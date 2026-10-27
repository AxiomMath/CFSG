module

public import CFSG.ClassicalInvolution.Q3.Q3MFODSpin
public import CFSG.ClassicalInvolution.Q3.Q3MFODSimE
public import CFSG.ClassicalInvolution.Q3.Q3OTCplx
public import CFSG.ClassicalInvolution.Q3.Q3NMOrth
public import CFSG.ClassicalInvolution.Q3.Q3OTDict

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Q3.Q3MFOD
  CFSG.ClassicalInvolution.Q3.Q3OT CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.RouteD.TWZ

section Data

variable {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm F (ι → F)}

theorem exists_sim_data (hF3 : Nat.card F = 3) [Group.IsPerfect (spinGroup Q)]
    (hlift : LiftSim Q (QuotientGroup.mk' (Subgroup.center (spinGroup Q))))
    (ρ : MulAut (spinGroup Q ⧸ Subgroup.center (spinGroup Q))) (hρ2 : ρ * ρ = 1) :
    ∃ (α : MulAut (spinGroup Q)) (a : (ι → F) ≃ₗ[F] (ι → F)) (μ : F),
      μ ≠ 0 ∧ (∀ v, Q (a v) = μ * Q v) ∧
      (∀ x, spinAction Q (α x) = a * spinAction Q x * a⁻¹) ∧
      autToCentralQuotient (spinGroup Q) α = ρ ∧ α * α = 1 := by
  classical
  set ψ : spinGroup Q →* spinGroup Q ⧸ Subgroup.center (spinGroup Q) :=
    QuotientGroup.mk' (Subgroup.center (spinGroup Q)) with hψ
  have hψs : Function.Surjective ψ := QuotientGroup.mk'_surjective _
  obtain ⟨α, hαψ, A, φ, μ, hsim, hmat⟩ := hlift (autRange ψ hψs ρ)
  have hαρ : ∀ x, ψ (α x) = ρ (ψ x) := fun x => congrArg Subtype.val (hαψ x)
  have hφ := ringEquiv_eq_refl_of_card_three hF3 φ
  subst hφ
  have hmat' : ∀ x, spinMatrix Q (α x) = A * spinMatrix Q x * A⁻¹ := by
    intro x
    rw [hmat x, glFieldEquiv_refl]
  set a : (ι → F) ≃ₗ[F] (ι → F) := glLin A with ha
  have hθα : ∀ x, spinAction Q (α x) = a * spinAction Q x * a⁻¹ := by
    intro x
    rw [← glLin_spinMatrix, hmat', map_mul, map_mul, map_inv, glLin_spinMatrix]
  have hsim' : ∀ v, Q (a v) = μ * Q v := by
    intro v
    have := hsim v
    simpa [ha, glLin_apply] using this
  have hρα : autToCentralQuotient (spinGroup Q) α = ρ := by
    refine MulEquiv.ext fun xb => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
    rw [autToCentralQuotient_mk]
    exact hαρ x
  have hα2 : α * α = 1 := by
    have hc : ∀ s ∈ (⊤ : Subgroup (spinGroup Q)),
        s⁻¹ * (α * α) s ∈ Subgroup.center (spinGroup Q) := by
      intro s _
      have h1 : ψ (α (α s)) = ψ s := by
        rw [hαρ, hαρ]
        have := congrArg (fun m : MulAut (spinGroup Q ⧸ Subgroup.center (spinGroup Q)) =>
          m (ψ s)) hρ2
        simpa using this
      exact QuotientGroup.eq.mp h1.symm
    have hfix := alpha_fixes_commutators (α * α) hc
    have hP : ⁅(⊤ : Subgroup (spinGroup Q)), (⊤ : Subgroup (spinGroup Q))⁆ =
        (⊤ : Subgroup (spinGroup Q)) := by
      rw [← commutator_def]
      exact Group.IsPerfect.commutator_eq_top
    refine MulEquiv.ext fun s => ?_
    exact hfix s (by rw [hP]; exact Subgroup.mem_top s)
  exact ⟨α, a, (μ : F), μ.ne_zero, hsim', hθα, hρα, hα2⟩

end Data

section Cases

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

theorem sim_cases4 (hF3 : Nat.card F = 3) (hQ : (polarBilin Q).Nondegenerate)
    (h3 : 3 ≤ Module.finrank F V) {a : V ≃ₗ[F] V} {μ : F} (hμ : μ ≠ 0)
    (hsim : ∀ v, Q (a v) = μ * Q v)
    (hcomm : ∀ h ∈ elementaryGroup Q, a * a * h = h * (a * a)) :
    (μ = 1 ∨ μ = -1) ∧ (a * a = 1 ∨ ∀ v, a (a v) = -v) := by
  have hodd : Odd (Nat.card F) := by rw [hF3]; decide
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  have hμ1 : μ = 1 ∨ μ = -1 := by
    rcases cases_of_card_three hF3 μ with h | h | h
    · exact absurd h hμ
    · exact Or.inl h
    · exact Or.inr h
  have hμ2 : μ * μ = 1 := by
    rcases hμ1 with h | h <;> rw [h] <;> ring
  have haO : a * a ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [LinearEquiv.mul_apply, hsim, hsim, ← mul_assoc, hμ2, one_mul]
  obtain ⟨c, hc⟩ := exists_smul_of_commute_elementary hodd hQ h3 haO (fun h hh => hcomm h hh)
  have hc' : ∀ v, a (a v) = c • v := fun v => hc v
  have hc0 : c ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    apply hv
    have h1 : a (a v) = 0 := by rw [hc', h0, zero_smul]
    exact a.injective (a.injective (by rw [h1, map_zero, map_zero]))
  refine ⟨hμ1, ?_⟩
  rcases cases_of_card_three hF3 c with h0 | hc1 | hc1
  · exact absurd h0 hc0
  · left
    refine LinearEquiv.ext fun v => ?_
    rw [LinearEquiv.mul_apply, hc', hc1, one_smul]
    rfl
  · right
    intro v
    rw [hc', hc1, neg_one_smul]

end Cases

section Main

variable {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm F (ι → F)}

theorem fixedOddFree_of_spin3 [Finite (spinGroup Q)] [Group.IsPerfect (spinGroup Q)]
    (hF3 : Nat.card F = 3) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 6 ≤ Module.finrank F (ι → F)) (hrange : (spinAction Q).range = elementaryGroup Q)
    (hEq : elementaryGroup Q = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hlift : LiftSim Q (QuotientGroup.mk' (Subgroup.center (spinGroup Q))))
    (hquasi : CFSG.Open.IsQuasisimple (spinGroup Q))
    (hZ2 : IsPGroup 2 (Subgroup.center (spinGroup Q)))
    (hneg : ∀ (a : (ι → F) ≃ₗ[F] (ι → F)) (hg : ∀ v, Q (a v) = (-1 : F) * Q v),
      (a * a = 1 ∨ ∀ v, a (a v) = -v) →
      oddCoreIn (fixedSubgroup (autToCentralQuotient ↥(elementaryGroup Q)
        (conjES Q hEq (neg_ne_zero.mpr one_ne_zero) hg))) = ⊥) :
    FixedOddFree (spinGroup Q ⧸ Subgroup.center (spinGroup Q)) := by
  classical
  intro ρ hρ2
  obtain ⟨α, a, μ, hμ, hsim, hα, hαρ, hα2⟩ := exists_sim_data hF3 hlift ρ hρ2
  rw [← hαρ]
  have hcomm : ∀ h ∈ elementaryGroup Q, a * a * h = h * (a * a) := by
    intro h hh
    rw [← hrange] at hh
    obtain ⟨s, rfl⟩ := hh
    have hαα : α (α s) = s := by
      have := congrArg (fun m : MulAut (spinGroup Q) => m s) hα2
      simpa using this
    have e : spinAction Q s = a * (a * spinAction Q s * a⁻¹) * a⁻¹ := by
      rw [← hα s, ← hα (α s), hαα]
    calc a * a * spinAction Q s
        = (a * (a * spinAction Q s * a⁻¹) * a⁻¹) * (a * a) := by group
      _ = spinAction Q s * (a * a) := by rw [← e]
  have hlift' : ∀ (g : (ι → F) ≃ₗ[F] (ι → F)) (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q),
      (∀ x, spinAction Q (α x) = g * spinAction Q x * g⁻¹) →
      oddCoreIn (fixedSubgroup (autToCentralQuotient ↥(elementaryGroup Q) (conjE Q g hgO))) = ⊥ →
      oddCoreIn (fixedSubgroup (autToCentralQuotient (spinGroup Q) α)) = ⊥ :=
    fun g hgO hg hN => oddCoreIn_fixed_of_lift hrange (θ := MonoidHom.id (spinGroup Q))
      Function.surjective_id (by rw [MonoidHom.ker_id]; exact bot_le) α α (fun s => rfl) hgO hg hN
  obtain ⟨hμ1 | hμ1, haa⟩ := sim_cases4 hF3 hQ (by omega) hμ hsim hcomm
  ·
    have haO : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
      rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
      intro v
      rw [hsim, hμ1, one_mul]
    rcases haa with haa | haa
    · by_cases hs : a ∈ scalars F (ι → F)
      ·
        obtain ⟨c, hc⟩ := mem_scalars.mp hs
        have hcomm_a : ∀ g : (ι → F) ≃ₗ[F] (ι → F), a * g = g * a := fun g => by
          refine LinearEquiv.ext fun v => ?_
          rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hc, hc, map_smul]
        have hone : autToCentralQuotient (spinGroup Q) α = 1 := by
          refine MulEquiv.ext fun xb => ?_
          obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
          rw [autToCentralQuotient_mk, MulAut.one_apply]
          refine QuotientGroup.eq.mpr (ker_spinAction_le_center Q ?_)
          rw [MonoidHom.mem_ker, map_mul, map_inv, hα, hcomm_a (spinAction Q x),
            mul_inv_cancel_right, inv_mul_cancel]
        rw [hone]
        have hf : fixedSubgroup (1 : MulAut (spinGroup Q ⧸ Subgroup.center (spinGroup Q))) =
            ⊤ := by
          ext x
          simp [mem_fixedSubgroup_iff]
        rw [hf]
        have h := CFSG.ClassicalInvolution.Q3.oddCoreIn_range_eq_bot_of_isQuasisimple
          (QuotientGroup.mk' (Subgroup.center (spinGroup Q))) hquasi hZ2
          (by rw [QuotientGroup.ker_mk'])
        rwa [MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h
      · exact hlift' a haO hα
          (oddCoreIn_fixed_eq_bot_of_involution hF3 hQ (by omega) haO haa hs)
    · have hOE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
          TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤ elementaryGroup Q := hEq.ge
      exact hlift' a haO hα (oddCoreIn_fixed_eq_bot_of_cplx hF3 hQ hdim hOE haO haa)
  ·
    have hg : ∀ v, Q (a v) = (-1 : F) * Q v := fun v => by rw [hsim, hμ1]
    have hmem : ∀ s : spinGroup Q, spinAction Q s ∈ elementaryGroup Q := fun s => by
      rw [← hrange]
      exact ⟨s, rfl⟩
    refine oddCoreIn_fixed_of_lift_aut hrange (θ := MonoidHom.id (spinGroup Q))
      Function.surjective_id (by rw [MonoidHom.ker_id]; exact bot_le) α α (fun s => rfl)
      (conjES Q hEq (neg_ne_zero.mpr one_ne_zero) hg) (fun s => ?_) (hneg a hg haa)
    refine Subtype.ext ?_
    rw [conjES_apply]
    exact (hα s).symm

end Main

end CFSG.ClassicalInvolution.Q3.TL4
