module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFRed
public import CFSG.ClassicalInvolution.Q3.Q3MFODPlus

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.ModelFacts.Orth15
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1

local notation "Q₄" => quadPlus 4 (GaloisField 3 1)

@[expose] def D4CplxR : Prop :=
  ∀ (hE : elementaryGroup Q₄ = ⁅TauCeti.QuadraticMap.orthogonalGroup Q₄,
      TauCeti.QuadraticMap.orthogonalGroup Q₄⁆)
    (a : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃))
    (hg : ∀ v, Q₄ (a v) = (-1 : 𝔽₃) * Q₄ v), (∀ v, a (a v) = -v) →
    oddCoreIn (fixedSubgroup (autToCentralQuotient ↥(elementaryGroup Q₄)
      (Q3MFOD.conjES Q₄ hE (neg_ne_zero.mpr one_ne_zero) hg))) = ⊥

@[expose] def D4OutCentR : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → LieModel S .POmegaPlus 4 3 1 →
    ∀ f : MulAut S, f * f = 1 → f ∉ innSubgroup S → ∀ β : MulAut S, Odd (orderOf β) →
      β * f = f * β → (∀ x ∈ fixedSubgroup f, β x = x) → β ∈ innSubgroup S

@[expose] def D4OuterAutOddFreeR : Prop := D4CplxR ∧ D4OutCentR

section Crit

variable {X : Type} [Group X] [Finite X]

theorem autOddFreeOn_of_fixed_centralizing (P : MulAut X → Prop) (hZ : Subgroup.center X = ⊥)
    (hfix : ∀ σ : MulAut X, P σ → σ * σ = 1 → oddCoreIn (fixedSubgroup σ) = ⊥)
    (hodd : ∀ f : MulAut X, P f → f * f = 1 → ∀ β : MulAut X, Odd (orderOf β) → β * f = f * β →
      (∀ x ∈ fixedSubgroup f, β x = x) → β ∈ innSubgroup X) :
    AutOddFreeOn X P := by
  intro 𝒳 hinn f hP hf
  have hf2 := mul_self_eq_one_of_orderOf_eq_two' hf
  have hf2' : (f : MulAut X) * f = 1 := congrArg Subtype.val hf2
  refine oddCoreIn_eq_bot_of_comm_mem (I := (innSubgroup X).subgroupOf 𝒳) f
    (oddCoreIn_centralizer_inner_eq_bot hZ 𝒳 hinn f hf2 (hfix _ hP hf2')) ?_
  intro g hg hcomm
  have hodd_g : Odd (orderOf (g : MulAut X)) := by
    rw [Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat (odd_card_oddCoreIn (Subgroup.centralizer ({f} : Set 𝒳)))
      (Subgroup.orderOf_dvd_natCard _ hg)
  have hgf : (g : MulAut X) * f = f * g :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (oddCoreIn_le _ hg))
  refine Subgroup.mem_subgroupOf.mpr (hodd f hP hf2' g hodd_g hgf ?_)
  intro x hxf
  have hxf' : (f : MulAut X) x = x := hxf
  have hmem : (⟨MulAut.conj x, hinn ⟨x, rfl⟩⟩ : 𝒳) ∈
      Subgroup.centralizer ({f} : Set 𝒳) ⊓ (innSubgroup X).subgroupOf 𝒳 := by
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext ?_),
      Subgroup.mem_subgroupOf.mpr ⟨x, rfl⟩⟩
    show MulAut.conj x * (f : MulAut X) = f * MulAut.conj x
    have h := mul_conj_mul_inv (f : MulAut X) x
    rw [hxf'] at h
    calc MulAut.conj x * (f : MulAut X) = ((f : MulAut X) * MulAut.conj x * (f : MulAut X)⁻¹) *
          (f : MulAut X) := by rw [h]
      _ = f * MulAut.conj x := by group
  have h1 := congrArg Subtype.val (hcomm _ hmem)
  have h2 : (g : MulAut X) * MulAut.conj x = MulAut.conj x * (g : MulAut X) := h1
  have h3 : MulAut.conj ((g : MulAut X) x) = MulAut.conj x := by
    rw [← mul_conj_mul_inv, h2]
    group
  exact conj_injective_of_center_eq_bot hZ h3

end Crit

section Spin

variable {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm F (ι → F)}

theorem oddCoreIn_fixed_of_sim_spin [Finite (spinGroup Q)] [Group.IsPerfect (spinGroup Q)]
    (hF3 : Nat.card F = 3) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 6 ≤ Module.finrank F (ι → F)) (hrange : (spinAction Q).range = elementaryGroup Q)
    (hEq : elementaryGroup Q = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hquasi : CFSG.Open.IsQuasisimple (spinGroup Q))
    (hZ2 : IsPGroup 2 (Subgroup.center (spinGroup Q)))
    (hneg : ∀ (a : (ι → F) ≃ₗ[F] (ι → F)) (hg : ∀ v, Q (a v) = (-1 : F) * Q v),
      (a * a = 1 ∨ ∀ v, a (a v) = -v) →
      oddCoreIn (fixedSubgroup (autToCentralQuotient ↥(elementaryGroup Q)
        (Q3MFOD.conjES Q hEq (neg_ne_zero.mpr one_ne_zero) hg))) = ⊥)
    (α : MulAut (spinGroup Q)) (hα2 : α * α = 1) {a : (ι → F) ≃ₗ[F] (ι → F)} {μ : F}
    (hμ : μ ≠ 0) (hsim : ∀ v, Q (a v) = μ * Q v)
    (hα : ∀ x, spinAction Q (α x) = a * spinAction Q x * a⁻¹) :
    oddCoreIn (fixedSubgroup (autToCentralQuotient (spinGroup Q) α)) = ⊥ := by
  classical
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
    fun g hgO hg hN => Q3OT.oddCoreIn_fixed_of_lift hrange (θ := MonoidHom.id (spinGroup Q))
      Function.surjective_id (by rw [MonoidHom.ker_id]; exact bot_le) α α (fun s => rfl) hgO hg hN
  obtain ⟨hμ1 | hμ1, haa⟩ := sim_cases4 hF3 hQ (by omega) hμ hsim hcomm
  · have haO : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
      rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
      intro v
      rw [hsim, hμ1, one_mul]
    rcases haa with haa | haa
    · by_cases hs : a ∈ scalars F (ι → F)
      · obtain ⟨c, hc⟩ := mem_scalars.mp hs
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
    · exact hlift' a haO hα (Q3OT.oddCoreIn_fixed_eq_bot_of_cplx hF3 hQ hdim hEq.ge haO haa)
  · have hg : ∀ v, Q (a v) = (-1 : F) * Q v := fun v => by rw [hsim, hμ1]
    refine Q3MFOD.oddCoreIn_fixed_of_lift_aut hrange (θ := MonoidHom.id (spinGroup Q))
      Function.surjective_id (by rw [MonoidHom.ker_id]; exact bot_le) α α (fun s => rfl)
      (Q3MFOD.conjES Q hEq (neg_ne_zero.mpr one_ne_zero) hg) (fun s => ?_) (hneg a hg haa)
    refine Subtype.ext ?_
    rw [Q3MFOD.conjES_apply]
    exact (hα s).symm

end Spin

section D4


theorem fixedOddFree_spinPlus4 (hC : D4CplxR) [Finite (spinGroup Q₄)]
    (hZ2 : IsPGroup 2 (Subgroup.center (spinGroup Q₄))) :
    FixedOddFree (spinGroup Q₄ ⧸ Subgroup.center (spinGroup Q₄)) := by
  classical
  intro ρ hρ2
  have hn3 : 3 ≤ 4 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF3 : Nat.card 𝔽₃ = 3 := ModelFacts.TG3.natCard_galoisField_three
  have : Group.IsPerfect (spinGroup Q₄) := isPerfect_spinGroup_quadPlus hn3
  have hQ := nondegenerate_polarBilin_quadPlus 4 𝔽₃
  have hrange := range_spinAction_quadPlus (K := 𝔽₃) hn3
  have hEq := (commutator_orthogonalGroup_quadPlus (K := 𝔽₃) hn3).symm
  have hdim : 6 ≤ Module.finrank 𝔽₃ (Fin 4 ⊕ Fin 4 → 𝔽₃) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    norm_num
  obtain ⟨hSL, hSLZ⟩ := sl3_facts (n := 4) (by norm_num)
  obtain ⟨α, hα⟩ := Q3PP.exists_lift_plus4 ρ
  have hρeq : ρ = autToCentralQuotient (spinGroup Q₄) α := by
    refine MulEquiv.ext fun xb => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
    rw [autToCentralQuotient_mk, hα]
  have hα2 := Q3PP.mul_self_eq_one_of_lift α ρ hρ2 hα
  obtain ⟨σ, -, hpres⟩ := Q3MFOD.exists_pres_conj α hα2
  have hα'2 : σ * α * σ⁻¹ * (σ * α * σ⁻¹) = 1 := by
    calc σ * α * σ⁻¹ * (σ * α * σ⁻¹) = σ * (α * α) * σ⁻¹ := by group
      _ = 1 := by rw [hα2]; group
  obtain ⟨a, μ, hμ, hsim, hαa⟩ := Q3MFOD.exists_sim_of_mat3 hF3 (σ * α * σ⁻¹)
    (Q3MFOD.spin_plus4_sim_of_family (σ * α * σ⁻¹) (Q3MFOD.descAut (σ * α * σ⁻¹))
      (Q3MFOD.descAut_apply (σ * α * σ⁻¹)) hpres)
  have h' := oddCoreIn_fixed_of_sim_spin hF3 hQ hdim hrange hEq
    (ModelFacts.open_isQuasisimple (isQuasisimple_spinGroup_quadPlus hn3)) hZ2
    (fun a hg ha => ha.elim
      (fun ha => oddCoreIn_fixed_conjES_of_sim_involution_n hF3 (by norm_num) hSL hSLZ hQ hEq ha hg)
      (fun ha => hC hEq a hg ha))
    (σ * α * σ⁻¹) hα'2 hμ hsim hαa
  rw [hρeq]
  exact Q3PP.oddCoreIn_fixed_of_conj_transfer σ α h'

theorem outerFixedOddFree_d4 (hC : D4CplxR) : OuterFixedOddFree .POmegaPlus 4 := by
  intro S _ _ _ hS σ hσ _
  have hFT : IsFundTag StatedLieTag.POmegaPlus := trivial
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  obtain ⟨ψ, hψ, hker⟩ :=
    Upgrade.lieModelCentralCover _ 4 3 1 Nat.prime_three (by norm_num) hFT hadm S hS
  obtain ⟨hSq, -, -, -, -⟩ := Q3NM.centralQuotientData Nat.prime_three hFT hadm S ψ hψ hker
  have hZ := center_eq_bot_of_isQuasisimple hSq
  have : Group.IsPerfect (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).K :=
    ⟨((ModelFacts.modelClauseZero .POmegaPlus 4 3 1 Nat.prime_three hFT hadm).1).1⟩
  have hfz := modelFiniteCenterTwoGroup3 .POmegaPlus 4 Nat.prime_three hFT hadm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn3 : 3 ≤ 4 := by norm_num
  have key : ∀ M : LieUniversal, M = ⟨spinGroup Q₄, plusDatum 4 𝔽₃ hn3⟩ →
      Finite M.K ∧ IsPGroup 2 (Subgroup.center M.K) →
      FixedOddFree (M.K ⧸ Subgroup.center M.K) := by
    intro M hM hMf
    subst hM
    have := hMf.1
    exact fixedOddFree_spinPlus4 hC hMf.2
  have hM : modelUniv .POmegaPlus 4 3 1 Nat.prime_three = ⟨spinGroup Q₄, plusDatum 4 𝔽₃ hn3⟩ := by
    simp only [modelUniv, CFSG.LieType.Universal.lieUniversal, hn3, ↓reduceDIte]
  let e : S ≃* (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).K ⧸
      Subgroup.center (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans
      (Q3NM.centralQuotientIso ψ hψ hker).symm
  exact Q3MFO.fixedOddFree_of_mulEquiv e (key _ hM hfz) σ hσ

theorem autOddFree_d4_of (hD4 : D4OuterAutOddFreeR) {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hS : LieModel S .POmegaPlus 4 3 1) : AutOddFree S := by
  have hFT : IsFundTag StatedLieTag.POmegaPlus := trivial
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  obtain ⟨ψ, hψ, hker⟩ :=
    Upgrade.lieModelCentralCover _ 4 3 1 Nat.prime_three (by norm_num) hFT hadm S hS
  obtain ⟨hSq, -, -, -, -⟩ := Q3NM.centralQuotientData Nat.prime_three hFT hadm S ψ hψ hker
  have hZ := center_eq_bot_of_isQuasisimple hSq
  have hout : AutOddFreeOn S (fun f => f ∉ innSubgroup S) :=
    autOddFreeOn_of_fixed_centralizing _ hZ
      (fun σ hσ hσ2 => outerFixedOddFree_d4 hD4.1 S inferInstance hS σ hσ2 hσ)
      (fun f hf hf2 β hβ hβf hfix => hD4.2 S inferInstance hS f hf2 hf β hβ hβf hfix)
  have h := ((autOddFreeInner_d4 hS).toOn).or hout
  intro 𝒳 hinn f hf
  exact h 𝒳 hinn f (em _) hf

theorem d4OuterAutOddFree_of (hD4 : D4OuterAutOddFreeR) : D4OuterAutOddFree :=
  fun _ _ _ _ hS => (autOddFree_d4_of hD4 hS).on _

theorem omegaAutOddFreeR_of (hSp : OuterFixedOddFree .PSp 2) (hL : OuterFixedOddFree .PSL 4)
    (hU : OuterFixedOddFree .PSU 4) (hD4 : D4OuterAutOddFreeR) : OmegaAutOddFreeR :=
  omegaAutOddFreeR_of_small hSp hL hU (d4OuterAutOddFree_of hD4)

end D4

end CFSG.ClassicalInvolution.Q3.TL4
