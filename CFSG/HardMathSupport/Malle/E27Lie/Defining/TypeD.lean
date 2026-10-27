module

public import CFSG.HardMathSupport.Malle.E27Lie.Defining.TypeDCoord
public import CFSG.HardMathSupport.Malle.Proving.E27SylowQuotient
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDOdd
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitSylow

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LieType.Universal.Spin CFSG.HardMathSupport.Foote.E27 CFSG.Assembly.LowTwoRank TauCeti

@[expose] def isometrySubgroup {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    (Q : (ι → F) → F) : Subgroup (GL ι F) where
  carrier := {A | ∀ v, Q ((A : Matrix ι ι F) *ᵥ v) = Q v}
  one_mem' := fun v => by simp
  mul_mem' := fun {A B} hA hB v => by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hA, hB]
  inv_mem' := fun {A} hA v => by
    have := hA ((↑A⁻¹ : Matrix ι ι F) *ᵥ v)
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec, eq_comm] at this

theorem statedOmega_le_isometrySubgroup {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type}
    [Field F] (Q : (ι → F) → F) : StatedOmega Q ≤ isometrySubgroup Q := by
  have hcl : Subgroup.closure {A : GL ι F | ∀ v, Q ((A : Matrix ι ι F) *ᵥ v) = Q v} ≤
      isometrySubgroup Q := Subgroup.closure_le _ |>.mpr fun A hA => hA
  refine le_trans (Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => ?_) hcl
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂)
    (Subgroup.inv_mem _ h₁)) (Subgroup.inv_mem _ h₂)

theorem sq_eq_one_of_mem_statedScalars {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type}
    [Field F] {Q : (ι → F) → F} (hQ : ∀ (c : F) v, Q (c • v) = c ^ 2 * Q v) {v₀ : ι → F}
    (hv₀ : Q v₀ ≠ 0) {g : GL ι F} (hg : g ∈ StatedOmega Q) (hs : g ∈ StatedScalars ι F) :
    g ^ 2 = 1 := by
  obtain ⟨c, rfl⟩ := hs
  have h1 := statedOmega_le_isometrySubgroup Q hg v₀
  have h2 : ((Matrix.GeneralLinearGroup.scalar ι c : GL ι F) : Matrix ι ι F) *ᵥ v₀ =
      (c : F) • v₀ := by
    ext i
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.mulVec_diagonal]
  rw [h2, hQ] at h1
  have hc2 : (c : F) ^ 2 = 1 := by
    have := mul_right_cancel₀ hv₀ (h1.trans (one_mul _).symm)
    exact this
  rw [← map_pow]
  have : c ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hc2, Units.val_one])
  rw [this, map_one]

theorem not_three_dvd_card_scalars_statedOmega {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type}
    [Field F] [Finite F] {Q : (ι → F) → F} (hQ : ∀ (c : F) v, Q (c • v) = c ^ 2 * Q v)
    {v₀ : ι → F} (hv₀ : Q v₀ ≠ 0) :
    ¬ 3 ∣ Nat.card ((StatedScalars ι F).subgroupOf (StatedOmega Q)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 ((StatedScalars ι F).subgroupOf (StatedOmega Q)) := fun x =>
    ⟨1, Subtype.ext (Subtype.ext (by
      have := sq_eq_one_of_mem_statedScalars hQ hv₀ (x : StatedOmega Q).2
        (Subgroup.mem_subgroupOf.mp x.2)
      simpa using this))⟩
  have : Finite (GL ι F) := inferInstance
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
  rw [hk]
  intro h3
  have := (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

theorem statedQuadPlus_smul (r : ℕ) {F : Type} [Field F] (c : F) (v : Fin r ⊕ Fin r → F) :
    StatedQuadPlus r F (c • v) = c ^ 2 * StatedQuadPlus r F v := by
  simp only [StatedQuadPlus, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem statedQuadPlus_ne_zero {r : ℕ} (hr : 1 ≤ r) (F : Type) [Field F] :
    StatedQuadPlus r F (Pi.single (Sum.inl ⟨0, by omega⟩) 1 + Pi.single (Sum.inr ⟨0, by omega⟩) 1) ≠
      0 := by
  rw [StatedQuadPlus, Finset.sum_eq_single ⟨0, by omega⟩]
  · simp
  · intro i _ hi
    simp [hi]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem false_of_pomegaPlus_model_char_three {X : Type} [Group X] [Finite X]
    {K R T : Subgroup X} {z : X} (h : E27Config X K R T z) (hz : z ∈ K) {r f : ℕ}
    (hcl : StatedClassicalModel K .POmegaPlus r 3 f) : False := by
  obtain ⟨⟨-, hf, hr⟩, F, _, _, hF, ⟨θ⟩⟩ := hcl
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP F 3 := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  have hK2 : ringChar F ≠ 2 := by rw [ringChar.eq F 3]; norm_num
  have hE := orthogonal_odd_derived_elementary hK2 (nondegenerate_polarBilin_quadPlus r F)
    ⟨flag r F 3, finrank_flag (r := r) (K := F) (i := 3) (by omega),
      fun _ hx => quadPlus_eq_zero_of_mem_flag hx⟩
  let e₁ : StatedOmega (StatedQuadPlus r F) ≃* orthElementaryGroup (quadPlus r F) :=
    CFSG.ClassicalGroups.Orthogonal.statedOmegaEquiv (coe_quadPlus r F) hE
  have := finite_orthElementaryGroup (r := r) (K := F)
  obtain ⟨S, hS⟩ := posUnip_isSylow (r := r) (K := F) 3 (by omega) fun a ha =>
    map_flag_top_ne_Xstar (r := r) (K := F) (by omega) ha
  set PE := (posUnip r F).subgroupOf (orthElementaryGroup (quadPlus r F))
  let PΩ : Subgroup (StatedOmega (StatedQuadPlus r F)) := PE.map e₁.symm.toMonoidHom
  have hPΩ : Nat.card PΩ = 3 ^ (Nat.card (StatedOmega (StatedQuadPlus r F))).factorization 3 := by
    rw [Subgroup.card_map_of_injective e₁.symm.injective, ← hS, S.card_eq_multiplicity,
      Nat.card_congr e₁.toEquiv]
  let eP : PE ≃* PΩ := e₁.symm.subgroupMap PE
  have hr2 : 2 ≤ r := by omega
  obtain ⟨Q, φ', hQ, hφ'⟩ := Proving.exists_sylow_hom_comm_of_surjective
    (QuotientGroup.mk' ((StatedScalars (Fin r ⊕ Fin r) F).subgroupOf
      (StatedOmega (StatedQuadPlus r F))))
    (QuotientGroup.mk'_surjective _)
    (by
      rw [QuotientGroup.ker_mk']
      exact not_three_dvd_card_scalars_statedOmega (statedQuadPlus_smul r)
        (statedQuadPlus_ne_zero (by omega) F))
    PΩ hPΩ ((orthUnipCoord hr2).comp eP.symm.toMonoidHom)
    ((orthUnipCoord_surjective hr2).comp eP.symm.surjective)
  refine E27Config.false_of_sylow_hom_comm h hz θ Q hQ φ' hφ' ?_
  have hcard : Nat.card (Multiplicative ((Fin (r - 1) → F) × F)) = 3 ^ (f * r) := by
    rw [show Nat.card (Multiplicative ((Fin (r - 1) → F) × F)) =
        Nat.card ((Fin (r - 1) → F) × F) from rfl, Nat.card_prod, Nat.card_fun,
      Nat.card_eq_fintype_card (α := Fin (r - 1)), Fintype.card_fin, hF, ← pow_mul, ← pow_add]
    congr 1
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  rw [hcard]
  calc 81 = 3 ^ 4 := by norm_num
    _ ≤ 3 ^ (f * r) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

theorem false_of_typeD_char_three {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}
    (h : E27Config X K R T z) (hz : z ∈ K) (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.D r q).Valid) (hp : q.p = 3)
    (e : ↥K ≃* (CFSGIndex.lie ⟨.D r q, hv⟩).Group) : False := by
  have hcl := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e
  rw [hp] at hcl
  exact false_of_pomegaPlus_model_char_three h hz hcl

end CFSG.HardMathSupport.Malle.E27Lie
