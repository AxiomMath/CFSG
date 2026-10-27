module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamCore
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamExc
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddG2Inner
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddCentralFixed

public noncomputable section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LieType.Ree (ReeTag)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

section


variable {K : Type} [Field K] [Finite K]

theorem cl24_toralCentralizer_G2_component
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hf : 1 ≤ f) (b : Fin Tag.G2.rank → Kˣ)
    (hb : ∀ i, b i = 1 ∨ b i = -1) (hb1 : b ≠ 1) {M : Subgroup (toralCentralizer .G2 K b)}
    (hM : IsComponent M) : Cl24Q p (fun f' => f' = f) M := by
  have hKodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hK2 : Nat.card K ≠ 2 := fun h => absurd (h ▸ hKodd) (by decide)
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  obtain ⟨-, -, hcases, hstruct, hq3⟩ :=
    odd_G2_toral_involution_fixed_p_components K hKodd b hb
  by_cases hK3 : Nat.card K = 3
  · have := (hq3 hK3 hb1).1
    exact (not_isComponent_of_isSolvable hM).elim
  obtain ⟨α₀, β₀, hc⟩ : ∃ α₀ β₀ : Fin Tag.G2.rank → ℤ,
      (b = ![-1, 1] ∧ α₀ = ![0, 1] ∧ β₀ = ![2, 3]) ∨
        (b = ![1, -1] ∧ α₀ = ![1, 0] ∧ β₀ = ![1, 2]) ∨
          (b = ![-1, -1] ∧ α₀ = ![1, 1] ∧ β₀ = ![1, 3]) := by
    rcases hcases with h | h | h | h
    · exact absurd h hb1
    · exact ⟨_, _, Or.inl ⟨h, rfl, rfl⟩⟩
    · exact ⟨_, _, Or.inr (Or.inl ⟨h, rfl, rfl⟩)⟩
    · exact ⟨_, _, Or.inr (Or.inr ⟨h, rfl, rfl⟩)⟩
  obtain ⟨-, -, hS, hcomm, -, ⟨eα⟩, ⟨eβ⟩, hSX, hSn, hsolv, -⟩ := hstruct α₀ β₀ hc
  set X := toralCentralizer .G2 K b
  set Qα := rootSubgroup .G2 K α₀ ⊔ rootSubgroup .G2 K (-α₀)
  set Qβ := rootSubgroup .G2 K β₀ ⊔ rootSubgroup .G2 K (-β₀)
  have hQαX : Qα ≤ X := (hS ▸ (le_sup_left : Qα ≤ Qα ⊔ Qβ)).trans hSX
  have hQβX : Qβ ≤ X := (hS ▸ (le_sup_right : Qβ ≤ Qα ⊔ Qβ)).trans hSX
  have hD : (rootSpan .G2 K (rootCharKernel b)).subgroupOf X =
      Qα.subgroupOf X ⊔ Qβ.subgroupOf X := by
    rw [hS]
    exact Subgroup.subgroupOf_sup hQαX hQβX
  have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl (Or.inr hK2)
    (Or.inr hK3)
  let eα' : Qα.subgroupOf X ≃* SL2 K := (Subgroup.subgroupOfEquivOfLe hQαX).trans eα.symm
  let eβ' : Qβ.subgroupOf X ≃* SL2 K := (Subgroup.subgroupOfEquivOfLe hQβX).trans eβ.symm
  have hqα : IsQuasisimple (Qα.subgroupOf X) := LocalCores.isQuasisimple_of_mulEquiv eα'.symm hSL
  have hqβ : IsQuasisimple (Qβ.subgroupOf X) := LocalCores.isQuasisimple_of_mulEquiv eβ'.symm hSL
  have hαβ : ∀ x ∈ Qα.subgroupOf X, ∀ y ∈ Qβ.subgroupOf X, x * y = y * x := by
    intro x hx y hy
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hx
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp h1 _ hy).symm)
  have hnα : ((Qα.subgroupOf X).subgroupOf
      ((rootSpan .G2 K (rootCharKernel b)).subgroupOf X)).Normal := by
    rw [hD, Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    refine sup_le Subgroup.le_normalizer fun y hy => ?_
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      hαβ x hx y hy)
  have hnβ : ((Qβ.subgroupOf X).subgroupOf
      ((rootSpan .G2 K (rootCharKernel b)).subgroupOf X)).Normal := by
    rw [hD, Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right]
    refine sup_le (fun y hy => ?_) Subgroup.le_normalizer
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      (hαβ y hy x hx).symm)
  have hMS := le_of_isComponent_of_solvable_quotient hsolv hM
  rcases eq_or_eq_of_isComponent_le_sup hD hqα hqβ hnα hnβ hM hMS with h | h
  · let e := (MulEquiv.subgroupCongr h).trans eα'
    exact cl24_of_equiv_psl_two (R := fun f' => f' = f) hp hf hK hK2 hK3
      (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e))
  · let e := (MulEquiv.subgroupCongr h).trans eβ'
    exact cl24_of_equiv_psl_two (R := fun f' => f' = f) hp hf hK hK2 hK3
      (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e))

theorem cl24_excInnerDiag_G2
    : Cl24ExcInnerDiag .G2 := by
  intro K _ _ p f hp hp2 hKp α g a hαg hαo L hL
  have hKodd : Odd (Nat.card K) := by rw [hKp]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hα : α ^ 2 = 1 := hαo ▸ pow_orderOf_eq_one α
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at hKp
      exact absurd hKp (Finite.one_lt_card).ne'
    · exact h0
  have hα1 : α ≠ 1 := fun h => by
    rw [h, orderOf_one] at hαo
    exact absurd hαo (by norm_num)
  obtain ⟨b, hb, hb1, ⟨Θ⟩⟩ := exists_toralCentralizer_equiv_of_innerDiag (Or.inl rfl) hKodd hαg hα
  exact cl24_of_mulEquiv (L.equivMapOfInjective Θ.toMonoidHom Θ.injective)
    (cl24_toralCentralizer_G2_component hp hp2 hKp hf b hb (hb1 hα1)
      (LocalCores.isComponent_map_mulEquiv Θ hL))

theorem cl24_reeGamma_G2
    [CharP K ReeTag.G2.prime] {b : ℕ} (hb : 1 ≤ b) (hK : Nat.card K = 3 ^ (2 * b + 1)) :
    Cl24Q 3 (fun f' => f' = 2 * b + 1) (ReeTag.G2.reeGamma K b) := by
  have hZ := ReeTag.center_reeGamma_G2_eq_bot hK
  obtain ⟨E⟩ := ReeTag.nonempty_derivedCentralQuotient_mulEquiv_reeGamma_G2 hb hK
  have hadm : StatedLieAdmissible .twistedG2 0 3 (2 * b + 1) :=
    ⟨Nat.prime_three, by omega, rfl, rfl, ⟨b, rfl⟩, by omega⟩
  have hfx : reeFixedGroup .G2 K reeG2Perm
      (fun i => if i ∈ reeG2Long then 3 ^ b else 3 ^ (b + 1)) = ReeTag.G2.reeGamma K b :=
    (ReeTag.reeGamma_eq_reeFixedGroup (t := ReeTag.G2) (K := K) (a := b)).symm
  let eC : DerivedCentralQuotient (reeFixedGroup .G2 K reeG2Perm
      (fun i => if i ∈ reeG2Long then 3 ^ b else 3 ^ (b + 1))) ≃*
      DerivedCentralQuotient (ReeTag.G2.reeGamma K b) :=
    QuotientGroup.congr _ _ (MulEquiv.subgroupCongr (by rw [hfx]; rfl))
      (Subgroup.map_center_eq _)
  let e' := ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans
    (E.symm.trans eC.symm)
  exact ⟨.twistedG2, 0, 2 * b + 1, rfl, hadm, Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hadm, b,
    rfl, K, inferInstance, inferInstance, hK, ⟨e'⟩⟩))⟩

theorem cl24_odd_G2_three_explicit
    [CharP K ReeTag.G2.prime] (hinner : Cl24ExcInnerDiag .G2) {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 3 ^ f) (β : MulAut (adjointGroup ReeTag.G2.tag K)) (hβ : orderOf β = 2)
    {X : Type} [Group X] (Ψ : X ≃* fixedSubgroup β) {L : Subgroup X} (hL : IsComponent L) :
    Cl24Q 3 (fun f' => f' = f ∨ f = 2 * f') L ∨
      (f = 1 ∧ β ∉ inner (adjointGroup ReeTag.G2.tag K) ∧ LieModel L .PSL 2 2 3) := by
  have hβ2 : β ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one β
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  rcases G2_three_involution_inner_quadratic_or_exceptional hf hK hβ2 with ⟨g, a, hβg⟩ |
    ⟨e, he, hKe, δ, hδ, g, a, hβg⟩ | ⟨b, g, hfb, rfl⟩
  · exact Or.inl ((cl24_of_component_equiv Ψ
      (hinner K 3 f Nat.prime_three (by decide) hK β g a hβg hβ) hL).mono fun _ h => Or.inl h)
  · have hf2 := cl24_exp_eq_two_mul Nat.prime_three hK hKe
    exact Or.inl ((cl24_odd_field (t := .G2) (Or.inl ⟨rfl, rfl⟩) Nat.prime_three
      (by decide) he hKe δ hδ hβg hβ2 Ψ hL).mono fun _ h => Or.inr (by omega))
  · have hK' : Nat.card K = 3 ^ (2 * b + 1) := hfb ▸ hK
    obtain ⟨⟨ψ, hψ⟩, -, -⟩ :=
      LieType.Ree.G2_exceptional_coset_involution_fixed_p_components b K hK' g hβ2
    have hc : MulAut.congr ψ (MulAut.conj g * ReeTag.G2.finiteReeAut K b) =
        ReeTag.G2.finiteReeAut K b :=
      (MulEquiv.ext fun _ => rfl : MulAut.congr ψ (MulAut.conj g * ReeTag.G2.finiteReeAut K b) =
        ψ * (MulAut.conj g * ReeTag.G2.finiteReeAut K b) * ψ⁻¹).trans hψ
    have hmap : (fixedSubgroup (ReeTag.G2.finiteReeAut K b)).map
        (adjointGroup ReeTag.G2.tag K).subtype = ReeTag.G2.reeGamma K b := rfl
    have hFc : fixedSubgroup (MulAut.congr ψ (MulAut.conj g * ReeTag.G2.finiteReeAut K b)) =
        fixedSubgroup (ReeTag.G2.finiteReeAut K b) := by rw [hc]
    let Ψ' : X ≃* ReeTag.G2.reeGamma K b := Ψ.trans ((fixedSubgroupCongrEquiv ψ _).trans
      ((MulEquiv.subgroupCongr hFc).trans
        (((fixedSubgroup (ReeTag.G2.finiteReeAut K b)).equivMapOfInjective _
          Subtype.val_injective).trans (MulEquiv.subgroupCongr hmap))))
    obtain ⟨hDs, -, -, htop, -, -⟩ :=
      CatalogueBSmallRee.small_Ree_whole_group_p_components b K hK'
    set Γ := ReeTag.G2.reeGamma K b with hΓ
    have eJ : commutator Γ ≃* (commutator Γ).map Γ.subtype :=
      (commutator Γ).equivMapOfInjective _ Subtype.val_injective
    have : IsSimpleGroup ((commutator Γ).map Γ.subtype) := (MulEquiv.isSimpleGroup_congr eJ).1 hDs
    have hJF : (commutator Γ).map Γ.subtype ≤ Γ := Subgroup.map_subtype_le _
    have hJsub : ((commutator Γ).map Γ.subtype).subgroupOf Γ = commutator Γ :=
      Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _
    have hJn : (((commutator Γ).map Γ.subtype).subgroupOf Γ).Normal := by
      rw [hJsub]
      exact Subgroup.commutator_normal ⊤ ⊤
    have hsolv : Group.IsSolvable (Γ ⧸ ((commutator Γ).map Γ.subtype).subgroupOf Γ) := by
      have : Group.IsSolvable (Abelianization Γ) := inferInstance
      exact Group.isSolvable_of_surjective
        (f := (QuotientGroup.quotientMulEquivOfEq hJsub.symm).toMonoidHom)
        (QuotientGroup.quotientMulEquivOfEq hJsub.symm).surjective
    obtain ⟨E⟩ := nonempty_component_equiv_of_normal_simple hJF hJn hsolv Ψ' hL
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · right
      refine ⟨by omega, ?_, ?_⟩
      · obtain ⟨-, -, ⟨Θ, hΘ, -, hker⟩, -, -, -, hodd⟩ :=
          G2_three_exact_automorphism_normal_form hf K hK
        obtain ⟨-, hR, -⟩ := hodd 0 hfb
        intro hin
        have hmem : MulAut.conj g * ReeTag.G2.finiteReeAut K 0 ∈ Θ.ker := by
          rw [hker]
          exact hin
        rw [MonoidHom.mem_ker, hΘ _ g f (by rw [hR])] at hmem
        have h1 : ((f : ℕ) : ZMod (2 * f)) = 0 := by
          simpa using congrArg Multiplicative.toAdd hmem
        rw [ZMod.natCast_eq_zero_iff] at h1
        have := Nat.le_of_dvd (by omega) h1
        omega
      · obtain ⟨-, -, -, -, -, -, h0⟩ :=
          LiteratureLocal.small_Ree_G2_fixed_points_and_Ree3_PGammaL2_8 0 K hK'
        obtain ⟨-, -, -, -, hstated, -⟩ := h0 rfl
        have hL0 : LieModel (commutator Γ) .PSL 2 2 3 := Or.inl ⟨by decide, hstated⟩
        exact LieType.CurtisTits.lieModel_of_mulEquiv (E.trans eJ.symm).symm hL0
    · left
      have eD : commutator Γ ≃* Γ := (MulEquiv.subgroupCongr (htop hb)).trans Subgroup.topEquiv
      exact cl24_of_mulEquiv ((E.trans eJ.symm).trans eD)
        ((cl24_reeGamma_G2 hb hK').mono fun _ h => Or.inl (by omega))

theorem cl24_tracked_G2_of_inner
    (hinner : Cl24ExcInnerDiag .G2) : Cl24TrackedFamily .G2 := by
  intro J _ n f hadm hm α hα Kc hKc
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .G2
    ((GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2 : UntwistedChevalleyModel J
      .G2 (3 ^ f))
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  have : CharP F ReeTag.G2.prime :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three hf hF
  rcases cl24_odd_G2_three_explicit hinner hf hF (MulAut.congr e α) hβ
      (fixedSubgroupCongrEquiv e α) hKc with h | ⟨rfl, hβo, hPSL⟩
  · obtain ⟨τ', n', f', hR, hadm', hmodel⟩ := h
    rcases hR with hR | hR
    · exact Or.inl ⟨τ', n', f', Or.inr (Or.inl hR), hadm', hmodel⟩
    · exact Or.inl ⟨τ', n', f', Or.inl hR, hadm', hmodel⟩
  · refine Or.inr ⟨?_, fun hin => hβo ?_, hPSL⟩
    · rw [show n = 0 from hadm.2.2.1] at hm
      exact hm
    · exact (LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff e α).2 hin

theorem cl24_tracked_G2 :
    Cl24TrackedFamily .G2 :=
  cl24_tracked_G2_of_inner cl24_excInnerDiag_G2

end

end CFSG.OddStandard.SmallF3.HypA2Leaves
