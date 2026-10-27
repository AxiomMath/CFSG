module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6
public import CFSG.LieType.SeitzGeneration.ExcTorusThreeTwRank
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Descent

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.AlgebraicGroups
  CFSG.LieType.SeitzGeneration
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

section TwE6


theorem exists_conj_fieldActor_of_not_mem_twistedE6Inndiag {ℓ f p : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ (2 * f))
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (Θ : MulAut (twistedE6RootGroup K σ) →* RingAut K)
    (hΘ : ∀ α g u δ, α = MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u *
      fieldActor σ δ → Θ α = δ)
    (hp : p.Prime) (hp2 : p ≠ 2) {α : MulAut (twistedE6RootGroup K σ)} (hαp : α ^ p = 1)
    (hαo : α ∉ twistedE6Inn K σ ⊔ twistedE6Diag K σ) :
    orderOf (Θ α) = p ∧ p ∣ f ∧
      ∃ ψ : MulAut (twistedE6RootGroup K σ), ψ * α * ψ⁻¹ = fieldActor σ (Θ α) := by
  have hK2 : Nat.card K = (ℓ ^ f) ^ 2 := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, -, -, -, -, -, -, hex, ⟨Θ', hΘ', -, hker', -, -, -⟩, -, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK2 σ hσ
  have hη1 : Θ α ≠ 1 := by
    intro h1
    have hmem : α ∈ Θ'.ker := by
      obtain ⟨g, u, δ, hα⟩ := hex α
      rw [MonoidHom.mem_ker, hΘ' α g u δ hα, ← hΘ α g u δ hα, h1]
    rw [hker'] at hmem
    exact hαo hmem
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hd, -, -, -, -, ψ, -, hψα⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.twisted_E6_field_descent_conj_of_prime_order hℓ hf K hK
      σ hσ Θ hΘ hp hp2 α hαp hη1
  exact ⟨orderOf_eq_prime (by rw [← map_pow, hαp, map_one]) hη1, ⟨d, hd⟩, ψ, hψα⟩

theorem fieldCoreAt_twistedE6_of_not_mem_inndiag {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ (2 * f)) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {x : MulAut (twistedE6RootGroup K σ)} (hx3 : x ^ 3 = 1)
    (hxo : x ∉ twistedE6Inn K σ ⊔ twistedE6Diag K σ) : FieldCoreAt 3 x := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hK2 : Nat.card K = (ℓ ^ f) ^ 2 := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK2 σ hσ
  obtain ⟨hηo, ⟨d, hd⟩, ψ, hψ⟩ := exists_conj_fieldActor_of_not_mem_twistedE6Inndiag hℓ hf K hK
    σ hσ Θ hΘ Nat.prime_three (by norm_num) hx3 hxo
  have hd0 : 1 ≤ d := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hdp : d * 3 = f := by rw [hd, mul_comm]
  have hdf : f / 3 = d := by rw [← hdp, Nat.mul_div_cancel _ (by norm_num)]
  obtain ⟨fr, hfr, hord, hgen, hcardAut, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality hℓ (by omega : 1 ≤ 2 * f) hK
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨fr, hgen⟩
  obtain ⟨T, hTdef⟩ : ∃ T, fr ^ d = T := ⟨_, rfl⟩
  have hT : ∀ c, T c = c ^ ℓ ^ d := fun c => by
    rw [← hTdef]
    exact ringAut_pow_apply_of_frobenius hfr d c
  have hT6 : T ^ (2 * 3) = 1 := by
    rw [← hTdef, ← pow_mul, show d * (2 * 3) = orderOf fr by rw [hord, ← hdp]; ring,
      pow_orderOf_eq_one]
  obtain ⟨ε, hεdef⟩ : ∃ ε, T ^ (3 + 1) = ε := ⟨_, rfl⟩
  have hε : ∀ c, ε c = c ^ ℓ ^ (d * (3 + 1)) := fun c => by
    rw [← hεdef, ← hTdef, ← pow_mul]
    exact ringAut_pow_apply_of_frobenius hfr _ c
  have hε3 : ε ^ 3 = 1 := by
    rw [← hεdef, ← pow_mul, show (3 + 1) * 3 = 2 * 3 * 2 by norm_num, pow_mul, hT6, one_pow]
  obtain ⟨κ, hκdef⟩ : ∃ κ, T ^ 2 = κ := ⟨_, rfl⟩
  have hκ : ∀ c, κ c = c ^ ℓ ^ (2 * d) := fun c => by
    rw [← hκdef, ← hTdef, ← pow_mul, mul_comm]
    exact ringAut_pow_apply_of_frobenius hfr _ c
  have hσ₀ : ∀ c, (fixSubfieldRestrict T κ c : K) = (c : K) ^ ℓ ^ d := fun c => by
    rw [coe_fixSubfieldRestrict, hT]
  have hKdp : Nat.card K = ℓ ^ (2 * d * 3) := by rw [hK, ← hdp, mul_assoc]
  have hσdp : ∀ c, σ c = c ^ ℓ ^ (d * 3) := fun c => by rw [hdp, hσ]
  obtain ⟨-, hkcard, hJC, hδord, -, hsimple, hnc, -, hNδ, hnormal, hcent, -⟩ :=
    twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer hℓ hd0
      le_rfl (by decide) K hKdp κ hκ σ hσdp (fixSubfieldRestrict T κ) hσ₀ ε hε
  have hZ := exceptional_fixed_center_trivial TwistTag.E6 K σ
  have hinj := mulAut_conj_injective_of_center_eq_bot hZ
  have e1 : ((subfieldRootGroupImage TwistTag.E6 (fixSubfield κ)
      (fixSubfieldRestrict T κ)).subgroupOf (twistedE6RootGroup K σ)) ≃*
      subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) (fixSubfieldRestrict T κ) :=
    Subgroup.subgroupOfEquivOfLe hJC
  have : IsSimpleGroup (subfieldRootGroupImage TwistTag.E6 (fixSubfield κ)
      (fixSubfieldRestrict T κ)) := hsimple
  have hq : CFSG.IsQuasisimple ((subfieldRootGroupImage TwistTag.E6 (fixSubfield κ)
      (fixSubfieldRestrict T κ)).subgroupOf (twistedE6RootGroup K σ)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e1.symm (isQuasisimple_of_simple_nonabelian hnc)
  have hdvd : ¬ Nat.Coprime 3 (Nat.card (subfieldRootGroupImage TwistTag.E6 (fixSubfield κ)
      (fixSubfieldRestrict T κ))) := by
    have : Finite (fixSubfield κ) := Subtype.finite
    have : Finite (ModGL TwistTag.E6.tag (fixSubfield κ)) := finite_modGL
    have : Finite (twistedE6RootGroup (fixSubfield κ) (fixSubfieldRestrict T κ)) :=
      Subtype.finite
    have hk2 : Nat.card (fixSubfield κ) = (ℓ ^ d) ^ 2 := by rw [hkcard, ← pow_mul, mul_comm]
    have hcard : Nat.card (subfieldRootGroupImage TwistTag.E6 (fixSubfield κ)
        (fixSubfieldRestrict T κ)) =
        Nat.card (twistedE6RootGroup (fixSubfield κ) (fixSubfieldRestrict T κ)) :=
      Subgroup.card_map_of_injective (baseChangeGL_injective _)
    have hpq0 : ¬ 3 ∣ ℓ ^ d := fun h => hℓ3
      ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1 (Nat.prime_three.dvd_of_dvd_pow h)).symm
    have hσ₀' : ∀ c, fixSubfieldRestrict T κ c = c ^ (ℓ ^ d) := fun c =>
      Subtype.ext (by rw [hσ₀ c, SubmonoidClass.coe_pow])
    rw [hcard, ← Nat.Prime.dvd_iff_not_coprime Nat.prime_three]
    exact dvd_card_of_not_rankLE2 Nat.prime_three (not_rankLE2_twistedE6_three hℓ hd0
      (fixSubfield κ) hk2 (fixSubfieldRestrict T κ) hσ₀' hpq0)
  have hcore : FieldCoreAt 3 (fieldActor (t := TwistTag.E6) σ ε) := by
    refine fieldCoreAt_of_canonical_quasisimple hinj hδord hq hNδ hnormal hcent ?_
    rw [Nat.card_congr e1.toEquiv]
    exact hdvd
  have hεne : ε ≠ 1 := fun h => by
    rw [h, fieldActor_one, orderOf_one] at hδord
    exact absurd hδord (by norm_num)
  have hεo : orderOf ε = 3 := orderOf_eq_prime hε3 hεne
  have hz : Subgroup.zpowers ε = Subgroup.zpowers (Θ x) := by
    refine le_antisymm (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · exact mem_zpowers_of_pow_eq_one_of_isCyclic' (by norm_num) hηo hε3
    · exact mem_zpowers_of_pow_eq_one_of_isCyclic' (by norm_num) hεo
        (by rw [← hηo]; exact pow_orderOf_eq_one _)
  have hzA : Subgroup.zpowers (fieldActor (t := TwistTag.E6) σ ε) =
      Subgroup.zpowers (fieldActor (t := TwistTag.E6) σ (Θ x)) := by
    have h1 := MonoidHom.map_zpowers (fieldActorHom (t := TwistTag.E6) σ) ε
    have h2 := MonoidHom.map_zpowers (fieldActorHom (t := TwistTag.E6) σ) (Θ x)
    rw [hz] at h1
    exact h1.symm.trans h2
  exact fieldCoreAt_of_conj (FieldCoreAt.of_zpowers_eq hzA hcore) ψ hψ

end TwE6

end CFSG.HardMathSupport.Timmesfeld.CrossChar
