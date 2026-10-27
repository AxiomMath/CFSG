module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcFieldCore
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6Noninner

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial

section TwE6


theorem fieldCoreAt_twistedE6 {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = ℓ ^ (2 * f)) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (Θ : MulAut (twistedE6RootGroup K σ) →* RingAut K)
    (hΘ : ∀ α g u δ, α = MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u *
      fieldActor σ δ → Θ α = δ) (hp : p.Prime) (hp3 : 3 < p)
    (hdvd : ∀ κ : K ≃+* K, (∀ c, κ c = c ^ ℓ ^ (2 * (f / p))) →
      ∀ σ₀ : fixSubfield κ ≃+* fixSubfield κ, (∀ c, (σ₀ c : K) = (c : K) ^ ℓ ^ (f / p)) →
        Nat.card (fixSubfield κ) = ℓ ^ (2 * (f / p)) →
        ¬ Nat.Coprime p (Nat.card (subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) σ₀)))
    {x : MulAut (twistedE6RootGroup K σ)} (hxp : orderOf x = p)
    (hxo : x ∉ (MulAut.conj : twistedE6RootGroup K σ →*
      MulAut (twistedE6RootGroup K σ)).range) :
    FieldCoreAt p x := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hαp : orderOf (⟨x, Subgroup.mem_top x⟩ :
      (⊤ : Subgroup (MulAut (twistedE6RootGroup K σ)))) = p := by
    rw [Subgroup.orderOf_mk]
    exact hxp
  obtain ⟨hηo, ⟨d, hd⟩, ⟨ψ, hψ⟩, -⟩ :=
    twisted_E6_noninner_large_prime_field_descent_and_local_core_trivial hℓ hf K hK σ hσ Θ hΘ hp
      hp3 ⊤ le_top ⟨x, Subgroup.mem_top x⟩ hxo hαp
  have hd0 : 1 ≤ d := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hdp : d * p = f := by rw [hd, mul_comm]
  have hdf : f / p = d := by rw [← hdp, Nat.mul_div_cancel _ hp.pos]
  obtain ⟨fr, hfr, hord, hgen, hcardAut, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality hℓ (by omega : 1 ≤ 2 * f) hK
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨fr, hgen⟩
  obtain ⟨T, hTdef⟩ : ∃ T, fr ^ d = T := ⟨_, rfl⟩
  have hT : ∀ c, T c = c ^ ℓ ^ d := fun c => by
    rw [← hTdef]
    exact ringAut_pow_apply_of_frobenius hfr d c
  have hT2p : T ^ (2 * p) = 1 := by
    rw [← hTdef, ← pow_mul, show d * (2 * p) = orderOf fr by rw [hord, ← hdp]; ring,
      pow_orderOf_eq_one]
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two (by omega)
  obtain ⟨ε, hεdef⟩ : ∃ ε, T ^ (p + 1) = ε := ⟨_, rfl⟩
  have hε : ∀ c, ε c = c ^ ℓ ^ (d * (p + 1)) := fun c => by
    rw [← hεdef, ← hTdef, ← pow_mul]
    exact ringAut_pow_apply_of_frobenius hfr _ c
  have hεp : ε ^ p = 1 := by
    rw [← hεdef, ← pow_mul, show (p + 1) * p = 2 * p * (m + 1) by rw [hm]; ring, pow_mul, hT2p,
      one_pow]
  obtain ⟨κ, hκdef⟩ : ∃ κ, T ^ 2 = κ := ⟨_, rfl⟩
  have hκ : ∀ c, κ c = c ^ ℓ ^ (2 * d) := fun c => by
    rw [← hκdef, ← hTdef, ← pow_mul, mul_comm]
    exact ringAut_pow_apply_of_frobenius hfr _ c
  have hσ₀ : ∀ c, (fixSubfieldRestrict T κ c : K) = (c : K) ^ ℓ ^ d := fun c => by
    rw [coe_fixSubfieldRestrict, hT]
  have hKdp : Nat.card K = ℓ ^ (2 * d * p) := by rw [hK, ← hdp, mul_assoc]
  have hσdp : ∀ c, σ c = c ^ ℓ ^ (d * p) := fun c => by rw [hdp, hσ]
  obtain ⟨-, hkcard, hJC, hδord, -, hsimple, hnc, -, hNδ, hnormal, hcent, -⟩ :=
    twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer hℓ hd0
      (by omega : 3 ≤ p) (hp.odd_of_ne_two (by omega)) K hKdp κ hκ σ hσdp
      (fixSubfieldRestrict T κ) hσ₀ ε hε
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
  have hκ' : ∀ c, κ c = c ^ ℓ ^ (2 * (f / p)) := fun c => by rw [hdf]; exact hκ c
  have hσ₀' : ∀ c, (fixSubfieldRestrict T κ c : K) = (c : K) ^ ℓ ^ (f / p) := fun c => by
    rw [hdf]; exact hσ₀ c
  have hcore : FieldCoreAt p (fieldActor (t := TwistTag.E6) σ ε) := by
    refine fieldCoreAt_of_canonical_quasisimple hinj hδord hq hNδ hnormal hcent ?_
    rw [Nat.card_congr e1.toEquiv]
    exact hdvd κ hκ' (fixSubfieldRestrict T κ) hσ₀' (by rw [hdf]; exact hkcard)
  have hεne : ε ≠ 1 := fun h => by
    rw [h, fieldActor_one, orderOf_one] at hδord
    exact hp.one_lt.ne hδord
  have hεo : orderOf ε = p := orderOf_eq_prime hεp hεne
  have hηo' : orderOf (Θ x) = p := hηo
  have hz : Subgroup.zpowers ε = Subgroup.zpowers (Θ x) := by
    refine le_antisymm (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · exact mem_zpowers_of_pow_eq_one_of_isCyclic' hp.pos hηo' hεp
    · exact mem_zpowers_of_pow_eq_one_of_isCyclic' hp.pos hεo
        (by rw [← hηo']; exact pow_orderOf_eq_one _)
  have hzA : Subgroup.zpowers (fieldActor (t := TwistTag.E6) σ ε) =
      Subgroup.zpowers (fieldActor (t := TwistTag.E6) σ (Θ x)) := by
    have h1 := MonoidHom.map_zpowers (fieldActorHom (t := TwistTag.E6) σ) ε
    have h2 := MonoidHom.map_zpowers (fieldActorHom (t := TwistTag.E6) σ) (Θ x)
    rw [hz] at h1
    exact h1.symm.trans h2
  exact fieldCoreAt_of_conj (FieldCoreAt.of_zpowers_eq hzA hcore) ψ hψ

end TwE6

end CFSG.HardMathSupport.Timmesfeld.CrossChar
