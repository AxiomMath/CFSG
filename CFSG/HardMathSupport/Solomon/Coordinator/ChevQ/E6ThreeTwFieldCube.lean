module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeFieldCubeE6
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwFixed
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwOvergroup
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcOuterLeOne
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
open CFSG.HardMathSupport.Timmesfeld.CrossChar
  (exists_conj_fieldActor_of_not_mem_twistedE6Inndiag mem_zpowers_of_pow_eq_one_of_isCyclic')
open CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc
  (not_isD2SeitzException_of_chevalleyExc isChevalleyExcIndex_twistedE6)

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

private theorem card_inf_eq_sq_of_decomp {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {E D : Subgroup X} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 3) {φ : X} (hφE : φ ∈ E)
    (hφD : φ ∉ D) (hdec : ∀ x ∈ E, ∃ j : ℤ, x * (φ ^ j)⁻¹ ∈ D) :
    Nat.card (E ⊓ D : Subgroup X) = p ^ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set B : Subgroup X := E ⊓ D with hB
  have hφ1 : φ ≠ 1 := fun h => hφD (h ▸ one_mem _)
  have hord : orderOf φ = p := orderOf_eq_prime (hE.2 _ hφE) hφ1
  let ψ : B × Subgroup.zpowers φ → E := fun bz =>
    ⟨(bz.1 : X) * bz.2, E.mul_mem bz.1.2.1 (Subgroup.zpowers_le.2 hφE bz.2.2)⟩
  have hsurj : Function.Surjective ψ := by
    rintro ⟨x₀, hx₀⟩
    obtain ⟨j, hj⟩ := hdec x₀ hx₀
    refine ⟨(⟨x₀ * (φ ^ j)⁻¹, E.mul_mem hx₀ (E.inv_mem (E.zpow_mem hφE j)), hj⟩,
      ⟨φ ^ j, Subgroup.zpow_mem_zpowers _ j⟩), ?_⟩
    apply Subtype.ext
    show x₀ * (φ ^ j)⁻¹ * φ ^ j = x₀
    group
  have h1 := Nat.card_le_card_of_surjective ψ hsurj
  rw [Nat.card_prod, Nat.card_zpowers, hord, hc] at h1
  have hBE : B ≤ E := inf_le_left
  obtain ⟨i, hi3, hBi⟩ := (Nat.dvd_prime_pow hp).1 (hc ▸ Subgroup.card_dvd_of_le hBE)
  have hBne : Nat.card B ≠ p ^ 3 := by
    intro h3
    have hBeq : B = E := Subgroup.eq_of_le_of_card_ge hBE (by rw [hc, h3])
    exact hφD (hBeq ▸ hφE : φ ∈ B).2
  rw [hBi] at h1 hBne ⊢
  have hp1 := hp.one_lt
  have h12 : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp1 (by norm_num)
  interval_cases i
  · rw [pow_zero] at h1
    nlinarith
  · rw [pow_one] at h1
    nlinarith
  · rfl
  · exact absurd rfl hBne



section TwE6

variable {K : Type} [Field K] [Finite K]

theorem mem_twFJ_of_commute {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hp : p.Prime)
    (hp2 : p ≠ 2) {η : K ≃+* K} (hη : orderOf η = p) {β : MulAut ↥(twistedE6RootGroup K σ)}
    (hβ : Commute β (fieldActor (t := TwistTag.E6) σ η)) {y : ↥(twistedE6RootGroup K σ)}
    (hy : y ∈ twFJ σ η) : β y ∈ twFJ σ η := by
  have hC : (fixedSubgroup (fieldActor (t := TwistTag.E6) σ η)).map β.toMonoidHom ≤
      fixedSubgroup (fieldActor (t := TwistTag.E6) σ η) := by
    rintro _ ⟨k, hk, rfl⟩
    refine mem_fixedSubgroup.2 ?_
    have h := congrArg (fun φ : MulAut ↥(twistedE6RootGroup K σ) => φ k) hβ.eq
    simp only [MulAut.mul_apply] at h
    rw [MulEquiv.coe_toMonoidHom, ← h, mem_fixedSubgroup.1 hk]
  rw [← commutator_fixedSubgroup_eq_twFJ hℓ hf hK σ hσ hp hp2 hη] at hy ⊢
  have h := Subgroup.mem_map_of_mem β.toMonoidHom hy
  rw [Subgroup.map_commutator] at h
  exact Subgroup.commutator_mono hC hC h

theorem le_fixedSubgroup_or_eq_top_of_twFJ_le {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hℓ3 : ℓ ≠ 3)
    (h8 : ℓ ^ f ≠ 8) {η : K ≃+* K} (hη : orderOf η = 3)
    {H : Subgroup ↥(twistedE6RootGroup K σ)} (hH : twFJ σ η ≤ H) :
    H ≤ fixedSubgroup (fieldActor (t := TwistTag.E6) σ η) ∨ H = ⊤ := by
  have hS : TwE6Setup K σ η 3 :=
    TwE6Setup.of_data hℓ hf hK hσ Nat.prime_three (by norm_num) (Ne.symm hℓ3) hη
  have hK2f : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hD : ringChar K ≠ 2 ∨ 4 ∣ Nat.card (fixSubfield (fixSubfieldRestrict η σ)) := by
    by_cases h2 : ringChar K = 2
    · right
      have : Fintype K := Fintype.ofFinite K
      have : Fact ℓ.Prime := ⟨hℓ⟩
      have : CharP K ℓ := charP_of_card_eq_prime_pow
        (by rw [← Nat.card_eq_fintype_card, hK2f] : Fintype.card K = ℓ ^ (2 * f))
      have hℓ2 : ℓ = 2 := (ringChar.eq K ℓ).symm.trans h2
      have hσo : orderOf σ = 2 := orderOf_eq_prime hS.sigma_sq hS.sigma_ne_one
      obtain ⟨-, hFσ⟩ :=
        CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield hℓ (by omega) hK2f σ
      rw [hσo, Nat.mul_div_cancel_left f (by norm_num : 0 < 2)] at hFσ
      obtain ⟨h3f, hFτ⟩ :=
        CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield hℓ hf hFσ (fixSubfieldRestrict η σ)
      rw [hS.orderOf_restrict] at h3f hFτ
      rw [hFτ, hℓ2]
      obtain ⟨k, rfl⟩ := h3f
      have hk : 2 ≤ k := by
        rcases Nat.lt_or_ge k 2 with hk | hk
        · interval_cases k
          · omega
          · exfalso
            apply h8
            rw [hℓ2]
            norm_num
        · exact hk
      rw [Nat.mul_div_cancel_left k (by norm_num : 0 < 3)]
      calc 4 = 2 ^ 2 := by norm_num
        _ ∣ 2 ^ k := Nat.pow_dvd_pow 2 hk
    · exact Or.inl h2
  exact TwOvergroup.le_twR_or_eq_top_of_twGens hS hD (twFJ_le_twR σ η)
    (twGens_twFJ hS.sigma_sq η) hH

theorem card_inf_twistedE6Inndiag {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {E : Subgroup (MulAut ↥(twistedE6RootGroup K σ))} (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 3) (hED : ¬ E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ) :
    Nat.card ↥(E ⊓ (twistedE6Inn K σ ⊔ twistedE6Diag K σ)) = 3 ^ 2 := by
  classical
  have hK2f : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  obtain ⟨fr, -, -, hgen, hcardAut, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ
      (by omega : 1 ≤ 2 * f) hK2f
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨fr, hgen⟩
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Finite ↥(twistedE6RootGroup K σ) := Subtype.finite
  have : Finite (MulAut ↥(twistedE6RootGroup K σ)) := MulEquiv.finite_left
  obtain ⟨x₀, hx₀E, hx₀D⟩ : ∃ x ∈ E, x ∉ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
    by_contra h
    push Not at h
    exact hED fun y hy => h y hy
  have hΘx₀ : orderOf (Θ x₀) = 3 := by
    refine orderOf_eq_prime (by rw [← map_pow, hE.2 x₀ hx₀E, map_one]) fun h => hx₀D ?_
    rw [← hker]
    exact MonoidHom.mem_ker.2 h
  refine card_inf_eq_sq_of_decomp Nat.prime_three hE hEc hx₀E hx₀D fun y hy => ?_
  have hy3 : Θ y ^ 3 = 1 := by rw [← map_pow, hE.2 y hy, map_one]
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1
    (mem_zpowers_of_pow_eq_one_of_isCyclic' (by norm_num) hΘx₀ hy3)
  refine ⟨j, ?_⟩
  rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hj, mul_inv_cancel]

end TwE6

theorem twE6FieldCubes_of_kfact (hS : AGLEmbeddingD2.KFactSeitzRankTwo) :
    E6ThreeDefs.TwE6FieldCubes := by
  intro K _ _ σ q hK3 hσ hKq _ hq8 E hE hEc hED
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  obtain ⟨ℓ, hℓK⟩ : ∃ ℓ, ringChar K = ℓ := ⟨_, rfl⟩
  rw [hℓK] at hℓ hn hK3
  have hKn : ℓ ^ (n : ℕ) = q ^ 2 := by rw [← hn, ← Nat.card_eq_fintype_card, hKq]
  obtain ⟨f, -, rfl⟩ := (Nat.dvd_prime_pow hℓ).1 (⟨q, by rw [hKn, pow_two]⟩ : q ∣ ℓ ^ (n : ℕ))
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · have h1 := Finite.one_lt_card (α := K)
      rw [hKq] at h1
      simp at h1
    · exact h
  have hK2f : Nat.card K = ℓ ^ (2 * f) := by rw [hKq, ← pow_mul, mul_comm]
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hKq σ hσ
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Finite ↥(twistedE6RootGroup K σ) := Subtype.finite
  have hDn : (twistedE6Inn K σ ⊔ twistedE6Diag K σ).Normal := by
    rw [← hker]
    infer_instance
  have hBc := card_inf_twistedE6Inndiag hℓ hf hKq σ hσ hE hEc hED
  have hA : E ⊓ (twistedE6Inn K σ ⊔ twistedE6Diag K σ) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hBc
    norm_num at hBc
  refine seitzHyperGamma_eq_top_of_overgroups Nat.prime_three hE hEc hED hA ?_
  intro x hxE hxD
  obtain ⟨hηo, -, ψ, hψ⟩ := exists_conj_fieldActor_of_not_mem_twistedE6Inndiag hℓ hf K hK2f σ hσ
    Θ hΘ Nat.prime_three (by norm_num) (hE.2 x hxE) hxD
  generalize Θ x = η at hηo hψ
  have hfaith : ∀ a ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ,
      (∀ k ∈ twFJ σ η, a k = k) → a = 1 := by
    intro a ha hfix
    obtain ⟨η', rfl⟩ := exists_fieldActor_eq_of_fix_twFJ hℓ hf hKq σ hσ η hfix
    have h1 : Θ (fieldActor σ η') = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact ha
    have h2 : Θ (fieldActor σ η') = η' := hΘ _ 1 1 η' (by rw [map_one, map_one, one_mul, one_mul])
    rw [h2] at h1
    rw [h1, fieldActor_one]
  have hAD : (E ⊓ (twistedE6Inn K σ ⊔ twistedE6Diag K σ)).map (MulAut.conj ψ).toMonoidHom ≤
      twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
    rintro _ ⟨b, hb, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hDn.conj_mem b hb.2 ψ
  obtain ⟨q₀, hq₀p, ⟨e₂⟩⟩ :=
    nonempty_twFJ_equiv_cat hℓ hf hKq σ hσ Nat.prime_three (by norm_num) hηo
  have hpd : 3 ≠ (⟨.twistedE6 q₀, TauCeti.LieTypeIndex.valid_twistedE6 q₀⟩ :
      TauCeti.ValidLieTypeIndex).1.characteristic := by
    show 3 ≠ (TauCeti.LieTypeIndex.twistedE6 q₀).characteristic
    rw [TauCeti.LieTypeIndex.characteristic_twistedE6, hq₀p]
    exact Ne.symm hK3
  have hgen := le_closure_fixed_of_kfact hS e₂ Nat.prime_three (by norm_num) hpd
    (not_isD2SeitzException_of_chevalleyExc (isChevalleyExcIndex_twistedE6 q₀))
    ((hE.mono (inf_le_left : E ⊓ (twistedE6Inn K σ ⊔ twistedE6Diag K σ) ≤ E)).map
      (MulAut.conj ψ).toMonoidHom)
    (by rw [Subgroup.card_map_of_injective (MulAut.conj ψ).injective, hBc])
    (by
      rintro _ ⟨b, hb, rfl⟩ k hk
      have hbx : Commute b x := congrArg Subtype.val (hE.1.is_comm.comm ⟨b, hb.1⟩ ⟨x, hxE⟩)
      refine mem_twFJ_of_commute hℓ hf hKq σ hσ Nat.prime_three (by norm_num) hηo ?_ hk
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hψ]
      exact hbx.conj ψ)
    (fun a ha hfix => hfaith a (hAD ha) hfix)
  exact exists_overgroupData_of_conj hψ (twFJ_le_twR σ η) hgen hfaith
    fun H hH => le_fixedSubgroup_or_eq_top_of_twFJ_le hℓ hf hKq σ hσ hK3 hq8 hηo hH

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
