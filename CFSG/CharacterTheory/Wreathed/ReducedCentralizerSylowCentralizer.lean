module

public import CFSG.CharacterTheory.Wreathed.FullCentralizerFromProjectiveModel
public import CFSG.CharacterTheory.Wreathed.ReducedCentralizerSylowCentralizerSupport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo

public section

namespace CFSG.Wreathed.ReducedCentralizerSylow

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.Semidihedral.OddFieldLift

theorem actual_reduced_centralizer_defining_sylow_centralizer_is_center_times_sylow
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f) (_hq : 5 ≤ p ^ f)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    let H := centralizerOddCoreQuotient n S e
    let M := CFSG.layer H
    (∀ P : Sylow p M,
      let PH := (P : Subgroup M).map M.subtype
      IsElementaryAbelian p P ∧ Nat.card P = p ^ f ∧
        Subgroup.centralizer (PH : Set H) = PH ⊔ Subgroup.center H ∧
        PH ⊓ Subgroup.center H = ⊥ ∧
        Nat.card (Subgroup.centralizer (PH : Set H)) = 2 ^ n * p ^ f ∧
        ∀ g ∈ Subgroup.centralizer (PH : Set H), Odd (orderOf g) →
          ∃ k : ℕ, orderOf g = p ^ k) ∧
      IsCyclic (Subgroup.center H) ∧ Nat.card (Subgroup.center H) = 2 ^ n := by
  intro H M
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, _, _, hcard, hchar, -, θ, ρ, η, hin, hρ, -, hdata⟩ :=
    FullCentralizerFromProjectiveModel.actual_projective_layer_model_determines_full_centralizer
      hnonab n hn S e hfour p f hp hpodd hf hmodel
  have hstr := hdata.structural
  refine ⟨fun P => ?_, hin.center_cyclic, hin.center_card⟩
  intro PH
  have : CharP F p := by
    rw [← hchar]
    exact ringChar.charP F
  let τ := centralizerFullQuotientMap n hn S e
  have hkerτ : τ.ker = Subgroup.center H := by
    change (QuotientGroup.mk' (centralizerFullCenterImage n hn S e)).ker = _
    rw [QuotientGroup.ker_mk']
    exact hstr.full_center
  let ψ : M →* Equiv.Perm (Omega F) := (slCoordinateAction F).comp η.toMonoidHom
  have hψ : ∀ v : M, ψ v = (ρ (τ v)).val := fun v => hstr.action_values v
  have hψG : ∀ v : M, ψ v ∈ coordinateG F := fun v => by
    rw [← WreathedCentralCover.slCoordinateAction_range F]
    exact ⟨η v, rfl⟩
  let ψG : M →* coordinateG F := ψ.codRestrict _ hψG
  have hψGsurj : Function.Surjective ψG := by
    intro y
    have hy : (y : Equiv.Perm (Omega F)) ∈ (slCoordinateAction F).range := by
      rw [WreathedCentralCover.slCoordinateAction_range F]
      exact y.2
    obtain ⟨X, hX⟩ := hy
    refine ⟨η.symm X, Subtype.ext ?_⟩
    change slCoordinateAction F (η (η.symm X)) = y
    rw [MulEquiv.apply_symm_apply, hX]
  let Q : Sylow p (coordinateG F) := P.mapSurjective hψGsurj
  obtain ⟨P0, hP0, -⟩ := CFSG.LinearGroups.linear_two_point_Sylow_bijection p F
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (coordinateG F) P0 Q
  have hQ : (Q : Subgroup (coordinateG F)) =
      ((coordinateU F).subgroupOf (coordinateG F)).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, hP0]
    rfl
  have hQP : (Q : Subgroup (coordinateG F)) = (P : Subgroup M).map ψG := rfl
  have hinj : Function.Injective (ψG.subgroupMap (P : Subgroup M)) := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have hv1 : ψ v = 1 := congrArg Subtype.val (congrArg Subtype.val hv)
    have hcen : η v ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      rw [← slCoordinateAction_ker]
      exact hv1
    obtain ⟨r, hr2, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcen
    have hsq : (v : M) ^ 2 = 1 := by
      apply η.injective
      rw [map_pow, map_one]
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, ← hr, ← map_pow]
      simp only [Fintype.card_fin] at hr2
      rw [hr2, map_one, Matrix.SpecialLinearGroup.coe_one]
    obtain ⟨k, hk⟩ := P.isPGroup' v
    have h1 : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one (Subtype.ext hsq)
    have h2 : orderOf v ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
    have hcop : Nat.Coprime 2 (p ^ k) :=
      Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hpodd))
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  let eP : P ≃* Multiplicative F :=
    ((MulEquiv.ofBijective _ ⟨hinj, ψG.subgroupMap_surjective _⟩).trans
      ((MulEquiv.subgroupCongr hQP.symm).trans ((MulEquiv.subgroupCongr hQ).trans
        (((coordinateU F).subgroupOf (coordinateG F)).equivMapOfInjective _
          (MulAut.conj g).injective).symm))).trans
      ((Subgroup.subgroupOfEquivOfLe CFSG.LinearGroups.coordinateU_le_coordinateG).trans
        (CFSG.LinearGroups.coordinateUEquiv F).symm)
  have hEA : IsElementaryAbelian p P := by
    have := isElementaryAbelian_multiplicative p F
    exact isElementaryAbelian_of_mulEquiv eP.symm
  have hcardP : Nat.card P = p ^ f := by
    rw [Nat.card_congr eP.toEquiv, Nat.card_congr Multiplicative.toAdd, hcard]
  have hcardPH : Nat.card PH = p ^ f := by
    rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact hcardP
  have hPHcomm : ∀ a ∈ PH, ∀ b ∈ PH, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h := (isMulCommutative_iff.mp hEA.toIsMulCommutative) ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg (fun x : P => ((x : M) : H)) h
  have hcop : Nat.Coprime (Nat.card PH) (Nat.card (Subgroup.center H)) := by
    rw [hcardPH, hin.center_card]
    exact Nat.Coprime.pow f n ((Nat.coprime_primes hp Nat.prime_two).mpr hpodd)
  have hdisj : Disjoint PH (Subgroup.center H) := Subgroup.disjoint_of_coprime_natCard hcop
  have hinf : PH ⊓ Subgroup.center H = ⊥ := disjoint_iff.mp hdisj
  have hcent : Subgroup.centralizer (PH : Set H) = PH ⊔ Subgroup.center H := by
    apply le_antisymm
    · intro c hc
      let σ : Equiv.Perm (Omega F) := (ρ (τ c)).val
      have hσQ : ∀ y ∈ (Q : Subgroup (coordinateG F)),
          σ * (y : Equiv.Perm (Omega F)) = (y : Equiv.Perm (Omega F)) * σ := by
        intro y hy
        rw [hQP] at hy
        obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hy
        have hvc : (v : H) * c = c * (v : H) :=
          Subgroup.mem_centralizer_iff.mp hc (v : H) ⟨v, hv, rfl⟩
        change (ρ (τ c)).val * ψ v = ψ v * (ρ (τ c)).val
        rw [hψ v]
        have h := congrArg (fun x : H => ((ρ (τ x) : coordinateE F) : Equiv.Perm (Omega F))) hvc
        simp only [map_mul, Subgroup.coe_mul] at h
        exact h.symm
      have hσ' : (g : Equiv.Perm (Omega F))⁻¹ * σ * g ∈ coordinateU F := by
        apply mem_coordinateU_of_forall_commute
        intro b
        have hbU : translation F b ∈ coordinateU F := Subgroup.subset_closure ⟨b, rfl⟩
        have hy : g * ⟨translation F b, CFSG.LinearGroups.coordinateU_le_coordinateG hbU⟩ *
            g⁻¹ ∈ (Q : Subgroup (coordinateG F)) := by
          rw [hQ]
          exact ⟨⟨translation F b, _⟩, hbU, rfl⟩
        have h := hσQ _ hy
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
        calc (g : Equiv.Perm (Omega F))⁻¹ * σ * g * translation F b
            = (g : Equiv.Perm (Omega F))⁻¹ *
                (σ * (g * translation F b * (g : Equiv.Perm (Omega F))⁻¹)) * g := by group
          _ = (g : Equiv.Perm (Omega F))⁻¹ *
                ((g * translation F b * (g : Equiv.Perm (Omega F))⁻¹) * σ) * g := by rw [h]
          _ = translation F b * ((g : Equiv.Perm (Omega F))⁻¹ * σ * g) := by group
      have hσG : (g : Equiv.Perm (Omega F))⁻¹ * σ * g ∈ coordinateG F :=
        CFSG.LinearGroups.coordinateU_le_coordinateG hσ'
      have hyQ : g * ⟨(g : Equiv.Perm (Omega F))⁻¹ * σ * g, hσG⟩ * g⁻¹ ∈
          (Q : Subgroup (coordinateG F)) := by
        rw [hQ]
        exact ⟨⟨_, hσG⟩, hσ', rfl⟩
      rw [hQP] at hyQ
      obtain ⟨v₀, hv₀, hv₀eq⟩ := Subgroup.mem_map.mp hyQ
      have hψv₀ : ψ v₀ = σ := by
        have h := congrArg Subtype.val hv₀eq
        simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
        change ψ v₀ = _ at h
        rw [h]
        group
      have hτ : τ v₀ = τ c := by
        apply hρ
        apply Subtype.ext
        rw [← hψ v₀]
        exact hψv₀
      have hz : (v₀ : H)⁻¹ * c ∈ Subgroup.center H := by
        rw [← hkerτ, MonoidHom.mem_ker, map_mul, map_inv, hτ, inv_mul_cancel]
      have hc' : c = (v₀ : H) * ((v₀ : H)⁻¹ * c) := by group
      rw [hc']
      exact Subgroup.mul_mem_sup ⟨v₀, hv₀, rfl⟩ hz
    · refine sup_le (fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb => hPHcomm b hb a ha)
        (Subgroup.center_le_centralizer _)
  have hcardC : Nat.card (Subgroup.centralizer (PH : Set H)) = 2 ^ n * p ^ f := by
    have hZN : Subgroup.center H ≤ Subgroup.normalizer (PH : Set H) := fun z hz =>
      Subgroup.mem_normalizer_iff.mpr fun h => by
        rw [← Subgroup.mem_center_iff.mp hz h, mul_inv_cancel_right]
    rw [hcent, GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer PH
      (Subgroup.center H) hZN hdisj, hcardPH, hin.center_card, mul_comm]
  refine ⟨hEA, hcardP, hcent, hinf, hcardC, ?_⟩
  intro x hx hodd
  rw [hcent, Subgroup.mem_sup_of_normal_right] at hx
  obtain ⟨u, hu, z, hz, rfl⟩ := hx
  have hzc : Commute u z := Subgroup.mem_center_iff.mp hz u
  have hpow : (u * z) ^ orderOf (u * z) = 1 := pow_orderOf_eq_one _
  rw [hzc.mul_pow] at hpow
  have hzpow : z ^ orderOf (u * z) = 1 := by
    have hmem : z ^ orderOf (u * z) ∈ PH ⊓ Subgroup.center H := by
      refine ⟨?_, Subgroup.pow_mem _ hz _⟩
      have : z ^ orderOf (u * z) = (u ^ orderOf (u * z))⁻¹ := eq_inv_of_mul_eq_one_right hpow
      rw [this]
      exact PH.inv_mem (PH.pow_mem hu _)
    rw [hinf] at hmem
    exact hmem
  have hz1 : z = 1 := by
    have h1 : orderOf z ∣ orderOf (u * z) := orderOf_dvd_of_pow_eq_one hzpow
    have h2 : orderOf z ∣ 2 ^ n := by
      rw [← hin.center_card]
      exact Subgroup.orderOf_dvd_natCard _ hz
    have hcop2 : Nat.Coprime (orderOf (u * z)) (2 ^ n) :=
      Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hodd)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop2 h1 h2)
  subst hz1
  rw [mul_one]
  have hdvd : orderOf u ∣ p ^ f := by
    rw [← hcardPH]
    exact Subgroup.orderOf_dvd_natCard _ hu
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  exact ⟨k, hk⟩

end CFSG.Wreathed.ReducedCentralizerSylow
