module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalRootGrading
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalToral
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedTotalComponents

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.ComponentClassification.CatalogueBPrimeJoin CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open scoped MatrixGroups commutatorElement

section SL2

private theorem false_of_int_ineq (a b : ℤ) (hab : b ^ 2 ≤ a) (hb : 5 ≤ b)
    (h3 : a * (a ^ 2 - 1) ≤ 2 * (b * (b ^ 2 - 1))) : False := by
  have hb0 : 0 < b := by omega
  have hb2 : 25 ≤ b ^ 2 := by nlinarith
  have ha : 25 ≤ a := le_trans hb2 hab
  have h1 : 0 ≤ (a - b ^ 2) * (a ^ 2 + a * b ^ 2 + b ^ 4 - 1) := by
    apply mul_nonneg (by omega)
    nlinarith [sq_nonneg a, sq_nonneg (b ^ 2), mul_pos (by omega : (0 : ℤ) < a)
      (by positivity : (0 : ℤ) < b ^ 2)]
  have h2 : b ^ 6 - b ^ 2 ≤ a ^ 3 - a := by nlinarith [h1]
  have h4 : b ^ 6 - b ^ 2 ≤ 2 * (b ^ 3 - b) := by nlinarith [h3, h2]
  nlinarith [pow_pos hb0 3, pow_pos hb0 2, pow_pos hb0 5, mul_pos (pow_pos hb0 3) (pow_pos hb0 3)]

variable {J : Type*} [Group J] [Finite J] {F₁ F₂ : Type} [Field F₁] [Finite F₁] [Field F₂]
  [Finite F₂]

theorem surjective_of_injective_of_card_eq (hcard : Nat.card F₁ = Nat.card F₂)
    (hodd : Odd (Nat.card F₁)) (h4 : 4 ≤ Nat.card F₁) (hJ : CFSG.IsQuasisimple J)
    (O : Subgroup J) [O.Normal] (hOodd : Odd (Nat.card O)) (eJ : J ⧸ O ≃* SL(2, F₂))
    (ι : SL(2, F₁) →* J) (hι : Function.Injective ι) : Function.Surjective ι := by
  let ρ : SL(2, F₁) →* J ⧸ O := (QuotientGroup.mk' O).comp ι
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    refine eq_bot_of_normal_of_odd_sl2 hodd h4 ρ.ker (MonoidHom.normal_ker ρ) ?_
    have hmem : ∀ x : ρ.ker, ι x.1 ∈ O := fun x =>
      (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.mp x.2)
    let ψ : ρ.ker →* O :=
      { toFun := fun x => ⟨ι x.1, hmem x⟩
        map_one' := Subtype.ext (map_one ι)
        map_mul' := fun x y => Subtype.ext (map_mul ι x.1 y.1) }
    have hψ : Function.Injective ψ := fun x y h => by
      have h' : ι x.1 = ι y.1 := by
        have := congrArg (fun u : O => (u : J)) h
        simpa [ψ] using this
      exact Subtype.ext (hι h')
    exact hOodd.of_dvd_nat (Subgroup.card_dvd_of_injective ψ hψ)
  have hcard' : Nat.card SL(2, F₁) = Nat.card (J ⧸ O) := by
    rw [Nat.card_congr eJ.toEquiv, CFSG.GorensteinWalter.sl2_card_formula,
      CFSG.GorensteinWalter.sl2_card_formula, hcard]
  have hρbij : Function.Bijective ρ := hρinj.bijective_of_nat_card_le hcard'.ge
  have hOc : O ≤ Subgroup.center J := by
    rcases quasisimple_subnormal_subgroups hJ
      (Subgroup.Normal.isSubnormal inferInstance : O.IsSubnormal) with h | h
    · exfalso
      have h0 : Nat.card (J ⧸ O) = 1 := by rw [h]; simp
      rw [← hcard'] at h0
      have : Nontrivial SL(2, F₁) := ⟨⟨-1, 1, sl2_neg_one_ne_one hodd⟩⟩
      exact absurd h0 (Finite.one_lt_card (α := SL(2, F₁))).ne'
    · exact h
  have hJ' : ∀ y : J, ∃ x : SL(2, F₁), ∃ o ∈ O, y = ι x * o := by
    intro y
    obtain ⟨x, hx⟩ := hρbij.2 (QuotientGroup.mk y)
    refine ⟨x, (ι x)⁻¹ * y, ?_, by group⟩
    have : QuotientGroup.mk (ι x) = (QuotientGroup.mk y : J ⧸ O) := hx
    exact QuotientGroup.eq.1 this
  have hcomm : ∀ y₁ y₂ : J, ⁅y₁, y₂⁆ ∈ ι.range := by
    intro y₁ y₂
    obtain ⟨x₁, o₁, ho₁, rfl⟩ := hJ' y₁
    obtain ⟨x₂, o₂, ho₂, rfl⟩ := hJ' y₂
    rw [commutatorElement_mul_central (hOc ho₁) (hOc ho₂), ← map_commutatorElement ι x₁ x₂]
    exact ⟨_, rfl⟩
  have hle : (⊤ : Subgroup J) ≤ ι.range := by
    have h1 : ⁅(⊤ : Subgroup J), (⊤ : Subgroup J)⁆ ≤ ι.range :=
      Subgroup.commutator_le.2 fun g₁ _ g₂ _ => hcomm g₁ g₂
    have hperf : ⁅(⊤ : Subgroup J), (⊤ : Subgroup J)⁆ = (⊤ : Subgroup J) :=
      hJ.1.commutator_eq_top
    rwa [hperf] at h1
  intro y
  exact hle (Subgroup.mem_top y)

omit [Finite J] in
theorem false_of_hom_sl2_of_sq_le (hodd₁ : Odd (Nat.card F₁)) (hodd₂ : Odd (Nat.card F₂))
    (h5₁ : 5 ≤ Nat.card F₁) (h5₂ : 5 ≤ Nat.card F₂) (hJ : CFSG.IsQuasisimple J)
    (O : Subgroup J) [O.Normal] (eJ : J ⧸ O ≃* SL(2, F₂)) (ι : SL(2, F₁) →* J)
    (hker : ∀ A, ι A = 1 → A = 1 ∨ A = -1) (hsq : Nat.card F₂ ^ 2 ≤ Nat.card F₁) : False := by
  set ρ : SL(2, F₁) →* SL(2, F₂) := eJ.toMonoidHom.comp ((QuotientGroup.mk' O).comp ι) with hρ
  have hSL₁ : CFSG.IsQuasisimple SL(2, F₁) :=
    native_isQuasisimple (isQuasisimple_specialLinearGroup_two (by omega))
  have hOc : O ≤ Subgroup.center J := by
    rcases quasisimple_subnormal_subgroups hJ
      (Subgroup.Normal.isSubnormal inferInstance : O.IsSubnormal) with h | h
    · exfalso
      have h0 : Nat.card (J ⧸ O) = 1 := by rw [h]; simp
      rw [Nat.card_congr eJ.toEquiv] at h0
      have : Nontrivial SL(2, F₂) := ⟨⟨-1, 1, sl2_neg_one_ne_one hodd₂⟩⟩
      exact absurd h0 (Finite.one_lt_card (α := SL(2, F₂))).ne'
    · exact h
  have hZ : ∀ A, A ∈ ρ.ker → ι A ∈ O := fun A hA => by
    have h1 : eJ (QuotientGroup.mk (ι A)) = 1 := hA
    exact (QuotientGroup.eq_one_iff _).1 (eJ.injective (h1.trans (map_one eJ).symm))
  rcases quasisimple_subnormal_subgroups hSL₁ (MonoidHom.normal_ker ρ).isSubnormal with hN | hN
  ·
    have hcomm : ∀ A B : SL(2, F₁), ⁅A, B⁆ ∈ Subgroup.center SL(2, F₁) := by
      intro A B
      have h1 : ι ⁅A, B⁆ = 1 := by
        rw [map_commutatorElement]
        have hA := hOc (hZ A (hN ▸ Subgroup.mem_top A))
        exact commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.mp hA (ι B)).symm
      exact CFSG.ABGLocalTools.sl2_mem_center_iff.2 (hker _ h1)
    have hle : (⊤ : Subgroup SL(2, F₁)) ≤ Subgroup.center SL(2, F₁) := by
      have h2 : ⁅(⊤ : Subgroup SL(2, F₁)), (⊤ : Subgroup SL(2, F₁))⁆ ≤
          Subgroup.center SL(2, F₁) := Subgroup.commutator_le.2 fun A _ B _ => hcomm A B
      have hperf : ⁅(⊤ : Subgroup SL(2, F₁)), (⊤ : Subgroup SL(2, F₁))⁆ = ⊤ :=
        hSL₁.1.commutator_eq_top
      rwa [hperf] at h2
    rcases CFSG.ABGLocalTools.sl2_mem_center_iff.1 (hle (Subgroup.mem_top (uSL (1 : F₁)))) with
      h | h
    · have := congrArg (fun A : SL(2, F₁) => (A : Matrix (Fin 2) (Fin 2) F₁) 0 1) h
      simp [coe_uSL] at this
    · have := congrArg (fun A : SL(2, F₁) => (A : Matrix (Fin 2) (Fin 2) F₁) 0 1) h
      simp [coe_uSL] at this
  ·
    have hker2 : Nat.card ρ.ker ≤ 2 := by
      calc Nat.card ρ.ker ≤ Nat.card (Subgroup.center SL(2, F₁)) :=
            Nat.card_le_card_of_injective (Subgroup.inclusion hN) (Subgroup.inclusion_injective hN)
        _ = 2 := CFSG.ABGLocalTools.card_center_sl2 hodd₁
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
    have h2 : Nat.card (SL(2, F₁) ⧸ ρ.ker) ≤ Nat.card SL(2, F₂) :=
      Nat.card_le_card_of_injective _ (QuotientGroup.kerLift_injective ρ)
    have h3 : Nat.card SL(2, F₁) ≤ 2 * Nat.card SL(2, F₂) := by
      rw [h1]
      calc Nat.card (SL(2, F₁) ⧸ ρ.ker) * Nat.card ρ.ker ≤ Nat.card SL(2, F₂) * 2 :=
            Nat.mul_le_mul h2 hker2
        _ = 2 * Nat.card SL(2, F₂) := mul_comm _ _
    rw [CFSG.GorensteinWalter.sl2_card_formula, CFSG.GorensteinWalter.sl2_card_formula] at h3
    set q₁ := Nat.card F₁
    set q₂ := Nat.card F₂
    have hq₁ : 1 ≤ q₁ ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hq₂ : 1 ≤ q₂ ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [hq₁, hq₂] at h3
    have hsq' : (q₂ : ℤ) ^ 2 ≤ q₁ := by exact_mod_cast hsq
    have h5₂' : (5 : ℤ) ≤ q₂ := by exact_mod_cast h5₂
    exact false_of_int_ineq q₁ q₂ hsq' h5₂' h3

end SL2

section TwoComponents

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem eq_orbitGroupC_of_isPComponent_fixedGroup {J₀ : Subgroup (adjointGroup τ k)}
    (hle : J₀ ≤ D.fixedGroup) (hJ₀ : CFSG.IsPComponent 2 (J₀.subgroupOf D.fixedGroup)) :
    J₀ = D.orbitGroupC ∧ CFSG.IsQuasisimple D.orbitGroup := by
  have := D.finite_fixedGroup
  obtain ⟨hN, hS⟩ := normal_isSolvable_subgroupOf (A := D.orbitGroupC) (B := D.fixedGroup)
    (fun x hx a ha => by
      have h1 := D.orbitGroupC_normal.conj_mem ⟨a, D.orbitGroupC_le_fixedGroup ha⟩
        (Subgroup.mem_subgroupOf.2 ha) ⟨x, hx⟩
      exact Subgroup.mem_subgroupOf.1 h1)
    (fun x hx y hy => D.commutator_fixedGroup_le (Subgroup.commutator_mem_commutator hx hy))
  obtain ⟨hJN, hJ₀N⟩ := (isPComponent_subgroupOf_iff_of_isSolvable D.orbitGroupC_le_fixedGroup 2
    Nat.prime_two J₀).1 ⟨hle, hJ₀⟩
  have hequiv : ↥D.orbitGroupC ≃* ↥D.orbitGroup :=
    (Subgroup.subgroupOfEquivOfLe D.orbitGroupC_le_fixedGroup).symm.trans D.orbitGroupEquiv
  rcases D.isQuasisimple_or_isSolvable with hq | hs
  · have hqN : CFSG.IsQuasisimple ↥D.orbitGroupC := (isQuasisimple_congr hequiv).2 hq
    exact ⟨le_antisymm hJN (Subgroup.subgroupOf_eq_top.1
      (eq_top_of_isPComponent_of_isQuasisimple hqN hJ₀N)), hq⟩
  · exfalso
    have : Group.IsSolvable ↥D.orbitGroupC := by
      have := hs
      exact Group.isSolvable_of_surjective (f := hequiv.symm.toMonoidHom) hequiv.symm.surjective
    exact CFSG.ComponentClassification.CatalogueBGeneralLinear.no_pComponent_of_solvable 2 _ hJ₀N

theorem exists_eq_orbitGroupC_of_isPComponent (hX : Finite D.totalFixedGroup)
    {J₀ : Subgroup (adjointGroup τ k)} (hle : J₀ ≤ D.totalFixedGroup)
    (hJ₀ : CFSG.IsPComponent 2 (J₀.subgroupOf D.totalFixedGroup)) :
    ∃ J' : Set.range D.classOrbit, J₀ = (D.withOrbit J').orbitGroupC ∧
      CFSG.IsQuasisimple (D.withOrbit J').orbitGroup := by
  classical
  have hRX := D.kernelFixedGroup_le_totalFixedGroup
  have hUR := D.orbitFixedJoin_le_kernelFixedGroup
  have hR : Finite D.kernelFixedGroup := Finite.of_injective _ (Subgroup.inclusion_injective hRX)
  have hU : Finite D.orbitFixedJoin := Finite.of_injective _ (Subgroup.inclusion_injective hUR)
  obtain ⟨hN1, hS1⟩ := normal_isSolvable_subgroupOf (A := D.kernelFixedGroup)
    (B := D.totalFixedGroup) (fun x hx a ha => D.conj_mem_kernelFixedGroup hx ha)
    (fun x hx y hy => D.commutatorElement_mem_kernelFixedGroup hx hy)
  obtain ⟨hN2, hS2⟩ := normal_isSolvable_subgroupOf (A := D.orbitFixedJoin)
    (B := D.kernelFixedGroup) (fun x hx a ha => D.conj_mem_orbitFixedJoin hx ha)
    (fun x hx y hy => D.commutatorElement_mem_orbitFixedJoin hx hy)
  have := hN1
  have := hS1
  obtain ⟨hJR, hJR'⟩ := (isPComponent_subgroupOf_iff_of_isSolvable hRX 2 Nat.prime_two J₀).1
    ⟨hle, hJ₀⟩
  have := hN2
  have := hS2
  obtain ⟨hJU, hJU'⟩ := (isPComponent_subgroupOf_iff_of_isSolvable hUR 2 Nat.prime_two J₀).1
    ⟨hJR, hJR'⟩
  have hnorm : ∀ J' : Set.range D.classOrbit,
      ((D.withOrbit J').fixedGroup.subgroupOf D.orbitFixedJoin).Normal := fun J' =>
    ⟨fun n hn g => Subgroup.mem_subgroupOf.2
      (D.conj_mem_fixedGroup_withOrbit (hUR g.2) (Subgroup.mem_subgroupOf.1 hn))⟩
  have hjoin : ⨆ J' : Set.range D.classOrbit,
      (D.withOrbit J').fixedGroup.subgroupOf D.orbitFixedJoin = ⊤ :=
    iSup_subgroupOf_iSup_eq_top (fun J' : Set.range D.classOrbit => (D.withOrbit J').fixedGroup)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨J', hJ'⟩ := exists_le_of_le_iSup 2 (J₀.subgroupOf D.orbitFixedJoin) hJU'
    (fun J' : Set.range D.classOrbit =>
      (D.withOrbit J').fixedGroup.subgroupOf D.orbitFixedJoin)
    (fun J' => (hnorm J').isSubnormal) (by rw [hjoin]; exact le_top)
  have hJΓ : J₀ ≤ (D.withOrbit J').fixedGroup := fun x hx =>
    Subgroup.mem_subgroupOf.1 (hJ' (Subgroup.mem_subgroupOf.2 hx : (⟨x, hJU hx⟩ : D.orbitFixedJoin)
      ∈ J₀.subgroupOf D.orbitFixedJoin))
  have hΓfin : Finite (D.withOrbit J').fixedGroup := (D.withOrbit J').finite_fixedGroup
  have hJΓ' : CFSG.IsPComponent 2 (J₀.subgroupOf (D.withOrbit J').fixedGroup) :=
    (isPComponent_subgroupOf_subgroupOf_iff (A := (D.withOrbit J').fixedGroup)
      (B := D.orbitFixedJoin) (L := J₀) (D.fixedGroup_withOrbit_le_orbitFixedJoin J') 2
      Nat.prime_two).1 (pComponent_restrict_overgroup 2 hJU' hJ')
  obtain ⟨heq, hq⟩ := eq_orbitGroupC_of_isPComponent_fixedGroup (D.withOrbit J') hJΓ hJΓ'
  exact ⟨J', heq, hq⟩

end TwoComponents

section Element

variable {τ : Tag} {K : Type} [Field K]

theorem pinnedX_sign_not_mem_rootSubgroup_sup {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hδ : IsRoot τ δ) (hne : δ ≠ γ) (hne' : δ ≠ -γ) {c : K} (hc : c = 1 ∨ c = -1) :
    pinnedX τ K δ c ∉ rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ) := by
  let ℓ : (Fin τ.rank → ℤ) →+ ℤ :=
    { toFun := fun v => iform γ γ * iform v δ - iform δ γ * iform v γ
      map_zero' := by
        have h1 := iform_smul_left (τ := τ) 0 0 δ
        have h2 := iform_smul_left (τ := τ) 0 0 γ
        simp only [smul_zero, zero_mul] at h1 h2
        rw [h1, h2]
        ring
      map_add' := fun u v => by
        rw [iform_add_left, iform_add_left]
        ring }
  have hℓγ : ℓ γ = 0 := by
    change iform γ γ * iform γ δ - iform δ γ * iform γ γ = 0
    rw [iform_comm δ γ]
    ring
  have hℓδ : ℓ δ ≠ 0 := by
    change iform γ γ * iform δ δ - iform δ γ * iform δ γ ≠ 0
    have h := iform_sq_lt hδ hγ hne hne'
    nlinarith
  intro hmem
  have hX : pinnedX τ K δ 1 ∈ rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ) := by
    rcases hc with rfl | rfl
    · exact hmem
    · rw [← inv_mem_iff, pinnedX_neg] at hmem
      simpa using hmem
  exact pinnedX_one_not_mem_gradingSubgroup ℓ hδ hℓδ
    (rootSubgroup_sup_le_gradingSubgroup ℓ hγ hℓγ hX)

end Element

section SingleOrbit

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem orbitMap_of_orbitCard_eq_one {O : Set (Fin τ.rank → ℤ)} (h1 : orbitCard O = 1)
    (A : SL2 (D.orbitField O)) :
    D.orbitMap O A =
      rootSL2 τ k (orbitRoot O) (Matrix.SpecialLinearGroup.map (D.orbitField O).subtype A) := by
  rw [D.orbitMap_eq_prod, h1, show List.range 1 = [0] from rfl, List.map_singleton,
    List.prod_singleton, D.orbitFactor_zero, D.orbitVec_zero]

theorem orbitMap_injective_of_orbitCard_eq_one {O : Set (Fin τ.rank → ℤ)}
    (h1 : orbitCard O = 1) : Function.Injective (D.orbitMap O) := fun A A' h => by
  rw [orbitMap_of_orbitCard_eq_one D h1, orbitMap_of_orbitCard_eq_one D h1] at h
  exact D.map_subtype_injective O (D.rootSL2_injective _ h)

theorem finite_orbitField {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    Finite (D.orbitField O) := by
  have hpos : 0 < Nat.card (D.orbitField O) := by
    rw [D.card_orbitField hO]
    exact pow_pos (by have := D.three_le_q; omega) _
  exact Nat.finite_of_card_ne_zero hpos.ne'

theorem odd_card_orbitField {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    Odd (Nat.card (D.orbitField O)) := by
  rw [D.card_orbitField hO]
  exact D.odd_q.pow

theorem orbits_eq_singleton_of_classical {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.IsQuasisimple Y) (φ : Y ≃* D.orbitGroup) (O : Subgroup Y) [O.Normal]
    (hOodd : Odd (Nat.card O)) {F₂ : Type} [Field F₂] [Finite F₂] (hF₂ : Nat.card F₂ = D.q)
    (h5 : 5 ≤ D.q) (eY : Y ⧸ O ≃* SL(2, F₂)) :
    ∃ O₀, O₀ ∈ D.orbits ∧ D.orbits = {O₀} ∧ orbitCard O₀ = 1 := by
  classical
  have hodd₂ : Odd (Nat.card F₂) := hF₂ ▸ D.odd_q
  have h5₂ : 5 ≤ Nat.card F₂ := hF₂ ▸ h5
  let ι : ∀ {O' : Set (Fin τ.rank → ℤ)}, O' ∈ D.orbits → SL(2, D.orbitField O') →* Y :=
    fun hO' => φ.symm.toMonoidHom.comp (D.orbitGroupHom hO')
  have hιmap : ∀ {O' : Set (Fin τ.rank → ℤ)} (hO' : O' ∈ D.orbits) (A : SL(2, D.orbitField O')),
      ((φ (ι hO' A) : D.orbitGroup) : ModGL τ k) = D.orbitMap O' A := fun _ _ => by
    simp [ι, orbitGroupHom]
    rfl
  have hker : ∀ {O' : Set (Fin τ.rank → ℤ)} (hO' : O' ∈ D.orbits) (A : SL(2, D.orbitField O')),
      ι hO' A = 1 → A = 1 ∨ A = -1 := by
    intro O' hO' A hA
    refine D.eq_one_or_neg_one_of_orbitMap_eq_one hO' ?_
    rw [← hιmap hO' A, hA, map_one]
    rfl
  have hcard1 : ∀ {O' : Set (Fin τ.rank → ℤ)}, O' ∈ D.orbits → orbitCard O' = 1 := by
    intro O' hO'
    by_contra hne
    have h2 : 2 ≤ orbitCard O' := by have := D.orbitCard_pos hO'; omega
    have := finite_orbitField D hO'
    have hsq : Nat.card F₂ ^ 2 ≤ Nat.card (D.orbitField O') := by
      rw [hF₂, D.card_orbitField hO']
      exact Nat.pow_le_pow_right (by omega) h2
    have h5₁ : 5 ≤ Nat.card (D.orbitField O') :=
      h5₂.trans ((Nat.le_self_pow (by norm_num) _).trans hsq)
    exact false_of_hom_sl2_of_sq_le (odd_card_orbitField D hO') hodd₂ h5₁ h5₂ hY O eY (ι hO')
      (hker hO') hsq
  have hinj : ∀ {O' : Set (Fin τ.rank → ℤ)} (hO' : O' ∈ D.orbits), Function.Injective (ι hO') :=
    fun {O'} hO' A A' h => orbitMap_injective_of_orbitCard_eq_one D (hcard1 hO') (by
      rw [← hιmap hO' A, ← hιmap hO' A', h])
  have hsurj : ∀ {O' : Set (Fin τ.rank → ℤ)} (hO' : O' ∈ D.orbits),
      Function.Surjective (ι hO') := by
    intro O' hO'
    have := finite_orbitField D hO'
    have hc : Nat.card (D.orbitField O') = Nat.card F₂ := by
      rw [D.card_orbitField hO', hcard1 hO', pow_one, hF₂]
    exact surjective_of_injective_of_card_eq hc (odd_card_orbitField D hO') (by omega) hY O hOodd
      eY (ι hO') (hinj hO')
  have hsingle : ∀ {O₁ O₂ : Set (Fin τ.rank → ℤ)}, O₁ ∈ D.orbits → O₂ ∈ D.orbits → O₁ = O₂ := by
    intro O₁ O₂ h₁ h₂
    by_contra hne
    have hO₁ := D.eq_singleton_of_orbitCard_eq_one h₁ (hcard1 h₁)
    have hO₂ := D.eq_singleton_of_orbitCard_eq_one h₂ (hcard1 h₂)
    have hβne : orbitRoot O₂ ≠ orbitRoot O₁ := fun h => hne (by rw [hO₁, hO₂, h])
    have hr₁ : IsRoot τ (orbitRoot O₁) := D.isRoot_of_mem_orbits h₁ (D.orbitRoot_mem h₁)
    have hr₂ : IsRoot τ (orbitRoot O₂) := D.isRoot_of_mem_orbits h₂ (D.orbitRoot_mem h₂)
    have hh₁ : 0 < height (orbitRoot O₁) :=
      (mem_posRoots_of_mem_unionSimpleRoots
        (D.mem_unionSimpleRoots_of_mem_orbits h₁ (D.orbitRoot_mem h₁))).2
    have hh₂ : 0 < height (orbitRoot O₂) :=
      (mem_posRoots_of_mem_unionSimpleRoots
        (D.mem_unionSimpleRoots_of_mem_orbits h₂ (D.orbitRoot_mem h₂))).2
    have hβne' : orbitRoot O₂ ≠ -orbitRoot O₁ := fun h => by
      have := congrArg height h
      rw [height_neg] at this
      omega
    have hxmem : D.orbitMap O₂ (uSL 1) ∈ D.orbitGroup := D.orbitMap_mem_orbitGroup h₂ _
    obtain ⟨A, hA⟩ := hsurj h₁ (φ.symm ⟨_, hxmem⟩)
    have hAx : D.orbitMap O₁ A = D.orbitMap O₂ (uSL 1) := by
      rw [← hιmap h₁ A, hA, MulEquiv.apply_symm_apply]
    have hin₁ : D.orbitMap O₁ A ∈ rootSubgroup τ k (orbitRoot O₁) ⊔
        rootSubgroup τ k (-orbitRoot O₁) := by
      rw [orbitMap_of_orbitCard_eq_one D (hcard1 h₁),
        ← (exceptional_Lang_root_rank_one_torus_transport τ k hr₁).1]
      exact ⟨_, rfl⟩
    have hx₂ : D.orbitMap O₂ (uSL 1) =
        pinnedX τ k (orbitRoot O₂) ((pinnedData τ (orbitRoot O₂)).2.2 • (1 : k)) := by
      have h := D.orbitX_of_orbitCard_eq_one (hcard1 h₂) 1
      rw [rootSL2_uSL_eq] at h
      exact h
    rw [hAx, hx₂] at hin₁
    refine pinnedX_sign_not_mem_rootSubgroup_sup hr₁ hr₂ hβne hβne' ?_ hin₁
    rcases pinnedSign_eq τ (orbitRoot O₂) with h | h <;> rw [h] <;> simp
  have hne : D.orbits.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hbot : D.orbitGroup = ⊥ := by
      rw [eq_bot_iff]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨O', hO', -⟩
      rw [h] at hO'
      exact absurd hO' (Set.notMem_empty O')
    have hY1 : ∀ y : Y, y = 1 := fun y => φ.injective (Subtype.ext (by
      have h2 : ((φ y : D.orbitGroup) : ModGL τ k) ∈ (⊥ : Subgroup (ModGL τ k)) := by
        rw [← hbot]
        exact (φ y).2
      rw [Subgroup.mem_bot] at h2
      rw [h2]
      exact (congrArg Subtype.val (map_one φ)).symm))
    obtain ⟨x, hx⟩ := eY.surjective (-1)
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hY1 y, QuotientGroup.mk_one, map_one] at hx
    exact sl2_neg_one_ne_one hodd₂ hx.symm
  obtain ⟨O₀, hO₀⟩ := hne
  exact ⟨O₀, hO₀, Set.eq_singleton_iff_unique_mem.2 ⟨hO₀, fun O' hO' => hsingle hO' hO₀⟩,
    hcard1 hO₀⟩

theorem simpleRootsJ_eq_singleton_of_orbits_eq {O₀ : Set (Fin τ.rank → ℤ)}
    (hA : D.orbits = {O₀}) (h1 : orbitCard O₀ = 1) : D.simpleRootsJ = {orbitRoot O₀} := by
  have hO₀ : O₀ ∈ D.orbits := by rw [hA]; exact Set.mem_singleton O₀
  have hsing := D.eq_singleton_of_orbitCard_eq_one hO₀ h1
  ext β
  rw [Set.mem_singleton_iff]
  constructor
  · intro hβ
    have h2 : thetaOrbit D.θ β ∈ D.orbits := D.thetaOrbit_mem_orbits hβ
    rw [hA, Set.mem_singleton_iff] at h2
    have h3 : β ∈ O₀ := by rw [← h2]; exact self_mem_thetaOrbit _ _
    rw [hsing, Set.mem_singleton_iff] at h3
    exact h3
  · rintro rfl
    exact D.subset_simpleRootsJ_of_mem_orbits hO₀ (D.orbitRoot_mem hO₀)

end SingleOrbit

section Classical

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)

theorem exists_eq_range_orbitMapHom_of_isPComponent (hX : Finite D.totalFixedGroup)
    {J₀ : Subgroup (adjointGroup τ k)} (hle : J₀ ≤ D.totalFixedGroup)
    (hJ₀ : CFSG.IsPComponent 2 (J₀.subgroupOf D.totalFixedGroup))
    {Y : Type} [Group Y] (φ : Y ≃* J₀) (O : Subgroup Y) [O.Normal] (hO : Odd (Nat.card O))
    {F₂ : Type} [Field F₂] [Finite F₂] (hF₂ : Nat.card F₂ = D.q) (h5 : 5 ≤ D.q)
    (eY : Y ⧸ O ≃* SL(2, F₂)) :
    ∃ (J' : Set.range D.classOrbit) (O₀ : Set (Fin τ.rank → ℤ))
      (hO₀ : O₀ ∈ (D.withOrbit J').orbits),
      (D.withOrbit J').orbits = {O₀} ∧ orbitCard O₀ = 1 ∧
        J₀ = ((D.withOrbit J').orbitMapHom hO₀).range.subgroupOf (adjointGroup τ k) := by
  obtain ⟨J', hJ', hq⟩ := exists_eq_orbitGroupC_of_isPComponent D hX hle hJ₀
  have hfinJ : Finite J₀ := Finite.of_injective _ (Subgroup.inclusion_injective hle)
  have hfinY : Finite Y := Finite.of_equiv _ φ.symm.toEquiv
  let eC : (D.withOrbit J').orbitGroupC ≃* (D.withOrbit J').orbitGroup :=
    Subgroup.subgroupOfEquivOfLe (D.withOrbit J').orbitGroup_le_adjointGroup
  let φ' : Y ≃* (D.withOrbit J').orbitGroup := (φ.trans (MulEquiv.subgroupCongr hJ')).trans eC
  have hY : CFSG.IsQuasisimple Y := (isQuasisimple_congr φ').2 hq
  obtain ⟨O₀, hO₀, hA, h1⟩ := orbits_eq_singleton_of_classical (D.withOrbit J') hY φ' O hO hF₂ h5 eY
  refine ⟨J', O₀, hO₀, hA, h1, ?_⟩
  rw [hJ']
  show (D.withOrbit J').orbitGroup.subgroupOf (adjointGroup τ k) = _
  congr 1
  refine SetLike.coe_injective ?_
  rw [← (D.withOrbit J').range_orbitMap_eq_of_orbits_eq hA]
  rfl

theorem exists_eq_rootSL2_of_isPComponent (hX : Finite D.totalFixedGroup)
    {J₀ : Subgroup (adjointGroup τ k)} (hle : J₀ ≤ D.totalFixedGroup)
    (hJ₀ : CFSG.IsPComponent 2 (J₀.subgroupOf D.totalFixedGroup))
    {Y : Type} [Group Y] (φ : Y ≃* J₀) (O : Subgroup Y) [O.Normal] (hO : Odd (Nat.card O))
    {F₂ : Type} [Field F₂] [Finite F₂] (hF₂ : Nat.card F₂ = D.q) (h5 : 5 ≤ D.q)
    (eY : Y ⧸ O ≃* SL(2, F₂)) :
    ∃ (J' : Set.range D.classOrbit) (β₀ : Fin τ.rank → ℤ),
      β₀ ∈ kernelRoots D.χ ∧ D.θ (toReal β₀) = toReal β₀ ∧
        unionSimpleRoots D.χ (J' : Set (KernelComponent D.χ)) = {β₀} ∧
        ∀ x : adjointGroup τ k, x ∈ J₀ ↔ ∃ A : SL2 (D.orbitField {β₀}),
          (x : ModGL τ k) =
            rootSL2 τ k β₀ (Matrix.SpecialLinearGroup.map (D.orbitField {β₀}).subtype A) := by
  obtain ⟨J', O₀, hO₀, hA, h1, hJ⟩ :=
    exists_eq_range_orbitMapHom_of_isPComponent D hX hle hJ₀ φ O hO hF₂ h5 eY
  have hroot := (D.withOrbit J').orbitRoot_mem hO₀
  obtain ⟨β₀, rfl⟩ : ∃ β₀, O₀ = {β₀} :=
    ⟨_, (D.withOrbit J').eq_singleton_of_orbitCard_eq_one hO₀ h1⟩
  have hroot' : orbitRoot ({β₀} : Set (Fin τ.rank → ℤ)) = β₀ := Set.mem_singleton_iff.1 hroot
  refine ⟨J', β₀, ?_, ?_, ?_, fun x => ?_⟩
  · have := (D.withOrbit J').orbitRoot_mem_kernelRoots hO₀
    rwa [hroot'] at this
  · have := (D.withOrbit J').theta_orbitRoot_of_orbitCard_eq_one hO₀ h1
    rwa [hroot'] at this
  · have h2 := simpleRootsJ_eq_singleton_of_orbits_eq (D.withOrbit J') hA h1
    rw [hroot'] at h2
    exact ((D.withOrbit J').simpleRootsJ_eq).symm.trans h2
  · rw [hJ, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
    constructor
    · rintro ⟨A, hA'⟩
      have h3 := orbitMap_of_orbitCard_eq_one (D.withOrbit J') h1 A
      rw [hroot'] at h3
      exact ⟨A, hA'.symm.trans h3⟩
    · rintro ⟨A, hA'⟩
      have h3 := orbitMap_of_orbitCard_eq_one (D.withOrbit J') h1 A
      rw [hroot'] at h3
      exact ⟨A, h3.trans hA'.symm⟩

theorem exists_eq_rootSL2_of_isPComponent_of_mulEquiv (hX : Finite D.totalFixedGroup)
    {X : Type*} [Group X] (eqv : D.totalFixedGroup ≃* X) {J : Subgroup X}
    (hJ : CFSG.IsPComponent 2 J) {Y : Type} [Group Y] (φ : Y ≃* J) (O : Subgroup Y)
    [O.Normal] (hO : Odd (Nat.card O)) {F₂ : Type} [Field F₂] [Finite F₂]
    (hF₂ : Nat.card F₂ = D.q) (h5 : 5 ≤ D.q) (eY : Y ⧸ O ≃* SL(2, F₂)) :
    ∃ (J' : Set.range D.classOrbit) (β₀ : Fin τ.rank → ℤ),
      β₀ ∈ kernelRoots D.χ ∧ D.θ (toReal β₀) = toReal β₀ ∧
        unionSimpleRoots D.χ (J' : Set (KernelComponent D.χ)) = {β₀} ∧
        ∀ y : D.totalFixedGroup, eqv y ∈ J ↔ ∃ A : SL2 (D.orbitField {β₀}),
          ((y : adjointGroup τ k) : ModGL τ k) =
            rootSL2 τ k β₀ (Matrix.SpecialLinearGroup.map (D.orbitField {β₀}).subtype A) := by
  set J₁ : Subgroup D.totalFixedGroup := J.map eqv.symm.toMonoidHom with hJ₁
  set J₀ : Subgroup (adjointGroup τ k) := J₁.map D.totalFixedGroup.subtype with hJ₀
  have hle : J₀ ≤ D.totalFixedGroup := Subgroup.map_subtype_le _
  have hsub : J₀.subgroupOf D.totalFixedGroup = J₁ :=
    Subgroup.comap_map_eq_self_of_injective D.totalFixedGroup.subtype_injective J₁
  have hcomp : CFSG.IsPComponent 2 (J₀.subgroupOf D.totalFixedGroup) := by
    rw [hsub]
    exact isPComponent_map_of_isPComponent 2 eqv.symm hJ
  let φ' : Y ≃* J₀ := φ.trans ((J.equivMapOfInjective eqv.symm.toMonoidHom
    eqv.symm.injective).trans (J₁.equivMapOfInjective D.totalFixedGroup.subtype
      D.totalFixedGroup.subtype_injective))
  obtain ⟨J', β₀, h1, h2, h3, h4⟩ :=
    exists_eq_rootSL2_of_isPComponent D hX hle hcomp φ' O hO hF₂ h5 eY
  refine ⟨J', β₀, h1, h2, h3, fun y => ?_⟩
  have hy : eqv y ∈ J ↔ (y : adjointGroup τ k) ∈ J₀ := by
    constructor
    · intro h
      exact ⟨y, ⟨eqv y, h, by simp⟩, rfl⟩
    · rintro ⟨z, ⟨w, hw, rfl⟩, hzy⟩
      have : (eqv.symm.toMonoidHom w) = y := Subtype.ext hzy
      rw [← this]
      simpa using hw
  rw [hy]
  exact h4 y

end Classical

end CFSG.ClassicalInvolution.ModelFacts
