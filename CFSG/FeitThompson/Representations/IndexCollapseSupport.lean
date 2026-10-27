module

public import CFSG.FeitThompson.Representations.TypeThreeFourPrincipalRowProjection
import CFSG.FeitThompson.Representations.AbelianByAbelianFrobeniusCharacters

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace ScalarCoreCoherence.IsScalarCoreConfig

variable {L : Type*} [Group L] {p q : ℕ} {K H U B H0 : Subgroup L} [H.Normal] [H0.Normal]
  {Eline : ZMod q → Subgroup (↥H ⧸ H0.subgroupOf H)} {A : Set L}
  (hc : IsScalarCoreConfig p q K H U B H0 Eline A)

include hc

theorem exists_axisIrrQuotient_commutator [Finite L] [Fintype (L ⧸ H0)] :
    ∃ T : Finset (↥(Subgroup.map (QuotientGroup.mk' H0) K) → ℂ),
      (∀ θ ∈ T, θ ∈ Irr ↥(Subgroup.map (QuotientGroup.mk' H0) K)) ∧
      (∀ θ ∈ T, ∀ x : ↥K, (x : L) ∈ (⁅U, U⁆ : Subgroup L) →
        θ (quotSubgroupHom H0 K x) = θ 1) ∧
      (∀ θ ∈ T, ∃ x : ↥K, (x : L) ∈ H ∧ θ (quotSubgroupHom H0 K x) ≠ θ 1) ∧
      (∀ θ ∈ T, θ 1 = ((lineFixer H H0 U (Eline 0)).relIndex U : ℂ)) ∧
      (∀ θ ∈ T, indClassFun (Subgroup.map (QuotientGroup.mk' H0) K) θ ∈ Irr (L ⧸ H0)) ∧
      T.card * (lineFixer H H0 U (Eline 0)).relIndex U ^ 2
        = (p - 1) * (⁅U, U⁆ : Subgroup L).relIndex U := by
  classical
  have _hfp : Fact p.Prime := ⟨hc.p_prime⟩
  obtain ⟨W, _hW1, _hW2, Sys, e, ha, hKmap, hU, hH⟩ := hc.exists_axisSystem
  have _hfU : Finite ↥U := Subtype.finite
  obtain ⟨T0, hT0mem, -, hT0card⟩ := Sys.exists_axisIrr_transversal
  refine ⟨T0.image (Sys.transportChar e hKmap), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro θ' hθ'
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.1 hθ'
    exact Sys.transportChar_mem_Irr e hKmap (Sys.axisIrr_subset_Irr (hT0mem θ hθ))
  · intro θ' hθ' x hx
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.1 hθ'
    have hxU : (x : L) ∈ U := Subgroup.commutator_le_self U hx
    have hucomm : (⟨(x : L), hxU⟩ : ↥U) ∈ commutator ↥U := by
      rw [commutator_eq_subgroupOf_commutator]
      exact Subgroup.mem_subgroupOf.2 hx
    rw [Sys.transportChar_apply e hKmap θ (x := SemidirectProduct.inr ⟨(x : L), hxU⟩) (by
        rw [hU ⟨(x : L), hxU⟩, coe_quotSubgroupHom_apply]),
      Sys.transportChar_one e hKmap]
    exact (Sys.mem_axisIrr.1 (hT0mem θ hθ)).2.1 _ hucomm
  · intro θ' hθ'
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.1 hθ'
    obtain ⟨v, hvne⟩ := Sys.exists_apply_inl_ne_of_mem_axisIrr (hT0mem θ hθ)
    obtain ⟨h, hhH, hhe⟩ := hH v
    refine ⟨⟨h, hc.H_le_K hhH⟩, hhH, ?_⟩
    rw [Sys.transportChar_apply e hKmap θ (x := SemidirectProduct.inl v) (by
        rw [hhe, coe_quotSubgroupHom_apply]), Sys.transportChar_one e hKmap]
    exact hvne
  · intro θ' hθ'
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.1 hθ'
    rw [Sys.transportChar_one e hKmap, Sys.apply_one_of_mem_axisIrr (hT0mem θ hθ), ha]
  · intro θ' hθ'
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.1 hθ'
    exact Sys.indClassFun_transportChar_mem_Irr e hKmap (hT0mem θ hθ)
  · rw [Finset.card_image_of_injective _ (Sys.transportChar_injective e hKmap), ← ha,
      Subgroup.relIndex, ← commutator_eq_subgroupOf_commutator]
    exact hT0card

theorem exists_mem_Irr_axis [Fintype L] :
    ∃ θ : ↥K → ℂ, θ ∈ Irr ↥K ∧
      (∀ x : ↥K, (x : L) ∈ (⁅U, U⁆ : Subgroup L) → θ x = θ 1) ∧
      (∃ x : ↥K, (x : L) ∈ H ∧ θ x ≠ θ 1) ∧
      θ 1 = ((lineFixer H H0 U (Eline 0)).relIndex U : ℂ) ∧
      indClassFun K θ ∈ Irr L := by
  classical
  have _hfq : Fintype (L ⧸ H0) := Fintype.ofFinite _
  obtain ⟨T, hIrr, hker, hdet, hdeg, hindIrr, hcard⟩ := hc.exists_axisIrrQuotient_commutator
  have hH0K : H0 ≤ K := hc.H0_le_H.trans hc.H_le_K
  obtain ⟨θ, hθ⟩ : T.Nonempty := by
    rw [← Finset.card_pos]
    have hppos : 0 < p - 1 := by have := hc.three_le_p; omega
    have hvpos : 0 < (⁅U, U⁆ : Subgroup L).relIndex U :=
      Nat.pos_of_ne_zero (relIndex_ne_zero _ _)
    rcases Nat.eq_zero_or_pos T.card with h0 | h0
    · rw [h0, zero_mul] at hcard
      exact absurd hcard.symm (Nat.mul_ne_zero hppos.ne' hvpos.ne')
    · exact h0
  refine ⟨deflateChar H0 K θ, deflateChar_mem_Irr (hIrr θ hθ), fun x hx => ?_, ?_, ?_, ?_⟩
  · rw [deflateChar_apply, deflateChar_one]; exact hker θ hθ x hx
  · obtain ⟨x, hx, hne⟩ := hdet θ hθ
    exact ⟨x, hx, by rwa [deflateChar_apply, deflateChar_one]⟩
  · rw [deflateChar_one]; exact hdeg θ hθ
  · rw [← indClassFun_comp_mk hH0K θ]
    exact FrobeniusInduction.mem_Irr_comp_of_surjective
      (QuotientGroup.mk'_surjective H0) (hindIrr θ hθ)

end ScalarCoreCoherence.IsScalarCoreConfig

section HallCoreQuot

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type*} [Group G]

noncomputable def hallCoreQuotBotHom (M : Subgroup G) :
    ↥(hallCore ↥M) ⧸ (⊥ : Subgroup ↥M).subgroupOf (hallCore ↥M) →* G :=
  QuotientGroup.lift _ (M.subtype.comp (hallCore ↥M).subtype) (by
    intro x hx
    have : x = 1 := Subtype.ext (by simpa [Subgroup.mem_subgroupOf] using hx)
    simp [this])

theorem hallCoreQuotBotHom_mk (M : Subgroup G) (h : ↥(hallCore ↥M)) :
    hallCoreQuotBotHom M (QuotientGroup.mk h) = ((h : ↥M) : G) := (rfl)

theorem hallCoreQuotBotHom_injective (M : Subgroup G) :
    Function.Injective (hallCoreQuotBotHom M) := by
  intro x y hxy
  induction x using QuotientGroup.induction_on with
  | _ x =>
  induction y using QuotientGroup.induction_on with
  | _ y =>
  rw [hallCoreQuotBotHom_mk, hallCoreQuotBotHom_mk] at hxy
  exact congrArg _ (Subtype.ext (Subtype.ext hxy))

theorem range_hallCoreQuotBotHom (M : Subgroup G) :
    (hallCoreQuotBotHom M).range = CFSG.FeitThompson.Prep06.hallCoreIn M := by
  ext x
  rw [MonoidHom.mem_range, CFSG.FeitThompson.Prep06.hallCoreIn_eq]
  constructor
  · rintro ⟨y, rfl⟩
    induction y using QuotientGroup.induction_on with
    | _ y => exact ⟨y, y.2, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨QuotientGroup.mk ⟨y, hy⟩, rfl⟩

theorem hallCoreQuotBotHom_conjQuotientAut (M : Subgroup G) (u : ↥M)
    (v : ↥(hallCore ↥M) ⧸ (⊥ : Subgroup ↥M).subgroupOf (hallCore ↥M)) :
    hallCoreQuotBotHom M (conjQuotientAut (hallCore ↥M) ⊥ u v)
      = (u : G) * hallCoreQuotBotHom M v * (u : G)⁻¹ := by
  induction v using QuotientGroup.induction_on with
  | _ v =>
    rw [conjQuotientAut_apply_mk, hallCoreQuotBotHom_mk, hallCoreQuotBotHom_mk,
      MulAut.conjNormal_apply]
    simp

theorem map_hallCoreQuotBotHom_map_conjQuotientAut (M : Subgroup G) (u : ↥M)
    (Y : Subgroup (↥(hallCore ↥M) ⧸ (⊥ : Subgroup ↥M).subgroupOf (hallCore ↥M))) :
    (Y.map (conjQuotientAut (hallCore ↥M) ⊥ u).toMonoidHom).map (hallCoreQuotBotHom M)
      = (Y.map (hallCoreQuotBotHom M)).map (MulAut.conj (u : G)).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨_, ⟨v, hv, rfl⟩, by
      simp only [MulEquiv.coe_toMonoidHom, MonoidHom.coe_coe, MulAut.conj_apply]
      exact (hallCoreQuotBotHom_conjQuotientAut M u v).symm⟩
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨_, ⟨v, hv, rfl⟩, by
      simp only [MulEquiv.coe_toMonoidHom, MonoidHom.coe_coe, MulAut.conj_apply]
      exact hallCoreQuotBotHom_conjQuotientAut M u v⟩

theorem map_hallCoreQuotBotHom_comap {M X : Subgroup G}
    (hX : X ≤ CFSG.FeitThompson.Prep06.hallCoreIn M) :
    (X.comap (hallCoreQuotBotHom M)).map (hallCoreQuotBotHom M) = X :=
  Subgroup.map_comap_eq_self (by rw [range_hallCoreQuotBotHom]; exact hX)

theorem lineFixer_comap_hallCoreQuotBotHom {M U X : Subgroup G}
    (hX : X ≤ CFSG.FeitThompson.Prep06.hallCoreIn M) :
    lineFixer (hallCore ↥M) ⊥ (U.subgroupOf M) (X.comap (hallCoreQuotBotHom M))
      = (U ⊓ centralizer (X : Set G)).subgroupOf M := by
  ext u
  rw [mem_lineFixer, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_iff]
  refine and_congr_right fun _ => ⟨fun h x hx => ?_, fun h v hv => ?_⟩
  · obtain ⟨v, rfl⟩ : x ∈ (hallCoreQuotBotHom M).range := by
      rw [range_hallCoreQuotBotHom]; exact hX hx
    have h2 := congrArg (hallCoreQuotBotHom M) (h v (Subgroup.mem_comap.2 hx))
    rw [hallCoreQuotBotHom_conjQuotientAut] at h2
    calc hallCoreQuotBotHom M v * u = ((u : G) * hallCoreQuotBotHom M v * (u : G)⁻¹) * u := by
          rw [h2]
      _ = u * hallCoreQuotBotHom M v := by group
  · refine hallCoreQuotBotHom_injective M ?_
    rw [hallCoreQuotBotHom_conjQuotientAut, ← h _ (Subgroup.mem_comap.1 hv)]
    group

theorem iSupIndep_of_iSupIndep_map {A B : Type*} [Group A] [Group B] {f : A →* B}
    (hf : Function.Injective f) {ι : Type*} {T : ι → Subgroup A}
    (h : iSupIndep fun i => (T i).map f) : iSupIndep T := by
  rw [iSupIndep_def] at h ⊢
  intro i
  have hi := h i
  rw [disjoint_iff] at hi ⊢
  apply Subgroup.map_injective hf
  rw [Subgroup.map_inf_eq _ _ f hf, Subgroup.map_bot, Subgroup.map_iSup]
  simpa only [Subgroup.map_iSup] using hi

noncomputable def hallCoreLineFamily (M : Subgroup G) {n : ℕ} [NeZero n]
    (E : Fin n → Subgroup G) :
    ZMod n → Subgroup (↥(hallCore ↥M) ⧸ (⊥ : Subgroup ↥M).subgroupOf (hallCore ↥M)) :=
  fun i => (E ((ZMod.finEquiv n).symm i)).comap (hallCoreQuotBotHom M)

theorem hallCoreLineFamily_apply (M : Subgroup G) {n : ℕ} [NeZero n]
    (E : Fin n → Subgroup G) (i : ZMod n) :
    hallCoreLineFamily M E i = (E ((ZMod.finEquiv n).symm i)).comap (hallCoreQuotBotHom M) :=
  (rfl)

theorem map_hallCoreLineFamily {M : Subgroup G} {n : ℕ} [NeZero n] {E : Fin n → Subgroup G}
    (hEH : ∀ i, E i ≤ CFSG.FeitThompson.Prep06.hallCoreIn M) (i : ZMod n) :
    (hallCoreLineFamily M E i).map (hallCoreQuotBotHom M) = E ((ZMod.finEquiv n).symm i) :=
  map_hallCoreQuotBotHom_comap (hEH _)

theorem lineFixer_hallCoreLineFamily {M U : Subgroup G} {n : ℕ} [NeZero n]
    {E : Fin n → Subgroup G} (hEH : ∀ i, E i ≤ CFSG.FeitThompson.Prep06.hallCoreIn M) (i : ZMod n) :
    lineFixer (hallCore ↥M) ⊥ (U.subgroupOf M) (hallCoreLineFamily M E i)
      = (U ⊓ centralizer ((E ((ZMod.finEquiv n).symm i) : Subgroup G) : Set G)).subgroupOf M :=
  lineFixer_comap_hallCoreQuotBotHom (hEH _)

end HallCoreQuot

open PrimeDadeColumnGluing in
theorem exists_sign_col_of_isUniformBridgeData {G : Type*} [Group G] [Fintype G]
    {L : Subgroup G} [Fintype ↥L] {K W₁ W₂ : Subgroup ↥L} [K.Normal] [Fintype ↥(W₁ ⊔ W₂)]
    [Fintype ↑(Irr ↥W₁)] {h : IsPrimeCyclicTIHyp K W₁ W₂}
    {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L} {ζ : ↥L → ℂ} {d n : ℤ} {A₀ : Set G}
    {T : G → Subgroup G} {S₂ : Set (↥L → ℂ)} {τ₂ : charSpanZero S₂ →+ virtualChars G}
    {Wamb V₁ V₂ : Subgroup G} [Fintype ↥Wamb] {ωa : classFun ↥Wamb →ₗ[ℂ] classFun G}
    (hmapW : (W₁ ⊔ W₂).map L.subtype = Wamb) (hmap1 : W₁.map L.subtype = V₁)
    (hmap2 : W₂.map L.subtype = V₂)
    (hodd : Odd (Nat.card G)) (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hstab : {g : G | (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
      = cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)}
      = (((W₁ ⊔ W₂).map L.subtype : Subgroup G) : Set G))
    (hdisj : ∀ g ∉ (W₁ ⊔ W₂).map L.subtype,
      (fun x => g⁻¹ * x * g) ''
          cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
        ∩ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) = ∅)
    (hWpair : IsCyclicTIPair Wamb V₁ V₂) (hωa : IsCyclicTIIsometry Wamb V₁ V₂ ωa)
    (hS₂ : S₂ ⊆ indFam K (Irr ↥K \ {1})) (hS₂star : ∀ χ ∈ S₂, star χ ∈ S₂)
    {ν₂ : Submodule.span ℤ S₂ →+ virtualChars G} (hν₂ : IsCoherentWith S₂ τ₂ ν₂)
    (hτ₂ : ∀ (f : charSpanZero S₂) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      ((τ₂ f : virtualChars G) : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (hrows : ∀ j : Irr ↥W₂, j ≠ principalIrr ↥W₂ → h.primeTIrow σ j ∈ S₂)
    {ξ : ↥L → ℂ} (hξS : ξ ∈ S₂) (hξIrr : ξ ∈ Irr ↥L)
    {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    ∃ j' : Irr ↥V₂, ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧
      (ν₂ ⟨h.primeTIrow σ j, Submodule.subset_span (hrows j hj)⟩ : G → ℂ)
        = ε • hWpair.prodCharEtaColSum ωa j' := by
  subst hmapW hmap1 hmap2
  rcases coe_nu_primeTIrow_eq_or hodd hB hA hD hstab hdisj hωa hS₂ hS₂star hν₂ hτ₂ hrows
    hξS hξIrr hj
    (coe_nu_primeTIrow_sub hB hA hD hstab hdisj hωa hS₂ hν₂ hτ₂ hj (starIrr_ne_principalIrr hj)
      (hrows j hj) (hrows _ (starIrr_ne_principalIrr hj))) with h1 | h1
  · exact ⟨_, 1, Or.inl rfl, by rw [h1, one_smul]⟩
  · exact ⟨_, -1, Or.inr rfl, h1⟩

open Subgroup CFSG.FeitThompson.Prep06

universe u

theorem isScalarCoreConfig_hallCoreLineFamily
    (h₁ : CFSG.FeitThompson.Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u})
    (h₃ : CFSG.FeitThompson.Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₅ : CFSG.FeitThompson.Statements.FPF_type_iii_v_second_factor_prime.{u})
    {G : Type u} [Group G] [Finite G] (hG : IsMinimalOddSimple G)
    {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M) (htype : IsTypeIII M ∨ IsTypeIV M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂)
    {E : Fin (Nat.card W₁) → Subgroup G} {a : ℕ} {b : G}
    (hEH : ∀ i, E i ≤ Prep06.hallCoreIn M)
    (hcard : ∀ i, Nat.card (E i) = Nat.card W₂)
    (hsup : (⨆ i, E i) = Prep06.hallCoreIn M)
    (hindep : ∀ i, E i ⊓ (⨆ j ∈ ({i}ᶜ : Set (Fin (Nat.card W₁))), E j) = ⊥)
    (hUnorm : ∀ i, U ≤ normalizer ((E i : Subgroup G) : Set G))
    (hb : b ∈ W₁ ∧ zpowers b = W₁)
    (hconj : ∀ i : Fin (Nat.card W₁),
      Subgroup.map (MulAut.conj b⁻¹ : G ≃* G) (E i) = E (i + 1))
    (ha : 1 < a)
    (hidx : ∀ i, (U ⊓ centralizer ((E i : Subgroup G) : Set G)).relIndex U = a) :
    haveI : NeZero (Nat.card W₁) := ⟨Nat.card_pos.ne'⟩
    ScalarCoreCoherence.IsScalarCoreConfig (Nat.card W₂) (Nat.card W₁) (derivedOf M)
      (hallCore ↥M) (U.subgroupOf M) (W₁.subgroupOf M) ⊥ (hallCoreLineFamily M E)
      (((derivedOf M : Subgroup ↥M) : Set ↥M) \ {1}) := by
  classical
  have _ : Fintype G := Fintype.ofFinite G
  have hcfg0 := isPtypeCoreConfig_bot_of_typeIII_IV h₁ h₃ h₅ hG hM htype hc
  have hcfg := hcfg0.isPTypeConfig
  have hKeq : (⁅M, M⁆.subgroupOf M : Subgroup ↥M) = derivedOf M := by
    rw [derivedOf_eq, commutator_eq_subgroupOf_commutator]
  rw [hKeq] at hcfg
  have hf := hallCoreQuotBotHom_injective M
  have hqprime : (Nat.card W₁).Prime := hcfg0.prime_natCard_W₁
  have hpprime : (Nat.card W₂).Prime := h₅ G hG M U W₁ W₂ hM (by tauto) hc
  have hcardB : Nat.card (W₁.subgroupOf M) = Nat.card W₁ := natCard_subgroupOf_eq_of_le hc.le_M_W₁
  set b' : ↥M := ⟨b, hc.le_M_W₁ hb.1⟩ with hb'
  have hmapB : ∀ g : ↥M, (Subgroup.zpowers g).map M.subtype = Subgroup.zpowers (g : G) := fun g =>
    MonoidHom.map_zpowers _ _
  have hBgen : W₁.subgroupOf M = Subgroup.zpowers b'⁻¹ := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hc.le_M_W₁, Subgroup.zpowers_inv, hmapB, hb.2]
  have hb1 : b'⁻¹ ≠ 1 := by
    intro h1
    apply hc.ne_bot_W₁
    rw [← hb.2]
    have : b = 1 := by simpa [hb'] using congrArg Subtype.val h1
    rw [this, Subgroup.zpowers_one_eq_bot]
  have hbmem : b'⁻¹ ∈ W₁.subgroupOf M := by rw [hBgen]; exact Subgroup.mem_zpowers _
  have hmapLine : ∀ i, (hallCoreLineFamily M E i).map (hallCoreQuotBotHom M)
      = E ((ZMod.finEquiv _).symm i) := map_hallCoreLineFamily hEH
  have hHcard : Nat.card (↥(hallCore ↥M) ⧸ (⊥ : Subgroup ↥M).subgroupOf (hallCore ↥M))
      = Nat.card (Prep06.hallCoreIn M) := by
    rw [← range_hallCoreQuotBotHom, MonoidHom.range_eq_map,
      Subgroup.card_map_of_injective hf, Subgroup.card_top]
  have hmapConj : ∀ (g : ↥M) (i : ZMod (Nat.card W₁)),
      Subgroup.map (conjQuotientAut (hallCore ↥M) ⊥ g) (hallCoreLineFamily M E i)
        = hallCoreLineFamily M E i ↔
      (E ((ZMod.finEquiv _).symm i)).map (MulAut.conj (g : G)).toMonoidHom
        = E ((ZMod.finEquiv _).symm i) := by
    intro g i
    rw [← (Subgroup.map_injective hf).eq_iff,
      show ((conjQuotientAut (hallCore ↥M) ⊥ g : MulEquiv _ _) : _ →* _)
        = (conjQuotientAut (hallCore ↥M) ⊥ g : MulEquiv _ _).toMonoidHom from rfl,
      map_hallCoreQuotBotHom_map_conjQuotientAut, hmapLine]
  refine
    { solvable := hG.solvable M hc.lt_top.ne
      odd_card := hcfg0.odd_natCard_M
      q_prime := hqprime
      p_prime := hpprime
      p_odd := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card W₂)
      p_ne_q := natCard_W₂_ne_natCard_W₁_of_isTypeIII_or_isTypeIV h₅
        (isMinimalSimpleOdd_of_isMinimalOddSimple hG) hM htype hc
      isComplement_K_B := hcfg.isComplement'_J_B
      H_le_K := hcfg.le_J_H
      U_le_K := hcfg.le_J_U
      disjoint_H_U := hcfg.disjoint_H_U
      sup_H_U := hcfg.sup_eq_J
      card_B := hcardB
      exists_gen_B := ⟨b'⁻¹, hbmem, hBgen, ?_⟩
      B_le_normalizer_U := hcfg.le_normalizer_U
      coprime_H_U := Nat.Coprime.coprime_dvd_right
        (Subgroup.card_dvd_of_le (le_sup_left : U.subgroupOf M ≤ U.subgroupOf M ⊔ W₁.subgroupOf M))
        hcfg.coprime_natCard_H_sup
      coprime_q_K := ?_
      inf_centralizer_U_B := ?_
      H0_le_H := bot_le
      card_quotient := ?_
      indep_Eline := ?_
      iSup_Eline := ?_
      card_Eline := ?_
      map_U_Eline := ?_
      lineFixer_ne := ?_
      A_subset := subset_rfl
      A_invariant := hcfg0.A_invariant
      centralizer_subset_A := ?_ }
  · intro i
    apply Subgroup.map_injective hf
    rw [show ((conjQuotientAut (hallCore ↥M) ⊥ b'⁻¹ : MulEquiv _ _) : _ →* _)
        = (conjQuotientAut (hallCore ↥M) ⊥ b'⁻¹ : MulEquiv _ _).toMonoidHom from rfl,
      map_hallCoreQuotBotHom_map_conjQuotientAut, hmapLine, hmapLine]
    have h2 := hconj ((ZMod.finEquiv _).symm i)
    have h3 : (ZMod.finEquiv (Nat.card W₁)).symm (i + 1)
        = (ZMod.finEquiv (Nat.card W₁)).symm i + 1 := by simp
    rw [h3, ← h2]
    rfl
  · have hhall := hcfg.hall_B
    rw [hcardB] at hhall
    rwa [hcfg.isComplement'_J_B.index_eq_card] at hhall
  · rw [centralizer_coe_eq_centralizer_singleton hBgen.symm]
    exact hcfg.inf_centralizer_U_eq_bot _ hbmem hb1
  · rw [hHcard]
    exact (h₁ G hG M U W₁ W₂ hM htype hc).2.1
  · refine iSupIndep_of_iSupIndep_map hf ?_
    simp only [hmapLine]
    have hE : iSupIndep E := by
      rw [iSupIndep_def]
      intro i
      rw [disjoint_iff, ← hindep i]
      congr 1
    exact hE.comp (ZMod.finEquiv _).symm.injective
  · apply Subgroup.map_injective hf
    rw [Subgroup.map_iSup]
    simp only [hmapLine]
    rw [← MonoidHom.range_eq_map, range_hallCoreQuotBotHom, ← hsup]
    exact (ZMod.finEquiv (Nat.card W₁)).symm.toEquiv.iSup_comp (g := E)
  · intro i
    rw [← Subgroup.card_map_of_injective hf, hmapLine, hcard]
  · intro g hg i
    rw [hmapConj]
    exact (FreeCore.mem_normalizer_iff_map _ _).1 (hUnorm _ (Subgroup.mem_subgroupOf.1 hg))
  · intro i heq
    rw [lineFixer_hallCoreLineFamily hEH] at heq
    have h1 := Subgroup.relIndex_subgroupOf (H := U ⊓ centralizer
      ((E ((ZMod.finEquiv _).symm i) : Subgroup G) : Set G)) hc.le_M_E
    rw [heq, Subgroup.relIndex_self, hidx] at h1
    omega
  · intro h _ _ x hx
    exact ⟨hx.1.1, hx.2⟩

end CFSG.FeitThompson
