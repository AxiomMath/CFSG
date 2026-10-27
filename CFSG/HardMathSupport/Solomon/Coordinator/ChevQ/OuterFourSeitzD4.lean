module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourIn
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzHyperGoodIn
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Entry
public import CFSG.RankThree.PartTwo.Sec4.E27.D4TwoLines
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LieType.SeitzGeneration CFSG.Open CFSG.AGLEmbedding
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourInAux
open CFSG.HardMathSupport.Lang.D4Three (d4Graph)

section Generic

variable {S T : Type} [Group S] [Group T]

theorem le_range_conj_of_map_congr (e : S ≃* T) {E : Subgroup (MulAut S)}
    (h : E.map (MulAut.congr e).toMonoidHom ≤ (MulAut.conj : T →* MulAut T).range) :
    E ≤ (MulAut.conj : S →* MulAut S).range := by
  intro φ hφ
  obtain ⟨t, ht⟩ := h ⟨φ, hφ, rfl⟩
  refine ⟨e.symm t, MulEquiv.ext fun s => e.injective ?_⟩
  have h1 : t * e s * t⁻¹ = e (φ s) := by
    have := congrArg (fun ψ : MulAut T => ψ (e s)) ht
    simpa [MulAut.congr_apply] using this
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h1]

theorem map_congr_data (e : S ≃* T) {E : Subgroup (MulAut S)} (hE : IsElemAbelian 3 E)
    (hc : Nat.card E = 3 ^ 3) :
    IsElemAbelian 3 (E.map (MulAut.congr e).toMonoidHom) ∧
      Nat.card (E.map (MulAut.congr e).toMonoidHom) = 3 ^ 3 :=
  ⟨CFSG.SectionRank.isElemAbelian_map hE _, by
    rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, hc]⟩

theorem seitzHyperGamma_eq_top_of_congr (e : S ≃* T) {E : Subgroup (MulAut S)}
    (h : seitzHyperGamma 3 (E.map (MulAut.congr e).toMonoidHom) = ⊤) : seitzHyperGamma 3 E = ⊤ :=
  CFSG.RankThree.PartTwo.Sec4.Res6L364.seitzHyperGamma_eq_top_of_map e
    (MulAut.congr e).toMonoidHom (fun a x => by simp [MulAut.congr_apply])
    (MulAut.congr e).injective h

theorem exists_noncomm_of_not_prime [Finite S] [IsSimpleGroup S] (h : ¬ (Nat.card S).Prime) :
    ∃ a b : S, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  letI : CommGroup S := { (inferInstance : Group S) with mul_comm := hc }
  exact h IsSimpleGroup.prime_card

theorem exists_noncomm_of_four_dvd [Finite S] [IsSimpleGroup S] (h : 4 ∣ Nat.card S) :
    ∃ a b : S, a * b ≠ b * a := by
  refine exists_noncomm_of_not_prime fun hp => ?_
  rcases Nat.Prime.eq_one_or_self_of_dvd hp 4 h with h1 | h1
  · omega
  · rw [← h1] at hp
    exact absurd hp (by decide)

end Generic

section GraphInvolution

set_option linter.unusedSectionVars false


variable {τ : Tag} (K : Type) [Field K]

@[expose] noncomputable def labelMap (π : Equiv.Perm (Fin τ.rank))
    (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j) : ModGL τ K :=
  LinearMap.GeneralLinearGroup.ofLinearEquiv (Finsupp.domLCongr (labelPerm π hπ))

variable {π : Equiv.Perm (Fin τ.rank)} (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j)

theorem labelMap_hVec (i : Fin τ.rank) :
    (labelMap K π hπ : Module.End K (RootModule τ K)) (hVec τ K i) = hVec τ K (π i) := by
  simp [labelMap, hVec, labelPerm]

theorem labelMap_rootVec (α : Fin τ.rank → ℤ) (hα : IsRoot τ α) :
    (labelMap K π hπ : Module.End K (RootModule τ K)) (rootVec τ K α) =
      rootVec τ K (permLattice π α) := by
  simp [labelMap, rootVec, hα, hα.permLattice hπ, labelPerm]

theorem labelMap_apply_rootVec (β : Fin τ.rank → ℤ) :
    (labelMap K π hπ : Module.End K (RootModule τ K)) (rootVec τ K β) =
      rootVec τ K (permLattice π β) := by
  by_cases hβ : IsRoot τ β
  · exact labelMap_rootVec K hπ β hβ
  · have hβ' : ¬IsRoot τ (permLattice π β) := (isRoot_permLattice_iff hπ).not.2 hβ
    simp [rootVec, hβ, hβ']

theorem end_ext_basis' {f g : Module.End K (RootModule τ K)}
    (hh : ∀ j, f (hVec τ K j) = g (hVec τ K j))
    (hr : ∀ α, IsRoot τ α → f (rootVec τ K α) = g (rootVec τ K α)) : f = g := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rcases b with j | ⟨α, hα⟩
  · exact hh j
  · have e : rootVec τ K α = Finsupp.single (Sum.inr ⟨α, hα⟩) 1 := by simp [rootVec, hα]
    rw [← e]
    exact hr α hα

theorem labelMap_mul_xCoeff (i : Fin τ.rank) (k : ℕ) :
    (labelMap K π hπ : Module.End K (RootModule τ K)) * xCoeff τ K i k =
      xCoeff τ K (π i) k * (labelMap K π hπ : Module.End K (RootModule τ K)) := by
  refine end_ext_basis' K (fun j => ?_) (fun α hα => ?_)
  · simp only [Module.End.mul_apply, labelMap_hVec, xCoeff_hVec, hπ]
    split_ifs <;> simp [labelMap_hVec, labelMap_apply_rootVec, permLattice_single]
  · simp only [Module.End.mul_apply, labelMap_apply_rootVec]
    by_cases h₁ : α = Pi.single i 1
    · subst h₁
      rw [permLattice_single, xCoeff_rootVec_single, xCoeff_rootVec_single]
      split_ifs <;> simp [labelMap_apply_rootVec, permLattice_single]
    by_cases h₂ : α = -Pi.single i 1
    · subst h₂
      rw [permLattice_neg_single, xCoeff_rootVec_neg_single, xCoeff_rootVec_neg_single]
      split_ifs <;> simp [labelMap_apply_rootVec, labelMap_hVec, permLattice_single,
        permLattice_neg_single]
    have hα' := hα.permLattice hπ
    have h₁' : permLattice π α ≠ Pi.single (π i) 1 := by
      rw [← permLattice_single]
      exact (permLattice_injective _).ne h₁
    have h₂' : permLattice π α ≠ -Pi.single (π i) 1 := by
      rw [← permLattice_neg_single]
      exact (permLattice_injective _).ne h₂
    rw [xCoeff_rootVec_of_ne i k hα h₁ h₂, xCoeff_rootVec_of_ne (π i) k hα' h₁' h₂',
      map_smul, labelMap_apply_rootVec, permLattice_add_smul_single,
      stringDown_permLattice hπ]

theorem labelMap_mul_yCoeff (i : Fin τ.rank) (k : ℕ) :
    (labelMap K π hπ : Module.End K (RootModule τ K)) * yCoeff τ K i k =
      yCoeff τ K (π i) k * (labelMap K π hπ : Module.End K (RootModule τ K)) := by
  refine end_ext_basis' K (fun j => ?_) (fun α hα => ?_)
  · simp only [Module.End.mul_apply, labelMap_hVec, yCoeff_hVec, hπ]
    split_ifs <;> simp [labelMap_hVec, labelMap_apply_rootVec, permLattice_neg_single]
  · simp only [Module.End.mul_apply, labelMap_apply_rootVec]
    by_cases h₂ : α = -Pi.single i 1
    · subst h₂
      rw [permLattice_neg_single, yCoeff_rootVec_neg_single, yCoeff_rootVec_neg_single]
      split_ifs <;> simp [labelMap_apply_rootVec, permLattice_neg_single]
    by_cases h₁ : α = Pi.single i 1
    · subst h₁
      rw [permLattice_single, yCoeff_rootVec_single, yCoeff_rootVec_single]
      split_ifs <;> simp [labelMap_apply_rootVec, labelMap_hVec, permLattice_single,
        permLattice_neg_single]
    have hα' := hα.permLattice hπ
    have h₁' : permLattice π α ≠ Pi.single (π i) 1 := by
      rw [← permLattice_single]
      exact (permLattice_injective _).ne h₁
    have h₂' : permLattice π α ≠ -Pi.single (π i) 1 := by
      rw [← permLattice_neg_single]
      exact (permLattice_injective _).ne h₂
    rw [yCoeff_rootVec_of_ne i k hα h₁ h₂, yCoeff_rootVec_of_ne (π i) k hα' h₁' h₂',
      map_smul, labelMap_apply_rootVec, permLattice_sub_smul_single,
      stringUp_permLattice hπ]

theorem labelMap_mul_xOp (i : Fin τ.rank) (c : K) :
    (labelMap K π hπ : Module.End K (RootModule τ K)) * xOp τ K i c =
      xOp τ K (π i) c * (labelMap K π hπ : Module.End K (RootModule τ K)) := by
  rw [xOp_eq_sum_xCoeff, xOp_eq_sum_xCoeff, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, labelMap_mul_xCoeff]

theorem labelMap_mul_yOp (i : Fin τ.rank) (c : K) :
    (labelMap K π hπ : Module.End K (RootModule τ K)) * yOp τ K i c =
      yOp τ K (π i) c * (labelMap K π hπ : Module.End K (RootModule τ K)) := by
  rw [yOp_eq_sum_yCoeff, yOp_eq_sum_yCoeff, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, labelMap_mul_yCoeff]

theorem labelMap_conj_mem {g : ModGL τ K} (hg : g ∈ adjointGroup τ K) :
    labelMap K π hπ * g * (labelMap K π hπ)⁻¹ ∈ adjointGroup τ K := by
  have hle : (adjointGroup τ K).map (MulAut.conj (labelMap K π hπ)).toMonoidHom ≤
      adjointGroup τ K := by
    unfold adjointGroup
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨x, ⟨i, c, hx | hx⟩, rfl⟩
    · refine ⟨π i, c, Or.inl ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Units.val_mul, hx]
      rw [labelMap_mul_xOp, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
    · refine ⟨π i, c, Or.inr ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Units.val_mul, hx]
      rw [labelMap_mul_yOp, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  exact hle ⟨g, hg, rfl⟩

theorem entrywise_domLCongr (σ : K →+* K) (e : Label τ ≃ Label τ) :
    entrywise σ ((Finsupp.domLCongr e : RootModule τ K ≃ₗ[K] RootModule τ K) :
      Module.End K (RootModule τ K)) = (Finsupp.domLCongr e : RootModule τ K ≃ₗ[K] RootModule τ K) := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [entrywise_single]
  simp

theorem units_map_entrywiseHom_labelMap (σ : K →+* K) :
    Units.map (entrywiseHom σ) (labelMap K π hπ) = labelMap K π hπ :=
  Units.ext (entrywise_domLCongr K σ (labelPerm π hπ))

@[expose] def d4Swap : Equiv.Perm (Fin TwistTag.D4.tag.rank) :=
  Equiv.swap ⟨1, by decide⟩ ⟨3, by decide⟩

theorem d4Swap_submatrix :
    TwistTag.D4.tag.cartan.submatrix d4Swap d4Swap = TwistTag.D4.tag.cartan := by
  decide

theorem d4Swap_cartan (i j : Fin TwistTag.D4.tag.rank) :
    TwistTag.D4.tag.cartan (d4Swap i) (d4Swap j) = TwistTag.D4.tag.cartan i j :=
  congrFun (congrFun d4Swap_submatrix i) j

theorem d4Swap_perm : TwistTag.D4.perm * d4Swap * TwistTag.D4.perm = d4Swap ∧
    TwistTag.D4.perm⁻¹ * d4Swap⁻¹ * TwistTag.D4.perm⁻¹ = d4Swap⁻¹ ∧ d4Swap * d4Swap = 1 ∧
    d4Swap⁻¹ * d4Swap⁻¹ = 1 := by
  decide

@[expose] noncomputable def d4SwapMap : ModGL TwistTag.D4.tag K := labelMap K d4Swap d4Swap_cartan

theorem d4P_mul_swap_mul_d4P :
    diagramMap TwistTag.D4 K * d4SwapMap K * diagramMap TwistTag.D4 K = d4SwapMap K := by
  have hperm : ∀ j, TwistTag.D4.perm (d4Swap (TwistTag.D4.perm j)) = d4Swap j := fun j => by
    have := congrArg (fun π : Equiv.Perm (Fin TwistTag.D4.tag.rank) => π j) d4Swap_perm.1
    simpa [Equiv.Perm.mul_apply] using this
  have hperm' : ∀ j, TwistTag.D4.perm.symm (d4Swap.symm (TwistTag.D4.perm.symm j)) =
      d4Swap.symm j := fun j => by
    have := congrArg (fun π : Equiv.Perm (Fin TwistTag.D4.tag.rank) => π j) d4Swap_perm.2.1
    simpa [Equiv.Perm.mul_apply, Equiv.Perm.inv_def] using this
  refine Units.ext (end_ext_basis' K (fun j => ?_) (fun α hα => ?_))
  · simp only [Units.val_mul, Module.End.mul_apply]
    unfold d4SwapMap
    rw [diagramMap_hVec, labelMap_hVec, diagramMap_hVec, hperm, labelMap_hVec]
  · simp only [Units.val_mul, Module.End.mul_apply]
    unfold d4SwapMap
    rw [diagramMap_rootVec TwistTag.D4 K α hα, labelMap_apply_rootVec, diagramMap_apply_rootVec,
      labelMap_apply_rootVec]
    congr 1
    funext j
    simp only [permLattice, Function.comp_apply]
    exact congrArg α (hperm' j)

theorem d4SwapMap_mul_self : d4SwapMap K * d4SwapMap K = 1 := by
  have hperm : ∀ j, d4Swap (d4Swap j) = j := fun j => by
    have := congrArg (fun π : Equiv.Perm (Fin TwistTag.D4.tag.rank) => π j) d4Swap_perm.2.2.1
    simpa [Equiv.Perm.mul_apply] using this
  have hperm' : ∀ j, d4Swap.symm (d4Swap.symm j) = j := fun j => by
    have := congrArg (fun π : Equiv.Perm (Fin TwistTag.D4.tag.rank) => π j) d4Swap_perm.2.2.2
    simpa [Equiv.Perm.mul_apply, Equiv.Perm.inv_def] using this
  refine Units.ext (end_ext_basis' K (fun j => ?_) (fun α hα => ?_))
  · simp only [Units.val_mul, Module.End.mul_apply, Units.val_one, Module.End.one_apply]
    unfold d4SwapMap
    rw [labelMap_hVec, labelMap_hVec, hperm]
  · simp only [Units.val_mul, Module.End.mul_apply, Units.val_one, Module.End.one_apply]
    unfold d4SwapMap
    rw [labelMap_apply_rootVec, labelMap_apply_rootVec]
    congr 1
    funext j
    simp only [permLattice, Function.comp_apply]
    exact congrArg α (hperm' j)

theorem d4SwapMap_inv : (d4SwapMap K)⁻¹ = d4SwapMap K :=
  inv_eq_of_mul_eq_one_right (d4SwapMap_mul_self K)

@[expose] noncomputable def d4Q : ModGL Tag.D4 K := d4SwapMap K

theorem d4Q_mul_self : d4Q K * d4Q K = 1 := d4SwapMap_mul_self K

theorem d4Q_inv : (d4Q K)⁻¹ = d4Q K := d4SwapMap_inv K

variable {K}

theorem d4Twist_inv_conj_swap (σ : K ≃+* K) {u : ModGL TwistTag.D4.tag K}
    (hu : diagramMap TwistTag.D4 K * Units.map (entrywiseHom σ.toRingHom) u *
      (diagramMap TwistTag.D4 K)⁻¹ = u) :
    diagramMap TwistTag.D4 K * Units.map (entrywiseHom σ⁻¹.toRingHom)
        (d4SwapMap K * u * (d4SwapMap K)⁻¹) * (diagramMap TwistTag.D4 K)⁻¹ =
      d4SwapMap K * u * (d4SwapMap K)⁻¹ := by
  set P := diagramMap TwistTag.D4 K with hP
  set Q := d4SwapMap K with hQ
  have hPfix : ∀ τ : K ≃+* K, Units.map (entrywiseHom τ.toRingHom) P = P := fun τ =>
    units_map_entrywiseHom_labelMap K TwistTag.D4.cartan_perm τ.toRingHom
  have hQfix : ∀ τ : K ≃+* K, Units.map (entrywiseHom τ.toRingHom) Q = Q := fun τ =>
    units_map_entrywiseHom_labelMap K d4Swap_cartan τ.toRingHom
  have h1 : Units.map (entrywiseHom σ⁻¹.toRingHom) u = P * u * P⁻¹ := by
    have h2 : Units.map (entrywiseHom σ.toRingHom) u = P⁻¹ * u * P :=
      calc Units.map (entrywiseHom σ.toRingHom) u
          = P⁻¹ * (P * Units.map (entrywiseHom σ.toRingHom) u * P⁻¹) * P := by group
        _ = P⁻¹ * u * P := by rw [hu]
    have h3 := congrArg (Units.map (entrywiseHom σ⁻¹.toRingHom)) h2
    rw [← units_map_entrywiseHom_mul_ringEquiv, inv_mul_cancel,
      units_map_entrywiseHom_one_ringEquiv, map_mul, map_mul, map_inv, hPfix] at h3
    calc Units.map (entrywiseHom σ⁻¹.toRingHom) u
        = P * (P⁻¹ * Units.map (entrywiseHom σ⁻¹.toRingHom) u * P) * P⁻¹ := by group
      _ = P * u * P⁻¹ := by rw [← h3]
  have hPQP : P * Q * P = Q := d4P_mul_swap_mul_d4P K
  rw [map_mul, map_mul, map_inv, hQfix, h1]
  calc P * (Q * (P * u * P⁻¹) * Q⁻¹) * P⁻¹ = (P * Q * P) * u * (P * Q * P)⁻¹ := by group
    _ = Q * u * Q⁻¹ := by rw [hPQP]

end GraphInvolution

section Triality

set_option linter.unusedSectionVars false


open CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.RankThree.PartOne.CTP
open scoped commutatorElement

variable {K : Type} [Field K]

theorem swap_mem_fixed {σ : K ≃+* K} {u : adjointGroup Tag.D4 K}
    (hu : u ∈ fixedSubgroup (d4Twist 1 σ)) :
    ∃ hv : d4Q K * (u : ModGL Tag.D4 K) * (d4Q K)⁻¹ ∈ adjointGroup Tag.D4 K,
      (⟨_, hv⟩ : adjointGroup Tag.D4 K) ∈ fixedSubgroup (d4Twist 1 σ⁻¹) := by
  have hmem : d4Q K * (u : ModGL Tag.D4 K) * (d4Q K)⁻¹ ∈ adjointGroup Tag.D4 K :=
    labelMap_conj_mem K d4Swap_cartan u.2
  refine ⟨hmem, ?_⟩
  have hu' : ((d4Twist 1 σ u : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) = u :=
    congrArg Subtype.val hu
  have hfix : CFSG.HardMathSupport.Lang.D4Three.d4P K *
      Units.map (entrywiseHom σ.toRingHom) (u : ModGL Tag.D4 K) *
        (CFSG.HardMathSupport.Lang.D4Three.d4P K)⁻¹ = u :=
    (coe_twistedEntrywiseAut_one_D4 σ u).symm.trans hu'
  apply Subtype.ext
  have hc := coe_twistedEntrywiseAut_one_D4 σ⁻¹ ⟨_, hmem⟩
  refine hc.trans ?_
  exact d4Twist_inv_conj_swap σ hfix

@[expose] noncomputable def fixedTwistSwapEquiv (σ : K ≃+* K) :
    fixedSubgroup (d4Twist 1 σ) ≃* fixedSubgroup (d4Twist 1 σ⁻¹) where
  toFun u := ⟨⟨_, (swap_mem_fixed u.2).1⟩, (swap_mem_fixed u.2).2⟩
  invFun v := ⟨⟨_, (swap_mem_fixed (σ := σ⁻¹) v.2).1⟩, by
    have h := (swap_mem_fixed (σ := σ⁻¹) v.2).2
    rwa [inv_inv] at h⟩
  left_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    show d4Q K * (d4Q K * ((u : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) * (d4Q K)⁻¹) *
      (d4Q K)⁻¹ = _
    rw [d4Q_inv]
    calc d4Q K * (d4Q K * ((u : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) * d4Q K) * d4Q K
        = (d4Q K * d4Q K) * ((u : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) *
            (d4Q K * d4Q K) := by group
      _ = _ := by rw [d4Q_mul_self, one_mul, mul_one]
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    show d4Q K * (d4Q K * ((v : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) * (d4Q K)⁻¹) *
      (d4Q K)⁻¹ = _
    rw [d4Q_inv]
    calc d4Q K * (d4Q K * ((v : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) * d4Q K) * d4Q K
        = (d4Q K * d4Q K) * ((v : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) *
            (d4Q K * d4Q K) := by group
      _ = _ := by rw [d4Q_mul_self, one_mul, mul_one]
  map_mul' u v := by
    apply Subtype.ext
    apply Subtype.ext
    show d4Q K * (((u * v : fixedSubgroup (d4Twist 1 σ)) : adjointGroup Tag.D4 K) :
      ModGL Tag.D4 K) * (d4Q K)⁻¹ = (d4Q K * ((u : adjointGroup Tag.D4 K) :
        ModGL Tag.D4 K) * (d4Q K)⁻¹) * (d4Q K * ((v : adjointGroup Tag.D4 K) :
          ModGL Tag.D4 K) * (d4Q K)⁻¹)
    simp only [Subgroup.coe_mul]
    group

@[expose] def primePowerTwo : TauCeti.PrimePower := ⟨2, 1, Nat.prime_two, Nat.one_pos⟩

theorem valid_trialityD4_two : (TauCeti.LieTypeIndex.trialityD4 primePowerTwo).Valid := by
  simp [TauCeti.LieTypeIndex.valid_iff, primePowerTwo]

@[expose] def trialityTwoIndex : TauCeti.ValidLieTypeIndex :=
  ⟨.trialityD4 primePowerTwo, valid_trialityD4_two⟩

theorem commutator_self_eq_of_perfect {G : Type*} [Group G] {H : Subgroup G}
    (h : commutator ↥H = ⊤) : ⁅H, H⁆ = H := by
  have h1 := Subgroup.map_commutator (⊤ : Subgroup ↥H) ⊤ H.subtype
  rw [← commutator_def, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
  exact h1.symm

theorem nonempty_fixed_d4Twist_equiv_cat [Finite K] (hK : Nat.card K = 2 ^ 3) (T : K ≃+* K)
    (hT : ∀ c, T c = c ^ 2) :
    Nonempty (↥(fixedSubgroup (d4Twist 1 T)) ≃*
      (TauCeti.CFSGIndex.lie trialityTwoIndex).Group) := by
  have hK' : Nat.card K = (2 ^ 1) ^ 3 := by rw [hK]; norm_num
  let Ω := AlgebraicClosure K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcharK : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (k := 3) (by norm_num) hK
  have : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  obtain ⟨-, -, hHC, hsimp, hnc⟩ := triality_both_field_orientations_simple_full_ambient_fixed_group
    2 1 Nat.prime_two le_rfl K hK' Ω 1 (Or.inl rfl) T.toRingHom
    (fun c => by rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hT]; norm_num)
    (frobenius Ω 2) (fun c => by rw [frobenius_def]; norm_num)
  set H := twistedFixedGroup TwistTag.D4 K T.toRingHom with hH
  set C := graphFixedRootGroup TwistTag.D4 K T.toRingHom with hC
  obtain ⟨x, y, hxy⟩ := hnc
  have hperfC : commutator ↥C = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥C) with h | h
    · exfalso
      apply hxy
      have hm : ⁅x, y⁆ ∈ commutator ↥C := Subgroup.commutator_mem_commutator trivial trivial
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
      exact hm
    · exact h
  have hZ : Subgroup.center ↥C = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥C) with h | h
    · exact h
    · exfalso
      exact hxy (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top y) x)
  have hperf : ⁅H, H⁆ = C := by
    rw [hHC]
    exact commutator_self_eq_of_perfect hperfC
  obtain ⟨e2⟩ := nonempty_derivedCentralQuotient_equiv hperf hZ
  have hq2 : primePowerTwo.p = 2 := rfl
  obtain ⟨e3⟩ := CFSG.TauCetiBridge.Even.twistedBridgeEven_trialityD4 primePowerTwo
    valid_trialityD4_two hq2 K (by rw [hK, TauCeti.PrimePower.card_def]; norm_num [primePowerTwo,
      TwistTag.order]) T.toRingHom
    (fun c => by
      rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hT, TauCeti.PrimePower.card_def]
      norm_num [primePowerTwo])
  have e1 : ↥(fixedSubgroup (d4Twist 1 T)) ≃* H :=
    CFSG.HardMathSupport.Lang.E6Descent.fixedSubgroupTwistedEntrywiseAutOneEquiv TwistTag.D4 T
  exact ⟨e1.trans ((MulEquiv.subgroupCongr hHC).trans (e2.symm.trans e3))⟩

theorem nonempty_fixed_d4Twist_equiv_cat' [Finite K] (hK : Nat.card K = 2 ^ 3) (T : K ≃+* K)
    (hT : ∀ c, T c = c ^ 2) {σ : K ≃+* K} (hσ : σ = T ∨ σ = T⁻¹) :
    Nonempty (↥(fixedSubgroup (d4Twist 1 σ)) ≃*
      (TauCeti.CFSGIndex.lie trialityTwoIndex).Group) := by
  obtain ⟨e⟩ := nonempty_fixed_d4Twist_equiv_cat hK T hT
  rcases hσ with rfl | rfl
  · exact ⟨e⟩
  · refine ⟨(fixedTwistSwapEquiv T⁻¹).trans ?_⟩
    rw [inv_inv]
    exact e

end Triality

section GraphFieldCube

set_option linter.unusedSectionVars false


open CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.PartTwo.Sec4.E27 (mem_seitzHyperGamma_of_fixed conj_not_mem_zpowers
  comm_of_isElemAbelian)
open CFSG.HardMathSupport.Lang.E6Descent (exists_frobenius_of_cube outer_cube_normal_form_cases
  cube_normal_form_sigma_cube mem_inner_of_normal_form_one)
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

theorem eq_top_of_fixed_escape {P : Type*} [Group P] [Finite P] {N : Subgroup (MulAut P)}
    [N.Normal] {R : Subgroup P} (hmax : ∀ M : Subgroup P, R ≤ M → M = R ∨ M = ⊤)
    (hker : ∀ ι ∈ N, (∀ x ∈ R, ι x = x) → ι = 1) {α ι ψa ψb : MulAut P} (hι1 : ι ≠ 1)
    (hιN : ι ∈ N) (hFa : fixedSubgroup (ψa * α * ψa⁻¹) = R)
    (hFb : fixedSubgroup (ψb * (α * ι) * ψb⁻¹) = R) {H : Subgroup P}
    (hHa : fixedSubgroup α ≤ H) (hHb : fixedSubgroup (α * ι) ≤ H) : H = ⊤ := by
  rw [fixedSubgroup_conj] at hFa hFb
  have hmaxα : ∀ M : Subgroup P, fixedSubgroup α ≤ M → M = fixedSubgroup α ∨ M = ⊤ := by
    intro M hM
    have hle : R ≤ M.map ψa.toMonoidHom := by
      rw [← hFa]
      exact Subgroup.map_mono hM
    have hMeq : M = (M.map ψa.toMonoidHom).comap ψa.toMonoidHom :=
      (Subgroup.comap_map_eq_self_of_injective ψa.injective M).symm
    rcases hmax _ hle with h | h
    · left
      rw [hMeq, h, ← hFa]
      exact Subgroup.comap_map_eq_self_of_injective ψa.injective _
    · right
      rw [hMeq, h]
      exact Subgroup.comap_top _
  rcases hmaxα H hHa with h | h
  · exfalso
    have hle : fixedSubgroup (α * ι) ≤ fixedSubgroup α := h ▸ hHb
    have hcard : Nat.card (fixedSubgroup (α * ι)) = Nat.card (fixedSubgroup α) := by
      have h1 := congrArg (fun H : Subgroup P => Nat.card H) hFb
      have h2 := congrArg (fun H : Subgroup P => Nat.card H) hFa
      rw [Subgroup.card_map_of_injective ψb.injective] at h1
      rw [Subgroup.card_map_of_injective ψa.injective] at h2
      rw [h1, h2]
    have heq : fixedSubgroup (α * ι) = fixedSubgroup α :=
      Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
    have hιfix : ∀ x ∈ fixedSubgroup α, ι x = x := by
      intro x hx
      have hx' : x ∈ fixedSubgroup (α * ι) := heq ▸ hx
      have h1 : (α * ι) x = x := hx'
      have h2 : α x = x := hx
      simp only [MulAut.mul_apply] at h1
      exact α.injective (h1.trans h2.symm)
    have hι'fix : ∀ x ∈ R, (ψa * ι * ψa⁻¹) x = x := by
      intro x hx
      rw [← hFa] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      show (ψa * ι * ψa⁻¹) (ψa y) = ψa y
      simp [MulAut.mul_apply, hιfix y hy]
    have h1 := hker _ (‹N.Normal›.conj_mem ι hιN ψa) hι'fix
    apply hι1
    have h2 : ψa⁻¹ * (ψa * ι * ψa⁻¹) * ψa = ι := by group
    rw [← h2, h1]
    simp
  · exact h

variable {K : Type} [Field K]

abbrev AdjD4 (K : Type) [Field K] : Type := ↥(adjointGroup Tag.D4 K)

instance finite_mulAut_adjointD4 [Finite K] : Finite (MulAut (AdjD4 K)) := by
  have : Finite (ModGL Tag.D4 K) := finite_modGL
  exact Finite.of_injective (fun e : MulAut (AdjD4 K) => (e : AdjD4 K → AdjD4 K))
    DFunLike.coe_injective

theorem conj_injective_adjointD4 [Finite K] : Function.Injective (MulAut.conj : AdjD4 K →* MulAut (AdjD4 K)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgc : g ∈ Subgroup.center (AdjD4 K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have := congrArg (fun φ : MulAut (AdjD4 K) => φ y) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc y * g = g * y * g⁻¹ * g := by rw [this]
      _ = g * y := by group
  rw [center_adjointGroup_eq_bot] at hgc
  exact Subgroup.mem_bot.1 hgc

theorem exists_frobenius_eight [Finite K] (hK : Nat.card K = 2 ^ 3) {σ : K ≃+* K}
    (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) :
    ∃ T : K ≃+* K, (∀ c, T c = c ^ 2) ∧ T ^ 3 = 1 ∧ T ≠ 1 ∧ (σ = T ∨ σ = T⁻¹) := by
  obtain ⟨d, T, hd0, hd3, hT, hT3, hσT⟩ :=
    exists_frobenius_of_cube Nat.prime_two (by norm_num) K hK σ hσ3 hσ1
  have hd : d = 1 := by omega
  subst hd
  have hT1 : T ≠ 1 := by
    rintro rfl
    rcases hσT with h | h
    · exact hσ1 h
    · exact hσ1 (by rw [h, one_pow])
  refine ⟨T, fun c => by rw [hT]; norm_num, hT3, hT1, ?_⟩
  rcases hσT with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans (inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hT3)).symm)

theorem graphField_conj_fixed [Finite K] (hK : Nat.card K = 2 ^ 3) {T : K ≃+* K}
    (hT : ∀ c, T c = c ^ 2) (hT3 : T ^ 3 = 1) (hT1 : T ≠ 1) {σ : K ≃+* K} (hσ : σ = T ∨ σ = T⁻¹)
    {ε : ℕ} (hε : ε = 1 ∨ ε = 2) {γ : MulAut (AdjD4 K)} (hγ3 : γ ^ 3 = 1) {g : AdjD4 K}
    {a : Fin Tag.D4.rank → Kˣ} (hγ : γ = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) :
    ∃ ψ : MulAut (AdjD4 K), fixedSubgroup (ψ * γ * ψ⁻¹) = fixedSubgroup (d4Twist 1 (d4GfTwist T σ ε)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (k := 3) (by norm_num) hK
  exact exists_conj_fixedSubgroup_D4_graphField (ℓ := 2) (f := 3) (e := 1) hK (by rw [hK]; norm_num)
    le_rfl rfl T σ (fun c => by rw [hT]; norm_num) hT3 hT1 hσ hε g a γ hγ3 hγ

theorem orderOf_d4GfTwist {T : K ≃+* K} (hT3 : T ^ 3 = 1) (hT1 : T ≠ 1) (σ : K ≃+* K) (ε : ℕ) :
    orderOf (d4GfTwist T σ ε) = 3 := by
  have hT' : orderOf T = 3 := orderOf_eq_prime hT3 hT1
  rcases d4GfTwist_eq_or T σ ε with h | h
  · rw [h]; exact hT'
  · rw [h, orderOf_inv]; exact hT'

theorem eq_one_of_commute_fixed_conj {γ ψ : MulAut (AdjD4 K)} {τ : K ≃+* K} [Finite K]
    (hF : fixedSubgroup (ψ * γ * ψ⁻¹) = fixedSubgroup (d4Twist 1 τ)) {z : AdjD4 K}
    (hz : ∀ u ∈ fixedSubgroup γ, z * u = u * z) : z = 1 := by
  rw [fixedSubgroup_conj] at hF
  have h1 : ψ z = 1 := by
    refine eq_one_of_commute_fixed_twisted_D4 τ fun u hu => ?_
    rw [← hF] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    show ψ z * ψ v = ψ v * ψ z
    rw [← map_mul, ← map_mul, hz v hv]
  rw [← map_one ψ] at h1
  exact ψ.injective h1

theorem not_inner_of_conj_fixed {γ ψ : MulAut (AdjD4 K)} {τ : K ≃+* K} [Finite K]
    (hF : fixedSubgroup (ψ * γ * ψ⁻¹) = fixedSubgroup (d4Twist 1 τ)) :
    ∀ h : AdjD4 K, γ ≠ MulAut.conj h := by
  intro h hγ
  have hh1 : h = 1 := eq_one_of_commute_fixed_conj hF fun u hu => by
    have hu' : γ u = u := hu
    rw [hγ, MulAut.conj_apply] at hu'
    calc h * u = (h * u * h⁻¹) * h := by group
      _ = u * h := by rw [hu']
  rw [hγ, hh1, map_one, mul_one, mul_inv_cancel] at hF
  have htop : fixedSubgroup (1 : MulAut (AdjD4 K)) = ⊤ := (Subgroup.eq_top_iff' _).2 fun x => rfl
  exact fixedSubgroup_d4Twist_ne_top τ (hF.symm.trans htop)

theorem fixed_graphField_le (hS2 : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo) [Finite K]
    (hK : Nat.card K = 2 ^ 3) {E : Subgroup (MulAut (AdjD4 K))} (hE : IsElemAbelian 3 E)
    (hc : Nat.card E = 3 ^ 3) {γ : MulAut (AdjD4 K)} (hγE : γ ∈ E) {ψ : MulAut (AdjD4 K)}
    {T τ : K ≃+* K} (hT : ∀ c, T c = c ^ 2) (hτ : τ = T ∨ τ = T⁻¹)
    (hF : fixedSubgroup (ψ * γ * ψ⁻¹) = fixedSubgroup (d4Twist 1 τ))
    {k₁ k₂ : AdjD4 K} (h₁ : MulAut.conj k₁ ∈ E) (h₂ : MulAut.conj k₂ ∈ E) (hk₁ : k₁ ≠ 1)
    (hk₂ : MulAut.conj k₂ ∉ Subgroup.zpowers (MulAut.conj k₁)) :
    fixedSubgroup γ ≤ seitzHyperGamma 3 E := by
  classical
  have : Finite (ModGL Tag.D4 K) := finite_modGL
  have : Finite (AdjD4 K) := Subtype.finite
  have hγ3 : γ ^ 3 = 1 := hE.2 γ hγE
  have hγout := not_inner_of_conj_fixed hF
  have hγ1 : γ ≠ 1 := fun h => hγout 1 (by rw [h, map_one])
  obtain ⟨e₀⟩ := nonempty_fixed_d4Twist_equiv_cat' hK T hT hτ
  have hF' := hF
  rw [fixedSubgroup_conj] at hF'
  set R := fixedSubgroup γ with hR
  let ι : ↥R ≃* (TauCeti.CFSGIndex.lie trialityTwoIndex).Group :=
    (Subgroup.equivMapOfInjective R ψ.toMonoidHom ψ.injective).trans
      ((MulEquiv.subgroupCongr hF').trans e₀)
  have hfixk : ∀ k : AdjD4 K, MulAut.conj k ∈ E → γ k = k := by
    intro k hk
    have hcomm := comm_of_isElemAbelian hE hγE hk
    have h1 : MulAut.conj (γ k) * γ = MulAut.conj k * γ := by
      rw [← mulAut_mul_conj]
      exact hcomm
    exact conj_injective_adjointD4 (mul_right_cancel h1)
  let k₁' : ↥R := ⟨k₁, hfixk k₁ h₁⟩
  let k₂' : ↥R := ⟨k₂, hfixk k₂ h₂⟩
  let j : ↥R →* MulAut (AdjD4 K) := (MulAut.conj : AdjD4 K →* MulAut (AdjD4 K)).comp R.subtype
  have hj : Function.Injective j := conj_injective_adjointD4.comp Subtype.val_injective
  set Pk : Subgroup ↥R := Subgroup.closure ({k₁', k₂'} : Set ↥R) with hPk
  have hPj : Pk.map j = Subgroup.closure ({MulAut.conj k₁, MulAut.conj k₂} :
      Set (MulAut (AdjD4 K))) := by
    rw [hPk, MonoidHom.map_closure, Set.image_pair]
    rfl
  have hPE : Pk.map j ≤ E := by
    rw [hPj, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact h₁
    · rw [Set.mem_singleton_iff.1 hx]
      exact h₂
  have hPel : IsElemAbelian 3 Pk := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply hj
      have := comm_of_isElemAbelian hE (hPE ⟨a, a.2, rfl⟩) (hPE ⟨b, b.2, rfl⟩)
      simpa only [Subgroup.coe_mul, map_mul] using this
    · apply hj
      rw [map_pow, map_one]
      exact hE.2 _ (hPE ⟨x, hx, rfl⟩)
  have hPcard : Nat.card Pk = 3 ^ 2 := by
    rw [← Subgroup.card_map_of_injective hj, hPj]
    exact CFSG.LieType.SeitzGeneration.card_closure_pair_of_not_mem Nat.prime_three hE h₁ h₂
      (fun h => hk₁ (conj_injective_adjointD4 (by rw [h, map_one]))) hk₂
  let jc : ↥R →* MulAut (TauCeti.CFSGIndex.lie trialityTwoIndex).Group :=
    (MulAut.conj : (TauCeti.CFSGIndex.lie trialityTwoIndex).Group →* _).comp ι.toMonoidHom
  have hjc : Function.Injective jc := by
    rw [injective_iff_map_eq_one]
    intro p hp
    have hcen : ∀ r : ↥R, p * r = r * p := by
      intro r
      have h1 := congrArg (fun φ : MulAut (TauCeti.CFSGIndex.lie trialityTwoIndex).Group =>
        φ (ι r)) hp
      simp only [jc, MonoidHom.comp_apply, MulAut.conj_apply, MulAut.one_apply,
        MulEquiv.coe_toMonoidHom] at h1
      apply ι.injective
      rw [map_mul, map_mul]
      calc ι p * ι r = ι p * ι r * (ι p)⁻¹ * ι p := by group
        _ = ι r * ι p := by rw [h1]
    have h1 : (p : AdjD4 K) = 1 := eq_one_of_commute_fixed_conj hF fun u hu =>
      congrArg Subtype.val (hcen ⟨u, hu⟩)
    exact Subtype.ext h1
  set E' := Pk.map jc with hE'
  have hE'el : IsElemAbelian 3 E' := CFSG.SectionRank.isElemAbelian_map hPel jc
  have hE'c : Nat.card E' = 3 ^ 2 := by rw [hE', Subgroup.card_map_of_injective hjc, hPcard]
  have hpd : (3 : ℕ) ≠ trialityTwoIndex.1.characteristic := by
    simp [trialityTwoIndex, primePowerTwo]
  have hexc : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3 trialityTwoIndex.1 := by
    simp [CFSG.AGLEmbeddingD2.IsD2SeitzException, trialityTwoIndex]
  have hgen := hS2 trialityTwoIndex 3 Nat.prime_three (by norm_num) hpd hexc E' hE'el hE'c
  intro r hr
  set S := {c : (TauCeti.CFSGIndex.lie trialityTwoIndex).Group | ∃ e ∈ E', e ≠ 1 ∧ e c = c}
    with hS
  have hle : Subgroup.closure (ι.symm.toMonoidHom '' S) ≤
      (seitzHyperGamma 3 E).comap R.subtype := by
    rw [Subgroup.closure_le]
    rintro _ ⟨c, ⟨e, ⟨p, hp, rfl⟩, he1, hec⟩, rfl⟩
    have hp1 : p ≠ 1 := fun h => he1 (by rw [h, map_one])
    have hjpE : j p ∈ E := hPE ⟨p, hp, rfl⟩
    have hp1' : (p : AdjD4 K) ≠ 1 := fun h => hp1 (Subtype.ext h)
    have hnot : j p ∉ Subgroup.zpowers γ :=
      conj_not_mem_zpowers conj_injective_adjointD4 hγ3 hγout hp1'
    show ((ι.symm c : ↥R) : AdjD4 K) ∈ seitzHyperGamma 3 E
    refine mem_seitzHyperGamma_of_fixed hE (by rw [hc]; norm_num) hγE hjpE hγ1 hnot
      (ι.symm c).2 ?_
    have h1 : ι p * c * (ι p)⁻¹ = c := hec
    have h2 : p * ι.symm c * p⁻¹ = ι.symm c := by
      apply ι.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact h1
    show (p : AdjD4 K) * ((ι.symm c : ↥R) : AdjD4 K) * (p : AdjD4 K)⁻¹ = ι.symm c
    exact congrArg Subtype.val h2
  have htop : Subgroup.closure (ι.symm.toMonoidHom '' S) = ⊤ := by
    rw [← MonoidHom.map_closure, hgen]
    exact Subgroup.map_top_of_surjective _ ι.symm.surjective
  have hmem : (⟨r, hr⟩ : ↥R) ∈ (seitzHyperGamma 3 E).comap R.subtype :=
    hle (htop ▸ Subgroup.mem_top _)
  exact hmem

theorem seitzHyperGamma_eq_top_of_graphField (hS2 : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo)
    [Finite K] (hK : Nat.card K = 2 ^ 3) {E : Subgroup (MulAut (AdjD4 K))}
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 3)
    (hnoF : ∀ α ∈ E, ¬ D4ElemType α fun ε σ => ε = 0 ∧ σ ≠ 1)
    (hGF : ∃ β ∈ E, D4ElemType β fun ε σ => ε ≠ 0 ∧ σ ≠ 1) : seitzHyperGamma 3 E = ⊤ := by
  classical
  have : Finite (ModGL Tag.D4 K) := finite_modGL
  have : Finite (AdjD4 K) := Subtype.finite
  haveI := inner_normal (AdjD4 K)
  obtain ⟨β, hβE, g, a, σ, ε, hεlt, hσ3, ⟨hε0, hσ1⟩, hβ⟩ := hGF
  have hε : ε = 1 ∨ ε = 2 := by omega
  have hβ3 : β ^ 3 = 1 := hE.2 β hβE
  obtain ⟨T, hT, hT3, hT1, hσT⟩ := exists_frobenius_eight hK hσ3 hσ1
  obtain ⟨ψ, hF⟩ := graphField_conj_fixed hK hT hT3 hT1 hσT hε hβ3 hβ
  have hβout := not_inner_of_conj_fixed hF
  have hβNF : HasNF β ε σ := ⟨g, a, hβ⟩
  have key : ∀ x ∈ E, x ∉ Subgroup.zpowers β → ∃ k : AdjD4 K, k ≠ 1 ∧ MulAut.conj k ∈ E ∧
      MulAut.conj k ∈ Subgroup.closure ({β, x} : Set (MulAut (AdjD4 K))) ∧
      x ∈ Subgroup.closure ({β, MulAut.conj k} : Set (MulAut (AdjD4 K))) := by
    intro x hxE hxβ
    have hx3 : x ^ 3 = 1 := hE.2 x hxE
    have hβc : β ∈ Subgroup.closure ({β, x} : Set (MulAut (AdjD4 K))) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have hxc : x ∈ Subgroup.closure ({β, x} : Set (MulAut (AdjD4 K))) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    by_cases hxin : x ∈ inner (AdjD4 K)
    · obtain ⟨k, rfl⟩ := hxin
      refine ⟨k, fun h => hxβ (by rw [h, map_one]; exact Subgroup.one_mem _), hxE, hxc,
        Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩
    obtain ⟨g', a', σ', ε', hε'lt, hxeq, hσ'3, hcase⟩ := outer_cube_normal_form_cases x hx3 hxin
    have hε'0 : ε' ≠ 0 := by
      rcases hcase with ⟨h, hσ'1⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact absurd ⟨g', a', σ', ε', hε'lt, hσ'3, ⟨h, hσ'1⟩, hxeq⟩ (hnoF x hxE)
      · exact h
      · exact h
    have hxNF : HasNF x ε' σ' := ⟨g', a', hxeq⟩
    obtain ⟨y, hyE, ⟨σ'', hyNF⟩, hyform⟩ : ∃ y ∈ E, (∃ σ'' : K ≃+* K, HasNF y 0 σ'') ∧
        (y = β * x ∨ y = β * (x * x)) := by
      by_cases hεε : ε = ε'
      · refine ⟨β * (x * x), mul_mem hβE (mul_mem hxE hxE), ⟨σ * (σ' * σ'), ?_⟩, Or.inr rfl⟩
        have h' := (hβNF.mul (hxNF.mul hxNF)).mod_three
        rwa [show (ε + (ε' + ε')) % 3 = 0 by omega] at h'
      · refine ⟨β * x, mul_mem hβE hxE, ⟨σ * σ', ?_⟩, Or.inl rfl⟩
        have h' := (hβNF.mul hxNF).mod_three
        rwa [show (ε + ε') % 3 = 0 by omega] at h'
    obtain ⟨g'', a'', hy⟩ := hyNF
    have hy3 : y ^ 3 = 1 := hE.2 y hyE
    have hσ''3 : σ'' ^ 3 = 1 := cube_normal_form_sigma_cube (hy ▸ hy3)
    have hσ''1 : σ'' = 1 := by
      by_contra h
      exact hnoF y hyE ⟨g'', a'', σ'', 0, by norm_num, hσ''3, ⟨rfl, h⟩, hy⟩
    subst hσ''1
    obtain ⟨k, hk⟩ := (show y ∈ inner (AdjD4 K) from
      hy ▸ mem_inner_of_normal_form_one g'' a'' (hy ▸ hy3))
    have hx4 : x = (x * x) * (x * x) := by
      calc x = x ^ 3 * x := by rw [hx3, one_mul]
        _ = (x * x) * (x * x) := by rw [pow_three]; simp only [mul_assoc]
    refine ⟨k, ?_, hk ▸ hyE, ?_, ?_⟩
    · intro hk1
      rw [hk1, map_one] at hk
      apply hxβ
      rcases hyform with h | h
      · rw [← hk] at h
        rw [eq_inv_of_mul_eq_one_right h.symm]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers β)
      · rw [← hk] at h
        rw [hx4, eq_inv_of_mul_eq_one_right h.symm]
        exact mul_mem (Subgroup.inv_mem _ (Subgroup.mem_zpowers β))
          (Subgroup.inv_mem _ (Subgroup.mem_zpowers β))
    · rw [hk]
      rcases hyform with h | h
      · rw [h]; exact mul_mem hβc hxc
      · rw [h]; exact mul_mem hβc (mul_mem hxc hxc)
    · have hβc' : β ∈ Subgroup.closure ({β, MulAut.conj k} : Set (MulAut (AdjD4 K))) :=
        Subgroup.subset_closure (Set.mem_insert _ _)
      have hyc : y ∈ Subgroup.closure ({β, MulAut.conj k} : Set (MulAut (AdjD4 K))) := by
        rw [← hk]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      rcases hyform with h | h
      · have : x = β⁻¹ * y := by rw [h]; group
        rw [this]
        exact mul_mem (inv_mem hβc') hyc
      · have h2 : x * x = β⁻¹ * y := by rw [h]; group
        rw [hx4, h2]
        exact mul_mem (mul_mem (inv_mem hβc') hyc) (mul_mem (inv_mem hβc') hyc)
  have hcardβ : Nat.card (Subgroup.zpowers β) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hβ3)
  obtain ⟨x₁, hx₁E, hx₁β⟩ : ∃ x ∈ E, x ∉ Subgroup.zpowers β := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le (fun x hx => h x hx : E ≤ Subgroup.zpowers β)
    rw [hc] at h1
    omega
  obtain ⟨k₁, hk₁1, hk₁E, -, -⟩ := key x₁ hx₁E hx₁β
  have hk₁β : MulAut.conj k₁ ∉ Subgroup.zpowers β :=
    conj_not_mem_zpowers conj_injective_adjointD4 hβ3 hβout hk₁1
  have hcl9 : Nat.card (Subgroup.closure ({β, MulAut.conj k₁} : Set (MulAut (AdjD4 K)))) = 3 ^ 2 :=
    CFSG.LieType.SeitzGeneration.card_closure_pair_of_not_mem Nat.prime_three hE hβE hk₁E
      (fun h => hβout 1 (by rw [h, map_one])) hk₁β
  obtain ⟨x₂, hx₂E, hx₂cl⟩ : ∃ x ∈ E, x ∉ Subgroup.closure ({β, MulAut.conj k₁} :
      Set (MulAut (AdjD4 K))) := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le (fun x hx => h x hx :
      E ≤ Subgroup.closure ({β, MulAut.conj k₁} : Set (MulAut (AdjD4 K))))
    rw [hc, hcl9] at h1
    omega
  have hx₂β : x₂ ∉ Subgroup.zpowers β := fun h => hx₂cl ((Subgroup.zpowers_le.2
    (Subgroup.subset_closure (Set.mem_insert _ _))) h)
  obtain ⟨k₂, hk₂1, hk₂E, -, hx₂cl'⟩ := key x₂ hx₂E hx₂β
  have hk₂k₁ : MulAut.conj k₂ ∉ Subgroup.zpowers (MulAut.conj k₁) := by
    intro h
    apply hx₂cl
    refine (Subgroup.closure_le _).2 ?_ hx₂cl'
    intro z hz
    rcases hz with rfl | hz
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · rw [Set.mem_singleton_iff.1 hz]
      exact (Subgroup.zpowers_le.2 (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))) h
  have hβ'E : β * MulAut.conj k₁ ∈ E := mul_mem hβE hk₁E
  have hβ'NF : HasNF (β * MulAut.conj k₁) ε σ := by
    have h := hβNF.mul (hasNF_conj k₁)
    simpa only [add_zero, mul_one] using h
  obtain ⟨g₂, a₂, hβ'⟩ := hβ'NF
  obtain ⟨ψ', hF'⟩ := graphField_conj_fixed hK hT hT3 hT1 hσT hε (hE.2 _ hβ'E) hβ'
  have hτ := d4GfTwist_eq_or T σ ε
  have hHa := fixed_graphField_le hS2 hK hE hc hβE hT hτ hF hk₁E hk₂E hk₁1 hk₂k₁
  have hHb := fixed_graphField_le hS2 hK hE hc hβ'E hT hτ hF' hk₁E hk₂E hk₁1 hk₂k₁
  have hchar : ringChar K = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        (k := 3) (by norm_num) hK
    exact ringChar.eq K 2
  refine eq_top_of_fixed_escape (N := inner (AdjD4 K))
    (D4TwistedSubfieldMaximal_of_entry D4TwF2Entry.D4TwF2EntryProp_holds K (by rw [hchar]; norm_num)
      _ (orderOf_d4GfTwist hT3 hT1 σ ε)) ?_ (fun h => hk₁1 (conj_injective_adjointD4
        (by rw [h, map_one]))) ⟨k₁, rfl⟩ hF hF' hHa hHb
  intro ι' hι' hfix
  obtain ⟨z, rfl⟩ := hι'
  have hz : z = 1 := by
    refine eq_one_of_commute_fixed_twisted_D4 (d4GfTwist T σ ε) fun u hu => ?_
    have h1 := hfix u hu
    rw [MulAut.conj_apply] at h1
    calc z * u = (z * u * z⁻¹) * z := by group
      _ = u * z := by rw [h1]
  rw [hz, map_one]

end GraphFieldCube

section Reduction

set_option linter.unusedSectionVars false


open CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.HardMathSupport.Lang.E6Descent (exists_frobenius_of_cube outer_cube_normal_form_cases
  exists_conj_eq_entrywiseAdjointAut_D4 sq_conj_mul_exactNormalAut d4Graph_zero)

@[expose] def D4EightOuterCubes : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ 3 →
    ∀ E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K)), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      ¬ E ≤ (MulAut.conj : ↥(adjointGroup Tag.D4 K) →* MulAut ↥(adjointGroup Tag.D4 K)).range →
      (∀ α ∈ E, ¬ CFSG.LieType.SeitzGeneration.ExcWideThree.D4ElemType α fun ε σ =>
        ε = 0 ∧ σ ≠ 1) →
      seitzHyperGamma 3 E = ⊤

@[expose] def D4EightGraphCubes : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ 3 →
    ∀ E : Subgroup (MulAut ↥(adjointGroup Tag.D4 K)), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      ¬ E ≤ (MulAut.conj : ↥(adjointGroup Tag.D4 K) →* MulAut ↥(adjointGroup Tag.D4 K)).range →
      (∀ α ∈ E,
        α ∉ (MulAut.conj : ↥(adjointGroup Tag.D4 K) →* MulAut ↥(adjointGroup Tag.D4 K)).range →
          CFSG.LieType.SeitzGeneration.ExcWideThree.D4ElemType α fun ε σ => ε ≠ 0 ∧ σ = 1) →
      seitzHyperGamma 3 E = ⊤

theorem d4EightOuterCubes_of_graph (hS2 : CFSG.AGLEmbeddingD2.KFactSeitzRankTwo)
    (hG : D4EightGraphCubes) : D4EightOuterCubes := by
  intro K _ _ hK E hE hc hinn hnoF
  by_cases hGF : ∃ β ∈ E, D4ElemType β fun ε σ => ε ≠ 0 ∧ σ ≠ 1
  · exact seitzHyperGamma_eq_top_of_graphField hS2 hK hE hc hnoF hGF
  · refine hG K hK E hE hc hinn fun α hα hαin => ?_
    obtain ⟨g, a, σ, ε, hε, hαeq, hσ3, hcase⟩ := outer_cube_normal_form_cases α (hE.2 α hα) hαin
    rcases hcase with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact absurd ⟨g, a, σ, ε, hε, hσ3, ⟨h0, h1⟩, hαeq⟩ (hnoF α hα)
    · exact absurd ⟨α, hα, g, a, σ, ε, hε, hσ3, ⟨h0, h1⟩, hαeq⟩ hGF
    · exact ⟨g, a, σ, ε, hε, hσ3, ⟨h0, h1⟩, hαeq⟩

theorem fieldAutD4_of_fieldType {S : Type} [Group S] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 3) (e : S ≃* ↥(adjointGroup Tag.D4 K)) {φ : MulAut S}
    (hφ3 : φ ^ 3 = 1)
    (hF : D4ElemType (MulAut.congr e φ) fun ε σ => ε = 0 ∧ σ ≠ 1) : FieldAutD4 S φ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by norm_num) hK
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; norm_num
  set α := MulAut.congr e φ with hαdef
  have hα : α ^ 3 = 1 := by rw [hαdef, ← map_pow, hφ3, map_one]
  obtain ⟨g, a, σ, ε, -, hσ3, ⟨hε0, hσ1⟩, hαeq⟩ := hF
  subst hε0
  rw [d4Graph_zero, mul_one] at hαeq
  obtain ⟨d, T, hd0, hdf, hT, hT3, hσT⟩ :=
    exists_frobenius_of_cube Nat.prime_two (by norm_num) K hK σ hσ3 hσ1
  have hconj : ∀ (β : MulAut ↥(adjointGroup Tag.D4 K)) (g' : ↥(adjointGroup Tag.D4 K))
      (a' : Fin Tag.D4.rank → Kˣ), β = MulAut.conj g' * exactNormalAut Tag.D4 K a' T 0 →
      β ^ 3 = 1 → ∃ ψ : MulAut ↥(adjointGroup Tag.D4 K),
        ψ * β * ψ⁻¹ = entrywiseAdjointAut Tag.D4 T := fun β g' a' hβ hβ3 =>
    exists_conj_eq_entrywiseAdjointAut_D4 hK hK4 hd0 hdf T hT g' a' β hβ hβ3
  obtain ⟨τ, ψ, hτ1, hψ⟩ : ∃ (τ : K ≃+* K) (ψ : MulAut ↥(adjointGroup Tag.D4 K)), τ ≠ 1 ∧
      ψ * α * ψ⁻¹ = entrywiseAdjointAut Tag.D4 τ := by
    rcases hσT with hσ | hσ
    · rw [hσ] at hαeq hσ1
      obtain ⟨ψ, hψ⟩ := hconj α g a hαeq hα
      exact ⟨T, ψ, hσ1, hψ⟩
    · obtain ⟨g', a', hα2⟩ := sq_conj_mul_exactNormalAut g a σ
      have hσ2 : σ ^ 2 = T := by
        rw [hσ, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hT3, one_mul]
      rw [hσ2, ← hαeq] at hα2
      have hα23 : (α ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hα, one_pow]
      have hα22 : (α ^ 2) ^ 2 = α := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hα, one_mul]
      obtain ⟨ψ, hψ⟩ := hconj (α ^ 2) g' a' hα2 hα23
      refine ⟨σ, ψ, hσ1, ?_⟩
      have h1 : ψ * α * ψ⁻¹ = (ψ * α ^ 2 * ψ⁻¹) ^ 2 := by
        calc ψ * α * ψ⁻¹ = ψ * (α ^ 2) ^ 2 * ψ⁻¹ := by rw [hα22]
          _ = (ψ * α ^ 2 * ψ⁻¹) ^ 2 := (conj_pow).symm
      rw [h1, hψ, ← entrywiseAdjointAut_pow, hσ]
  refine ⟨K, inferInstance, inferInstance, e, τ, ψ, hK, hτ1, fun h => ?_⟩
  exact ⟨entrywiseAdjointAut Tag.D4 τ h, rfl, by rw [hψ]⟩

theorem seitzGoodIndex_d4Eight {q : TauCeti.PrimePower} (hq : IsTwoPow q 3) :
    SeitzGoodIndex 3 (.D 4 q) :=
  Or.inr (Or.inr (Or.inr (show FourIndex (.D 4 q) from ⟨rfl, hq⟩)))

theorem seitz2310FourFreeAt_d4_of (hL : SeitzHyperLie fun d p _ => SeitzGoodIndex p d.1)
    (hO : D4EightOuterCubes) :
    Seitz2310FourFreeAt OuterFourAux.IsD4EightIndex FieldAutD4 := by
  intro S _ _ d hS hd E hEel hEcard hno
  obtain ⟨d₀, hv⟩ := d
  cases d₀ with
  | D r q =>
    obtain ⟨rfl, hq⟩ := hd
    obtain ⟨e⟩ := hS
    obtain ⟨K, _, _, e', hK⟩ := exists_mulEquiv_adjointD4 hv hq e
    by_cases hinn : E ≤ (MulAut.conj : S →* MulAut S).range
    ·
      have hmod := CFSG.Models.lieModel_D 4 q hv e
      rw [hq.1, hq.2] at hmod
      obtain ⟨-, hcl | ⟨h0, -⟩⟩ := hmod
      swap
      · omega
      haveI : IsSimpleGroup S :=
        (CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaPlus S 4 2 3
          hcl).2
      have hnab : ∃ a b : S, a * b ≠ b * a := by
        obtain ⟨g, h, hgh⟩ := (opposite_simple_root_noncommutativity Tag.D4 K).2.2.1
        refine ⟨e'.symm g, e'.symm h, fun hc => hgh ?_⟩
        have := congrArg e' hc
        simpa using this
      have hpd : (3 : ℕ) ≠ (TauCeti.LieTypeIndex.D 4 q).characteristic := by
        rw [TauCeti.LieTypeIndex.characteristic_D, hq.1]
        norm_num
      have hgood := seitzGoodIndex_d4Eight hq
      have hlist : ¬ P1ThreeLieList 3 ⟨.D 4 q, hv⟩ := by
        intro hl
        obtain ⟨-, q', -, -, h | h⟩ := SeitzBridgeAux.p1_cases hpd hl (Or.inr (Or.inr
          (Or.inr ⟨rfl, hq⟩)))
        · cases h
        · cases h
      exact SeitzHyperGoodInAux.seitzHyperGamma_eq_top_of_inner hL Nat.prime_three (by norm_num)
        inferInstance hnab ⟨.D 4 q, hv⟩ e hpd hlist hgood hEel hEcard hinn
    ·
      refine seitzHyperGamma_eq_top_of_congr e' ?_
      obtain ⟨hE'el, hE'c⟩ := map_congr_data e' hEel hEcard
      refine hO K hK _ hE'el hE'c (fun h => hinn (le_range_conj_of_map_congr e' h)) ?_
      rintro _ ⟨φ, hφ, rfl⟩ hF
      exact hno φ hφ (fieldAutD4_of_fieldType hK e' (hEel.2 φ hφ) hF)
  | _ => exact hd.elim

end Reduction

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz
